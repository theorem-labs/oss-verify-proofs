(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8q.v:156-158;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACbk.v:76-79; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:200-203, 287-290,
   358-363, for libreac/fuzz_identity's asan-ubsan build (lib/B). The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8h.v:75-78, 95-98, 104-107. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_family_of.v, with its module paths and numbers changed; 1396 of its 1480 lines of code are new or changed and 763 lines of the source are left out. *)
(* read_name (fuzz_boxreg.asan-ubsan 0x81318, 116 instructions; C: fuzz/fuzz_boxreg.c:70-81, with fuzz_u8 and fuzz_take
   of fuzz/fuzz.h:36-66 inlined): the contract of the ASan+UBSan build's code, in cgif's caller-journal form
   (proofs/cgif/cgif_file_fuzzer/lib/YC20.v:311-365, tlzw_*; CONVENTIONS section 2) with the shapes of
   lib/B/Prog/BoxBCJ.v (tbwr_ok, tbcj_kept: lib/A/Prog/BoxCJ.v over boxb_listing).
   What the code does. The function takes a 48-byte frame on the machine stack (addi sp,sp,-48; ra, s0..s3 saved) and
   gets a0 = c, the address of the caller's cursor struct fuzz_in { p at c, n at c + 8 }. It traps (unimp 0x8148c) when
   c is not 8-aligned (andi/bnez 0x81330). fuzz_u8: it loads n (0x81358); when n = 0 the length byte is 0 (0x813d4),
   else it stores n - 1 at c + 8, loads p, traps when p is NULL or p + 1 wraps (bgeu 0x8138c), stores p + 1 at c and
   loads the byte x at p; the wanted length is x mod 48 (mul 0xab / srli 13, 0x813b0-0x813cc). fuzz_take: it loads n
   again, takes k = min (x mod 48, n) (bltu 0x813e4), loads p, traps when p + k wraps or crosses NULL (bltu /
   snez-seqz-xor 0x81400-0x81410),
   stores p + k at c and n - k at c + 8. Then it calls malloc (k + 1) (0x81434, BB___interceptor_trampoline_malloc),
   branches to abort when the result is NULL (beqz 0x81438 -> 0x81490 __asan_handle_no_return, abort), copies the k
   bytes with __asan_memcpy (s, p', k) (0x81448; p' is the cursor's p after fuzz_u8), traps when s + k wraps
   (not/bltu 0x8144c), stores 0 at s + k after the shadow check of that byte, and returns s.
   With pl the n remaining input bytes: k = read_name_c.rn_k pl, the name holds Boxreg.bsub pl 1 k ++ [0], and the
   cursor advances by min (n, 1) + k.
   UBSan traps, each refuted: c not 8-aligned by the premise c mod 8 = 0; p + 1 and p + k by the input block (n > 0:
   4096 <= bi <= p and p + n <= bi + Li below the allocator's ceiling; n = 0: k = 0 and the check passes for every p);
   s + k by the allocator's block law for the new block.
   Why the caller-journal form: the cursor is in the caller's frame. Its one caller, LLVMFuzzerTestOneInput, keeps
   `struct fuzz_in in` in its spill area on the machine stack (s1 + 136 = p, s1 + 144 = n; the two calls at 0x80520
   and 0x80824 pass a0 = s1 + 136), between its own sp and its entry sp, so the right to write the 16 bytes is
   awr_byte's window case of the caller's journal; the spec takes it as the premise tbwr_ok (BoxBCJ.v).
   Bytes of the caller written: exactly the 16 cursor bytes [c, c + 16) (8-byte stores at c + 8 and c: twice each when
   n > 0, once each when n = 0).
   Bytes written besides: the new name block [s, s + k + 1) and the own window [sp - READ_NAME_STKB, sp). The post's
   tbcj_kept says every other byte is kept (E = read_name_c.rn_writes c s k).
   The malloc rule: cgif's amalloc04_rule (lib/Reusable/YC5d.v:57-76), taken in the proof at
   pa_sigma BB___interceptor_trampoline_malloc = pc_wrap_malloc (as_code B) (BoxBPaLib.v pal_malloc). Its post gives
   4096 <= res, so the NULL branch to abort is never taken and the post has no NULL case; it extends the caller's
   journal by one event and adds exactly the block (s, k + 1) (ablocks ... = ablocks ... ++ [(s, k + 1)]). Its
   premises, carried here: 0 <= k + 1 < MALLOC_MAX and blocks_bytes Sc + (k + 1) <= LIVE_MAX (from the room fact
   below and k + 1 <= 48), st_nev Sc < EV_MAX (from st_nev Sc + EV_READ_NAMEB <= EV_MAX), mo_ok MT Sc (mo_malloc MT
   (k + 1)), the stack (ASTACK below the call's sp, inside READ_NAME_STKB), and the call trace. The trace is
   [pc_malloc_ra0; AB_read_nameP + 0x120]: at the call s0 holds k (0..47, below the stack), so chain_pre's bad_next
   gives the empty chain and call_trace0 is pc_malloc_ra0 :: [ra] (lib/Reusable/YCbq.v:327 call_trace_nil; ra is not
   pc_malloc_ra0 because pc_malloc_ra0 < BASE, BoxBPaLib.v pal_rt_below). The caller's own chain is not part of it.
   Room facts (internal path P3): the request k + 1 is 1..48 (x mod 48 <= 47); LIVE_READ_NAMEB = 48;
   EV_READ_NAMEB = 1 (the one malloc tick; read_name frees nothing). The caller discharges
   blocks_bytes Sc + 48 <= LIVE_MAX from its entry's blocks_bytes S + LIVE_LIB <= LIVE_MAX and its loop invariant
   "live blocks = the entry's ++ [(r, 288)]" (288 + 48 = 336 <= LIVE_LIB); the name is freed in the same loop
   iteration on every returning path (free at 0x808f4 / 0x808b4).
   Stack: the own 48-byte frame and ASTACK below it for the malloc wrapper (amalloc04_rule: ASTACK - o <= STK); the
   memcpy wrapper's ESTACK is less. No program callee.
   Read footprint, each byte covered by a premise: the 16 cursor bytes (val_mem; their shadow bytes, both 0 because c
   is 8-aligned and range_addressable c 16, refute the __asan_report_load8 / store8 branches); the input bytes
   [p, p + n) (their values; for n > 0 a heap block of the caller holds them, the driver's input block (p0, n0) of
   LLVMFuzzerTestOneInput's pre, whose shadow AR's block law gives: the load1 check at p and the memcpy source
   [p + 1, p + 1 + k)); for n = 0 the memcpy source is the empty range at p, hence amem_range p n and
   p + n <= 2 ^ 63. The store s[k] and the memcpy destination are in the new block (AR's block law after malloc).
   The only image reads are the GOT word of the shadow base and the shadow cell, both fixed by AR (AR_const_law).
   Hazards: the old walk's contract (a working branch 67b70ae1ec3 lib/B/Prog/read_name_c.v) is stated over AsanRT's RT,
   which pins malloc_context_size = 1 and is VACUOUS on this image: only its functional content is taken here
   (rn_k, the name bytes, the advanced cursor); no f* or csr instruction occurs in the 116 instructions (capstone
   scan, PROGRAM.md P1), so the fixed {fx} is sound.
   Image difference: the asan build (lib/A/Prog/ReadName.v, 0x812b0, 96 instructions) has no UBSan checks; the
   result and the written bytes are the same.
   The memory model is Pau's plain one (lib/Prog/read_name_c.v rn_k, rn_writes; lib/Prog/Boxreg.v bsub), used as it
   is. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaRun PaShadow.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBSyms BoxBList BoxBPa.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaJournal BoxBase.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBCJ.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Boxreg read_name_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
(* The room facts of the call: one allocator event (the malloc), and at most 48 bytes of new live heap. *)
Definition EV_READ_NAMEB : Z := 1.
Definition LIVE_READ_NAMEB : Z := 48.
(* How far the cursor advances: the length byte (when there is one) and the k name bytes. *)
Definition tbread_name_used (pl : list byte) : Z := Z.min (Z.of_nat (length pl)) 1 + read_name_c.rn_k pl.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg boxb_listing}.
#[local] Notation SEGS := (@pa_segs _ boxb_listing PI).
#[local] Notation BASE := (@pa_val _ boxb_listing PI A_TEXT).
(* The function's address in the image, the return address of its malloc call (0x81434 + 4), and the stack it
   needs: its own 48-byte frame and ASTACK below it for the malloc wrapper. *)
Definition AB_read_nameP : Z := BASE + AF_read_name.
Definition AB_read_name_mallocRA : Z := AB_read_nameP + 0x120.
Definition READ_NAME_STKB : Z := 48 + ASTACK.
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Definition tbread_name_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
  (regs : bvmap 5 word) (c p : Z) (pl : list byte) : world SEGS -> config -> Prop :=
fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (s : Z),
c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + EV_READ_NAMEB) /\
aregs_preserved regs regs2 /\ getr regs2 10 = w64 s /\ frames S2 = frames Sc /\
(* the name: one new heap block of rn_k pl + 1 bytes, the caller's to write and to free *)
4096 <= s /\
ablocks B ly2 S2 = ablocks B lyc Sc ++ [(s, read_name_c.rn_k pl + 1)] /\
(forall blc i, In (s, read_name_c.rn_k pl + 1) blc -> 0 <= i < read_name_c.rn_k pl + 1 ->
  awr_byte STK sp0 FP (ablocks B ly S) blc ly2 own (s + i)) /\
aftok FP (ablocks B ly S) (s, read_name_c.rn_k pl + 1) /\
(forall i, 0 <= i <= read_name_c.rn_k pl ->
  aview SEGS (w_H W2) mem2 (s + i) =
  Some (bv_unsigned (nth (Z.to_nat i) (Boxreg.bsub pl 1 (read_name_c.rn_k pl) ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)))) /\
(* the caller's cursor, advanced *)
val_mem SEGS (mrestrict (w_H W2) mem2) c 8 (p + tbread_name_used pl) /\
val_mem SEGS (mrestrict (w_H W2) mem2) (c + 8) 8 (Z.of_nat (length pl) - tbread_name_used pl) /\
mo_le MT Sc S2 (mo_malloc MT (read_name_c.rn_k pl + 1)) /\
tbcj_kept B READ_NAME_STKB lyc Sc W memc W2 mem2 (spZ regs) (read_name_c.rn_writes c s (read_name_c.rn_k pl)).
Definition tbread_name_spec : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (c p bi Li : Z) (pl : list byte),
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - READ_NAME_STKB -> spZ regs <= sp0 ->
getr regs 10 = w64 c ->
(* the caller's cursor { p, n = length pl } at c, above sp, the caller's to let the call write *)
c mod 8 = 0 -> spZ regs <= c ->
val_mem SEGS (mrestrict (w_H W) memc) c 8 p ->
val_mem SEGS (mrestrict (w_H W) memc) (c + 8) 8 (Z.of_nat (length pl)) ->
range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF c 16 ->
tbwr_ok B STK sp0 FP ly S lyc Sc own W memc (spZ regs) c 16 ->
(* the remaining input bytes pl at p: a heap block holds them when there are any *)
0 <= p -> p + Z.of_nat (length pl) <= 2 ^ 63 -> amem_range p (Z.of_nat (length pl)) ->
(pl <> [] -> In (bi, Li) (ablocks B lyc Sc) /\ bi <= p /\ p + Z.of_nat (length pl) <= bi + Li) ->
(forall i, 0 <= i < Z.of_nat (length pl) ->
  aview SEGS (w_H W) memc (p + i) = Some (bv_unsigned (nth (Z.to_nat i) pl (Z_to_bv 8 0)))) ->
(* room for the malloc *)
st_nev Sc + EV_READ_NAMEB <= EV_MAX -> blocks_bytes Sc + LIVE_READ_NAMEB <= LIVE_MAX ->
mo_ok MT Sc (mo_malloc MT (read_name_c.rn_k pl + 1)) ->
In [pc_malloc_ra0 (as_code B); AB_read_name_mallocRA] (as_universe B) ->
SRr SEGS W (cfg_at SEGS AB_read_nameP regs memc mdc)
(tbread_name_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs c p pl).
End h.
End f.
End d.
(* ---- The walk. Its own layer (the tactics and the two call rules) is imported here, after the frozen statement
   text above (provenance/WALK-INTERFACE.md records lines 1-152 byte for byte), and the walk reopens the
   statement's sections with the same context. ---- *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBPaLib YC1g YC1h YC85 BoxBFrame.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YImgTop.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg boxb_listing}.
#[local] Notation SEGS := (@pa_segs _ boxb_listing PI).
#[local] Notation BASE := (@pa_val _ boxb_listing PI A_TEXT).
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
(* ---- The walk (CONVENTIONS section 5; the two calls through lib/B/Prog/YC85.v's amalloc04_sub and
   aj_intrin_atS, as cgif's lib/A/ACgc.v walks a call that allocates inside a caller's journal) ---------- *)
#[local] Notation VAL := (@pa_val _ boxb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ boxb_listing PI).
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis AMALLOC4 : amalloc04_rule SEGS B MT.
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA BB___asan_memcpy).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_boxb) (PI := PI).
(* The shadow base is atom 32; the band of shadow cells the walk may touch; the shadow entry of the 16 cursor
   bytes (the other shadow checks are discharged as obligations, see rn_tail). *)
Definition RN_SB : Z := 0x7fff8000.
Definition RN_HI : Z := 140737479966720.
Definition RNx : sv := SOff 32 0.
Definition RNspan : Z * Z := (RN_SB, RN_SB + 2 ^ 44 - 1).
Definition rn_SH : list shent := [mkSHE 10 0 16].
Definition F2 : afact := mkAF (2 ^ 46) (2 ^ 47) 4.
Definition F10 : afact := mkAF 4096 (2 ^ 47 - 16) 3.
Definition F32 : afact := mkAF RN_SB RN_SB 0.
Definition FK : afact := mkAF 0 47 0.
(* x mod 48 as 0x813b0-0x813cc computes it (mul 0xab, srl 13, 16q - 64q, + x, & 255). *)
Lemma rn_mod48 : forall x, 0 <= x < 256 -> x - 48 * (x * 171 / 8192) = x mod 48.
Proof.
intros x Hx.
assert (H : forallb (fun i => Z.of_nat i - 48 * (Z.of_nat i * 171 / 8192) =? Z.of_nat i mod 48) (seq 0 256) = true)
by (vm_compute; reflexivity).
rewrite forallb_forall in H. specialize (H (Z.to_nat x) ltac:(apply in_seq; lia)).
rewrite Z2Nat.id in H by lia. apply Z.eqb_eq in H. exact H.
Qed.
Definition RN_KQ : sv := SAlu ALU_SRL (SMd M_MUL (SOff 35 0) (SLit 171)) (SLit 13).
Definition RN_KX : sv :=
SAlu ALU_AND (SAlu ALU_ADD (SOff 35 0) (SAlu ALU_SUB (SAlu ALU_SLL RN_KQ (SLit 4)) (SAlu ALU_SLL RN_KQ (SLit 6))))
(SLit 255).
Lemma rn_kx_val : forall E x, ew E 35 = Z_to_bv 64 x -> 0 <= x < 256 -> U E RN_KX = x mod 48.
Proof.
intros E x H35 Hx.
assert (Ux : U E (SOff 35 0) = x) by (apply (U_atom E 35 x H35); lia).
pose proof (rn_mod48 x Hx) as Hm.
assert (Hq0 : 0 <= x * 171 / 8192 <= 6) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (Uq : U E RN_KQ = x * 171 / 8192).
{ unfold RN_KQ. rewrite U_SAlu, U_SMd, Ux, !U_SLit.
rewrite (zcanon_id 171) by (unfold M64; lia). rewrite (zcanon_id 13) by (unfold M64; lia).
cbn [zmd_raw zalu_raw]. rewrite (zcanon_id (x * 171)) by (unfold M64; lia).
change (Z.land 13 63) with 13. rewrite Z.shiftr_div_pow2 by lia.
apply zcanon_id. unfold M64. change (2 ^ 13) with 8192. lia. }
assert (U16 : U E (SAlu ALU_SLL RN_KQ (SLit 4)) = 16 * (x * 171 / 8192)).
{ rewrite U_SAlu, Uq, U_SLit, (zcanon_id 4) by (unfold M64; lia). cbn [zalu_raw].
change (Z.land 4 63) with 4. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.
rewrite zcanon_id by (unfold M64; lia). lia. }
assert (U64 : U E (SAlu ALU_SLL RN_KQ (SLit 6)) = 64 * (x * 171 / 8192)).
{ rewrite U_SAlu, Uq, U_SLit, (zcanon_id 6) by (unfold M64; lia). cbn [zalu_raw].
change (Z.land 6 63) with 6. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 6) with 64.
rewrite zcanon_id by (unfold M64; lia). lia. }
assert (Usub : U E (SAlu ALU_SUB (SAlu ALU_SLL RN_KQ (SLit 4)) (SAlu ALU_SLL RN_KQ (SLit 6)))
= (- (48 * (x * 171 / 8192))) mod M64).
{ rewrite U_SAlu, U16, U64. cbn [zalu_raw]. unfold zcanon. f_equal. lia. }
assert (Uadd : U E (SAlu ALU_ADD (SOff 35 0) (SAlu ALU_SUB (SAlu ALU_SLL RN_KQ (SLit 4)) (SAlu ALU_SLL RN_KQ (SLit 6))))
= x mod 48).
{ rewrite U_SAlu, Ux, Usub. cbn [zalu_raw]. unfold zcanon.
rewrite Zplus_mod_idemp_r. rewrite <- Hm. apply Z.mod_small. unfold M64.
pose proof (Z.mod_pos_bound x 48 ltac:(lia)). lia. }
unfold RN_KX. rewrite U_SAlu, Uadd, U_SLit, (zcanon_id 255) by (unfold M64; lia). cbn [zalu_raw].
change 255 with (Z.ones 8). rewrite Z.land_ones by lia.
pose proof (Z.mod_pos_bound x 48 ltac:(lia)) as Hb.
rewrite (Z.mod_small (x mod 48) (2 ^ 8)) by (change (2 ^ 8) with 256; lia).
apply zcanon_id. unfold M64. lia.
Qed.
Lemma rn_aview_val : forall (W : world SEGS) mem a v,
aview SEGS (w_H W) mem a = Some v -> 0 <= v < 256 -> val_mem SEGS (mrestrict (w_H W) mem) a 1 v.
Proof.
intros W mem a v Ha Hv k Hk. destruct k; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r.
unfold aview in Ha. destruct (mbyte SEGS (mrestrict (w_H W) mem) a) as [b|] eqn:Hb; cbn [option_map] in Ha; [|discriminate].
injection Ha as <-. f_equal.
unfold YO0f.le_byte. replace (8 * Z.of_nat 0) with 0 by reflexivity. replace (2 ^ (8 * Z.of_nat 1)) with 256 by reflexivity.
pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
rewrite Z.shiftr_0_r. rewrite (Z.mod_small (bv_unsigned b) 256) by lia. rewrite Z.mod_small by lia.
symmetry. apply Z_to_bv_bv_unsigned.
Qed.
(* Every byte the caller lets the call write is below the caller's own sp0 and above 4096: the stack case of
   awr_byte by astk_ok, the block cases by the allocator's block law, the frame case by frames_bounds. *)
Lemma rn_awr_above : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) mem md k a,
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k ->
awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a -> 4096 <= a /\ a < sp0.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k a HJ Hw.
pose proof HJ as (HARc & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct Hw as [Hw | [(Hfp & b & m & Hin & Hr) | [(b & m & Hin & _ & Hr) | (cid & pos & Hin & Hr)]]].
- lia.
- destruct (al_blocks _ _ LAWS lyc Sc W mem md b m HARc Hin) as (_ & Hb4096 & Hbceil & _). lia.
- destruct (al_blocks _ _ LAWS lyc Sc W mem md b m HARc Hin) as (_ & Hb4096 & Hbceil & _). lia.
- assert (Hin2 : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hin).
destruct (frames_bounds SEGS B LAWS lyc Sc W mem md cid pos HARc Hin2) as (Hf4096 & Hfceil & _).
pose proof (fs_frame_bytes_nonneg cid) as Hnn.
pose proof (fs_frame_bytes_nonneg cid) as Hnn2.
unfold shadow_addr in Hr. unfold in_zr in Hr. cbn [fst snd] in Hr.
destruct Hr as [Hr | Hr]; [lia|].
pose proof (Z.div_le_upper_bound (frame_addr lyc cid pos) 8 17592186044416 ltac:(lia) ltac:(lia)) as D1.
pose proof (Z.div_le_upper_bound (fs_frame_bytes cid) 8 17592186044416 ltac:(lia) ltac:(lia)) as D2.
pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)) as D3.
pose proof (Z.div_pos (fs_frame_bytes cid) 8 ltac:(lia) ltac:(lia)) as D4.
unfold SHADOW_OFF in *. lia.
Qed.
(* The symbolic state at the first slot, for a non-empty input: atom 32 is the shadow base (the walk loads it
   through the GOT word, object 1, and the cell, object 12), 33 the input pointer p, 34 the count n, 35 the
   length byte at p. *)
Definition rn_cur : YP09.region :=
YP09.mkRegion (Some 10%nat) 0 16 0 16 [YP09.mkChunk 0 (CVal 8 (SOff 33 0)); YP09.mkChunk 8 (CVal 8 (SOff 34 0))].
Definition rn_inp : YP09.region :=
YP09.mkRegion (Some 33%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 35 0))].
Definition rn_regions : smem := [stack_region 48; got_regionP; bcell_regionP 32; rn_cur; rn_inp].
Definition rn_facts : facts :=
mkFacts [(2%nat, F2); (10%nat, F10); (32%nat, F32); (33%nat, mkAF 4096 RN_HI 0); (34%nat, mkAF 1 RN_HI 0);
(35%nat, mkAF 0 255 0)] [] [].
Definition ss_rn : sstate := mkSS AF_read_name sr_atoms rn_regions None rn_facts.
Definition RNE (regs : bvmap 5 word) (p n x : Z) : env :=
Eimg (Ereg regs [Z_to_bv 64 RN_SB; Z_to_bv 64 p; Z_to_bv 64 n; Z_to_bv 64 x]).
(* and for the empty input, where there is no byte at p and p is only a number: atom 33 is p - 1 and atom 34 is 1,
   so that the cursor's two words are SOff 33 1 and SOff 34 (-1) in both entries. *)
Definition rn_cur0 : YP09.region :=
YP09.mkRegion (Some 10%nat) 0 16 0 16 [YP09.mkChunk 0 (CVal 8 (SOff 33 1)); YP09.mkChunk 8 (CVal 8 (SOff 34 (-1)))].
Definition rn_regions0 : smem := [stack_region 48; got_regionP; bcell_regionP 32; rn_cur0].
Definition rn_facts0 : facts := mkFacts [(2%nat, F2); (10%nat, F10); (32%nat, F32); (34%nat, mkAF 1 1 0)] [] [].
Definition ss_rn0 : sstate := mkSS AF_read_name sr_atoms rn_regions0 None rn_facts0.
Definition RNE0 (regs : bvmap 5 word) (p : Z) : env :=
Eimg (Ereg regs [Z_to_bv 64 RN_SB; Z_to_bv 64 (p - 1); Z_to_bv 64 1]).
(* The two entries share this: the stack frame, the GOT word and the shadow cell are in place. *)
Lemma rn_entry_common : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) mem md k
(regs : bvmap 5 word) (E : env),
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k ->
sp0 - STK <= spZ regs - READ_NAME_STKB -> spZ regs <= sp0 ->
ew E 2 = getr regs 2 -> ew E 32 = Z_to_bv 64 RN_SB ->
ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)) -> ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)) ->
Forall (region_ok SEGS E (mrestrict (w_H W) mem)) [stack_region 48; got_regionP; bcell_regionP 32].
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k regs E HJ Hlo Hhi E2 E32 Eo1 Eo12.
pose proof HJ as (HARc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (al_const _ _ LAWS lyc Sc W mem md HARc) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pa_obj_img 1 ltac:(lia)) as HgotR.
assert (WS : READ_NAME_STKB = 16432) by reflexivity.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok, stack_region, got_regionP, bcell_regionP;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
- rewrite E2. split; [unfold spZ in *; lia|]. split; [unfold spZ in *; lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. unfold spZ in *. lia.
- rewrite Eo1, unsigned_lit_small by (pose proof (pa_val_range (A_OBJ 1)); lia).
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
[cbn [sv_denot]; rewrite Eo12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
- rewrite Eo12, unsigned_lit_small by (pose proof (pa_val_range (A_OBJ 12)); lia).
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 RNx RN_SB);
[cbn [sv_denot RNx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold RN_SB; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
Qed.
(* the entry for a non-empty input *)
Lemma rn_entry : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) mem md k
(regs : bvmap 5 word) (c p n x : Z),
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - READ_NAME_STKB -> spZ regs <= sp0 ->
getr regs 10 = w64 c -> c mod 8 = 0 -> spZ regs <= c -> c + 16 <= sp0 ->
val_mem SEGS (mrestrict (w_H W) mem) c 8 p ->
val_mem SEGS (mrestrict (w_H W) mem) (c + 8) 8 n ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF c 16 ->
(forall a, c <= a < c + 16 -> apresent (w_H W) mem a) ->
4096 <= p -> p + n <= alloc_ceiling -> (p + 1 <= IMG_LO \/ IMG_TOP <= p) -> 1 <= n ->
aview SEGS (w_H W) mem p = Some x -> 0 <= x < 256 ->
st_ok_pi SEGS VAL (RNE regs p n x) ss_rn
(restrict (w_H W) (mkst regs (Z_to_bv 64 AB_read_nameP) mem (seg_rom SEGS)))
/\ sh_ok SEGS RNx rn_SH (RNE regs p n x) (mrestrict (w_H W) mem).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k regs c p n x
HJ Hal16 Hlo Hhi H10 Hc8 Hcsp Hchi Hvc Hvn HRA Hcpres Hp4096 Hpn Hpimg Hn1 Hx Hxr.
pose proof HJ as (HARc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16' & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pa_obj_img 1 ltac:(lia)) as HgotR.
assert (WS : READ_NAME_STKB = 16432) by reflexivity.
assert (Hsp0 : 0 <= spZ regs) by (unfold spZ; pose proof (bv_unsigned_in_range 64 (getr regs 2)); lia).
pose proof (pal_got_cell B TL) as HgcD.
set (E := RNE regs p n x) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E, RNE; apply Eimg_env).
assert (EE : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E i = getr regs r)
by (intros i r Hi; unfold E, RNE; apply ew_Eimg_Ereg_nat; exact Hi).
assert (EX : forall j, (j < 4)%nat ->
ew E (32 + j) = nth j [Z_to_bv 64 RN_SB; Z_to_bv 64 p; Z_to_bv 64 n; Z_to_bv 64 x] (Z_to_bv 64 0))
by (intros j Hj; unfold E, RNE; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
cbn [nth Nat.add] in E32, E33, E34, E35.
assert (Eo1 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)))
by (unfold E, RNE; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Eo12 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
by (unfold E, RNE; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E2 : ew E 2 = getr regs 2) by (apply (EE 2%nat 2%bv); reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 c) by (rewrite (EE 10%nat 10%bv eq_refl); exact H10).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (Uc : bv_unsigned (ew E 10) = c) by (rewrite E10; apply unsigned_lit_small; lia).
assert (Up : bv_unsigned (ew E 33) = p) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U1 : bv_unsigned (ew E (A_OBJ 1)) = VAL (A_OBJ 1))
by (rewrite Eo1; apply unsigned_lit_small; pose proof (pa_val_range (A_OBJ 1)); lia).
assert (U12 : bv_unsigned (ew E (A_OBJ 12)) = VAL (A_OBJ 12))
by (rewrite Eo12, unsigned_lit_small; [reflexivity | pose proof (pa_val_range (A_OBJ 12)); lia]).
pose proof (rn_entry_common STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k regs E HJ Hlo Hhi E2 E32 Eo1 Eo12) as HC.
pose proof (Forall_inv HC) as Hrst. pose proof (Forall_inv (Forall_inv_tail HC)) as Hrgot.
pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HC))) as Hrcell.
rewrite restrict_mkst_fx.
split.
- unfold ss_rn, AB_read_nameP. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold rn_regions. repeat apply Forall_cons; try apply Forall_nil;
[exact Hrst | exact Hrgot | exact Hrcell | |].
* unfold region_ok, rn_cur.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite Uc. split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (apresent_writable SEGS). apply Hcpres. lia. }
constructor; [|constructor; [|constructor]].
-- apply (chunk_ok_val SEGS E _ c 0 8 (SOff 33 0) p);
[cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
rewrite Z.add_0_r. exact Hvc.
-- apply (chunk_ok_val SEGS E _ c 8 8 (SOff 34 0) n);
[cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Hvn].
* unfold region_ok, rn_inp.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite Up. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ p 0 1 (SOff 35 0) x);
[cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
rewrite Z.add_0_r. apply rn_aview_val; [exact Hx | lia].
+ apply pairwise_disjoint_of_extents.
unfold rn_regions, stack_region, got_regionP, bcell_regionP, rn_cur, rn_inp, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
rewrite Usp, Uc, Up, U1, U12.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hcsp Hchi Hlo Hhi Hn1 Hp4096 Hpn Hpimg HcellR HgotR HgcD Hceil Hslo Hshi H47 Hstk0 Hsp0 C1 WS. clear. intros.
repeat split; lia.
+ split; [|split; [exact I | exact I]].
cbn [rn_facts f_atoms atoms_ok].
split; [unfold afact_ok, F2; cbn [af_lo af_hi af_al2]; rewrite Usp; change (2 ^ 4) with 16;
revert Hceil Hslo Hshi H47 Hstk0 Hal16 Hlo Hhi WS C1; clear; unfold spZ in *; intros; repeat split; lia|].
split; [unfold afact_ok, F10; cbn [af_lo af_hi af_al2]; rewrite Uc; change (2 ^ 3) with 8;
revert Hcsp Hchi Hc8 Hlo Hhi Hceil Hslo Hshi H47 Hstk0 Hsp0 WS C1; clear; intros; repeat split; lia|].
split; [unfold afact_ok, F32; cbn [af_lo af_hi af_al2]; rewrite E32, unsigned_lit_small by (unfold RN_SB; lia);
rewrite Z.pow_0_r, Z.mod_1_r; unfold RN_SB; lia|].
split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Up; rewrite Z.pow_0_r, Z.mod_1_r;
unfold RN_HI; revert Hp4096 Hpn Hn1 C1; clear; intros; lia|].
split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E34, unsigned_lit_small by (unfold RN_HI in *; lia);
rewrite Z.pow_0_r, Z.mod_1_r; unfold RN_HI; revert Hn1 Hp4096 Hpn C1; clear; intros; lia|].
split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E35, unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r. lia.
- unfold sh_ok, rn_SH. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) mem E RNx 10 c 16 c 0 16 HRA).
+ unfold U, RNx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite unsigned_lit_small by (unfold RN_SB; lia). unfold RN_SB, SHADOW_OFF. reflexivity.
+ unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite unsigned_lit_small by lia. reflexivity.
+ lia.
+ lia.
+ intros y Hy. cbn [Z.min Z.max] in Hy. unfold SHADOW_OFF.
revert Hy Hcsp Hlo Hhi Hceil Hslo Hshi H47 Hstk0 Hsp0 WS C1. clear. intros. lia.
Qed.
(* the entry for the empty input: no byte at p, and p is only a number *)
Lemma rn_entry0 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) mem md k
(regs : bvmap 5 word) (c p : Z),
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - READ_NAME_STKB -> spZ regs <= sp0 ->
getr regs 10 = w64 c -> c mod 8 = 0 -> spZ regs <= c -> c + 16 <= sp0 ->
val_mem SEGS (mrestrict (w_H W) mem) c 8 p ->
val_mem SEGS (mrestrict (w_H W) mem) (c + 8) 8 0 ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF c 16 ->
(forall a, c <= a < c + 16 -> apresent (w_H W) mem a) ->
0 <= p -> p <= 2 ^ 63 ->
st_ok_pi SEGS VAL (RNE0 regs p) ss_rn0
(restrict (w_H W) (mkst regs (Z_to_bv 64 AB_read_nameP) mem (seg_rom SEGS)))
/\ sh_ok SEGS RNx rn_SH (RNE0 regs p) (mrestrict (w_H W) mem).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k regs c p
HJ Hal16 Hlo Hhi H10 Hc8 Hcsp Hchi Hvc Hvn HRA Hcpres Hp0 Hp63.
pose proof HJ as (HARc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16' & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pa_obj_img 1 ltac:(lia)) as HgotR.
assert (WS : READ_NAME_STKB = 16432) by reflexivity.
assert (Hsp0 : 0 <= spZ regs) by (unfold spZ; pose proof (bv_unsigned_in_range 64 (getr regs 2)); lia).
pose proof (pal_got_cell B TL) as HgcD.
set (E := RNE0 regs p) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E, RNE0; apply Eimg_env).
assert (EE : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E i = getr regs r)
by (intros i r Hi; unfold E, RNE0; apply ew_Eimg_Ereg_nat; exact Hi).
assert (EX : forall j, (j < 3)%nat ->
ew E (32 + j) = nth j [Z_to_bv 64 RN_SB; Z_to_bv 64 (p - 1); Z_to_bv 64 1] (Z_to_bv 64 0))
by (intros j Hj; unfold E, RNE0; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 2%nat ltac:(lia)) as E34. cbn [nth Nat.add] in E32, E33, E34.
assert (Eo1 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)))
by (unfold E, RNE0; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Eo12 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
by (unfold E, RNE0; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E2 : ew E 2 = getr regs 2) by (apply (EE 2%nat 2%bv); reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 c) by (rewrite (EE 10%nat 10%bv eq_refl); exact H10).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (Uc : bv_unsigned (ew E 10) = c)
by (rewrite E10; apply unsigned_lit_small; revert Hcsp Hchi Hlo Hhi Hceil Hslo Hshi H47 Hstk0 Hsp0 WS C1; clear; intros; lia).
assert (U1 : bv_unsigned (ew E (A_OBJ 1)) = VAL (A_OBJ 1))
by (rewrite Eo1; apply unsigned_lit_small; pose proof (pa_val_range (A_OBJ 1)); lia).
assert (U12 : bv_unsigned (ew E (A_OBJ 12)) = VAL (A_OBJ 12))
by (rewrite Eo12, unsigned_lit_small; [reflexivity | pose proof (pa_val_range (A_OBJ 12)); lia]).
assert (Dp : sv_denot E (SOff 33 1) = Z_to_bv 64 p).
{ cbn [sv_denot]. rewrite E33. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
rewrite Zplus_mod_idemp_l. f_equal. lia. }
assert (D0 : sv_denot E (SOff 34 (-1)) = Z_to_bv 64 0).
{ cbn [sv_denot]. rewrite E34, unsigned_lit_small by lia. reflexivity. }
pose proof (rn_entry_common STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k regs E HJ Hlo Hhi E2 E32 Eo1 Eo12) as HC.
pose proof (Forall_inv HC) as Hrst. pose proof (Forall_inv (Forall_inv_tail HC)) as Hrgot.
pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HC))) as Hrcell.
rewrite restrict_mkst_fx.
split.
- unfold ss_rn0, AB_read_nameP. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold rn_regions0. repeat apply Forall_cons; try apply Forall_nil;
[exact Hrst | exact Hrgot | exact Hrcell |].
unfold region_ok, rn_cur0.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite Uc. split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (apresent_writable SEGS). apply Hcpres. lia. }
constructor; [|constructor; [|constructor]].
-- apply (chunk_ok_val SEGS E _ c 0 8 (SOff 33 1) p); [exact Dp | zside | zside |].
rewrite Z.add_0_r. exact Hvc.
-- apply (chunk_ok_val SEGS E _ c 8 8 (SOff 34 (-1)) 0); [exact D0 | zside | zside | exact Hvn].
+ apply pairwise_disjoint_of_extents.
unfold rn_regions0, stack_region, got_regionP, bcell_regionP, rn_cur0, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
rewrite Usp, Uc, U1, U12.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hcsp Hchi Hlo Hhi HcellR HgotR HgcD Hceil Hslo Hshi H47 Hstk0 Hsp0 C1 WS. clear. intros.
repeat split; lia.
+ split; [|split; [exact I | exact I]].
cbn [rn_facts0 f_atoms atoms_ok].
split; [unfold afact_ok, F2; cbn [af_lo af_hi af_al2]; rewrite Usp; change (2 ^ 4) with 16;
revert Hceil Hslo Hshi H47 Hstk0 Hal16 Hlo Hhi WS C1; clear; unfold spZ in *; intros; repeat split; lia|].
split; [unfold afact_ok, F10; cbn [af_lo af_hi af_al2]; rewrite Uc; change (2 ^ 3) with 8;
revert Hcsp Hchi Hc8 Hlo Hhi Hceil Hslo Hshi H47 Hstk0 Hsp0 WS C1; clear; intros; repeat split; lia|].
split; [unfold afact_ok, F32; cbn [af_lo af_hi af_al2]; rewrite E32, unsigned_lit_small by (unfold RN_SB; lia);
rewrite Z.pow_0_r, Z.mod_1_r; unfold RN_SB; lia|].
split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E34, unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r. lia.
- unfold sh_ok, rn_SH. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) mem E RNx 10 c 16 c 0 16 HRA).
+ unfold U, RNx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite unsigned_lit_small by (unfold RN_SB; lia). unfold RN_SB, SHADOW_OFF. reflexivity.
+ unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite unsigned_lit_small by (revert Hcsp Hchi Hlo Hhi Hceil Hslo Hshi H47 Hstk0 Hsp0 WS C1; clear; intros; lia).
reflexivity.
+ lia.
+ lia.
+ intros y Hy. cbn [Z.min Z.max] in Hy. unfold SHADOW_OFF.
revert Hy Hcsp Hlo Hhi Hceil Hslo Hshi H47 Hstk0 Hsp0 WS C1. clear. intros. lia.
Qed.
(* The state both entries reach at 0x813ec (listing 0x1440), after the length byte and the min: atom 100 is the
   name length k (0..47), the cursor holds SOff 33 1 = p' (the input pointer after the length byte) and
   SOff 34 (-1) = m (the bytes left at p'). Registers 8, 15, 16 and 17 are re-seated there (the two entries
   compute them differently; 15, 16, 17 are dead). *)
Definition rn_mid_regs : list sv :=
[SLit 0; SOff 1 0; SOff 2 (-48); SOff 3 0; SOff 4 0; SOff 5 0; SOff 6 0; SOff 7 0;
SOff 100 0; SOff 9 0; SOff 10 0; SOff 10 8; SOff 34 (-1);
SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 8) (SLit 3)) (SOff 32 0);
SAlu ALU_SRL (SOff 10 0) (SLit 3); SOff 101 0; SOff 102 0; SOff 103 0; SOff 18 0; SOff 32 0;
SOff 20 0; SOff 21 0; SOff 22 0; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0;
SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0].
Definition rn_mid_stack : YP09.region :=
YP09.mkRegion (Some 2%nat) (-48) 0 (-48) 0
[YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0));
YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
YP09.mkChunk (-8) (CVal 8 (SOff 1 0))].
Definition rn_mid_facts : facts := mkFacts [(100%nat, FK); (2%nat, F2); (10%nat, F10); (32%nat, F32)] [] [].
Definition ss_mid : sstate := mkSS 0x1440 rn_mid_regs [rn_mid_stack; rn_cur0] None rn_mid_facts.
(* not a0, s2 at 0x8144c: the complement of the new block's address. *)
Lemma rn_lxor_ones : forall z, 0 <= z < 2 ^ 64 -> Z.lxor z (2 ^ 64 - 1) = 2 ^ 64 - 1 - z.
Proof.
intros z Hz. replace (2 ^ 64 - 1) with (Z.ones 64) by (rewrite Z.ones_equiv; lia).
pose proof (Z.add_lxor_2land z (Z.ones 64)) as H.
rewrite Z.land_ones in H by lia. rewrite (Z.mod_small z (2 ^ 64)) in H by lia.
rewrite Z.ones_equiv in H |- *. lia.
Qed.
(* 0x81400 bltu a5, s1 (a5 = p' + k, s1 = p'): the UBSan pointer-overflow trap is not taken. *)
Lemma rn_nowrap : forall E (a b : sv) (u v : Z),
U E a = u -> U E b = v -> v <= u -> branch_taken BC_LTU (sv_denot E a) (sv_denot E b) = false.
Proof. intros E a b u v Ha Hb Hle. rewrite branch_ltu_U, Ha, Hb. apply Z.ltb_ge. exact Hle. Qed.
(* 0x81410 beqz a6 (a6 = (p' <> 0) xor (p' + k = 0)): the UBSan trap is not taken either, because a name of
   k > 0 bytes starts inside the input block (4096 <= p') and k = 0 leaves p' + k = p'. *)
Lemma rn_xor_ok : forall E (p' kk : Z),
U E (SOff 33 1) = p' -> U E (SOff 100 0) = kk -> 0 <= kk -> 0 <= p' -> p' + kk < 2 ^ 64 ->
(0 < kk -> 0 < p') ->
branch_taken BC_EQ
(sv_denot E (SAlu ALU_XOR (SAlu ALU_SLTU (SLit 0) (SOff 33 1))
(SAlu ALU_SLTU (SAlu ALU_ADD (SOff 33 1) (SOff 100 0)) (SLit 1)))) (sv_denot E (SLit 0)) = false.
Proof.
intros E p' kk Hp Hk Hk0 Hp0 Hsum Hnz.
assert (Hadd : U E (SAlu ALU_ADD (SOff 33 1) (SOff 100 0)) = p' + kk).
{ rewrite U_SAlu, Hp, Hk. cbn [zalu_raw]. apply zcanon_id. unfold M64. lia. }
assert (H1 : U E (SAlu ALU_SLTU (SLit 0) (SOff 33 1)) = (if 0 <? p' then 1 else 0)).
{ rewrite U_SAlu, Hp, U_SLit, (zcanon_id 0) by (unfold M64; lia). cbn [zalu_raw].
destruct (0 <? p'); apply zcanon_id; unfold M64; lia. }
assert (H2 : U E (SAlu ALU_SLTU (SAlu ALU_ADD (SOff 33 1) (SOff 100 0)) (SLit 1)) = (if p' + kk <? 1 then 1 else 0)).
{ rewrite U_SAlu, Hadd, U_SLit, (zcanon_id 1) by (unfold M64; lia). cbn [zalu_raw].
destruct (p' + kk <? 1); apply zcanon_id; unfold M64; lia. }
rewrite branch_eq_U, (U_lit E 0 ltac:(lia)). apply Z.eqb_neq.
rewrite U_SAlu, H1, H2. cbn [zalu_raw].
destruct (Z.ltb_spec 0 p') as [Hlt | Hle]; destruct (Z.ltb_spec (p' + kk) 1) as [Hl2 | Hg2];
[exfalso; lia | | | exfalso; lia]; vm_compute; discriminate.
Qed.
(* 0x81450 bltu a0, s0 (a0 = not s, s0 = k): the UBSan trap is not taken, the new block being far below 2 ^ 64. *)
Lemma rn_not_ok : forall E (r kx : Z),
U E (SOff 108 0) = r -> U E (SOff 100 0) = kx -> 4096 <= r -> r <= RN_HI -> 0 <= kx <= 47 ->
branch_taken BC_LTU (sv_denot E (SAlu ALU_XOR (SOff 108 0) (SLit (-1)))) (sv_denot E (SOff 100 0)) = false.
Proof.
intros E r kx H108 H100 Hr1 Hr2 Hk.
assert (Hm1 : zcanon (-1) = 2 ^ 64 - 1) by (unfold zcanon, M64; reflexivity).
rewrite branch_ltu_U, H100, U_SAlu, H108, U_SLit, Hm1. cbn [zalu_raw].
rewrite rn_lxor_ones by (unfold RN_HI in *; lia).
rewrite zcanon_id by (unfold M64, RN_HI in *; lia).
apply Z.ltb_ge. unfold RN_HI in *. lia.
Qed.
(* A side-stack frame's bytes and its shadow lie below alloc_ceiling (frames_bounds). *)
Lemma rn_frame_low : forall lyc Sc (W : world SEGS) mem md cid pos a,
AR SEGS B lyc Sc W mem md -> In (cid, pos) (frames Sc) ->
(in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
0 <= a < alloc_ceiling.
Proof.
intros lyc Sc W mem md cid pos a HAR Hin Hr.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (frames_bounds SEGS B LAWS lyc Sc W mem md cid pos HAR Hin) as (Hf4096 & Hfceil & _).
pose proof (fs_frame_bytes_nonneg cid) as Hnn.
unfold frame_rng, shadow_addr, in_zr in Hr. cbn [fst snd] in Hr.
destruct Hr as [Hr | Hr]; [lia|].
pose proof (Z.div_le_upper_bound (frame_addr lyc cid pos) 8 17592186044416 ltac:(lia) ltac:(lia)) as D1.
pose proof (Z.div_le_upper_bound (fs_frame_bytes cid) 8 17592186044416 ltac:(lia) ltac:(lia)) as D2.
pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)) as D3.
pose proof (Z.div_pos (fs_frame_bytes cid) 8 ltac:(lia) ltac:(lia)) as D4.
unfold SHADOW_OFF in *. lia.
Qed.
(* What the call keeps, step by step (BoxBCJ.tbcj_kept), as lib/A/Prog/ReadName.v:447-497 builds BoxCJ.tcj_kept:
   a run or a memcpy keeps every byte outside the bytes E it may write and the own stack window; malloc keeps
   what acall_kept says. *)
Lemma tk_init : forall STK' lyc Sc W memc sp E,
(forall a, sp - STK' <= a < sp -> apresent (w_H W) memc a) -> tbcj_kept B STK' lyc Sc W memc W memc sp E.
Proof.
intros STK' lyc Sc W memc sp E HP.
split; [intros; reflexivity|]. split; [intros; reflexivity|]. split; [intros; reflexivity|].
split; [intros; reflexivity|]. split; [intros a _ _ Ha; exact Ha | exact HP].
Qed.
Lemma tk_weaken : forall STK' lyc Sc W memc W2 m2 sp (E E' : Z -> Prop),
tbcj_kept B STK' lyc Sc W memc W2 m2 sp E -> (forall a, E a -> E' a) -> tbcj_kept B STK' lyc Sc W memc W2 m2 sp E'.
Proof.
intros STK' lyc Sc W memc W2 m2 sp E E' (K1 & K2 & K3 & K4 & K5 & K6) HE.
split; [intros a Ha Hw He; apply K1; [exact Ha | exact Hw | intros h; exact (He (HE _ h))]|].
split; [intros b m i Hin Hi He; apply (K2 b m i); [exact Hin | exact Hi | intros h; exact (He (HE _ h))]|].
split; [exact K3|].
split; [intros cid pos a Hin Hz He; apply (K4 cid pos a Hin Hz); intros h; exact (He (HE _ h))|].
split; [exact K5 | exact K6].
Qed.
Lemma tk_step : forall STK' lyc Sc W memc W1 m1 W2 m2 sp (E : Z -> Prop) mdx,
AR SEGS B lyc Sc W memc mdx -> alloc_ceiling <= sp - STK' -> (forall a, in_img SEGS a -> ~ E a) ->
tbcj_kept B STK' lyc Sc W memc W1 m1 sp E ->
(forall a, 0 <= a < 2 ^ 64 -> ~ E a -> ~ (sp - STK' <= a < sp) -> aview SEGS (w_H W2) m2 a = aview SEGS (w_H W1) m1 a) ->
(forall a, apresent (w_H W1) m1 a -> apresent (w_H W2) m2 a) ->
(forall a, sp - STK' <= a < sp -> apresent (w_H W2) m2 a) ->
tbcj_kept B STK' lyc Sc W memc W2 m2 sp E.
Proof.
intros STK' lyc Sc W memc W1 m1 W2 m2 sp E mdx HAR Hsp HEi (K1 & K2 & K3 & K4 & K5 & K6) HK HP HP6.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split. { intros a Ha Hw He. rewrite (HK a ltac:(lia) He Hw). apply K1; assumption. }
split. { intros b m i Hin Hi He. destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hin) as (_ & H4096 & Hceil & _).
rewrite (HK (b + i) ltac:(lia) He ltac:(lia)). apply (K2 b m i); assumption. }
split. { intros a Hi Hns Her. pose proof (pa_segs_low a Hi). unfold kLowMemEnd in *.
rewrite (HK a ltac:(lia) (HEi a Hi) ltac:(lia)). apply K3; assumption. }
split. { intros cid pos a Hin Hz He. destruct (rn_frame_low lyc Sc W memc mdx cid pos a HAR Hin Hz) as (Hz1 & Hz2).
rewrite (HK a ltac:(lia) He ltac:(lia)). apply (K4 cid pos a Hin Hz He). }
split; [intros a Ha Hw Hp; apply HP; apply K5; assumption | exact HP6].
Qed.
Lemma tk_malloc : forall STK' lyc Sc W memc W1 m1 W2 m2 sp (E : Z -> Prop) slo shi (E2 : Z -> Prop),
tbcj_kept B STK' lyc Sc W memc W1 m1 sp E ->
acall_kept SEGS B lyc Sc W1 m1 W2 m2 slo shi E2 ->
sp - STK' <= slo -> shi <= sp -> (forall a, E2 a -> E a) ->
(forall a, sp - STK' <= a < sp -> apresent (w_H W2) m2 a) ->
tbcj_kept B STK' lyc Sc W memc W2 m2 sp E.
Proof.
intros STK' lyc Sc W memc W1 m1 W2 m2 sp E slo shi E2 (K1 & K2 & K3 & K4 & K5 & K6) (A1 & A2 & A3 & A4 & A5 & A6) Hlo Hhi HE2 HP6.
split. { intros a Ha Hw He. rewrite (A1 a Ha ltac:(lia)). apply K1; assumption. }
split. { intros b m i Hin Hi He. rewrite (A2 b m i Hin Hi (fun h => He (HE2 _ h))). apply (K2 b m i); assumption. }
split. { intros a Hi Hns Her. rewrite (A3 a Hi Hns Her). apply K3; assumption. }
split. { intros cid pos a Hin Hz He. rewrite (A4 cid pos a Hin Hz (fun h => He (HE2 _ h))). apply (K4 cid pos a Hin Hz He). }
split; [intros a Ha Hw Hp; apply A5; [exact Ha | lia | apply K5; assumption] | exact HP6].
Qed.
(* A value in memory moves with its bytes. *)
Lemma rn_vm_move : forall H1 (m1 : word -> option byte) H2 (m2 : word -> option byte) a n v,
(forall x, a <= x < a + Z.of_nat n -> aview SEGS H2 m2 x = aview SEGS H1 m1 x) ->
val_mem SEGS (mrestrict H1 m1) a n v -> val_mem SEGS (mrestrict H2 m2) a n v.
Proof.
intros H1 m1 H2 m2 a n v HK HV j Hj.
rewrite (mbyte_of_aview SEGS H1 H2 m1 m2 (a + Z.of_nat j) (HK (a + Z.of_nat j) ltac:(lia))). apply HV. exact Hj.
Qed.
(* After a run: what the call kept, with the write set Ewr (lib/A/Prog/ReadName.v:542 rn_tkupd). *)
Ltac rn_tkupdB lyc Sc W memc mdc HAR sp Ewr HEimg TK HJc :=
lazymatch goal with HFr : frame_of ?Ex ?rsx (mrestrict (w_H ?Wx) ?m0) (mrestrict (w_H ?Wx) ?m1),
HG : mem_grows (mrestrict (w_H ?Wx) ?m0) (mrestrict (w_H ?Wx) ?m1) |- _ =>
let TK2 := fresh "TK" in
assert (TK2 : tbcj_kept B READ_NAME_STKB lyc Sc W memc Wx m1 sp Ewr);
[ apply (tk_step READ_NAME_STKB lyc Sc W memc Wx m0 Wx m1 sp Ewr mdc HAR);
[ unfold READ_NAME_STKB, ASTACK in *; lia
| exact HEimg
| exact TK
| intros a Ha HnE HnS;
refine (kept_of_frame Ex rsx (w_H Wx) m0 m1 (fun x => Ewr x \/ (sp - READ_NAME_STKB <= x < sp)) HFr _ a Ha _);
[ intros bb wlo whi x Hin Hr;
let wsv := eval vm_compute in (windows rsx) in change (In (bb, wlo, whi) wsv) in Hin;
cbn [In] in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; unfold base_val in Hr|]); try contradiction;
cbv beta; unfold read_name_c.rn_writes;
repeat match goal with Hb : bv_unsigned (ew ?Ey ?nn) = _ |- _ =>
match type of Hr with context [bv_unsigned (ew Ey nn)] => rewrite Hb in Hr end end;
unfold READ_NAME_STKB, ASTACK in *; lia
| intros [h | h]; [exact (HnE h) | exact (HnS h)] ]
| intros a Ha; exact (apresent_grows (w_H Wx) m0 m1 a HG Ha)
| intros a Ha; pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJp & _);
apply HJp; unfold READ_NAME_STKB, ASTACK in *; lia ]
| clear TK; rename TK2 into TK ]
end.
(* After a run: a value in memory outside the run's windows stays. *)
Ltac rn_vmupd VC :=
lazymatch goal with HFr : frame_of ?Ex ?rsx (mrestrict (w_H ?Wx) ?m0) (mrestrict (w_H ?Wx) ?m1) |- _ =>
lazymatch type of VC with val_mem _ (mrestrict _ m0) ?a ?n ?v =>
let V2 := fresh "VCx" in
assert (V2 : val_mem SEGS (mrestrict (w_H Wx) m1) a n v);
[ apply (rn_vm_move (w_H Wx) m0 (w_H Wx) m1 a n v); [| exact VC];
intros x Hx; simpl Z.of_nat in Hx;
refine (kept_of_frame Ex rsx (w_H Wx) m0 m1 (fun y => ~ (a <= y < a + Z.of_nat n)) HFr _ x _ _);
[ intros bb wlo whi y Hin Hr;
let wsv := eval vm_compute in (windows rsx) in change (In (bb, wlo, whi) wsv) in Hin;
cbn [In] in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; unfold base_val in Hr|]); try contradiction;
cbv beta; simpl Z.of_nat;
repeat match goal with Hb : bv_unsigned (ew ?Ey ?nn) = _ |- _ =>
match type of Hr with context [bv_unsigned (ew Ey nn)] => rewrite Hb in Hr end end;
lia
| lia
| cbv beta; simpl Z.of_nat; intros Hn; apply Hn; exact Hx ]
| clear VC; rename V2 into VC ]
end end.
(* The walk from 0x813ec on: the two UBSan checks, the malloc, the memcpy, the NUL and the return. *)
Lemma rn_tail : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc md k
(regs : bvmap 5 word) (E : env) (ms : machine_state) (c p p' m kk : Z) (pl : list byte),
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms) md k ->
AR SEGS B lyc Sc W memc mdc ->
st_ok_pi SEGS VAL E ss_mid (restrict (w_H W) ms) ->
sh_ok SEGS RNx rn_SH E (mrestrict (w_H W) (ms_mem ms)) ->
img_env VAL A_LIM E -> env_agree 32 (Ereg regs []) E ->
tbcj_kept B READ_NAME_STKB lyc Sc W memc W (ms_mem ms) (spZ regs) (fun a => c <= a < c + 16) ->
ew E 10 = w64 c -> ew E 32 = w64 RN_SB -> ew E 100 = w64 kk ->
U E (SOff 33 1) = p' -> U E (SOff 34 (-1)) = m ->
YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - READ_NAME_STKB -> spZ regs <= sp0 ->
c mod 8 = 0 -> spZ regs <= c -> c + 16 <= sp0 ->
tbwr_ok B STK sp0 FP ly S lyc Sc own W memc (spZ regs) c 16 ->
kk = read_name_c.rn_k pl -> p' = p + Z.min (Z.of_nat (length pl)) 1 ->
m = Z.of_nat (length pl) - Z.min (Z.of_nat (length pl)) 1 ->
0 <= kk <= 47 -> kk <= m -> m <= 2 ^ 63 -> 0 <= p' -> p' + kk <= 2 ^ 63 -> (0 < kk -> 4096 <= p') ->
amem_range p' kk ->
(0 < kk -> exists b n0, In (b, n0) (ablocks B lyc Sc) /\ b <= p' /\ p' + kk <= b + req_size n0) ->
(forall i, 0 <= i < kk -> aview SEGS (w_H W) memc (p' + i) =
Some (bv_unsigned (nth (Z.to_nat i) (Boxreg.bsub pl 1 kk ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)))) ->
st_nev Sc + EV_READ_NAMEB <= EV_MAX -> blocks_bytes Sc + LIVE_READ_NAMEB <= LIVE_MAX ->
mo_ok MT Sc (mo_malloc MT (kk + 1)) ->
In [pc_malloc_ra0 (as_code B); AB_read_name_mallocRA] (as_universe B) ->
SRr SEGS W (mkCfg ms md) (tbread_name_post B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs c p pl).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc md k regs E ms c p p' m kk pl
HJ HARc HS SHOK HEI HAE TK E10 E32 E100 Up' Um Hraok Hra4 Hgp Htp
Hal16 Hlo Hhi Hc8 Hcsp Hchi HWR Hkk Hp' Hm Hkr Hkm Hm63 Hp'0 Hp'63 Hp'4096 HAMR HSRC HBYTES Hev Hlive MOK HUNIV.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof pa_B_ok as HBASE. pose proof (pa_base_lo (PL := PL_boxb)) as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : READ_NAME_STKB = 16432) by reflexivity.
assert (HAS : ASTACK = 16384) by reflexivity. assert (HES : ESTACK = 4096) by reflexivity.
pose proof HJ as (HAR1 & _ & _ & _ & _ & Hfrs & Hnev & Hk0 & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16' & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (E2 : ew E 2 = getr regs 2)
by (destruct HAE as [HA _]; rewrite (HA 2%nat ltac:(lia)); apply (ew_Ereg_nat regs [] 2 2%bv); reflexivity).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (Uc : bv_unsigned (ew E 10) = c)
by (rewrite E10; unfold w64; apply unsigned_lit_small;
revert Hcsp Hchi Hlo Hhi Hceil Hslo Hshi H47 Hstk0 WS C1; clear; intros; lia).
assert (U100 : U E (SOff 100 0) = kk) by (apply (U_atom E 100%nat kk E100); lia).
assert (Hspc : alloc_ceiling + READ_NAME_STKB <= spZ regs) by lia.
(* to the UBSan overflow check at 0x81400 *)
assert (Hadd : U E (SAlu ALU_ADD (SOff 33 1) (SOff 100 0)) = p' + kk)
by (rewrite U_SAlu, Up', U100; cbn [zalu_raw]; apply zcanon_id; unfold M64; lia).
assert (HAWR : awr_ok E [rn_mid_stack; rn_cur0] STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own).
{ eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spZ regs - sp0);
[reflexivity | rewrite Usp; lia | unfold rn_mid_stack; cbn [YP09.r_wlo]; lia
| unfold rn_mid_stack; cbn [YP09.r_whi]; lia |].
eapply awr_ok_cons_gen with (n := 10%nat) (b := c);
[reflexivity | exact Uc | | apply awr_ok_nil].
intros a Ha. unfold rn_cur0 in Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
exact (proj1 (HWR a ltac:(lia))). }
assert (HEimg0 : forall a, in_img SEGS a -> ~ (fun a : Z => c <= a < c + 16) a)
by (intros a Hi Ha; pose proof (pa_segs_low a Hi); unfold kLowMemEnd in *; cbv beta in Ha; lia).
(* to the UBSan overflow check at 0x81400 *)
paj_run_tok RUN HS HJ SHOK RNspan.
{ unfold ss_mid. cbn [ss_mem]. exact HAWR. }
rn_tkupdB lyc Sc W memc mdc HARc (spZ regs) (fun a : Z => c <= a < c + 16) HEimg0 TK HJ.
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.

(* 0x81400 bltu a5, s1: the trap side is impossible *)
psrr_branch_tok RUN BR HS SHOK RNspan.
{ exfalso. rewrite (rn_nowrap E _ _ (p' + kk) p' Hadd Up' ltac:(lia)) in Hc. discriminate. }
paj_run_tok RUN HS HJ SHOK RNspan.
{ exact HAWR. }
rn_tkupdB lyc Sc W memc mdc HARc (spZ regs) (fun a : Z => c <= a < c + 16) HEimg0 TK HJ.
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.

(* 0x81410 beqz a6: the trap side is impossible *)
psrr_branch_tok RUN BR HS SHOK RNspan.
{ exfalso. lazymatch goal with
| H : branch_taken BC_EQ (sv_denot ?Ex (SAlu ALU_XOR _ _)) _ = true |- _ =>
rewrite (rn_xor_ok Ex p' kk Up' U100 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in H; discriminate
end. }
(* to the malloc call at 0x81434 *)
paj_run_tok RUN HS HJ SHOK RNspan.
{ exact HAWR. }
rn_tkupdB lyc Sc W memc mdc HARc (spZ regs) (fun a : Z => c <= a < c + 16) HEimg0 TK HJ.
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.

(* the malloc of k + 1 bytes *)
prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp.
prreg HS (4%bv : bv 5) Rtp. prreg HS (8%bv : bv 5) Rs0. prreg HS (10%bv : bv 5) Ra0.
pmkst HS. ppcs.
assert (E3 : ew E 3 = getr regs 3)
by (destruct HAE as [HA _]; rewrite (HA 3%nat ltac:(lia)); apply (ew_Ereg_nat regs [] 3 3%bv); reflexivity).
assert (E4 : ew E 4 = getr regs 4)
by (destruct HAE as [HA _]; rewrite (HA 4%nat ltac:(lia)); apply (ew_Ereg_nat regs [] 4 4%bv); reflexivity).
assert (HMsp : spZ (ms_regs ms2) = spZ regs - 48)
by (unfold spZ at 1; rewrite Rsp, Usp, unsigned_lit_small by lia; reflexivity).
assert (HMra : raZ (ms_regs ms2) = AB_read_name_mallocRA).
{ unfold raZ. rewrite Rra, unsigned_lit_small by (pose proof (pa_val_range A_TEXT); lia).
unfold AB_read_name_mallocRA, AB_read_nameP, AF_read_name. lia. }
assert (HMs0 : s0Z (ms_regs ms2) = kk)
by (unfold s0Z; rewrite Rs0, E100, unsigned_lit_small by lia; reflexivity).
(* the cursor, as the two stores of 0x8141c and 0x8142c left it *)
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
pose proof (st_ok_region_nth Ex ssx msx 1%nat _ HS eq_refl) as HCUR end.
destruct HCUR as (_ & _ & _ & HCH).
pose proof (Forall_inv HCH) as HC8. pose proof (Forall_inv (Forall_inv_tail HCH)) as HC0.
cbn [YP09.r_base] in HC0, HC8. unfold base_val in HC0, HC8.
assert (Hmul : U E (SMd M_MUL (SOff 100 0) (SLit (-1))) = (- kk) mod M64).
{ rewrite U_SMd, U100, U_SLit. cbn [zmd_raw].
replace (zcanon (-1)) with (M64 - 1) by (unfold zcanon, M64; reflexivity).
unfold zcanon. replace (kk * (M64 - 1)) with (- kk + kk * M64) by ring.
rewrite Z_mod_plus_full. reflexivity. }
assert (VC0 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms2)) (bv_unsigned (ew E 10) + 0) 8 (p' + kk)).
{ apply (val_of_chunk_ok SEGS E _ (bv_unsigned (ew E 10)) 0 8 (SAlu ALU_ADD (SOff 33 1) (SOff 100 0)) (p' + kk) HC0).
- rewrite denot_lit_U. f_equal. rewrite U_SAlu, Up', U100. cbn [zalu_raw]. apply zcanon_id. unfold M64.
revert Hp'0 Hp'63 Hkr; clear; intros; lia.
- cbn [Z.of_N]. revert Hp'0 Hp'63 Hkr; clear; intros; lia.
- cbn [Z.of_N]. lia. }
assert (VC8 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms2)) (bv_unsigned (ew E 10) + 8) 8 (m - kk)).
{ apply (val_of_chunk_ok SEGS E _ (bv_unsigned (ew E 10)) 8 8
(SAlu ALU_ADD (SOff 34 (-1)) (SMd M_MUL (SOff 100 0) (SLit (-1)))) (m - kk) HC8).
- rewrite denot_lit_U. f_equal. rewrite U_SAlu, Um, Hmul. cbn [zalu_raw]. unfold zcanon.
rewrite Zplus_mod_idemp_r. apply Z.mod_small. unfold M64.
revert Hkm Hkr Hm63 Hp'63 Hp'0; clear; intros; lia.
- cbn [Z.of_N]. revert Hkm Hkr Hm63 Hp'63 Hp'0; clear; intros; lia.
- cbn [Z.of_N]. lia. }
eapply SRr_bind.
{ eapply (amalloc04_sub SEGS B LAWS Hsegs MT AMALLOC4 W (ms_regs ms2) (ms_mem ms2) STK sp0 FP ly S W0 mem0 md0 own
lyc Sc _ k (kk + 1) (spZ regs - 48 - sp0) (Z_to_bv 64 (VAL A_TEXT + 5260)) [] HJ).
- rewrite Ra0, E100, unsigned_lit_small by lia. reflexivity.
- unfold MALLOC_MAX. lia.
- unfold LIVE_READ_NAMEB in Hlive. lia.
- rewrite HMsp. lia.
- assert (Hq : spZ regs - 48 - sp0 = (spZ regs / 16 - 3 - sp0 / 16) * 16).
{ pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as D1. pose proof (Z.div_mod sp0 16 ltac:(lia)) as D2.
rewrite Hal16 in D1. rewrite Hal16' in D2. lia. }
rewrite Hq. apply Z_mod_mult.
- lia.
- rewrite HAS, WS in *. lia.
- rewrite Rgp, E3. exact Hgp.
- rewrite Rtp, E4. exact Htp.
- exact Rra.
- apply ret_ok_codeptr_v; [lia | reflexivity].


- unfold EV_READ_NAMEB in Hev. lia.
- apply (achain_chain_pre lyc (aview SEGS (w_H W) (ms_mem ms2)) (spZ (ms_regs ms2)) (s0Z (ms_regs ms2)) []
(ms_regs ms2)).
+ apply achain_low. rewrite HMs0. lia.
+ rewrite HMsp. lia.
+ reflexivity.
+ rewrite HMra. unfold AB_read_name_mallocRA, AB_read_nameP, AF_read_name. lia.
- rewrite call_trace_nil, HMra.
rewrite (proj2 (Z.eqb_neq _ _)) by
(pose proof (pal_rt_below B TL) as Hrtb; unfold AB_read_name_mallocRA, AB_read_nameP, AF_read_name; lia).
exact HUNIV.
- exact MOK. }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HJ2 & HP2 & Ha02 & Hfrs2 & Hres4096 & Eab2 & HK2 & MLE2 & _).
pose proof (proj1 HJ2) as HAR2.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres2 & _).
assert (HresIn : In (res, kk + 1) (ablocks B ly2 S2)) by (rewrite Eab2; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 res (kk + 1) HAR2 HresIn) as (Hr16 & Hr4096 & Hrceil & _ & HrP & _).
assert (Hrq : req_size (kk + 1) = kk + 1)
by (unfold req_size; destruct (Z.eqb_spec (kk + 1) 0) as [He | Hne]; [lia | reflexivity]).
rewrite Hrq in Hrceil, HrP.
(* what the call kept, through the malloc (lib/A/Prog/ReadName.v:901-908) *)
assert (TK1 : tbcj_kept B READ_NAME_STKB lyc Sc W memc W2 mem2 (spZ regs) (read_name_c.rn_writes c res kk)).
{ apply (tk_malloc _ _ _ _ _ _ _ _ _ _ (read_name_c.rn_writes c res kk) _ _ _
(tk_weaken _ _ _ _ _ _ _ _ _ (read_name_c.rn_writes c res kk) TK (fun a Ha => or_introl Ha)) HK2).
- rewrite WS, HAS. lia.
- lia.
- intros a Ha. right. rewrite Hrq in Ha. lia.
- intros a Ha. apply HJpres2. rewrite WS in *. lia. }
clear TK. rename TK1 into TK.
assert (HEimg : forall a, in_img SEGS a -> ~ read_name_c.rn_writes c res kk a).
{ intros a Hi [Ha | Ha]; pose proof (pa_segs_low a Hi) as Hlow; unfold kLowMemEnd in *.
- lia.
- pose proof (pa_img_range a Hi) as Himg.
pose proof (blk_off_imgP B ly2 S2 W2 mem2 md2 res (kk + 1) HAR2 HresIn) as Hoff. rewrite Hrq in Hoff. lia. }
(* the cursor's two words, through the malloc (outside its stack window) *)
rewrite Uc, Z.add_0_r in VC0. rewrite Uc in VC8.
assert (VC0m : val_mem SEGS (mrestrict (w_H W2) mem2) c 8 (p' + kk)).
{ apply (rn_vm_move (w_H W) (ms_mem ms2) (w_H W2) mem2 c 8 (p' + kk)); [| exact VC0].
intros x Hx. simpl Z.of_nat in Hx. apply (proj1 HK2); rewrite ?HAS; lia. }
assert (VC8m : val_mem SEGS (mrestrict (w_H W2) mem2) (c + 8) 8 (m - kk)).
{ apply (rn_vm_move (w_H W) (ms_mem ms2) (w_H W2) mem2 (c + 8) 8 (m - kk)); [| exact VC8].
intros x Hx. simpl Z.of_nat in Hx. apply (proj1 HK2); rewrite ?HAS; lia. }
clear VC0 VC8. rename VC0m into VC0. rename VC8m into VC8.
(* re-seat the symbolic state on the kept stack frame *)
jafter_call_keep_pi HS 104%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0]%nat HS2.
lazymatch type of HS2 with ?Q -> _ => assert (HQ : Q) end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp; intros a Ha.
- apply (mbyte_of_aview SEGS). apply (proj1 HK2); [rewrite HAS in *; lia | rewrite HAS in *; lia].
- intros _. apply (apresent_writable SEGS). apply HJpres2. rewrite WS in *. lia. }
specialize (HS2 HQ). clear HQ. rewrite <- restrict_mkst_fx in HS2. clear HS. rename HS2 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => set (EA := Ex) in HS end.
assert (HEIA : img_env VAL A_LIM EA) by (subst EA; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDA : forall n, (n < 104)%nat -> ew EA n = ew E n) by (intros n Hn; subst EA; apply ew_havoc_old; lia).
assert (EAres : ew EA 108 = getr regs2 10)
by (subst EA; exact (ew_havoc_new E 104 (map (getr regs2) CLOB) 4 (Z_to_bv 64 0) ltac:(cbv; lia))).
assert (Ures : bv_unsigned (ew EA 108) = res)
by (rewrite EAres, Ha02; apply unsigned_lit_small; revert Hr4096 Hrceil Hkr C1; clear; intros; lia).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ss _ =>
pose proof (st_ok_pi_add_fact Ex ss _ 108%nat (mkAF 4096 RN_HI 4) HS
ltac:(unfold afact_ok, RN_HI; cbn [af_lo af_hi af_al2]; rewrite Ures; change (2 ^ 4) with 16;
revert Hr4096 Hrceil Hr16 C1 Hkr; clear; intros; repeat split; lia)) as HS3;
clear HS; rename HS3 into HS end.
assert (SHOKA : sh_ok SEGS RNx [] EA (mrestrict (w_H W2) mem2)) by apply Forall_nil.
assert (UspA : bv_unsigned (ew EA 2) = spZ regs) by (rewrite OLDA by lia; exact Usp).
assert (HAWRA : awr_ok EA [rn_mid_stack] STK sp0 FP (ablocks B ly S) (ablocks B ly2 S2) ly2 own).
{ eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spZ regs - sp0);
[reflexivity | rewrite UspA; lia | unfold rn_mid_stack; cbn [YP09.r_wlo]; lia
| unfold rn_mid_stack; cbn [YP09.r_whi]; lia | apply awr_ok_nil]. }
(* to the memcpy call at 0x81448 *)
paj_run_tok RUN HS HJ2 SHOKA RNspan.
{ exact HAWRA. }
rn_vmupd VC0. rn_vmupd VC8.
rn_tkupdB lyc Sc W memc mdc HARc (spZ regs) (read_name_c.rn_writes c res kk) HEimg TK HJ2.
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
(* the run naming shifts once the kept facts are threaded: bind the state at the memcpy call by hand *)
lazymatch type of HS with
| st_ok_pi _ _ _ _ (restrict _ ?msx) => set (ms3 := msx) in *
| st_ok _ _ _ (restrict _ ?msx) => set (ms3 := msx) in * end.

prreg HS (1%bv : bv 5) Qra. prreg HS (2%bv : bv 5) Qsp. prreg HS (3%bv : bv 5) Qgp.
prreg HS (4%bv : bv 5) Qtp. prreg HS (10%bv : bv 5) Qa0. prreg HS (11%bv : bv 5) Qa1.
prreg HS (12%bv : bv 5) Qa2.
pmkst HS.
pose proof (proj1 HJ2) as HAR3.
assert (HQsp : spZ (ms_regs ms3) = spZ regs - 48)
by (unfold spZ at 1; rewrite Qsp, UspA, unsigned_lit_small by lia; reflexivity).
assert (HQa1 : getr (ms_regs ms3) 11 = w64 p').
{ rewrite Qa1. unfold w64. rewrite <- Up', U_SOff, OLDA by lia. apply bv_eq.
rewrite !Z_to_bv_unsigned. unfold bv_wrap, zcanon, M64. change (bv_modulus 64) with (2 ^ 64).
symmetry. apply Zmod_mod. }
assert (HSEPsrc : 0 < kk -> res + kk <= p' \/ p' + kk <= res).
{ intros Hk1. destruct (HSRC Hk1) as (b0 & n0 & Hb0 & Hble & Hbhi).
destruct (in_split _ _ Hb0) as (l1 & l2 & Hsplit).
pose proof (sep_blocks_pos SEGS B LAWS ly2 S2 W2 (ms_mem ms3) _ (b0, n0) (res, kk + 1) l1 l2 [] HAR3
ltac:(rewrite Eab2, Hsplit, <- app_assoc; cbn [app]; reflexivity)) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. rewrite Hrq in D.
revert D Hble Hbhi Hk1. clear. intros. lia. }
assert (HSRCok : forall a, p' <= a < p' + kk -> aview SEGS (w_H W2) (ms_mem ms3) a <> None).
{ intros a Ha. assert (Hk1 : 0 < kk) by lia. destruct (HSRC Hk1) as (b0 & n0 & Hb0 & Hble & Hbhi).
assert (Hb2 : In (b0, n0) (ablocks B ly2 S2)) by (rewrite Eab2; apply in_or_app; left; exact Hb0).
destruct (al_blocks _ _ LAWS ly2 S2 W2 (ms_mem ms3) _ b0 n0 HAR3 Hb2) as (_ & _ & _ & _ & HbP & _).
apply (aview_some_of_apresent SEGS). apply (proj1 (HbP a ltac:(lia))). }
assert (HQa0 : getr (ms_regs ms3) 10 = w64 res) by (rewrite Qa0, EAres; exact Ha02).
assert (HQa2 : getr (ms_regs ms3) 12 = w64 kk) by (rewrite Qa2, OLDA by lia; exact E100).
assert (HSRCblk : 0 < kk -> exists b0 n0, In (b0, n0) (ablocks B ly2 S2) /\ b0 <= p' /\ p' + kk <= b0 + req_size n0
/\ b0 + req_size n0 <= alloc_ceiling).
{ intros Hk1. destruct (HSRC Hk1) as (b0 & n0 & Hb0 & Hble & Hbhi). exists b0, n0.
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b0 n0 HARc Hb0) as (_ & _ & Hbceil & _).
split; [rewrite Eab2; apply in_or_app; left; exact Hb0|]. lia. }
eapply SRr_bind.
{ eapply (aj_intrin_atS SEGS B LAWS Hsegs OCpy (SIGMA BB___asan_memcpy) AMEMCPY W2 (ms_regs ms3) (ms_mem ms3)
STK sp0 FP ly S W0 mem0 md0 own ly2 S2 _ (k + 1) res p' kk (spZ regs - 48 - sp0)
(Z_to_bv 64 (VAL A_TEXT + 5280)) HJ2).
- exact HQa0.
- exact HQa1.
- exact HQa2.
- lia.
- lia.
- revert Hrceil Hkr C1. clear. intros. lia.
- rewrite HQsp. lia.
- assert (Hq : spZ regs - 48 - sp0 = (spZ regs / 16 - 3 - sp0 / 16) * 16).
{ pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as D1. pose proof (Z.div_mod sp0 16 ltac:(lia)) as D2.
rewrite Hal16 in D1. rewrite Hal16' in D2. lia. }
rewrite Hq. apply Z_mod_mult.
- lia.
- rewrite HES, WS in *. lia.
- rewrite Qgp, OLDA, E3 by lia. exact Hgp.
- rewrite Qtp, OLDA, E4 by lia. exact Htp.
- exact Qra.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- intros a Ha. split.
+ replace a with (res + (a - res)) by lia.
exact (awr_new_block_any SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ res (kk + 1) (ablocks B ly2 S2)
(a - res) ly2 own HJ HAR2 Eab2 ltac:(lia) HresIn ltac:(rewrite Hrq; lia)).
+ rewrite HES in *. revert Ha Hrceil Hspc WS C1. clear. intros. lia.
- apply (amem_range_of_block SEGS B LAWS ly2 S2 W2 (ms_mem ms3) _ res (kk + 1) res kk HAR3 HresIn); rewrite ?Hrq; lia.
- apply (range_addressable_of_block SEGS B LAWS ly2 S2 W2 (ms_mem ms3) _ res (kk + 1) res kk HAR3 HresIn);
rewrite ?Hrq; lia.
- intros Hk1. apply (shadow_hull_vis_of_block SEGS B LAWS ly2 S2 W2 (ms_mem ms3) _ res (kk + 1) res kk HAR3 HresIn);
rewrite ?Hrq; lia.
- split; [lia|]. split; [lia|]. split.
{ intros a Ha. assert (Hk1 : 0 < kk) by lia. split; [exact (HSRCok a Ha)|].
destruct (HSRCblk Hk1) as (b0 & n0 & _ & Hble & Hbhi & Hbceil).
rewrite HQsp, HES, WS in *. revert Ha Hble Hbhi Hbceil Hspc. clear. intros. lia. }
split; [destruct (Z.eq_dec kk 0) as [Hkz | Hkz]; [lia | apply HSEPsrc; lia]|].
split; [exact HAMR|]. split.
{ destruct (Z.eq_dec kk 0) as [Hkz | Hkz]; [intros x Hx; lia|].
destruct (HSRCblk ltac:(lia)) as (b0 & n0 & Hb2 & Hble & Hbhi & _).
apply (range_addressable_of_block SEGS B LAWS ly2 S2 W2 (ms_mem ms3) _ b0 n0 p' kk HAR3 Hb2); lia. }
intros Hk1. destruct (HSRCblk Hk1) as (b0 & n0 & Hb2 & Hble & Hbhi & _).
apply (shadow_hull_vis_of_block SEGS B LAWS ly2 S2 W2 (ms_mem ms3) _ b0 n0 p' kk HAR3 Hb2); lia. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Ha03 & Heff3 & Hfr3 & Hpres3 & HSM3).
(* re-seat on the kept stack frame again *)
jafter_call_keep_pi HS 120%nat regs3 (mrestrict (w_H W2) mem3) HP3 [0]%nat HS4.
lazymatch type of HS4 with ?Q -> _ => assert (HQ : Q) end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite UspA; intros a Ha.
- apply (mbyte_of_aview SEGS). apply Hfr3;
revert Ha Hspc Hrceil Hkr Hhi Hshi H47 Hceil Hslo WS HES C1; clear; intros; lia.
- intros _. apply (apresent_writable SEGS). apply Hpres3.
pose proof (proj1 HJ2) as HARx. pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpx & _).
apply Hpx. rewrite WS in *. lia. }
specialize (HS4 HQ). clear HQ. rewrite <- restrict_mkst_fx in HS4. clear HS. rename HS4 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => set (EB := Ex) in HS end.
assert (HEIB : img_env VAL A_LIM EB) by (subst EB; apply img_env_havoc; [exact HEIA | cbv; lia]).
assert (OLDB : forall n, (n < 120)%nat -> ew EB n = ew EA n) by (intros n Hn; subst EB; apply ew_havoc_old; lia).
pose proof (proj1 HJ3) as HAR4.
(* the NUL store at s + k: a fresh atom 150 for its address, with the alias the engine folds through *)
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ss _ =>
pose proof (st_ok_pi_havoc 150%nat Ex ss _ [Z_to_bv 64 (res + kk)] HS
ltac:(vm_compute; reflexivity) ltac:(cbv; lia)) as HS5; clear HS; rename HS5 into HS end.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => set (EC := Ex) in HS end.
assert (HEIC : img_env VAL A_LIM EC) by (subst EC; apply img_env_havoc; [exact HEIB | cbv; lia]).
assert (OLDC : forall n, (n < 150)%nat -> ew EC n = ew EB n) by (intros n Hn; subst EC; apply ew_havoc_old; lia).
assert (EC150 : ew EC 150 = Z_to_bv 64 (res + kk))
by (subst EC; exact (ew_havoc_new EB 150 [Z_to_bv 64 (res + kk)] 0 (Z_to_bv 64 0) ltac:(cbv; lia))).
assert (Hrng : 0 <= res + kk < 2 ^ 64) by (revert Hr4096 Hrceil Hkr C1; clear; intros; lia).
assert (U150 : U EC (SOff 150 0) = res + kk) by (apply (U_atom EC 150%nat (res + kk) EC150); lia).
assert (U108 : U EC (SOff 108 0) = res).
{ apply (U_atom EC 108%nat res); [rewrite OLDC by lia; rewrite OLDB by lia; rewrite EAres; exact Ha02 | lia]. }
assert (U100C : U EC (SOff 100 0) = kk).
{ apply (U_atom EC 100%nat kk); [rewrite OLDC by lia; rewrite OLDB by lia; exact E100 | lia]. }
(* the alias and the one-byte region at s + k *)
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ss _ =>
pose proof (st_ok_pi_add_alias Ex ss _ (SAlu ALU_ADD (SOff 108 0) (SOff 100 0)) (SOff 150 0) HS
ltac:(apply U_inj; rewrite U_SAlu, U108, U100C, U150; cbn [zalu_raw]; apply zcanon_id; unfold M64; lia))
as HS6; clear HS; rename HS6 into HS end.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ss ?msx =>
pose proof (st_ok_pi_add_region Ex ss msx (YP09.mkRegion (Some 150%nat) 0 1 0 1 []) HS) as HADD end.
specialize (HADD ltac:(vm_compute; reflexivity)).
lazymatch type of HADD with ?Q -> _ => assert (HRO : Q) end.
{ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite EC150, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [| apply Forall_nil].
intros o Ho. apply (apresent_writable SEGS).
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem3 md3 res (kk + 1) HAR4 HresIn) as (_ & _ & _ & _ & HrP3 & _).
rewrite Hrq in HrP3. apply (proj1 (HrP3 (res + kk + o) ltac:(lia))). }
specialize (HADD HRO). clear HRO.
lazymatch type of HADD with ?Q -> _ => assert (HDJ : Q) end.
{ cbn [ss_mem set_facts]. unfold rn_mid_stack. cbn [all_disjoint].
split; [|exact I]. unfold extent_disjoint. cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi].
rewrite EC150, unsigned_lit_small by lia.
rewrite OLDC by lia. rewrite OLDB by lia. rewrite UspA.
revert Hr4096 Hrceil Hkr Hspc WS C1. clear. intros. lia. }
specialize (HADD HDJ). clear HDJ HS. rename HADD into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ss _ =>
pose proof (st_ok_pi_add_fact Ex ss _ 150%nat (mkAF 4096 RN_HI 0) HS
ltac:(unfold afact_ok, RN_HI; cbn [af_lo af_hi af_al2]; rewrite EC150, unsigned_lit_small by lia;
rewrite Z.pow_0_r, Z.mod_1_r; revert Hr4096 Hrceil Hkr C1; clear; intros; lia)) as HS8;
clear HS; rename HS8 into HS end.
assert (EC32 : ew EC 32 = w64 RN_SB)
by (rewrite OLDC by lia; rewrite OLDB by lia; rewrite OLDA by lia; exact E32).
assert (SHOK3 : sh_ok SEGS RNx [mkSHE 150 0 1] EC (mrestrict (w_H W2) mem3)).
{ unfold sh_ok. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W2) mem3 EC RNx 150 res (kk + 1) (res + kk) 0 1).
- apply (range_addressable_of_block SEGS B LAWS ly2 S2 W2 mem3 md3 res (kk + 1) res (kk + 1) HAR4 HresIn);
rewrite ?Hrq; lia.
- unfold U, RNx. cbn [sv_denot]. rewrite EC32. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite unsigned_lit_small by (unfold RN_SB; lia). unfold RN_SB, SHADOW_OFF. reflexivity.
- exact U150.
- lia.
- lia.
- intros y Hy. cbn [Z.min Z.max] in Hy.
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem3 md3 res (kk + 1) HAR4 HresIn) as (_ & _ & _ & Happ & _).
rewrite Hrq in Happ. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *.
revert Hy Happ Hkr C3. clear. intros. lia. }
(* the NUL store, then the return *)
paj_run_tok RUN HS HJ3 SHOK3 RNspan.
{ lazymatch goal with |- awr_ok _ ?rs _ _ _ _ _ _ _ =>
let rs' := eval vm_compute in rs in change rs with rs' end.
eapply awr_ok_cons_gen with (n := 150%nat) (b := res + kk);
[reflexivity | rewrite EC150; apply unsigned_lit_small; lia | | ].
- intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
replace a with (res + (a - res)) by lia.
exact (awr_new_block_any SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ res (kk + 1) (ablocks B ly2 S2)
(a - res) ly2 own HJ HAR2 Eab2 ltac:(lia) HresIn ltac:(rewrite Hrq; lia)).
- eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spZ regs - sp0);
[reflexivity | rewrite OLDC by lia; rewrite OLDB by lia; rewrite UspA; lia
| unfold rn_mid_stack; cbn [YP09.r_wlo]; lia | unfold rn_mid_stack; cbn [YP09.r_whi]; lia | apply awr_ok_nil]. }
lazymatch goal with HFrx : frame_of _ _ _ _ |- _ => rename HFrx into FRa end.
lazymatch goal with HGx : mem_grows _ _ |- _ => rename HGx into GRa end.
pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => (spZ regs - 48 <= a < spZ regs) \/ (res + kk <= a < res + kk + 1)) FRa
ltac:(intros bb wlo whi aa Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; unfold base_val in Hrr;
rewrite ?EC150 in Hrr; rewrite ?unsigned_lit_small in Hrr by lia;
rewrite ?OLDC in Hrr by lia; rewrite ?OLDB in Hrr by lia; rewrite ?UspA in Hrr; clear - Hrr; lia |]); destruct Hin)) as UNEa.
(* 0x81450 bltu a0, s0: the trap side is impossible *)
psrr_branch_tok RUN BR HS SHOK3 RNspan.
{ exfalso. lazymatch goal with
| H : branch_taken BC_LTU (sv_denot ?Ex (SAlu ALU_XOR _ _)) _ = true |- _ =>
rewrite (rn_not_ok Ex res kk U108 U100C ltac:(lia) ltac:(unfold RN_HI in *; lia) ltac:(lia)) in H; discriminate
end. }
(* to the return at 0x81488 *)
paj_run_tok RUN HS HJ3 SHOK3 RNspan.
{ lazymatch goal with |- awr_ok _ ?rs _ _ _ _ _ _ _ =>
let rs' := eval vm_compute in rs in change rs with rs' end.
eapply awr_ok_cons_gen with (n := 150%nat) (b := res + kk);
[reflexivity | rewrite EC150; apply unsigned_lit_small; lia | | ].
- intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
replace a with (res + (a - res)) by lia.
exact (awr_new_block_any SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ res (kk + 1) (ablocks B ly2 S2)
(a - res) ly2 own HJ HAR2 Eab2 ltac:(lia) HresIn ltac:(rewrite Hrq; lia)).
- eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spZ regs - sp0);
[reflexivity | rewrite OLDC by lia; rewrite OLDB by lia; rewrite UspA; lia
| unfold rn_mid_stack; cbn [YP09.r_wlo]; lia | unfold rn_mid_stack; cbn [YP09.r_whi]; lia | apply awr_ok_nil]. }
lazymatch type of HS with
| st_ok_pi _ _ _ _ (restrict _ ?msx) => set (ms5 := msx) in *
| st_ok _ _ _ (restrict _ ?msx) => set (ms5 := msx) in * end.
match goal with HFrx : frame_of _ _ _ _ |- _ =>
lazymatch HFrx with FRa => fail | _ => rename HFrx into FRb end end.
match goal with HGx : mem_grows _ _ |- _ =>
lazymatch HGx with GRa => fail | _ => rename HGx into GRb end end.
pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => (spZ regs - 48 <= a < spZ regs) \/ (res + kk <= a < res + kk + 1)) FRb
ltac:(intros bb wlo whi aa Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; unfold base_val in Hrr;
rewrite ?EC150 in Hrr; rewrite ?unsigned_lit_small in Hrr by lia;
rewrite ?OLDC in Hrr by lia; rewrite ?OLDB in Hrr by lia; rewrite ?UspA in Hrr; clear - Hrr; lia |]); destruct Hin)) as UNE.
(* ---- the post at the ret 0x81488 ---- *)
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres5 & _).
assert (E1 : ew E 1 = getr regs 1)
by (rewrite (proj1 HAE 1%nat ltac:(lia)); apply (ew_Ereg_nat regs [] 1 1%bv); reflexivity).
assert (Hp'ceil : 0 < kk -> p' + kk <= alloc_ceiling).
{ intros Hk1. destruct (HSRCblk Hk1) as (b0 & n0 & _ & Hble & Hbhi & Hbceil). lia. }
(* what the memcpy and the two runs after it kept *)
assert (KQ : forall a, 0 <= a < 2 ^ 64 -> ~ read_name_c.rn_writes c res kk a ->
~ (spZ regs - READ_NAME_STKB <= a < spZ regs) ->
aview SEGS (w_H W2) (ms_mem ms5) a = aview SEGS (w_H W2) (ms_mem ms3) a).
{ intros a Ha HnE Hnw. unfold read_name_c.rn_writes in HnE.
rewrite (UNE a Ha ltac:(cbv beta; lia)), (UNEa a Ha ltac:(cbv beta; lia)).
apply Hfr3; [exact Ha | revert HnE; clear; intros; lia | revert Hnw WS HES; clear; intros; lia]. }
assert (PQ : forall a, apresent (w_H W2) (ms_mem ms3) a -> apresent (w_H W2) (ms_mem ms5) a).
{ intros a Hp. eapply apresent_grows; [exact GRb|]. eapply apresent_grows; [exact GRa|].
apply Hpres3. exact Hp. }
assert (TK2 : tbcj_kept B READ_NAME_STKB lyc Sc W memc W2 (ms_mem ms5) (spZ regs)
(read_name_c.rn_writes c res kk)).
{ apply (tk_step READ_NAME_STKB lyc Sc W memc W2 (ms_mem ms3) W2 (ms_mem ms5) (spZ regs) _ mdc HARc
ltac:(rewrite WS, HAS in *; lia) HEimg TK KQ PQ).
intros a Ha. apply Hpres5. revert Ha Hlo Hhi WS; clear; intros; lia. }
(* the caller's cursor, moved from the memcpy call to the return *)
assert (HCK : forall a, c <= a < c + 16 ->
aview SEGS (w_H W2) (ms_mem ms5) a = aview SEGS (w_H W2) (ms_mem ms3) a).
{ intros a Ha.
rewrite (UNE a ltac:(lia) ltac:(cbv beta; lia)), (UNEa a ltac:(lia) ltac:(cbv beta; lia)).
apply Hfr3; lia. }
assert (VC0f : val_mem SEGS (mrestrict (w_H W2) (ms_mem ms5)) c 8 (p + tbread_name_used pl)).
{ replace (p + tbread_name_used pl) with (p' + kk) by (unfold tbread_name_used; lia).
apply (rn_vm_move (w_H W2) (ms_mem ms3) (w_H W2) (ms_mem ms5) c 8 (p' + kk)); [| exact VC0].
intros x Hx. simpl Z.of_nat in Hx. apply HCK. lia. }
assert (VC8f : val_mem SEGS (mrestrict (w_H W2) (ms_mem ms5)) (c + 8) 8
(Z.of_nat (length pl) - tbread_name_used pl)).
{ replace (Z.of_nat (length pl) - tbread_name_used pl) with (m - kk) by (unfold tbread_name_used; lia).
apply (rn_vm_move (w_H W2) (ms_mem ms3) (w_H W2) (ms_mem ms5) (c + 8) 8 (m - kk)); [| exact VC8].
intros x Hx. simpl Z.of_nat in Hx. apply HCK. lia. }
(* the k copied name bytes: the memcpy's source is still the caller's input block *)
assert (HOLDN : forall i, 0 <= i < kk ->
aview SEGS (w_H W2) (ms_mem ms3) (p' + i) = aview SEGS (w_H W) memc (p' + i)).
{ intros i Hi. pose proof (Hp'ceil ltac:(lia)) as Hpc.
destruct (HSRC ltac:(lia)) as (b0 & n0 & Hb0 & Hble & Hbhi).
destruct (in_split _ _ Hb0) as (l1 & l2 & Hsplit).
pose proof (sep_blocks_pos SEGS B LAWS ly2 S2 W2 mem2 _ (b0, n0) (res, kk + 1) l1 l2 [] HAR2
ltac:(rewrite Eab2, Hsplit, <- app_assoc; cbn [app]; reflexivity)) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. rewrite Hrq in D.
replace (p' + i) with (b0 + (p' + i - b0)) by lia.
apply (proj1 (proj2 TK) b0 n0 (p' + i - b0) Hb0 ltac:(lia)).
intros Hbad. unfold read_name_c.rn_writes in Hbad.
revert D Hbad Hi Hble Hbhi Hpc Hcsp Hspc WS. clear. intros. lia. }
assert (HNAME : forall i, 0 <= i < kk -> aview SEGS (w_H W2) (ms_mem ms5) (res + i) =
Some (bv_unsigned (nth (Z.to_nat i) (Boxreg.bsub pl 1 kk ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)))).
{ intros i Hi.
rewrite (UNE (res + i) ltac:(lia) ltac:(cbv beta; lia)), (UNEa (res + i) ltac:(lia) ltac:(cbv beta; lia)).
rewrite (Heff3 i Hi), (HOLDN i Hi). exact (HBYTES i Hi). }
assert (Hblen : length (Boxreg.bsub pl 1 kk) = Z.to_nat kk).
{ unfold Boxreg.bsub. rewrite length_firstn, length_skipn. revert Hkm Hm Hkr. clear. intros. lia. }
(* the terminating NUL at s + k, from the one-byte region the store left *)
lazymatch type of HS with st_ok_pi _ _ ?Ef ?ssf ?msr =>
let rr0 := eval vm_compute in (nth_error (ss_mem ssf) 0) in
lazymatch rr0 with Some ?r0 => pose proof (st_ok_pi_region_nth Ef ssf msr 0 r0 HS eq_refl) as HRS end;
assert (Ub150 : bv_unsigned (ew Ef 150) = res + kk)
by (rewrite !ew_ewset_other by lia; rewrite EC150; apply unsigned_lit_small; lia);
assert (VSN : aview SEGS (w_H W2) (ms_mem ms5) (res + kk) = Some (bv_unsigned (Z_to_bv 8 0)));
[ pose proof (field_of_region Ef _ 150%nat (res + kk) _ _ _ _ _ 0 1%N (SLit 0) 0 HRS Ub150
ltac:(cbn [In]; auto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V;
specialize (V 0%nat ltac:(cbn; lia));
change (res + kk + 0 + Z.of_nat 0) with (res + kk + 0 + 0) in V;
rewrite !Z.add_0_r in V; unfold aview; cbn [ms_mem restrict] in V; rewrite V; reflexivity
| ] end.
(* the return *)
prreg HS (1%bv : bv 5) R1. prreg HS (10%bv : bv 5) R10.
eapply (RET W2 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)); intros mat'.
unfold tbread_name_post.
exists ly2, S2, (ms_regs ms5), (ms_mem ms5); eexists; exists res.
split; [rewrite R1; rewrite ?ew_ewset_other by lia; rewrite OLDC by lia; rewrite OLDB by lia;
rewrite OLDA by lia; rewrite E1, Hraok; reflexivity|].
split; [replace (k + EV_READ_NAMEB) with (k + 1) by (unfold EV_READ_NAMEB; lia);
apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ3|].
split; [lazymatch type of HS with st_ok_pi _ _ ?Ef _ _ =>
eapply (aregs_preserved_of_st_ok SEGS _ Ef _ _ regs (@nil word) HS);
[ eapply env_agree_trans; [exact HAE|];
split; [intros n Hn; rewrite !ew_ewset_other by lia; rewrite OLDC by lia; rewrite OLDB by lia;
rewrite OLDA by lia; reflexivity | reflexivity]
| vm_compute; reflexivity ] end|].
split; [rewrite R10; rewrite ?ew_ewset_other by lia; rewrite OLDC by lia; rewrite OLDB by lia;
rewrite EAres; exact Ha02|].
split; [exact Hfrs2|].
split; [exact Hr4096|].
split; [rewrite <- Hkk; exact Eab2|].
split; [intros blc i Hin Hi; rewrite <- Hkk in Hin, Hi;
exact (awr_new_block_any SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ res (kk + 1) blc i ly2 own
HJ HAR2 Eab2 ltac:(lia) Hin ltac:(rewrite Hrq; lia))|].
split; [rewrite <- Hkk; eapply (aftok_new_block SEGS B LAWS); [exact HJ | exact HAR2 | exact Eab2 | lia]|].
split; [intros i Hi; rewrite <- Hkk in Hi |- *;
destruct (Z.eq_dec i kk) as [-> | Hne];
[ rewrite app_nth2 by (rewrite Hblen; lia); rewrite Hblen;
replace (Z.to_nat kk - Z.to_nat kk)%nat with 0%nat by lia; cbn [nth]; exact VSN
| exact (HNAME i ltac:(lia)) ]|].
split; [exact VC0f|].
split; [exact VC8f|].
split; [rewrite <- Hkk; exact MLE2|].
rewrite <- Hkk. exact TK2.
Qed.
(* The name's bytes for a non-empty input: the k bytes after the length byte (lib/A/Prog/ReadName.v:577). *)
Lemma rn_bsub_nthB : forall (b0 : byte) rest i, 0 <= i < read_name_c.rn_k (b0 :: rest) ->
nth (Z.to_nat i) (Boxreg.bsub (b0 :: rest) 1 (read_name_c.rn_k (b0 :: rest)) ++ [Z_to_bv 8 0]) (Z_to_bv 8 0) =
nth (Z.to_nat (1 + i)) (b0 :: rest) (Z_to_bv 8 0).
Proof.
intros b0 rest i Hi.
assert (Hk : read_name_c.rn_k (b0 :: rest) <= Z.of_nat (length rest)).
{ change (read_name_c.rn_k (b0 :: rest)) with (Z.min (bv_unsigned b0 mod 48) (Z.of_nat (length rest))). lia. }
unfold Boxreg.bsub. rewrite app_nth1.
- rewrite nth_firstn. destruct (Nat.ltb_spec (Z.to_nat i) (Z.to_nat (read_name_c.rn_k (b0 :: rest)))); [|lia].
rewrite nth_skipn. replace (Z.to_nat 1 + Z.to_nat i)%nat with (Z.to_nat (1 + i)) by lia. reflexivity.
- rewrite length_firstn, length_skipn. cbn [length]. lia.
Qed.
(* The right to write the regions at the entry: the own frame, the cursor (tbwr_ok), read-only ones. *)
Ltac rn_awrB c sp sp0 Uc Usp HWR :=
lazymatch goal with |- awr_ok ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?lyx ?ownx =>
let rs' := eval vm_compute in rsx in change (awr_ok Ex rs' stkx spx fpx b0x bcx lyx ownx) end;
repeat first
[ apply awr_ok_nil
| apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
| eapply awr_ok_cons_gen with (n := 10%nat) (b := c);
[reflexivity | exact Uc | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; exact (proj1 (HWR a ltac:(lia))) |]
| eapply awr_ok_cons_stack_off with (n := 2%nat) (d := sp - sp0);
[reflexivity | etransitivity; [exact Usp | lia] | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |] ].
Theorem pb_bread_name : tbread_name_spec B MT.
Proof.
unfold tbread_name_spec.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs c p bi Li pl
HJc Hraok Hra4 Hgp Htp Hal16 Hlo Hhi H10 Hc8 Hcsp Hvp Hvn HRA HWR Hp0 Hpn Hamr Hblk Hbytes Hev Hlive MOK HUNIV.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : READ_NAME_STKB = 16432) by reflexivity.
assert (HAS : ASTACK = 16384) by reflexivity.
pose proof HJc as (HARc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16' & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (Hsp0 : 0 <= spZ regs) by (unfold spZ; pose proof (bv_unsigned_in_range 64 (getr regs 2)); lia).
assert (Hchi : c + 16 <= sp0).
{ destruct (HWR (c + 15) ltac:(lia)) as (Hw & _).
pose proof (rn_awr_above _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc Hw). lia. }
assert (Hcpres : forall a, c <= a < c + 16 -> apresent (w_H W) memc a)
by (intros a Ha; exact (proj1 (proj2 (HWR a Ha)))).
pose proof (tk_init READ_NAME_STKB lyc Sc W memc (spZ regs) (fun a => c <= a < c + 16)
ltac:(intros a Ha; apply Hpres; lia)) as TK.
assert (HEimg0 : forall a, in_img SEGS a -> ~ (fun a : Z => c <= a < c + 16) a)
by (intros a Hi Ha; pose proof (pa_segs_low a Hi); unfold kLowMemEnd in *; cbv beta in Ha; lia).
unfold cfg_at. change (w64 AB_read_nameP) with (Z_to_bv 64 AB_read_nameP).
destruct pl as [|b0 rest].
- (* the empty input: the cursor holds { p, 0 } *)
destruct (rn_entry0 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs c p HJc Hal16 Hlo Hhi H10 Hc8 Hcsp Hchi
Hvp Hvn HRA Hcpres Hp0 ltac:(lia)) as [HS SHOK].
set (E := RNE0 regs p) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E, RNE0; apply Eimg_env).
assert (EE : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E i = getr regs r)
by (intros i r Hi; unfold E, RNE0; apply ew_Eimg_Ereg_nat; exact Hi).
assert (E2 : ew E 2 = getr regs 2) by (apply (EE 2%nat 2%bv); reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 c) by (rewrite (EE 10%nat 10%bv eq_refl); exact H10).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (Uc : bv_unsigned (ew E 10) = c) by (rewrite E10; apply unsigned_lit_small; lia).
paj_run_tok RUN HS HJc SHOK RNspan.
{ rn_awrB c (spZ regs) sp0 Uc Usp HWR. }
rn_tkupdB lyc Sc W memc mdc HARc (spZ regs) (fun a : Z => c <= a < c + 16) HEimg0 TK HJc.
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
(* 0x81360 beqz a2: n = 0, the branch to 0x813d4 is taken *)
assert (EX : forall j, (j < 3)%nat ->
ew E (32 + j) = nth j [Z_to_bv 64 RN_SB; Z_to_bv 64 (p - 1); Z_to_bv 64 1] (Z_to_bv 64 0))
by (intros j Hj; unfold E, RNE0; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 2%nat ltac:(lia)) as E34. cbn [nth Nat.add] in E32, E33, E34.
assert (U34 : U E (SOff 34 (-1)) = 0) by (rewrite U_SOff, E34, unsigned_lit_small by lia; reflexivity).
psrr_branch_tok RUN BR HS SHOK RNspan.
2: { exfalso. rewrite branch_eq_U, U34, U_lit in Hc by lia. vm_compute in Hc. discriminate. }
paj_run_to_tok RUNTO HS HJc SHOK RNspan 5184.
{ rn_awrB c (spZ regs) sp0 Uc Usp HWR. }
rn_tkupdB lyc Sc W memc mdc HARc (spZ regs) (fun a : Z => c <= a < c + 16) HEimg0 TK HJc.
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
(* re-seat at 0x813ec: k = 0 in atom 100, registers 15-17 (dead) in atoms 101-103 *)
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) => set (msM := msx) in * end.
pose proof (st_ok_pi_havoc 100%nat E _ _
[Z_to_bv 64 0; getr (ms_regs msM) 15; getr (ms_regs msM) 16; getr (ms_regs msM) 17] HS
ltac:(vm_compute; reflexivity) ltac:(cbv; lia)) as HS1.
clear HS. rename HS1 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => set (E' := Ex) in HS end.
assert (HEI' : img_env VAL A_LIM E') by (subst E'; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDM : forall n, (n < 100)%nat -> ew E' n = ew E n) by (intros n Hn; subst E'; apply ew_havoc_old; lia).
assert (EM100 : ew E' 100 = Z_to_bv 64 0)
by (subst E'; exact (ew_havoc_new E 100
[Z_to_bv 64 0; getr (ms_regs msM) 15; getr (ms_regs msM) 16; getr (ms_regs msM) 17] 0 (Z_to_bv 64 0)
ltac:(cbn [length]; lia))).
assert (EM101 : ew E' 101 = getr (ms_regs msM) 15)
by (subst E'; exact (ew_havoc_new E 100
[Z_to_bv 64 0; getr (ms_regs msM) 15; getr (ms_regs msM) 16; getr (ms_regs msM) 17] 1 (Z_to_bv 64 0)
ltac:(cbn [length]; lia))).
assert (EM102 : ew E' 102 = getr (ms_regs msM) 16)
by (subst E'; exact (ew_havoc_new E 100
[Z_to_bv 64 0; getr (ms_regs msM) 15; getr (ms_regs msM) 16; getr (ms_regs msM) 17] 2 (Z_to_bv 64 0)
ltac:(cbn [length]; lia))).
assert (EM103 : ew E' 103 = getr (ms_regs msM) 17)
by (subst E'; exact (ew_havoc_new E 100
[Z_to_bv 64 0; getr (ms_regs msM) 15; getr (ms_regs msM) 16; getr (ms_regs msM) 17] 3 (Z_to_bv 64 0)
ltac:(cbn [length]; lia))).
pose proof (st_ok_pi_restrict_reg _ _ _ _ 8%bv HS) as R8.
lazymatch type of R8 with _ = sv_denot _ ?e => let e' := eval vm_compute in e in change e with e' in R8 end.
assert (D8 : getr (ms_regs msM) 8 = sv_denot E' (SOff 100 0)).
{ rewrite R8. apply bv_eq. change (U E' (SOff 34 (-1)) = U E' (SOff 100 0)).
rewrite !U_SOff, OLDM by lia. rewrite E34, EM100, !unsigned_lit_small by lia. reflexivity. }
assert (D15 : getr (ms_regs msM) 15 = sv_denot E' (SOff 101 0))
by (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, EM101; reflexivity).
assert (D16 : getr (ms_regs msM) 16 = sv_denot E' (SOff 102 0))
by (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, EM102; reflexivity).
assert (D17 : getr (ms_regs msM) 17 = sv_denot E' (SOff 103 0))
by (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, EM103; reflexivity).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msr =>
pose proof (st_ok_pi_set_reg Ex ssx msr 8%bv (SOff 100 0) HS
ltac:(intros Hq; apply (f_equal bv_unsigned) in Hq; vm_compute in Hq; discriminate) D8) as HS1 end.
clear HS. rename HS1 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msr =>
pose proof (st_ok_pi_set_reg Ex ssx msr 15%bv (SOff 101 0) HS
ltac:(intros Hq; apply (f_equal bv_unsigned) in Hq; vm_compute in Hq; discriminate) D15) as HS1 end.
clear HS. rename HS1 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msr =>
pose proof (st_ok_pi_set_reg Ex ssx msr 16%bv (SOff 102 0) HS
ltac:(intros Hq; apply (f_equal bv_unsigned) in Hq; vm_compute in Hq; discriminate) D16) as HS1 end.
clear HS. rename HS1 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msr =>
pose proof (st_ok_pi_set_reg Ex ssx msr 17%bv (SOff 103 0) HS
ltac:(intros Hq; apply (f_equal bv_unsigned) in Hq; vm_compute in Hq; discriminate) D17) as HS1 end.
clear HS. rename HS1 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msr =>
pose proof (st_ok_pi_submem Ex ssx msr [rn_mid_stack; rn_cur0] HS ltac:(vm_compute; submem_tac) eq_refl) as HS1 end.
clear HS. rename HS1 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msr =>
pose proof (st_ok_pi_pick_facts Ex ssx msr [0%nat; 1%nat; 2%nat] [] [] HS) as HS1 end.
clear HS. rename HS1 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msr =>
pose proof (st_ok_pi_add_fact Ex ssx msr 100%nat FK HS
ltac:(unfold afact_ok, FK; cbn [af_lo af_hi af_al2]; rewrite EM100, unsigned_lit_small by (clear; lia);
rewrite Z.pow_0_r, Z.mod_1_r; clear; lia)) as HS1 end.
clear HS. rename HS1 into HS.
assert (HSM : st_ok_pi SEGS VAL E' ss_mid (restrict (w_H W) msM)).
{ lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ =>
let v := eval vm_compute in ssx in change ssx with v in HS end.
exact HS. }
clear HS.
assert (SHOK' : sh_ok SEGS RNx rn_SH E' (mrestrict (w_H W) (ms_mem msM))).
{ eapply sh_ok_agree with (k := 100%nat) (E := E); [ idtac .. | exact SHOK ].
all: first [ split; [intros n Hn; apply OLDM; exact Hn | subst E'; reflexivity] | reflexivity ]. }
assert (HAE' : env_agree 32 (Ereg regs []) E').
{ split.
- intros n Hn. rewrite OLDM by lia. unfold E, RNE0. rewrite Eimg_low by (unfold A_TEXT; lia).
do 32 (destruct n as [|n]; [reflexivity|]). lia.
- subst E'. unfold E, RNE0. reflexivity. }
assert (Up : U E' (SOff 33 1) = p).
{ rewrite U_SOff, OLDM by lia. rewrite E33. unfold zcanon, M64. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). rewrite Zplus_mod_idemp_l. replace (p - 1 + 1) with p by lia.
apply Z.mod_small. lia. }
assert (Um : U E' (SOff 34 (-1)) = 0) by (rewrite U_SOff, OLDM, E34, unsigned_lit_small by lia; reflexivity).
eapply (rn_tail STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc _ k regs E' msM c p p 0 0 []).
+ exact HJc.
+ exact HARc.
+ exact HSM.
+ exact SHOK'.
+ exact HEI'.
+ exact HAE'.
+ exact TK.
+ rewrite OLDM by lia. exact E10.
+ rewrite OLDM by lia. exact E32.
+ exact EM100.
+ exact Up.
+ exact Um.
+ exact Hraok.
+ exact Hra4.
+ exact Hgp.
+ exact Htp.
+ exact Hal16.
+ exact Hlo.
+ exact Hhi.
+ exact Hc8.
+ exact Hcsp.
+ exact Hchi.
+ exact HWR.
+ reflexivity.
+ cbn [length Z.of_nat]. lia.
+ cbn [length Z.of_nat]. lia.
+ lia.
+ lia.
+ lia.
+ exact Hp0.
+ cbn [length Z.of_nat] in Hpn. lia.
+ intros; exfalso; lia.
+ exact Hamr.
+ intros; exfalso; lia.
+ intros i Hi; exfalso; lia.
+ exact Hev.
+ exact Hlive.
+ exact MOK.
+ exact HUNIV.
- (* a non-empty input: the length byte x at p, the n - 1 bytes after it *)
destruct (Hblk ltac:(discriminate)) as (Hbin & Hbi & Hbe).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bi Li HARc Hbin) as (_ & Hb4096 & Hbceil & _).
assert (HLi : Li <= req_size Li) by (unfold req_size; destruct (Z.eqb_spec Li 0); lia).
pose proof (blk_off_imgP B lyc Sc W memc mdc bi Li HARc Hbin) as Hoff.
set (n := Z.of_nat (length (b0 :: rest))) in *.
assert (Hn1 : 1 <= n) by (unfold n; cbn [length]; lia).
set (xb := bv_unsigned b0).
assert (Hx : aview SEGS (w_H W) memc p = Some xb)
by (replace p with (p + 0) by lia; rewrite (Hbytes 0 ltac:(lia)); reflexivity).
assert (Hxr : 0 <= xb < 256)
by (unfold xb; pose proof (bv_unsigned_in_range 8 b0) as Hr8; change (bv_modulus 8) with 256 in Hr8; lia).
destruct (rn_entry STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs c p n xb HJc Hal16 Hlo Hhi H10 Hc8 Hcsp Hchi
Hvp Hvn HRA Hcpres ltac:(lia) ltac:(lia) ltac:(lia) Hn1 Hx Hxr) as [HS SHOK].
set (E := RNE regs p n xb) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E, RNE; apply Eimg_env).
assert (EE : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E i = getr regs r)
by (intros i r Hi; unfold E, RNE; apply ew_Eimg_Ereg_nat; exact Hi).
assert (EX : forall j, (j < 4)%nat ->
ew E (32 + j) = nth j [Z_to_bv 64 RN_SB; Z_to_bv 64 p; Z_to_bv 64 n; Z_to_bv 64 xb] (Z_to_bv 64 0))
by (intros j Hj; unfold E, RNE; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
cbn [nth Nat.add] in E32, E33, E34, E35.
assert (E2 : ew E 2 = getr regs 2) by (apply (EE 2%nat 2%bv); reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 c) by (rewrite (EE 10%nat 10%bv eq_refl); exact H10).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (Uc : bv_unsigned (ew E 10) = c) by (rewrite E10; apply unsigned_lit_small; lia).
paj_run_tok RUN HS HJc SHOK RNspan.
{ (* 0x813a4: the load1 check of the length byte at p (ASan #5); its shadow is the input block's *)
cbn [ms_mem mkst].
assert (UB : U E RNx = SHADOW_OFF)
by (unfold RNx; rewrite U_SOff, E32, unsigned_lit_small by (unfold RN_SB; lia); unfold RN_SB, SHADOW_OFF; reflexivity).
assert (UP : U E (SOff 33 0) = p)
by (rewrite U_SOff, E33, unsigned_lit_small by lia; rewrite zcanon_id; [lia | unfold M64; lia]).
rewrite UB, UP.
exact (range_addressable_of_block SEGS B LAWS lyc Sc W memc mdc bi Li p 1 HARc Hbin ltac:(lia) ltac:(lia)). }
{ rn_awrB c (spZ regs) sp0 Uc Usp HWR. }
rn_tkupdB lyc Sc W memc mdc HARc (spZ regs) (fun a : Z => c <= a < c + 16) HEimg0 TK HJc.
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
(* 0x813e4 bltu s0, a2: k = xb mod 48 when xb mod 48 < n - 1, else k = n - 1 *)
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => set (E1 := Ex) in * end.
assert (OLD1 : forall j, (j < 512)%nat -> ew E1 j = ew E j)
by (intros j Hj; subst E1; rewrite !ew_ewset_other by lia; reflexivity).
assert (UKX : U E1 RN_KX = xb mod 48) by (apply rn_kx_val; [rewrite OLD1 by lia; exact E35 | exact Hxr]).
assert (U34m : U E1 (SOff 34 (-1)) = n - 1)
by (rewrite U_SOff, OLD1, E34, unsigned_lit_small by lia; rewrite zcanon_id; [lia | unfold M64; lia]).
assert (Uc1 : bv_unsigned (ew E1 10) = c) by (rewrite OLD1 by lia; exact Uc).
assert (Usp1 : bv_unsigned (ew E1 2) = spZ regs) by (rewrite OLD1 by lia; exact Usp).
assert (Hkd : read_name_c.rn_k (b0 :: rest) = Z.min (xb mod 48) (n - 1)).
{ change (read_name_c.rn_k (b0 :: rest)) with (Z.min (bv_unsigned b0 mod 48) (Z.of_nat (length rest))).
unfold xb, n. cbn [length]. lia. }
assert (Hk47 : 0 <= read_name_c.rn_k (b0 :: rest) <= 47)
by (rewrite Hkd; pose proof (Z.mod_pos_bound xb 48 ltac:(lia)); lia).
assert (Hkn : read_name_c.rn_k (b0 :: rest) <= n - 1) by (rewrite Hkd; lia).
psrr_branch_tok RUN BR HS SHOK RNspan.
all: fold RN_KQ RN_KX in Hc; rewrite branch_ltu_U, UKX, U34m in Hc.
all: paj_run_to_tok RUNTO HS HJc SHOK RNspan 5184.
all: try (rn_awrB c (spZ regs) sp0 Uc Usp HWR).
all: rn_tkupdB lyc Sc W memc mdc HARc (spZ regs) (fun a : Z => c <= a < c + 16) HEimg0 TK HJc.
all: repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
(* re-seat at 0x813ec: k in atom 100, registers 15-17 (dead) in atoms 101-103 *)
all: lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) => set (msM := msx) in * end.
all: pose proof (st_ok_pi_restrict_reg _ _ _ _ 8%bv HS) as R8.
all: lazymatch type of R8 with _ = sv_denot _ ?e => let e' := eval vm_compute in e in change e with e' in R8 end.
all: assert (Hk8 : bv_unsigned (getr (ms_regs msM) 8) = read_name_c.rn_k (b0 :: rest))
by (rewrite R8; first
[ fold RN_KQ RN_KX; change (U E1 RN_KX = read_name_c.rn_k (b0 :: rest)); rewrite UKX, Hkd;
apply Z.ltb_lt in Hc; lia
| change (U E1 (SOff 34 (-1)) = read_name_c.rn_k (b0 :: rest)); rewrite U34m, Hkd;
apply Z.ltb_ge in Hc; lia ]).
all: pose proof (st_ok_pi_havoc 100%nat E1 _ _
[Z_to_bv 64 (read_name_c.rn_k (b0 :: rest)); getr (ms_regs msM) 15; getr (ms_regs msM) 16; getr (ms_regs msM) 17] HS
ltac:(vm_compute; reflexivity) ltac:(cbn [length]; unfold A_TEXT; lia)) as HS1.
all: clear HS; rename HS1 into HS.
all: lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => set (E' := Ex) in HS end.
all: assert (HEI' : img_env VAL A_LIM E') by (subst E'; apply img_env_havoc; [assumption | cbv; lia]).
all: assert (OLDM : forall j, (j < 100)%nat -> ew E' j = ew E1 j) by (intros j Hj; subst E'; apply ew_havoc_old; lia).
all: assert (EM100 : ew E' 100 = Z_to_bv 64 (read_name_c.rn_k (b0 :: rest)))
by (subst E'; exact (ew_havoc_new E1 100
[Z_to_bv 64 (read_name_c.rn_k (b0 :: rest)); getr (ms_regs msM) 15; getr (ms_regs msM) 16; getr (ms_regs msM) 17]
0 (Z_to_bv 64 0) ltac:(cbn [length]; lia))).
all: assert (EM101 : ew E' 101 = getr (ms_regs msM) 15)
by (subst E'; exact (ew_havoc_new E1 100
[Z_to_bv 64 (read_name_c.rn_k (b0 :: rest)); getr (ms_regs msM) 15; getr (ms_regs msM) 16; getr (ms_regs msM) 17]
1 (Z_to_bv 64 0) ltac:(cbn [length]; lia))).
all: assert (EM102 : ew E' 102 = getr (ms_regs msM) 16)
by (subst E'; exact (ew_havoc_new E1 100
[Z_to_bv 64 (read_name_c.rn_k (b0 :: rest)); getr (ms_regs msM) 15; getr (ms_regs msM) 16; getr (ms_regs msM) 17]
2 (Z_to_bv 64 0) ltac:(cbn [length]; lia))).
all: assert (EM103 : ew E' 103 = getr (ms_regs msM) 17)
by (subst E'; exact (ew_havoc_new E1 100
[Z_to_bv 64 (read_name_c.rn_k (b0 :: rest)); getr (ms_regs msM) 15; getr (ms_regs msM) 16; getr (ms_regs msM) 17]
3 (Z_to_bv 64 0) ltac:(cbn [length]; lia))).
all: assert (D8 : getr (ms_regs msM) 8 = sv_denot E' (SOff 100 0))
by (apply bv_eq; rewrite Hk8; change (read_name_c.rn_k (b0 :: rest) = U E' (SOff 100 0));
rewrite U_SOff, EM100, unsigned_lit_small by lia; rewrite Z.add_0_r, zcanon_id; [reflexivity | unfold M64; lia]).
all: assert (D15 : getr (ms_regs msM) 15 = sv_denot E' (SOff 101 0))
by (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, EM101; reflexivity).
all: assert (D16 : getr (ms_regs msM) 16 = sv_denot E' (SOff 102 0))
by (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, EM102; reflexivity).
all: assert (D17 : getr (ms_regs msM) 17 = sv_denot E' (SOff 103 0))
by (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, EM103; reflexivity).
all: lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msr =>
pose proof (st_ok_pi_set_reg Ex ssx msr 8%bv (SOff 100 0) HS
ltac:(intros Hq; apply (f_equal bv_unsigned) in Hq; vm_compute in Hq; discriminate) D8) as HS1 end.
all: clear HS; rename HS1 into HS.
all: lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msr =>
pose proof (st_ok_pi_set_reg Ex ssx msr 15%bv (SOff 101 0) HS
ltac:(intros Hq; apply (f_equal bv_unsigned) in Hq; vm_compute in Hq; discriminate) D15) as HS1 end.
all: clear HS; rename HS1 into HS.
all: lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msr =>
pose proof (st_ok_pi_set_reg Ex ssx msr 16%bv (SOff 102 0) HS
ltac:(intros Hq; apply (f_equal bv_unsigned) in Hq; vm_compute in Hq; discriminate) D16) as HS1 end.
all: clear HS; rename HS1 into HS.
all: lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msr =>
pose proof (st_ok_pi_set_reg Ex ssx msr 17%bv (SOff 103 0) HS
ltac:(intros Hq; apply (f_equal bv_unsigned) in Hq; vm_compute in Hq; discriminate) D17) as HS1 end.
all: clear HS; rename HS1 into HS.
all: lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msr =>
pose proof (st_ok_pi_submem Ex ssx msr [rn_mid_stack; rn_cur0] HS ltac:(vm_compute; submem_tac) eq_refl) as HS1 end.
all: clear HS; rename HS1 into HS.
all: lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msr =>
pose proof (st_ok_pi_pick_facts Ex ssx msr [0%nat; 1%nat; 2%nat] [] [] HS) as HS1 end.
all: clear HS; rename HS1 into HS.
all: lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msr =>
pose proof (st_ok_pi_add_fact Ex ssx msr 100%nat FK HS
ltac:(unfold afact_ok, FK; cbn [af_lo af_hi af_al2]; rewrite EM100, unsigned_lit_small by lia;
rewrite Z.pow_0_r, Z.mod_1_r; revert Hk47; clear; intros; lia)) as HS1 end.
all: clear HS; rename HS1 into HS.
all: assert (HSM : st_ok_pi SEGS VAL E' ss_mid (restrict (w_H W) msM))
by (lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ =>
let v := eval vm_compute in ssx in change ssx with v in HS end; exact HS).
all: clear HS.
all: assert (SHOK' : sh_ok SEGS RNx rn_SH E' (mrestrict (w_H W) (ms_mem msM)))
by (eapply sh_ok_agree with (k := 100%nat) (E := E1); [ idtac .. | exact SHOK ];
first [ split; [intros j Hj; apply OLDM; exact Hj | subst E'; reflexivity] | reflexivity ]).
all: assert (HAE' : env_agree 32 (Ereg regs []) E').
all: [> split; [intros j Hj; rewrite OLDM, OLD1 by lia; unfold E, RNE; rewrite Eimg_low by (unfold A_TEXT; lia);
do 32 (destruct j as [|j]; [reflexivity|]); lia | subst E' E1; unfold E, RNE; reflexivity] | idtac
| split; [intros j Hj; rewrite OLDM, OLD1 by lia; unfold E, RNE; rewrite Eimg_low by (unfold A_TEXT; lia);
do 32 (destruct j as [|j]; [reflexivity|]); lia | subst E' E1; unfold E, RNE; reflexivity] | idtac ].
all: assert (Up : U E' (SOff 33 1) = p + 1)
by (rewrite U_SOff, OLDM, OLD1, E33, unsigned_lit_small by lia; rewrite zcanon_id; [lia | unfold M64; lia]).
all: assert (Um : U E' (SOff 34 (-1)) = n - 1)
by (rewrite U_SOff, OLDM, OLD1, E34, unsigned_lit_small by lia; rewrite zcanon_id; [lia | unfold M64; lia]).
all: eapply (rn_tail STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc _ k regs E' msM c p (p + 1) (n - 1)
(read_name_c.rn_k (b0 :: rest)) (b0 :: rest)).
all: [> exact HJc | exact HARc | exact HSM | exact SHOK' | exact HEI' | exact HAE' | exact TK
| rewrite OLDM, OLD1 by lia; exact E10 | rewrite OLDM, OLD1 by lia; exact E32 | exact EM100 | exact Up | exact Um
| exact Hraok | exact Hra4 | exact Hgp | exact Htp | exact Hal16 | exact Hlo | exact Hhi | exact Hc8 | exact Hcsp
| exact Hchi | exact HWR | reflexivity | fold n; lia | fold n; lia | exact Hk47 | exact Hkn | lia | lia | lia
| intros; lia | unfold amem_range in Hamr |- *; lia
| intros _; exists bi, Li; split; [exact Hbin | split; lia]
| intros i Hi; rewrite (rn_bsub_nthB b0 rest i Hi); replace (p + 1 + i) with (p + (1 + i)) by lia; apply Hbytes; lia
| exact Hev | exact Hlive | exact MOK | exact HUNIV
| exact HJc | exact HARc | exact HSM | exact SHOK' | exact HEI' | exact HAE' | exact TK
| rewrite OLDM, OLD1 by lia; exact E10 | rewrite OLDM, OLD1 by lia; exact E32 | exact EM100 | exact Up | exact Um
| exact Hraok | exact Hra4 | exact Hgp | exact Htp | exact Hal16 | exact Hlo | exact Hhi | exact Hc8 | exact Hcsp
| exact Hchi | exact HWR | reflexivity | fold n; lia | fold n; lia | exact Hk47 | exact Hkn | lia | lia | lia
| intros; lia | unfold amem_range in Hamr |- *; lia
| intros _; exists bi, Li; split; [exact Hbin | split; lia]
| intros i Hi; rewrite (rn_bsub_nthB b0 rest i Hi); replace (p + 1 + i) with (p + (1 + i)) by lia; apply Hbytes; lia
| exact Hev | exact Hlive | exact MOK | exact HUNIV ].
Qed.
End h.
End f.
End d.
