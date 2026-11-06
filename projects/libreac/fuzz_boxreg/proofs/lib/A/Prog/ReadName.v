(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:176-178; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:180-183, 357-361,
   for libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_catalogue.v, with its module paths, module names and numbers changed; 952 of its 1036 lines of code are new or changed and 285 lines of the source are left out. *)
(* read_name (fuzz_boxreg.asan 0x812b0, 96 instructions; C: fuzz/fuzz_boxreg.c:70-81, with fuzz_u8 and fuzz_take of
   fuzz/fuzz.h:36-66 inlined): the contract of the ASan build's code, in cgif's caller-journal form
   (proofs/cgif/cgif_file_fuzzer/lib/YC20.v:311-365, tlzw_*; CONVENTIONS section 2) with the shapes of
   lib/A/Prog/BoxCJ.v (twr_ok, tcj_kept).
   What the code does. The function takes a 48-byte frame on the machine stack (addi sp,sp,-48; ra, s0..s3 saved) and
   gets a0 = c, the address of the caller's cursor struct fuzz_in { p at c, n at c + 8 }. fuzz_u8: it loads n
   (0x812ec); when n = 0 the length byte is 0 (0x81358), else it stores n - 1 at c + 8, loads p, stores p + 1 at c and
   loads the byte x at p; the wanted length is x mod 48 (mul 0xab / srli 13, 0x81334-0x81350). fuzz_take: it loads n
   again, takes k = min (x mod 48, n) (bltu 0x81368), loads p, stores p + k at c and n - k at c + 8. Then it calls
   malloc (k + 1) (0x8139c, BS___interceptor_trampoline_malloc), branches to abort when the result is NULL
   (beqz 0x813a0 -> 0x813ec __asan_handle_no_return, abort), copies the k bytes with __asan_memcpy (s, p', k)
   (0x813b0; p' is the cursor's p after fuzz_u8), stores 0 at s + k after the shadow check of that byte, and returns s.
   With pl the n remaining input bytes: k = read_name_c.rn_k pl, the name holds Boxreg.bsub pl 1 k ++ [0], and the
   cursor advances by min (n, 1) + k.
   Why the caller-journal form: the cursor is in the caller's frame. Its one caller, LLVMFuzzerTestOneInput, keeps
   `struct fuzz_in in` in its spill area on the machine stack (s1 + 136 = p, s1 + 144 = n; the two calls at 0x8051c
   and 0x80580 pass a0 = s1 + 136), between its own sp and its entry sp, so the right to write the 16 bytes is
   awr_byte's window case of the caller's journal; the spec takes it as the premise twr_ok (BoxCJ.v).
   Bytes of the caller written: exactly the 16 cursor bytes [c, c + 16) (8-byte stores at c + 8 and c: twice each when
   n > 0, once each when n = 0).
   Bytes written besides: the new name block [s, s + k + 1) and the own window [sp - READ_NAME_STK, sp). The post's
   tcj_kept says every other byte is kept (E = read_name_c.rn_writes c s k).
   The malloc rule: cgif's amalloc04_rule (lib/Reusable/YC5d.v:57-76), taken in the proof at
   pa_sigma BS___interceptor_trampoline_malloc = pc_wrap_malloc (as_code B) (BoxPaLib.v pal_malloc). Its post gives
   4096 <= res, so the NULL branch to abort is never taken and the post has no NULL case; it extends the caller's
   journal by one event and adds exactly the block (s, k + 1) (ablocks ... = ablocks ... ++ [(s, k + 1)]). Its
   premises, carried here: 0 <= k + 1 < MALLOC_MAX and blocks_bytes Sc + (k + 1) <= LIVE_MAX (from the room fact
   below and k + 1 <= 48), st_nev Sc < EV_MAX (from st_nev Sc + EV_READ_NAME <= EV_MAX), mo_ok MT Sc (mo_malloc MT
   (k + 1)), the stack (ASTACK below the call's sp, inside READ_NAME_STK), and the call trace. The trace is
   [pc_malloc_ra0; A_read_nameP + 0xf0]: at the call s0 holds k (0..47, below the stack), so chain_pre's bad_next
   gives the empty chain and call_trace0 is pc_malloc_ra0 :: [ra] (lib/Reusable/YCbq.v:327 call_trace_nil; ra is not
   pc_malloc_ra0 because pc_malloc_ra0 < BASE, BoxPaLib.v pal_rt_below). The caller's own chain is not part of it.
   Room facts (internal path P3): the request k + 1 is 1..48 (x mod 48 <= 47); LIVE_READ_NAME = 48;
   EV_READ_NAME = 1 (the one malloc tick; read_name frees nothing). The caller discharges
   blocks_bytes Sc + 48 <= LIVE_MAX from its entry's blocks_bytes S + LIVE_LIB <= LIVE_MAX and its loop invariant
   "live blocks = the entry's ++ [(r, 288)]" (288 + 48 = 336 <= LIVE_LIB); the name is freed in the same loop
   iteration on every returning path (free at 0x80aa8 / 0x805fc).
   Stack: the own 48-byte frame and ASTACK below it for the malloc wrapper (amalloc04_rule: ASTACK - o <= STK); the
   memcpy wrapper's ESTACK is less. No program callee.
   Read footprint, each byte covered by a premise: the 16 cursor bytes (val_mem; their shadow bytes, both 0 because c
   is 8-aligned and range_addressable c 16, refute the __asan_report_load8 / store8 branches); the input bytes
   [p, p + n) (their values; for n > 0 a heap block of the caller holds them, the driver's input block (p0, n0) of
   LLVMFuzzerTestOneInput's pre, whose shadow AR's block law gives: the load1 check at p and the memcpy source
   [p + 1, p + 1 + k)); for n = 0 the memcpy source is the empty range at p, hence amem_range p n and
   p + n <= 2 ^ 63. The store s[k] and the memcpy destination are in the new block (AR's block law after malloc).
   The only image reads are the GOT word of the shadow base and the shadow cell, both fixed by AR (AR_const_law).
   Hazards: the old walk's contract (a working branch 67b70ae1ec3 lib/A/Prog/read_name_c.v) is stated over AsanRT's RT,
   which pins malloc_context_size = 1 and is VACUOUS on this image: only its functional content is taken here
   (rn_k, the name bytes, the advanced cursor); no f* or csr instruction occurs in the 96 instructions (capstone
   scan, PROGRAM.md P1), so the fixed {fx} is sound.
   Image difference: the asan-ubsan build (lib/B/Prog/BoxBReadName.v, 0x81318, 116 instructions) adds UBSan traps for
   c not 8-aligned and for the pointer overflows of p + 1, p + k and s + k; the result and the written bytes are the
   same.
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
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaRun PaShadow BoxSyms BoxList BoxPa.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaJournal BoxBase BoxCJ.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Boxreg read_name_c.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YImgTop.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaStep BoxPaLib YC1g YC1h YC81 YC4b YC85.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
(* The room facts of the call: one allocator event (the malloc), and at most 48 bytes of new live heap. *)
Definition EV_READ_NAME : Z := 1.
Definition LIVE_READ_NAME : Z := 48.
(* How far the cursor advances: the length byte (when there is one) and the k name bytes. *)
Definition tread_name_used (pl : list byte) : Z := Z.min (Z.of_nat (length pl)) 1 + read_name_c.rn_k pl.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg box_listing}.
#[local] Notation SEGS := (@pa_segs _ box_listing PI).
#[local] Notation BASE := (@pa_val _ box_listing PI A_TEXT).
(* The function's address in the image, the return address of its malloc call (0x8139c + 4), and the stack it
   needs: its own 48-byte frame and ASTACK below it for the malloc wrapper. *)
Definition A_read_nameP : Z := BASE + AF_read_name.
Definition A_read_name_mallocRA : Z := A_read_nameP + 0xf0.
Definition READ_NAME_STK : Z := 48 + ASTACK.
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Definition tread_name_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
  (regs : bvmap 5 word) (c p : Z) (pl : list byte) : world SEGS -> config -> Prop :=
fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (s : Z),
c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + EV_READ_NAME) /\
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
val_mem SEGS (mrestrict (w_H W2) mem2) c 8 (p + tread_name_used pl) /\
val_mem SEGS (mrestrict (w_H W2) mem2) (c + 8) 8 (Z.of_nat (length pl) - tread_name_used pl) /\
mo_le MT Sc S2 (mo_malloc MT (read_name_c.rn_k pl + 1)) /\
tcj_kept B READ_NAME_STK lyc Sc W memc W2 mem2 (spZ regs) (read_name_c.rn_writes c s (read_name_c.rn_k pl)).
Definition tread_name_spec : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (c p bi Li : Z) (pl : list byte),
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - READ_NAME_STK -> spZ regs <= sp0 ->
getr regs 10 = w64 c ->
(* the caller's cursor { p, n = length pl } at c, above sp, the caller's to let the call write *)
c mod 8 = 0 -> spZ regs <= c ->
val_mem SEGS (mrestrict (w_H W) memc) c 8 p ->
val_mem SEGS (mrestrict (w_H W) memc) (c + 8) 8 (Z.of_nat (length pl)) ->
range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF c 16 ->
twr_ok B STK sp0 FP ly S lyc Sc own W memc (spZ regs) c 16 ->
(* the remaining input bytes pl at p: a heap block holds them when there are any *)
0 <= p -> p + Z.of_nat (length pl) <= 2 ^ 63 -> amem_range p (Z.of_nat (length pl)) ->
(pl <> [] -> In (bi, Li) (ablocks B lyc Sc) /\ bi <= p /\ p + Z.of_nat (length pl) <= bi + Li) ->
(forall i, 0 <= i < Z.of_nat (length pl) ->
  aview SEGS (w_H W) memc (p + i) = Some (bv_unsigned (nth (Z.to_nat i) pl (Z_to_bv 8 0)))) ->
(* room for the malloc *)
st_nev Sc + EV_READ_NAME <= EV_MAX -> blocks_bytes Sc + LIVE_READ_NAME <= LIVE_MAX ->
mo_ok MT Sc (mo_malloc MT (read_name_c.rn_k pl + 1)) ->
In [pc_malloc_ra0 (as_code B); A_read_name_mallocRA] (as_universe B) ->
SRr SEGS W (cfg_at SEGS A_read_nameP regs memc mdc)
(tread_name_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs c p pl).
(* YC4b switches lia's division handling off for its importers; this file's arithmetic needs it. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* The walk. The symbolic state's environment: the registers at entry, then (slots 32-38) the shadow base, the
   cursor's p and n, the first input byte x, k = rn_k pl, and the cursor after fuzz_u8 (p', n'). The code reads the
   shadow base through the GOT word of the shadow-base cell (objects 1 and 12, PALib). *)
#[local] Notation VAL := (@pa_val _ box_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ box_listing PI).
Definition rn_n (pl : list byte) : Z := Z.of_nat (length pl).
Definition rn_u (pl : list byte) : Z := Z.min (rn_n pl) 1.
Definition rn_x (pl : list byte) : Z := bv_unsigned (nth 0 pl (Z_to_bv 8 0)).
Definition rn_extra (p : Z) (pl : list byte) : list word :=
[Z_to_bv 64 SB; Z_to_bv 64 p; Z_to_bv 64 (rn_n pl); Z_to_bv 64 (rn_x pl); Z_to_bv 64 (read_name_c.rn_k pl);
 Z_to_bv 64 (p + rn_u pl); Z_to_bv 64 (rn_n pl - rn_u pl)].
Definition rn_cur : YP09.region :=
YP09.mkRegion (Some 10%nat) 0 16 0 16 [YP09.mkChunk 0 (CVal 8 (SOff 33 0)); YP09.mkChunk 8 (CVal 8 (SOff 34 0))].
Definition rn_facts : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF (2 ^ 46) (2 ^ 47 - 16) 3); (32%nat, mkAF SB SB 0)] [] [].
Definition ss_rn : sstate := mkSS AF_read_name sr_atoms [rn_cur; stack_region 48; got_regionP; bcell_regionP 32] None rn_facts.
Definition rn_SH0 : list shent := [mkSHE 10 0 16].
(* The byte x at p (when n > 0): read only. *)
Definition rn_preg : YP09.region := YP09.mkRegion (Some 33%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 35 0))].
Lemma rn_val_mem1 : forall H (m : word -> option byte) a v, aview SEGS H m a = Some v -> val_mem SEGS (mrestrict H m) a 1 v.
Proof.
intros H m a v Hv kk Hk. assert (kk = 0%nat) as -> by lia.
destruct (aview_byte SEGS H m a v Hv) as (b & Hb & -> & Hr). change (a + Z.of_nat 0) with (a + 0). rewrite Z.add_0_r, Hb.
f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. unfold YO0f.le_byte, bv_wrap. change (bv_modulus 8) with 256.
change (8 * Z.of_nat 0) with 0. change (2 ^ (8 * Z.of_nat 1)) with 256. rewrite Z.shiftr_0_r.
rewrite !Z.mod_small by lia. reflexivity.
Qed.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis AM : amalloc04_rule SEGS B MT.
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA BS___asan_memcpy).
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_box) (PI := PI).
Let HBgot := pal_got_shadow B TL.
Let HBcell := pal_cell B TL.
(* The cursor lies in the caller's stack window: each byte the caller lets the call write and that lies above sp is
   in neither a heap block nor a side-stack frame (both below alloc_ceiling). *)
Lemma rn_c_where : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) c,
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
sp0 - STK <= spZ regs - READ_NAME_STK -> spZ regs <= c ->
twr_ok B STK sp0 FP ly S lyc Sc own W memc (spZ regs) c 16 ->
alloc_ceiling <= spZ regs /\ c + 16 <= sp0 /\ sp0 <= 2 ^ 47.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs c HJ Hwlo Hc Hw.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
assert (RS : READ_NAME_STK = 16432) by reflexivity.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (Hw (c + 15) ltac:(lia)) as (Haw & _ & _ & _).
destruct (awr_byte_cases SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ Haw)
  as (_ & [(_ & H1) | [(Happ & _) | (cid & pos & _ & [(Happ & _) | (Hsh & _)])]]); zlia.
Qed.
Lemma rn_entry : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) c p (pl : list byte),
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 10 = w64 c -> spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - READ_NAME_STK -> spZ regs <= sp0 ->
c mod 8 = 0 -> spZ regs <= c ->
val_mem SEGS (mrestrict (w_H W) memc) c 8 p ->
val_mem SEGS (mrestrict (w_H W) memc) (c + 8) 8 (Z.of_nat (length pl)) ->
range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF c 16 ->
twr_ok B STK sp0 FP ly S lyc Sc own W memc (spZ regs) c 16 ->
0 <= p -> p + Z.of_nat (length pl) <= 2 ^ 63 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (rn_extra p pl))) ss_rn
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_read_name)) memc (seg_rom SEGS)))
/\ sh_ok SEGS (SOff 32 0) rn_SH0 (Eimg (Ereg regs (rn_extra p pl))) (mrestrict (w_H W) memc).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs c p pl HJ H10 Hal16 Hwlo Hwhi Hc8 Hcsp Hvp Hvn Hra Hw Hp0 Hpn.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (rn_c_where STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs c HJ Hwlo Hcsp Hw) as (Hsp & Hc16 & H47').
assert (RS : READ_NAME_STK = 16432) by reflexivity.
destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD.
pose proof (pa_obj_img 1 ltac:(lia)) as HgotR.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (rn_extra p pl))).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (rn_extra p pl)) n)
by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 c)
by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 p) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (rn_n pl)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E1o : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)))
by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E12o : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (Uc : bv_unsigned (ew E 10) = c) by (rewrite E10; apply unsigned_lit_small; lia).
assert (USB : bv_unsigned (ew E 32) = SB) by (rewrite E32; apply unsigned_lit_small; unfold SB; lia).
assert (UBx : U E (SOff 32 0) = SHADOW_OFF).
{ rewrite U_SOff, E32, Z.add_0_r, unsigned_lit_small by (unfold SB; lia).
  rewrite zcanon_id by (unfold SB, M64; lia). reflexivity. }
assert (U10 : U E (SOff 10 0) = c).
{ rewrite U_SOff, E10, Z.add_0_r, unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia. }
split.
- unfold ss_rn. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold rn_cur, stack_region, got_regionP, bcell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Uc. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable SEGS); exact (proj1 (proj2 (Hw (c + o) ltac:(lia))))|].
      constructor; [|constructor; [|constructor]].
      -- apply (chunk_ok_val SEGS E _ c 0 8 (SOff 33 0) p);
         [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
         rewrite Z.add_0_r. exact Hvp.
      -- apply (chunk_ok_val SEGS E _ c 8 8 (SOff 34 0) (rn_n pl));
         [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold rn_n; zside | zside |].
         exact Hvn.
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    * cbn [base_val]. rewrite E1o, unsigned_lit_small by (pose proof (pa_val_range (A_OBJ 1)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [cbn [sv_denot]; rewrite E12o, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kgot).
    * cbn [base_val]. rewrite E12o, unsigned_lit_small by (pose proof (pa_val_range (A_OBJ 12)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SB);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kcell).
  + apply pairwise_disjoint_of_extents. unfold rn_cur, stack_region, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val].
    rewrite Uc, Usp, E1o, E12o, !unsigned_lit_small
      by (pose proof (pa_val_range (A_OBJ 1)); pose proof (pa_val_range (A_OBJ 12)); lia).
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [rn_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, Uc, USB.
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SB; lia.
- unfold sh_ok, rn_SH0. constructor; [|constructor].
  unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
  rewrite UBx, U10. rewrite <- (aview_rd_of SEGS).
  split.
  + replace (16 - 0) with 16 by lia. rewrite Z.add_0_r. exact Hra.
  + intros a Ha. cbn [Z.min Z.max] in Ha. rewrite Z.add_0_r in Ha.
    unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
Lemma rn_den_eq : forall E a b, U E a = U E b -> sv_denot E a = sv_denot E b.
Proof. intros E a b H. unfold U in H. apply bv_eq. exact H. Qed.
Lemma rn_U_off : forall E E0 (n : nat) v z, (forall m, (m < 512)%nat -> ew E m = ew E0 m) -> (n < 512)%nat ->
ew E0 n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + z < 2 ^ 64 -> U E (SOff n z) = v + z.
Proof.
intros E E0 n v z AG Hn Hv Hr Hz. rewrite U_SOff, (AG n Hn), Hv, unsigned_lit_small by lia.
apply zcanon_id. unfold M64. lia.
Qed.
(* The length byte modulo 48 as the code computes it (0x81334-0x81350: mul 0xab, srli 13, slli 4 and 6, subw, add,
   andi 0xff), as the symbolic run leaves it in s0; x is the first input byte (slot 35). *)
Definition rn_s0x : sv :=
SAlu ALU_AND
  (SAlu ALU_ADD (SExt false 8 (SOff 35 0))
     (SAlu ALU_SUB
        (SAlu ALU_SLL (SAlu ALU_SRL (SMd M_MUL (SExt false 8 (SOff 35 0)) (SLit 171)) (SLit 13)) (SLit 4))
        (SAlu ALU_SLL (SAlu ALU_SRL (SMd M_MUL (SExt false 8 (SOff 35 0)) (SLit 171)) (SLit 13)) (SLit 6))))
  (SLit 255).
Lemma rn_mod48 : forall E x, ew E 35 = Z_to_bv 64 x -> 0 <= x < 256 -> U E rn_s0x = x mod 48.
Proof.
intros E x H35 Hx.
set (E' := mkEnv (fun _ => Z_to_bv 64 x) (ed E)).
assert (HA : env_agree_p (fun n => Nat.eqb n 35) E E').
{ split; [|reflexivity]. intros n Hn. apply Nat.eqb_eq in Hn. subst n. cbn [ew E']. symmetry. exact H35. }
unfold U. rewrite <- (sv_denot_agree_p (fun n => Nat.eqb n 35) E E' rn_s0x HA eq_refl).
assert (Hb : forallb (fun n => Z.eqb (bv_unsigned (sv_denot (mkEnv (fun _ => Z_to_bv 64 (Z.of_nat n)) (ed E)) rn_s0x))
  (Z.of_nat n mod 48)) (seq 0 256) = true) by (vm_compute; reflexivity).
rewrite forallb_forall in Hb. specialize (Hb (Z.to_nat x)). rewrite Z2Nat.id in Hb by lia.
apply Z.eqb_eq. apply Hb. apply in_seq. lia.
Qed.
Lemma rn_k_cons : forall b rest, read_name_c.rn_k (b :: rest) = Z.min (bv_unsigned b mod 48) (Z.of_nat (length rest)).
Proof. reflexivity. Qed.
Lemma rn_k_A : forall pl, pl <> [] -> rn_x pl mod 48 < rn_n pl - 1 -> read_name_c.rn_k pl = rn_x pl mod 48.
Proof. intros [|b rest] Hne H; [congruence|]. rewrite rn_k_cons. unfold rn_x, rn_n in *. cbn [nth length] in *. lia. Qed.
Lemma rn_k_B : forall pl, pl <> [] -> rn_n pl - 1 <= rn_x pl mod 48 -> read_name_c.rn_k pl = rn_n pl - 1.
Proof. intros [|b rest] Hne H; [congruence|]. rewrite rn_k_cons. unfold rn_x, rn_n in *. cbn [nth length] in *. lia. Qed.
Lemma rn_k_D : forall pl, rn_n pl = 0 -> read_name_c.rn_k pl = 0.
Proof. intros [|b rest] H; [reflexivity|]. unfold rn_n in H. cbn [length] in H. lia. Qed.
Lemma rn_k_range : forall pl, 0 <= read_name_c.rn_k pl <= 47 /\ read_name_c.rn_k pl <= rn_n pl - rn_u pl.
Proof.
intros [|b rest]; [cbn; unfold rn_u, rn_n; cbn; lia|]. rewrite rn_k_cons. unfold rn_u, rn_n. cbn [length].
pose proof (Z.mod_pos_bound (bv_unsigned b) 48 ltac:(lia)). lia.
Qed.
(* The cursor after fuzz_u8, with its two words named by slots 37 (p') and 38 (n'). *)
Definition rn_cur2 : YP09.region :=
YP09.mkRegion (Some 10%nat) 0 16 0 16 [YP09.mkChunk 0 (CVal 8 (SOff 37 0)); YP09.mkChunk 8 (CVal 8 (SOff 38 0))].
Lemma rn_cur_norm : forall E m e0 e8,
region_ok SEGS E m (YP09.mkRegion (Some 10%nat) 0 16 0 16 [YP09.mkChunk 0 (CVal 8 e0); YP09.mkChunk 8 (CVal 8 e8)]) ->
sv_denot E e0 = sv_denot E (SOff 37 0) -> sv_denot E e8 = sv_denot E (SOff 38 0) ->
region_ok SEGS E m rn_cur2.
Proof.
intros E m e0 e8 (H1 & H2 & H3 & H4) He0 He8. unfold rn_cur2, region_ok in *.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks] in *.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
apply Forall_cons_iff in H4 as [Hc0 H4]. apply Forall_cons_iff in H4 as [Hc1 _].
unfold YP09.chunk_ok in *. cbn [YP09.cbyte YP09.c_val YP09.c_off YP09.c_len YP09.cv_len] in *.
constructor; [|constructor; [|constructor]]; unfold YP09.chunk_ok; cbn [YP09.cbyte YP09.c_val YP09.c_off YP09.c_len YP09.cv_len];
intros i Hi; [destruct (Hc0 i Hi) as (b & Hb1 & Hb2) | destruct (Hc1 i Hi) as (b & Hb1 & Hb2)];
exists b; (split; [|exact Hb2]); [rewrite <- He0 | rewrite <- He8]; exact Hb1.
Qed.
(* The right to write the regions: the cursor (twr_ok), the own frame (the caller's stack window), read-only ones. *)
Ltac rn_awr c sp sp0 Uc Usp Hcw :=
let AG := lazymatch goal with H : forall n, (n < 512)%nat -> ew _ n = ew _ n |- _ => H end in
lazymatch goal with |- awr_ok ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?lyx ?ownx =>
  let rs' := eval vm_compute in rsx in change (awr_ok Ex rs' stkx spx fpx b0x bcx lyx ownx) end;
repeat first
[ apply awr_ok_nil
| apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
| eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 10%nat c);
  [ reflexivity | first [exact Uc | rewrite (AG 10%nat) by lia; exact Uc] | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; left; unfold READ_NAME_STK, ASTACK in *; lia |]
| eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (sp - sp0));
  [ reflexivity | first [rewrite Usp | rewrite (AG 2%nat), Usp by lia]; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |] ].
(* After a run or a call the environment grows above slot 511; AG says the slots below are those of the entry. Keep
   AG and the img_env fact for the current environment. *)
Ltac rn_env HS AG :=
let Ex := lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => Ex | st_ok _ ?Ex _ _ => Ex end in
lazymatch type of AG with forall n, _ -> ew ?Eo n = ew ?E0 n =>
lazymatch Ex with
| Eo => idtac
| _ => let AG2 := fresh "AG" in
  assert (AG2 : forall n, (n < 512)%nat -> ew Ex n = ew E0 n)
    by (intros nn Hnn; repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia];
        first [reflexivity | apply AG; exact Hnn]);
  clear AG; rename AG2 into AG
end end;
repeat match goal with H : img_env _ _ ?Ey |- _ => lazymatch Ey with Ex => fail | _ => clear H end end.
(* A run writes only the windows of its regions: the cursor and the own frame (the other regions are read only).
   KR / GR: every byte outside those two windows is the caller's (memc) one, and every present byte stays present. *)
Ltac rn_kupd c sp memc Uc Usp KR GR :=
let AG := lazymatch goal with H : forall n, (n < 512)%nat -> ew _ n = ew _ n |- _ => H end in
lazymatch goal with HFr : frame_of ?Ex ?rsx (mrestrict ?H ?m0) (mrestrict ?H ?m1), HG : mem_grows (mrestrict ?H ?m0) (mrestrict ?H ?m1) |- _ =>
 let KR2 := fresh "KR" in let GR2 := fresh "GR" in
 assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> ~ (c <= a < c + 16) -> ~ (sp - 48 <= a < sp) -> aview SEGS H m1 a = aview SEGS H memc a);
 [ intros a Ha HnC HnS; try rewrite <- (KR a Ha HnC HnS);
   refine (kept_of_frame Ex rsx H m0 m1 (fun x => (c <= x < c + 16) \/ (sp - 48 <= x < sp)) HFr _ a Ha _);
   [ intros bb wlo whi x Hin Hr;
     let wsv := eval vm_compute in (windows rsx) in change (In (bb, wlo, whi) wsv) in Hin;
     cbn [In] in Hin;
     repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hr|]); try contradiction;
     first [ lia
           | first [rewrite Uc in Hr | rewrite (AG 10%nat), Uc in Hr by lia]; left; lia
           | first [rewrite Usp in Hr | rewrite (AG 2%nat), Usp in Hr by lia]; right; lia ]
   | intros [Hq | Hq]; [exact (HnC Hq) | exact (HnS Hq)] ]
 | ];
 assert (GR2 : forall a, apresent H memc a -> apresent H m1 a)
   by (intros a Ha; apply (apresent_grows H m0 m1 a HG); apply GR; exact Ha);
 clear KR GR; rename KR2 into KR; rename GR2 into GR
end;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
(* A register's symbolic value, without unfolding its denotation. *)
Ltac rn_reg HS r Hr :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
  cbn [ms_regs restrict mkst] in Hr
| st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
  cbn [ms_regs restrict mkst] in Hr
end.
(* The base atoms of the current environment: the cursor (10), sp (2), the GOT word (object 1) and the shadow-base
   cell (object 12) keep their entry values. *)
Ltac rn_bases Ex c sp Uc Usp E1o E12o AG :=
let H10 := fresh "Ub10" in let H2 := fresh "Ub2" in let H1o := fresh "Ub1o" in let H12o := fresh "Ub12o" in
assert (H10 : bv_unsigned (ew Ex 10) = c) by (first [exact Uc | rewrite (AG 10%nat) by lia; exact Uc]);
assert (H2 : bv_unsigned (ew Ex 2) = sp) by (first [exact Usp | rewrite (AG 2%nat) by lia; exact Usp]);
assert (H1o : ew Ex (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (first [exact E1o | rewrite (AG (A_OBJ 1)) by (unfold A_OBJ; lia); exact E1o]);
assert (H12o : ew Ex (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (first [exact E12o | rewrite (AG (A_OBJ 12)) by (unfold A_OBJ; lia); exact E12o]).
(* At 0x81370 (slot 5156): s0 := k (slot 36), a2 := n' (slot 38), the cursor region := rn_cur2, and the regions
   but the last three (own frame, GOT word, cell) dropped. *)
Ltac rn_rebuild HS Hs0 Ha2 HCUR :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msr =>
  pose proof (st_ok_pi_set_reg Ex ssx msr 8%bv (SOff 36 0) HS
    ltac:(intros Hq; apply (f_equal bv_unsigned) in Hq; vm_compute in Hq; discriminate) Hs0) as HS1;
  clear HS; rename HS1 into HS end;
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msr =>
  pose proof (st_ok_pi_set_reg Ex ssx msr 12%bv (SOff 38 0) HS
    ltac:(intros Hq; apply (f_equal bv_unsigned) in Hq; vm_compute in Hq; discriminate) Ha2) as HS1;
  clear HS; rename HS1 into HS end;
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msr =>
  let rs := eval vm_compute in (skipn (length (ss_mem ssx) - 3) (ss_mem ssx)) in
  pose proof (st_ok_pi_submem Ex ssx msr rs HS ltac:(vm_compute; submem_tac) eq_refl) as HS1;
  clear HS; rename HS1 into HS end;
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msr =>
  pose proof (st_ok_pi_add_region Ex ssx msr rn_cur2 HS eq_refl HCUR) as HS1;
  clear HS; rename HS1 into HS end.
(* What the call keeps, step by step (BoxCJ.tcj_kept): a run or a memcpy keeps every byte outside the bytes E it may
   write and the own stack window; malloc keeps what acall_kept says. *)
Lemma tk_init : forall STK' lyc Sc W memc sp E,
(forall a, sp - STK' <= a < sp -> apresent (w_H W) memc a) -> tcj_kept B STK' lyc Sc W memc W memc sp E.
Proof.
intros STK' lyc Sc W memc sp E HP.
split; [intros; reflexivity|]. split; [intros; reflexivity|]. split; [intros; reflexivity|].
split; [intros; reflexivity|]. split; [intros a _ _ Ha; exact Ha | exact HP].
Qed.
Lemma tk_weaken : forall STK' lyc Sc W memc W2 m2 sp (E E' : Z -> Prop),
tcj_kept B STK' lyc Sc W memc W2 m2 sp E -> (forall a, E a -> E' a) -> tcj_kept B STK' lyc Sc W memc W2 m2 sp E'.
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
tcj_kept B STK' lyc Sc W memc W1 m1 sp E ->
(forall a, 0 <= a < 2 ^ 64 -> ~ E a -> ~ (sp - STK' <= a < sp) -> aview SEGS (w_H W2) m2 a = aview SEGS (w_H W1) m1 a) ->
(forall a, apresent (w_H W1) m1 a -> apresent (w_H W2) m2 a) ->
(forall a, sp - STK' <= a < sp -> apresent (w_H W2) m2 a) ->
tcj_kept B STK' lyc Sc W memc W2 m2 sp E.
Proof.
intros STK' lyc Sc W memc W1 m1 W2 m2 sp E mdx HAR Hsp HEi (K1 & K2 & K3 & K4 & K5 & K6) HK HP HP6.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split. { intros a Ha Hw He. rewrite (HK a ltac:(lia) He Hw). apply K1; assumption. }
split. { intros b m i Hin Hi He. destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hin) as (_ & H4096 & Hceil & _).
  rewrite (HK (b + i) ltac:(lia) He ltac:(lia)). apply (K2 b m i); assumption. }
split. { intros a Hi Hns Her. pose proof (pa_segs_low a Hi). unfold kLowMemEnd in *.
  rewrite (HK a ltac:(lia) (HEi a Hi) ltac:(lia)). apply K3; assumption. }
split. { intros cid pos a Hin Hz He. destruct (frame_zone SEGS B LAWS lyc Sc W memc mdx cid pos a HAR Hin Hz) as (Hz1 & Hz2).
  destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdx cid pos HAR Hin) as (Hf0 & _). unfold kLowMemEnd in Hz2.
  rewrite (HK a ltac:(lia) He ltac:(lia)). apply (K4 cid pos a Hin Hz He). }
split; [intros a Ha Hw Hp; apply HP; apply K5; assumption | exact HP6].
Qed.
Lemma tk_malloc : forall STK' lyc Sc W memc W1 m1 W2 m2 sp (E : Z -> Prop) slo shi (E2 : Z -> Prop),
tcj_kept B STK' lyc Sc W memc W1 m1 sp E ->
acall_kept SEGS B lyc Sc W1 m1 W2 m2 slo shi E2 ->
sp - STK' <= slo -> shi <= sp -> (forall a, E2 a -> E a) ->
(forall a, sp - STK' <= a < sp -> apresent (w_H W2) m2 a) ->
tcj_kept B STK' lyc Sc W memc W2 m2 sp E.
Proof.
intros STK' lyc Sc W memc W1 m1 W2 m2 sp E slo shi E2 (K1 & K2 & K3 & K4 & K5 & K6) (A1 & A2 & A3 & A4 & A5 & A6) Hlo Hhi HE2 HP6.
split. { intros a Ha Hw He. rewrite (A1 a Ha ltac:(lia)). apply K1; assumption. }
split. { intros b m i Hin Hi He. rewrite (A2 b m i Hin Hi (fun h => He (HE2 _ h))). apply (K2 b m i); assumption. }
split. { intros a Hi Hns Her. rewrite (A3 a Hi Hns Her). apply K3; assumption. }
split. { intros cid pos a Hin Hz He. rewrite (A4 cid pos a Hin Hz (fun h => He (HE2 _ h))). apply (K4 cid pos a Hin Hz He). }
split; [intros a Ha Hw Hp; apply A5; [exact Ha | lia | apply K5; assumption] | exact HP6].
Qed.
Lemma rn_req : forall kk, 0 <= kk -> req_size (kk + 1) = kk + 1.
Proof. intros kk H. unfold req_size. destruct (Z.eqb_spec (kk + 1) 0); lia. Qed.
(* memcpy's source: the k bytes after the length byte, in the caller's input block when n > 0, the empty range at p
   when n = 0; in either case apart from the new block (res, k + 1) and below the stack. *)
Lemma rn_src_ok : forall lyc Sc ly2 S2 W2 m2 md2 (regsT : bvmap 5 word) res p bi Li pl,
AR SEGS B ly2 S2 W2 m2 md2 -> ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, read_name_c.rn_k pl + 1)] ->
0 <= p -> p + rn_n pl <= 2 ^ 63 -> amem_range p (rn_n pl) ->
(pl <> [] -> In (bi, Li) (ablocks B lyc Sc) /\ bi <= p /\ p + rn_n pl <= bi + Li) ->
alloc_ceiling <= spZ regsT - ESTACK ->
0 <= p + rn_u pl /\ p + rn_u pl + read_name_c.rn_k pl <= 2 ^ 63 /\
src_ok SEGS W2 regsT m2 (p + rn_u pl) (read_name_c.rn_k pl) /\
(res + read_name_c.rn_k pl <= p + rn_u pl \/ p + rn_u pl + read_name_c.rn_k pl <= res) /\
amem_range (p + rn_u pl) (read_name_c.rn_k pl) /\
range_addressable (aview SEGS (w_H W2) m2) SHADOW_OFF (p + rn_u pl) (read_name_c.rn_k pl) /\
(0 < read_name_c.rn_k pl -> shadow_hull_vis (aview SEGS (w_H W2) m2) (p + rn_u pl) (read_name_c.rn_k pl)) /\
(res + read_name_c.rn_k pl + 1 <= p + rn_u pl \/ p + rn_u pl + read_name_c.rn_k pl <= res).
Proof.
intros lyc Sc ly2 S2 W2 m2 md2 regsT res p bi Li pl HAR Ebl Hp0 Hpn Hamr Hblk Hsp.
pose proof (rn_k_range pl) as Hk.
destruct pl as [|b0 rest].
{ unfold rn_u, rn_n in *. cbn [length Z.of_nat Z.min] in *. change (read_name_c.rn_k []) with 0 in *. rewrite Z.add_0_r.
  split; [lia|]. split; [lia|]. split; [intros a Ha; lia|]. split; [lia|]. split; [exact Hamr|].
  split; [apply range_addressable_nil; lia|]. split; lia. }
destruct (Hblk ltac:(discriminate)) as (Hbin & Hbi & Hbe).
assert (Hn1 : rn_n (b0 :: rest) = 1 + Z.of_nat (length rest)) by (unfold rn_n; cbn [length]; lia).
assert (Hu : rn_u (b0 :: rest) = 1) by (unfold rn_u; lia).
rewrite Hu. rewrite Hn1 in Hk, Hpn, Hbe. rewrite Hu in Hk.
assert (Hbin2 : In (bi, Li) (ablocks B ly2 S2)) by (rewrite Ebl; apply in_or_app; left; exact Hbin).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bi Li HAR Hbin2) as (_ & Hb4096 & Hbceil & Hbapp & Hbpres & _).
pose proof (req_size_pos0 Li ltac:(lia)) as HLi.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; [lia|]. split; [lia|].
split. { intros a Ha. split; [apply (aview_some_of_apresent SEGS); exact (proj1 (Hbpres a ltac:(lia))) | unfold ESTACK in *; lia]. }
assert (Hd : bi + req_size Li <= res \/ res + (read_name_c.rn_k (b0 :: rest) + 1) <= bi).
{ apply in_split in Hbin as (l1 & l2 & E1).
  pose proof (sep_blocks_pos SEGS B LAWS ly2 S2 W2 m2 md2 (bi, Li) (res, read_name_c.rn_k (b0 :: rest) + 1) l1 l2 [] HAR) as Hd.
  rewrite Ebl, E1, <- app_assoc in Hd. cbn [app] in Hd. specialize (Hd eq_refl).
  unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. rewrite rn_req in Hd by lia. lia. }
split; [lia|].
split; [eapply (amem_range_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR Hbin2); lia|].
split; [eapply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR Hbin2); lia|].
split; [intros Hk0; eapply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR Hbin2); lia | lia].
Qed.
(* After a run from 0x813a0 on: what the call kept, with the write set Ewr (the cursor and the new block). *)
Ltac rn_tkupd lyc Sc W memc mdc HAR sp Ewr HEimg TK HJc :=
lazymatch goal with HFr : frame_of ?Ex ?rsx (mrestrict (w_H ?Wx) ?m0) (mrestrict (w_H ?Wx) ?m1),
  HG : mem_grows (mrestrict (w_H ?Wx) ?m0) (mrestrict (w_H ?Wx) ?m1) |- _ =>
 let TK2 := fresh "TK" in
 assert (TK2 : tcj_kept B READ_NAME_STK lyc Sc W memc Wx m1 sp Ewr);
 [ apply (tk_step READ_NAME_STK lyc Sc W memc Wx m0 Wx m1 sp Ewr mdc HAR);
   [ unfold READ_NAME_STK, ASTACK in *; lia
   | exact HEimg
   | exact TK
   | intros a Ha HnE HnS;
     refine (kept_of_frame Ex rsx (w_H Wx) m0 m1 (fun x => Ewr x \/ (sp - READ_NAME_STK <= x < sp)) HFr _ a Ha _);
     [ intros bb wlo whi x Hin Hr;
       let wsv := eval vm_compute in (windows rsx) in change (In (bb, wlo, whi) wsv) in Hin;
       cbn [In] in Hin;
       repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hr|]); try contradiction;
       unfold read_name_c.rn_writes;
       repeat match goal with Hb : bv_unsigned (ew ?Ey ?nn) = _ |- _ =>
         match type of Hr with context [bv_unsigned (ew Ey nn)] => rewrite Hb in Hr end end;
       unfold READ_NAME_STK, ASTACK in *; lia
     | intros [h | h]; [exact (HnE h) | exact (HnS h)] ]
   | intros a Ha; exact (apresent_grows (w_H Wx) m0 m1 a HG Ha)
   | intros a Ha; pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJp & _);
     apply HJp; unfold READ_NAME_STK, ASTACK in *; lia ]
 | clear TK; rename TK2 into TK ]
end;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
(* A run's environment may grow by fresh slots: a slot no part of the state names may be set. *)
Lemma rn_st_ok_ewset : forall E ss ms n w, st_ok_pi SEGS VAL E ss ms ->
ss_atoms_p (fun m => negb (Nat.eqb m n)) ss = true -> st_ok_pi SEGS VAL (ewset E n w) ss ms.
Proof.
intros E ss ms n w HS Hat. unfold st_ok_pi in *.
eapply (st_ok_agree_p (fun m => negb (Nat.eqb m n)) SEGS); [exact HS | | destruct ss; exact Hat].
split; [|reflexivity]. intros m Hm. apply ew_ewset_other. apply negb_true_iff, Nat.eqb_neq in Hm. exact Hm.
Qed.
(* The name's bytes: the k input bytes after the length byte, then the terminating 0. *)
Lemma rn_bsub_nth : forall pl i, pl <> [] -> 0 <= i < read_name_c.rn_k pl ->
nth (Z.to_nat i) (Boxreg.bsub pl 1 (read_name_c.rn_k pl) ++ [Z_to_bv 8 0]) (Z_to_bv 8 0) =
nth (Z.to_nat (rn_u pl + i)) pl (Z_to_bv 8 0).
Proof.
intros [|b0 rest] i Hne Hi; [congruence|].
pose proof (rn_k_range (b0 :: rest)) as Hk. unfold rn_u, rn_n in *. cbn [length] in *.
unfold Boxreg.bsub. rewrite app_nth1.
- rewrite nth_firstn. destruct (Nat.ltb_spec (Z.to_nat i) (Z.to_nat (read_name_c.rn_k (b0 :: rest)))); [|lia].
  rewrite nth_skipn. replace (Z.to_nat 1 + Z.to_nat i)%nat with (Z.to_nat (Z.min (Z.of_nat (S (length rest))) 1 + i)) by lia.
  reflexivity.
- rewrite length_firstn, length_skipn. cbn [length]. lia.
Qed.
Lemma rn_bsub_last : forall pl,
nth (Z.to_nat (read_name_c.rn_k pl)) (Boxreg.bsub pl 1 (read_name_c.rn_k pl) ++ [Z_to_bv 8 0]) (Z_to_bv 8 0) = Z_to_bv 8 0.
Proof.
intros pl. pose proof (rn_k_range pl) as Hk. unfold rn_u, rn_n in Hk.
unfold Boxreg.bsub. rewrite app_nth2; rewrite length_firstn, length_skipn.
- replace (Z.to_nat (read_name_c.rn_k pl) - Init.Nat.min (Z.to_nat (read_name_c.rn_k pl)) (length pl - Z.to_nat 1))%nat with 0%nat by lia.
  reflexivity.
- lia.
Qed.
(* The cursor's two words after fuzz_take, as the symbolic run leaves them: p' + k at c, n' - k at c + 8. *)
Lemma rn_cur_word0 : forall E E0 p pl, (forall m, (m < 512)%nat -> ew E m = ew E0 m) ->
ew E0 36 = Z_to_bv 64 (read_name_c.rn_k pl) -> ew E0 37 = Z_to_bv 64 (p + rn_u pl) -> 0 <= p -> p + rn_n pl <= 2 ^ 63 ->
sv_denot E (SAlu ALU_ADD (SOff 36 0) (SOff 37 0)) = Z_to_bv 64 (p + tread_name_used pl).
Proof.
intros E E0 p pl AG H36 H37 Hp Hpn. pose proof (rn_k_range pl) as Hk. unfold rn_u, rn_n, tread_name_used in *.
rewrite denot_lit_U, U_SAlu. cbn [zalu_raw].
rewrite (rn_U_off E E0 36 _ 0 AG ltac:(lia) H36 ltac:(lia) ltac:(lia)), (rn_U_off E E0 37 _ 0 AG ltac:(lia) H37 ltac:(lia) ltac:(lia)).
f_equal. unfold zcanon, M64. rewrite Z.mod_small by lia. lia.
Qed.
Lemma rn_cur_word8 : forall E E0 pl, (forall m, (m < 512)%nat -> ew E m = ew E0 m) ->
ew E0 36 = Z_to_bv 64 (read_name_c.rn_k pl) -> ew E0 38 = Z_to_bv 64 (rn_n pl - rn_u pl) -> rn_n pl <= 2 ^ 63 ->
sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff 36 0) (SLit (-1))) (SOff 38 0)) = Z_to_bv 64 (rn_n pl - tread_name_used pl).
Proof.
intros E E0 pl AG H36 H38 Hn. pose proof (rn_k_range pl) as Hk. unfold rn_u, rn_n, tread_name_used in *.
rewrite denot_lit_U, U_SAlu, U_SMd, U_SLit. cbn [zalu_raw zmd_raw].
rewrite (rn_U_off E E0 36 _ 0 AG ltac:(lia) H36 ltac:(lia) ltac:(lia)), (rn_U_off E E0 38 _ 0 AG ltac:(lia) H38 ltac:(lia) ltac:(lia)).
f_equal. unfold zcanon, M64. change ((-1) mod 2 ^ 64) with 18446744073709551615.
rewrite !Z.add_0_r. rewrite Z.add_mod_idemp_l by lia.
replace (read_name_c.rn_k pl * 18446744073709551615 + (Z.of_nat (length pl) - Z.min (Z.of_nat (length pl)) 1))
  with ((Z.of_nat (length pl) - (Z.min (Z.of_nat (length pl)) 1 + read_name_c.rn_k pl)) + read_name_c.rn_k pl * 2 ^ 64) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
(* The byte s[k] the code clears (0x813c8): writable, no chunk yet. *)
Definition rn_sreg : YP09.region := YP09.mkRegion (Some 600%nat) 0 1 0 1 [].
(* After a run from 0x813b4 on: the k copied name bytes stay (the run writes only the cursor, the own frame and
   s[k]). *)
Ltac rn_nameupd c sp res pl NAME :=
lazymatch goal with HFr : frame_of ?Ex ?rsx (mrestrict (w_H ?Wx) ?m0) (mrestrict (w_H ?Wx) ?m1) |- _ =>
 let N2 := fresh "NAMEx" in
 assert (N2 : forall i, 0 <= i < read_name_c.rn_k pl ->
   aview SEGS (w_H Wx) m1 (res + i) = Some (bv_unsigned (nth (Z.to_nat (rn_u pl + i)) pl (Z_to_bv 8 0))));
 [ intros i Hi; rewrite <- (NAME i Hi);
   refine (kept_of_frame Ex rsx (w_H Wx) m0 m1
     (fun x => (c <= x < c + 16) \/ (sp - 48 <= x < sp) \/ x = res + read_name_c.rn_k pl) HFr _ (res + i) ltac:(lia) _);
   [ intros bb wlo whi x Hin Hr;
     let wsv := eval vm_compute in (windows rsx) in change (In (bb, wlo, whi) wsv) in Hin;
     cbn [In] in Hin;
     repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hr|]); try contradiction;
     repeat match goal with Hb : bv_unsigned (ew ?Ey ?nn) = _ |- _ =>
       match type of Hr with context [bv_unsigned (ew Ey nn)] => rewrite Hb in Hr end end;
     lia
   | lia ]
 | clear NAME; rename N2 into NAME ]
end.
Theorem pb_read_name : tread_name_spec.
Proof.
unfold tread_name_spec.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs c p bi Li pl
HJc Hra Hra4 Hgp Htp Hal16 Hwlo Hwhi H10 Hc8 Hcsp Hvp Hvn Hcra Hcw Hp0 Hpn Hamr Hblk Hbytes Hev Hlive Hmo Huniv.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJc as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & G1 & G2 & G3 & G4 & Hgone & Hpres & Hstk & G5 & HQT).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
destruct (rn_c_where STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs c HJc Hwlo Hcsp Hcw) as (Hsp & Hc16 & H47').
assert (RS : READ_NAME_STK = 16432) by reflexivity.
destruct (rn_entry STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs c p pl
  HJc H10 Hal16 Hwlo Hwhi Hc8 Hcsp Hvp Hvn Hcra Hcw Hp0 Hpn) as [HS SHOK].
assert (Hn64 : 0 <= rn_n pl /\ p + rn_n pl <= 2 ^ 63) by (unfold rn_n; lia).
remember (Eimg (Ereg regs (rn_extra p pl))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (rn_extra p pl)) n)
by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 c)
by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 p) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (rn_n pl)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (rn_x pl)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 (read_name_c.rn_k pl)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 (p + rn_u pl)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 5)).
assert (E38 : ew E 38 = Z_to_bv 64 (rn_n pl - rn_u pl)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 6)).
assert (HAE : env_agree 32 (Ereg regs (rn_extra p pl)) E)
by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (Uc : bv_unsigned (ew E 10) = c) by (rewrite E10; apply unsigned_lit_small; lia).
assert (E1o : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (apply (img_env_atomP E); [exact HEI | unfold A_OBJ, A_TEXT, A_LIM; lia]).
assert (E12o : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (apply (img_env_atomP E); [exact HEI | unfold A_OBJ, A_TEXT, A_LIM; lia]).
assert (Hrn : rn_n pl = Z.of_nat (length pl)) by reflexivity.
clear HE EL.
assert (AG : forall n, (n < 512)%nat -> ew E n = ew E n) by reflexivity.
assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (c <= a < c + 16) -> ~ (spZ regs - 48 <= a < spZ regs) ->
  aview SEGS (w_H W) memc a = aview SEGS (w_H W) memc a) by reflexivity.
assert (GR : forall a, apresent (w_H W) memc a -> apresent (w_H W) memc a) by auto.
assert (Hk47 := rn_k_range pl).
unfold cfg_at, A_read_nameP. change (w64 (BASE + AF_read_name)) with (Z_to_bv 64 (BASE + AF_read_name)).
(* 1. The frame, the saves, the shadow base, the load of n (its shadow byte is 0), up to the branch on n = 0. *)
paj_run_tok RUN HS HJc SHOK Bspan; [rn_awr c (spZ regs) sp0 Uc Usp Hcw |].
rn_kupd c (spZ regs) memc Uc Usp KR GR.
try clear HEI0.
psrr_branch_tok RUN BR HS SHOK Bspan.
all: rewrite branch_eq_U, (U_atom E 34 (rn_n pl) E34), U_lit in Hc by lia.
1: shelve.
(* n <> 0: the input bytes lie in the caller's heap block (bi, Li); the byte at p becomes a read-only region with
   its shadow entry. *)
assert (Hne : pl <> []) by (intros ->; cbn in Hc; discriminate).
destruct (Hblk Hne) as (Hbin & Hbi & Hbe).
pose proof (proj1 HJc) as HARc.
destruct (al_blocks _ _ LAWS _ _ _ _ _ bi Li HARc Hbin) as (_ & Hb4096 & Hbceil & Hbapp & _).
assert (Hn1 : 1 <= rn_n pl) by (destruct pl; [congruence | unfold rn_n; cbn [length]; lia]).
pose proof (req_size_pos0 Li ltac:(lia)) as HLi.
assert (Hx255 : 0 <= rn_x pl < 256) by (unfold rn_x; pose proof (bv_unsigned_in_range 8 (nth 0 pl (Z_to_bv 8 0))) as Hr8;
  change (bv_modulus 8) with 256 in Hr8; lia).
assert (Hxv : aview SEGS (w_H W) (ms_mem ms) p = Some (rn_x pl))
  by (rewrite KR by lia; replace p with (p + 0) by lia; rewrite (Hbytes 0 ltac:(lia)); reflexivity).
assert (HRp : region_ok SEGS E (ms_mem (restrict (w_H W) ms)) rn_preg).
{ unfold rn_preg, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val restrict ms_mem].
  rewrite E33, unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS E _ p 0 1 (SOff 35 0) (rn_x pl));
  [ cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
  rewrite Z.add_0_r. exact (rn_val_mem1 _ _ _ _ Hxv). }
lazymatch goal with HS : st_ok_pi _ _ _ ?ssx (restrict (w_H W) ms) |- _ =>
  pose proof (st_ok_pi_add_region E ssx _ rn_preg HS eq_refl HRp) as HS1 end.
match type of HS1 with ?A -> _ => assert (HDJ : A) end.
{ lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end.
  cbn [all_disjoint]. unfold extent_disjoint, rn_preg.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
  pose proof (blk_off_imgP B lyc Sc W _ _ bi Li HARc Hbin).
  pose proof (pa_obj_img 12 ltac:(lia)). pose proof (pa_obj_img 1 ltac:(lia)).
  pose proof (pa_val_range (A_OBJ 1)). pose proof (pa_val_range (A_OBJ 12)).
  unfold A_OBJ in *; cbn [Nat.add] in *.
  rewrite E33, Uc, Usp, E1o, E12o, !unsigned_lit_small by lia.
  repeat split; lia. }
specialize (HS1 HDJ). clear HS HDJ. rename HS1 into HS.
pose proof (st_ok_pi_add_fact E _ _ 33 (PTR 0) HS) as HS1.
match type of HS1 with ?A -> _ => assert (HDJ : A) end.
{ unfold afact_ok, PTR. cbn [af_lo af_hi af_al2]. rewrite E33, unsigned_lit_small by lia.
  rewrite Z.pow_0_r, Z.mod_1_r. lia. }
specialize (HS1 HDJ). clear HS HDJ. rename HS1 into HS.
assert (SHOK1 : sh_ok SEGS (SOff 32 0) (mkSHE 33 0 1 :: rn_SH0) E (mrestrict (w_H W) (ms_mem ms))).
{ apply Forall_cons; [|exact SHOK].
  apply (shent_ok_of_range SEGS (w_H W) (ms_mem ms) E (SOff 32 0) 33 p 1 p 0 1).
  - eapply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ bi Li p 1 HARc Hbin); lia.
  - rewrite U_SOff, E32, Z.add_0_r, unsigned_lit_small by (unfold SB; lia).
    rewrite zcanon_id by (unfold SB, M64; lia). reflexivity.
  - apply U_atom; [exact E33 | lia].
  - lia.
  - lia.
  - intros xx Hxx. cbn [Z.min Z.max] in Hxx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp.
    unfold SHADOW_OFF. lia. }
clear SHOK. rename SHOK1 into SHOK.
Unshelve.
(* 2. n <> 0: fuzz_u8 (n - 1 stored at c + 8, p + 1 at c, the byte x, x mod 48), then fuzz_take up to the branch
   k = min (x mod 48, n - 1). n = 0: k = 0, up to the same branch. *)
all: paj_run_tok RUN HS HJc SHOK Bspan; [rn_awr c (spZ regs) sp0 Uc Usp Hcw |].
all: rn_kupd c (spZ regs) memc Uc Usp KR GR.
all: rn_env HS AG.
all: psrr_branch_tok RUN BR HS SHOK Bspan.
all: paj_run_to_tok RUNTO HS HJc SHOK Bspan 5156; [rn_awr c (spZ regs) sp0 Uc Usp Hcw |].
all: rn_kupd c (spZ regs) memc Uc Usp KR GR.
all: rn_env HS AG.
all: lazymatch goal with HS : st_ok_pi _ _ ?Ex _ _ |- _ => rn_bases Ex c (spZ regs) Uc Usp E1o E12o AG end.
all: rn_reg HS (8%bv : bv 5) Rs0.
all: rn_reg HS (12%bv : bv 5) Ra2.
(* path C (n = 0 and 0 < n): impossible. *)
3: { exfalso. rewrite branch_ltu_U, U_lit, (rn_U_off _ E 34 (rn_n pl) 0 AG ltac:(lia) E34) in Hc0 by lia.
     apply Z.eqb_eq in Hc. apply Z.ltb_lt in Hc0. lia. }
(* 3. At 0x81370 each path names s0 = k, a2 = n' and the cursor (p', n') by the slots 36, 38, 37. *)
(* path A: n > 0, x mod 48 < n - 1, s0 = x mod 48. *)
1: rewrite branch_ltu_U in Hc0; fold rn_s0x in Hc0, Rs0;
   rewrite (rn_mod48 _ (rn_x pl) (eq_trans (AG 35%nat ltac:(lia)) E35) Hx255),
     (rn_U_off _ E 34 (rn_n pl) (-1) AG ltac:(lia) E34 ltac:(lia) ltac:(lia)) in Hc0; apply Z.ltb_lt in Hc0.
1: lazymatch goal with HS : st_ok_pi _ _ ?Ex _ _ |- _ =>
  assert (Hs0 : getr (ms_regs ms1) 8 = sv_denot Ex (SOff 36 0));
  [ rewrite Rs0; apply rn_den_eq;
    rewrite (rn_mod48 _ (rn_x pl) (eq_trans (AG 35%nat ltac:(lia)) E35) Hx255),
      (rn_U_off _ E 36 (read_name_c.rn_k pl) 0 AG ltac:(lia) E36 ltac:(lia) ltac:(lia));
    rewrite (rn_k_A pl Hne Hc0); lia
  | ];
  assert (Ha2 : getr (ms_regs ms1) 12 = sv_denot Ex (SOff 38 0));
  [ rewrite Ra2; apply rn_den_eq;
    rewrite (rn_U_off _ E 34 (rn_n pl) (-1) AG ltac:(lia) E34 ltac:(lia) ltac:(lia)),
      (rn_U_off _ E 38 (rn_n pl - rn_u pl) 0 AG ltac:(lia) E38 ltac:(unfold rn_u; lia) ltac:(unfold rn_u; lia));
    unfold rn_u; lia
  | ] end.
(* path B: n > 0, n - 1 <= x mod 48, s0 = n - 1. *)
2: rewrite branch_ltu_U in Hc0; fold rn_s0x in Hc0;
   rewrite (rn_mod48 _ (rn_x pl) (eq_trans (AG 35%nat ltac:(lia)) E35) Hx255),
     (rn_U_off _ E 34 (rn_n pl) (-1) AG ltac:(lia) E34 ltac:(lia) ltac:(lia)) in Hc0; apply Z.ltb_ge in Hc0.
2: lazymatch goal with HS : st_ok_pi _ _ ?Ex _ _ |- _ =>
  assert (Hs0 : getr (ms_regs ms1) 8 = sv_denot Ex (SOff 36 0));
  [ rewrite Rs0; apply rn_den_eq;
    rewrite (rn_U_off _ E 34 (rn_n pl) (-1) AG ltac:(lia) E34 ltac:(lia) ltac:(lia)),
      (rn_U_off _ E 36 (read_name_c.rn_k pl) 0 AG ltac:(lia) E36 ltac:(lia) ltac:(lia));
    rewrite (rn_k_B pl Hne ltac:(lia)); lia
  | ];
  assert (Ha2 : getr (ms_regs ms1) 12 = sv_denot Ex (SOff 38 0));
  [ rewrite Ra2; apply rn_den_eq;
    rewrite (rn_U_off _ E 34 (rn_n pl) (-1) AG ltac:(lia) E34 ltac:(lia) ltac:(lia)),
      (rn_U_off _ E 38 (rn_n pl - rn_u pl) 0 AG ltac:(lia) E38 ltac:(unfold rn_u; lia) ltac:(unfold rn_u; lia));
    unfold rn_u; lia
  | ] end.
(* path D: n = 0, s0 = n = 0. *)
3: apply Z.eqb_eq in Hc.
3: lazymatch goal with HS : st_ok_pi _ _ ?Ex _ _ |- _ =>
  assert (Hs0 : getr (ms_regs ms1) 8 = sv_denot Ex (SOff 36 0));
  [ rewrite Rs0; apply rn_den_eq;
    rewrite (rn_U_off _ E 34 (rn_n pl) 0 AG ltac:(lia) E34 ltac:(lia) ltac:(lia)),
      (rn_U_off _ E 36 (read_name_c.rn_k pl) 0 AG ltac:(lia) E36 ltac:(lia) ltac:(lia));
    rewrite (rn_k_D pl Hc); lia
  | ];
  assert (Ha2 : getr (ms_regs ms1) 12 = sv_denot Ex (SOff 38 0));
  [ rewrite Ra2; apply rn_den_eq;
    rewrite (rn_U_off _ E 34 (rn_n pl) 0 AG ltac:(lia) E34 ltac:(lia) ltac:(lia)),
      (rn_U_off _ E 38 (rn_n pl - rn_u pl) 0 AG ltac:(lia) E38 ltac:(unfold rn_u; lia) ltac:(unfold rn_u; lia));
    unfold rn_u; lia
  | ] end.
(* The cursor: region 1 (after the byte at p) when n > 0, region 0 when n = 0. *)
all: lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ssx ?msr |- _ =>
  let i := eval vm_compute in (match ss_mem ssx with r0 :: r1 :: _ => match YP09.r_base r0 with Some 10%nat => 0%nat | _ => 1%nat end | _ => 0%nat end) in
  let rr := eval vm_compute in (nth_error (ss_mem ssx) i) in
  lazymatch rr with Some ?r => pose proof (st_ok_pi_region_nth Ex ssx msr i r HS eq_refl) as HR0 end end.
all: lazymatch goal with HS : st_ok_pi _ _ ?Ex _ _ |- _ =>
  assert (HCUR : region_ok SEGS Ex (ms_mem (restrict (w_H W) ms1)) rn_cur2);
  [ apply (rn_cur_norm _ _ _ _ HR0); apply rn_den_eq;
    rewrite ?(rn_U_off _ E 37 (p + rn_u pl) 0 AG ltac:(lia) E37 ltac:(unfold rn_u; lia) ltac:(unfold rn_u; lia));
    rewrite ?(rn_U_off _ E 38 (rn_n pl - rn_u pl) 0 AG ltac:(lia) E38 ltac:(unfold rn_u; lia) ltac:(unfold rn_u; lia));
    first [ rewrite (rn_U_off _ E 33 p 1 AG ltac:(lia) E33 ltac:(lia) ltac:(lia)); unfold rn_u; lia
          | rewrite (rn_U_off _ E 33 p 0 AG ltac:(lia) E33 ltac:(lia) ltac:(lia)); unfold rn_u; lia
          | rewrite (rn_U_off _ E 34 (rn_n pl) (-1) AG ltac:(lia) E34 ltac:(lia) ltac:(lia)); unfold rn_u; lia
          | rewrite (rn_U_off _ E 34 (rn_n pl) 0 AG ltac:(lia) E34 ltac:(lia) ltac:(lia)); unfold rn_u; lia ]
  | ] end.
all: rn_rebuild HS Hs0 Ha2 HCUR.
all: match type of HS with ?A -> _ => assert (HDJ : A);
  [ lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
    cbn [all_disjoint]; unfold extent_disjoint, rn_cur2; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
    pose proof (pa_val_range (A_OBJ 1)); pose proof (pa_val_range (A_OBJ 12));
    pose proof (pa_obj_img 12 ltac:(lia)); pose proof (pa_obj_img 1 ltac:(lia));
    unfold A_OBJ in *; cbn [Nat.add] in *;
    rewrite Ub10, Ub2, Ub1o, Ub12o, !unsigned_lit_small by lia; repeat split; lia
  | specialize (HS HDJ); clear HDJ ] end.
all: clear Rs0 Ra2 Hs0 Ha2 HR0 HCUR.
all: lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
(* 4. fuzz_take's stores of the cursor (p' + k at c, n' - k at c + 8) and the call malloc (k + 1). *)
all: paj_run_tok RUN HS HJc SHOK Bspan; [rn_awr c (spZ regs) sp0 Uc Usp Hcw |].
all: rn_kupd c (spZ regs) memc Uc Usp KR GR.
all: rn_env HS AG.
(* 5. malloc (k + 1) by amalloc04_rule (YC85 amalloc04_sub): the call trace is [pc_malloc_ra0; A_read_name_mallocRA]
   (s0 = k < sp, so chain_pre's bad_next gives the empty chain). *)
all: assert (E2' : ew E 2 = Z_to_bv 64 (spZ regs)) by (rewrite E2; unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
all: assert (Hmra : A_read_name_mallocRA = BASE + 5204) by (unfold A_read_name_mallocRA, A_read_nameP, AF_read_name; lia).
all: pose proof (pal_rt_below B TL) as Hrtb.
all: lazymatch goal with HS : st_ok _ ?Ex _ (restrict _ ?msx) |- _ =>
  rn_reg HS (10%bv : bv 5) Ra0; rn_reg HS (1%bv : bv 5) Rra; rn_reg HS (2%bv : bv 5) Rsp;
  rn_reg HS (3%bv : bv 5) Rgp; rn_reg HS (4%bv : bv 5) Rtp; rn_reg HS (8%bv : bv 5) Rs0;
  assert (Qa0 : getr (ms_regs msx) 10 = w64 (read_name_c.rn_k pl + 1))
    by (rewrite Ra0, denot_lit_U, (rn_U_off _ E 36 (read_name_c.rn_k pl) 1 AG ltac:(lia) E36 ltac:(lia) ltac:(lia)); reflexivity);
  assert (Qsp : spZ (ms_regs msx) = sp0 + (spZ regs - 48 - sp0))
    by (unfold spZ at 1; rewrite Rsp; change (bv_unsigned (sv_denot Ex (SOff 2 (-48)))) with (U Ex (SOff 2 (-48)));
        rewrite (rn_U_off _ E 2 (spZ regs) (-48) AG ltac:(lia) E2' ltac:(lia) ltac:(lia)); lia);
  assert (Qgp : getr (ms_regs msx) 3 = w64 (as_gp B))
    by (rewrite Rgp; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; try rewrite (AG 3%nat) by lia; rewrite E3; exact Hgp);
  assert (Qtp : getr (ms_regs msx) 4 = w64 (as_tp B))
    by (rewrite Rtp; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; try rewrite (AG 4%nat) by lia; rewrite E4; exact Htp);
  assert (Qra : getr (ms_regs msx) 1 = Z_to_bv 64 (BASE + 5204))
    by (rewrite Rra; apply codeptr_val; assumption);
  assert (Qs0 : s0Z (ms_regs msx) = read_name_c.rn_k pl)
    by (unfold s0Z; rewrite Rs0; change (bv_unsigned (sv_denot Ex (SOff 36 0))) with (U Ex (SOff 36 0));
        rewrite (rn_U_off _ E 36 (read_name_c.rn_k pl) 0 AG ltac:(lia) E36 ltac:(lia) ltac:(lia)); lia);
  assert (Qraz : raZ (ms_regs msx) = BASE + 5204)
    by (unfold raZ; rewrite Qra; apply unsigned_lit_small; lia);
  assert (Qch : chain_pre lyc (aview SEGS (w_H W) (ms_mem msx)) (ms_regs msx) []);
  [ unfold chain_pre; split; [lia|];
    destruct (frame0_ok lyc (ms_regs msx)); [|reflexivity];
    unfold bad_next; rewrite Qs0, Qsp;
    replace (read_name_c.rn_k pl <=? sp0 + (spZ regs - 48 - sp0)) with true by (symmetry; apply Z.leb_le; lia); reflexivity
  | ];
  assert (Qtr : In (call_trace0 (pc_malloc_ra0 (as_code B)) (ms_regs msx) []) (as_universe B));
  [ rewrite call_trace_nil, Qraz; replace (BASE + 5204 =? pc_malloc_ra0 (as_code B)) with false by (symmetry; apply Z.eqb_neq; lia);
    rewrite <- Hmra; exact Huniv
  | ] end.
(* What the call kept so far: everything but the cursor and the own stack window. *)
all: lazymatch goal with HS : st_ok _ ?Ex _ (restrict _ ?msx) |- _ =>
  assert (TK : tcj_kept B READ_NAME_STK lyc Sc W memc W (ms_mem msx) (spZ regs) (fun a => c <= a < c + 16));
  [ apply (tk_step READ_NAME_STK lyc Sc W memc W memc W (ms_mem msx) (spZ regs) _ mdc HAR);
    [ unfold READ_NAME_STK, ASTACK in *; lia
    | intros a Hi Ha; pose proof (pa_segs_low a Hi); unfold kLowMemEnd in *; lia
    | apply tk_init; intros a Ha; apply Hpres; unfold READ_NAME_STK, ASTACK in *; lia
    | intros a Ha HnC HnS; apply KR; [lia | exact HnC | unfold READ_NAME_STK, ASTACK in *; lia]
    | intros a Ha; apply GR; exact Ha
    | intros a Ha; pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJp & _);
      apply HJp; unfold READ_NAME_STK, ASTACK in *; lia ]
  | ] end.
all: pmkst HS.
all: rewrite (pal_malloc B TL).
all: lazymatch goal with HS : st_ok _ ?Ex _ (restrict _ ?msx), HJc : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdx _ |- _ =>
  eapply SRr_bind;
  [ eapply (amalloc04_sub SEGS B LAWS Hsegs MT AM W (ms_regs msx) (ms_mem msx) STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdx k
      (read_name_c.rn_k pl + 1) (spZ regs - 48 - sp0) (Z_to_bv 64 (BASE + 5204)) [] HJc Qa0);
    [ unfold MALLOC_MAX; lia | unfold LIVE_READ_NAME in Hlive; lia | exact Qsp | lia | lia | unfold ASTACK; lia | exact Qgp | exact Qtp | exact Qra
    | apply ret_ok_codeptr_v; [lia | reflexivity] | unfold EV_READ_NAME in Hev; lia | exact Qch | exact Qtr | exact Hmo ]
  | ] end.
all: cbv beta; intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HJ2 & HP2 & Hres & Hfr2 & Hr4 & Hbl & HK & MLE & HJ1).
(* 6. Back from malloc at 0x813a0: the cursor and the own frame are kept (acall_kept); the block (res, k + 1) is
   new. *)
all: pose proof HK as (HK1 & HK2 & HK3 & HK4 & HK5 & HK6).
all: pose proof HJ2 as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJ2pres & _).
all: assert (TK1 : tcj_kept B READ_NAME_STK lyc Sc W memc W2 mem2 (spZ regs) (read_name_c.rn_writes c res (read_name_c.rn_k pl)));
  [ apply (tk_malloc _ _ _ _ _ _ _ _ _ _ (read_name_c.rn_writes c res (read_name_c.rn_k pl)) _ _ _
      (tk_weaken _ _ _ _ _ _ _ _ _ (read_name_c.rn_writes c res (read_name_c.rn_k pl)) TK (fun a Ha => or_introl Ha)) HK);
    [ unfold READ_NAME_STK, ASTACK; lia | lia
    | intros a Ha; right; replace (req_size (read_name_c.rn_k pl + 1)) with (read_name_c.rn_k pl + 1) in Ha
        by (unfold req_size; destruct (Z.eqb_spec (read_name_c.rn_k pl + 1) 0); lia); lia
    | intros a Ha; apply HJ2pres; unfold READ_NAME_STK, ASTACK in *; lia ]
  | clear TK ].
all: clear Ub10 Ub2 Ub1o Ub12o.
all: lazymatch goal with HS : st_ok _ ?Ex _ _ |- _ => rn_bases Ex c (spZ regs) Uc Usp E1o E12o AG end.
all: jafter_call_keep_hi HS 512%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0%nat; 1%nat] HS2.
all: match type of HS2 with ?tq -> _ => assert (HRK : tq);
  [ cbn [ms_mem restrict]; apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
    split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?Ub10, ?Ub2; intros a Ha;
    first [ apply (mbyte_of_aview SEGS); apply HK1; unfold READ_NAME_STK, ASTACK in *; lia
          | intros _; apply (apresent_writable SEGS); apply HJ2pres; unfold READ_NAME_STK, ASTACK in *; lia ]
  | specialize (HS2 HRK); clear HRK ] end.
all: clear HS; rewrite <- restrict_mkst_fx in HS2; rename HS2 into HS.
all: lazymatch type of HS with st_ok_pi _ _ ?Ex2 _ _ =>
  assert (HEIn : img_env VAL A_LIM Ex2) by (apply img_env_havoc_hi; [assumption | cbv; lia]) end.
all: rn_env HS AG.
all: lazymatch type of HS with st_ok_pi _ _ ?Ex2 _ _ =>
  assert (Ers : ew Ex2 516 = w64 res) by (cbn [ew havoc]; exact Hres);
  clear SHOK; assert (SHOK : sh_ok SEGS (SOff 32 0) [] Ex2 (mrestrict (w_H W2) mem2)) by constructor end.
all: rename HJc into HJm; rename HJ2 into HJc.
all: rename TK1 into TK.
all: pose proof (rn_req (read_name_c.rn_k pl) ltac:(lia)) as Hreq.
all: assert (Hinb : In (res, read_name_c.rn_k pl + 1) (ablocks B ly2 S2)) by (rewrite Hbl; apply in_or_app; right; left; reflexivity).
all: destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR2 Hinb) as (_ & Hs4096 & Hsceil & Hsapp & Hspres & _); try rewrite Hreq in Hsceil; try rewrite Hreq in Hsapp; try rewrite Hreq in Hspres.
all: assert (HEimg : forall a, in_img SEGS a -> ~ read_name_c.rn_writes c res (read_name_c.rn_k pl) a);
  [ intros a Hi [Ha | Ha]; pose proof (pa_segs_low a Hi); pose proof (pa_img_range a Hi);
    [ unfold kLowMemEnd in *; lia
    | pose proof (blk_off_imgP B ly2 S2 W2 mem2 md2 res _ HAR2 Hinb) as Hoff; try rewrite Hreq in Hoff; lia ]
  | ].
all: try clear Ub10 Ub2 Ub1o Ub12o; lazymatch goal with HS : st_ok_pi _ _ ?Ex _ _ |- _ => rn_bases Ex c (spZ regs) Uc Usp E1o E12o AG end.
(* 7. The NULL branch (beqz a0 at 0x813a0) is not taken: res >= 4096. *)
all: psrr_branch_tok RUN BR HS SHOK Bspan.
all: lazymatch goal with Hb : branch_taken BC_EQ (sv_denot ?Ex (SOff 516 0)) (sv_denot ?Ex (SLit 0)) = true |- _ =>
  exfalso; rewrite branch_eq_U, U_lit in Hb by lia; rewrite (U_atom Ex 516 res Ers) in Hb by lia; apply Z.eqb_eq in Hb; lia
  | _ => idtac end.
(* 8. memcpy (res, p', k). *)
all: paj_run_tok RUN HS HJc SHOK Bspan; [rn_awr c (spZ regs) sp0 Uc Usp Hcw |].
all: rn_tkupd lyc Sc W memc mdc HAR (spZ regs) (read_name_c.rn_writes c res (read_name_c.rn_k pl)) HEimg TK HJc.
all: rn_env HS AG.
all: try clear Ub10 Ub2 Ub1o Ub12o; lazymatch goal with HS : st_ok _ ?Ex _ _ |- _ => rn_bases Ex c (spZ regs) Uc Usp E1o E12o AG end.
all: lazymatch goal with HS : st_ok _ ?Ex _ (restrict _ ?msx) |- _ =>
  rn_reg HS (10%bv : bv 5) Rd; rn_reg HS (11%bv : bv 5) Rx; rn_reg HS (12%bv : bv 5) Rn; rn_reg HS (1%bv : bv 5) Rra2;
  rn_reg HS (2%bv : bv 5) Rsp2; rn_reg HS (3%bv : bv 5) Rgp2; rn_reg HS (4%bv : bv 5) Rtp2;
  assert (Ers2 : ew Ex 516 = Z_to_bv 64 res) by (repeat rewrite ew_ewset_other by lia; exact Ers);
  assert (Wd : getr (ms_regs msx) 10 = w64 res) by (rewrite Rd, denot_lit_U, (U_atom Ex 516 res Ers2) by lia; reflexivity);
  assert (Wx : getr (ms_regs msx) 11 = w64 (p + rn_u pl))
    by (rewrite Rx, denot_lit_U, (rn_U_off _ E 37 (p + rn_u pl) 0 AG ltac:(lia) E37 ltac:(unfold rn_u; lia) ltac:(unfold rn_u; lia)), Z.add_0_r; reflexivity);
  assert (Wn : getr (ms_regs msx) 12 = w64 (read_name_c.rn_k pl))
    by (rewrite Rn, denot_lit_U, (rn_U_off _ E 36 (read_name_c.rn_k pl) 0 AG ltac:(lia) E36 ltac:(lia) ltac:(lia)), Z.add_0_r; reflexivity);
  assert (Wsp : spZ (ms_regs msx) = sp0 + (spZ regs - 48 - sp0))
    by (unfold spZ at 1; rewrite Rsp2; change (bv_unsigned (sv_denot Ex (SOff 2 (-48)))) with (U Ex (SOff 2 (-48)));
        rewrite (rn_U_off _ E 2 (spZ regs) (-48) AG ltac:(lia) E2' ltac:(lia) ltac:(lia)); lia);
  assert (Wgp : getr (ms_regs msx) 3 = w64 (as_gp B))
    by (rewrite Rgp2; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; try rewrite (AG 3%nat) by lia; rewrite E3; exact Hgp);
  assert (Wtp : getr (ms_regs msx) 4 = w64 (as_tp B))
    by (rewrite Rtp2; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; try rewrite (AG 4%nat) by lia; rewrite E4; exact Htp);
  assert (Wra : getr (ms_regs msx) 1 = Z_to_bv 64 (BASE + 5224)) by (rewrite Rra2; apply codeptr_val; assumption)
end.
all: pmkst HS.
all: lazymatch goal with HS : st_ok _ ?Ex _ (restrict _ ?msx), HJc : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdx _ |- _ =>
  pose proof TK as TKm;
  destruct (rn_src_ok lyc Sc ly2 S2 W2 (ms_mem msx) mdx (ms_regs msx) res p bi Li pl (proj1 HJc) Hbl Hp0 (proj2 Hn64) Hamr Hblk
    ltac:(rewrite Wsp; unfold ESTACK, READ_NAME_STK, ASTACK in *; lia)) as (S1 & S2' & S3 & S4 & S5 & S6 & S7 & S8);
  eapply SRr_bind;
  [ eapply (aj_intrin_at SEGS B LAWS Hsegs OCpy (SIGMA BS___asan_memcpy) AMEMCPY W2 (ms_regs msx) (ms_mem msx) STK sp0 FP ly S W0 mem0 md0 own ly2 S2 mdx (k + 1) res (p + rn_u pl) (read_name_c.rn_k pl) (spZ regs - 48 - sp0) (Z_to_bv 64 (BASE + 5224)) HJc Wd Wx Wn);
    [ lia | lia | lia | exact Wsp | lia | lia | unfold ESTACK; lia | exact Wgp | exact Wtp | exact Wra
    | apply ret_ok_codeptr_v; [lia | reflexivity]
    | intros a Ha; split;
      [ replace a with (res + (a - res)) by lia; eapply (awr_new_block SEGS B LAWS); [exact HJm | exact HAR2 | exact Hbl | lia | exact Hinb | rewrite Hreq; lia]
      | unfold ESTACK; lia ]
    | eapply (amem_range_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJc) Hinb); try rewrite Hreq; lia
    | eapply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJc) Hinb); try rewrite Hreq; lia
    | intros Hk0; eapply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJc) Hinb); try rewrite Hreq; lia
    | exact (conj S1 (conj S2' (conj S3 (conj S4 (conj S5 (conj S6 S7)))))) ]
  | ] end.
all: cbv beta; intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hd3 & Heff3 & Hkeep3 & Hpres3).
(* 9. Back from memcpy at 0x813b4: the cursor and the own frame are kept; [res, res + k) holds the input bytes
   [p', p' + k). *)
all: pose proof HJ3 as (HAR3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJ3pres & _).
all: jafter_call_keep_hi HS 544%nat regs3 (mrestrict (w_H W2) mem3) HP3 [0%nat; 1%nat] HS2.
all: match type of HS2 with ?tq -> _ => assert (HRK : tq);
  [ cbn [ms_mem restrict]; apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
    split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?Ub10, ?Ub2; intros a Ha;
    first [ apply (mbyte_of_aview SEGS); apply Hkeep3; unfold ESTACK, READ_NAME_STK, ASTACK in *; lia
          | intros _; apply (apresent_writable SEGS); apply HJ3pres; unfold READ_NAME_STK, ASTACK in *; lia ]
  | specialize (HS2 HRK); clear HRK ] end.
all: clear HS; rewrite <- restrict_mkst_fx in HS2; rename HS2 into HS.
all: lazymatch type of HS with st_ok_pi _ _ ?Ex2 _ _ =>
  assert (HEIn2 : img_env VAL A_LIM Ex2) by (apply img_env_havoc_hi; [assumption | cbv; lia]);
  assert (Ers3 : ew Ex2 516 = Z_to_bv 64 res) by (rewrite ew_havoc_old by lia; exact Ers2) end.
all: rn_env HS AG.
all: rename HJc into HJpre; rename HJ3 into HJc.
all: assert (TK3 : tcj_kept B READ_NAME_STK lyc Sc W memc W2 mem3 (spZ regs) (read_name_c.rn_writes c res (read_name_c.rn_k pl)));
  [ eapply (tk_step READ_NAME_STK lyc Sc W memc W2 _ W2 mem3 (spZ regs) _ mdc HAR);
    [ unfold READ_NAME_STK, ASTACK in *; lia | exact HEimg | exact TK
    | intros a Ha HnE HnS; apply Hkeep3; [lia | intros h; apply HnE; right; lia | unfold ESTACK, READ_NAME_STK, ASTACK in *; lia]
    | exact Hpres3
    | intros a Ha; apply HJ3pres; unfold READ_NAME_STK, ASTACK in *; lia ]
  | ].
all: assert (NAME1 : forall i, 0 <= i < read_name_c.rn_k pl ->
    aview SEGS (w_H W2) mem3 (res + i) = Some (bv_unsigned (nth (Z.to_nat (rn_u pl + i)) pl (Z_to_bv 8 0))));
  [ intros i Hi; rewrite (Heff3 i Hi);
    assert (Hne' : pl <> []) by (intros Hq; subst pl; change (read_name_c.rn_k []) with 0 in Hi; lia);
    destruct (Hblk Hne') as (Hbin' & Hbi' & Hbe');
    destruct (al_blocks _ _ LAWS _ _ _ _ _ bi Li HAR Hbin') as (_ & Hb4096' & Hbceil' & _);
    pose proof (req_size_pos0 Li ltac:(lia)) as HLi';
    pose proof TKm as (_ & T2 & _);
    replace (p + rn_u pl + i) with (bi + (p + rn_u pl + i - bi)) by lia;
    rewrite (T2 bi Li (p + rn_u pl + i - bi) Hbin' ltac:(unfold rn_u, rn_n in *; lia)
      ltac:(unfold read_name_c.rn_writes, rn_u, rn_n in *; lia));
    replace (bi + (p + rn_u pl + i - bi)) with (p + (rn_u pl + i)) by lia;
    rewrite (Hbytes (rn_u pl + i) ltac:(unfold rn_u, rn_n in *; lia)); reflexivity
  | ].
all: clear TK; rename TK3 into TK.
all: try clear Ub10 Ub2 Ub1o Ub12o; lazymatch goal with HS : st_ok_pi _ _ ?Ex _ _ |- _ => rn_bases Ex c (spZ regs) Uc Usp E1o E12o AG end.
all: lazymatch type of HS with st_ok_pi _ _ ?Ex2 _ _ =>
  clear SHOK; assert (SHOK : sh_ok SEGS (SOff 32 0) [] Ex2 (mrestrict (w_H W2) mem3)) by constructor end.
(* 10. a0 := s + k (0x813b4), named by the fresh slot 600; s[k] becomes a writable region with its shadow entry. *)
all: paj_run_to_tok RUNTO HS HJc SHOK Bspan 5228; [rn_awr c (spZ regs) sp0 Uc Usp Hcw |].
all: rn_nameupd c (spZ regs) res pl NAME1.
all: rn_tkupd lyc Sc W memc mdc HAR (spZ regs) (read_name_c.rn_writes c res (read_name_c.rn_k pl)) HEimg TK HJc.
all: rn_env HS AG.
all: lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ss3 _ |- _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
all: lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ssx ?msr |- _ =>
  pose proof (rn_st_ok_ewset Ex ssx msr 600 (Z_to_bv 64 (res + read_name_c.rn_k pl)) HS ltac:(vm_compute; reflexivity)) as HS1;
  assert (HEI6 : img_env VAL A_LIM (ewset Ex 600 (Z_to_bv 64 (res + read_name_c.rn_k pl)))) by (apply img_env_ewset_hi; [assumption | cbv; lia]);
  assert (E600 : ew (ewset Ex 600 (Z_to_bv 64 (res + read_name_c.rn_k pl))) 600 = Z_to_bv 64 (res + read_name_c.rn_k pl)) by apply ew_ewset_same;
  assert (Ers5 : ew (ewset Ex 600 (Z_to_bv 64 (res + read_name_c.rn_k pl))) 516 = Z_to_bv 64 res)
    by (repeat rewrite ew_ewset_other by lia; exact Ers3);
  clear HS; rename HS1 into HS end.
all: rn_env HS AG.
all: try clear Ub10 Ub2 Ub1o Ub12o; lazymatch goal with HS : st_ok_pi _ _ ?Ex _ _ |- _ => rn_bases Ex c (spZ regs) Uc Usp E1o E12o AG end.
all: lazymatch goal with HS : st_ok_pi _ _ ?Ex _ _ |- _ =>
  assert (Ub600 : bv_unsigned (ew Ex 600) = res + read_name_c.rn_k pl) by (rewrite E600; apply unsigned_lit_small; lia) end.
all: rn_reg HS (10%bv : bv 5) Ra0f.
all: lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ssx ?msr |- _ =>
  assert (Ha0f : getr (ms_regs msr) 10 = sv_denot Ex (SOff 600 0));
  [ cbn [ms_regs restrict]; rewrite Ra0f; apply rn_den_eq;
    rewrite (U_atom Ex 600 (res + read_name_c.rn_k pl) E600) by lia;
    rewrite U_SAlu; cbn [zalu_raw];
    rewrite (U_atom Ex 516 res Ers5) by lia;
    rewrite (rn_U_off Ex E 36 (read_name_c.rn_k pl) 0 AG ltac:(lia) E36 ltac:(lia) ltac:(lia));
    unfold zcanon, M64; rewrite Z.mod_small by lia; lia
  | ];
  pose proof (st_ok_pi_set_reg Ex ssx msr 10%bv (SOff 600 0) HS
    ltac:(intros Hq; apply (f_equal bv_unsigned) in Hq; vm_compute in Hq; discriminate) Ha0f) as HS1;
  clear HS; rename HS1 into HS end.
all: lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ssx (restrict (w_H ?Wq) ?msx), HJc : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ (proj1 HJc) Hinb) as (_ & _ & _ & _ & Hspres2 & _);
  assert (HRs : region_ok SEGS Ex (ms_mem (restrict (w_H W2) msx)) rn_sreg);
  [ unfold rn_sreg, region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val restrict ms_mem];
    rewrite Ub600;
    split; [lia|]; split; [lia|]; split; [|constructor];
    intros o Ho; apply (apresent_writable SEGS);
    apply (proj1 (Hspres2 (res + read_name_c.rn_k pl + o) ltac:(try rewrite Hreq; lia)))
  | ];
  pose proof (st_ok_pi_add_region Ex ssx _ rn_sreg HS eq_refl HRs) as HS1 end.
all: match type of HS1 with ?A -> _ => assert (HDJ : A);
  [ lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
    cbn [all_disjoint]; unfold extent_disjoint, rn_sreg; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
    rewrite Ub600, Ub10, Ub2; unfold READ_NAME_STK, ASTACK in *; repeat split; lia
  | specialize (HS1 HDJ); clear HS HDJ; rename HS1 into HS ] end.
all: lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ssx ?msr |- _ =>
  pose proof (st_ok_pi_add_fact Ex ssx msr 600 (PTR 0) HS
    ltac:(unfold afact_ok, PTR; cbn [af_lo af_hi af_al2]; rewrite Ub600; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS1;
  clear HS; rename HS1 into HS end.
all: lazymatch goal with HS : st_ok_pi _ _ ?Ex _ (restrict (w_H ?Wq) ?msx), HJc : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  clear SHOK; assert (SHOK : sh_ok SEGS (SOff 32 0) [mkSHE 600 0 1] Ex (mrestrict (w_H W2) (ms_mem msx)));
  [ apply Forall_cons; [|apply Forall_nil];
    apply (shent_ok_of_range SEGS (w_H W2) (ms_mem msx) Ex (SOff 32 0) 600 (res + read_name_c.rn_k pl) 1 (res + read_name_c.rn_k pl) 0 1);
    [ eapply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJc) Hinb); try rewrite Hreq; lia
    | rewrite U_SOff, (AG 32%nat), E32, Z.add_0_r, unsigned_lit_small by (unfold SB; lia);
      rewrite zcanon_id by (unfold SB, M64; lia); reflexivity
    | apply U_atom; [exact E600 | lia]
    | lia | lia
    | intros xx Hxx; cbn [Z.min Z.max] in Hxx; unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hsapp; unfold SHADOW_OFF; lia ]
  | ] end.
(* 11. The shadow check of s[k] (its granule may be partial: the slow path at 0x813f4), the store s[k] = 0, the
   restores and the return. *)
all: paj_run_tok RUN HS HJc SHOK Bspan;
  [ lazymatch goal with |- awr_ok ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?lyx ?ownx =>
      let rs' := eval vm_compute in rsx in change (awr_ok Ex rs' stkx spx fpx b0x bcx lyx ownx) end;
    eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 600%nat (res + read_name_c.rn_k pl));
    [ reflexivity | exact Ub600
    | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; replace a with (res + (a - res)) by lia;
      eapply (awr_new_block SEGS B LAWS); [exact HJm | exact HAR2 | exact Hbl | lia | exact Hinb | rewrite Hreq; lia]
    | rn_awr c (spZ regs) sp0 Uc Usp Hcw ]
  | ].
all: rn_nameupd c (spZ regs) res pl NAME1.
all: rn_tkupd lyc Sc W memc mdc HAR (spZ regs) (read_name_c.rn_writes c res (read_name_c.rn_k pl)) HEimg TK HJc.
all: rn_env HS AG.
all: try clear Ub10 Ub2 Ub1o Ub12o; lazymatch goal with HS : st_ok_pi _ _ ?Ex _ _ |- _ => rn_bases Ex c (spZ regs) Uc Usp E1o E12o AG end.
all: lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ss3 _ |- _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
(* 12. The return: the name block's bytes, the cursor's words, and the post. *)
all: lazymatch goal with HS : st_ok_pi _ _ ?Ef ?ssf ?msr |- _ =>
  let rr0 := eval vm_compute in (nth_error (ss_mem ssf) 0) in
  let rr1 := eval vm_compute in (nth_error (ss_mem ssf) 1) in
  lazymatch rr0 with Some ?r0 => pose proof (st_ok_pi_region_nth Ef ssf msr 0 r0 HS eq_refl) as HRS end;
  lazymatch rr1 with Some ?r1 => pose proof (st_ok_pi_region_nth Ef ssf msr 1 r1 HS eq_refl) as HRC end end.
all: lazymatch goal with HS : st_ok_pi _ _ ?Ef _ (restrict _ ?msc) |- _ =>
  assert (Ub600f : bv_unsigned (ew Ef 600) = res + read_name_c.rn_k pl)
    by (repeat rewrite ew_ewset_other by lia; rewrite E600; apply unsigned_lit_small; lia);
  assert (VS0 : aview SEGS (w_H W2) (ms_mem msc) (res + read_name_c.rn_k pl) = Some (bv_unsigned (Z_to_bv 8 0)));
  [ pose proof (field_of_region Ef _ 600 (res + read_name_c.rn_k pl) _ _ _ _ _ 0 1%N (SLit 0) 0 HRS Ub600f
      ltac:(cbn [In]; auto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V;
    specialize (V 0%nat ltac:(cbn; lia)); change (res + read_name_c.rn_k pl + 0 + Z.of_nat 0) with (res + read_name_c.rn_k pl + 0 + 0) in V;
    rewrite !Z.add_0_r in V; unfold aview; cbn [ms_mem restrict] in V; rewrite V; reflexivity
  | ];
  assert (VC0 : val_mem SEGS (mrestrict (w_H W2) (ms_mem msc)) c 8 (p + tread_name_used pl));
  [ pose proof (field_of_region Ef _ 10 c _ _ _ _ _ 0 8%N _ (p + tread_name_used pl) HRC Ub10
      ltac:(cbn [In]; auto) (rn_cur_word0 Ef E p pl AG E36 E37 Hp0 (proj2 Hn64))
      ltac:(pose proof (rn_k_range pl); unfold tread_name_used, rn_u, rn_n in *; cbn; lia) ltac:(cbn; lia)) as V;
    rewrite Z.add_0_r in V; exact V
  | ];
  assert (VC8 : val_mem SEGS (mrestrict (w_H W2) (ms_mem msc)) (c + 8) 8 (Z.of_nat (length pl) - tread_name_used pl));
  [ pose proof (field_of_region Ef _ 10 c _ _ _ _ _ 8 8%N _ (rn_n pl - tread_name_used pl) HRC Ub10
      ltac:(cbn [In]; auto) (rn_cur_word8 Ef E pl AG E36 E38 ltac:(lia))
      ltac:(pose proof (rn_k_range pl); unfold tread_name_used, rn_u, rn_n in *; cbn; lia) ltac:(cbn; lia)) as V;
    exact V
  | ] end.
all: lazymatch goal with HS : st_ok_pi _ _ ?Ef ?ssf (restrict _ ?msc) |- _ =>
  prreg HS (1%bv : bv 5) Rraf; rn_reg HS (10%bv : bv 5) Ra0r;
  assert (Ersf : ew Ef 516 = Z_to_bv 64 res) by (repeat rewrite ew_ewset_other by lia; first [exact Ers3 | exact Ers5]);
  eapply (RET W2 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)); intros mat';
  unfold tread_name_post;
  exists ly2, S2, (ms_regs msc), (ms_mem msc); eexists; exists res end.
all: split; [cbn [ms_regs]; rewrite Rraf; try rewrite (AG 1%nat) by lia; rewrite E1, Hra; reflexivity|].
all: split; [replace (k + EV_READ_NAME) with (k + 1) by (unfold EV_READ_NAME; lia);
  apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJc|].
all: split; [lazymatch goal with HS : st_ok_pi _ _ ?Ef _ _ |- _ =>
    eapply (aregs_preserved_of_st_ok SEGS _ Ef _ _ regs (rn_extra p pl) HS);
    [ split; [intros n Hn; rewrite (AG n) by lia; exact (proj1 HAE n Hn) | cbn [ed ewset havoc]; exact (proj2 HAE)]
    | vm_compute; reflexivity ] end|].
all: split; [rewrite Ra0r, denot_lit_U, (U_atom _ 516 res Ersf) by lia; reflexivity|].
all: split; [exact Hfr2|].
all: split; [exact Hr4|].
all: split; [exact Hbl|].
all: split; [intros blc i Hin Hi; eapply (awr_new_block SEGS B LAWS); [exact HJm | exact HAR2 | exact Hbl | lia | exact Hin | rewrite Hreq; exact Hi]|].
all: split; [eapply (aftok_new_block SEGS B LAWS); [exact HJm | exact HAR2 | exact Hbl | lia]|].
all: split; [intros i Hi; destruct (Z.eq_dec i (read_name_c.rn_k pl)) as [Heq | Hne2];
  [ subst i; rewrite rn_bsub_last; exact VS0
  | rewrite (rn_bsub_nth pl i ltac:(intros Hq; rewrite Hq in Hi, Hne2; cbn in Hi, Hne2; lia) ltac:(lia));
    exact (NAME1 i ltac:(lia)) ]|].
all: split; [exact VC0|].
all: split; [exact VC8|].
all: split; [exact MLE|].
all: exact TK.
Qed.
End h.
End f.
End d.
