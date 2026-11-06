(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the contract and walk of ctrl_finish on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/YC20.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlFinish.v, with its module paths and numbers changed; 748 of its 814 lines of code are new or changed and 868 lines of the source are left out. *)
(* read_mac (fuzz_boxreg.asan-ubsan 0x81618, 133 instructions; C: fuzz/fuzz_boxreg.c:58-68, with fuzz_u8 of
   fuzz/fuzz.h:36-42 inlined): the contract of the ASan+UBSan build's code, in cgif's caller-journal form
   (proofs/cgif/cgif_file_fuzzer/lib/YC20.v:311-365; CONVENTIONS section 2) with the shapes of lib/B/Prog/BoxBCJ.v
   (tbwr_ok, tbcj_kept). The asan build inlines read_mac into LLVMFuzzerTestOneInput (no symbol, no call), so it has
   no A twin.
   What the code does. The function takes a 32-byte frame on the machine stack (addi sp,sp,-32; ra, s0..s2 saved) and
   gets a0 = c, the address of the caller's cursor struct fuzz_in { p at c, n at c + 8 }, a1 = full (the harness's
   op & 4) and a2 = mac. full <> 0 (beqz a1 0x81640 not taken): it traps (unimp 0x817d8) when c is not 8-aligned,
   then for i = 0 .. 5 runs fuzz_u8 (load n; when n = 0 the byte is 0, else store n - 1 at c + 8, load p, trap when p
   is NULL or p + 1 wraps (bgeu 0x816a4), store p + 1 at c, load the byte at p), traps when mac + i wraps (bltu
   0x816c8) and stores the byte at mac + i. full = 0: it copies the 5 bytes 00 40 ab 00 00 of the image's static
   read_mac.base (A_OBJ 6, 0x20d00; auipc/addi 0x81710) to mac with __asan_memcpy (mac, base, 5) (0x81720), traps when
   c is not 8-aligned, runs fuzz_u8 once (as above, 0x8172c-0x81798), traps when mac + 5 wraps (bltu 0x817a4) and stores
   the byte at mac + 5. With pl the n remaining input bytes the cursor advances by tbread_mac_used full n
   (min 1 n or min 6 n) and the 6 MAC bytes are tbread_mac_out full pl.
   UBSan traps, each refuted: c not 8-aligned by the premise c mod 8 = 0; p NULL or p + 1 wrapping by the input block
   (n > 0: 4096 <= bi <= p and p + n <= bi + Li below the allocator's ceiling); mac + i wrapping by afobj (the MAC
   lies in a side-stack frame, below the allocator's ceiling).
   Why the caller-journal form: both written ranges are in the caller's frames. The caller is LLVMFuzzerTestOneInput
   (calls at 0x803e4 and 0x80490): the cursor `struct fuzz_in in` is in its spill area on the machine stack (a0 =
   s1 + 136: s1 + 136 = p, s1 + 144 = n), between its own sp and its entry sp, so the right to write it is awr_byte's
   window case of the caller's journal; the MAC is its local uint8_t mac[6] (fuzz/fuzz_boxreg.c:206) at offset 32 of
   the 416-byte frame fb it takes from __asan_stack_malloc_3 (a2 = the word fb + 32 at s1 + 104), a frame it allocated
   itself, so the right to write it is awr_byte's frame case (in_frames ... own). The spec takes both as the premise
   tbwr_ok, and the MAC's place as afobj (the form of lib/A/Prog/ReacBoxregAdd.v and grant's CtrlChecksumVerify.v).
   Bytes of the caller written: exactly the 16 cursor bytes [c, c + 16) (8-byte stores at c + 8 and c) and the 6 MAC
   bytes [mac, mac + 6) (byte stores, or the memcpy of 5 bytes and one byte store). Besides those only the own window
   [sp - READ_MAC_STKB, sp) is written; the post's tbcj_kept says every other byte is kept. No allocator event: the
   journal's count stays k.
   The two written ranges are apart from each other and from the own window, by two premises: tbwr_ok alone lets the
   cursor lie in one of the caller's own side-stack frames (awr_byte's frame case) and so on the MAC, and then the
   cursor stores would overwrite MAC bytes (or the reverse) and the post's two byte claims could not both hold. The
   caller discharges both from its layout: the cursor is in its machine-stack spill area, the MAC in its side-stack
   frame, and AR's layout keeps the fake stack apart from the machine stack (layout_ok lo_disj, lib/Reusable/YG0f.v).
   Stack: the own 32-byte frame and ESTACK below it for the __asan_memcpy wrapper (aintrin_realizes OCpy at
   pa_sigma BB___asan_memcpy). No program callee.
   Read footprint, each byte covered by a premise: the 16 cursor bytes (val_mem; their shadow bytes, both 0 because c
   is 8-aligned and range_addressable c 16, refute the __asan_report_load8 / store8 branches); the input bytes
   [p, p + n) (their values, and for n > 0 the heap block of the caller that holds them, the driver's input block
   (p0, n0) of LLVMFuzzerTestOneInput's pre, whose shadow AR's block law gives for the load1 checks); the 5 bytes of
   read_mac.base at pa_val (A_OBJ 6) (their values and their start-up shadow, premises because the listing's check
   fixes the code only; the memcpy source); the shadow of the MAC bytes (afobj's range_addressable: the harness sets
   the granule's shadow byte to 6 at its loop top, so the store1 checks pass). The only other image reads are the GOT
   word of the shadow base and the shadow cell, both fixed by AR (AR_const_law).
   Hazards: afobj holds only on the fake-stack path (AR fixes the use-after-return flag cell to 1, so the harness takes
   it; see ReacBoxregAdd.v hazard (2)); full is the whole 64-bit register a1 (the code tests beqz a1, the harness passes
   op & 4 as an int: 0 or 4); the old walk's contract (a working branch 67b70ae1ec3 lib/B/Prog/read_mac_c.v) carries
   runtime cells (asan_cells, shadow_rw, MAC_BASE addressable) that leave the statement; no f* or csr instruction occurs
   in the 133 instructions (capstone scan, PROGRAM.md P1), so the fixed {fx} is sound.
   The memory model is the old walk's address-free one (read_mac_c.v mac_base, read_mac_used, read_mac_out), restated
   below over Z; there is no plain lib/Prog file for read_mac (the plain build inlines it). *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaRun PaShadow.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBSyms BoxBList BoxBPa.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaJournal BoxBase.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBCJ.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBPaLib YC1g YC1h BoxBFrame.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
(* The image's static const uint8_t base[5] of read_mac (fuzz/fuzz_boxreg.c:64), object A_OBJ 6 of boxb_listing. *)
Definition tbread_mac_base : list byte := map (Z_to_bv 8) [0; 0x40; 0xab; 0; 0].
(* How many input bytes a call consumes, from n remaining: one when full = 0, else up to six. *)
Definition tbread_mac_used (full n : Z) : Z := if full =? 0 then Z.min 1 n else Z.min 6 n.
(* The 6 MAC bytes it leaves, from the remaining input pl (fuzz_u8 gives 0 once the input is used up). *)
Definition tbread_mac_out (full : Z) (pl : list byte) : list byte :=
if full =? 0 then tbread_mac_base ++ firstn 1 (pl ++ [Z_to_bv 8 0])
else firstn 6 (pl ++ repeat (Z_to_bv 8 0) 6).
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg boxb_listing}.
#[local] Notation SEGS := (@pa_segs _ boxb_listing PI).
#[local] Notation VAL := (@pa_val _ boxb_listing PI).
#[local] Notation BASE := (@pa_val _ boxb_listing PI A_TEXT).
(* The function's address in the image and the stack it needs: its own 32-byte frame and ESTACK below it for the
   memcpy wrapper. *)
Definition AB_read_macP : Z := BASE + AF_read_mac.
Definition READ_MAC_STKB : Z := 32 + ESTACK.
Section h.
Variable B : asyms.
Definition tbread_mac_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
  (regs : bvmap 5 word) (c full mac p : Z) (pl : list byte) : world SEGS -> config -> Prop :=
fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W2 mem2 md2 k /\
aregs_preserved regs regs2 /\
(* the caller's MAC buffer *)
(forall i, 0 <= i < 6 ->
  aview SEGS (w_H W2) mem2 (mac + i) = Some (bv_unsigned (nth (Z.to_nat i) (tbread_mac_out full pl) (Z_to_bv 8 0)))) /\
(* the caller's cursor, advanced *)
val_mem SEGS (mrestrict (w_H W2) mem2) c 8 (p + tbread_mac_used full (Z.of_nat (length pl))) /\
val_mem SEGS (mrestrict (w_H W2) mem2) (c + 8) 8
  (Z.of_nat (length pl) - tbread_mac_used full (Z.of_nat (length pl))) /\
tbcj_kept B READ_MAC_STKB lyc Sc W memc W2 mem2 (spZ regs) (fun a => c <= a < c + 16 \/ mac <= a < mac + 6).
Definition tbread_mac_spec : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (c full mac p bi Li : Z)
  (pl : list byte),
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - READ_MAC_STKB -> spZ regs <= sp0 ->
getr regs 10 = w64 c -> getr regs 11 = w64 full -> getr regs 12 = w64 mac -> 0 <= full < 2 ^ 64 ->
(* the caller's cursor { p, n = length pl } at c, above sp, the caller's to let the call write *)
c mod 8 = 0 -> spZ regs <= c ->
val_mem SEGS (mrestrict (w_H W) memc) c 8 p ->
val_mem SEGS (mrestrict (w_H W) memc) (c + 8) 8 (Z.of_nat (length pl)) ->
range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF c 16 ->
tbwr_ok B STK sp0 FP ly S lyc Sc own W memc (spZ regs) c 16 ->
(* the remaining input bytes pl at p: a heap block holds them when there are any *)
0 <= p < 2 ^ 64 ->
(pl <> [] -> In (bi, Li) (ablocks B lyc Sc) /\ bi <= p /\ p + Z.of_nat (length pl) <= bi + Li) ->
(forall i, 0 <= i < Z.of_nat (length pl) ->
  aview SEGS (w_H W) memc (p + i) = Some (bv_unsigned (nth (Z.to_nat i) pl (Z_to_bv 8 0)))) ->
(* the caller's 6-byte MAC buffer: an object of a side-stack frame, the caller's to let the call write *)
afobj SEGS B lyc Sc W memc mac 6 ->
tbwr_ok B STK sp0 FP ly S lyc Sc own W memc (spZ regs) mac 6 ->
(* ... apart from the cursor and from the own window, the other bytes the call writes *)
(mac + 6 <= c \/ c + 16 <= mac) -> (mac + 6 <= spZ regs - READ_MAC_STKB \/ spZ regs <= mac) ->
(* the image's read_mac.base (A_OBJ 6): its 5 bytes and their shadow *)
(forall i, 0 <= i < 5 ->
  aview SEGS (w_H W) memc (VAL (A_OBJ 6) + i) =
  Some (bv_unsigned (nth (Z.to_nat i) tbread_mac_base (Z_to_bv 8 0)))) ->
range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF (VAL (A_OBJ 6)) 5 ->
shadow_hull_vis (aview SEGS (w_H W) memc) (VAL (A_OBJ 6)) 5 ->
SRr SEGS W (cfg_at SEGS AB_read_macP regs memc mdc)
(tbread_mac_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs c full mac p pl).
(* The walk. *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
#[local] Notation SIGMA := (@pa_sigma _ boxb_listing PI).
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA BB___asan_memcpy).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_boxb) (PI := PI).
(* The symbolic state at the first slot. Atom 32 is the shadow base, 33 the cursor's p, 34 its n (read as an atom
   when n >= 6), 35 .. 40 the input bytes pl[0..5]. k = min n 6 is the number of input bytes the walk may read; the
   walk is run once for each k. *)
Definition RM_SB : Z := 0x7fff8000.
Definition RMx : sv := SOff 32 0.
Definition RMspan : Z * Z := (RM_SB, RM_SB + 2 ^ 44 - 1).
Definition rm_nv (k : nat) : sv := if (k <? 6)%nat then SLit (Z.of_nat k) else SOff 34 0.
Definition rm_cur (k : nat) : YP09.region :=
YP09.mkRegion (Some 10%nat) 0 16 0 16 [YP09.mkChunk 0 (CVal 8 (SOff 33 0)); YP09.mkChunk 8 (CVal 8 (rm_nv k))].
Definition rm_mac : YP09.region := YP09.mkRegion (Some 12%nat) 0 6 0 6 [].
Definition rm_chunk (j : nat) : YP09.chunk := YP09.mkChunk (Z.of_nat j) (CVal 1 (SOff (35 + j) 0)).
Definition rm_in (k : nat) : YP09.region := YP09.mkRegion (Some 33%nat) 0 (Z.of_nat k) 0 0 (map rm_chunk (seq 0 k)).
Definition rm_regions (k : nat) : smem :=
[stack_region 32; got_regionP; bcell_regionP 32; rm_cur k; rm_mac] ++ (if (k =? 0)%nat then [] else [rm_in k]).
Definition rm_facts (k : nat) : facts :=
mkFacts ([(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF (2 ^ 46) (2 ^ 47 - 16) 3);
(12%nat, mkAF 4096 140737479966720 3); (32%nat, mkAF RM_SB RM_SB 0)] ++
(if (k =? 0)%nat then [] else [(33%nat, mkAF 4096 140737479966720 0)]) ++
(if (k <? 6)%nat then [] else [(34%nat, mkAF 6 (2 ^ 47) 0)]) ++
map (fun j => ((35 + j)%nat, mkAF 0 255 0)) (seq 0 6)) [] [].
Definition ss_rm (k : nat) : sstate := mkSS AF_read_mac sr_atoms (rm_regions k) None (rm_facts k).
Definition rm_SH (k : nat) : list shent :=
[mkSHE 10 0 16; mkSHE 12 0 6] ++ (if (k =? 0)%nat then [] else [mkSHE 33 0 (Z.of_nat k)]).
Definition rmb (pl : list byte) (j : nat) : Z := bv_unsigned (nth j pl (Z_to_bv 8 0)).
Definition rm_extra (p n : Z) (pl : list byte) : list word :=
Z_to_bv 64 RM_SB :: Z_to_bv 64 p :: Z_to_bv 64 n :: map (fun j => Z_to_bv 64 (rmb pl j)) (seq 0 6).
Definition ERM (regs : bvmap 5 word) (p n : Z) (pl : list byte) : env := Eimg (Ereg regs (rm_extra p n pl)).
Lemma rmb_range : forall pl j, 0 <= rmb pl j < 256.
Proof.
intros pl j. unfold rmb. pose proof (bv_unsigned_in_range 8 (nth j pl (Z_to_bv 8 0))) as R.
change (bv_modulus 8) with 256 in R. exact R.
Qed.
Lemma rm_ew : forall regs p n pl,
ew (ERM regs p n pl) 32 = Z_to_bv 64 RM_SB /\ ew (ERM regs p n pl) 33 = Z_to_bv 64 p /\
ew (ERM regs p n pl) 34 = Z_to_bv 64 n /\
(forall j, (j < 6)%nat -> ew (ERM regs p n pl) (35 + j) = Z_to_bv 64 (rmb pl j)).
Proof.
intros regs p n pl. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
intros j Hj. do 6 (destruct j as [|j]; [reflexivity|]). lia.
Qed.
Lemma rm_afact : forall E n v lo hi al, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> lo <= v <= hi ->
v mod 2 ^ al = 0 -> 0 <= al <= 64 -> afact_ok E n (mkAF lo hi al).
Proof.
intros E n v lo hi al H Hv Hlh Hal Hal2. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite H, unsigned_lit_small by lia. split; [lia|]. split; [exact Hal | lia].
Qed.
Lemma rm_aview_val : forall (W : world SEGS) mem a v,
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
Local Ltac rm_af :=
lazymatch goal with |- afact_ok ?E ?n (mkAF ?lo ?hi ?al) =>
let Hn := lazymatch goal with H : ew E n = Z_to_bv 64 _ |- _ => H end in
eapply (rm_afact E n _ lo hi al Hn);
[ lia | lia
| first [ change (2 ^ 0) with 1; apply Z.mod_1_r | change (2 ^ 3) with 8; lia | change (2 ^ 4) with 16; lia ]
| lia ] end.
(* The cursor lies in the caller's stack window, above sp: the only case of awr_byte above the allocator's ceiling. *)
Lemma rm_c16 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc kk (regs : bvmap 5 word) c,
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc kk ->
sp0 - STK <= spZ regs - READ_MAC_STKB -> spZ regs <= c ->
tbwr_ok B STK sp0 FP ly S lyc Sc own W memc (spZ regs) c 16 -> c + 16 <= sp0.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc kk regs c HJ Hwlo Hspc HWc.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _ & _).
pose proof Hstk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : READ_MAC_STKB = 4128) by reflexivity.
destruct (HWc (c + 15) ltac:(lia)) as (Hw & _ & _ & _).
destruct (awr_byte_cases SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (c + 15) HJ Hw) as (_ & Hcs).
destruct Hcs as [(_ & Hw1) | [(Ha & _) | (cid & pos & _ & [(Ha & _) | (Ha & _)])]].
- lia.
- apply app_addr_below_ceil in Ha. unfold ASAN_CEIL in Ha. lia.
- apply app_addr_below_ceil in Ha. unfold ASAN_CEIL in Ha. lia.
- lia.
Qed.
(* The input bytes lie in the caller's heap block when there are any. *)
Lemma rm_blk : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc kk (p bi Li : Z) (pl : list byte),
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc kk ->
(pl <> [] -> In (bi, Li) (ablocks B lyc Sc) /\ bi <= p /\ p + Z.of_nat (length pl) <= bi + Li) ->
(0 < length pl)%nat ->
In (bi, Li) (ablocks B lyc Sc) /\ 4096 <= p /\ bi <= p /\
p + Z.of_nat (length pl) <= bi + req_size Li /\ bi + req_size Li <= alloc_ceiling /\ in_app bi (req_size Li).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc kk p bi Li pl HJ Hblk Hl.
pose proof HJ as (HAR & _).
assert (Hne : pl <> []) by (intros Hnil; rewrite Hnil in Hl; cbn in Hl; lia).
destruct (Hblk Hne) as (Hin & Hb1 & Hb2).
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bi Li HAR Hin) as (_ & Hb4096 & Hbceil & Hbia & _).
assert (HLi : Li <= req_size Li) by (unfold req_size; destruct (Li =? 0) eqn:EL; [apply Z.eqb_eq in EL; lia | lia]).
split; [exact Hin|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact Hbia].
Qed.
Lemma rm_n47 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc kk (p bi Li : Z) (pl : list byte),
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc kk ->
(pl <> [] -> In (bi, Li) (ablocks B lyc Sc) /\ bi <= p /\ p + Z.of_nat (length pl) <= bi + Li) ->
0 <= p -> Z.of_nat (length pl) <= 2 ^ 47.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc kk p bi Li pl HJ Hblk Hp.
pose proof (asan_consts) as (C1 & _).
destruct (Nat.eq_dec (length pl) 0) as [H0|H0]; [rewrite H0; lia|].
destruct (rm_blk STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc kk p bi Li pl HJ Hblk ltac:(lia)) as (_ & _ & _ & Hb2 & Hbc & _).
lia.
Qed.
(* The entry: the symbolic state at the first slot holds, and so do the shadow entries of the cursor, the MAC and the
   input bytes the walk reads. *)
Lemma rm_entry : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc kk (regs : bvmap 5 word)
(c mac p bi Li : Z) (pl : list byte) (k : nat),
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc kk ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - READ_MAC_STKB -> spZ regs <= sp0 ->
getr regs 10 = w64 c -> getr regs 12 = w64 mac ->
c mod 8 = 0 -> spZ regs <= c ->
val_mem SEGS (mrestrict (w_H W) memc) c 8 p ->
val_mem SEGS (mrestrict (w_H W) memc) (c + 8) 8 (Z.of_nat (length pl)) ->
range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF c 16 ->
tbwr_ok B STK sp0 FP ly S lyc Sc own W memc (spZ regs) c 16 ->
0 <= p < 2 ^ 64 ->
(pl <> [] -> In (bi, Li) (ablocks B lyc Sc) /\ bi <= p /\ p + Z.of_nat (length pl) <= bi + Li) ->
(forall i, 0 <= i < Z.of_nat (length pl) -> aview SEGS (w_H W) memc (p + i) = Some (rmb pl (Z.to_nat i))) ->
afobj SEGS B lyc Sc W memc mac 6 ->
tbwr_ok B STK sp0 FP ly S lyc Sc own W memc (spZ regs) mac 6 ->
(k <= 6)%nat -> k = Nat.min (length pl) 6 ->
st_ok_pi SEGS VAL (ERM regs p (Z.of_nat (length pl)) pl) (ss_rm k)
(restrict (w_H W) (mkst regs (Z_to_bv 64 AB_read_macP) memc (seg_rom SEGS)))
/\ sh_ok SEGS RMx (rm_SH k) (ERM regs p (Z.of_nat (length pl)) pl) (mrestrict (w_H W) memc).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc kk regs c mac p bi Li pl k
HJ Hal16 Hwlo Hwhi H10 H12 Hc8 Hspc Hcp Hcn HRAc HWc Hp64 Hblk HPL HFO HWm Hk6 Hkd.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _ & _).
pose proof Hstk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : READ_MAC_STKB = 4128) by reflexivity.
assert (HSB : RM_SB = 2147450880) by reflexivity.
(* the cursor is in the caller's stack window, above sp *)
pose proof (rm_c16 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc kk regs c HJ Hwlo Hspc HWc) as Hc16.
(* the MAC is in a side-stack frame *)
pose proof HFO as ((cid & pos & Hfin & Hcid & Hfal & Hflo & Hfhi) & Hm8 & HRAm).
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hfin) as (Hf4096 & Hfceil & Hfapp).
pose proof (frm_off_imgP B lyc Sc W memc mdc cid pos HAR Hfin) as Hfimg.
destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD.
pose proof (pa_obj_img 1 ltac:(lia)) as HgotR.
(* the input bytes are in a heap block when there are any *)
assert (HBI := rm_blk STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc kk p bi Li pl HJ Hblk).
pose proof (rm_n47 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc kk p bi Li pl HJ Hblk ltac:(lia)) as Hn47.
rewrite restrict_mkst_fx.
destruct (rm_ew regs p (Z.of_nat (length pl)) pl) as (E32 & E33 & E34 & EB).
set (E := ERM regs p (Z.of_nat (length pl)) pl) in *.
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (rm_extra p (Z.of_nat (length pl)) pl)) n)
by (intros n Hn; subst E; unfold ERM; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 c) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E12 : ew E 12 = Z_to_bv 64 mac) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (Eo12 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; unfold ERM; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Eo1 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; unfold ERM; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (E2' : ew E 2 = Z_to_bv 64 (spZ regs)) by (rewrite E2; unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
pose proof (EB 0%nat ltac:(lia)) as E35. pose proof (EB 1%nat ltac:(lia)) as E36. pose proof (EB 2%nat ltac:(lia)) as E37.
pose proof (EB 3%nat ltac:(lia)) as E38. pose proof (EB 4%nat ltac:(lia)) as E39. pose proof (EB 5%nat ltac:(lia)) as E40.
cbn [Nat.add] in E35, E36, E37, E38, E39, E40.
pose proof (rmb_range pl 0) as R35. pose proof (rmb_range pl 1) as R36. pose proof (rmb_range pl 2) as R37.
pose proof (rmb_range pl 3) as R38. pose proof (rmb_range pl 4) as R39. pose proof (rmb_range pl 5) as R40.
(* the regions *)
assert (RCUR : region_ok SEGS E (mrestrict (w_H W) memc) (rm_cur k)).
{ unfold rm_cur, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
rewrite (VB 10%nat c E10) by lia.
split; [lia|]. split; [lia|].
split; [intros o Ho; apply (apresent_writable SEGS); exact (proj1 (proj2 (HWc (c + o) ltac:(lia))))|].
constructor; [|constructor; [|constructor]].
- apply (chunk_ok_val SEGS E _ c 0 8 (SOff 33 0) p);
[cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact Hcp].
- unfold rm_nv. destruct (k <? 6)%nat eqn:Hk.
+ apply Nat.ltb_lt in Hk.
apply (chunk_ok_val SEGS E _ c 8 8 (SLit (Z.of_nat k)) (Z.of_nat (length pl)));
[cbn [sv_denot]; f_equal; lia | zside | zside | exact Hcn].
+ apply (chunk_ok_val SEGS E _ c 8 8 (SOff 34 0) (Z.of_nat (length pl)));
[cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Hcn]. }
assert (RMAC : region_ok SEGS E (mrestrict (w_H W) memc) rm_mac).
{ unfold rm_mac, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
rewrite (VB 12%nat mac E12) by lia. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). exact (proj1 (proj2 (HWm (mac + o) ltac:(lia)))). }
assert (RIN : (0 < k)%nat -> region_ok SEGS E (mrestrict (w_H W) memc) (rm_in k)).
{ intros Hk0. destruct (HBI ltac:(lia)) as (Hin & Hp4096 & Hb1 & Hb2 & Hbceil & Hbia).
unfold rm_in, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
rewrite (VB 33%nat p E33) by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_forall. intros ch Hch. apply in_map_iff in Hch as (j & <- & Hj). apply in_seq in Hj.
unfold rm_chunk.
apply (chunk_ok_val SEGS E _ p (Z.of_nat j) 1 (SOff (35 + j) 0) (rmb pl j)).
- cbn [sv_denot]. rewrite (EB j) by lia. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- pose proof (rmb_range pl j). zside.
- zside.
- apply rm_aview_val; [|apply rmb_range].
pose proof (HPL (Z.of_nat j) ltac:(lia)) as Hj'. rewrite Nat2Z.id in Hj'. exact Hj'. }
(* the shadow entries *)
assert (HSH : sh_ok SEGS RMx (rm_SH k) E (mrestrict (w_H W) memc)).
{ assert (UB : U E RMx = SHADOW_OFF) by (unfold RMx; rewrite (U_atom E 32 RM_SB E32) by lia; reflexivity).
unfold sh_ok, rm_SH. apply Forall_app. split.
- constructor; [|constructor; [|constructor]].
+ apply (shent_ok_of_range SEGS (w_H W) memc E RMx 10 c 16 c 0 16 HRAc UB (U_atom E 10 c E10 ltac:(lia))); [lia | lia |].
intros x Hx. unfold SHADOW_OFF. lia.
+ apply (shent_ok_of_range SEGS (w_H W) memc E RMx 12 mac 6 mac 0 6 HRAm UB (U_atom E 12 mac E12 ltac:(lia))); [lia | lia |].
intros x Hx. revert Hfapp Hflo Hfhi Hx. clear. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg. intros. lia.
- destruct (k =? 0)%nat eqn:Hk0; [constructor|]. apply Nat.eqb_neq in Hk0.
destruct (HBI ltac:(lia)) as (Hin & Hp4096 & Hb1 & Hb2 & Hbceil & Hbia).
constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) memc E RMx 33 p (Z.of_nat k) p 0 (Z.of_nat k)); [| exact UB | apply (U_atom E 33 p E33); lia | lia | lia |].
  + eapply (range_addressable_of_block SEGS B LAWS lyc Sc W memc mdc bi Li p (Z.of_nat k) HAR Hin); lia.
+ intros x Hx. revert Hbia Hb1 Hb2 Hx Hkd. clear. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg. intros. lia. }
split; [|exact HSH].
unfold ss_rm, AB_read_macP. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- destruct k as [|[|[|[|[|[|[|k]]]]]]]; [ idtac .. | exfalso; lia ]; vm_compute; reflexivity.
- unfold rm_regions. apply Forall_app. split.
+ unfold stack_region, got_regionP, bcell_regionP.
constructor; [|constructor; [|constructor; [|constructor; [exact RCUR|constructor; [exact RMAC|constructor]]]]];
unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
* cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
* rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Eo1) by (pose proof (pa_val_range (A_OBJ 1)); lia).
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
[cbn [sv_denot]; rewrite Eo12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kgot).
* rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) Eo12) by (pose proof (pa_val_range (A_OBJ 12)); lia).
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 RMx RM_SB);
[cbn [sv_denot RMx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | rewrite HSB; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kcell).
+ destruct (k =? 0)%nat eqn:Hk0; [constructor|]. apply Nat.eqb_neq in Hk0. constructor; [apply RIN; lia | constructor].
- apply pairwise_disjoint_of_extents.
assert (Hk0 : k = 0%nat \/ (0 < k)%nat) by lia. destruct Hk0 as [-> | Hk0].
+ unfold rm_regions, rm_cur, rm_mac, stack_region, got_regionP, bcell_regionP, extent_of_region.
cbn [app Nat.eqb map YP09.r_base YP09.r_lo YP09.r_hi].
rewrite (VB 10%nat c E10), (VB 12%nat mac E12) by lia.
rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Eo1), (VB (A_OBJ 12) (VAL (A_OBJ 12)) Eo12)
by (pose proof (pa_val_range (A_OBJ 1)); pose proof (pa_val_range (A_OBJ 12)); lia).
cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 Hwlo Hwhi Hspc Hc16 HcellR HgcD HgotR Hf4096 Hfceil Hflo Hfhi Hfimg.
clear. intros. repeat split; lia.
+ destruct (HBI ltac:(lia)) as (Hin & Hp4096 & Hb1 & Hb2 & Hbceil & Hbia).
pose proof (blk_off_imgP B lyc Sc W memc mdc bi Li HAR Hin) as Hbimg.
pose proof (sep_block_frame SEGS B LAWS lyc Sc W memc mdc bi Li cid pos HAR Hin Hfin) as Hbf.
unfold zdisjoint in Hbf. cbn [fst snd] in Hbf.
unfold rm_regions. replace (k =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
unfold rm_cur, rm_mac, rm_in, stack_region, got_regionP, bcell_regionP, extent_of_region.
cbn [app map YP09.r_base YP09.r_lo YP09.r_hi].
rewrite (VB 10%nat c E10), (VB 12%nat mac E12), (VB 33%nat p E33) by lia.
rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Eo1), (VB (A_OBJ 12) (VAL (A_OBJ 12)) Eo12)
by (pose proof (pa_val_range (A_OBJ 1)); pose proof (pa_val_range (A_OBJ 12)); lia).
cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 Hwlo Hwhi Hspc Hc16 HcellR HgcD HgotR Hf4096 Hfceil Hflo Hfhi Hfimg
Hp4096 Hb1 Hb2 Hbceil Hbimg Hbf Hkd Hk6 Hk0.
clear. intros. repeat split; lia.
- split; [|split; exact I].
unfold rm_facts. cbn [f_atoms].
destruct k as [|[|[|[|[|[|[|k]]]]]]]; [ idtac .. | exfalso; lia ];
try (destruct (HBI ltac:(lia)) as (_ & Hp4096 & Hb1 & Hb2 & Hbceil & _));
cbn [atoms_ok app map seq Nat.add Nat.eqb Nat.ltb Nat.leb];
repeat match goal with |- afact_ok _ _ _ /\ _ => split; [rm_af|] end; exact I.
Qed.
(* The write windows of a run: the own frame (the stack region at sp), the cursor and the MAC. *)
Local Ltac rm_awr sp0 spv cv mv Usp E10 E12 HcW HmW :=
lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk s0 fp b0 bc ly own) end;
repeat first
[ apply awr_ok_nil
| apply awr_ok_cons_ro; [cbn; lia|]
| eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spv - sp0));
[ reflexivity | cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; rewrite Usp; lia | cbn; lia | cbn; lia | ]
| eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 10%nat cv);
[ reflexivity | cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; rewrite E10; apply unsigned_lit_small; lia
| cbn [YP09.r_wlo YP09.r_whi]; intros aa Haa; exact (proj1 (HcW aa ltac:(lia))) | ]
| eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 12%nat mv);
[ reflexivity | cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; rewrite E12; apply unsigned_lit_small; lia
| cbn [YP09.r_wlo YP09.r_whi]; intros aa Haa; exact (proj1 (HmW aa ltac:(lia))) | ] ].
(* The facts the walk uses at its stops. *)
(* 0x81640 beqz a1: the branch on full. *)
Lemma rm_full_br : forall E full b, ew E 11 = Z_to_bv 64 full -> 0 <= full < 2 ^ 64 ->
branch_taken BC_EQ (sv_denot E (SOff 11 0)) (sv_denot E (SLit 0)) = b -> (full =? 0) = b.
Proof.
intros E full b H Hf Hb. rewrite branch_eq_U, (U_atom E 11 full H Hf), (U_lit E 0 ltac:(lia)) in Hb. exact Hb.
Qed.
(* 0x816c8 bltu a4, a3 (a4 = ~mac, a3 = i): the UBSan trap side (mac + i wraps) is not taken. *)
Lemma rm_mac_ovf : forall E (mac i : Z), ew E 12 = Z_to_bv 64 mac -> 0 <= mac -> mac + 6 <= 2 ^ 47 -> 0 <= i < 6 ->
branch_taken BC_LTU (sv_denot E (SAlu ALU_XOR (SOff 12 0) (SLit (-1)))) (sv_denot E (SLit i)) = false.
Proof.
intros E mac i H Hm Hm6 Hi. rewrite branch_ltu_U, (U_not E 12 mac H) by lia. rewrite (U_lit E i) by lia.
apply Z.ltb_ge. lia.
Qed.
(* The model: the 6 MAC bytes. *)
Lemma rm_nth_firstn : forall (A : Type) (l : list A) n j d, (j < n)%nat -> nth j (firstn n l) d = nth j l d.
Proof.
intros A l. induction l as [|x l IH]; intros n j d Hj.
- destruct n; [lia|]. reflexivity.
- destruct n; [lia|]. cbn [firstn]. destruct j; [reflexivity|]. cbn [nth]. apply IH. lia.
Qed.
Lemma rm_out_ne0 : forall full pl i, (full =? 0) = false -> 0 <= i < 6 ->
bv_unsigned (nth (Z.to_nat i) (tbread_mac_out full pl) (Z_to_bv 8 0)) = rmb pl (Z.to_nat i).
Proof.
intros full pl i Hf Hi. unfold tbread_mac_out. rewrite Hf. rewrite rm_nth_firstn by lia. unfold rmb.
destruct (Nat.lt_ge_cases (Z.to_nat i) (length pl)) as [Hl|Hl].
- rewrite app_nth1 by exact Hl. reflexivity.
- rewrite app_nth2 by exact Hl. rewrite nth_repeat. rewrite (nth_overflow pl) by exact Hl. reflexivity.
Qed.
Lemma rm_out_eq0 : forall full pl i, (full =? 0) = true -> 0 <= i < 5 ->
bv_unsigned (nth (Z.to_nat i) (tbread_mac_out full pl) (Z_to_bv 8 0)) =
bv_unsigned (nth (Z.to_nat i) tbread_mac_base (Z_to_bv 8 0)).
Proof.
intros full pl i Hf Hi. unfold tbread_mac_out. rewrite Hf. rewrite app_nth1; [reflexivity|].
unfold tbread_mac_base. cbn [length map]. lia.
Qed.
Lemma rm_out_eq0_5 : forall full pl, (full =? 0) = true ->
bv_unsigned (nth (Z.to_nat 5) (tbread_mac_out full pl) (Z_to_bv 8 0)) = rmb pl 0.
Proof. intros full pl Hf. unfold tbread_mac_out. rewrite Hf. unfold rmb. destruct pl; reflexivity. Qed.
(* A byte and a word of a region's chunk. *)
Lemma rm_byte_at : forall (W : world SEGS) mem E (n : nat) b lo hi wlo whi cs a j e v,
region_ok SEGS E (mrestrict (w_H W) mem) (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = b ->
In (YP09.mkChunk j (CVal 1 e)) cs -> b + j = a -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 256 ->
aview SEGS (w_H W) mem a = Some v.
Proof.
intros W mem E n b lo hi wlo whi cs a j e v HR Hn Hc Ha He Hv. subst a.
apply aview_of_val_mem1; [|exact Hv].
change 1%nat with (N.to_nat 1). eapply field_of_region; [exact HR | exact Hn | exact Hc | exact He | cbn; lia | cbn; lia].
Qed.
Lemma rm_val8_at : forall m E (n : nat) b lo hi wlo whi cs a j e v,
region_ok SEGS E m (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = b ->
In (YP09.mkChunk j (CVal 8 e)) cs -> b + j = a -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
val_mem SEGS m a 8 v.
Proof.
intros m E n b lo hi wlo whi cs a j e v HR Hn Hc Ha He Hv. subst a.
change 8%nat with (N.to_nat 8). eapply field_of_region; [exact HR | exact Hn | exact Hc | exact He | cbn; lia | cbn; lia].
Qed.
(* Shadow facts survive a change that keeps the shadow band. *)
Lemma rm_ra_kept : forall (rd rd' : Z -> option Z) a n,
(forall s, SHADOW_OFF <= s < SHADOW_OFF + 2 ^ 44 -> rd' s = rd s) -> 0 <= a -> a + n <= 2 ^ 47 ->
range_addressable rd SHADOW_OFF a n -> range_addressable rd' SHADOW_OFF a n.
Proof.
intros rd rd' a n HK Ha Han HR x Hx. destruct (HR x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
rewrite HK; [exact Hs|]. unfold shadow_of_addr.
assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). assert (0 <= x / 8) by (apply Z.div_pos; lia). lia.
Qed.
Lemma rm_hull_kept : forall (rd rd' : Z -> option Z) a n,
(forall s, SHADOW_OFF <= s < SHADOW_OFF + 2 ^ 44 -> rd' s = rd s) -> 0 <= a -> a + n <= 2 ^ 46 -> 0 < n ->
shadow_hull_vis rd a n -> shadow_hull_vis rd' a n.
Proof.
intros rd rd' a n HK Ha Han Hn HV s Hs. rewrite HK; [exact (HV s Hs)|]. unfold shadow_addr, SHADOW_OFF in *.
pose proof (Z.div_pos a 8 ltac:(lia) ltac:(lia)).
pose proof (Z.div_lt_upper_bound (a + n - 1) 8 (2 ^ 43) ltac:(lia) ltac:(lia)).
pose proof (Z.mul_div_le (2147450880 + a / 8) 8 ltac:(lia)).
pose proof (Z.mul_div_le (2147450880 + (a + n - 1) / 8) 8 ltac:(lia)).
pose proof (Z_div_mod_eq_full (2147450880 + a / 8) 8). pose proof (Z.mod_pos_bound (2147450880 + a / 8) 8 ltac:(lia)).
lia.
Qed.
Lemma rm_shok_kept : forall E E' (m m' : word -> option byte) SH,
(forall n, (n < 512)%nat -> ew E' n = ew E n) ->
(forall s, SHADOW_OFF <= s < SHADOW_OFF + 2 ^ 44 -> rd_of SEGS m' s = rd_of SEGS m s) ->
U E RMx = SHADOW_OFF ->
Forall (fun e => 0 <= U E (SOff (she_m e) 0) + she_lo e /\ U E (SOff (she_m e) 0) + she_hi e <= 2 ^ 47 /\
(she_m e < 512)%nat) SH ->
sh_ok SEGS RMx SH E m -> sh_ok SEGS RMx SH E' m'.
Proof.
intros E E' m m' SH Hag Hk HB HF HS. unfold sh_ok in *.
assert (UB' : U E' RMx = U E RMx) by (unfold RMx; rewrite !U_SOff, (Hag 32%nat) by lia; reflexivity).
revert HF. induction HS as [|e l He Hl IH]; intros HF; [constructor|].
apply Forall_cons_iff in HF as ((Hlo & Hhi & Hm) & HF').
constructor; [|exact (IH HF')].
assert (UM : U E' (SOff (she_m e) 0) = U E (SOff (she_m e) 0)) by (rewrite !U_SOff, (Hag (she_m e)) by exact Hm; reflexivity).
destruct He as [Hra Hap]. split.
- rewrite UB', UM, HB. rewrite HB in Hra. intros x Hx. destruct (Hra x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
rewrite Hk; [exact Hs|]. unfold shadow_of_addr.
assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). assert (0 <= x / 8) by (apply Z.div_pos; lia). lia.
- unfold app_apart in *. rewrite UB', UM. exact Hap.
Qed.
(* The bytes a run may write: its own frame, the cursor and the MAC (rm_zs); after the memcpy, MAC byte 5 only
   (rm_zs5). *)
Definition rm_zs (sp c mac x : Z) : Prop := (sp - 32 <= x < sp) \/ (c <= x < c + 16) \/ (mac <= x < mac + 6).
Definition rm_zs5 (sp c mac x : Z) : Prop := (sp - 32 <= x < sp) \/ (c <= x < c + 16) \/ (mac + 5 <= x < mac + 6).
(* The index of the region at atom n. *)
Fixpoint rm_idx (n : nat) (l : smem) (i : nat) : nat :=
match l with
| [] => i
| r :: l' => match YP09.r_base r with
| Some m => if Nat.eqb m n then i else rm_idx n l' (S i)
| None => rm_idx n l' (S i) end
end.
(* A run's windows lie in rm_zs / rm_zs5. *)
Local Ltac rm_win :=
let bb := fresh "bb" in let wlo := fresh "wlo" in let whi := fresh "whi" in let aa := fresh "aa" in
let Hwin := fresh "Hwin" in let Hr := fresh "Hr" in
intros bb wlo whi aa Hwin Hr; vm_compute in Hwin;
repeat (destruct Hwin as [Hwin | Hwin];
[ injection Hwin as <- <- <-; cbn [base_val] in Hr; cbn [ew ewset Nat.eqb] in Hr; rewrite ?ew_ewset_other in Hr by lia;
repeat match goal with H : bv_unsigned (ew ?E ?n) = _ |- _ =>
lazymatch type of Hr with context [bv_unsigned (ew E n)] => rewrite H in Hr end end;
unfold rm_zs, rm_zs5; lia |]);
destruct Hwin.
(* What the runs kept, back to the memory the first of them started from. *)
Local Ltac rm_chain Zs a Ha Hz :=
repeat match goal with
| Hf : frame_of ?Ew ?rsw (mrestrict ?Hq ?mA) (mrestrict ?Hq ?mB) |- aview _ ?Hq ?mB a = _ =>
rewrite (kept_of_frame (segs := SEGS) Ew rsw Hq mA mB Zs Hf ltac:(rm_win) a Ha Hz); clear Hf
end; reflexivity.
Local Ltac rm_pchain a Hp :=
repeat match goal with
| Hg : mem_grows (mrestrict ?Hq ?mA) (mrestrict ?Hq ?mB) |- apresent ?Hq ?mB a => apply (apresent_grows Hq mA mB a Hg); clear Hg
| P0 : forall x, apresent ?Hq ?mA x -> apresent ?Hq ?mB x |- apresent ?Hq ?mB a => apply P0; clear P0
end; exact Hp.
(* A MAC byte's value: an input byte atom, or 0 once the input is used up. *)
Local Ltac rm_den_byte :=
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia;
first [ lazymatch goal with H : ew ?E ?n = _ |- ew ?E ?n = _ => exact H end
| f_equal; unfold rmb; rewrite nth_overflow by lia; reflexivity ].
(* A cursor word's value. *)
Local Ltac rm_full_rw := lazymatch goal with H : (_ =? 0) = _ |- _ => rewrite H end.
Local Ltac rm_den8 :=
cbn [sv_denot]; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia;
repeat match goal with H : ew ?E ?n = Z_to_bv 64 _ |- context [ew ?E ?n] => rewrite H end;
rewrite ?unsigned_lit_small by lia; f_equal; unfold tbread_mac_used; rm_full_rw; lia.
Local Ltac rm_cur8 HRc cv a j :=
eapply (rm_val8_at _ _ 10%nat cv _ _ _ _ _ a j _ _ HRc);
[ cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia;
lazymatch goal with H : bv_unsigned (ew ?E 10) = _ |- bv_unsigned (ew ?E 10) = _ => exact H end
| repeat (first [left; reflexivity | right])
| lia
| rm_den8
| unfold tbread_mac_used; rm_full_rw; lia ].
Theorem pb_bread_mac : tbread_mac_spec.
Proof.
unfold tbread_mac_spec.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc kk regs c full mac p bi Li pl
HJ Hra Hra4 Hgp Htp Hal16 Hwlo Hwhi H10 H11 H12 Hfull Hc8 Hspc Hcp Hcn HRAc HWc Hp64 Hblk HPL HFO HWm _ _ HBV HBRA HBHV.
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
remember (Nat.min (length pl) 6) as k eqn:Hkd.
assert (Hk6 : (k <= 6)%nat) by lia.
destruct (rm_entry STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc kk regs c mac p bi Li pl k
HJ Hal16 Hwlo Hwhi H10 H12 Hc8 Hspc Hcp Hcn HRAc HWc Hp64 Hblk HPL HFO HWm Hk6 Hkd) as [HS SHOK].
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _ & _).
pose proof Hstk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : READ_MAC_STKB = 4128) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
pose proof (rm_c16 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc kk regs c HJ Hwlo Hspc HWc) as Hc16.
pose proof HFO as ((cid & pos & Hfin & Hcid & Hfal & Hflo & Hfhi) & Hm8 & HRAm).
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hfin) as (Hf4096 & Hfceil & Hfapp).
pose proof (frm_off_imgP B lyc Sc W memc mdc cid pos HAR Hfin) as Hfimg.
assert (Hmband : mac + 6 <= SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= mac)
by (revert Hfapp Hflo Hfhi; unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg; clear; intros; lia).
pose proof (pa_obj_img 6 ltac:(lia)) as HxR.
pose proof (rm_n47 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc kk p bi Li pl HJ Hblk ltac:(lia)) as Hn47.
destruct (rm_ew regs p (Z.of_nat (length pl)) pl) as (E32 & E33 & E34 & EB).
remember (ERM regs p (Z.of_nat (length pl)) pl) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold ERM; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (rm_extra p (Z.of_nat (length pl)) pl)) n)
by (intros n Hn; subst E; unfold ERM; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (RUs : bv_unsigned (ew E 2) = spZ regs)
by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 c) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 full) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 mac) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (RUc : bv_unsigned (ew E 10) = c) by (rewrite E10; apply unsigned_lit_small; lia).
assert (RUm : bv_unsigned (ew E 12) = mac) by (rewrite E12; apply unsigned_lit_small; lia).
assert (RUp : bv_unsigned (ew E 33) = p) by (rewrite E33; apply unsigned_lit_small; lia).
assert (HAE : env_agree 32 (Ereg regs (rm_extra p (Z.of_nat (length pl)) pl)) E)
by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
pose proof (EB 0%nat ltac:(lia)) as E35. pose proof (EB 1%nat ltac:(lia)) as E36. pose proof (EB 2%nat ltac:(lia)) as E37.
pose proof (EB 3%nat ltac:(lia)) as E38. pose proof (EB 4%nat ltac:(lia)) as E39. pose proof (EB 5%nat ltac:(lia)) as E40.
cbn [Nat.add] in E35, E36, E37, E38, E39, E40.
clear HE EL EB.
unfold cfg_at. change (w64 AB_read_macP) with (Z_to_bv 64 AB_read_macP).
(* One walk for each k = min n 6. *)
destruct k as [|[|[|[|[|[|[|k]]]]]]]; [ idtac .. | exfalso; lia ].
all: try (destruct (rm_blk STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc kk p bi Li pl HJ Hblk ltac:(lia))
as (Hin & Hp4096 & Hb1 & Hb2 & Hbceil & Hbia);
pose proof (sep_block_frame SEGS B LAWS lyc Sc W memc mdc bi Li cid pos HAR Hin Hfin) as Hbf;
unfold zdisjoint in Hbf; cbn [fst snd] in Hbf).
all:
(* 0x81640: the branch on full; HFULL records which side the walk is on. *)
let rm_full := idtac;
lazymatch goal with Hc : branch_taken BC_EQ (sv_denot ?Ez (SOff 11 0)) (sv_denot _ (SLit 0)) = ?b |- _ =>
pose proof (rm_full_br Ez full b ltac:(cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact E11) Hfull Hc) as HFULL;
clear Hc end in
(* 0x816c8: the UBSan trap side of mac + i is refuted. *)
let rm_trap i := exfalso;
lazymatch goal with Hc : branch_taken BC_LTU (sv_denot ?Ez (SAlu ALU_XOR (SOff 12 0) (SLit (-1)))) (sv_denot _ (SLit i)) = true |- _ =>
rewrite (rm_mac_ovf Ez mac i ltac:(cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact E12)
ltac:(lia) ltac:(lia) ltac:(lia)) in Hc; discriminate Hc end in
(* 0x81720: __asan_memcpy (mac, read_mac.base, 5) on the full = 0 side, and the state after it. *)
let rm_call := idtac;
lazymatch goal with HSc : st_ok _ ?Ec _ (restrict _ ?msT) |- _ =>
assert (KPT : forall a, 0 <= a < 2 ^ 64 -> ~ rm_zs (spZ regs) c mac a ->
aview SEGS (w_H W) (ms_mem msT) a = aview SEGS (w_H W) memc a)
by (let a := fresh "a" in let Ha := fresh "Ha" in let Hz := fresh "Hz" in intros a Ha Hz;
rm_chain (rm_zs (spZ regs) c mac) a Ha Hz);
assert (PPT : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem msT) a)
by (let a := fresh "a" in let Hp := fresh "Hp" in intros a Hp; rm_pchain a Hp);
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
assert (BANDT : forall s, SHADOW_OFF <= s < SHADOW_OFF + 2 ^ 44 ->
aview SEGS (w_H W) (ms_mem msT) s = aview SEGS (w_H W) memc s)
by (let s := fresh "s" in let Hs := fresh "Hs" in intros s Hs; unfold SHADOW_OFF in *; apply KPT; [lia | unfold rm_zs; lia]);
pmkst HSc;
prreg HSc (10%bv : bv 5) Ra0; prreg HSc (11%bv : bv 5) Ra1; prreg HSc (12%bv : bv 5) Ra2; prreg HSc (1%bv : bv 5) Rra;
prreg HSc (2%bv : bv 5) Rsp; prreg HSc (3%bv : bv 5) Rgp; prreg HSc (4%bv : bv 5) Rtp;
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
assert (Qsp : spZ rg = spZ regs + -32) by (unfold spZ at 1; rewrite Rsp, RUs, unsigned_lit_small by lia; reflexivity);
eapply SRr_bind;
[ eapply (aj_intrin_at SEGS B LAWS Hsegs OCpy (SIGMA BB___asan_memcpy) AMEMCPY W rg mm
STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ kk mac (VAL (A_OBJ 6)) 5 (spZ regs + -32 - sp0) _ HJ);
[ rewrite Ra0, E12; reflexivity
| rewrite Ra1; exact (img_env_atomP E (A_OBJ 6) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))
| rewrite Ra2; reflexivity
| lia | lia | lia
| rewrite Qsp; lia
| replace (spZ regs + -32 - sp0) with (spZ regs + (-2 - sp0 / 16) * 16) by (pose proof (Z.div_mod sp0 16 ltac:(lia)); lia);
rewrite Z_mod_plus_full; exact Hal16
| lia
| rewrite Hes; lia
| rewrite Rgp, E3; exact Hgp
| rewrite Rtp, E4; exact Htp
| exact Rra
| apply ret_ok_codeptr_v; [lia | reflexivity]
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; split; [exact (proj1 (HWm a ltac:(lia))) | rewrite Hes; lia]
| apply (amem_range_sub_app _ _ mac 5 Hfapp Hfceil); lia
| apply (rm_ra_kept (aview SEGS (w_H W) memc)); [exact BANDT | lia | lia | apply (range_addressable_sub _ _ mac 6 mac 5 HRAm); lia]
| intros _; eapply (shadow_hull_vis_of_frame SEGS B LAWS _ _ _ _ _ cid pos _ _ (proj1 HJ) Hfin); lia
| cbv iota; split; [lia|]; split; [lia|]; split;
[ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; split;
[ rewrite (KPT a ltac:(lia) ltac:(unfold rm_zs; lia));
replace a with (VAL (A_OBJ 6) + (a - VAL (A_OBJ 6))) by lia; rewrite (HBV (a - VAL (A_OBJ 6))) by lia; discriminate
| rewrite Qsp, Hes; lia ]
| split; [lia|]; split; [unfold amem_range, kLowMemEnd; left; lia|]; split;
[ apply (rm_ra_kept (aview SEGS (w_H W) memc)); [exact BANDT | lia | lia | exact HBRA]
| intros _; apply (rm_hull_kept (aview SEGS (w_H W) memc)); [exact BANDT | lia | lia | lia | exact HBHV] ] ] ]
| ];
cbv beta; intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha0 & Heff & Hfr & Hpres2);
cbv iota in Heff;
(* what the call and the walk before it kept *)
assert (KP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 4128 <= a < spZ regs) -> ~ (c <= a < c + 16 \/ mac <= a < mac + 6) ->
aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memc a)
by (let a := fresh "a" in let Ha := fresh "Ha" in let Hw := fresh "Hw" in let He := fresh "He" in
intros a Ha Hw He; rewrite (Hfr a Ha) by (rewrite ?Hes; lia); apply KPT; [exact Ha | unfold rm_zs; lia]);
assert (PP1 : forall a, apresent (w_H W) memc a -> apresent (w_H W) mem2 a)
by (let a := fresh "a" in let Hp := fresh "Hp" in intros a Hp; apply Hpres2; apply PPT; exact Hp);
(* the shadow entries after the call *)
lazymatch type of SHOK with sh_ok _ _ ?SHk ?Ec' ?mT =>
assert (SHOK2 : sh_ok SEGS RMx SHk (havoc Ec' 512 (map (getr regs2) CLOB)) (mrestrict (w_H W) mem2))
by (apply (rm_shok_kept Ec' _ mT);
[ let n := fresh "n" in let Hn := fresh "Hn" in intros n Hn; apply YN3v.ew_havoc_old; exact Hn
| let s := fresh "s" in let Hs := fresh "Hs" in intros s Hs; rewrite <- !(aview_rd_of SEGS);
unfold SHADOW_OFF in *; apply Hfr; [lia | lia | rewrite Hes; lia]
| unfold RMx; rewrite (U_atom Ec' 32 RM_SB ltac:(cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact E32)
ltac:(unfold RM_SB; lia)); reflexivity
| unfold rm_SH; cbn [app Nat.eqb]; repeat apply Forall_cons; try apply Forall_nil; cbn [she_m she_lo she_hi];
rewrite ?(U_atom Ec' 10 c ltac:(cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact E10) ltac:(lia)),
?(U_atom Ec' 12 mac ltac:(cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact E12) ltac:(lia)),
?(U_atom Ec' 33 p ltac:(cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact E33) ltac:(lia)); lia
| exact SHOK ])
end;
(* the symbolic state after the call: the frame, the cursor and the input bytes are kept *)
jafter_call_keep_hi HSc 512%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 3; 5]%nat HS2;
match type of HS2 with ?tq -> _ =>
assert (HRK : tq);
[ cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil;
(eapply region_kept_aview;
[ cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; first [exact RUs | exact RUc | exact RUp]
| let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply Hfr; [lia | lia | rewrite Hes; lia]
| exact Hpres2 ])
| specialize (HS2 HRK); clear HRK ] end;
clear HSc; rewrite <- restrict_mkst_fx in HS2;
lazymatch type of HS2 with st_ok_pi _ _ ?Eh _ _ =>
let Eb := fresh "Eb" in
remember Eh as Eb eqn:HEb;
assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc_hi; [eassumption | unfold A_LIM; lia]);
assert (OLD : forall n, (n < 512)%nat -> ew Eb n = ew E n)
by (let n := fresh "n" in let Hn := fresh "Hn" in intros n Hn; rewrite HEb, YN3v.ew_havoc_old by exact Hn;
rewrite ?ew_ewset_other by lia; reflexivity);
assert (F1 : ew Eb 1 = getr regs 1) by (rewrite OLD by lia; exact E1);
assert (F3 : ew Eb 3 = getr regs 3) by (rewrite OLD by lia; exact E3);
assert (F4 : ew Eb 4 = getr regs 4) by (rewrite OLD by lia; exact E4);
assert (F10 : ew Eb 10 = Z_to_bv 64 c) by (rewrite OLD by lia; exact E10);
assert (F11 : ew Eb 11 = Z_to_bv 64 full) by (rewrite OLD by lia; exact E11);
assert (F12 : ew Eb 12 = Z_to_bv 64 mac) by (rewrite OLD by lia; exact E12);
assert (F32 : ew Eb 32 = Z_to_bv 64 RM_SB) by (rewrite OLD by lia; exact E32);
assert (F33 : ew Eb 33 = Z_to_bv 64 p) by (rewrite OLD by lia; exact E33);
assert (F34 : ew Eb 34 = Z_to_bv 64 (Z.of_nat (length pl))) by (rewrite OLD by lia; exact E34);
assert (F35 : ew Eb 35 = Z_to_bv 64 (rmb pl 0)) by (rewrite OLD by lia; exact E35);
assert (F36 : ew Eb 36 = Z_to_bv 64 (rmb pl 1)) by (rewrite OLD by lia; exact E36);
assert (F37 : ew Eb 37 = Z_to_bv 64 (rmb pl 2)) by (rewrite OLD by lia; exact E37);
assert (F38 : ew Eb 38 = Z_to_bv 64 (rmb pl 3)) by (rewrite OLD by lia; exact E38);
assert (F39 : ew Eb 39 = Z_to_bv 64 (rmb pl 4)) by (rewrite OLD by lia; exact E39);
assert (F40 : ew Eb 40 = Z_to_bv 64 (rmb pl 5)) by (rewrite OLD by lia; exact E40);
assert (FRUs : bv_unsigned (ew Eb 2) = spZ regs) by (rewrite OLD by lia; exact RUs);
assert (FRUc : bv_unsigned (ew Eb 10) = c) by (rewrite OLD by lia; exact RUc);
assert (FRUm : bv_unsigned (ew Eb 12) = mac) by (rewrite OLD by lia; exact RUm);
assert (FRUp : bv_unsigned (ew Eb 33) = p) by (rewrite OLD by lia; exact RUp);
assert (FAE : env_agree 32 (Ereg regs (rm_extra p (Z.of_nat (length pl)) pl)) Eb)
by (rewrite HEb; apply env_agree_havoc_ge; [lia | split;
[ let n := fresh "n" in let Hn := fresh "Hn" in intros n Hn; rewrite ?ew_ewset_other by lia; apply (proj1 HAE); lia
| cbn [ed ewset]; apply (proj2 HAE) ] ]);
clear HEb OLD;
clear E1 E3 E4 E10 E11 E12 E32 E33 E34 E35 E36 E37 E38 E39 E40 RUs RUc RUm RUp HAE HEI;
rename F1 into E1; rename F3 into E3; rename F4 into E4; rename F10 into E10; rename F11 into E11; rename F12 into E12;
rename F32 into E32; rename F33 into E33; rename F34 into E34; rename F35 into E35; rename F36 into E36;
rename F37 into E37; rename F38 into E38; rename F39 into E39; rename F40 into E40;
rename FRUs into RUs; rename FRUc into RUc; rename FRUm into RUm; rename FRUp into RUp; rename FAE into HAE; rename HEIb into HEI;
(* MAC byte 5 as a writable window again; the rest of the MAC is the memcpy's *)
lazymatch type of HS2 with st_ok_pi _ _ _ ?ssx (restrict ?Hh ?msx) =>
assert (HR5 : region_ok SEGS Eb (ms_mem (restrict Hh msx)) (YP09.mkRegion (Some 12%nat) 5 6 5 6 []));
[ cbn [restrict ms_mem mkst]; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
rewrite RUm; split; [lia|]; split; [lia|]; split; [|constructor];
let o := fresh "o" in let Ho := fresh "Ho" in intros o Ho; apply (apresent_writable SEGS); apply PP1;
exact (proj1 (proj2 (HWm (mac + o) ltac:(lia))))
| pose proof (st_ok_pi_add_region Eb ssx (restrict Hh msx) (YP09.mkRegion (Some 12%nat) 5 6 5 6 []) HS2 ltac:(vm_compute; reflexivity) HR5
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite ?RUs, ?RUc, ?RUm, ?RUp; repeat match goal with |- _ /\ _ => split end; first [exact I | lia])) as HS3;
clear HS2 HR5; rename HS3 into HS ]
end end;
clear SHOK; rename SHOK2 into SHOK; clear HJ; rename HJ2 into HJ
end end in
(* The return at 0x817d4. *)
let rm_cj := idtac;
unfold tbcj_kept; rewrite WS; cbv beta; 
split; [let a := fresh "a" in let Ha := fresh "Ha" in let Hw := fresh "Hw" in let He := fresh "He" in
intros a Ha Hw He; apply KEEP; [lia | exact Hw | exact He]|];
split; [let b := fresh "b" in let m := fresh "m" in let i := fresh "i" in let Hin' := fresh "Hin" in
let Hi := fresh "Hi" in let He := fresh "He" in
intros b m i Hin' Hi He; destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hin') as (_ & ? & ? & _);
apply KEEP; [lia | lia | exact He]|];
split; [let a := fresh "a" in let Hin' := fresh "Hin" in intros a Hin' _ _; pose proof (pa_img_range a Hin'); apply KEEP; lia|];
split; [let cid' := fresh "cid" in let pos' := fresh "pos" in let a := fresh "a" in let Hin' := fresh "Hin" in
let Hrr := fresh "Hrr" in let He := fresh "He" in
intros cid' pos' a Hin' Hrr He;
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid' pos' HAR Hin') as (? & ? & _);
pose proof (fs_frame_bytes_nonneg cid');
pose proof (YCbq.shadow_addr_bounds (frame_addr lyc cid' pos') ltac:(lia));
pose proof (YCbq.shadow_addr_bounds (frame_addr lyc cid' pos' + fs_frame_bytes cid') ltac:(lia));
pose proof (shadow_range_end (frame_addr lyc cid' pos') (fs_frame_bytes cid') ltac:(lia));
unfold in_zr, frame_rng in Hrr; cbn [fst snd] in Hrr;
apply KEEP; [destruct Hrr; lia | destruct Hrr; lia | exact He]|];
split; [let a := fresh "a" in let Hp := fresh "Hp" in intros a _ _ Hp; apply PRES; exact Hp|];
let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
lazymatch goal with HJz : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
let HJp := fresh "HJp" in pose proof HJz as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJp & _); apply HJp; lia end in
let rm_macbytes HRm := idtac;
lazymatch goal with
| HF1 : (_ =? 0) = false |- _ =>
let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi;
rewrite (rm_out_ne0 full pl i HF1 Hi);
assert (Hi' : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5) by lia;
destruct Hi' as [-> | [-> | [-> | [-> | [-> | ->]]]]];
lazymatch goal with |- aview _ _ _ (_ + ?j) = _ =>
eapply (rm_byte_at W _ _ 12%nat mac _ _ _ _ _ (mac + j) j _ _ HRm);
[ cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact RUm
| repeat (first [left; reflexivity | right])
| lia
| rm_den_byte
| apply rmb_range ] end
| HF0 : (_ =? 0) = true |- _ =>
let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi;
destruct (Z.lt_ge_cases i 5) as [Hi5 | Hi5];
[ rewrite (rm_out_eq0 full pl i HF0 ltac:(lia));
rewrite (KPm (mac + i) ltac:(lia) ltac:(unfold rm_zs5; lia)), (Heff i ltac:(lia)),
(KPT (VAL (A_OBJ 6) + i) ltac:(lia) ltac:(unfold rm_zs; lia));
exact (HBV i ltac:(lia))
| assert (i = 5) as -> by lia; rewrite (rm_out_eq0_5 full pl HF0);
eapply (rm_byte_at W _ _ 12%nat mac _ _ _ _ _ (mac + 5) 5 _ _ HRm);
[ cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact RUm
| repeat (first [left; reflexivity | right])
| lia
| rm_den_byte
| apply rmb_range ] ]
end in
let rm_post msc := idtac;
lazymatch goal with HSz : st_ok_pi _ _ ?Ez ?ssx (restrict ?Hh msc), HJz : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
assert (PRES : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem msc) a)
by (let a := fresh "a" in let Hp := fresh "Hp" in intros a Hp; rm_pchain a Hp);
prreg HSz (1%bv : bv 5) R1;
eapply (RET W _ _ _ _ _ HSz eq_refl ltac:(vm_compute; reflexivity));
let mq := fresh "mat" in intros mq;
unfold tbread_mac_post;
split; [reflexivity|];
exists (ms_regs msc), (ms_mem msc); eexists;
split; [cbn [ms_regs]; rewrite R1; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; rewrite E1, Hra; reflexivity|];
split; [cbn [ms_mem]; apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJz|];
split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs (rm_extra p (Z.of_nat (length pl)) pl) HSz);
[ split; [let nn := fresh "nn" in let Hnn := fresh "Hnn" in intros nn Hnn; rewrite ?ew_ewset_other by lia;
apply (proj1 HAE); lia | cbn [ed ewset]; apply (proj2 HAE)]
| vm_compute; reflexivity ]|];
let i10 := eval vm_compute in (rm_idx 10 (ss_mem ssx) 0) in
let i12 := eval vm_compute in (rm_idx 12 (ss_mem ssx) 0) in
pose proof (st_ok_pi_region_nth _ _ _ i10 _ HSz eq_refl) as HRc; cbn [restrict ms_mem] in HRc;
pose proof (st_ok_pi_region_nth _ _ _ i12 _ HSz eq_refl) as HRm; cbn [restrict ms_mem] in HRm;
split; [rm_macbytes HRm|]; 
split; [rm_cur8 HRc c c 0|];
split; [rm_cur8 HRc c (c + 8) 8|];
rm_cj
end in
let rm_ret := idtac;
lazymatch goal with HSz : st_ok_pi _ _ _ _ (restrict _ ?msc) |- _ =>
lazymatch goal with
| HF0 : (_ =? 0) = true |- _ =>
assert (KPm : forall a, 0 <= a < 2 ^ 64 -> ~ rm_zs5 (spZ regs) c mac a ->
aview SEGS (w_H W) (ms_mem msc) a = aview SEGS (w_H W) mem2 a)
by (let a := fresh "a" in let Ha := fresh "Ha" in let Hz := fresh "Hz" in intros a Ha Hz;
rm_chain (rm_zs5 (spZ regs) c mac) a Ha Hz);
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 4128 <= a < spZ regs) -> ~ (c <= a < c + 16 \/ mac <= a < mac + 6) ->
aview SEGS (w_H W) (ms_mem msc) a = aview SEGS (w_H W) memc a)
by (let a := fresh "a" in let Ha := fresh "Ha" in let Hw := fresh "Hw" in let He := fresh "He" in
intros a Ha Hw He; rewrite (KPm a Ha ltac:(unfold rm_zs5; lia)); exact (KP1 a Ha Hw He));
rm_post msc
| HF1 : (_ =? 0) = false |- _ =>
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 4128 <= a < spZ regs) -> ~ (c <= a < c + 16 \/ mac <= a < mac + 6) ->
aview SEGS (w_H W) (ms_mem msc) a = aview SEGS (w_H W) memc a)
by (let a := fresh "a" in let Ha := fresh "Ha" in let Hw := fresh "Hw" in let He := fresh "He" in intros a Ha Hw He;
let Hz := fresh "Hz" in assert (Hz : ~ rm_zs (spZ regs) c mac a) by (unfold rm_zs; lia);
rm_chain (rm_zs (spZ regs) c mac) a Ha Hz);
rm_post msc
end end in
(* The runs: the engine decides the ASan checks (the shadow entries of the cursor, the MAC and the input bytes), the
   alignment and NULL / p + 1 UBSan checks; it stops at the branch on full, at the mac + i UBSan check, at the memcpy
   and at the return. *)
let rec go := idtac;
lazymatch goal with HSx : st_ok_pi _ _ _ _ _, HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOKx : sh_ok _ _ _ _ _ |- _ =>
paj_run_tok RUN HSx HJx SHOKx RMspan; [rm_awr sp0 (spZ regs) c mac RUs E10 E12 HWc HWm |];
lazymatch goal with
| HS' : st_ok_pi _ _ _ ?ss _, SHOK' : sh_ok _ _ ?SHx _ _ |- _ =>
let K := eval vm_compute in (run_K A_LIM RMx SHx ss) in
let why := lazymatch paj_tables RUN with (?tpi, ?tw) =>
psym_why_tok tpi tw K RMx RMspan SHx (start K RMx RMspan SHx ss) end in
lazymatch why with
| SR_jalr _ => rm_ret
| SR_branch BC_EQ (SOff 11 0) (SLit 0) => psrr_branch_tok RUN BR HS' SHOK' RMspan; rm_full; go
| SR_branch BC_LTU (SAlu ALU_XOR (SOff 12 0) (SLit (-1))) (SLit ?i) =>
psrr_branch_tok RUN BR HS' SHOK' RMspan; [rm_trap i | go]
| _ => let pc := eval vm_compute in (ss_pc ss) in idtac "STUCK" pc why; fail
end
| HS' : st_ok _ _ _ _ |- _ => rm_call; go
end end in go.
Qed.
End h.
End f.
End d.
