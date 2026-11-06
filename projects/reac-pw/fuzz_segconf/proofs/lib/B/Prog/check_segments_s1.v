(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of rec_calls_equal on the ASan build of plugin-hostd/fuzz_command
   (0x89968, 135 instructions), in the shape of cgif_file_fuzzer's walks (lib/A/AChc.v, ACh1.v..ACh8.v): the
   symbolic executor over the position-abstract listing (CmdPaLib.v), the inline checks removed by the shadow tokens
   (PaShadow.v), and the strcmp wrapper's call stepped through by its contract (PaArt.v aj_art_at). The two loops
   are cut at their heads (0x899dc, 0x89a6c) and at the outer latch (0x89ab0); each piece is re-seeded from the
   concrete state there and the loops are proved by induction. Every call is strcmp, which writes only its stack
   window, so the memory below the frame stays the entry's (kept_out) and the read-only bytes strcmp reads
   (rt_rom_view) follow from the statement's arodata_okP. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/rec_calls_equal.v, with its module paths, module names and numbers changed; 575 of its 722 lines of code are new or changed and 1344 lines of the source are left out. *)
(* The image-B port of lib/A/Prog/check_segments_s1.v (commit 4173a03b8db0).
   The walk of check_segments on fuzz_segconf.asan-ubsan (image B, 0x86f58 = BASE + AF_check_segments, 104
   instructions, frame 80), part 1: the cut points, the entry stretch 0x86f58 .. 0x8703c and the exit
   0x8706c .. 0x8709c. Part 2 (check_segments.v) walks the loop 0x87040 .. 0x87068 through the strcmp wrapper and
   states the theorem. The form is image A's: the symbolic executor over the position-abstract listing, the four
   inline checks removed by the shadow entries of the two structs, one struct region at a time (swapped between
   the loads of c and of m), the loop cut at its head and re-seeded from the concrete state there.
   Image B's code is image A's plus UBSan's tests, a frame of 80 bytes (ra, s0 .. s8) and a loop that counts by
   offsets (s3 = 356 i, s4 = 256 i, s5 = ~c, s6 = ~m, s7 = n << 8, s8 = 32 - i, the bound of seg[32]).
   The UBSan traps (the `unimp` at 0x870a0) of the entry, each refuted at its branch:
     0x86f8c `bnez a0`, a0 = c & 7: the executor folds `andi a0,a0,7` to 0 from c's seed fact (cs_PF, alignment
                     2^4), which cs_entry_seed proves from the contract's c mod 16 = 0; the branch falls through
     0x86fc4 `bnez a0`, a0 = m & 3: the same from m's seed fact and m mod 16 = 0
   The loop's traps (0x87040 beqz s8, 0x87044 bltu s5,s3, 0x87048 bltu s6,s4) are refuted in part 2.
   Plan: the unit record's Bwalks-G45-plans/plan-check_segments.md. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaDenot PaSB PaLibG PaLibH PaLibF PaCallRun PaCall.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaArt.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Mem ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require check_segments.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase SegGlob check_segments_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the plain walk of the same function: its image-free lemmas (strcmp's zero on NUL-free strings, the
   premise check_segments unfolded) *)
Module PCS := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.check_segments.CsPure.
Module PMem := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Mem.
(* the image-free bit lemma of `not` (lib/Lib/ZBridge.v) of the plain proofs *)
Module PZB := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.ZBridge.

(* ---------- bytes of the two structs through a reader ---------- *)
Lemma cs_bytes_app : forall (rd : reader) a l1 l2, sa_bytes rd a (l1 ++ l2) ->
  sa_bytes rd a l1 /\ sa_bytes rd (a + Z.of_nat (length l1)) l2.
Proof.
intros rd a l1 l2 H. split.
- intros i Hi. rewrite (H i) by (rewrite length_app; lia). rewrite app_nth1 by exact Hi. reflexivity.
- intros i Hi. replace (a + Z.of_nat (length l1) + Z.of_nat i) with (a + Z.of_nat (length l1 + i)) by lia.
  rewrite (H (length l1 + i)%nat) by (rewrite length_app; lia). rewrite app_nth2 by lia.
  replace (length l1 + i - length l1)%nat with i by lia. reflexivity.
Qed.
Lemma cs_bytes_sub : forall (rd : reader) a bs k l, sa_bytes rd a bs -> (k + l <= length bs)%nat ->
  sa_bytes rd (a + Z.of_nat k) (firstn l (skipn k bs)).
Proof.
intros rd a bs k l H Hl.
rewrite <- (firstn_skipn k bs) in H. apply cs_bytes_app in H as [_ H].
rewrite length_firstn, Nat.min_l in H by lia.
rewrite <- (firstn_skipn l (skipn k bs)) in H. apply cs_bytes_app in H as [H _]. exact H.
Qed.
(* a char[cap] field holding the C string s: its bytes sx and their NUL *)
Lemma cs_cstr : forall (rd : reader) a f cap s, sa_bytes rd a f -> (cap <= length f)%nat ->
  seg_spec.cstr_enc cap s (firstn cap f) ->
  exists sx, sa_bytes rd a (sx ++ [seg_spec.ZERO]) /\ ~ In seg_spec.ZERO sx /\ seg_spec.zs sx = s /\ (length sx < cap)%nat.
Proof.
intros rd a f cap s H Hc (_ & Ls & N & E).
rewrite PCS.firstn_zs, firstn_firstn, Nat.min_l in E by lia.
remember (firstn (S (length s)) f) as g eqn:Hg.
assert (Lg : length g = S (length s)) by (subst g; rewrite length_firstn; lia).
destruct (skipn (length s) g) as [|b [|b' r]] eqn:Sk.
- apply (f_equal (@length byte)) in Sk. rewrite length_skipn in Sk. cbn in Sk. lia.
- assert (Eg : g = firstn (length s) g ++ [b]) by (rewrite <- Sk; symmetry; apply firstn_skipn).
  rewrite Eg in E. unfold seg_spec.zs in E. rewrite map_app in E. cbn [map] in E.
  apply app_inj_tail in E as [E1 E2].
  assert (Eb : b = seg_spec.ZERO) by (apply bv_eq; rewrite E2; reflexivity). subst b.
  exists (firstn (length s) g). split; [|split; [|split]].
  + rewrite <- Eg, Hg. rewrite <- (firstn_skipn (S (length s)) f) in H.
    apply cs_bytes_app in H as [H _]. exact H.
  + apply PCS.zs_nul. unfold seg_spec.zs. rewrite E1. exact N.
  + unfold seg_spec.zs. exact E1.
  + rewrite length_firstn. lia.
- apply (f_equal (@length byte)) in Sk. rewrite length_skipn in Sk. cbn in Sk. lia.
Qed.
(* the name of c->seg[i] (offset 0 of its 356-byte entry) and of m->seg[i] (offset 0 of its 256-byte entry) *)
Lemma cs_rname : forall (rd : reader) c rcs i, sa_rconf rd c rcs -> (i < length (rc_seg rcs))%nat ->
  exists sx, sa_bytes rd (c + 356 * Z.of_nat i) (sx ++ [seg_spec.ZERO]) /\ ~ In seg_spec.ZERO sx /\
             seg_spec.zs sx = rs_name (nth i (rc_seg rcs) rseg_d) /\ (length sx < 16)%nat.
Proof.
intros rd c rcs i (bs & H & L & L32 & HS & _) Hi.
destruct (HS i Hi) as (Lf & Hn & _).
unfold seg_spec.SEG_C_SIZE in L.
assert (B : sa_bytes rd (c + Z.of_nat (356 * i)) (seg_spec.fld (356 * i) 356 bs))
  by (unfold seg_spec.fld; apply cs_bytes_sub; [exact H | lia]).
replace (c + 356 * Z.of_nat i) with (c + Z.of_nat (356 * i)) by lia.
apply (cs_cstr rd _ _ 16 _ B); [lia | exact Hn].
Qed.
Lemma cs_mname : forall (rd : reader) m mcs i, sa_mconf rd m mcs -> (i < length (mc_seg mcs))%nat ->
  exists sx, sa_bytes rd (m + 256 * Z.of_nat i) (sx ++ [seg_spec.ZERO]) /\ ~ In seg_spec.ZERO sx /\
             seg_spec.zs sx = ms_name (nth i (mc_seg mcs) mseg_d) /\ (length sx < 16)%nat.
Proof.
intros rd m mcs i (bs & H & L & L32 & HS & _) Hi.
destruct (HS i Hi) as (Lf & Hn & _).
unfold seg_spec.SEG_M_SIZE in L.
assert (B : sa_bytes rd (m + Z.of_nat (256 * i)) (seg_spec.fld (256 * i) 256 bs))
  by (unfold seg_spec.fld; apply cs_bytes_sub; [exact H | lia]).
replace (m + 256 * Z.of_nat i) with (m + Z.of_nat (256 * i)) by lia.
apply (cs_cstr rd _ _ 16 _ B); [lia | exact Hn].
Qed.
(* under the premise, the i-th names of the two structs are one byte string sx *)
Lemma cs_names : forall (rd : reader) c m rcs mcs i,
  sa_rconf rd c rcs -> sa_mconf rd m mcs -> check_segments rcs mcs true = true -> (i < length (mc_seg mcs))%nat ->
  exists sx, sa_bytes rd (c + 356 * Z.of_nat i) (sx ++ [seg_spec.ZERO]) /\
             sa_bytes rd (m + 256 * Z.of_nat i) (sx ++ [seg_spec.ZERO]) /\
             ~ In seg_spec.ZERO sx /\ (length sx < 16)%nat.
Proof.
intros rd c m rcs mcs i HC HM CS Hi.
destruct (PCS.cs_true _ _ _ CS) as (Ln & _ & Hf & _).
destruct (cs_rname rd c rcs i HC ltac:(lia)) as (sx & Bx & Nx & Zx & Lx).
destruct (cs_mname rd m mcs i HM Hi) as (sy & By & Ny & Zy & Ly).
pose proof (PCS.forallb2_nth _ _ _ rseg_d mseg_d i Hf ltac:(lia)) as P. cbv beta in P.
apply Z.eqb_eq in P. rewrite <- Zx, <- Zy in P.
apply (proj1 (PCS.bridge_strcmp sx sy Nx Ny)) in P. subst sy.
exists sx. auto.
Qed.
(* the 4 bytes of a u32 field *)
Lemma cs_le4_byte : forall v k, 0 <= v < 2 ^ 32 -> (k < 4)%nat ->
  bv_unsigned (nth k (PMem.le4 (Z_to_bv 64 v)) seg_spec.ZERO) = le_byte v 4 k.
Proof.
intros v k Hv Hk. unfold PMem.le4. rewrite unsigned_lit_small by lia.
unfold le_byte. change (8 * Z.of_nat 4) with 32. rewrite (Z.mod_small v (2 ^ 32)) by lia.
destruct k as [|[|[|[|k]]]]; [| | | | lia]; cbn [Z_to_le_bytes nth Z.of_nat];
rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 8) with 256;
rewrite ?Z.shiftr_shiftr by lia; rewrite ?Z.mul_0_r, ?Z.shiftr_0_r; try reflexivity; f_equal; f_equal; lia.
Qed.
Lemma cs_u32_at : forall (rd : reader) a bs k v, sa_bytes rd a bs -> 0 <= k -> k + 4 <= Z.of_nat (length bs) ->
  seg_spec.u32_enc v (seg_spec.fldz k 4 bs) -> sa_val rd (a + k) 4 v.
Proof.
intros rd a bs k v H Hk Hl (Hv & E) j Hj.
replace (a + k + Z.of_nat j) with (a + Z.of_nat (Z.to_nat k + j)) by lia.
rewrite (H (Z.to_nat k + j)%nat) by lia. f_equal.
rewrite <- (cs_le4_byte v j Hv Hj). rewrite <- E. unfold seg_spec.fldz, seg_spec.fld.
change (Z.to_nat 4) with 4%nat. rewrite nth_firstn, nth_skipn.
replace (j <? 4)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hj). reflexivity.
Qed.
Lemma cs_val_mem_of_sa : forall segs H mem a n v, sa_val (aview segs H mem) a n v -> val_mem segs (mrestrict H mem) a n v.
Proof.
intros segs H mem a n v Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
destruct (mbyte segs (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:Eb; cbn in Hv; [|discriminate Hv].
injection Hv as Hb. rewrite <- (Z_to_bv_bv_unsigned 8 b). rewrite Hb. reflexivity.
Qed.
Lemma cs_val_keep : forall (rd rd' : reader) lo hi a n v, kept_out rd rd' lo hi -> sa_val rd a n v ->
  0 <= a -> (hi <= a \/ a + Z.of_nat n <= lo) -> a + Z.of_nat n < 2 ^ 64 -> sa_val rd' a n v.
Proof. intros rd rd' lo hi a n v HK H Ha Hw Hr k Hk. rewrite (HK (a + Z.of_nat k)) by lia. exact (H k Hk). Qed.

(* ---------- small facts of the symbolic values ---------- *)
Lemma cs_swrap_small : forall z, 0 <= z < 2 ^ 63 -> bv_swrap 64 z = z.
Proof.
intros z Hz. unfold bv_swrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). change (2 ^ 64 / 2) with (2 ^ 63).
rewrite bv_wrap_small; [lia|]. change (bv_modulus 64) with (2 ^ 64). lia.
Qed.
Lemma cs_bge0 : forall E n v, ew E n = w64 v -> 0 <= v < 2 ^ 63 ->
  branch_taken BC_GE (sv_denot E (SLit 0)) (sv_denot E (SOff n 0)) = (v <=? 0).
Proof.
intros E n v Hn Hv. cbn [branch_taken sv_denot]. rewrite Hn, Z.add_0_r. unfold w64. rewrite unsigned_lit_small by lia.
unfold bv_lts. rewrite !signed_lit. rewrite !zcanon_small by lia. rewrite !cs_swrap_small by lia.
destruct (Z.ltb_spec 0 v); destruct (Z.leb_spec v 0); try reflexivity; lia.
Qed.
(* image B's loop registers as its code computes them: `not s5,s1` (xori -1, 0x87030), `slli s7,a3,8` (0x87038),
   `add a0,s1,s3` / `add a1,s2,s4` (0x8704c, 0x87050) *)
Lemma cs_not_w : forall x k, 0 <= x < 2 ^ 64 -> k mod 2 ^ 64 = 2 ^ 64 - 1 ->
  alu64 ALU_XOR (Z_to_bv 64 x) (Z_to_bv 64 k) = Z_to_bv 64 (2 ^ 64 - 1 - x).
Proof.
intros x k Hx Hk. apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw].
rewrite (unsigned_lit_small x) by lia.
replace (bv_unsigned (Z_to_bv 64 k)) with 18446744073709551615
  by (rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64); rewrite Hk; reflexivity).
rewrite (PZB.zb_lxor_ones x Hx). rewrite unsigned_lit_small by lia.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia. lia.
Qed.
Lemma cs_sll8_w : forall v, 0 <= v < 2 ^ 32 ->
  alu64 ALU_SLL (Z_to_bv 64 v) (Z_to_bv 64 8) = Z_to_bv 64 (256 * v).
Proof.
intros v Hv. apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw].
rewrite (unsigned_lit_small v), (unsigned_lit_small 8) by lia. change (Z.land 8 63) with 8.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256. rewrite (unsigned_lit_small (256 * v)) by lia.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia. lia.
Qed.
Lemma cs_add_w : forall a b, alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
intros a b. apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite !Z_to_bv_unsigned.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite <- Z.add_mod by lia. reflexivity.
Qed.

(* ---------- image B's numbers, the listing offsets and the symbolic states ---------- *)
(* image B's stack need of check_segments, image B's instance file's SegInstB.STK_check_segments, under the name the
   proofs here and in check_segments.v use: its frame (0x86f58 `addi sp,sp,-80`) and, below it, the strcmp wrapper's
   window (lib/B/Rt/RtString.v astrcmp_realizes: 2 * ESTACK; the call 0x87054 is at sp0 - 80, 16-aligned) *)
Notation STK_check_segments_B := SegInstB.STK_check_segments (only parsing).
(* the offsets from the listing's base (BASE + AF_check_segments = 0x84dc0 + 0x2198 = 0x86f58) *)
Definition CS_LOOP : Z := 0x2280.   (* 0x87040, the loop's head (`beqz s8`) *)
Definition CS_EXIT : Z := 0x22ac.   (* 0x8706c, `beqz s0` and the epilogue *)
Definition CS_RA : Z := 0x2298.     (* 0x87058, after `jal wrapper_strcmp` *)
(* the frame: ra, s0 .. s8 saved at sp0 - 8 .. sp0 - 80 *)
Definition cs_saved : list Z := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24].
(* the callee-saved registers the function never writes (besides sp) *)
Definition cs_untouched : list Z := [3; 4; 25; 26; 27].
Definition cs_spF : afact := mkAF (2 ^ 46) (2 ^ 47) 4.
Definition cs_SBF : afact := mkAF SB SB 0.
(* the two structs' pointers: heap blocks below the allocator's ceiling (at most 2^47 - 2^23), 16-aligned; the bound
   keeps each struct's shadow inside the shadow band (sh_static_ok's shent_in_span); the alignment 2^4 folds UBSan's
   `andi a0,a0,7` (0x86f88) and `andi a0,s2,3` (0x86fc0) to 0 *)
Definition cs_PF : afact := mkAF 4096 (2 ^ 47 - 2 ^ 23) 4.
Definition cs_NF : afact := mkAF 0 32 0.
Definition cs_Bx : sv := SOff 32 0.
(* the entry's atoms 32 .. 36: the shadow base, c->n, m->n, c->overflow, m->overflow *)
Definition cs_creg : YP09.region := YP09.mkRegion (Some 10%nat) 0x2c80 0x34d4 0 0
  [YP09.mkChunk 0x2c80 (CVal 4 (SOff 33 0)); YP09.mkChunk 0x34d0 (CVal 4 (SOff 35 0))].
Definition cs_mreg : YP09.region := YP09.mkRegion (Some 11%nat) 0x2000 0x2008 0 0
  [YP09.mkChunk 0x2000 (CVal 4 (SOff 34 0)); YP09.mkChunk 0x2004 (CVal 4 (SOff 36 0))].
Definition cs_e_facts : facts := mkFacts
  [(2%nat, cs_spF); (32%nat, cs_SBF); (10%nat, cs_PF); (11%nat, cs_PF); (33%nat, cs_NF); (34%nat, cs_NF)] [] [].
Definition cs_ss_entry : sstate :=
  mkSS AF_check_segments sr_atoms [stack_region 80; got_regionP; bcell_regionP 32; cs_creg] None cs_e_facts.
(* the two structs' shadow: [c, c + 16616) and [m, m + 9236) *)
Definition cs_SH : list shent := [mkSHE 10 0 16616; mkSHE 11 0 9236].
(* the loop's head: registers only *)
Definition cs_ss_loop : sstate := mkSS CS_LOOP sr_atoms [] None (mkFacts [(2%nat, cs_spF)] [] []).
(* the exit: s0 pinned to 1, the frame re-read from its ten words (atoms 32 .. 41) *)
Definition cs_estack : YP09.region := YP09.mkRegion (Some 2%nat) 0 80 0 0
  (map (fun j => YP09.mkChunk (72 - 8 * Z.of_nat j) (CVal 8 (SOff (32 + j) 0))) (seq 0 10)).
Definition cs_ss_exit : sstate :=
  mkSS CS_EXIT (sr_set sr_atoms 8 (SLit 1)) [cs_estack] None (mkFacts [(2%nat, cs_spF)] [] []).
(* swap the one table region of a state *)
Definition cs_swap (r : YP09.region) (ss : sstate) : sstate := mkSS (ss_pc ss) (ss_regs ss) [r] (ss_resv ss) (ss_facts ss).

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Lemma cs_swap_ok : forall E ss ms r,
  st_ok_pi SEGS VAL E ss ms -> region_wf r = true -> region_ok SEGS E (ms_mem ms) r ->
  st_ok_pi SEGS VAL E (cs_swap r ss) ms.
Proof.
intros E ss ms r HS Hwf Hr.
pose proof (st_ok_pi_submem E ss ms [] HS (submem_nil _) eq_refl) as HS0.
pose proof (st_ok_pi_add_region E _ ms r HS0 Hwf Hr I) as HS1. exact HS1.
Qed.
Lemma cs_ex_w64 : forall regs1 (l : list Z) j, (32 + j < A_TEXT)%nat -> (j < length l)%nat ->
  ew (Eimg (Ereg regs1 (map w64 l))) (32 + j) = w64 (nth j l 0).
Proof.
intros regs1 l j H1 H2. rewrite Eimg_low by exact H1. rewrite ew_Ereg_extra.
rewrite (nth_indep _ _ (w64 0)) by (rewrite length_map; exact H2). apply map_nth.
Qed.

Section e.
Variable B : asyms.
Hypothesis TL : PALib B.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let errno_low := pal_env B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_seg) (PI := PI).

Ltac cs_regs_ok EE eqs :=
  apply regs_ok_by_cases; intros rr Hrr; cbv [all_regs In] in Hrr;
  repeat (destruct Hrr as [<- | Hrr];
    [ lazymatch goal with |- getr _ _ = sv_denot _ (sr_get ?a0 ?rr2) =>
        let v := eval vm_compute in (sr_get a0 rr2) in change (sr_get a0 rr2) with v end;
      cbn [sv_denot];
      first [ reflexivity
            | rewrite Z.add_0_r, Z_to_bv_bv_unsigned; symmetry; apply EE; reflexivity
            | rewrite ?Z.add_0_r; eqs; assumption ]
    | ]); try (destruct Hrr).
Ltac cs_md :=
  lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?md2 _ |- _ =>
    lazymatch md2 with with_vm_backing _ _ _ => let m := fresh "mdv" in set (m := md2) in *; clearbody m | _ => idtac end end.
Ltac cs_kept_empty HFr K lo hi :=
  lazymatch type of HFr with frame_of _ _ (mrestrict ?H ?m1) (mrestrict ?H ?m2) =>
  assert (K : kept_out (aview SEGS H m1) (aview SEGS H m2) lo hi)
  by (intros x0 Hx0 Hn0; apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) HFr);
      [ intros b0 wlo whi a0 Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia|]); destruct Hin
      | exact Hx0 | tauto ]) end.
Ltac cs_kept_win HFr K lo hi Usp :=
  lazymatch type of HFr with frame_of _ _ (mrestrict ?H ?m1) (mrestrict ?H ?m2) =>
  assert (K : kept_out (aview SEGS H m1) (aview SEGS H m2) lo hi)
  by (intros x0 Hx0 Hn0; apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun x => lo <= x < hi) HFr);
      [ intros b0 wlo whi a0 Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp in Hrr; lia|]); destruct Hin
      | exact Hx0 | exact Hn0 ]) end.

(* ---------- one call of check_segments ---------- *)
Section w.
Variables (ly : alayout) (S : astate) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (ch : list (Z * Z * Z)) (c mm : Z) (rcs : rconf) (mcs : mconf) (returned : bool).
Hypothesis HPRE : afn_pre SEGS B STK_check_segments_B ly S W regs mem md ch.
Hypothesis H10 : getr regs 10 = w64 c.
Hypothesis H11 : getr regs 11 = w64 mm.
Hypothesis H12 : getr regs 12 = w64 (seg_spec.b2z returned).
Hypothesis HC16 : c mod 16 = 0.
Hypothesis HRC : sa_rconf (rdW W mem) c rcs.
Hypothesis HHC : sa_heap B ly S c seg_spec.SEG_C_SIZE.
Hypothesis HAC : sa_addr (rdW W mem) c seg_spec.SEG_C_SIZE.
Hypothesis HM16 : mm mod 16 = 0.
Hypothesis HRM : sa_mconf (rdW W mem) mm mcs.
Hypothesis HHM : sa_heap B ly S mm seg_spec.SEG_M_SIZE.
Hypothesis HAM : sa_addr (rdW W mem) mm seg_spec.SEG_M_SIZE.
Hypothesis HCS : check_segments rcs mcs returned = true.

Definition cs_Q : world SEGS -> config -> Prop :=
apost_base SEGS B STK_check_segments_B [] regs ly S W mem md EV_check_segments
(fun ly' S' W' regs' mem' md' =>
 sa_kept SEGS W mem W' mem' regs STK_check_segments_B (fun _ => False) /\ sa_noalloc B ly S ly' S').
(* the saved registers in the frame *)
Definition cs_frame (rd : reader) : Prop :=
forall j r, nth_error cs_saved j = Some r ->
sa_val rd (spZ regs - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r))).
(* a cut point: the journal from the entry, the memory below the stack window unchanged, the frame, sp, the
   callee-saved registers the function does not write, and s0 = returned = 1 *)
Definition cs_cut (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
ajournal SEGS B STK_check_segments_B (spZ regs) [] ly S W mem md [] ly S W mem1 md1 0 /\
kept_out (rdW W mem) (rdW W mem1) (spZ regs - STK_check_segments_B) (spZ regs) /\
cs_frame (rdW W mem1) /\
getr regs1 2 = w64 (spZ regs - 80) /\
(forall k, In k cs_untouched -> getr regs1 (Z_to_bv 5 k) = getr regs (Z_to_bv 5 k)) /\
getr regs1 8 = w64 1.
(* the loop's head after i entries: s1 = c, s2 = m, s3 = 356 i, s4 = 256 i, s5 = ~c, s6 = ~m, s7 = 256 n, s8 = 32 - i *)
Definition cs_loop (i : nat) (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
cs_cut regs1 mem1 md1 /\ (i < length (mc_seg mcs))%nat /\
getr regs1 9 = w64 c /\ getr regs1 18 = w64 mm /\
getr regs1 19 = w64 (356 * Z.of_nat i) /\ getr regs1 20 = w64 (256 * Z.of_nat i) /\
getr regs1 21 = w64 (2 ^ 64 - 1 - c) /\ getr regs1 22 = w64 (2 ^ 64 - 1 - mm) /\
getr regs1 23 = w64 (256 * Z.of_nat (length (mc_seg mcs))) /\ getr regs1 24 = w64 (32 - Z.of_nat i).

Lemma cs_sp : spZ regs mod 16 = 0 /\ alloc_ceiling + STK_check_segments_B <= spZ regs /\ spZ regs <= 2 ^ 47.
Proof using HPRE c mm.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2). lia.
Qed.
(* where the two structs lie: inside a live heap block, below the stack window, apart from the shadow band *)
Lemma cs_blk : forall q n, sa_heap B ly S q n -> 0 < n ->
  4096 <= q /\ q + n <= alloc_ceiling /\ (forall x, q <= x < q + n -> ~ (SB <= x < SB + 2 ^ 44)) /\
  (q + n <= 0x10000 \/ 0x602000 <= q) /\
  exists b k, In (b, k) (ablocks B ly S) /\ b <= q /\ q + n <= b + k.
Proof using HPRE c mm.
intros q n (b & k & Hin & Hb & Hk) Hn.
pose proof HPRE as (HAR & _).
destruct (al_blocks _ _ LAWS ly S W mem md b k HAR Hin) as (Hp16 & Hp4096 & Hpceil & Hpapp & Hppres & _ & Hkr).
pose proof (req_size_pos k ltac:(lia)) as [_ Hreq].
assert (Hoff : off_img b (req_size k)) by (eapply blk_off_imgP; eassumption).
unfold off_img, kImgEnd in Hoff.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; [lia|]. split; [lia|]. split; [|split; [lia | exists b, k; auto]].
intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SB in *. lia.
Qed.
Lemma cs_n : length (rc_seg rcs) = length (mc_seg mcs) /\ rc_overflow rcs = mc_overflow mcs /\ returned = true /\
  (length (mc_seg mcs) <= 32)%nat.
Proof using HCS HRM.
destruct (PCS.cs_true _ _ _ HCS) as (Ln & Ov & _ & Hr). destruct HRM as (bs & _ & _ & L32 & _). auto.
Qed.

(* the regions of the two structs at a later state whose memory equals the entry's below the stack window *)
Lemma cs_creg_ok : forall E memx, kept_out (rdW W mem) (rdW W memx) (spZ regs - STK_check_segments_B) (spZ regs) ->
  bv_unsigned (ew E 10) = c -> ew E 33 = w64 (Z.of_nat (length (rc_seg rcs))) -> ew E 35 = w64 (rc_overflow rcs) ->
  region_ok SEGS E (mrestrict (w_H W) memx) cs_creg.
Proof using HPRE HRC HHC c mm.
intros E memx HK E10 E33 E35.
pose proof cs_sp as (Hal16 & Hslo & Hshi). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (cs_blk c _ HHC ltac:(unfold seg_spec.SEG_C_SIZE; lia)) as (Hc4 & Hcc & _ & _).
unfold seg_spec.SEG_C_SIZE in *.
destruct HRC as (bs & HB & L & _ & _ & UN & _ & _ & _ & _ & UO & _). unfold seg_spec.SEG_C_SIZE in L.
pose proof (cs_u32_at _ c bs seg_spec.RC_N _ HB ltac:(unfold seg_spec.RC_N; lia) ltac:(unfold seg_spec.RC_N; lia) UN) as VN.
pose proof (cs_u32_at _ c bs seg_spec.RC_OVERFLOW _ HB ltac:(unfold seg_spec.RC_OVERFLOW; lia) ltac:(unfold seg_spec.RC_OVERFLOW; lia) UO) as VO.
unfold seg_spec.RC_N, seg_spec.RC_OVERFLOW in VN, VO.
destruct UN as [RN _]. destruct UO as [RO _].
unfold region_ok, cs_creg. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E10.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
- apply (chunk_ok_val SEGS E _ c 0x2c80 4 (SOff 33 0) (Z.of_nat (length (rc_seg rcs))));
    [cbn [sv_denot]; rewrite E33, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
  apply cs_val_mem_of_sa. apply (cs_val_keep _ _ _ _ _ _ _ HK VN); cbn; lia.
- apply (chunk_ok_val SEGS E _ c 0x34d0 4 (SOff 35 0) (rc_overflow rcs));
    [cbn [sv_denot]; rewrite E35, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
  apply cs_val_mem_of_sa. apply (cs_val_keep _ _ _ _ _ _ _ HK VO); cbn; lia.
Qed.
Lemma cs_mreg_ok : forall E memx, kept_out (rdW W mem) (rdW W memx) (spZ regs - STK_check_segments_B) (spZ regs) ->
  bv_unsigned (ew E 11) = mm -> ew E 34 = w64 (Z.of_nat (length (mc_seg mcs))) -> ew E 36 = w64 (mc_overflow mcs) ->
  region_ok SEGS E (mrestrict (w_H W) memx) cs_mreg.
Proof using HPRE HRM HHM c mm.
intros E memx HK E11 E34 E36.
pose proof cs_sp as (Hal16 & Hslo & Hshi). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (cs_blk mm _ HHM ltac:(unfold seg_spec.SEG_M_SIZE; lia)) as (Hm4 & Hmc & _ & _).
unfold seg_spec.SEG_M_SIZE in *.
destruct HRM as (bs & HB & L & _ & _ & UN & UO & _). unfold seg_spec.SEG_M_SIZE in L.
pose proof (cs_u32_at _ mm bs seg_spec.MC_N _ HB ltac:(unfold seg_spec.MC_N; lia) ltac:(unfold seg_spec.MC_N; lia) UN) as VN.
pose proof (cs_u32_at _ mm bs seg_spec.MC_OVERFLOW _ HB ltac:(unfold seg_spec.MC_OVERFLOW; lia) ltac:(unfold seg_spec.MC_OVERFLOW; lia) UO) as VO.
unfold seg_spec.MC_N, seg_spec.MC_OVERFLOW in VN, VO.
destruct UN as [RN _]. destruct UO as [RO _].
unfold region_ok, cs_mreg. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E11.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
- apply (chunk_ok_val SEGS E _ mm 0x2000 4 (SOff 34 0) (Z.of_nat (length (mc_seg mcs))));
    [cbn [sv_denot]; rewrite E34, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
  apply cs_val_mem_of_sa. apply (cs_val_keep _ _ _ _ _ _ _ HK VN); cbn; lia.
- apply (chunk_ok_val SEGS E _ mm 0x2004 4 (SOff 36 0) (mc_overflow mcs));
    [cbn [sv_denot]; rewrite E36, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
  apply cs_val_mem_of_sa. apply (cs_val_keep _ _ _ _ _ _ _ HK VO); cbn; lia.
Qed.

(* the shadow of a struct the walk's checks read *)
Lemma cs_shent_ok : forall E m n x lo hi, ew E 32 = w64 SB -> bv_unsigned (ew E n) = x -> 0 <= x + lo -> x + hi < 2 ^ 64 -> lo <= hi ->
  range_addressable (YCbn.rd_of SEGS m) SHADOW_OFF (x + lo) (hi - lo) ->
  (forall y, x + lo <= y < x + hi -> ~ (SB <= y < SB + 2 ^ 44)) ->
  shent_ok SEGS cs_Bx E m (mkSHE n lo hi).
Proof.
intros E m n x lo hi H32 Hn H0 H1 Hlh Hra Hband. unfold shent_ok, app_apart, cs_Bx. cbn [she_m she_lo she_hi].
assert (U32 : U E (SOff 32 0) = SB).
{ rewrite U_SOff, H32, Z.add_0_r. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). apply zcanon_small. unfold SB; lia. }
assert (Hxr : 0 <= x < 2 ^ 64) by (rewrite <- Hn; pose proof (bv_unsigned_in_range 64 (ew E n)) as HR; change (bv_modulus 64) with (2 ^ 64) in HR; exact HR).
assert (Un : U E (SOff n 0) = x) by (rewrite U_SOff, Hn, Z.add_0_r; apply zcanon_small; exact Hxr).
rewrite U32, Un. split; [exact Hra|].
intros y Hy. rewrite Z.min_l, Z.max_r in Hy by lia. apply Hband. lia.
Qed.

(* ---------- the exit: 0x8706c .. 0x8709c, `beqz s0` (s0 = 1), ra s0 .. s8 restored, ret ---------- *)
Definition cs_x_extra : list word := map (fun r => getr regs (Z_to_bv 5 r)) cs_saved.
Lemma cs_x_nth : forall j r, nth_error cs_saved j = Some r -> nth j cs_x_extra (Z_to_bv 64 0) = getr regs (Z_to_bv 5 r).
Proof. intros j r H. unfold cs_x_extra. apply nth_error_nth. rewrite (map_nth_error (fun r0 => getr regs (Z_to_bv 5 r0)) j cs_saved H). reflexivity. Qed.
Lemma cs_exit_seed : forall regs1 mem1, getr regs1 2 = w64 (spZ regs - 80) -> getr regs1 8 = w64 1 -> cs_frame (rdW W mem1) ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs1 cs_x_extra)) cs_ss_exit
    (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + CS_EXIT)) mem1 (seg_rom SEGS)))
  /\ sh_ok SEGS cs_Bx [] (Eimg (Ereg regs1 cs_x_extra)) (mrestrict (w_H W) mem1).
Proof using HPRE c mm.
intros regs1 mem1 R2 R8 HFR. pose proof cs_sp as (Hal16 & Hlo & Hhi).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HST : STK_check_segments_B = 8272) by reflexivity.
set (E := Eimg (Ereg regs1 cs_x_extra)).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r) by (intros n r Hn; apply ew_Eimg_Ereg_nat; exact Hn).
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 80).
{ rewrite (EE 2%nat 2%bv eq_refl), R2. unfold w64. apply unsigned_lit_small. lia. }
split; [|apply Forall_nil].
rewrite restrict_mkst_fx. unfold cs_ss_exit. apply pa_entry_st_ok_full.
- cs_regs_ok EE ltac:(idtac).
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok, cs_estack.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_forall. intros ck Hck. apply in_map_iff in Hck as (j & <- & Hj). apply in_seq in Hj.
  destruct (nth_error cs_saved j) as [r|] eqn:Hr; [| apply nth_error_None in Hr; cbn in Hr; lia].
  pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as HRr. change (bv_modulus 64) with (2 ^ 64) in HRr.
  apply (chunk_ok_val SEGS E _ (spZ regs - 80) (72 - 8 * Z.of_nat j) 8 (SOff (32 + j) 0) (bv_unsigned (getr regs (Z_to_bv 5 r)))).
  + cbn [sv_denot]. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite ew_Ereg_extra, (cs_x_nth j r Hr).
    rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  + change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact HRr.
  + cbn. lia.
  + replace (spZ regs - 80 + (72 - 8 * Z.of_nat j)) with (spZ regs - 8 - 8 * Z.of_nat j) by lia.
    apply cs_val_mem_of_sa. exact (HFR j r Hr).
- cbn. tauto.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. split; [|exact I]. unfold afact_ok, cs_spF. cbn [af_lo af_hi af_al2]. rewrite Usp.
  change (2 ^ 4) with 16. split; [lia|]. split; [|lia]. rewrite Zminus_mod, Hal16. reflexivity.
Qed.
Lemma cs_exit : forall regs1 mem1 md1, cs_cut regs1 mem1 md1 ->
  SRr SEGS W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + CS_EXIT)) mem1 (seg_rom SEGS)) md1) cs_Q.
Proof using TL HPRE HHC HHM c mm.
intros regs1 mem1 md1 (HJ & HK & HFR & R2 & RU & R8).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof cs_sp as (Hal16 & Hlo & Hhi).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HST : STK_check_segments_B = 8272) by reflexivity.
destruct (cs_exit_seed regs1 mem1 R2 R8 HFR) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs1 cs_x_extra))) by apply Eimg_env.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (Eimg (Ereg regs1 cs_x_extra)) n = getr regs1 r)
  by (intros n r Hn; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j r, nth_error cs_saved j = Some r -> ew (Eimg (Ereg regs1 cs_x_extra)) (32 + j) = getr regs (Z_to_bv 5 r)).
{ intros j r Hr. assert (Hj : (j < 10)%nat) by (change 10%nat with (length cs_saved); apply (proj1 (nth_error_Some cs_saved j)); rewrite Hr; discriminate).
  rewrite Eimg_low by (unfold A_TEXT; lia). rewrite ew_Ereg_extra. exact (cs_x_nth j r Hr). }
assert (Usp : bv_unsigned (ew (Eimg (Ereg regs1 cs_x_extra)) 2) = spZ regs - 80).
{ rewrite (EE 2%nat 2%bv eq_refl), R2. unfold w64. apply unsigned_lit_small. lia. }
pose proof (EX 0%nat 1 eq_refl) as E32. pose proof (EX 1%nat 8 eq_refl) as E33. pose proof (EX 2%nat 9 eq_refl) as E34.
pose proof (EX 3%nat 18 eq_refl) as E35. pose proof (EX 4%nat 19 eq_refl) as E36. pose proof (EX 5%nat 20 eq_refl) as E37.
pose proof (EX 6%nat 21 eq_refl) as E38. pose proof (EX 7%nat 22 eq_refl) as E39. pose proof (EX 8%nat 23 eq_refl) as E40.
pose proof (EX 9%nat 24 eq_refl) as E41.
cbn [Nat.add] in E32, E33, E34, E35, E36, E37, E38, E39, E40, E41. clear EX.
assert (RUk : forall k, In k cs_untouched -> ew (Eimg (Ereg regs1 cs_x_extra)) (Z.to_nat k) = getr regs (Z_to_bv 5 k)).
{ intros k Hk. rewrite <- (RU k Hk). apply EE. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32.
  assert (0 <= k < 32) by (cbv [cs_untouched In] in Hk; lia). rewrite Z.mod_small by lia. lia. }
remember (Eimg (Ereg regs1 cs_x_extra)) as E eqn:HE. clear HE.
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac; exact Usp. }
cs_md.
cs_kept_empty HFr KEEPX (spZ regs - STK_check_segments_B) (spZ regs - STK_check_segments_B). clear HF HFr HG.
prreg HS (1%bv : bv 5) F1.
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold cs_Q, apost_base.
lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly, S, r, m, d end.
split.
{ rewrite F1, E32. change (getr regs (Z_to_bv 5 1)) with (getr regs 1). unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split.
{ apply (ajournal_materialize SEGS B LAWS pa_segs_low). exact HJ. }
split.
{ unfold aregs_preserved. intros r Hr.
  assert (Hcases : r = 2 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ In r cs_untouched)
    by (unfold acallee_saved in Hr; cbv [cs_untouched In]; lia).
  clear Hr.
  destruct Hcases as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | Hu]]]]]]]]]];
  try (rewrite (st_ok_pi_restrict_reg (w_H W) E _ _ _ HS); cbn [ms_regs];
    lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ => let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
    cbn [sv_denot];
    first
    [ rewrite Usp; replace (spZ regs - 80 + 80) with (spZ regs) by lia; unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity
    | rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
      first [ rewrite E33; reflexivity | rewrite E34; reflexivity | rewrite E35; reflexivity | rewrite E36; reflexivity
            | rewrite E37; reflexivity | rewrite E38; reflexivity | rewrite E39; reflexivity | rewrite E40; reflexivity
            | rewrite E41; reflexivity ] ]).
  assert (Hr32 : 0 <= r < 32) by (cbv [cs_untouched In] in Hu; lia).
  rewrite (st_ok_pi_restrict_reg (w_H W) E _ _ _ HS); cbn [ms_regs].
  cbv [cs_untouched In] in Hu.
  repeat (destruct Hu as [<- | Hu];
    [ lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ => let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
      cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
      lazymatch goal with |- _ = getr _ (Z_to_bv 5 ?kk) => apply (RUk kk); cbv [cs_untouched In]; tauto end
    | ]); destruct Hu. }
split.
{ intros a Ha Hn _. rewrite (KEEPX a Ha) by lia. exact (HK a Ha Hn). }
unfold sa_noalloc. split; [apply Permutation_refl|]. split; [reflexivity|]. exists (st_fs S). destruct S; reflexivity.
Qed.

(* ---------- the entry: 0x86f58 .. 0x8703c ---------- *)
Definition cs_e_extra : list word :=
map w64 [SB; Z.of_nat (length (rc_seg rcs)); Z.of_nat (length (mc_seg mcs)); rc_overflow rcs; mc_overflow mcs].
Lemma cs_stack_field : forall E H mem' cs off n v,
  region_ok SEGS E (mrestrict H mem') (YP09.mkRegion (Some 2%nat) (-80) 0 (-80) 0 cs) -> bv_unsigned (ew E 2) = spZ regs ->
  In (YP09.mkChunk off (CVal 8 (SOff n 0))) cs -> ew E n = w64 v -> 0 <= v < 2 ^ 64 ->
  sa_val (aview SEGS H mem') (spZ regs + off) 8 v.
Proof.
intros E H mem' cs off n v HR Hsp Hin Hn Hv.
intros k Hk. unfold aview.
change 8%nat with (N.to_nat 8) in Hk.
pose proof (field_of_region E _ 2 (spZ regs) cs (-80) 0 (-80) 0 off 8 (SOff n 0) v HR Hsp Hin) as HF.
rewrite (HF ltac:(cbn [sv_denot]; rewrite Hn, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by lia; reflexivity)
  ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Hv) ltac:(cbn; lia) k Hk).
cbn [option_map]. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold le_byte. apply Z.mod_mod. lia.
Qed.
Lemma cs_entry_seed :
  st_ok_pi SEGS VAL (Eimg (Ereg regs cs_e_extra)) cs_ss_entry
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_check_segments)) mem (seg_rom SEGS)))
  /\ sh_ok SEGS cs_Bx cs_SH (Eimg (Ereg regs cs_e_extra)) (mrestrict (w_H W) mem).
Proof using TL HPRE H10 H11 HC16 HRC HHC HAC HM16 HRM HHM HAM HCS.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof cs_sp as (Hal16 & Hslo & Hshi). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HST : STK_check_segments_B = 8272) by reflexivity.
destruct cs_n as (Ln & Ov & Hret & L32).
destruct (cs_blk c _ HHC ltac:(unfold seg_spec.SEG_C_SIZE; lia)) as (Hc4 & Hcc & HcBD & HcOff & _).
destruct (cs_blk mm _ HHM ltac:(unfold seg_spec.SEG_M_SIZE; lia)) as (Hm4 & Hmc & HmBD & HmOff & _).
unfold seg_spec.SEG_C_SIZE, seg_spec.SEG_M_SIZE in *.
set (E := Eimg (Ereg regs cs_e_extra)).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) by (intros n r Hn; apply ew_Eimg_Ereg_nat; exact Hn).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (EX : forall j v, nth_error [SB; Z.of_nat (length (rc_seg rcs)); Z.of_nat (length (mc_seg mcs)); rc_overflow rcs; mc_overflow mcs] j = Some v ->
  ew E (32 + j) = w64 v).
{ intros j v Hj. assert (Hj5 : (j < 5)%nat) by (change 5%nat with (length [SB; Z.of_nat (length (rc_seg rcs)); Z.of_nat (length (mc_seg mcs)); rc_overflow rcs; mc_overflow mcs]); apply (proj1 (nth_error_Some _ j)); rewrite Hj; discriminate).
  subst E. unfold cs_e_extra. rewrite cs_ex_w64 by (cbn; unfold A_TEXT; lia). f_equal. apply nth_error_nth. exact Hj. }
pose proof (EX 0%nat _ eq_refl) as E32. pose proof (EX 1%nat _ eq_refl) as E33. pose proof (EX 2%nat _ eq_refl) as E34.
pose proof (EX 3%nat _ eq_refl) as E35. pose proof (EX 4%nat _ eq_refl) as E36.
cbn [Nat.add] in E32, E33, E34, E35, E36. clear EX.
assert (E32u : bv_unsigned (ew E 32) = SB) by (rewrite E32; apply unsigned_lit_small; unfold SB; lia).
assert (E10u : bv_unsigned (ew E 10) = c) by (rewrite (EE 10%nat 10%bv eq_refl), H10; apply unsigned_lit_small; lia).
assert (E11u : bv_unsigned (ew E 11) = mm) by (rewrite (EE 11%nat 11%bv eq_refl), H11; apply unsigned_lit_small; lia).
assert (E33u : bv_unsigned (ew E 33) = Z.of_nat (length (rc_seg rcs))) by (rewrite E33; apply unsigned_lit_small; lia).
assert (E34u : bv_unsigned (ew E 34) = Z.of_nat (length (mc_seg mcs))) by (rewrite E34; apply unsigned_lit_small; lia).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_val_range (A_OBJ 0)) as R0. pose proof (pa_val_range (A_OBJ 12)) as R12.
assert (U241 : bv_unsigned (ew E (A_OBJ 0)) = VAL (A_OBJ 0)) by (rewrite E241; apply unsigned_lit_small; lia).
assert (U253 : bv_unsigned (ew E (A_OBJ 12)) = VAL (A_OBJ 12)) by (rewrite E253; apply unsigned_lit_small; lia).
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR. pose proof (pal_got_cell B TL) as HgcD.
unfold kImgEnd in HcellR, HgotR.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
pose proof (cs_creg_ok E mem ltac:(intros a Ha Hn; reflexivity) E10u E33 E35) as RCR.
split.
- rewrite restrict_mkst_fx. unfold cs_ss_entry. apply pa_entry_st_ok_full.
  + subst E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold stack_region, got_regionP, bcell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; [unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]..| exact RCR].
    * rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    * rewrite U241. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
        [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kgot).
    * rewrite U253. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SB);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by (unfold SB; lia); reflexivity
        | unfold SB; cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kcell).
  + apply pairwise_disjoint_of_extents. unfold stack_region, got_regionP, bcell_regionP, cs_creg, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, U241, U253, E10u.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kImgEnd in *. repeat split; lia.
  + split; [|split; exact I]. cbn [f_atoms atoms_ok cs_e_facts]. unfold afact_ok, cs_spF, cs_SBF, cs_PF, cs_NF. cbn [af_lo af_hi af_al2].
    rewrite Usp, E32u, E10u, E11u, E33u, E34u. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat split; try lia.
- unfold sh_ok, cs_SH. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + apply (cs_shent_ok E _ 10 c 0 16616 E32 E10u); try lia.
    * rewrite Z.add_0_r. exact (proj1 (proj2 (proj2 (proj2 HAC)))).
    * intros y Hy. apply HcBD. lia.
  + apply (cs_shent_ok E _ 11 mm 0 9236 E32 E11u); try lia.
    * rewrite Z.add_0_r. exact (proj1 (proj2 (proj2 (proj2 HAM)))).
    * intros y Hy. apply HmBD. lia.
Qed.

Lemma cs_entry :
  (forall r m d, cs_loop 0 r m d -> SRr SEGS W (mkCfg (mkst r (Z_to_bv 64 (BASE + CS_LOOP)) m (seg_rom SEGS)) d) cs_Q) ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_check_segments) regs mem md) cs_Q.
Proof using TL HPRE H10 H11 H12 HC16 HRC HHC HAC HM16 HRM HHM HAM HCS.
intros LOOPK.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof cs_sp as (Hal16 & Hslo & Hshi). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HST : STK_check_segments_B = 8272) by reflexivity.
destruct cs_n as (Ln & Ov & Hret & L32).
destruct (cs_blk c _ HHC ltac:(unfold seg_spec.SEG_C_SIZE; lia)) as (Hc4 & Hcc & HcBD & _).
destruct (cs_blk mm _ HHM ltac:(unfold seg_spec.SEG_M_SIZE; lia)) as (Hm4 & Hmc & HmBD & _).
unfold seg_spec.SEG_C_SIZE, seg_spec.SEG_M_SIZE in Hcc, Hmc, HcBD, HmBD.
destruct cs_entry_seed as [HS SHOK].
pose proof (ajournal_init SEGS B STK_check_segments_B [] ly S W regs mem md ch HPRE) as HJ.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs cs_e_extra))) by apply Eimg_env.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (Eimg (Ereg regs cs_e_extra)) n = getr regs r)
  by (intros n r Hn; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j v, nth_error [SB; Z.of_nat (length (rc_seg rcs)); Z.of_nat (length (mc_seg mcs)); rc_overflow rcs; mc_overflow mcs] j = Some v ->
  ew (Eimg (Ereg regs cs_e_extra)) (32 + j) = w64 v).
{ intros j v Hj. assert (Hj5 : (j < 5)%nat) by (change 5%nat with (length [SB; Z.of_nat (length (rc_seg rcs)); Z.of_nat (length (mc_seg mcs)); rc_overflow rcs; mc_overflow mcs]); apply (proj1 (nth_error_Some _ j)); rewrite Hj; discriminate).
  unfold cs_e_extra. rewrite cs_ex_w64 by (cbn; unfold A_TEXT; lia). f_equal. apply nth_error_nth. exact Hj. }
pose proof (EX 0%nat _ eq_refl) as E32. pose proof (EX 1%nat _ eq_refl) as E33. pose proof (EX 2%nat _ eq_refl) as E34.
pose proof (EX 3%nat _ eq_refl) as E35. pose proof (EX 4%nat _ eq_refl) as E36.
cbn [Nat.add] in E32, E33, E34, E35, E36. clear EX.
remember (Eimg (Ereg regs cs_e_extra)) as E eqn:HE. clear HE.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (E10u : bv_unsigned (ew E 10) = c) by (rewrite (EE 10%nat 10%bv eq_refl), H10; apply unsigned_lit_small; lia).
assert (E11u : bv_unsigned (ew E 11) = mm) by (rewrite (EE 11%nat 11%bv eq_refl), H11; apply unsigned_lit_small; lia).
assert (E12 : ew E 12 = w64 1) by (rewrite (EE 12%nat 12%bv eq_refl), H12, Hret; reflexivity).
assert (E33u : bv_unsigned (ew E 33) = Z.of_nat (length (rc_seg rcs))) by (rewrite E33; apply unsigned_lit_small; lia).
assert (E34u : bv_unsigned (ew E 34) = Z.of_nat (length (mc_seg mcs))) by (rewrite E34; apply unsigned_lit_small; lia).
assert (FRM : forall H mem' cs, region_ok SEGS E (mrestrict H mem') (YP09.mkRegion (Some 2%nat) (-80) 0 (-80) 0 cs) ->
  (forall j r, nth_error cs_saved j = Some r -> In (YP09.mkChunk (-8 - 8 * Z.of_nat j) (CVal 8 (SOff (Z.to_nat r) 0))) cs) ->
  cs_frame (aview SEGS H mem')).
{ intros H mem' cs HR Hin j r Hr.
  assert (Hr' : 1 <= r <= 24) by (apply nth_error_In in Hr; cbn in Hr; intuition lia).
  replace (spZ regs - 8 - 8 * Z.of_nat j) with (spZ regs + (-8 - 8 * Z.of_nat j)) by lia.
  apply (cs_stack_field E H mem' cs _ (Z.to_nat r)); [exact HR | exact Usp | exact (Hin j r Hr) | |
    pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as HRr; change (bv_modulus 64) with (2 ^ 64) in HRr; exact HRr].
  rewrite (EE (Z.to_nat r) (Z_to_bv 5 r)); [unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. lia. }
(* the cut at a later state (the frame read at 0x86fe4, the memory unchanged since) *)
assert (CUT : forall regs2 mem1 mem2 md2,
  ajournal SEGS B STK_check_segments_B (spZ regs) [] ly S W mem md [] ly S W mem2 md2 0 ->
  kept_out (rdW W mem) (rdW W mem1) (spZ regs - STK_check_segments_B) (spZ regs) -> cs_frame (rdW W mem1) ->
  kept_out (rdW W mem1) (rdW W mem2) (spZ regs - STK_check_segments_B) (spZ regs - STK_check_segments_B) ->
  getr regs2 2 = Z_to_bv 64 (bv_unsigned (ew E 2) + -80) ->
  (forall k, In k cs_untouched -> getr regs2 (Z_to_bv 5 k) = ew E (Z.to_nat k)) ->
  getr regs2 8 = ew E 12 ->
  cs_cut regs2 mem2 md2).
{ intros regs2 mem1 mem2 md2 HJ2 HK1 HF1 HK2 Q2 QU Q8.
  split; [exact HJ2|]. split; [apply (kept_out_trans _ _ _ _ _ _ _ HK1 HK2); lia|].
  split.
  { intros j r Hr. assert (Hj : (j < 10)%nat) by (change 10%nat with (length cs_saved); apply (proj1 (nth_error_Some cs_saved j)); rewrite Hr; discriminate).
    apply (cs_val_keep _ _ _ _ _ _ _ HK2 (HF1 j r Hr)); lia. }
  split; [rewrite Q2, Usp; unfold w64; f_equal; lia|].
  split; [|rewrite Q8; exact E12].
  intros k Hk. rewrite QU by exact Hk. apply EE. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32.
  assert (0 <= k < 32) by (cbv [cs_untouched In] in Hk; lia). rewrite Z.mod_small by lia. lia. }
unfold cfg_at. change (w64 (BASE + AF_check_segments)) with (Z_to_bv 64 (BASE + AF_check_segments)).
(* 0x86f58 .. 0x86fe0: the frame (ra, s0 .. s8), s1 := c, UBSan's `andi a0,a0,7` / `bnez a0` (0x86f88, 0x86f8c:
   folded to 0 by c's alignment fact, so the trap 0x870a0 is not taken), s0 := returned, s2 := m, the shadow base,
   the check of c + 0x2c80, UBSan's `andi a0,s2,3` / `bnez a0` (0x86fc0, 0x86fc4: 0 by m's alignment fact), the
   check of m + 0x2000, a3 := c->n; stops at m->n, which needs m's region *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac; exact Usp. }
cs_md.
cs_kept_win HFr KEEP0 (spZ regs - STK_check_segments_B) (spZ regs) Usp. clear HF HFr HG.
lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
  let r := eval vm_compute in (nth 0 (ss_mem ssx) (stack_region 0)) in
  pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 0 r HS ltac:(vm_compute; reflexivity)) as HRg;
  cbn [ms_mem restrict] in HRg end.
assert (HF1 : cs_frame (rdW W (ms_mem ms))).
{ apply (FRM _ _ _ HRg). intros j r Hr. do 10 (destruct j as [|j]; [cbn in Hr; injection Hr as <-; vm_compute; repeat first [left; reflexivity | right] |]).
  cbn in Hr; destruct j; discriminate Hr. }
clear HRg.
rename ms into ms1.
pose proof (cs_swap_ok E _ _ cs_mreg HS eq_refl (cs_mreg_ok E (ms_mem ms1) KEEP0 E11u E34 E36)) as HS'. clear HS. rename HS' into HS.
(* 0x86fe4 .. 0x86fe8: m->n, bne a3,a1 *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac; exact Usp. }
cs_md.
cs_kept_empty HFr KEEP1 (spZ regs - STK_check_segments_B) (spZ regs - STK_check_segments_B). clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* c->n <> m->n: the abort arm 0x870a4; refuted by the premise's equal counts *)
  exfalso. rewrite branch_ne_U in Hc. apply negb_true_iff, Z.eqb_neq in Hc. apply Hc.
  unfold U. cbn [sv_denot]. rewrite E33, E34, Ln. reflexivity.
- clear Hc.
  pose proof (kept_out_trans _ _ _ _ _ _ _ KEEP0 KEEP1 ltac:(lia) ltac:(lia)) as K01.
  pose proof (cs_swap_ok E _ _ cs_creg HS eq_refl (cs_creg_ok E _ K01 E10u E33 E35)) as HS'. clear HS. rename HS' into HS.
  (* 0x86fec .. 0x87018: the checks of c + 0x34d0 and m + 0x2004, a1 := c->overflow; stops at m->overflow *)
  paj_run_tok RUN HS HJ SHOK Bspan.
  { awr_ok_tac; exact Usp. }
  cs_md.
  cs_kept_empty HFr KEEP2 (spZ regs - STK_check_segments_B) (spZ regs - STK_check_segments_B). clear HF HFr HG.
  pose proof (kept_out_trans _ _ _ _ _ _ _ K01 KEEP2 ltac:(lia) ltac:(lia)) as K02.
  pose proof (cs_swap_ok E _ _ cs_mreg HS eq_refl (cs_mreg_ok E _ K02 E11u E34 E36)) as HS'. clear HS. rename HS' into HS.
  (* 0x8701c .. 0x87020: m->overflow, bne a1,a0 *)
  paj_run_tok RUN HS HJ SHOK Bspan.
  { awr_ok_tac; exact Usp. }
  cs_md.
  cs_kept_empty HFr KEEP3 (spZ regs - STK_check_segments_B) (spZ regs - STK_check_segments_B). clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* c->overflow <> m->overflow: the abort arm; refuted by the premise's equal overflows *)
    exfalso. rewrite branch_ne_U in Hc. apply negb_true_iff, Z.eqb_neq in Hc. apply Hc.
    unfold U. cbn [sv_denot]. rewrite E35, E36, Ov. reflexivity.
  + clear Hc.
    (* 0x87024: blez a3 *)
    paj_run_tok RUN HS HJ SHOK Bspan.
    { awr_ok_tac; exact Usp. }
    cs_md.
    cs_kept_empty HFr KEEP4 (spZ regs - STK_check_segments_B) (spZ regs - STK_check_segments_B). clear HF HFr HG.
    lazymatch type of KEEP4 with kept_out _ (aview _ _ ?mlast) _ _ =>
    assert (K14 : kept_out (rdW W (ms_mem ms1)) (rdW W mlast) (spZ regs - STK_check_segments_B) (spZ regs - STK_check_segments_B))
    by (apply (kept_out_trans _ _ _ _ _ _ _ (kept_out_trans _ _ _ _ _ _ _ (kept_out_trans _ _ _ _ _ _ _ KEEP1 KEEP2 ltac:(lia) ltac:(lia)) KEEP3 ltac:(lia) ltac:(lia)) KEEP4); lia) end.
    psrr_branch_tok RUN BR HS SHOK Bspan.
    * (* n <= 0: no segment; to the exit 0x8706c *)
      assert (H0 : length (mc_seg mcs) = 0%nat).
      { rewrite (cs_bge0 E 33 (Z.of_nat (length (rc_seg rcs))) E33) in Hc by lia. apply Z.leb_le in Hc. lia. }
      clear Hc.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan CS_EXIT.
      { awr_ok_tac; exact Usp. }
      cs_md.
      cs_kept_empty HFr KEEP5 (spZ regs - STK_check_segments_B) (spZ regs - STK_check_segments_B). clear HF HFr HG.
      pmkst HS.
      prreg HS (2%bv : bv 5) Q2. prreg HS (8%bv : bv 5) Q8.
      apply cs_exit. apply (CUT _ (ms_mem ms1) _ _ HJ KEEP0 HF1).
      { apply (kept_out_trans _ _ _ _ _ _ _ K14 KEEP5); lia. }
      { rewrite Q2. reflexivity. }
      { intros k Hk. cbv [cs_untouched In] in Hk.
        repeat (destruct Hk as [<- | Hk]; [lazymatch goal with |- getr _ (Z_to_bv 5 ?kk) = _ => prreg HS (Z_to_bv 5 kk : bv 5) QX; rewrite QX; reflexivity end |]); destruct Hk. }
      { rewrite Q8. reflexivity. }
    * (* n > 0: 0x87028 .. 0x8703c, the loop's registers (s3 := 0, s4 := 0, s5 := ~c, s6 := ~m, s7 := n << 8,
         s8 := 32); to the loop's head 0x87040 with i = 0 *)
      assert (H0 : (0 < length (mc_seg mcs))%nat).
      { rewrite (cs_bge0 E 33 (Z.of_nat (length (rc_seg rcs))) E33) in Hc by lia. apply Z.leb_gt in Hc. lia. }
      clear Hc.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan CS_LOOP.
      { awr_ok_tac; exact Usp. }
      cs_md.
      cs_kept_empty HFr KEEP5 (spZ regs - STK_check_segments_B) (spZ regs - STK_check_segments_B). clear HF HFr HG.
      pmkst HS.
      prreg HS (2%bv : bv 5) Q2. prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9.
      prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20.
      prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23.
      prreg HS (24%bv : bv 5) Q24.
      apply LOOPK. split; [|split; [exact H0|]].
      { apply (CUT _ (ms_mem ms1) _ _ HJ KEEP0 HF1).
        - apply (kept_out_trans _ _ _ _ _ _ _ K14 KEEP5); lia.
        - rewrite Q2. reflexivity.
        - intros k Hk. cbv [cs_untouched In] in Hk.
          repeat (destruct Hk as [<- | Hk]; [lazymatch goal with |- getr _ (Z_to_bv 5 ?kk) = _ => prreg HS (Z_to_bv 5 kk : bv 5) QX; rewrite QX; reflexivity end |]); destruct Hk.
        - rewrite Q8. reflexivity. }
      split; [rewrite Q9, (EE 10%nat 10%bv eq_refl), H10; reflexivity|].
      split; [rewrite Q18, (EE 11%nat 11%bv eq_refl), H11; reflexivity|].
      split; [rewrite Q19; unfold w64; f_equal; lia|].
      split; [rewrite Q20; unfold w64; f_equal; lia|].
      split; [rewrite Q21, (EE 10%nat 10%bv eq_refl), H10; unfold w64; apply cs_not_w; [lia | reflexivity]|].
      split; [rewrite Q22, (EE 11%nat 11%bv eq_refl), H11; unfold w64; apply cs_not_w; [lia | reflexivity]|].
      split; [rewrite Q23, E33, Ln; unfold w64; apply cs_sll8_w; lia|].
      rewrite Q24; unfold w64; f_equal; lia.
Qed.

End w.
End e.
End d.
End b.
