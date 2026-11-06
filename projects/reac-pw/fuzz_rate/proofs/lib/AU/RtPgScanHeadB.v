(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgScanHead.v at cdde2c4d95be for
   reac-pw/fuzz_rate's image A: role's pcs (C3 0x820c4, the memcpy return 0x820e4, the parse return 0x8210c, E
   0x8212c, MAL 0x823fc, T 0x82408) become rate's (0x828b8, 0x828dc, 0x8290c, E 0x82930, MAL 0x82c9c, A 0x82ca8);
   the registers are renamed as rate's code has them (pod s2 -> s6, &cell s6 -> s5 = &hz, flags & 1 s4 -> s3, the
   frame's shadow base s3 -> s4, the shadow offset s7 -> s2, len s8 -> s10, pp + 0x4d18 s10 -> s9); F is read from
   the cell R+0x78 (blocks A and C: a read-only region at R), the hz cell takes the 4-byte 0x5a5a5a5a, block B also
   stores pod into R+0x138 (a writable window of the region at R) and reloads the flags byte into s10; the memcpy call
   is lib/A/RtPgSteps.v rts_intrin_at (role's hd_memcpy dropped), the .rodata zone is [0x10000, 0x22000), the cut file
   is lib/A/RtPgSeg.v (rl_ -> rt_, e_ -> q_, the role cell -> rs_hz_at, the frame pattern at the exits rs_PZ), the
   entry-state and list lemmas come from lib/A/RtPgScanKit.v and the memory facts from lib/A/RtPgMem.v. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgScanHead.v at fa28558fbb17 for image B
   (fuzz_rate.asan-ubsan); image B's pcs (C3 0x82a30, the memcpy return 0x82a58, the parse return 0x82a80, E 0x82aac,
   MAL 0x82de0, A 0x82dec, the slow block 0x830c0) and runtime entries (memcpy 0x518b8, the parse 0x8474c with its five
   doubles); image B's registers (pod s9, &hz s5 = F + 0x2a0, the flags byte s7 read before the memcpy, flags & 1 s2,
   the frame's shadow base s3, the shadow offset s4, len s6, pp + 0x4d18 s8, rc s10) and cells (F from R+0x60, pp from
   R+0x168, the mask from R+0x148, pp + 0x4008 from R+0x8); the frame is class 4 (hz's granule 84, the pattern
   rsb_PB at the exits); pod is stored into R+0x178 in block C after the parse (block C's region at R has a write
   window, so its exits are read from the run's final state); the cut file is lib/AU/RtPgSegB.v and the kit, model
   facts, memory and step layers are lib/AU's RtPgScanKitB.v, RtPgScanFB.v, RtPgMemB.v and RtPgStepsB.v. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; every address measured on the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1, same loaded bytes): the head of the checking
   segment M02 of LLVMFuzzerTestOneInput, lib/AU/RtPgSegB.v rsb_piece_W11a_head_stmt. Proves no function (kind:
   segment lemma).

   THE CODE (C3 0x82a30 to E 0x82aac, MAL 0x82de0 and A 0x82dec; fuzz.h:73-78, fuzz_rate.c:248-250)
     0x82a30  beqz a0,0x8308c      the second block is not NULL: decided by a0's atom fact (pod >= 4096)
     0x82a34  mv s9,a0; ld a0,0x60(s1) (F, from the cell R+0x60); addi s5,a0,0x2a0 (&hz = F + 0x2a0)
     0x82a40  ld s7,0x50(s1)       the flags byte, before the call (callee-saved s7 keeps it)
     0x82a44  beqz s6,0x82a58      len = 0: decided by s6's atom fact (8 <= len <= 5440)
     0x82a48  a0 = pod, a1 = pp (the cell R+0x168), a2 = len; 0x82a54 jal __asan_memcpy (0x518b8)
     0x82a58  a0 = 4, a1 = 0x5a5a6000; 0x82a60 sb a0,0x54(s3) (hz's shadow byte := 0x04)
     0x82a64  s2 = flags & 1; a0 = 0x5a5a5a5a; 0x82a6c sw a0,0(s5) (hz := 0x5a5a5a5a)
     0x82a70  a0 = s2 - 1; a0 = a0 & s9 (NULL when bit 0 is set, else pod); a1 = s5; 0x82a7c jal the parse (0x8474c)
     0x82a80  srli / add s4 / lb: the shadow byte of pp->corrupt (an instrumented 4-byte check); 0x82a8c s10 = rc
     0x82a90  bnez a1 (the check's slow block 0x830c0): decided not taken, the granule of pp + 0x4d18 is usable
     0x82a94  lw a0,0(s8) (pp->corrupt); ld s6,0x148(s1) (the mask); 0x82a9c sd s9,0x178(s1) (pod into R+0x178)
     0x82aa0  bnez a0 -> A; 0x82aa4 ld a0,8(s1) (pp + 0x4008); 0x82aa8 bnez s2 -> MAL; else E.
   The walk is three engine runs (lib/Reusable: st_ok, aj_run_to / aj_run_tok) cut at the two calls: the memcpy is
   the runtime's __asan_memcpy (YG0d.aintrin_realizes, the Section hypothesis AMEMCPY), the parse is RtPgCSpec's
   rt_parse_specX at the parse's entry, its key literal "reac.cfg.rate" (0x21720) and its five doubles (the
   Section hypothesis PARSE). Every byte the head writes lies in the pod block, the callees' stack
   [R - T_SEG_STK, R), the hz cell [F + 0x2a0, F + 0x2a4), its shadow byte or the cell [R + 0x178, R + 0x180), all
   inside RtPgSegB.rsb_E2 or the callees' stack, so the segment's kept clause carries over. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout Accessors Spa.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Rate.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgImgB RtPgSegB RtPgMemB RtPgScanFB RtPgScanKitB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require RtPgStepsB.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* image B's loaded segments; an abbreviation, so every statement names the image module's own term *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

(* ============================== the code table ============================== *)
(* the 31 words 0x82a30 .. 0x82aa8 (every run of the head leaves them at a call or at an exit) and the three words
   0x830c0 .. 0x830c8 of the slow block of the check at 0x82a90 (`andi`, `addi`, `blt` back to 0x82a94) *)
Definition HD_PC0 : Z := 0x82a30.
Definition HD_SLOW : Z := 0x830c0.
Definition hd_tbl : ctable := build_table rsegs HD_SLOW 3 (build_table rsegs HD_PC0 31 TEmpty).
Lemma hd_tbl_ok : table_ok rsegs hd_tbl.
Proof. apply build_table_ok; [unfold HD_SLOW; lia|]. apply build_table_ok0. unfold HD_PC0. lia. Qed.
Definition HD_MEMCPY : Z := 0x518b8.
Definition HD_AFTER_CPY : Z := 0x82a58.
Definition HD_PARSE : Z := 0x8474c.
Definition HD_AFTER_PARSE : Z := 0x82a80.
(* the shadow base of the last run: s4's own atom (x20); its one shadow entry is pp->corrupt's granule at s8 (x24) *)
Definition HDBx : sv := SOff 20 0.
Definition HDspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition HDSH : list shent := [mkSHE 24 0 8].
Definition HDCEIL_HI : Z := 0x7fffff800000.

#[local] Arguments x_STK {segs}. #[local] Arguments x_sp0 {segs}. #[local] Arguments x_FP {segs}.
#[local] Arguments x_ly {segs}. #[local] Arguments x_S {segs}. #[local] Arguments x_W0 {segs}.
#[local] Arguments x_mem0 {segs}. #[local] Arguments x_md0 {segs}. #[local] Arguments x_own {segs}.
#[local] Arguments x_k {segs}. #[local] Arguments x_regs {segs}. #[local] Arguments x_lyc {segs}.
#[local] Arguments x_Sc {segs}. #[local] Arguments x_W {segs}. #[local] Arguments x_memc {segs}.
#[local] Arguments x_mdc {segs}. #[local] Arguments x_RLO {segs}. #[local] Arguments x_RHI {segs}.
#[local] Arguments x_e {segs}. #[local] Arguments x_pos {segs}.

(* a byte a block or a frame holds is present *)
Lemma hd_aview_some : forall (H : word -> bool) (m : word -> option byte) a, apresent H m a -> aview rsegs H m a <> None.
Proof.
intros H m a [Hh [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate.
Qed.

Lemma hd_m32 : forall F, F mod 32 = 0 -> F = 8 * (F / 8) /\ F mod 8 = 0.
Proof.
intros F H. assert (H8 : F mod 8 = 0).
{ rewrite <- (Z.mod_mod_divide F 32 8) by (exists 4; reflexivity). rewrite H. reflexivity. }
pose proof (Z.div_mod F 8 ltac:(lia)). lia.
Qed.

(* `andi s2,s7,1` on the flags byte, and `addi a0,s2,-1; and a0,a0,s9`: NULL when bit 0 is set, else pod *)
Lemma hd_bit : forall fl, 0 <= fl < 2 ^ 64 -> zcanon (Z.land fl (zcanon 1)) = Z.b2z (Z.testbit fl 0).
Proof.
intros fl H. change (zcanon 1) with 1.
assert (E : Z.land fl 1 = fl mod 2) by (change 1 with (Z.ones 1); rewrite Z.land_ones by lia; reflexivity).
rewrite E, Zmod_odd, Z.bit0_odd. destruct (Z.odd fl); reflexivity.
Qed.
Lemma hd_sel : forall fl pod, 0 <= fl < 2 ^ 64 -> 0 <= pod < 2 ^ 64 ->
zcanon (Z.land (zcanon (zcanon (Z.land fl (zcanon 1)) + zcanon (-1))) pod) = if Z.testbit fl 0 then 0 else pod.
Proof.
intros fl pod Hf Hp. rewrite hd_bit by exact Hf. destruct (Z.testbit fl 0); cbn [Z.b2z].
- change (zcanon (1 + zcanon (-1))) with 0. rewrite Z.land_0_l. reflexivity.
- change (zcanon (0 + zcanon (-1))) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia.
  unfold zcanon, M64. rewrite Z.mod_mod by lia. apply Z.mod_small. lia.
Qed.

(* the .rodata range the parse's key string and its five doubles lie in, and its shadow bytes *)
Definition hd_szone (a : Z) : Prop :=
(0x10000 <= a < 0x22000) \/ (SHADOW_OFF + 0x2000 <= a < SHADOW_OFF + 0x4400).
Lemma hd_img_zone : forall a, 0x10000 <= a < 0x22000 -> in_img rsegs a.
Proof.
intros a Ha.
assert (H1 : existsb (fun s : Segment => (Z.of_N (seg_base s) <=? 0x10000) &&
  (0x22000 <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) rsegs = true) by (vm_compute; reflexivity).
apply existsb_exists in H1. destruct H1 as (sg & Hin & Hb).
apply andb_prop in Hb. destruct Hb as [Hb1 Hb2]. apply Z.leb_le in Hb1. apply Z.leb_le in Hb2.
exists sg. split; [exact Hin | lia].
Qed.
(* a string of that range whose bytes and shadow bytes read the same in another world and memory is the same string
   there *)
Lemma hd_cstr_kept : forall H H' (m m' : word -> option byte) a s,
(forall x, hd_szone x -> aview rsegs H' m' x = aview rsegs H m x) ->
0x10000 <= a -> a + Z.of_nat (length s) < 0x22000 ->
rt_cstr rsegs H m a s -> rt_cstr rsegs H' m' a s.
Proof.
intros H H' m m' a s HK Ha Hb (Hc & Hn & Hf & Ha0 & Hhi & Himg & Ham & Hra & Hhv).
assert (Kx : forall x, 0x10000 <= x < 0x22000 -> aview rsegs H' m' x = aview rsegs H m x)
by (intros x Hx; apply HK; left; exact Hx).
assert (Ks : forall x, 0x10000 <= x < 0x22000 ->
  aview rsegs H' m' (shadow_of_addr SHADOW_OFF x) = aview rsegs H m (shadow_of_addr SHADOW_OFF x)).
{ intros x Hx. apply HK. right. unfold shadow_of_addr.
  assert (0x2000 <= x / 8 < 0x4400) by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
  lia. }
split; [intros i Hi; rewrite Kx by lia; exact (Hc i Hi)|].
split; [rewrite Kx by lia; exact Hn|].
split; [exact Hf|]. split; [exact Ha0|]. split; [exact Hhi|]. split; [exact Himg|]. split; [exact Ham|].
split.
- intros x Hx. destruct (Hra x Hx) as (sv & Hsv & Hok). exists sv. split; [|exact Hok]. rewrite Ks by lia. exact Hsv.
- intros t Ht. rewrite (HK t); [exact (Hhv t Ht)|]. right.
  unfold shadow_addr, SHADOW_OFF in Ht |- *.
  replace (a + (Z.of_nat (length s) + 1) - 1) with (a + Z.of_nat (length s)) in Ht by lia.
  assert (L1 : 0x2000 <= a / 8) by (apply Z.div_le_lower_bound; lia).
  assert (L2 : (a + Z.of_nat (length s)) / 8 <= 0x43ff) by (apply Z.lt_succ_r; apply Z.div_lt_upper_bound; lia).
  assert (L3 : (0x7fff8000 + 0x2000) / 8 <= (0x7fff8000 + a / 8) / 8) by (apply Z.div_le_mono; lia).
  assert (L4 : (0x7fff8000 + (a + Z.of_nat (length s)) / 8) / 8 <= (0x7fff8000 + 0x43ff) / 8)
  by (apply Z.div_le_mono; lia).
  change ((0x7fff8000 + 0x2000) / 8) with 268432384 in L3.
  change ((0x7fff8000 + 0x43ff) / 8) with 268433535 in L4.
  lia.
Qed.

(* ============================== the bytes the head writes ============================== *)
Definition hdZ (cx : rsb_scx rsegs) (a : Z) : Prop :=
(q_pod (x_e cx) <= a < q_pod (x_e cx) + q_len (x_e cx)) \/ (q_R (x_e cx) - T_SEG_STK <= a < q_R (x_e cx)) \/
a = shadow_addr (q_F (x_e cx)) + 0x54 \/ (q_F (x_e cx) + 0x2a0 <= a < q_F (x_e cx) + 0x2a4) \/
(q_R (x_e cx) + 0x178 <= a < q_R (x_e cx) + 0x180).

Lemma hdZ_E2 : forall cx a, hdZ cx a -> (q_R (x_e cx) - T_SEG_STK <= a < q_R (x_e cx)) \/ rsb_E2 rsegs cx a.
Proof.
intros cx a [H|[H|[H|[H|H]]]].
- right. right. exact H.
- left. exact H.
- right. left. unfold rt_inw. cbn [hi_w2 rate_himg_B].
  apply Exists_cons_tl. apply Exists_cons_hd. cbn [rt_xv fst snd]. lia.
- right. left. unfold rt_inw. cbn [hi_w2 rate_himg_B]. apply Exists_cons_hd. cbn [rt_xv fst snd]. lia.
- right. left. unfold rt_inw. cbn [hi_w2 rate_himg_B].
  do 4 apply Exists_cons_tl. apply Exists_cons_hd. cbn [rt_xv fst snd]. lia.
Qed.

(* the cut lists of A and MAL are sub-lists of this one; E's is this one with a0 = pp + 0x4008 added *)
Definition hd_L (cx : rsb_scx rsegs) (rec : pod_rec) : list (rt_loc * Z) :=
rsb_L_chk rsegs cx ++ [(LReg 26, snd (rsb_PA rsegs cx rec)); (LReg 22, q_mask (x_e cx)); (LReg 23, q_fl (x_e cx));
                       (LCell XR 0x60, q_F (x_e cx));
                       (LCell XR 0xf8, Z.shiftr (q_pp (x_e cx) + 0x4d14) 3);
                       (LCell XR 0x138, q_pp (x_e cx) + 0x4d14); (LCell XR 0x168, q_pp (x_e cx));
                       (LCell XR 0x120, -0x3ffd)].

(* the entry states of blocks A, B and C: the regions they read and write *)
Definition hd_rA : YP09.region := YP09.mkRegion (Some 9%nat) 0x50 0x170 0 0
  [YP09.mkChunk 0x50 (CVal 8 (SOff 33 0)); YP09.mkChunk 0x60 (CVal 8 (SOff 32 0));
   YP09.mkChunk 0x168 (CVal 8 (SOff 34 0))].
Definition hd_rB0 : YP09.region := YP09.mkRegion (Some 19%nat) 0x54 0x55 0x54 0x55 [].
Definition hd_rB2 : YP09.region := YP09.mkRegion (Some 21%nat) 0 4 0 4 [].
Definition hd_rC (c : Z) : YP09.region := YP09.mkRegion (Some 24%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SLit c))].
Definition hd_rC2 : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x8 0x180 0x178 0x180
    [YP09.mkChunk 0x8 (CVal 8 (SOff 33 0)); YP09.mkChunk 0x148 (CVal 8 (SOff 32 0))].
(* s1 = R carries its stack range as an atom fact: the token engine's shadow loads need the write window
   [R + 0x178, R + 0x180) of hd_rC2 apart from the shadow span HDspan *)
Definition hd_factsC : facts :=
  mkFacts [(9%nat, mkAF 0x7fff7f804000 0x800000000000 0); (20%nat, mkAF 0x7fff8000 0x7fff8000 0);
           (24%nat, mkAF 4096 HDCEIL_HI 3)] [] [].

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* the entry state of the last run at 0x82a80: the registers as atoms with the overrides ov, pp->corrupt's 4 bytes
   at s8 as the closed value c, the mask (the extra atom 32) in the cell R+0x148, pp + 0x4008 (the extra atom 33) in
   the cell R+0x8, the cell R+0x178 writable, s1 = R, s4 = the shadow offset and s8 = pp + 0x4d18 as atom facts *)
Lemma hd_C_entry : forall (fx' : YK11.FPState) (W2 : world rsegs) regs2 mem2 (ov : list (bv 5 * sv)) c pp R mask,
Forall (fun p => fst p <> 0%bv /\
  sv_denot (Ereg regs2 [w64 mask; w64 (pp + 0x4008)]) (snd p) = getr regs2 (fst p)) ov ->
getr regs2 (Z_to_bv 5 24) = w64 (pp + 0x4d18) -> getr regs2 (Z_to_bv 5 20) = w64 SHADOW_OFF ->
getr regs2 (Z_to_bv 5 9) = w64 R ->
4096 <= pp + 0x4d18 <= HDCEIL_HI -> pp mod 16 = 0 -> 0 <= c < 2 ^ 32 ->
pp + 0x4d1c <= R -> 0x7fff7f804000 <= R <= 0x800000000000 -> 0 <= mask < 2 ^ 64 ->
(forall o, 0x178 <= o < 0x180 -> apresent (w_H W2) mem2 (R + o)) ->
val_mem rsegs (mrestrict (w_H W2) mem2) (pp + 0x4d18) 4 c ->
val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0x8) 8 (pp + 0x4008) ->
val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0x148) 8 mask ->
@st_ok rsegs fx' (Ereg regs2 [w64 mask; w64 (pp + 0x4008)])
  (mkSS 0x82a80 (skb_sr ov) [hd_rC c; hd_rC2] None hd_factsC)
  (restrict (w_H W2) (@mkst fx' regs2 (Z_to_bv 64 0x82a80) mem2 (seg_rom rsegs))).
Proof.
intros fx' W2 regs2 mem2 ov c pp R mask Hov H24 H20 H9 Hpp Hpp16 Hc HppR HR Hmask Hpres Hv Hv8 Hv148.
assert (E24 : bv_unsigned (ew (Ereg regs2 [w64 mask; w64 (pp + 0x4008)]) 24) = pp + 0x4d18).
{ rewrite (ew_Ereg_nat regs2 _ 24 (Z_to_bv 5 24) eq_refl), H24. unfold w64. apply unsigned_lit_small.
  unfold HDCEIL_HI in Hpp. lia. }
assert (E20 : bv_unsigned (ew (Ereg regs2 [w64 mask; w64 (pp + 0x4008)]) 20) = SHADOW_OFF).
{ rewrite (ew_Ereg_nat regs2 _ 20 (Z_to_bv 5 20) eq_refl), H20. unfold w64. apply unsigned_lit_small.
  unfold SHADOW_OFF. lia. }
assert (E9 : bv_unsigned (ew (Ereg regs2 [w64 mask; w64 (pp + 0x4008)]) 9) = R).
{ rewrite (ew_Ereg_nat regs2 _ 9 (Z_to_bv 5 9) eq_refl), H9. unfold w64. apply unsigned_lit_small.
  unfold HDCEIL_HI in Hpp. lia. }
assert (E32 : ew (Ereg regs2 [w64 mask; w64 (pp + 0x4008)]) 32 = Z_to_bv 64 mask)
  by (change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E33 : ew (Ereg regs2 [w64 mask; w64 (pp + 0x4008)]) 33 = Z_to_bv 64 (pp + 0x4008))
  by (change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; reflexivity).
rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
- apply skb_regs_ok. exact Hov.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + unfold hd_rC. apply (rtmb_ro_region rsegs _ (w_H W2) mem2 24 (pp + 0x4d18) 0 4);
      [exact E24 | lia | unfold HDCEIL_HI in Hpp; lia |].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val rsegs _ _ (pp + 0x4d18) 0 4 (SLit c) c); [reflexivity | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact Hv.
  + unfold hd_rC2. apply (rtmb_rw_region rsegs _ (w_H W2) mem2 9 R 0x8 0x180 0x178 0x180); [exact E9 | lia | lia | exact Hpres |].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    * apply (chunk_ok_val rsegs _ _ R 0x8 8 (SOff 33 0) (pp + 0x4008)).
      -- cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E33.
      -- cbn. unfold HDCEIL_HI in Hpp. lia.
      -- cbn. lia.
      -- exact Hv8.
    * apply (chunk_ok_val rsegs _ _ R 0x148 8 (SOff 32 0) mask).
      -- cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E32.
      -- cbn. lia.
      -- cbn. lia.
      -- exact Hv148.
- cbn [pairwise_disjoint all_disjoint hd_rC hd_rC2 extent_disjoint YP09.r_base YP09.r_lo YP09.r_hi base_val].
  unfold extent_disjoint, hd_rC, hd_rC2. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite E24, E9. unfold HDCEIL_HI in Hpp. repeat split; lia.
- unfold facts_ok, hd_factsC. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. unfold afact_ok.
  cbn [af_lo af_hi af_al2]. rewrite E24, E20, E9. unfold SHADOW_OFF, HDCEIL_HI in *.
  change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
  assert (H8p : pp mod 8 = 0)
    by (rewrite <- (Z.mod_mod_divide pp 16 8) by (exists 2; reflexivity); rewrite Hpp16; reflexivity).
  assert (H8 : (pp + 0x4d18) mod 8 = 0) by (rewrite Zplus_mod, H8p; reflexivity).
  repeat split; lia.
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
(* the runtime's __asan_memcpy (YG0d.AsanAPI's aa_asan_memcpy at image B's checked_memcpy entry 0x518b8, the target
   of the `jal` at 0x82a54) *)
Hypothesis AMEMCPY : aintrin_realizes rsegs B OCpy 0x518b8.
(* the parse's contract (RtPgCSpec.rt_parse_specX at the parse's entry 0x8474c, the target of the `jal` at 0x82a7c,
   its key literal .str.8 "reac.cfg.rate" at 0x21720 and its five doubles, the first five cells of rate_B_cells) *)
Hypothesis PARSE : rt_parse_specX rsegs B MT 0x8474c 0x21720
  [(0x10388, 0x3fe0000000000000); (0x103f0, 0xc1e0000000000000); (0x10338, 0x41e0000000000000);
   (0x10400, 0xc3e0000000000001); (0x10360, 0x43e0000000000000)].

(* ================= the start state at C3 (rsb_start_M02), unfolded into the facts the walk uses ================= *)
Record hd_c3 (cx : rsb_scx rsegs) (inp : list byte) : Prop := HDC3 {
c3_J : ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
  (x_own cx) (x_lyc cx) (x_Sc cx) (x_W cx) (x_memc cx) (x_mdc cx) (x_k cx);
c3_ev : st_nev (x_S cx) + x_k cx <= EV_MAX;
c3_r2 : getr (x_regs cx) 2 = w64 (q_R (x_e cx));
c3_r3 : getr (x_regs cx) 3 = w64 (as_gp B);
c3_r4 : getr (x_regs cx) 4 = w64 (as_tp B);
c3_S : q_S (x_e cx) = x_sp0 cx;
c3_R16 : q_R (x_e cx) mod 16 = 0;
c3_RS : q_R (x_e cx) + 0x220 <= q_S (x_e cx);
c3_STK : x_sp0 cx - x_STK cx <= q_R (x_e cx) - T_SEG_STK;
c3_own : In (4, x_pos cx) (x_own cx);
c3_F : q_F (x_e cx) = frame_addr (x_lyc cx) 4 (x_pos cx);
c3_ppin : In (q_pp (x_e cx), Layout.PP_SIZE) (ablocks B (x_lyc cx) (x_Sc cx));
c3_hdr : rt_hdr_ok (x_e cx);
c3_strs : Forall (fun s => rt_cstr rsegs (w_H (x_W cx)) (x_memc cx) (fst s) (snd s)) rate_B_strs;
c3_cells : rt_ro_cells rsegs (w_H (x_W cx)) (x_memc cx) rate_B_cells;
c3_rom : rom_view rsegs (x_W cx) (x_memc cx);
c3_ppnew : ~ In (q_pp (x_e cx), Layout.PP_SIZE) (ablocks B (x_ly cx) (x_S cx));
c3_fsh : rt_fsh rsegs (w_H (x_W cx)) (x_memc cx) (q_F (x_e cx)) rate_B_shA;
c3_a0 : getr (x_regs cx) (Z_to_bv 5 10) = w64 (q_pod (x_e cx));
c3_s0 : getr (x_regs cx) (Z_to_bv 5 8) = w64 (q_S (x_e cx));
c3_s1 : getr (x_regs cx) (Z_to_bv 5 9) = w64 (q_R (x_e cx));
c3_s3 : getr (x_regs cx) (Z_to_bv 5 19) = w64 (shadow_addr (q_F (x_e cx)));
c3_s4 : getr (x_regs cx) (Z_to_bv 5 20) = w64 SHADOW_OFF;
c3_s6 : getr (x_regs cx) (Z_to_bv 5 22) = w64 (q_len (x_e cx));
c3_s8 : getr (x_regs cx) (Z_to_bv 5 24) = w64 (q_pp (x_e cx) + 0x4d18);
c3_c8 : val_mem rsegs (mrestrict (w_H (x_W cx)) (x_memc cx)) (q_R (x_e cx) + 0x8) 8
  ((q_pp (x_e cx) + 0x4008) mod 2 ^ 64);
c3_c10 : val_mem rsegs (mrestrict (w_H (x_W cx)) (x_memc cx)) (q_R (x_e cx) + 0x10) 8 (q_F (x_e cx) mod 2 ^ 64);
c3_c18 : val_mem rsegs (mrestrict (w_H (x_W cx)) (x_memc cx)) (q_R (x_e cx) + 0x18) 8 (q_buflen (x_e cx) mod 2 ^ 64);
c3_c30 : val_mem rsegs (mrestrict (w_H (x_W cx)) (x_memc cx)) (q_R (x_e cx) + 0x30) 8
  (Z.shiftl (q_b6 (x_e cx)) 8 mod 2 ^ 64);
c3_c38 : val_mem rsegs (mrestrict (w_H (x_W cx)) (x_memc cx)) (q_R (x_e cx) + 0x38) 8 (q_b5 (x_e cx) mod 2 ^ 64);
c3_c40 : val_mem rsegs (mrestrict (w_H (x_W cx)) (x_memc cx)) (q_R (x_e cx) + 0x40) 8
  (Z.shiftl (q_b4 (x_e cx)) 8 mod 2 ^ 64);
c3_c48 : val_mem rsegs (mrestrict (w_H (x_W cx)) (x_memc cx)) (q_R (x_e cx) + 0x48) 8 (q_b3 (x_e cx) mod 2 ^ 64);
c3_c50 : val_mem rsegs (mrestrict (w_H (x_W cx)) (x_memc cx)) (q_R (x_e cx) + 0x50) 8 (q_fl (x_e cx) mod 2 ^ 64);
c3_c60 : val_mem rsegs (mrestrict (w_H (x_W cx)) (x_memc cx)) (q_R (x_e cx) + 0x60) 8 (q_F (x_e cx) mod 2 ^ 64);
c3_cf8 : val_mem rsegs (mrestrict (w_H (x_W cx)) (x_memc cx)) (q_R (x_e cx) + 0xf8) 8
  (Z.shiftr (q_pp (x_e cx) + 0x4d14) 3 mod 2 ^ 64);
c3_c120 : val_mem rsegs (mrestrict (w_H (x_W cx)) (x_memc cx)) (q_R (x_e cx) + 0x120) 8 (-0x3ffd mod 2 ^ 64);
c3_c138 : val_mem rsegs (mrestrict (w_H (x_W cx)) (x_memc cx)) (q_R (x_e cx) + 0x138) 8
  ((q_pp (x_e cx) + 0x4d14) mod 2 ^ 64);
c3_c148 : val_mem rsegs (mrestrict (w_H (x_W cx)) (x_memc cx)) (q_R (x_e cx) + 0x148) 8 (q_mask (x_e cx) mod 2 ^ 64);
c3_c168 : val_mem rsegs (mrestrict (w_H (x_W cx)) (x_memc cx)) (q_R (x_e cx) + 0x168) 8
  ((q_pp (x_e cx) + 0) mod 2 ^ 64);
c3_len : q_len (x_e cx) = rt_len inp;
c3_pp : rsb_pp_at rsegs cx (x_W cx) (x_memc cx) (pp_bytes (fst (pod_build inp)));
c3_pod0 : q_pod (x_e cx) <> 0;
c3_podin : In (q_pod (x_e cx), q_len (x_e cx)) (ablocks B (x_lyc cx) (x_Sc cx));
c3_podnew : ~ In (q_pod (x_e cx), q_len (x_e cx)) (ablocks B (x_ly cx) (x_S cx));
c3_frm : YK0o.frm_zero (@fp_csr fx) }.

Lemma hd_c3_of : forall cx inp, rsb_start_M02 rsegs B cx inp -> hd_c3 cx inp.
Proof.
intros cx inp (HP & Hfsh & HL3 & Hlen & Hpp & Hpod0 & Hpodin & Hpodnew & Hfrm).
destruct HP as (HJ & Hev & H2 & H3 & H4 & HeS & HR16 & HRS & HSTK & Hown & HeF & _ & Hppin & Hhdr & _ & _ & _ &
  Hstrs & Hcells & Hrom & Hppnew & _ & _).
unfold rt_cut in HL3. cbn [hi_L3 rate_himg_B] in HL3. unfold rate_B_L23, rate_B_L23_tl in HL3.
repeat rewrite Forall_cons_iff in HL3.
destruct HL3 as (A10 & A8 & A9 & A19 & A20 & A22 & A24 & C8 & C10 & C18 & C30 & C38 & C40 & C48 & C50 & C60 &
  Cf8 & C120 & C138 & C148 & C168 & _).
cbn [fst snd rt_at rt_xv] in A10, A8, A9, A19, A20, A22, A24.
cbn [hi_cid hi_rsz hi_shA hi_strs hi_cells rate_himg_B] in *.
constructor; assumption.
Qed.

(* the bounds the walk uses, from C3's journal and the allocator's block and frame laws *)
Lemma hd_bounds : forall cx inp, hd_c3 cx inp ->
let e := x_e cx in
q_pp e mod 16 = 0 /\ 4096 <= q_pp e /\ q_pp e + Layout.PP_SIZE <= alloc_ceiling /\ in_app (q_pp e) Layout.PP_SIZE /\
q_pod e mod 16 = 0 /\ 4096 <= q_pod e /\ q_pod e + q_len e <= alloc_ceiling /\ in_app (q_pod e) (q_len e) /\
8 <= q_len e <= 5440 /\
q_F e mod 32 = 0 /\ 4096 <= q_F e /\ q_F e + 1024 <= alloc_ceiling /\ in_app (q_F e) 1024 /\
alloc_ceiling + T_SEG_STK <= q_R e /\ q_R e + 0x220 <= x_sp0 cx /\ x_sp0 cx <= 2 ^ 47 /\ x_sp0 cx mod 16 = 0 /\
x_sp0 cx - x_STK cx <= q_R e - T_SEG_STK /\ 0x7fff7f800000 <= alloc_ceiling <= HDCEIL_HI.
Proof.
intros cx inp HC e. pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof (c3_J cx inp HC) as HJ.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR (c3_ppin cx inp HC)) as (Hm16 & H4096 & Hpc & Happ & _).
pose proof (RtPgCSpec.rt_len_bounds inp) as Hlb. rewrite <- (c3_len cx inp HC) in Hlb.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR (c3_podin cx inp HC)) as (Qm16 & Q4096 & Qpc & Qapp & _).
assert (Hfin : In (4, x_pos cx) (frames (x_Sc cx))) by (rewrite Hfrs; apply in_or_app; left; exact (c3_own cx inp HC)).
destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR Hfin) as (Fm32 & Fapp & _).
destruct (frames_bounds rsegs B LAWS _ _ _ _ _ _ _ HAR Hfin) as (F4096 & Fc & _).
pose proof asan_consts as ((Ca1 & Ca2) & _).
replace (fs_frame_bytes 4) with 1024 in Fapp, Fc by reflexivity.
rewrite <- (c3_F cx inp HC) in Fm32, Fapp, F4096, Fc.
pose proof (c3_RS cx inp HC) as HRS. pose proof (c3_S cx inp HC) as HS. pose proof (c3_STK cx inp HC) as HSTK.
replace (req_size Layout.PP_SIZE) with Layout.PP_SIZE in Hpc, Happ by reflexivity.
replace (req_size (q_len (x_e cx))) with (q_len (x_e cx)) in Qpc, Qapp
  by (unfold req_size; destruct (Z.eqb_spec (q_len (x_e cx)) 0); lia).
unfold HDCEIL_HI, T_SEG_STK, ASTACK in *. subst e. rewrite HS in HRS.
repeat (first [assumption | split]); unfold Layout.PP_SIZE in *; lia.
Qed.

(* none of the frame for locals, the second block or the first block is in the image *)
Lemma hd_imgs : forall cx inp, hd_c3 cx inp ->
(forall a, q_F (x_e cx) <= a < q_F (x_e cx) + 1024 -> ~ in_img rsegs a) /\
(forall a, q_pod (x_e cx) <= a < q_pod (x_e cx) + q_len (x_e cx) -> ~ in_img rsegs a) /\
(forall a, q_pp (x_e cx) <= a < q_pp (x_e cx) + Layout.PP_SIZE -> ~ in_img rsegs a).
Proof.
intros cx inp HC. pose proof (AR_laws_ok rsegs B) as LAWS. pose proof (c3_J cx inp HC) as HJ.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hfin : In (4, x_pos cx) (frames (x_Sc cx))) by (rewrite Hfrs; apply in_or_app; left; exact (c3_own cx inp HC)).
split; [|split]; intros a Ha; refine (proj2 (al_client_img _ _ LAWS _ _ _ _ _ a HAR _)).
- right. left. exists 4, (x_pos cx). split; [exact Hfin|]. rewrite <- (c3_F cx inp HC).
  change (fs_frame_bytes 4) with 1024. exact Ha.
- left. exists (q_pod (x_e cx)), (q_len (x_e cx)). split; [exact (c3_podin cx inp HC)|].
  unfold req_size. destruct (Z.eqb_spec (q_len (x_e cx)) 0); lia.
- left. exists (q_pp (x_e cx)), Layout.PP_SIZE. split; [exact (c3_ppin cx inp HC)|].
  unfold req_size, Layout.PP_SIZE in *. cbn. lia.
Qed.

(* no byte of the .rodata range or of its shadow is written by the head *)
Lemma hd_szone_ok : forall cx inp, hd_c3 cx inp -> forall a, hd_szone a -> 0 <= a < 2 ^ 64 /\ ~ hdZ cx a.
Proof.
intros cx inp HC a Ha.
pose proof (hd_bounds cx inp HC) as (Pm16 & P4096 & Pc & Papp & Qm16 & Q4096 & Qc & Qapp & Hlen8 &
  Fm32 & F4096 & Fc & Fapp & HRlo & HRS & H47 & Hs16 & HSTK & Hceil).
pose proof (hd_imgs cx inp HC) as (Fimg & Qimg & Pimg).
destruct (hd_m32 _ Fm32) as (F8 & _).
set (F := q_F (x_e cx)) in *. set (pod := q_pod (x_e cx)) in *. set (len := q_len (x_e cx)) in *.
set (R := q_R (x_e cx)) in *.
unfold hd_szone, SHADOW_OFF in Ha. unfold hdZ. fold F pod len R.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Fapp, Qapp.
unfold HDCEIL_HI, T_SEG_STK, ASTACK in *.
assert (Hfq : 0 <= F / 8) by (apply Z.div_pos; lia).
split; [lia|]. intros [H|[H|[H|[H|H]]]].
- destruct Ha as [Ha|Ha]; [exact (Qimg a H (hd_img_zone a Ha)) | lia].
- lia.
- unfold shadow_addr, SHADOW_OFF in H. destruct Ha as [Ha|Ha]; [lia|].
  apply (Fimg (F + 0x2a0)); [lia|]. apply hd_img_zone. lia.
- destruct Ha as [Ha|Ha]; [exact (Fimg a ltac:(lia) (hd_img_zone a Ha)) | lia].
- lia.
Qed.

(* none of the real frame's cells below R+0x178, the first block or the image is written by the head *)
Lemma hd_nz : forall cx inp, hd_c3 cx inp ->
(forall a, q_R (x_e cx) <= a < q_R (x_e cx) + 0x178 -> ~ hdZ cx a) /\
(forall a, q_pp (x_e cx) <= a < q_pp (x_e cx) + Layout.PP_SIZE -> ~ hdZ cx a) /\
(forall a, in_img rsegs a -> ~ hdZ cx a).
Proof.
intros cx inp HC.
pose proof (hd_bounds cx inp HC) as (Pm16 & P4096 & Pc & Papp & Qm16 & Q4096 & Qc & Qapp & Hlen8 &
  Fm32 & F4096 & Fc & Fapp & HRlo & HRS & H47 & Hs16 & HSTK & Hceil).
pose proof (hd_imgs cx inp HC) as (Fimg & Qimg & Pimg).
destruct (hd_m32 _ Fm32) as (F8 & _).
pose proof (AR_laws_ok rsegs B) as LAWS. pose proof (c3_J cx inp HC) as HJ.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hfin : In (4, x_pos cx) (frames (x_Sc cx))) by (rewrite Hfrs; apply in_or_app; left; exact (c3_own cx inp HC)).
assert (Hne : (q_pod (x_e cx), q_len (x_e cx)) <> (q_pp (x_e cx), Layout.PP_SIZE))
  by (intros Heq; injection Heq as _ Hl; unfold Layout.PP_SIZE in Hl; lia).
pose proof (sep_blocks rsegs B LAWS _ _ _ _ _ _ _ _ _ HAR (c3_podin cx inp HC) (c3_ppin cx inp HC) Hne) as Hpq.
pose proof (sep_block_frame rsegs B LAWS _ _ _ _ _ _ _ _ _ HAR (c3_ppin cx inp HC) Hfin) as Hpf.
unfold zdisjoint in Hpq, Hpf. cbn [fst snd] in Hpq, Hpf. rewrite <- (c3_F cx inp HC) in Hpf.
change (fs_frame_bytes 4) with 1024 in Hpf.
replace (req_size (q_len (x_e cx))) with (q_len (x_e cx)) in Hpq
  by (unfold req_size; destruct (Z.eqb_spec (q_len (x_e cx)) 0); lia).
change (req_size Layout.PP_SIZE) with 19744 in Hpq, Hpf. change Layout.PP_SIZE with 19744 in *.
set (F := q_F (x_e cx)) in *. set (pod := q_pod (x_e cx)) in *. set (len := q_len (x_e cx)) in *.
set (R := q_R (x_e cx)) in *. set (pp := q_pp (x_e cx)) in *.
unfold hdZ. fold F pod len R.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Fapp, Qapp, Papp.
unfold HDCEIL_HI, T_SEG_STK, ASTACK in *. unfold shadow_addr, SHADOW_OFF.
assert (Hfq : 0 <= F / 8) by (apply Z.div_pos; lia).
split; [|split].
- intros a Ha [H|[H|[H|[H|H]]]]; lia.
- intros a Ha [H|[H|[H|[H|H]]]]; lia.
- intros a Ha. pose proof (RtPgStepsB.rtsb_segs_low a Ha) as Hl. unfold kLowMemEnd in Hl.
  intros [H|[H|[H|[H|H]]]]; [exact (Qimg a H Ha) | lia | lia | exact (Fimg a ltac:(lia) Ha) | lia].
Qed.

(* ===================== block A: 0x82a30 .. the memcpy's return 0x82a58 ===================== *)
(* what C3 becomes after the memcpy: the pod block holds pp's first len bytes, every byte outside the pod block and
   the callee's stack [R - ESTACK, R) is as at C3, s9 = pod, s5 = F + 0x2a0, s7 = the flags byte and the other
   callee-saved registers their C3 values *)
Definition hd_A_post (cx : rsb_scx rsegs) (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
  (x_own cx) (x_lyc cx) (x_Sc cx) (x_W cx) mem1 md1 (x_k cx) /\
same_io (x_mdc cx) md1 /\
(forall r, In r [2; 3; 4; 8; 9; 19; 20; 24] ->
 getr regs1 (Z_to_bv 5 r) = getr (x_regs cx) (Z_to_bv 5 r)) /\
getr regs1 (Z_to_bv 5 25) = w64 (q_pod (x_e cx)) /\
getr regs1 (Z_to_bv 5 21) = w64 (q_F (x_e cx) + 0x2a0) /\
getr regs1 (Z_to_bv 5 23) = w64 (q_fl (x_e cx)) /\
(forall i, 0 <= i < q_len (x_e cx) -> aview rsegs (w_H (x_W cx)) mem1 (q_pod (x_e cx) + i) =
  aview rsegs (w_H (x_W cx)) (x_memc cx) (q_pp (x_e cx) + i)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (q_pod (x_e cx) <= a < q_pod (x_e cx) + q_len (x_e cx)) ->
 ~ (q_R (x_e cx) - ESTACK <= a < q_R (x_e cx)) ->
 aview rsegs (w_H (x_W cx)) mem1 a = aview rsegs (w_H (x_W cx)) (x_memc cx) a).

Lemma hd_A : forall cx inp (Q : world rsegs -> config -> Prop),
hd_c3 cx inp ->
(forall regs1 mem1 md1, hd_A_post cx regs1 mem1 md1 -> SRr rsegs (x_W cx) (cfg_at rsegs HD_AFTER_CPY regs1 mem1 md1) Q) ->
SRr rsegs (x_W cx) (cfg_at rsegs (hi_c3 rate_himg_B) (x_regs cx) (x_memc cx) (x_mdc cx)) Q.
Proof using AMEMCPY.
intros cx inp Q HC K.
pose proof (hd_bounds cx inp HC) as (Pm16 & P4096 & Pc & Papp & Qm16 & Q4096 & Qc & Qapp & Hlen8 &
  Fm32 & F4096 & Fc & Fapp & HRlo & HRS & H47 & Hs16 & HSTK & Hceil).
destruct HC as [HJ Hev H2 H3 H4 HeS HR16 _ _ Hown HeF Hppin Hhdr Hstrs Hcells Hrom Hppnew Hfsh
  A10 A8 A9 A19 A20 A22 A24 C8 C10 C18 C30 C38 C40 C48 C50 C60 Cf8 C120 C138 C148 C168
  Hlen Hpp Hpod0 Hpodin Hpodnew Hfrm].
destruct cx as [STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc RLO RHI e pos]; cbn in *.
set (pp := q_pp e) in *. set (pod := q_pod e) in *. set (len := q_len e) in *. set (R := q_R e) in *.
set (F := q_F e) in *. set (fl := q_fl e) in *.
assert (Hfl : 0 <= fl < 256) by exact (proj1 Hhdr).
unfold HDCEIL_HI, T_SEG_STK, ASTACK in Hceil, HRlo, HSTK. change Layout.PP_SIZE with 19744 in Pc.
pose proof (AR_laws_ok rsegs B) as LAWS. pose proof RtPgStepsB.rtsb_wx as Hwx.
pose proof RtPgStepsB.rtsb_segs_low as Hsegs.
assert (E32 : ew (Ereg regs [w64 F; w64 fl; w64 pp]) 32 = Z_to_bv 64 F)
  by (change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E33 : ew (Ereg regs [w64 F; w64 fl; w64 pp]) 33 = Z_to_bv 64 fl)
  by (change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E34 : ew (Ereg regs [w64 F; w64 fl; w64 pp]) 34 = Z_to_bv 64 pp)
  by (change 34%nat with (32 + 2)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E9 : bv_unsigned (ew (Ereg regs [w64 F; w64 fl; w64 pp]) 9) = R).
{ rewrite (ew_Ereg_nat regs _ 9 (Z_to_bv 5 9) eq_refl), A9. unfold w64. apply unsigned_lit_small. lia. }
assert (HS : st_ok rsegs (Ereg regs [w64 F; w64 fl; w64 pp]) (mkSS 0x82a30 sr_atoms [hd_rA] None
  (mkFacts [(10%nat, mkAF 4096 HDCEIL_HI 4); (22%nat, mkAF 8 5440 0)] [] []))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 0x82a30) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold hd_rA.
    apply (rtmb_ro_region rsegs _ (w_H W) memc 9 R 0x50 0x170 _ E9); [lia | lia |].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    + apply (chunk_ok_val rsegs _ _ R 0x50 8 (SOff 33 0) fl).
      * cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E33.
      * cbn. lia.
      * cbn. lia.
      * rewrite (Z.mod_small fl) in C50 by lia. exact C50.
    + apply (chunk_ok_val rsegs _ _ R 0x60 8 (SOff 32 0) F).
      * cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E32.
      * cbn. lia.
      * cbn. lia.
      * rewrite (Z.mod_small F) in C60 by lia. exact C60.
    + apply (chunk_ok_val rsegs _ _ R 0x168 8 (SOff 34 0) pp).
      * cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E34.
      * cbn. lia.
      * cbn. lia.
      * rewrite Z.add_0_r, (Z.mod_small pp) in C168 by lia. exact C168.
  - cbn. tauto.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. split; [|split; [|exact I]]; unfold afact_ok; cbn [af_lo af_hi af_al2].
    + rewrite (ew_Ereg_nat regs _ 10 (Z_to_bv 5 10) eq_refl), A10. unfold w64.
      rewrite unsigned_lit_small by (unfold HDCEIL_HI; lia). change (2 ^ 4) with 16. unfold HDCEIL_HI. lia.
    + rewrite (ew_Ereg_nat regs _ 22 (Z_to_bv 5 22) eq_refl), A22. unfold w64.
      rewrite unsigned_lit_small by lia. change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia. }
unfold cfg_at. cbn [hi_c3 rate_himg_B]. change (w64 0x82a30) with (Z_to_bv 64 0x82a30).
aj_run_to hd_tbl_ok HS HJ HD_MEMCPY.
{ apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
assert (HAE : env_agree 32 (Ereg regs [w64 F; w64 fl; w64 pp]) (Ereg regs [w64 F; w64 fl; w64 pp]))
  by apply env_agree_refl.
lazymatch goal with HF : frame_of ?E0 ?rs0 _ (ms_mem ?ms) |- _ =>
  pose proof (frame_of_read_only E0 rs0 _ _ eq_refl HF) as Hmem end.
rewrite Hmem in HJ.
rreg HS (Z_to_bv 5 1) Ra1. rreg HS (Z_to_bv 5 10) Ra10. rreg HS (Z_to_bv 5 11) Ra11. rreg HS (Z_to_bv 5 12) Ra12.
rreg HS (Z_to_bv 5 25) Ra25.
assert (Ra21 : getr (ms_regs ms) (Z_to_bv 5 21) = w64 (F + 0x2a0)).
{ rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms _ HS).
  lazymatch type of HS with st_ok _ _ ?ss _ => let v := eval vm_compute in (sr_get (ss_regs ss) (Z_to_bv 5 21)) in
    change (sr_get (ss_regs ss) (Z_to_bv 5 21)) with v end.
  rewrite (skb_soff _ 32 F 0x2a0 E32). reflexivity. }
assert (Ra23 : getr (ms_regs ms) (Z_to_bv 5 23) = w64 fl).
{ rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms _ HS).
  lazymatch type of HS with st_ok _ _ ?ss _ => let v := eval vm_compute in (sr_get (ss_regs ss) (Z_to_bv 5 23)) in
    change (sr_get (ss_regs ss) (Z_to_bv 5 23)) with v end.
  rewrite (skb_soff _ 33 fl 0 E33), Z.add_0_r. reflexivity. }
assert (Rk : forall r, In r [2; 3; 4; 8; 9; 19; 20; 24] ->
  getr (ms_regs ms) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr. exact (YI04.regs_kept_of_st_ok rsegs _ _ _ regs [w64 F; w64 fl; w64 pp]
    (map (Z_to_bv 5) [2; 3; 4; 8; 9; 19; 20; 24]) HS HAE ltac:(vm_compute; reflexivity)
    (Z_to_bv 5 r) (in_map _ _ _ Hr)). }
pose proof (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) as Ems. cbn [ss_pc] in Ems.
rewrite Ems, Hmem.
assert (HAR : AR rsegs B lyc Sc W memc (with_vm_backing (m_vm_lazy mdc) mat mdc)) by exact (proj1 HJ).
assert (E2 : getr (ms_regs ms) (2%bv : bv 5) = getr regs (2%bv : bv 5))
  by (eapply (skb_reg_atom _ _ ms (w_H W) regs _ _ HS HAE); vm_compute; reflexivity).
assert (E3 : getr (ms_regs ms) (3%bv : bv 5) = getr regs (3%bv : bv 5))
  by (eapply (skb_reg_atom _ _ ms (w_H W) regs _ _ HS HAE); vm_compute; reflexivity).
assert (E4 : getr (ms_regs ms) (4%bv : bv 5) = getr regs (4%bv : bv 5))
  by (eapply (skb_reg_atom _ _ ms (w_H W) regs _ _ HS HAE); vm_compute; reflexivity).
assert (Hsp : spZ (ms_regs ms) = sp0 + (R - sp0)).
{ unfold spZ. rewrite E2, H2. unfold w64. rewrite unsigned_lit_small; [ring | lia]. }
destruct (rtmb_blk_ra rsegs B lyc Sc W memc _ pod len pod len HAR Hpodin ltac:(lia)
  ltac:(unfold req_size; destruct (Z.eqb_spec len 0); lia)) as (Hrad & Hhd).
destruct (rtmb_blk_ra rsegs B lyc Sc W memc _ pp Layout.PP_SIZE pp len HAR Hppin ltac:(lia)
  ltac:(unfold req_size; cbn; unfold Layout.PP_SIZE; lia)) as (Hrax & Hhx).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hppin) as (_ & _ & _ & _ & Hpres_pp & _).
assert (Hne : (pod, len) <> (pp, Layout.PP_SIZE)) by (intros Heq; injection Heq as _ Hl; unfold Layout.PP_SIZE in Hl; lia).
pose proof (sep_blocks rsegs B LAWS _ _ _ _ _ _ _ _ _ HAR Hpodin Hppin Hne) as Hdj.
unfold zdisjoint in Hdj. cbn [fst snd] in Hdj.
replace (req_size len) with len in Hdj by (unfold req_size; destruct (Z.eqb_spec len 0); lia).
replace (req_size Layout.PP_SIZE) with Layout.PP_SIZE in Hdj by reflexivity.
eapply SRr_bind.
{ eapply (RtPgStepsB.rtsb_intrin_at B LAWS OCpy 0x518b8 AMEMCPY W (ms_regs ms) memc STK sp0 FP ly S W0 mem0 md0
    own lyc Sc _ k pod pp len (R - sp0) (Z_to_bv 64 0x82a58) HJ).
  - rewrite <- (skb_getr_z (ms_regs ms) 10 10 eq_refl), Ra10. exact A10.
  - rewrite <- (skb_getr_z (ms_regs ms) 11 11 eq_refl), Ra11. first [exact E34 | reflexivity].
  - rewrite <- (skb_getr_z (ms_regs ms) 12 12 eq_refl), Ra12. exact A22.
  - lia.
  - lia.
  - lia.
  - exact Hsp.
  - rewrite Zminus_mod, HR16, Hs16. reflexivity.
  - lia.
  - unfold ESTACK. lia.
  - rewrite E3. exact H3.
  - rewrite E4. exact H4.
  - rewrite <- (skb_getr_z (ms_regs ms) 1 1 eq_refl). exact Ra1.
  - vm_compute. reflexivity.
  - intros a Ha. split.
    + replace a with (pod + (a - pod)) by lia.
      apply (rt_fresh_awr_n STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own pod len Hpodin Hpodnew); lia.
    + unfold ESTACK. lia.
  - eapply amem_range_of_block; [exact LAWS | exact HAR | exact Hpodin | lia | unfold req_size; destruct (Z.eqb_spec len 0); lia].
  - exact Hrad.
  - exact Hhd.
  - split; [lia|]. split; [lia|]. split.
    { intros a Ha. split.
      + apply hd_aview_some. exact (proj1 (Hpres_pp a ltac:(unfold req_size, Layout.PP_SIZE in *; cbn; lia))).
      + rewrite Hsp. unfold ESTACK. lia. }
    split; [change Layout.PP_SIZE with 19744 in Hdj; lia|].
    split; [eapply amem_range_of_block; [exact LAWS | exact HAR | exact Hppin | lia | unfold req_size, Layout.PP_SIZE; cbn; lia]|].
    split; [exact Hrax | exact Hhx]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & Hpres2 & Hsame & Ha02 & Hcpy & Hkeep).
apply K.
split; [exact HJ2|].
split; [eapply same_io_trans; [apply RtPgStepsB.same_io_wvb | exact (same_io_materialized _ _ Hsame)]|].
split.
{ intros r Hr. rewrite (Hpres2 r) by (cbn [In] in Hr; unfold acallee_saved; lia). apply Rk. exact Hr. }
split.
{ rewrite (Hpres2 25) by (unfold acallee_saved; lia). rewrite Ra25. exact A10. }
split.
{ rewrite (Hpres2 21) by (unfold acallee_saved; lia). exact Ra21. }
split.
{ rewrite (Hpres2 23) by (unfold acallee_saved; lia). exact Ra23. }
split.
{ intros i Hi. exact (Hcpy i Hi). }
intros a Ha Hnp Hns. apply Hkeep; [exact Ha | exact Hnp |]. replace (sp0 + (R - sp0)) with R by lia. exact Hns.
Qed.

(* ===================== block B: 0x82a58 .. the parse's return 0x82a80 ===================== *)
(* what C3 becomes when the parse returns (at its float state fx2): the parse's post, s2 = bit 0 of the flags byte,
   s5 = F + 0x2a0, s7 = the flags byte, s9 = pod, a0 = the parse's answer, every byte outside hdZ as at C3, the
   frame's shadow with hz's granule in scope and the hz cell *)
Definition hd_B_post (cx : rsb_scx rsegs) (inp : list byte) (fx2 : YK11.FPState) ly2 S2 (W2 : world rsegs)
(regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) : Prop :=
rt_fxk [13; 14; 15] fx fx2 /\
ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
  (x_own cx) ly2 S2 W2 mem2 md2 (x_k cx) /\
frames S2 = frames (x_Sc cx) /\ Permutation (ablocks B ly2 S2) (ablocks B (x_lyc cx) (x_Sc cx)) /\
same_io (x_mdc cx) md2 /\ mo_le MT (x_Sc cx) S2 0 /\
(forall r, In r [2; 3; 4; 8; 9; 19; 20; 24] ->
 getr regs2 (Z_to_bv 5 r) = getr (x_regs cx) (Z_to_bv 5 r)) /\
getr regs2 (Z_to_bv 5 18) = w64 (Z.b2z (Z.testbit (q_fl (x_e cx)) 0)) /\
getr regs2 (Z_to_bv 5 21) = w64 (q_F (x_e cx) + 0x2a0) /\
getr regs2 (Z_to_bv 5 23) = w64 (q_fl (x_e cx)) /\
getr regs2 (Z_to_bv 5 25) = w64 (q_pod (x_e cx)) /\
getr regs2 (Z_to_bv 5 10) = w64 (snd (rsb_PA rsegs cx (fst (pod_build inp)))) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ hdZ cx a ->
 aview rsegs (w_H W2) mem2 a = aview rsegs (w_H (x_W cx)) (x_memc cx) a) /\
rt_fsh rsegs (w_H W2) mem2 (q_F (x_e cx)) rsb_PB /\
rsb_hz_at rsegs cx (fst (pod_build inp)) W2 mem2.

Lemma hd_B : forall cx inp regs1 mem1 md1 (Q : world rsegs -> config -> Prop),
hd_c3 cx inp -> hd_A_post cx regs1 mem1 md1 ->
(forall (fx2 : YK11.FPState) ly2 S2 W2 regs2 mem2 md2, hd_B_post cx inp fx2 ly2 S2 W2 regs2 mem2 md2 ->
 SRr rsegs W2 (@cfg_at fx2 rsegs HD_AFTER_PARSE regs2 mem2 md2) Q) ->
SRr rsegs (x_W cx) (cfg_at rsegs HD_AFTER_CPY regs1 mem1 md1) Q.
Proof using PARSE.
intros cx inp regs1 mem1 md1 Q HC HA K.
pose proof (hd_bounds cx inp HC) as (Pm16 & P4096 & Pc & Papp & Qm16 & Q4096 & Qc & Qapp & Hlen8 &
  Fm32 & F4096 & Fc & Fapp & HRlo & HRS & H47 & Hs16 & HSTK & Hceil).
pose proof (hd_imgs cx inp HC) as (Fimg & Qimg & Pimg).
pose proof (hd_szone_ok cx inp HC) as Hsz.
destruct (hd_m32 _ Fm32) as (F8 & F8m).
pose proof (rkb_wf inp) as Hwf.
pose proof (Spa.buf_header _ Hwf) as (_ & _ & Hu32 & Hblen).
destruct HA as (HJ & Hio1 & Rk1 & R25 & R21 & R23 & Hcpy & Hkeep).
destruct HC as [_ Hev H2 H3 H4 HeS HR16 _ _ Hown HeF Hppin Hhdr Hstrs Hcells Hrom Hppnew Hfsh
  A10 A8 A9 A19 A20 A22 A24 C8 C10 C18 C30 C38 C40 C48 C50 C60 Cf8 C120 C138 C148 C168
  Hlen Hpp Hpod0 Hpodin Hpodnew Hfrm].
unfold rt_len in Hlen.
set (rec := fst (pod_build inp)) in *.
destruct cx as [STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc RLO RHI e pos]; cbn in *.
set (pp := q_pp e) in *. set (pod := q_pod e) in *. set (len := q_len e) in *. set (R := q_R e) in *.
set (F := q_F e) in *. set (fl := q_fl e) in *.
assert (Hfl : 0 <= fl < 256) by exact (proj1 Hhdr).
unfold HDCEIL_HI, T_SEG_STK, ASTACK in Hceil, HRlo, HSTK. change Layout.PP_SIZE with 19744 in Pc.
pose proof (AR_laws_ok rsegs B) as LAWS. pose proof RtPgStepsB.rtsb_wx as Hwx.
pose proof RtPgStepsB.rtsb_segs_low as Hsegs.
assert (Hfq : 0 <= F / 8) by (apply Z.div_pos; lia).
assert (HFa : F + 1024 <= 0x7fff7000 \/ 0x10007fff8000 <= F)
  by (unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Fapp; lia).
assert (HQa : pod + len <= 0x7fff7000 \/ 0x10007fff8000 <= pod)
  by (unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Qapp; lia).
(* the env of the run and the two bases *)
set (E := Ereg regs1 [w64 fl]).
assert (E19 : bv_unsigned (ew E 19) = shadow_addr F).
{ subst E. rewrite (ew_Ereg_nat regs1 _ 19 (Z_to_bv 5 19) eq_refl), (Rk1 19 ltac:(cbn; tauto)).
  refine (eq_trans (f_equal (@bv_unsigned 64) A19) _). unfold w64. apply unsigned_lit_small.
  unfold shadow_addr, SHADOW_OFF. lia. }
assert (E21 : bv_unsigned (ew E 21) = F + 0x2a0).
{ subst E. rewrite (ew_Ereg_nat regs1 _ 21 (Z_to_bv 5 21) eq_refl), R21. unfold w64. apply unsigned_lit_small. lia. }
assert (E23 : ew E 23 = Z_to_bv 64 fl) by (subst E; rewrite (ew_Ereg_nat regs1 _ 23 (Z_to_bv 5 23) eq_refl); exact R23).
assert (E25 : ew E 25 = Z_to_bv 64 pod) by (subst E; rewrite (ew_Ereg_nat regs1 _ 25 (Z_to_bv 5 25) eq_refl); exact R25).
(* the frame's bytes and shadow bytes are present *)
assert (HAR1 : AR rsegs B lyc Sc W mem1 md1) by exact (proj1 HJ).
assert (Hfin : In (4, pos) (frames Sc)).
{ pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _). rewrite Hfrs. apply in_or_app. left. exact Hown. }
destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR1 Hfin) as (_ & _ & Hfb & Hfs).
rewrite <- HeF in Hfb, Hfs. change (fs_frame_bytes 4 / 8) with 128 in Hfs. change (fs_frame_bytes 4) with 1024 in Hfb.
assert (HS : st_ok rsegs E (mkSS 0x82a58 sr_atoms [hd_rB0; hd_rB2] None (mkFacts [] [] []))
  (restrict (w_H W) (mkst regs1 (Z_to_bv 64 0x82a58) mem1 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold hd_rB0. apply (rtmb_rw_region rsegs E (w_H W) mem1 19 (shadow_addr F) 0x54 0x55 0x54 0x55 [] E19);
        [unfold shadow_addr, SHADOW_OFF; lia | unfold shadow_addr, SHADOW_OFF; lia | | apply Forall_nil].
      intros o Ho. exact (proj1 (Hfs o ltac:(lia))).
    + unfold hd_rB2. apply (rtmb_rw_region rsegs E (w_H W) mem1 21 (F + 0x2a0) 0 4 0 4 [] E21);
        [lia | lia | | apply Forall_nil].
      intros o Ho. exact (proj1 (Hfb (F + 0x2a0 + o) ltac:(lia))).
  - cbn [pairwise_disjoint all_disjoint hd_rB0 hd_rB2 extent_disjoint YP09.r_base YP09.r_lo YP09.r_hi base_val].
    unfold extent_disjoint, hd_rB0, hd_rB2. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    fold E. rewrite E19, E21. unfold shadow_addr, SHADOW_OFF. repeat split; lia.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. tauto. }
unfold cfg_at. change (w64 HD_AFTER_CPY) with (Z_to_bv 64 0x82a58).
aj_run_to hd_tbl_ok HS HJ HD_PARSE.
{ cbn [ss_mem].
  eapply (RtPgStepsB.rtsb_awr_ok_fsh _ _ _ _ _ _ _ _ _ _ 19%nat pos);
    [reflexivity | rewrite E19; f_equal; exact HeF | exact Hown | cbn; lia | cbn; lia |].
  eapply (RtPgStepsB.rtsb_awr_ok_fobj _ _ _ _ _ _ _ _ _ _ 21%nat pos 0x2a0);
    [reflexivity | rewrite E21; lia | exact Hown | cbn; lia | cbn; lia |].
  apply awr_ok_nil. }
assert (HAE : env_agree 32 (Ereg regs1 [w64 fl]) E) by (subst E; apply env_agree_refl).
(* the registers at the call *)
assert (Rb1 : getr (ms_regs ms) 1 = w64 HD_AFTER_PARSE).
{ rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms _ HS).
  lazymatch type of HS with st_ok _ _ ?ss _ => let v := eval vm_compute in (sr_get (ss_regs ss) (1%bv : bv 5)) in
    change (sr_get (ss_regs ss) (1%bv : bv 5)) with v end. reflexivity. }
assert (Rb10 : getr (ms_regs ms) 10 = w64 (if Z.testbit fl 0 then 0 else pod)).
{ rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms _ HS).
  lazymatch type of HS with st_ok _ _ ?ss _ => let v := eval vm_compute in (sr_get (ss_regs ss) (10%bv : bv 5)) in
    change (sr_get (ss_regs ss) (10%bv : bv 5)) with v end.
  rewrite denot_lit_U. unfold w64. f_equal.
  rewrite !U_SAlu, !U_SLit. cbn [zalu_raw].
  rewrite (U_atom E 23 fl E23 ltac:(lia)), (U_atom E 25 pod E25 ltac:(lia)).
  apply hd_sel; lia. }
assert (Rb18 : getr (ms_regs ms) 18 = w64 (Z.b2z (Z.testbit fl 0))).
{ rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms _ HS).
  lazymatch type of HS with st_ok _ _ ?ss _ => let v := eval vm_compute in (sr_get (ss_regs ss) (18%bv : bv 5)) in
    change (sr_get (ss_regs ss) (18%bv : bv 5)) with v end.
  rewrite denot_lit_U. unfold w64. f_equal.
  rewrite !U_SAlu, !U_SLit. cbn [zalu_raw].
  rewrite (U_atom E 23 fl E23 ltac:(lia)). apply hd_bit; lia. }
assert (Rb11 : getr (ms_regs ms) 11 = getr regs1 (Z_to_bv 5 21))
  by (eapply (skb_reg_is _ _ ms (w_H W) regs1 _ _ _ 21%nat HS HAE); [vm_compute; reflexivity | reflexivity]).
assert (Rkb : forall r, In r [2; 3; 4; 8; 9; 19; 20; 21; 23; 24; 25] ->
  getr (ms_regs ms) (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)).
{ intros r Hr. exact (YI04.regs_kept_of_st_ok rsegs _ _ _ regs1 [w64 fl]
    (map (Z_to_bv 5) [2; 3; 4; 8; 9; 19; 20; 21; 23; 24; 25]) HS HAE ltac:(vm_compute; reflexivity)
    (Z_to_bv 5 r) (in_map _ _ _ Hr)). }
assert (Rx : forall r, In r [2; 3; 4; 8; 9; 19; 20; 24] ->
  getr (ms_regs ms) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr. rewrite Rkb by (cbn [In] in Hr |- *; tauto). apply Rk1. cbn [In] in Hr |- *; tauto. }
assert (HspP : spZ (ms_regs ms) = R).
{ unfold spZ. rewrite <- (skb_getr_z (ms_regs ms) 2 2 eq_refl), (Rx 2 ltac:(cbn; tauto)), (skb_getr_z regs 2 2 eq_refl), H2.
  unfold w64. apply unsigned_lit_small. lia. }
(* the memory at the call: hz's shadow byte, hz, and every byte outside them as before *)
assert (Hsb : val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) (shadow_addr F + 0x54) 1 4).
{ lazymatch type of HS with st_ok _ _ ?ss _ =>
    let r := eval vm_compute in (nth_error (ss_mem ss) 0) in
    lazymatch r with Some ?rg =>
      assert (Hr : nth_error (ss_mem ss) 0 = Some rg) by (vm_compute; reflexivity);
      pose proof (RtPgStepsB.rtsb_region_nth _ _ _ 0 _ _ HS Hr) as Hreg end end.
  exact (skb_field_of_region _ _ _ _ _ _ _ _ _ 0x54 1 (SLit 4) 4 Hreg E19 ltac:(cbn; tauto) eq_refl
    ltac:(cbn; lia) ltac:(cbn; lia)). }
assert (Hrc : val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) (F + 0x2a0) 4 0x5a5a5a5a).
{ lazymatch type of HS with st_ok _ _ ?ss _ =>
    let r := eval vm_compute in (nth_error (ss_mem ss) 1) in
    lazymatch r with Some ?rg =>
      assert (Hr : nth_error (ss_mem ss) 1 = Some rg) by (vm_compute; reflexivity);
      pose proof (RtPgStepsB.rtsb_region_nth _ _ _ 1 _ _ HS Hr) as Hreg end end.
  pose proof (skb_field_of_region _ _ _ _ _ _ _ _ _ 0 4 (SLit 0x5a5a5a5a) 0x5a5a5a5a Hreg E21 ltac:(cbn; tauto) eq_refl
    ltac:(cbn; lia) ltac:(cbn; lia)) as Hv. rewrite Z.add_0_r in Hv. exact Hv. }
assert (KB : forall a, 0 <= a < 2 ^ 64 -> a <> shadow_addr F + 0x54 -> ~ (F + 0x2a0 <= a < F + 0x2a4) ->
  aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) mem1 a).
{ intros a Ha H1 H2'. unfold aview, mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
  rewrite unsigned_lit_small by exact Ha. intros (r & Hin & Hr). cbn [In] in Hin.
  destruct Hin as [<-|[<-|[]]]; cbn [hd_rB0 hd_rB2 YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
  [rewrite E19 in Hr | rewrite E21 in Hr]; lia. }
assert (KP : forall a, 0 <= a < 2 ^ 64 ->
  ~ hdZ (RSBCx rsegs STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc RLO RHI e pos) a ->
  aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) memc a).
{ intros a Ha Hz. unfold hdZ in Hz. cbn [x_e] in Hz. fold pod len R F in Hz.
  rewrite KB; [| exact Ha | intros ->; apply Hz; right; right; left; reflexivity
             | intros Hr; apply Hz; right; right; right; left; exact Hr].
  apply Hkeep; [exact Ha | intros Hp; apply Hz; left; exact Hp
               | intros Hs; apply Hz; right; left; unfold ESTACK in Hs; unfold T_SEG_STK, ASTACK; lia]. }
(* the frame's shadow at the call: the prologue's with hz's granule in scope *)
assert (Hfsh1 : rt_fsh rsegs (w_H W) mem1 F rate_B_shA).
{ apply (rtmb_fsh_kept rsegs (w_H W) memc (w_H W) mem1 F rate_B_shA Hfsh).
  intros i Hi. change (length rate_B_shA) with 88%nat in Hi. cbn in Hi.
  apply Hkeep; unfold shadow_addr, SHADOW_OFF; [lia | lia | unfold ESTACK; lia]. }
assert (HfshP : rt_fsh rsegs (w_H W) (ms_mem ms) F rsb_PB).
{ unfold rsb_PB. rewrite <- (rtmb_sh_hz_in false false false false false false false), rtmb_sh_P0.
  apply (rtmb_fsh_set rsegs (w_H W) mem1 (w_H W) (ms_mem ms) F rate_B_shA 84 1 4 Hfsh1).
  - intros i Hi. cbn in Hi. assert (i = 84) as -> by lia.
    apply (rtmb_val1_aview rsegs). exact Hsb. lia.
  - intros i Hi Hn. change (length rate_B_shA) with 88%nat in Hi. cbn in Hi, Hn.
    apply KB; unfold shadow_addr, SHADOW_OFF; lia. }
(* the second block holds the record's bytes *)
assert (Hbytes : rtmb_bytes rsegs (w_H W) (ms_mem ms) pod (buf rec)).
{ unfold rsb_pp_at, rsb_u8s in Hpp. fold (rtmb_bytes rsegs (w_H W) memc pp (pp_bytes rec)) in Hpp.
  unfold pp_bytes, pp_image in Hpp. apply rtmb_bytes_app in Hpp. destruct Hpp as (Hb & _).
  apply (rtmb_bytes_kept rsegs (w_H W) mem1).
  - apply (rtmb_memcpy_bytes rsegs (w_H W) memc (w_H W) mem1 pp pod (buf rec) Hb).
    intros i Hi. apply Hcpy. lia.
  - pose proof (sep_block_frame rsegs B LAWS _ _ _ _ _ _ _ _ _ HAR1 Hpodin Hfin) as Hsep.
    unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. rewrite <- HeF in Hsep. change (fs_frame_bytes 4) with 1024 in Hsep.
    replace (req_size len) with len in Hsep by (unfold req_size; destruct (Z.eqb_spec len 0); lia).
    intros x Hx. apply KB; [lia | unfold shadow_addr, SHADOW_OFF; lia | lia]. }
(* the parse's string and doubles *)
assert (KS : forall x, hd_szone x -> aview rsegs (w_H W) (ms_mem ms) x = aview rsegs (w_H W) memc x).
{ intros x Hx. destruct (Hsz x Hx) as [Hx64 Hnz]. exact (KP x Hx64 Hnz). }
assert (Hkey : rt_cstr rsegs (w_H W) (ms_mem ms) 0x21720 (map (fun x : byte => bv_unsigned x) Rate.RATE_KEY)).
{ rewrite rate_B_key_text. apply (hd_cstr_kept _ _ _ _ _ _ KS); [lia | cbn; lia |].
  rewrite Forall_forall in Hstrs. apply (Hstrs (0x21720, _)). unfold rate_B_strs. cbn [In].
  repeat (first [left; reflexivity | right]). }
assert (Hdcs : rt_ro_cells rsegs (w_H W) (ms_mem ms)
  [(0x10388, 0x3fe0000000000000); (0x103f0, 0xc1e0000000000000); (0x10338, 0x41e0000000000000);
   (0x10400, 0xc3e0000000000001); (0x10360, 0x43e0000000000000)]).
{ unfold rt_ro_cells in Hcells |- *. rewrite Forall_forall in Hcells.
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
  (eapply (val_mem_kept rsegs); [intros kk Hkk; apply KS; left; cbn in Hkk; lia |]);
  (refine (Hcells (_, _) _); unfold rate_B_cells; cbn [In]; repeat (first [left; reflexivity | right])). }
pose proof (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) as Ems. cbn [ss_pc] in Ems.
rewrite Ems.
destruct (rtmb_blk_ra rsegs B lyc Sc W (ms_mem ms) _ pod len pod len (proj1 HJ) Hpodin ltac:(lia)
  ltac:(unfold req_size; destruct (Z.eqb_spec len 0); lia)) as (Hrad & Hhd).
eapply SRr_bind.
{ apply (PARSE STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms) (with_vm_backing (m_vm_lazy md1) mat md1) k
    (ms_regs ms) (Z.testbit fl 0) pod (F + 0x2a0) (buf rec)).
  - unfold rt_cpre. split; [exact HJ|].
    split; [rewrite Rb1; vm_compute; reflexivity|].
    split; [unfold raZ; rewrite Rb1; unfold w64, HD_AFTER_PARSE; rewrite unsigned_lit_small; lia|].
    split; [rewrite <- (skb_getr_z (ms_regs ms) 3 3 eq_refl), (Rx 3 ltac:(cbn; tauto)), (skb_getr_z regs 3 3 eq_refl); exact H3|].
    split; [rewrite <- (skb_getr_z (ms_regs ms) 4 4 eq_refl), (Rx 4 ltac:(cbn; tauto)), (skb_getr_z regs 4 4 eq_refl); exact H4|].
    rewrite HspP. unfold T_parse_STK, ESTACK. split; [exact HR16|]. split; [lia|]. split; [lia | exact Hev].
  - exact Rb10.
  - rewrite Rb11, R21. reflexivity.
  - intros _. rewrite <- Hlen. split; [lia|]. split; [exact Qm16|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [exact Hbytes|]. split; [exact Hrad|]. split; [apply Hhd; lia|].
    split; [eapply amem_range_of_block; [exact LAWS | exact (proj1 HJ) | exact Hpodin | lia | unfold req_size; destruct (Z.eqb_spec len 0); lia]|].
    left. rewrite HspP. unfold T_parse_STK, ESTACK. lia.
  - unfold rt_wcell. split.
    + right. exists 4, pos. split; [exact Hown|]. split; [lia|]. rewrite <- HeF. change (fs_frame_bytes 4) with 1024. lia.
    + right. rewrite HspP. unfold T_parse_STK, ESTACK. lia.
  - lia.
  - rewrite F8. replace (8 * (F / 8) + 0x2a0) with ((2 * (F / 8) + 0xa8) * 4) by ring. apply Z.mod_mul. lia.
  - replace (F + 0x2a0) with (F + RTMB_HZ + 0) by (unfold RTMB_HZ; ring).
    apply (rtmb_B_ra_hz rsegs (w_H W) (ms_mem ms) F false false false false false false 0 4); [|exact F8m | lia | lia].
    exact HfshP.
  - exact Hkey.
  - exact Hdcs.
  - exact Hfrm. }
cbv beta. intros W2 c2 _ (fx2 & ly2 & S2 & regs2 & mem2 & md2 & -> & HFX & HJ2 & Hpres & Hfr2 & _ & Hperm & Hio2 & Hmo & Hkp & H10 & HRc).
rewrite Rb1. apply (K fx2 ly2 S2 W2 regs2 mem2 md2).
split; [exact HFX|].
split; [exact HJ2|].
split; [exact Hfr2|].
split; [exact Hperm|].
split; [eapply same_io_trans; [exact Hio1|]; eapply same_io_trans; [apply RtPgStepsB.same_io_wvb | exact Hio2]|].
split; [exact Hmo|].
split.
{ intros r Hr. rewrite (Hpres r) by (cbn [In] in Hr; unfold acallee_saved; lia). apply Rx. exact Hr. }
split.
{ rewrite (Hpres 18) by (unfold acallee_saved; lia). rewrite (skb_getr_z (ms_regs ms) 18 18 eq_refl). exact Rb18. }
split.
{ rewrite (Hpres 21) by (unfold acallee_saved; lia). rewrite Rkb by (cbn; tauto). exact R21. }
split.
{ rewrite (Hpres 23) by (unfold acallee_saved; lia). rewrite Rkb by (cbn; tauto). exact R23. }
split.
{ rewrite (Hpres 25) by (unfold acallee_saved; lia). rewrite Rkb by (cbn; tauto). exact R25. }
split.
{ rewrite (skb_getr_z regs2 10 10 eq_refl). exact H10. }
assert (KQ : forall a, 0 <= a < 2 ^ 64 -> ~ (R - T_parse_STK <= a < R) -> ~ (F + 0x2a0 <= a < F + 0x2a4) ->
  aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W) (ms_mem ms) a).
{ intros a Ha H1 H2'. apply Hkp; [exact Ha | rewrite HspP; exact H1 | intros (_ & Hq); apply H2'; lia]. }
split.
{ intros a Ha Hz. rewrite KQ; [| exact Ha | | ].
  - apply KP; [exact Ha | exact Hz].
  - intros Hs. apply Hz. right. left. cbn [x_e]. unfold T_parse_STK, ESTACK in Hs. unfold T_SEG_STK, ASTACK. lia.
  - intros Hr. apply Hz. right. right. right. left. exact Hr. }
split.
{ apply (rtmb_fsh_kept rsegs (w_H W) (ms_mem ms) (w_H W2) mem2 F rsb_PB HfshP).
  intros i Hi. change (length rsb_PB) with 88%nat in Hi. cbn in Hi.
  apply KQ; unfold shadow_addr, SHADOW_OFF, T_parse_STK, ESTACK; lia. }
unfold rsb_hz_at, rsb_hz, rsb_PA, Rate.written_or. cbn [x_e]. fold F fl rec.
destruct (fst (Rate.harness_parse (Z.testbit fl 0) (buf rec))) as [w|] eqn:Ef.
- first [exact HRc | rewrite Ef in HRc; exact HRc].
- change (0x5a5a5a5a mod 2 ^ 32) with 0x5a5a5a5a.
  eapply (val_mem_kept rsegs); [|exact Hrc].
  intros kk Hkk. cbn in Hkk. apply Hkp; [lia | rewrite HspP; unfold T_parse_STK, ESTACK; lia |].
  intros (Hn & _). apply Hn. first [exact Ef | reflexivity].
Qed.

(* ===================== the facts the three exits share ===================== *)
(* at an exit of the last run: rsb_chk_base, the list hd_L and the hz cell, at the run's final memory memF, which
   differs from the memory at the parse's return only in the cell [R + 0x178, R + 0x180) (pod, 0x82a9c) *)
Lemma hd_common : forall cx inp (fx2 : YK11.FPState) ly2 S2 W2 regs2 mem2 md2 regsF memF mdF,
hd_c3 cx inp -> hd_B_post cx inp fx2 ly2 S2 W2 regs2 mem2 md2 ->
ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
  (x_own cx) ly2 S2 W2 memF mdF (x_k cx) ->
same_io md2 mdF ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (q_R (x_e cx) + 0x178 <= a < q_R (x_e cx) + 0x180) ->
 aview rsegs (w_H W2) memF a = aview rsegs (w_H W2) mem2 a) ->
val_mem rsegs (mrestrict (w_H W2) memF) (q_R (x_e cx) + 0x178) 8 (q_pod (x_e cx) mod 2 ^ 64) ->
(forall r, In r [2; 3; 4; 8; 9; 19; 20; 21; 23] ->
 getr regsF (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r)) ->
getr regsF (Z_to_bv 5 26) = getr regs2 (Z_to_bv 5 10) ->
getr regsF (Z_to_bv 5 22) = w64 (q_mask (x_e cx)) ->
@rsb_chk_base fx rc SK rsegs B MT cx fx2 (fst (pod_build inp)) ly2 S2 W2 regsF memF mdF /\
rsb_at_cx rsegs cx W2 memF regsF (hd_L cx (fst (pod_build inp))) /\
rsb_hz_at rsegs cx (fst (pod_build inp)) W2 memF.
Proof.
intros cx inp fx2 ly2 S2 W2 regs2 mem2 md2 regsF memF mdF HC HBp HJF HioF KF H178 HrF H26 H22.
pose proof (hd_nz cx inp HC) as (NR & NP & NI).
pose proof (hd_bounds cx inp HC) as (Pm16 & P4096 & Pc & Papp & Qm16 & Q4096 & Qc & Qapp & Hlen8 &
  Fm32 & F4096 & Fc & Fapp & HRlo & HRS0 & H47 & Hs16 & HSTK0 & Hceil).
destruct (hd_m32 _ Fm32) as (F8 & _).
assert (Hfq : 0 <= q_F (x_e cx) / 8) by (apply Z.div_pos; lia).
pose proof (c3_S cx inp HC) as HS0.
unfold T_SEG_STK, ASTACK in HRlo. unfold HDCEIL_HI in Hceil.
pose proof (rkb_wf inp) as Hwf.
destruct HBp as (HFX & HJ2 & Hfr2 & Hperm & Hio2 & Hmo & Rk2 & R18 & R21 & R23 & R25 & R10 & K2 & Hfsh2 & Hhz2).
assert (Hx : forall r, In r [2; 3; 4; 8; 9; 19; 20] ->
  getr regsF (Z_to_bv 5 r) = getr (x_regs cx) (Z_to_bv 5 r)).
{ intros r Hr. rewrite HrF by (cbn [In] in Hr |- *; tauto). apply Rk2. cbn [In] in Hr |- *; tauto. }
assert (KZ : forall a, 0 <= a < 2 ^ 64 -> ~ hdZ cx a ->
  aview rsegs (w_H W2) memF a = aview rsegs (w_H (x_W cx)) (x_memc cx) a).
{ intros a Ha Hz. rewrite KF; [apply K2; [exact Ha | exact Hz] | exact Ha |].
  intros Hr. apply Hz. right. right. right. right. exact Hr. }
assert (KC : forall o v, 0 <= o -> o + 8 <= 0x178 ->
  val_mem rsegs (mrestrict (w_H (x_W cx)) (x_memc cx)) (q_R (x_e cx) + o) 8 v ->
  val_mem rsegs (mrestrict (w_H W2) memF) (q_R (x_e cx) + o) 8 v).
{ intros o v Ho Ho8 Hv. eapply (val_mem_kept rsegs); [|exact Hv]. intros kk Hkk. cbn in Hkk.
  apply KZ; [lia|]. apply NR. lia. }
destruct HC as [HJ Hev H2 H3 H4 HeS HR16 HRS HSTK Hown HeF Hppin Hhdr Hstrs Hcells Hrom Hppnew Hfsh
  A10 A8 A9 A19 A20 A22 A24 C8 C10 C18 C30 C38 C40 C48 C50 C60 Cf8 C120 C138 C148 C168
  Hlen Hpp Hpod0 Hpodin Hpodnew Hfrm].
unfold rt_len in Hlen.
split; [|split].
- split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]].
  + split; [exact HJF|].
    split; [intros r Hr; apply Hx; cbn [In]; lia|].
    split; [exact Hfr2|]. split; [exact Hperm|].
    split; [eapply same_io_trans; [exact Hio2 | exact HioF]|]. split; [exact Hmo|].
    intros a Ha Hs He. apply KZ; [exact Ha|]. intros Hz. destruct (hdZ_E2 cx a Hz) as [Hz'|Hz']; [|exact (He Hz')].
    apply Hs. unfold spZ. rewrite H2. unfold w64. rewrite unsigned_lit_small; [exact Hz'|]. lia.
  + destruct HFX as [HFk HFf]. split; [|exact HFf]. intros k0 Hk. apply HFk. intros Hin. apply Hk. right. exact Hin.
  + unfold rsb_fsh_at.
    apply (rtmb_fsh_kept rsegs (w_H W2) mem2 (w_H W2) memF (q_F (x_e cx)) rsb_PB Hfsh2).
    intros i Hi. change (length rsb_PB) with 88%nat in Hi. cbn in Hi.
    apply KF; unfold shadow_addr, SHADOW_OFF; lia.
  + intros a Ha.
    assert (Hia : in_img rsegs a) by (destruct Ha as (sg' & Hsg' & _ & Hr'); exists sg'; split; [exact Hsg' | exact Hr']).
    pose proof (RtPgStepsB.rtsb_segs_low a Hia) as Hl.
    rewrite <- (Hrom a Ha). apply KZ; [unfold kLowMemEnd in Hl; lia | exact (NI a Hia)].
  + unfold rsb_pp_at, rsb_u8s in Hpp |- *.
    fold (rtmb_bytes rsegs (w_H (x_W cx)) (x_memc cx) (q_pp (x_e cx)) (pp_bytes (fst (pod_build inp)))) in Hpp.
    fold (rtmb_bytes rsegs (w_H W2) memF (q_pp (x_e cx)) (pp_bytes (fst (pod_build inp)))).
    apply (rtmb_bytes_kept rsegs _ _ _ _ _ _ Hpp). intros x Hx'.
    assert (Hlp : Z.of_nat (length (pp_bytes (fst (pod_build inp)))) = Layout.PP_SIZE).
    { pose proof (Spa.buf_header _ Hwf) as (_ & _ & _ & Hbl).
      apply Layout.length_pp_image; [unfold Layout.POD_BUF_MAX; lia | exact (rkb_nent_le _ Hwf) |].
      pose proof (rkb_ents_wf _ Hwf) as Hew. rewrite Forall_forall in Hew |- *. intros x0 Hx0.
      destruct (Hew x0 Hx0) as (_ & Hb & Hs). rewrite Hb. lia. }
    rewrite Hlp in Hx'.
    apply KZ; [change Layout.PP_SIZE with 19744 in *; lia|]. apply NP. exact Hx'.
  + exact Hwf.
  + exact Hlen.
  + exact Hpod0.
  + exact Hpodin.
  + exact Hpodnew.
- unfold rsb_at_cx, rsb_at, hd_L, rsb_L_chk, rsb_Hc. cbn [app].
  repeat (apply Forall_cons; [cbn [fst snd rt_at rt_xv] |]); [..|apply Forall_nil].
  + rewrite Hx by (cbn; tauto). exact A8.
  + rewrite Hx by (cbn; tauto). exact A9.
  + rewrite Hx by (cbn; tauto). exact A19.
  + rewrite Hx by (cbn; tauto). exact A20.
  + exact H178.
  + rewrite HrF by (cbn; tauto). exact R21.
  + apply KC; [lia | lia | exact C10].
  + apply KC; [lia | lia | exact C50].
  + apply KC; [lia | lia | exact C48].
  + apply KC; [lia | lia | exact C30].
  + apply KC; [lia | lia | exact C38].
  + apply KC; [lia | lia | exact C40].
  + apply KC; [lia | lia | exact C18].
  + apply KC; [lia | lia | exact C148].
  + rewrite H26. exact R10.
  + exact H22.
  + rewrite HrF by (cbn; tauto). exact R23.
  + apply KC; [lia | lia | exact C60].
  + apply KC; [lia | lia | exact Cf8].
  + apply KC; [lia | lia | exact C138].
  + apply KC; [lia | lia | rewrite Z.add_0_r in C168; exact C168].
  + apply KC; [lia | lia | exact C120].
- unfold rsb_hz_at in Hhz2 |- *. eapply (val_mem_kept rsegs); [|exact Hhz2].
  intros kk Hkk. cbn in Hkk. apply KF; lia.
Qed.

(* at an exit of the last run: the state is written with its pc *)
Ltac hd_exit HS :=
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?m) =>
    let Ems := fresh "Ems" in
    pose proof (st_ok_restrict_mkst rsegs _ _ _ m HS eq_refl) as Ems; cbn [ss_pc] in Ems; rewrite Ems
  end.

(* ===================== block C: 0x82a80 .. E 0x82aac / MAL 0x82de0 / A 0x82dec ===================== *)
Lemma hd_C : forall cx inp POST (fx2 : YK11.FPState) ly2 S2 W2 regs2 mem2 md2,
hd_c3 cx inp -> hd_B_post cx inp fx2 ly2 S2 W2 regs2 mem2 md2 ->
@rsb_from_E fx rc SK rsegs B MT cx POST -> @rsb_from_MAL fx rc SK rsegs B MT cx POST ->
@rsb_from_A fx rc SK rsegs B MT cx POST ->
SRr rsegs W2 (@cfg_at fx2 rsegs HD_AFTER_PARSE regs2 mem2 md2) POST.
Proof.
intros cx inp POST fx2 ly2 S2 W2 regs2 mem2 md2 HC HBp HE HM HA.
pose proof (hd_bounds cx inp HC) as (Pm16 & P4096 & Pc & Papp & Qm16 & Q4096 & Qc & Qapp & Hlen8 &
  Fm32 & F4096 & Fc & Fapp & HRlo & HRS & H47 & Hs16 & HSTK & Hceil).
pose proof (hd_nz cx inp HC) as (NR & NP & NI).
pose proof (rkb_wf inp) as Hwf.
pose proof (Spa.buf_header _ Hwf) as (_ & _ & _ & Hblen).
pose proof HBp as (HFX & HJ2 & Hfr2 & Hperm & Hio2 & Hmo & Rk2 & R18 & R21 & R23 & R25 & R10 & K2 & Hfsh2 & Hhz2).
pose proof (AR_laws_ok rsegs B) as LAWS. pose proof RtPgStepsB.rtsb_wx as Hwx.
pose proof RtPgStepsB.rtsb_segs_low as Hsegs.
pose proof (c3_s8 cx inp HC) as S8. pose proof (c3_s4 cx inp HC) as S4r. pose proof (c3_s1 cx inp HC) as S1.
pose proof (c3_c8 cx inp HC) as C8. pose proof (c3_c148 cx inp HC) as C148.
pose proof (c3_pp cx inp HC) as Hpp. pose proof (c3_ppin cx inp HC) as Hppin.
pose proof (c3_hdr cx inp HC) as Hhdr.
set (rec := fst (pod_build inp)) in *.
set (pp := q_pp (x_e cx)) in *. set (fl := q_fl (x_e cx)) in *. set (F := q_F (x_e cx)) in *.
set (R := q_R (x_e cx)) in *. set (mask := q_mask (x_e cx)) in *. set (pod := q_pod (x_e cx)) in *.
assert (Hmk : 0 <= mask < 256) by exact (proj1 (proj2 Hhdr)).
unfold HDCEIL_HI, T_SEG_STK, ASTACK in Hceil, HRlo, HSTK. change Layout.PP_SIZE with 19744 in Pc.
(* pp->corrupt and its granule's shadow at the parse's return; pp + 0x4008 in R+0x8, the mask in R+0x148 *)
assert (H24 : getr regs2 (Z_to_bv 5 24) = w64 (pp + 0x4d18)) by (rewrite Rk2 by (cbn; tauto); exact S8).
assert (H20 : getr regs2 (Z_to_bv 5 20) = w64 SHADOW_OFF) by (rewrite Rk2 by (cbn; tauto); exact S4r).
assert (H9 : getr regs2 (Z_to_bv 5 9) = w64 R) by (rewrite Rk2 by (cbn; tauto); exact S1).
assert (Hv8 : val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0x8) 8 (pp + 0x4008)).
{ rewrite (Z.mod_small (pp + 0x4008)) in C8 by lia.
  eapply (val_mem_kept rsegs); [|exact C8]. intros kk Hkk. cbn in Hkk. apply K2; [lia|]. apply NR. lia. }
assert (Hv148 : val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0x148) 8 mask).
{ rewrite (Z.mod_small mask) in C148 by lia.
  eapply (val_mem_kept rsegs); [|exact C148]. intros kk Hkk. cbn in Hkk. apply K2; [lia|]. apply NR. lia. }
assert (Hstk : forall o, 0x178 <= o < 0x180 -> apresent (w_H W2) mem2 (R + o)).
{ intros o Ho. refine (proj1 (awr_byte_present rsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (R + o) HJ2 _)).
  apply RtPgStepsB.rtsb_awr_stk. lia. }
assert (Hpp2 : rtmb_bytes rsegs (w_H W2) mem2 pp (pp_bytes rec)).
{ unfold rsb_pp_at, rsb_u8s in Hpp. fold rec pp in Hpp.
  fold (rtmb_bytes rsegs (w_H (x_W cx)) (x_memc cx) pp (pp_bytes rec)) in Hpp.
  apply (rtmb_bytes_kept rsegs _ _ _ _ _ _ Hpp). intros x Hx.
  assert (Hlp : Z.of_nat (length (pp_bytes rec)) = Layout.PP_SIZE).
  { apply Layout.length_pp_image; [unfold Layout.POD_BUF_MAX; lia | exact (rkb_nent_le _ Hwf) |].
    pose proof (rkb_ents_wf _ Hwf) as Hew. rewrite Forall_forall in Hew |- *. intros x0 Hx0.
    destruct (Hew x0 Hx0) as (_ & Hb & Hs). rewrite Hb. lia. }
  rewrite Hlp in Hx. apply K2; [change Layout.PP_SIZE with 19744 in *; lia|]. apply NP. exact Hx. }
assert (Hcor : val_mem rsegs (mrestrict (w_H W2) mem2) (pp + 0x4d18) 4 (Z.b2z (corrupt rec))).
{ apply (rtmb_pp_corrupt rsegs (buf rec) (is_props rec) (has_params rec) (params_struct rec) (ents rec) (corrupt rec));
    [unfold Layout.POD_BUF_MAX; lia | exact (rkb_nent_le _ Hwf) | | exact Hpp2].
  pose proof (rkb_ents_wf _ Hwf) as Hew. rewrite Forall_forall in Hew |- *. intros x0 Hx0.
  destruct (Hew x0 Hx0) as (_ & Hb & Hs). rewrite Hb. lia. }
assert (Hppin2 : In (pp, Layout.PP_SIZE) (ablocks B ly2 S2))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); exact Hppin).
destruct (rtmb_blk_ra rsegs B ly2 S2 W2 mem2 md2 pp Layout.PP_SIZE (pp + 0x4d18) 8 (proj1 HJ2) Hppin2 ltac:(lia)
  ltac:(unfold req_size, Layout.PP_SIZE; cbn; lia)) as (Hra & _).
assert (Hpa : pp + 19744 <= 0x7fff7000 \/ 0x10007fff8000 <= pp)
  by (unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, Layout.PP_SIZE in Papp; lia).
(* the env of the run: the mask (atom 32) and pp + 0x4008 (atom 33) as its extra atoms *)
assert (E32 : ew (Ereg regs2 [w64 mask; w64 (pp + 0x4008)]) 32 = Z_to_bv 64 mask)
  by (change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E33 : ew (Ereg regs2 [w64 mask; w64 (pp + 0x4008)]) 33 = Z_to_bv 64 (pp + 0x4008))
  by (change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E9C : bv_unsigned (ew (Ereg regs2 [w64 mask; w64 (pp + 0x4008)]) 9) = R).
{ rewrite (ew_Ereg_nat regs2 _ 9 (Z_to_bv 5 9) eq_refl), H9. unfold w64. apply unsigned_lit_small. lia. }
assert (E25 : ew (Ereg regs2 [w64 mask; w64 (pp + 0x4008)]) 25 = Z_to_bv 64 pod)
  by (rewrite (ew_Ereg_nat regs2 _ 25 (Z_to_bv 5 25) eq_refl); exact R25).
(* the shadow entry of the check *)
assert (SHOK : sh_ok rsegs HDBx HDSH (Ereg regs2 [w64 mask; w64 (pp + 0x4008)]) (mrestrict (w_H W2) mem2)).
{ apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range rsegs (w_H W2) mem2 (Ereg regs2 [w64 mask; w64 (pp + 0x4008)]) HDBx 24 (pp + 0x4d18) 8
    (pp + 0x4d18) 0 8 Hra).
  - apply (U_atom _ 20 SHADOW_OFF); [rewrite (ew_Ereg_nat regs2 _ 20 (Z_to_bv 5 20) eq_refl); exact H20 | unfold SHADOW_OFF; lia].
  - apply (U_atom _ 24 (pp + 0x4d18)); [rewrite (ew_Ereg_nat regs2 _ 24 (Z_to_bv 5 24) eq_refl); exact H24 | lia].
  - lia.
  - lia.
  - intros x Hx. cbn in Hx. unfold SHADOW_OFF. lia. }
assert (HAE : env_agree 32 (Ereg regs2 [w64 mask; w64 (pp + 0x4008)]) (Ereg regs2 [w64 mask; w64 (pp + 0x4008)]))
  by apply env_agree_refl.
unfold cfg_at. change (w64 HD_AFTER_PARSE) with (Z_to_bv 64 0x82a80).
destruct (corrupt rec) eqn:Hc; [| destruct (Z.testbit fl 0) eqn:Hb].
- (* pp->corrupt = 1: to A *)
  pose proof (hd_C_entry fx2 W2 regs2 mem2 [] 1 pp R mask (Forall_nil _) H24 H20 H9 ltac:(unfold HDCEIL_HI; lia) Pm16
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hstk Hcor Hv8 Hv148) as HS.
  aj_run_tok hd_tbl_ok HS HJ2 SHOK HDspan.
  { apply awr_ok_cons_ro; [cbn; lia|].
    eapply awr_ok_cons_gen; [reflexivity | exact E9C | | apply awr_ok_nil].
    intros a Ha. cbn [hd_rC2 YP09.r_wlo YP09.r_whi] in Ha. apply RtPgStepsB.rtsb_awr_stk. lia. }
  assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (R + 0x178 <= a < R + 0x180) ->
    aview rsegs (w_H W2) (ms_mem ms) a = aview rsegs (w_H W2) mem2 a).
  { intros a Ha Hn. unfold aview, mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
    rewrite unsigned_lit_small by exact Ha. intros (r & Hin & Hr). cbn [In] in Hin.
    destruct Hin as [<-|[<-|[]]]; cbn [hd_rC hd_rC2 YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    [lia | rewrite E9C in Hr; lia]. }
  assert (H178 : val_mem rsegs (mrestrict (w_H W2) (ms_mem ms)) (R + 0x178) 8 (pod mod 2 ^ 64)).
  { rewrite (Z.mod_small pod) by lia.
    lazymatch type of HS with st_ok _ _ ?ss _ =>
      let r := eval vm_compute in (nth_error (ss_mem ss) 1) in
      lazymatch r with Some ?rg =>
        assert (Hr : nth_error (ss_mem ss) 1 = Some rg) by (vm_compute; reflexivity);
        pose proof (RtPgStepsB.rtsb_region_nth _ _ _ 1 _ _ HS Hr) as Hreg end end.
    exact (skb_field_of_region _ _ _ _ _ _ _ _ _ 0x178 8 (SOff 25 0) pod Hreg E9C ltac:(cbn; tauto)
      ltac:(rewrite (skb_soff _ 25 pod 0 E25), Z.add_0_r; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)). }
  hd_exit HS.
  apply (HA fx2 ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ rec).
  destruct (hd_common cx inp fx2 ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms) _ HC HBp HJ2
    (RtPgStepsB.same_io_wvb _ _ _) KF H178) as (Hbase & Hat & Hhz).
  + intros r Hr. exact (YI04.regs_kept_of_st_ok rsegs _ _ _ regs2 [w64 mask; w64 (pp + 0x4008)]
      (map (Z_to_bv 5) [2; 3; 4; 8; 9; 19; 20; 21; 23]) HS HAE ltac:(vm_compute; reflexivity)
      (Z_to_bv 5 r) (in_map _ _ _ Hr)).
  + eapply (skb_reg_is _ _ ms (w_H W2) regs2 _ _ _ 10%nat HS HAE); [vm_compute; reflexivity | reflexivity].
  + rewrite (st_ok_restrict_reg rsegs (w_H W2) _ _ ms _ HS).
    lazymatch type of HS with st_ok _ _ ?ss _ => let v := eval vm_compute in (sr_get (ss_regs ss) (Z_to_bv 5 22)) in
      change (sr_get (ss_regs ss) (Z_to_bv 5 22)) with v end.
    rewrite (skb_soff _ 32 mask 0 E32), Z.add_0_r. reflexivity.
  + split; [exact Hbase|]. split; [|exact Hhz].
    apply (skb_at_sub _ _ _ _ _ _ Hat). intros x Hx. unfold hd_L. fold rec. unfold rsb_L_chk, rsb_Hc in Hx |- *.
    cbn [In app] in Hx |- *. tauto.
- (* corrupt = 0, flags bit 0 set: to MAL *)
  assert (Hv : getr regs2 18 = w64 1).
  { rewrite <- (skb_getr_z regs2 18 18 eq_refl). first [exact R18 | rewrite Hb in R18; exact R18]. }
  pose proof (hd_C_entry fx2 W2 regs2 mem2 [((18%bv : bv 5), SLit 1)] 0 pp R mask
    ltac:(apply Forall_cons; [split; [intros Hz; apply (f_equal (@bv_unsigned 5)) in Hz; vm_compute in Hz; discriminate Hz | symmetry; exact Hv] | apply Forall_nil])
    H24 H20 H9 ltac:(unfold HDCEIL_HI; lia) Pm16 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hstk Hcor Hv8 Hv148) as HS.
  aj_run_tok hd_tbl_ok HS HJ2 SHOK HDspan.
  { apply awr_ok_cons_ro; [cbn; lia|].
    eapply awr_ok_cons_gen; [reflexivity | exact E9C | | apply awr_ok_nil].
    intros a Ha. cbn [hd_rC2 YP09.r_wlo YP09.r_whi] in Ha. apply RtPgStepsB.rtsb_awr_stk. lia. }
  assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (R + 0x178 <= a < R + 0x180) ->
    aview rsegs (w_H W2) (ms_mem ms) a = aview rsegs (w_H W2) mem2 a).
  { intros a Ha Hn. unfold aview, mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
    rewrite unsigned_lit_small by exact Ha. intros (r & Hin & Hr). cbn [In] in Hin.
    destruct Hin as [<-|[<-|[]]]; cbn [hd_rC hd_rC2 YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    [lia | rewrite E9C in Hr; lia]. }
  assert (H178 : val_mem rsegs (mrestrict (w_H W2) (ms_mem ms)) (R + 0x178) 8 (pod mod 2 ^ 64)).
  { rewrite (Z.mod_small pod) by lia.
    lazymatch type of HS with st_ok _ _ ?ss _ =>
      let r := eval vm_compute in (nth_error (ss_mem ss) 1) in
      lazymatch r with Some ?rg =>
        assert (Hr : nth_error (ss_mem ss) 1 = Some rg) by (vm_compute; reflexivity);
        pose proof (RtPgStepsB.rtsb_region_nth _ _ _ 1 _ _ HS Hr) as Hreg end end.
    exact (skb_field_of_region _ _ _ _ _ _ _ _ _ 0x178 8 (SOff 25 0) pod Hreg E9C ltac:(cbn; tauto)
      ltac:(rewrite (skb_soff _ 25 pod 0 E25), Z.add_0_r; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)). }
  hd_exit HS.
  apply (HM fx2 ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ rec).
  destruct (hd_common cx inp fx2 ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms) _ HC HBp HJ2
    (RtPgStepsB.same_io_wvb _ _ _) KF H178) as (Hbase & Hat & Hhz).
  + intros r Hr. exact (YI04.regs_kept_of_st_ok rsegs _ _ _ regs2 [w64 mask; w64 (pp + 0x4008)]
      (map (Z_to_bv 5) [2; 3; 4; 8; 9; 19; 20; 21; 23]) HS HAE ltac:(vm_compute; reflexivity)
      (Z_to_bv 5 r) (in_map _ _ _ Hr)).
  + eapply (skb_reg_is _ _ ms (w_H W2) regs2 _ _ _ 10%nat HS HAE); [vm_compute; reflexivity | reflexivity].
  + rewrite (st_ok_restrict_reg rsegs (w_H W2) _ _ ms _ HS).
    lazymatch type of HS with st_ok _ _ ?ss _ => let v := eval vm_compute in (sr_get (ss_regs ss) (Z_to_bv 5 22)) in
      change (sr_get (ss_regs ss) (Z_to_bv 5 22)) with v end.
    rewrite (skb_soff _ 32 mask 0 E32), Z.add_0_r. reflexivity.
  + assert (HPA : rsb_PA rsegs cx rec = (None, -1)) by (unfold rsb_PA; fold fl; rewrite Hb; reflexivity).
    split; [exact Hbase|]. split; [|split; [exact Hhz | rewrite HPA; split; reflexivity]].
    apply (skb_at_sub _ _ _ _ _ _ Hat). intros x Hx. unfold hd_L. fold rec. rewrite HPA. unfold rsb_L_chk, rsb_Hc in Hx |- *.
    cbn [In app snd] in Hx |- *. tauto.
- (* corrupt = 0, flags bit 0 clear: to E *)
  assert (Hv : getr regs2 18 = w64 0).
  { rewrite <- (skb_getr_z regs2 18 18 eq_refl). first [exact R18 | rewrite Hb in R18; exact R18]. }
  pose proof (hd_C_entry fx2 W2 regs2 mem2 [((18%bv : bv 5), SLit 0)] 0 pp R mask
    ltac:(apply Forall_cons; [split; [intros Hz; apply (f_equal (@bv_unsigned 5)) in Hz; vm_compute in Hz; discriminate Hz | symmetry; exact Hv] | apply Forall_nil])
    H24 H20 H9 ltac:(unfold HDCEIL_HI; lia) Pm16 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hstk Hcor Hv8 Hv148) as HS.
  aj_run_tok hd_tbl_ok HS HJ2 SHOK HDspan.
  { apply awr_ok_cons_ro; [cbn; lia|].
    eapply awr_ok_cons_gen; [reflexivity | exact E9C | | apply awr_ok_nil].
    intros a Ha. cbn [hd_rC2 YP09.r_wlo YP09.r_whi] in Ha. apply RtPgStepsB.rtsb_awr_stk. lia. }
  assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (R + 0x178 <= a < R + 0x180) ->
    aview rsegs (w_H W2) (ms_mem ms) a = aview rsegs (w_H W2) mem2 a).
  { intros a Ha Hn. unfold aview, mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
    rewrite unsigned_lit_small by exact Ha. intros (r & Hin & Hr). cbn [In] in Hin.
    destruct Hin as [<-|[<-|[]]]; cbn [hd_rC hd_rC2 YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    [lia | rewrite E9C in Hr; lia]. }
  assert (H178 : val_mem rsegs (mrestrict (w_H W2) (ms_mem ms)) (R + 0x178) 8 (pod mod 2 ^ 64)).
  { rewrite (Z.mod_small pod) by lia.
    lazymatch type of HS with st_ok _ _ ?ss _ =>
      let r := eval vm_compute in (nth_error (ss_mem ss) 1) in
      lazymatch r with Some ?rg =>
        assert (Hr : nth_error (ss_mem ss) 1 = Some rg) by (vm_compute; reflexivity);
        pose proof (RtPgStepsB.rtsb_region_nth _ _ _ 1 _ _ HS Hr) as Hreg end end.
    exact (skb_field_of_region _ _ _ _ _ _ _ _ _ 0x178 8 (SOff 25 0) pod Hreg E9C ltac:(cbn; tauto)
      ltac:(rewrite (skb_soff _ 25 pod 0 E25), Z.add_0_r; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)). }
  assert (Ra0 : getr (ms_regs ms) (Z_to_bv 5 10) = w64 (pp + 0x4008)).
  { rewrite (st_ok_restrict_reg rsegs (w_H W2) _ _ ms _ HS).
    lazymatch type of HS with st_ok _ _ ?ss _ => let v := eval vm_compute in (sr_get (ss_regs ss) (Z_to_bv 5 10)) in
      change (sr_get (ss_regs ss) (Z_to_bv 5 10)) with v end.
    rewrite (skb_soff _ 33 (pp + 0x4008) 0 E33), Z.add_0_r. reflexivity. }
  hd_exit HS.
  apply (HE fx2 ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ rec).
  destruct (hd_common cx inp fx2 ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms) _ HC HBp HJ2
    (RtPgStepsB.same_io_wvb _ _ _) KF H178) as (Hbase & Hat & Hhz).
  + intros r Hr. exact (YI04.regs_kept_of_st_ok rsegs _ _ _ regs2 [w64 mask; w64 (pp + 0x4008)]
      (map (Z_to_bv 5) [2; 3; 4; 8; 9; 19; 20; 21; 23]) HS HAE ltac:(vm_compute; reflexivity)
      (Z_to_bv 5 r) (in_map _ _ _ Hr)).
  + eapply (skb_reg_is _ _ ms (w_H W2) regs2 _ _ _ 10%nat HS HAE); [vm_compute; reflexivity | reflexivity].
  + rewrite (st_ok_restrict_reg rsegs (w_H W2) _ _ ms _ HS).
    lazymatch type of HS with st_ok _ _ ?ss _ => let v := eval vm_compute in (sr_get (ss_regs ss) (Z_to_bv 5 22)) in
      change (sr_get (ss_regs ss) (Z_to_bv 5 22)) with v end.
    rewrite (skb_soff _ 32 mask 0 E32), Z.add_0_r. reflexivity.
  + split; [exact Hbase|]. split.
    { unfold hd_L in Hat. unfold rsb_at_cx, rsb_at in Hat |- *.
      apply Forall_app in Hat as [Hl Hr]. apply Forall_app. split; [exact Hl|].
      apply Forall_cons; [cbn [fst snd rt_at]; exact Ra0 | exact Hr]. }
    split; [exact Hhz|].
    split; [exact Hb|]. split; [exact Hc|].
    exact (rkb_parse_expect rec Hwf Hc).
Qed.

(* ===================== the piece ===================== *)
Theorem rkb_head_B : rsb_piece_W11a_head_stmt rsegs B MT.
Proof using AMEMCPY PARSE.
unfold rsb_piece_W11a_head_stmt. intros cx POST inp Hst HE HM HA.
pose proof (hd_c3_of cx inp Hst) as HC.
apply (hd_A cx inp POST HC).
intros regs1 mem1 md1 HAp.
apply (hd_B cx inp regs1 mem1 md1 POST HC HAp).
intros fx2 ly2 S2 W2 regs2 mem2 md2 HBp.
exact (hd_C cx inp POST fx2 ly2 S2 W2 regs2 mem2 md2 HC HBp HE HM HA).
Qed.
End e.
End c.

Print Assumptions rkb_head_B.
