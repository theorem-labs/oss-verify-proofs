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
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/RtPgScanHeadB.v at e4ef964f482f for
   reac-pw/fuzz_role's image B (fuzz_role.asan-ubsan): module paths fuzz_rate -> fuzz_role, the segments are
   lib/AU/Img0.v rsegs, the cut file is lib/AU/RPgSeg.v (rsb_ -> rs_, rt_ -> rl_, q_ -> e_, the hz cell -> the role
   cell rs_role_at, the exit A -> T), the kit lib/AU/RPgScanKit.v, the model facts lib/AU/RPgScanF.v, the memory and
   step layers lib/AU/RPgMem.v and RPgSteps.v; role B's pcs (C3 0x82168, the memcpy return 0x8218c, the parse return
   0x821b4, E 0x821dc, MAL 0x824f8, T 0x82504, the slow block 0x82638), runtime entries (memcpy 0x5116c, the parse
   0x83130 with lib/AU/RPgParseBase.v's key 0x215e0 and five doubles: RPgCSpec.rl_parse_specX as lib/AU/RPgParse.v
   rl_parse_B states it), registers (pod s2, &role s4 = F + 0x2a0, F s10 read in block A, the flags byte s8 read
   after the memcpy in block B, flags & 1 s5, the shadow offset s11, len s8, pp + 0x4d18 s7, rc s9, pp s6) and cells
   (F from R+0x38, pp from R+0x140, the flags byte from R+0x40, pp + 0x4008 from R+0x18); the role cell takes role's
   literal 90 (0x5a) and the parse's role_z (role A's semantics); block C stores nothing (rate's pod store into
   R+0x178 has no role twin), so its regions are read-only and its exits keep the memory at the parse's return. *)
(* reac-pw/fuzz_role image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; every address measured on the unstripped twin
   dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a, same loaded bytes): the head of the checking
   segment M02 of LLVMFuzzerTestOneInput, lib/AU/RPgSeg.v rs_piece_W11a_head_stmt. Proves no function (kind:
   segment lemma).

   THE CODE (C3 0x82168 to E 0x821dc, MAL 0x824f8 and T 0x82504; fuzz.h:73-78, fuzz_role.c:147-149)
     0x82168  beqz a0,0x82608      the second block is not NULL: decided by a0's atom fact (pod >= 4096)
     0x8216c  mv s2,a0; ld s10,0x38(s1) (F, from the cell R+0x38); addi s4,s10,0x2a0 (&role = F + 0x2a0)
     0x82178  beqz s8,0x8218c      len = 0: decided by s8's atom fact (8 <= len <= 5440)
     0x8217c  a0 = pod, a1 = pp (the cell R+0x140), a2 = len; 0x82188 jal __asan_memcpy (0x5116c)
     0x8218c  a0 = 4, a1 = 90; 0x82194 sb a0,0x54(s3) (role's shadow byte := 0x04)
     0x82198  ld s8,0x40(s1) (the flags byte); s5 = flags & 1; 0x821a0 sw a1,0(s4) (role := 90)
     0x821a4  a0 = s5 - 1; a0 = a0 & s2 (NULL when bit 0 is set, else pod); a1 = s4; 0x821b0 jal the parse (0x83130)
     0x821b4  srli / add s11 / lb: the shadow byte of pp->corrupt (an instrumented 4-byte check); 0x821c0 s9 = rc
     0x821c4  bnez a1 (the check's slow block 0x82638): decided not taken, the granule of pp + 0x4d18 is usable
     0x821c8  lw a0,0(s7) (pp->corrupt); ld s6,0x140(s1) (pp)
     0x821d0  bnez a0 -> T; 0x821d4 ld a0,0x18(s1) (pp + 0x4008); 0x821d8 bnez s5 -> MAL; else E.
   The walk is three engine runs (lib/Reusable: st_ok, aj_run_to / aj_run_tok) cut at the two calls: the memcpy is
   the runtime's __asan_memcpy (YG0d.aintrin_realizes, the Section hypothesis AMEMCPY), the parse is RPgCSpec's
   rl_parse_specX at the parse's entry, its key literal "reac.cfg.role" (0x215e0) and its five doubles (the
   Section hypothesis PARSE). Every byte the head writes lies in the pod block, the callees' stack
   [R - T_SEG_STK, R), the role cell [F + 0x2a0, F + 0x2a4) or its shadow byte, all inside RPgSeg.rs_E2 or the
   callees' stack, so the segment's kept clause carries over. The trap branch `beqz a0,0x82608` (0x82168, the NULL
   test before abort) is decided not taken; the instrumented check of pp->corrupt (0x821bc) never reaches its error
   path (0x82644 .., after the slow block 0x82638). *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout Accessors Spa Role.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0 RPgImgA RPgSeg RPgMem RPgScanF RPgScanKit.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require RPgSteps RPgSiteA RPgParseBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ============================== the code table ============================== *)
(* the 29 words 0x82168 .. 0x821d8 (every run of the head leaves them at a call or at an exit) and the three words
   0x82638 .. 0x82640 of the slow block of the check at 0x821c4 (`andi`, `addi`, `blt` back to 0x821c8) *)
Definition HD_PC0 : Z := 0x82168.
Definition HD_SLOW : Z := 0x82638.
Definition hd_tbl : ctable := build_table rsegs HD_SLOW 3 (build_table rsegs HD_PC0 29 TEmpty).
Lemma hd_tbl_ok : table_ok rsegs hd_tbl.
Proof. apply build_table_ok; [unfold HD_SLOW; lia|]. apply build_table_ok0. unfold HD_PC0. lia. Qed.
Definition HD_MEMCPY : Z := 0x5116c.
Definition HD_AFTER_CPY : Z := 0x8218c.
Definition HD_PARSE : Z := 0x83130.
Definition HD_AFTER_PARSE : Z := 0x821b4.
(* the shadow base of the last run: s11's own atom (x27); its one shadow entry is pp->corrupt's granule at s7 (x23) *)
Definition HDBx : sv := SOff 27 0.
Definition HDspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition HDSH : list shent := [mkSHE 23 0 8].
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

(* `andi s5,s8,1` on the flags byte, and `addi a0,s5,-1; and a0,a0,s2`: NULL when bit 0 is set, else pod *)
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
rl_cstr rsegs H m a s -> rl_cstr rsegs H' m' a s.
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
Definition hdZ (cx : rs_scx rsegs) (a : Z) : Prop :=
(e_pod (x_e cx) <= a < e_pod (x_e cx) + e_len (x_e cx)) \/ (e_R (x_e cx) - T_SEG_STK <= a < e_R (x_e cx)) \/
a = shadow_addr (e_F (x_e cx)) + 0x54 \/ (e_F (x_e cx) + 0x2a0 <= a < e_F (x_e cx) + 0x2a4).

Lemma hdZ_E2 : forall cx a, hdZ cx a -> (e_R (x_e cx) - T_SEG_STK <= a < e_R (x_e cx)) \/ rs_E2 rsegs cx a.
Proof.
intros cx a [H|[H|[H|H]]].
- right. right. exact H.
- left. exact H.
- right. left. unfold rl_inw. cbn [hi_w2 role_himg_B].
  apply Exists_cons_tl. apply Exists_cons_hd. cbn [rl_xv fst snd]. lia.
- right. left. unfold rl_inw. cbn [hi_w2 role_himg_B]. apply Exists_cons_hd. cbn [rl_xv fst snd]. lia.
Qed.

(* the cut lists of T and MAL are sub-lists of this one; E's is this one with a0 = pp + 0x4008 added *)
Definition hd_L (cx : rs_scx rsegs) (rec : pod_rec) : list (rl_loc * Z) :=
rs_L_chk rsegs cx ++ [(LReg 25, snd (rs_PA rsegs cx rec)); (LReg 22, e_pp (x_e cx)); (LReg 24, e_fl (x_e cx));
                       (LReg 26, e_F (x_e cx)); (LCell XR 0x38, e_F (x_e cx));
                       (LCell XR 0xe8, Z.shiftr (e_pp (x_e cx) + 0x4d14) 3);
                       (LCell XR 0x120, e_pp (x_e cx) + 0x4d14); (LCell XR 0x140, e_pp (x_e cx));
                       (LCell XR 0xc0, -0x3ffd)].

(* the entry states of blocks A, B and C: the regions they read and write *)
Definition hd_rA : YP09.region := YP09.mkRegion (Some 9%nat) 0x38 0x148 0 0
  [YP09.mkChunk 0x38 (CVal 8 (SOff 32 0)); YP09.mkChunk 0x140 (CVal 8 (SOff 33 0))].
Definition hd_rB0 : YP09.region := YP09.mkRegion (Some 19%nat) 0x54 0x55 0x54 0x55 [].
Definition hd_rB1 : YP09.region := YP09.mkRegion (Some 9%nat) 0x40 0x48 0 0 [YP09.mkChunk 0x40 (CVal 8 (SOff 32 0))].
Definition hd_rB2 : YP09.region := YP09.mkRegion (Some 20%nat) 0 4 0 4 [].
Definition hd_rC (c : Z) : YP09.region := YP09.mkRegion (Some 23%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SLit c))].
Definition hd_rC2 : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x18 0x148 0 0
    [YP09.mkChunk 0x18 (CVal 8 (SOff 33 0)); YP09.mkChunk 0x140 (CVal 8 (SOff 32 0))].
Definition hd_factsC : facts :=
  mkFacts [(27%nat, mkAF 0x7fff8000 0x7fff8000 0); (23%nat, mkAF 4096 HDCEIL_HI 3)] [] [].

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* the entry state of the last run at 0x821b4: the registers as atoms with the overrides ov, pp->corrupt's 4 bytes
   at s7 as the closed value c, pp (the extra atom 32) in the cell R+0x140, pp + 0x4008 (the extra atom 33) in the
   cell R+0x18, s11 = the shadow offset and s7 = pp + 0x4d18 as atom facts *)
Lemma hd_C_entry : forall (fx' : YK11.FPState) (W2 : world rsegs) regs2 mem2 (ov : list (bv 5 * sv)) c pp R,
Forall (fun p => fst p <> 0%bv /\
  sv_denot (Ereg regs2 [w64 pp; w64 (pp + 0x4008)]) (snd p) = getr regs2 (fst p)) ov ->
getr regs2 (Z_to_bv 5 23) = w64 (pp + 0x4d18) -> getr regs2 (Z_to_bv 5 27) = w64 SHADOW_OFF ->
getr regs2 (Z_to_bv 5 9) = w64 R ->
4096 <= pp + 0x4d18 <= HDCEIL_HI -> pp mod 16 = 0 -> 4096 <= pp -> 0 <= c < 2 ^ 32 ->
pp + 0x4d1c <= R -> R <= 0x800000000000 ->
val_mem rsegs (mrestrict (w_H W2) mem2) (pp + 0x4d18) 4 c ->
val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0x18) 8 (pp + 0x4008) ->
val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0x140) 8 pp ->
@st_ok rsegs fx' (Ereg regs2 [w64 pp; w64 (pp + 0x4008)])
  (mkSS 0x821b4 (sk_sr ov) [hd_rC c; hd_rC2] None hd_factsC)
  (restrict (w_H W2) (@mkst fx' regs2 (Z_to_bv 64 0x821b4) mem2 (seg_rom rsegs))).
Proof.
intros fx' W2 regs2 mem2 ov c pp R Hov H23 H27 H9 Hpp Hpp16 Hpp0 Hc HppR HR Hv Hv18 Hv140.
assert (E23 : bv_unsigned (ew (Ereg regs2 [w64 pp; w64 (pp + 0x4008)]) 23) = pp + 0x4d18).
{ rewrite (ew_Ereg_nat regs2 _ 23 (Z_to_bv 5 23) eq_refl), H23. unfold w64. apply unsigned_lit_small.
  unfold HDCEIL_HI in Hpp. lia. }
assert (E27 : bv_unsigned (ew (Ereg regs2 [w64 pp; w64 (pp + 0x4008)]) 27) = SHADOW_OFF).
{ rewrite (ew_Ereg_nat regs2 _ 27 (Z_to_bv 5 27) eq_refl), H27. unfold w64. apply unsigned_lit_small.
  unfold SHADOW_OFF. lia. }
assert (E9 : bv_unsigned (ew (Ereg regs2 [w64 pp; w64 (pp + 0x4008)]) 9) = R).
{ rewrite (ew_Ereg_nat regs2 _ 9 (Z_to_bv 5 9) eq_refl), H9. unfold w64. apply unsigned_lit_small.
  unfold HDCEIL_HI in Hpp. lia. }
assert (E32 : ew (Ereg regs2 [w64 pp; w64 (pp + 0x4008)]) 32 = Z_to_bv 64 pp)
  by (change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E33 : ew (Ereg regs2 [w64 pp; w64 (pp + 0x4008)]) 33 = Z_to_bv 64 (pp + 0x4008))
  by (change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; reflexivity).
rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
- apply sk_regs_ok. exact Hov.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + unfold hd_rC. apply (rm_ro_region rsegs _ (w_H W2) mem2 23 (pp + 0x4d18) 0 4);
      [exact E23 | lia | unfold HDCEIL_HI in Hpp; lia |].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val rsegs _ _ (pp + 0x4d18) 0 4 (SLit c) c); [reflexivity | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact Hv.
  + unfold hd_rC2. apply (rm_ro_region rsegs _ (w_H W2) mem2 9 R 0x18 0x148); [exact E9 | lia | lia |].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    * apply (chunk_ok_val rsegs _ _ R 0x18 8 (SOff 33 0) (pp + 0x4008)).
      -- cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E33.
      -- cbn. unfold HDCEIL_HI in Hpp. lia.
      -- cbn. lia.
      -- exact Hv18.
    * apply (chunk_ok_val rsegs _ _ R 0x140 8 (SOff 32 0) pp).
      -- cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E32.
      -- cbn. unfold HDCEIL_HI in Hpp. lia.
      -- cbn. lia.
      -- exact Hv140.
- cbn [pairwise_disjoint all_disjoint hd_rC hd_rC2 extent_disjoint YP09.r_base YP09.r_lo YP09.r_hi base_val].
  unfold extent_disjoint, hd_rC, hd_rC2. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite E23, E9. unfold HDCEIL_HI in Hpp. repeat split; lia.
- unfold facts_ok, hd_factsC. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. unfold afact_ok.
  cbn [af_lo af_hi af_al2]. rewrite E23, E27. unfold SHADOW_OFF, HDCEIL_HI in *.
  change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
  assert (H8p : pp mod 8 = 0)
    by (rewrite <- (Z.mod_mod_divide pp 16 8) by (exists 2; reflexivity); rewrite Hpp16; reflexivity).
  assert (H8 : (pp + 0x4d18) mod 8 = 0) by (rewrite Zplus_mod, H8p; reflexivity).
  repeat split; lia.
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
(* the runtime's __asan_memcpy (YG0d.AsanAPI's aa_asan_memcpy at image B's checked_memcpy entry 0x5116c, the target
   of the `jal` at 0x82188) *)
Hypothesis AMEMCPY : aintrin_realizes rsegs B OCpy 0x5116c.
(* the parse's contract (RPgCSpec.rl_parse_specX at the parse's entry 0x83130, the target of the `jal` at 0x821b0,
   its key literal "reac.cfg.role" at 0x215e0 and its five doubles: lib/AU/RPgParseBase.v A_PARSE, A_KEY,
   role_B_dcs, the statement lib/AU/RPgParse.v rl_parse_B proves) *)
Hypothesis PARSE : rl_parse_specX rsegs B MT RPgParseBase.A_PARSE RPgParseBase.A_KEY RPgParseBase.role_B_dcs.

(* ================= the start state at C3 (rs_start_M02), unfolded into the facts the walk uses ================= *)
Record hd_c3 (cx : rs_scx rsegs) (inp : list byte) : Prop := HDC3 {
c3_J : ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
  (x_own cx) (x_lyc cx) (x_Sc cx) (x_W cx) (x_memc cx) (x_mdc cx) (x_k cx);
c3_ev : st_nev (x_S cx) + x_k cx <= EV_MAX;
c3_r2 : getr (x_regs cx) 2 = w64 (e_R (x_e cx));
c3_r3 : getr (x_regs cx) 3 = w64 (as_gp B);
c3_r4 : getr (x_regs cx) 4 = w64 (as_tp B);
c3_S : e_S (x_e cx) = x_sp0 cx;
c3_R16 : e_R (x_e cx) mod 16 = 0;
c3_RS : e_R (x_e cx) + 0x200 <= e_S (x_e cx);
c3_STK : x_sp0 cx - x_STK cx <= e_R (x_e cx) - T_SEG_STK;
c3_own : In (4, x_pos cx) (x_own cx);
c3_F : e_F (x_e cx) = frame_addr (x_lyc cx) 4 (x_pos cx);
c3_ppin : In (e_pp (x_e cx), Layout.PP_SIZE) (ablocks B (x_lyc cx) (x_Sc cx));
c3_fl : 0 <= e_fl (x_e cx) < 256;
c3_strs : Forall (fun s => rl_cstr rsegs (w_H (x_W cx)) (x_memc cx) (fst s) (snd s)) role_B_strs;
c3_cells : rl_ro_cells rsegs (w_H (x_W cx)) (x_memc cx) role_B_cells;
c3_rom : rom_view rsegs (x_W cx) (x_memc cx);
c3_ppnew : ~ In (e_pp (x_e cx), Layout.PP_SIZE) (ablocks B (x_ly cx) (x_S cx));
c3_fsh : rl_fsh rsegs (w_H (x_W cx)) (x_memc cx) (e_F (x_e cx)) role_B_shA;
c3_a0 : getr (x_regs cx) (Z_to_bv 5 10) = w64 (e_pod (x_e cx));
c3_s0 : getr (x_regs cx) (Z_to_bv 5 8) = w64 (e_S (x_e cx));
c3_s1 : getr (x_regs cx) (Z_to_bv 5 9) = w64 (e_R (x_e cx));
c3_s3 : getr (x_regs cx) (Z_to_bv 5 19) = w64 (shadow_addr (e_F (x_e cx)));
c3_s7 : getr (x_regs cx) (Z_to_bv 5 23) = w64 (e_pp (x_e cx) + 0x4d18);
c3_s8 : getr (x_regs cx) (Z_to_bv 5 24) = w64 (e_len (x_e cx));
c3_s11 : getr (x_regs cx) (Z_to_bv 5 27) = w64 SHADOW_OFF;
c3_c18 : val_mem rsegs (mrestrict (w_H (x_W cx)) (x_memc cx)) (e_R (x_e cx) + 0x18) 8
  ((e_pp (x_e cx) + 0x4008) mod 2 ^ 64);
c3_c20 : val_mem rsegs (mrestrict (w_H (x_W cx)) (x_memc cx)) (e_R (x_e cx) + 0x20) 8 (e_F (x_e cx) mod 2 ^ 64);
c3_c38 : val_mem rsegs (mrestrict (w_H (x_W cx)) (x_memc cx)) (e_R (x_e cx) + 0x38) 8 (e_F (x_e cx) mod 2 ^ 64);
c3_c40 : val_mem rsegs (mrestrict (w_H (x_W cx)) (x_memc cx)) (e_R (x_e cx) + 0x40) 8 (e_fl (x_e cx) mod 2 ^ 64);
c3_cc0 : val_mem rsegs (mrestrict (w_H (x_W cx)) (x_memc cx)) (e_R (x_e cx) + 0xc0) 8 (-0x3ffd mod 2 ^ 64);
c3_ce8 : val_mem rsegs (mrestrict (w_H (x_W cx)) (x_memc cx)) (e_R (x_e cx) + 0xe8) 8
  (Z.shiftr (e_pp (x_e cx) + 0x4d14) 3 mod 2 ^ 64);
c3_c120 : val_mem rsegs (mrestrict (w_H (x_W cx)) (x_memc cx)) (e_R (x_e cx) + 0x120) 8
  ((e_pp (x_e cx) + 0x4d14) mod 2 ^ 64);
c3_c140 : val_mem rsegs (mrestrict (w_H (x_W cx)) (x_memc cx)) (e_R (x_e cx) + 0x140) 8
  ((e_pp (x_e cx) + 0) mod 2 ^ 64);
c3_len : e_len (x_e cx) = rl_len inp;
c3_pp : rs_pp_at rsegs cx (x_W cx) (x_memc cx) (pp_bytes (fst (pod_build inp)));
c3_pod0 : e_pod (x_e cx) <> 0;
c3_podin : In (e_pod (x_e cx), e_len (x_e cx)) (ablocks B (x_lyc cx) (x_Sc cx));
c3_podnew : ~ In (e_pod (x_e cx), e_len (x_e cx)) (ablocks B (x_ly cx) (x_S cx));
c3_frm : YK0o.frm_zero (@fp_csr fx) }.

Lemma hd_c3_of : forall cx inp, rs_start_M02 rsegs B cx inp -> hd_c3 cx inp.
Proof.
intros cx inp (HP & Hfsh & HL3 & Hlen & Hpp & Hpod0 & Hpodin & Hpodnew & Hfrm).
destruct HP as (HJ & Hev & H2 & H3 & H4 & HeS & HR16 & HRS & HSTK & Hown & HeF & _ & _ & Hppin & Hfl & _ & _ & _ &
  Hstrs & Hcells & Hrom & Hppnew).
unfold rl_cut in HL3. cbn [hi_L3 role_himg_B] in HL3. unfold role_B_L23 in HL3.
repeat rewrite Forall_cons_iff in HL3.
destruct HL3 as (A10 & A8 & A9 & A19 & A23 & A24 & A27 & C18 & C20 & C38 & C40 & Cc0 & Ce8 & C120 & C140 & _).
cbn [fst snd rl_at rl_xv] in A10, A8, A9, A19, A23, A24, A27, C18, C20, C38, C40, Cc0, Ce8, C120, C140.
cbn [hi_cid hi_rsz hi_shA hi_strs hi_cells role_himg_B] in *.
constructor; assumption.
Qed.

(* the bounds the walk uses, from C3's journal and the allocator's block and frame laws *)
Lemma hd_bounds : forall cx inp, hd_c3 cx inp ->
let e := x_e cx in
e_pp e mod 16 = 0 /\ 4096 <= e_pp e /\ e_pp e + Layout.PP_SIZE <= alloc_ceiling /\ in_app (e_pp e) Layout.PP_SIZE /\
e_pod e mod 16 = 0 /\ 4096 <= e_pod e /\ e_pod e + e_len e <= alloc_ceiling /\ in_app (e_pod e) (e_len e) /\
8 <= e_len e <= 5440 /\
e_F e mod 32 = 0 /\ 4096 <= e_F e /\ e_F e + 1024 <= alloc_ceiling /\ in_app (e_F e) 1024 /\
alloc_ceiling + T_SEG_STK <= e_R e /\ e_R e + 0x200 <= x_sp0 cx /\ x_sp0 cx <= 2 ^ 47 /\ x_sp0 cx mod 16 = 0 /\
x_sp0 cx - x_STK cx <= e_R e - T_SEG_STK /\ 0x7fff7f800000 <= alloc_ceiling <= HDCEIL_HI.
Proof.
intros cx inp HC e. pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof (c3_J cx inp HC) as HJ.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR (c3_ppin cx inp HC)) as (Hm16 & H4096 & Hpc & Happ & _).
pose proof (RPgSiteA.rl_len_bounds inp) as Hlb. rewrite <- (c3_len cx inp HC) in Hlb.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR (c3_podin cx inp HC)) as (Qm16 & Q4096 & Qpc & Qapp & _).
assert (Hfin : In (4, x_pos cx) (frames (x_Sc cx))) by (rewrite Hfrs; apply in_or_app; left; exact (c3_own cx inp HC)).
destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR Hfin) as (Fm32 & Fapp & _).
destruct (frames_bounds rsegs B LAWS _ _ _ _ _ _ _ HAR Hfin) as (F4096 & Fc & _).
pose proof asan_consts as ((Ca1 & Ca2) & _).
replace (fs_frame_bytes 4) with 1024 in Fapp, Fc by reflexivity.
rewrite <- (c3_F cx inp HC) in Fm32, Fapp, F4096, Fc.
pose proof (c3_RS cx inp HC) as HRS. pose proof (c3_S cx inp HC) as HS. pose proof (c3_STK cx inp HC) as HSTK.
replace (req_size Layout.PP_SIZE) with Layout.PP_SIZE in Hpc, Happ by reflexivity.
replace (req_size (e_len (x_e cx))) with (e_len (x_e cx)) in Qpc, Qapp
  by (unfold req_size; destruct (Z.eqb_spec (e_len (x_e cx)) 0); lia).
unfold HDCEIL_HI, T_SEG_STK, ASTACK in *. subst e. rewrite HS in HRS.
repeat (first [assumption | split]); unfold Layout.PP_SIZE in *; lia.
Qed.

(* none of the frame for locals, the second block or the first block is in the image *)
Lemma hd_imgs : forall cx inp, hd_c3 cx inp ->
(forall a, e_F (x_e cx) <= a < e_F (x_e cx) + 1024 -> ~ in_img rsegs a) /\
(forall a, e_pod (x_e cx) <= a < e_pod (x_e cx) + e_len (x_e cx) -> ~ in_img rsegs a) /\
(forall a, e_pp (x_e cx) <= a < e_pp (x_e cx) + Layout.PP_SIZE -> ~ in_img rsegs a).
Proof.
intros cx inp HC. pose proof (AR_laws_ok rsegs B) as LAWS. pose proof (c3_J cx inp HC) as HJ.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hfin : In (4, x_pos cx) (frames (x_Sc cx))) by (rewrite Hfrs; apply in_or_app; left; exact (c3_own cx inp HC)).
split; [|split]; intros a Ha; refine (proj2 (al_client_img _ _ LAWS _ _ _ _ _ a HAR _)).
- right. left. exists 4, (x_pos cx). split; [exact Hfin|]. rewrite <- (c3_F cx inp HC).
  change (fs_frame_bytes 4) with 1024. exact Ha.
- left. exists (e_pod (x_e cx)), (e_len (x_e cx)). split; [exact (c3_podin cx inp HC)|].
  unfold req_size. destruct (Z.eqb_spec (e_len (x_e cx)) 0); lia.
- left. exists (e_pp (x_e cx)), Layout.PP_SIZE. split; [exact (c3_ppin cx inp HC)|].
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
set (F := e_F (x_e cx)) in *. set (pod := e_pod (x_e cx)) in *. set (len := e_len (x_e cx)) in *.
set (R := e_R (x_e cx)) in *.
unfold hd_szone, SHADOW_OFF in Ha. unfold hdZ. fold F pod len R.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Fapp, Qapp.
unfold HDCEIL_HI, T_SEG_STK, ASTACK in *.
assert (Hfq : 0 <= F / 8) by (apply Z.div_pos; lia).
split; [lia|]. intros [H|[H|[H|H]]].
- destruct Ha as [Ha|Ha]; [exact (Qimg a H (hd_img_zone a Ha)) | lia].
- lia.
- unfold shadow_addr, SHADOW_OFF in H. destruct Ha as [Ha|Ha]; [lia|].
  apply (Fimg (F + 0x2a0)); [lia|]. apply hd_img_zone. lia.
- destruct Ha as [Ha|Ha]; [exact (Fimg a ltac:(lia) (hd_img_zone a Ha)) | lia].
Qed.

(* none of the real frame from R on, the first block or the image is written by the head *)
Lemma hd_nz : forall cx inp, hd_c3 cx inp ->
(forall a, e_R (x_e cx) <= a < 2 ^ 64 -> ~ hdZ cx a) /\
(forall a, e_pp (x_e cx) <= a < e_pp (x_e cx) + Layout.PP_SIZE -> ~ hdZ cx a) /\
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
assert (Hne : (e_pod (x_e cx), e_len (x_e cx)) <> (e_pp (x_e cx), Layout.PP_SIZE))
  by (intros Heq; injection Heq as _ Hl; unfold Layout.PP_SIZE in Hl; lia).
pose proof (sep_blocks rsegs B LAWS _ _ _ _ _ _ _ _ _ HAR (c3_podin cx inp HC) (c3_ppin cx inp HC) Hne) as Hpq.
pose proof (sep_block_frame rsegs B LAWS _ _ _ _ _ _ _ _ _ HAR (c3_ppin cx inp HC) Hfin) as Hpf.
unfold zdisjoint in Hpq, Hpf. cbn [fst snd] in Hpq, Hpf. rewrite <- (c3_F cx inp HC) in Hpf.
change (fs_frame_bytes 4) with 1024 in Hpf.
replace (req_size (e_len (x_e cx))) with (e_len (x_e cx)) in Hpq
  by (unfold req_size; destruct (Z.eqb_spec (e_len (x_e cx)) 0); lia).
change (req_size Layout.PP_SIZE) with 19744 in Hpq, Hpf. change Layout.PP_SIZE with 19744 in *.
set (F := e_F (x_e cx)) in *. set (pod := e_pod (x_e cx)) in *. set (len := e_len (x_e cx)) in *.
set (R := e_R (x_e cx)) in *. set (pp := e_pp (x_e cx)) in *.
unfold hdZ. fold F pod len R.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Fapp, Qapp, Papp.
unfold HDCEIL_HI, T_SEG_STK, ASTACK in *. unfold shadow_addr, SHADOW_OFF.
assert (Hfq : 0 <= F / 8) by (apply Z.div_pos; lia).
split; [|split].
- intros a Ha [H|[H|[H|H]]]; lia.
- intros a Ha [H|[H|[H|H]]]; lia.
- intros a Ha. pose proof (RPgSteps.rl_segs_low a Ha) as Hl. unfold kLowMemEnd in Hl.
  intros [H|[H|[H|H]]]; [exact (Qimg a H Ha) | lia | lia | exact (Fimg a ltac:(lia) Ha)].
Qed.

(* ===================== block A: 0x82168 .. the memcpy's return 0x8218c ===================== *)
(* what C3 becomes after the memcpy: the pod block holds pp's first len bytes, every byte outside the pod block and
   the callee's stack [R - ESTACK, R) is as at C3, s2 = pod, s4 = F + 0x2a0, s10 = F and the other callee-saved
   registers the walk reads their C3 values *)
Definition hd_A_post (cx : rs_scx rsegs) (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
  (x_own cx) (x_lyc cx) (x_Sc cx) (x_W cx) mem1 md1 (x_k cx) /\
same_io (x_mdc cx) md1 /\
(forall r, In r [2; 3; 4; 8; 9; 19; 23; 27] ->
 getr regs1 (Z_to_bv 5 r) = getr (x_regs cx) (Z_to_bv 5 r)) /\
getr regs1 (Z_to_bv 5 18) = w64 (e_pod (x_e cx)) /\
getr regs1 (Z_to_bv 5 20) = w64 (e_F (x_e cx) + 0x2a0) /\
getr regs1 (Z_to_bv 5 26) = w64 (e_F (x_e cx)) /\
(forall i, 0 <= i < e_len (x_e cx) -> aview rsegs (w_H (x_W cx)) mem1 (e_pod (x_e cx) + i) =
  aview rsegs (w_H (x_W cx)) (x_memc cx) (e_pp (x_e cx) + i)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (e_pod (x_e cx) <= a < e_pod (x_e cx) + e_len (x_e cx)) ->
 ~ (e_R (x_e cx) - ESTACK <= a < e_R (x_e cx)) ->
 aview rsegs (w_H (x_W cx)) mem1 a = aview rsegs (w_H (x_W cx)) (x_memc cx) a).

Lemma hd_A : forall cx inp (Q : world rsegs -> config -> Prop),
hd_c3 cx inp ->
(forall regs1 mem1 md1, hd_A_post cx regs1 mem1 md1 -> SRr rsegs (x_W cx) (cfg_at rsegs HD_AFTER_CPY regs1 mem1 md1) Q) ->
SRr rsegs (x_W cx) (cfg_at rsegs (hi_c3 role_himg_B) (x_regs cx) (x_memc cx) (x_mdc cx)) Q.
Proof using AMEMCPY.
intros cx inp Q HC K.
pose proof (hd_bounds cx inp HC) as (Pm16 & P4096 & Pc & Papp & Qm16 & Q4096 & Qc & Qapp & Hlen8 &
  Fm32 & F4096 & Fc & Fapp & HRlo & HRS & H47 & Hs16 & HSTK & Hceil).
destruct HC as [HJ Hev H2 H3 H4 HeS HR16 _ _ Hown HeF Hppin Hfl Hstrs Hcells Hrom Hppnew Hfsh
  A10 A8 A9 A19 A23 A24 A27 C18 C20 C38 C40 Cc0 Ce8 C120 C140
  Hlen Hpp Hpod0 Hpodin Hpodnew Hfrm].
destruct cx as [STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc RLO RHI e pos]; cbn in *.
set (pp := e_pp e) in *. set (pod := e_pod e) in *. set (len := e_len e) in *. set (R := e_R e) in *.
set (F := e_F e) in *. set (fl := e_fl e) in *.
unfold HDCEIL_HI, T_SEG_STK, ASTACK in Hceil, HRlo, HSTK. change Layout.PP_SIZE with 19744 in Pc.
pose proof (AR_laws_ok rsegs B) as LAWS. pose proof RPgSteps.rl_wx as Hwx.
pose proof RPgSteps.rl_segs_low as Hsegs.
assert (E32 : ew (Ereg regs [w64 F; w64 pp]) 32 = Z_to_bv 64 F)
  by (change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E33 : ew (Ereg regs [w64 F; w64 pp]) 33 = Z_to_bv 64 pp)
  by (change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E9 : bv_unsigned (ew (Ereg regs [w64 F; w64 pp]) 9) = R).
{ rewrite (ew_Ereg_nat regs _ 9 (Z_to_bv 5 9) eq_refl), A9. unfold w64. apply unsigned_lit_small. lia. }
assert (HS : st_ok rsegs (Ereg regs [w64 F; w64 pp]) (mkSS 0x82168 sr_atoms [hd_rA] None
  (mkFacts [(10%nat, mkAF 4096 HDCEIL_HI 4); (24%nat, mkAF 8 5440 0)] [] []))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 0x82168) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold hd_rA.
    apply (rm_ro_region rsegs _ (w_H W) memc 9 R 0x38 0x148 _ E9); [lia | lia |].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + apply (chunk_ok_val rsegs _ _ R 0x38 8 (SOff 32 0) F).
      * cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E32.
      * cbn. lia.
      * cbn. lia.
      * rewrite (Z.mod_small F) in C38 by lia. exact C38.
    + apply (chunk_ok_val rsegs _ _ R 0x140 8 (SOff 33 0) pp).
      * cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E33.
      * cbn. lia.
      * cbn. lia.
      * rewrite Z.add_0_r, (Z.mod_small pp) in C140 by lia. exact C140.
  - cbn. tauto.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. split; [|split; [|exact I]]; unfold afact_ok; cbn [af_lo af_hi af_al2].
    + rewrite (ew_Ereg_nat regs _ 10 (Z_to_bv 5 10) eq_refl), A10. unfold w64.
      rewrite unsigned_lit_small by (unfold HDCEIL_HI; lia). change (2 ^ 4) with 16. unfold HDCEIL_HI. lia.
    + rewrite (ew_Ereg_nat regs _ 24 (Z_to_bv 5 24) eq_refl), A24. unfold w64.
      rewrite unsigned_lit_small by lia. change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia. }
unfold cfg_at. cbn [hi_c3 role_himg_B]. change (w64 0x82168) with (Z_to_bv 64 0x82168).
aj_run_to hd_tbl_ok HS HJ HD_MEMCPY.
{ apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
assert (HAE : env_agree 32 (Ereg regs [w64 F; w64 pp]) (Ereg regs [w64 F; w64 pp]))
  by apply env_agree_refl.
lazymatch goal with HF : frame_of ?E0 ?rs0 _ (ms_mem ?ms) |- _ =>
  pose proof (frame_of_read_only E0 rs0 _ _ eq_refl HF) as Hmem end.
rewrite Hmem in HJ.
rreg HS (Z_to_bv 5 1) Ra1. rreg HS (Z_to_bv 5 10) Ra10. rreg HS (Z_to_bv 5 11) Ra11. rreg HS (Z_to_bv 5 12) Ra12.
rreg HS (Z_to_bv 5 18) Ra18.
assert (Ra20 : getr (ms_regs ms) (Z_to_bv 5 20) = w64 (F + 0x2a0)).
{ rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms _ HS).
  lazymatch type of HS with st_ok _ _ ?ss _ => let v := eval vm_compute in (sr_get (ss_regs ss) (Z_to_bv 5 20)) in
    change (sr_get (ss_regs ss) (Z_to_bv 5 20)) with v end.
  rewrite (sk_soff _ 32 F 0x2a0 E32). reflexivity. }
assert (Ra26 : getr (ms_regs ms) (Z_to_bv 5 26) = w64 F).
{ rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms _ HS).
  lazymatch type of HS with st_ok _ _ ?ss _ => let v := eval vm_compute in (sr_get (ss_regs ss) (Z_to_bv 5 26)) in
    change (sr_get (ss_regs ss) (Z_to_bv 5 26)) with v end.
  rewrite (sk_soff _ 32 F 0 E32), Z.add_0_r. reflexivity. }
assert (Rk : forall r, In r [2; 3; 4; 8; 9; 19; 23; 27] ->
  getr (ms_regs ms) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr. exact (YI04.regs_kept_of_st_ok rsegs _ _ _ regs [w64 F; w64 pp]
    (map (Z_to_bv 5) [2; 3; 4; 8; 9; 19; 23; 27]) HS HAE ltac:(vm_compute; reflexivity)
    (Z_to_bv 5 r) (in_map _ _ _ Hr)). }
pose proof (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) as Ems. cbn [ss_pc] in Ems.
rewrite Ems, Hmem.
assert (HAR : AR rsegs B lyc Sc W memc (with_vm_backing (m_vm_lazy mdc) mat mdc)) by exact (proj1 HJ).
assert (E2 : getr (ms_regs ms) (2%bv : bv 5) = getr regs (2%bv : bv 5))
  by (eapply (sk_reg_atom _ _ ms (w_H W) regs _ _ HS HAE); vm_compute; reflexivity).
assert (E3 : getr (ms_regs ms) (3%bv : bv 5) = getr regs (3%bv : bv 5))
  by (eapply (sk_reg_atom _ _ ms (w_H W) regs _ _ HS HAE); vm_compute; reflexivity).
assert (E4 : getr (ms_regs ms) (4%bv : bv 5) = getr regs (4%bv : bv 5))
  by (eapply (sk_reg_atom _ _ ms (w_H W) regs _ _ HS HAE); vm_compute; reflexivity).
assert (Hsp : spZ (ms_regs ms) = sp0 + (R - sp0)).
{ unfold spZ. rewrite E2, H2. unfold w64. rewrite unsigned_lit_small; [ring | lia]. }
destruct (rm_blk_ra rsegs B lyc Sc W memc _ pod len pod len HAR Hpodin ltac:(lia)
  ltac:(unfold req_size; destruct (Z.eqb_spec len 0); lia)) as (Hrad & Hhd).
destruct (rm_blk_ra rsegs B lyc Sc W memc _ pp Layout.PP_SIZE pp len HAR Hppin ltac:(lia)
  ltac:(unfold req_size; cbn; unfold Layout.PP_SIZE; lia)) as (Hrax & Hhx).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hppin) as (_ & _ & _ & _ & Hpres_pp & _).
assert (Hne : (pod, len) <> (pp, Layout.PP_SIZE)) by (intros Heq; injection Heq as _ Hl; unfold Layout.PP_SIZE in Hl; lia).
pose proof (sep_blocks rsegs B LAWS _ _ _ _ _ _ _ _ _ HAR Hpodin Hppin Hne) as Hdj.
unfold zdisjoint in Hdj. cbn [fst snd] in Hdj.
replace (req_size len) with len in Hdj by (unfold req_size; destruct (Z.eqb_spec len 0); lia).
replace (req_size Layout.PP_SIZE) with Layout.PP_SIZE in Hdj by reflexivity.
eapply SRr_bind.
{ eapply (RPgSteps.rl_intrin_at B LAWS OCpy 0x5116c AMEMCPY W (ms_regs ms) memc STK sp0 FP ly S W0 mem0 md0
    own lyc Sc _ k pod pp len (R - sp0) (Z_to_bv 64 0x8218c) HJ).
  - rewrite <- (sk_getr_z (ms_regs ms) 10 10 eq_refl), Ra10. exact A10.
  - rewrite <- (sk_getr_z (ms_regs ms) 11 11 eq_refl), Ra11. first [exact E33 | reflexivity].
  - rewrite <- (sk_getr_z (ms_regs ms) 12 12 eq_refl), Ra12. exact A24.
  - lia.
  - lia.
  - lia.
  - exact Hsp.
  - rewrite Zminus_mod, HR16, Hs16. reflexivity.
  - lia.
  - unfold ESTACK. lia.
  - rewrite E3. exact H3.
  - rewrite E4. exact H4.
  - rewrite <- (sk_getr_z (ms_regs ms) 1 1 eq_refl). exact Ra1.
  - vm_compute. reflexivity.
  - intros a Ha. split.
    + replace a with (pod + (a - pod)) by lia.
      apply (rl_fresh_awr_n STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own pod len Hpodin Hpodnew); lia.
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
split; [eapply same_io_trans; [apply RPgSteps.same_io_wvb | exact (same_io_materialized _ _ Hsame)]|].
split.
{ intros r Hr. rewrite (Hpres2 r) by (cbn [In] in Hr; unfold acallee_saved; lia). apply Rk. exact Hr. }
split.
{ rewrite (Hpres2 18) by (unfold acallee_saved; lia). rewrite Ra18. exact A10. }
split.
{ rewrite (Hpres2 20) by (unfold acallee_saved; lia). exact Ra20. }
split.
{ rewrite (Hpres2 26) by (unfold acallee_saved; lia). exact Ra26. }
split.
{ intros i Hi. exact (Hcpy i Hi). }
intros a Ha Hnp Hns. apply Hkeep; [exact Ha | exact Hnp |]. replace (sp0 + (R - sp0)) with R by lia. exact Hns.
Qed.

(* ===================== block B: 0x8218c .. the parse's return 0x821b4 ===================== *)
(* what C3 becomes when the parse returns (at its float state fx2): the parse's post, s2 = pod, s4 = F + 0x2a0,
   s5 = bit 0 of the flags byte, s8 = the flags byte, s10 = F, a0 = the parse's answer, every byte outside hdZ as at
   C3, the frame's shadow with role's granule in scope and the role cell *)
Definition hd_B_post (cx : rs_scx rsegs) (inp : list byte) (fx2 : YK11.FPState) ly2 S2 (W2 : world rsegs)
(regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) : Prop :=
rl_fxk [13; 14; 15] fx fx2 /\
ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
  (x_own cx) ly2 S2 W2 mem2 md2 (x_k cx) /\
frames S2 = frames (x_Sc cx) /\ Permutation (ablocks B ly2 S2) (ablocks B (x_lyc cx) (x_Sc cx)) /\
same_io (x_mdc cx) md2 /\ mo_le MT (x_Sc cx) S2 0 /\
(forall r, In r [2; 3; 4; 8; 9; 19; 23; 27] ->
 getr regs2 (Z_to_bv 5 r) = getr (x_regs cx) (Z_to_bv 5 r)) /\
getr regs2 (Z_to_bv 5 18) = w64 (e_pod (x_e cx)) /\
getr regs2 (Z_to_bv 5 20) = w64 (e_F (x_e cx) + 0x2a0) /\
getr regs2 (Z_to_bv 5 21) = w64 (Z.b2z (Z.testbit (e_fl (x_e cx)) 0)) /\
getr regs2 (Z_to_bv 5 24) = w64 (e_fl (x_e cx)) /\
getr regs2 (Z_to_bv 5 26) = w64 (e_F (x_e cx)) /\
getr regs2 (Z_to_bv 5 10) = w64 (snd (rs_PA rsegs cx (fst (pod_build inp)))) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ hdZ cx a ->
 aview rsegs (w_H W2) mem2 a = aview rsegs (w_H (x_W cx)) (x_memc cx) a) /\
rl_fsh rsegs (w_H W2) mem2 (e_F (x_e cx)) rs_PB /\
rs_role_at rsegs cx (fst (pod_build inp)) W2 mem2.

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
pose proof (rk_wf inp) as Hwf.
pose proof (Spa.buf_header _ Hwf) as (_ & _ & Hu32 & Hblen).
destruct HA as (HJ & Hio1 & Rk1 & R18 & R20 & R26 & Hcpy & Hkeep).
destruct HC as [_ Hev H2 H3 H4 HeS HR16 _ _ Hown HeF Hppin Hfl Hstrs Hcells Hrom Hppnew Hfsh
  A10 A8 A9 A19 A23 A24 A27 C18 C20 C38 C40 Cc0 Ce8 C120 C140
  Hlen Hpp Hpod0 Hpodin Hpodnew Hfrm].
unfold rl_len in Hlen.
set (rec := fst (pod_build inp)) in *.
destruct cx as [STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc RLO RHI e pos]; cbn in *.
set (pp := e_pp e) in *. set (pod := e_pod e) in *. set (len := e_len e) in *. set (R := e_R e) in *.
set (F := e_F e) in *. set (fl := e_fl e) in *.
unfold HDCEIL_HI, T_SEG_STK, ASTACK in Hceil, HRlo, HSTK. change Layout.PP_SIZE with 19744 in Pc.
pose proof (AR_laws_ok rsegs B) as LAWS. pose proof RPgSteps.rl_wx as Hwx.
pose proof RPgSteps.rl_segs_low as Hsegs.
assert (Hfq : 0 <= F / 8) by (apply Z.div_pos; lia).
assert (HFa : F + 1024 <= 0x7fff7000 \/ 0x10007fff8000 <= F)
  by (unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Fapp; lia).
assert (HQa : pod + len <= 0x7fff7000 \/ 0x10007fff8000 <= pod)
  by (unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Qapp; lia).
(* the env of the run and the four bases *)
set (E := Ereg regs1 [w64 fl]).
assert (E9 : bv_unsigned (ew E 9) = R).
{ subst E. rewrite (ew_Ereg_nat regs1 _ 9 (Z_to_bv 5 9) eq_refl), (Rk1 9 ltac:(cbn; tauto)).
  refine (eq_trans (f_equal (@bv_unsigned 64) A9) _). unfold w64. apply unsigned_lit_small. lia. }
assert (E19 : bv_unsigned (ew E 19) = shadow_addr F).
{ subst E. rewrite (ew_Ereg_nat regs1 _ 19 (Z_to_bv 5 19) eq_refl), (Rk1 19 ltac:(cbn; tauto)).
  refine (eq_trans (f_equal (@bv_unsigned 64) A19) _). unfold w64. apply unsigned_lit_small.
  unfold shadow_addr, SHADOW_OFF. lia. }
assert (E20 : bv_unsigned (ew E 20) = F + 0x2a0).
{ subst E. rewrite (ew_Ereg_nat regs1 _ 20 (Z_to_bv 5 20) eq_refl), R20. unfold w64. apply unsigned_lit_small. lia. }
assert (E32 : ew E 32 = Z_to_bv 64 fl) by (subst E; change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E18 : ew E 18 = Z_to_bv 64 pod) by (subst E; rewrite (ew_Ereg_nat regs1 _ 18 (Z_to_bv 5 18) eq_refl); exact R18).
(* the frame's bytes and shadow bytes are present *)
assert (HAR1 : AR rsegs B lyc Sc W mem1 md1) by exact (proj1 HJ).
assert (Hfin : In (4, pos) (frames Sc)).
{ pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _). rewrite Hfrs. apply in_or_app. left. exact Hown. }
destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR1 Hfin) as (_ & _ & Hfb & Hfs).
rewrite <- HeF in Hfb, Hfs. change (fs_frame_bytes 4 / 8) with 128 in Hfs. change (fs_frame_bytes 4) with 1024 in Hfb.
(* every byte outside the pod block and [R - ESTACK, R) is as at C3 *)
assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (pod <= a < pod + len) -> ~ (R - ESTACK <= a < R) ->
  aview rsegs (w_H W) mem1 a = aview rsegs (w_H W) memc a) by exact Hkeep.
assert (HS : st_ok rsegs E (mkSS 0x8218c sr_atoms [hd_rB0; hd_rB1; hd_rB2] None (mkFacts [] [] []))
  (restrict (w_H W) (mkst regs1 (Z_to_bv 64 0x8218c) mem1 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; [ | | | apply Forall_nil].
    + unfold hd_rB0. apply (rm_rw_region rsegs E (w_H W) mem1 19 (shadow_addr F) 0x54 0x55 0x54 0x55 [] E19);
        [unfold shadow_addr, SHADOW_OFF; lia | unfold shadow_addr, SHADOW_OFF; lia | | apply Forall_nil].
      intros o Ho. exact (proj1 (Hfs o ltac:(lia))).
    + unfold hd_rB1. apply (rm_ro_region rsegs E (w_H W) mem1 9 R 0x40 0x48 _ E9); [lia | lia |].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val rsegs E _ R 0x40 8 (SOff 32 0) fl).
      * cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E32.
      * cbn. lia.
      * cbn. lia.
      * rewrite (Z.mod_small fl) in C40 by lia.
        eapply (val_mem_kept rsegs); [|exact C40].
        intros kk Hkk. cbn in Hkk. apply KA; [lia | lia | unfold ESTACK; lia].
    + unfold hd_rB2. apply (rm_rw_region rsegs E (w_H W) mem1 20 (F + 0x2a0) 0 4 0 4 [] E20); [lia | lia | | apply Forall_nil].
      intros o Ho. exact (proj1 (Hfb (F + 0x2a0 + o) ltac:(lia))).
  - cbn [pairwise_disjoint all_disjoint hd_rB0 hd_rB1 hd_rB2 extent_disjoint YP09.r_base YP09.r_lo YP09.r_hi base_val].
    unfold extent_disjoint, hd_rB0, hd_rB1, hd_rB2. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    fold E. rewrite E9, E19, E20. unfold shadow_addr, SHADOW_OFF. repeat split; lia.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. tauto. }
unfold cfg_at. change (w64 HD_AFTER_CPY) with (Z_to_bv 64 0x8218c).
aj_run_to hd_tbl_ok HS HJ HD_PARSE.
{ cbn [ss_mem].
  eapply (RPgSteps.rl_awr_ok_fsh _ _ _ _ _ _ _ _ _ _ 19%nat pos);
    [reflexivity | rewrite E19; f_equal; exact HeF | exact Hown | cbn; lia | cbn; lia |].
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply (RPgSteps.rl_awr_ok_fobj _ _ _ _ _ _ _ _ _ _ 20%nat pos 0x2a0);
    [reflexivity | rewrite E20; lia | exact Hown | cbn; lia | cbn; lia |].
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
  rewrite (U_atom E 32 fl E32 ltac:(lia)), (U_atom E 18 pod E18 ltac:(lia)).
  apply hd_sel; lia. }
assert (Rb21 : getr (ms_regs ms) 21 = w64 (Z.b2z (Z.testbit fl 0))).
{ rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms _ HS).
  lazymatch type of HS with st_ok _ _ ?ss _ => let v := eval vm_compute in (sr_get (ss_regs ss) (21%bv : bv 5)) in
    change (sr_get (ss_regs ss) (21%bv : bv 5)) with v end.
  rewrite denot_lit_U. unfold w64. f_equal.
  rewrite !U_SAlu, !U_SLit. cbn [zalu_raw].
  rewrite (U_atom E 32 fl E32 ltac:(lia)). apply hd_bit; lia. }
assert (Rb24 : getr (ms_regs ms) 24 = w64 fl).
{ rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms _ HS).
  lazymatch type of HS with st_ok _ _ ?ss _ => let v := eval vm_compute in (sr_get (ss_regs ss) (24%bv : bv 5)) in
    change (sr_get (ss_regs ss) (24%bv : bv 5)) with v end.
  rewrite (sk_soff _ 32 fl 0 E32), Z.add_0_r. reflexivity. }
assert (Rb11 : getr (ms_regs ms) 11 = getr regs1 (Z_to_bv 5 20))
  by (eapply (sk_reg_is _ _ ms (w_H W) regs1 _ _ _ 20%nat HS HAE); [vm_compute; reflexivity | reflexivity]).
assert (Rkb : forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 23; 26; 27] ->
  getr (ms_regs ms) (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)).
{ intros r Hr. exact (YI04.regs_kept_of_st_ok rsegs _ _ _ regs1 [w64 fl]
    (map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 19; 20; 23; 26; 27]) HS HAE ltac:(vm_compute; reflexivity)
    (Z_to_bv 5 r) (in_map _ _ _ Hr)). }
assert (Rx : forall r, In r [2; 3; 4; 8; 9; 19; 23; 27] ->
  getr (ms_regs ms) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr. rewrite Rkb by (cbn [In] in Hr |- *; tauto). apply Rk1. cbn [In] in Hr |- *; tauto. }
assert (HspP : spZ (ms_regs ms) = R).
{ unfold spZ. rewrite <- (sk_getr_z (ms_regs ms) 2 2 eq_refl), (Rx 2 ltac:(cbn; tauto)), (sk_getr_z regs 2 2 eq_refl), H2.
  unfold w64. apply unsigned_lit_small. lia. }
(* the memory at the call: role's shadow byte, the role cell, and every byte outside them as before *)
assert (Hsb : val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) (shadow_addr F + 0x54) 1 4).
{ lazymatch type of HS with st_ok _ _ ?ss _ =>
    let r := eval vm_compute in (nth_error (ss_mem ss) 0) in
    lazymatch r with Some ?rg =>
      assert (Hr : nth_error (ss_mem ss) 0 = Some rg) by (vm_compute; reflexivity);
      pose proof (RPgSteps.rl_region_nth _ _ _ 0 _ _ HS Hr) as Hreg end end.
  exact (sk_field_of_region _ _ _ _ _ _ _ _ _ 0x54 1 (SLit 4) 4 Hreg E19 ltac:(cbn; tauto) eq_refl
    ltac:(cbn; lia) ltac:(cbn; lia)). }
assert (Hrc : val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) (F + 0x2a0) 4 0x5a).
{ lazymatch type of HS with st_ok _ _ ?ss _ =>
    let r := eval vm_compute in (nth_error (ss_mem ss) 2) in
    lazymatch r with Some ?rg =>
      assert (Hr : nth_error (ss_mem ss) 2 = Some rg) by (vm_compute; reflexivity);
      pose proof (RPgSteps.rl_region_nth _ _ _ 2 _ _ HS Hr) as Hreg end end.
  pose proof (sk_field_of_region _ _ _ _ _ _ _ _ _ 0 4 (SLit 0x5a) 0x5a Hreg E20 ltac:(cbn; tauto) eq_refl
    ltac:(cbn; lia) ltac:(cbn; lia)) as Hv. rewrite Z.add_0_r in Hv. exact Hv. }
assert (KB : forall a, 0 <= a < 2 ^ 64 -> a <> shadow_addr F + 0x54 -> ~ (F + 0x2a0 <= a < F + 0x2a4) ->
  aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) mem1 a).
{ intros a Ha H1 H2'. unfold aview, mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
  rewrite unsigned_lit_small by exact Ha. intros (r & Hin & Hr). cbn [In] in Hin.
  destruct Hin as [<-|[<-|[<-|[]]]]; cbn [hd_rB0 hd_rB1 hd_rB2 YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
  [rewrite E19 in Hr | rewrite E9 in Hr | rewrite E20 in Hr]; lia. }
assert (KP : forall a, 0 <= a < 2 ^ 64 ->
  ~ hdZ (RSCx rsegs STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc RLO RHI e pos) a ->
  aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) memc a).
{ intros a Ha Hz. unfold hdZ in Hz. cbn [x_e] in Hz. fold pod len R F in Hz.
  rewrite KB; [| exact Ha | intros ->; apply Hz; right; right; left; reflexivity
             | intros Hr; apply Hz; right; right; right; exact Hr].
  apply KA; [exact Ha | intros Hp; apply Hz; left; exact Hp
             | intros Hs; apply Hz; right; left; unfold ESTACK in Hs; unfold T_SEG_STK, ASTACK; lia]. }
(* the frame's shadow at the call: the prologue's with role's granule in scope *)
assert (Hfsh1 : rl_fsh rsegs (w_H W) mem1 F role_B_shA).
{ apply (rm_fsh_kept rsegs (w_H W) memc (w_H W) mem1 F role_B_shA Hfsh).
  intros i Hi. change (length role_B_shA) with 88%nat in Hi. cbn in Hi.
  apply KA; unfold shadow_addr, SHADOW_OFF; [lia | lia | unfold ESTACK; lia]. }
assert (HfshP : rl_fsh rsegs (w_H W) (ms_mem ms) F rs_PB).
{ unfold rs_PB. rewrite <- (rm_sh_role_in false false false false false false false), rm_sh_P0.
  change (hi_shA role_himg_B) with role_B_shA.
  apply (rm_fsh_set rsegs (w_H W) mem1 (w_H W) (ms_mem ms) F role_B_shA 84 1 4 Hfsh1).
  - intros i Hi. cbn in Hi. assert (i = 84) as -> by lia.
    apply (rm_val1_aview rsegs). exact Hsb. lia.
  - intros i Hi Hn. change (length role_B_shA) with 88%nat in Hi. cbn in Hi, Hn.
    apply KB; unfold shadow_addr, SHADOW_OFF; lia. }
(* the second block holds the record's bytes *)
assert (Hbytes : rm_bytes rsegs (w_H W) (ms_mem ms) pod (buf rec)).
{ unfold rs_pp_at, rs_u8s in Hpp. fold (rm_bytes rsegs (w_H W) memc pp (pp_bytes rec)) in Hpp.
  unfold pp_bytes, pp_image in Hpp. apply rm_bytes_app in Hpp. destruct Hpp as (Hb & _).
  apply (rm_bytes_kept rsegs (w_H W) mem1).
  - apply (rm_memcpy_bytes rsegs (w_H W) memc (w_H W) mem1 pp pod (buf rec) Hb).
    intros i Hi. apply Hcpy. lia.
  - pose proof (sep_block_frame rsegs B LAWS _ _ _ _ _ _ _ _ _ HAR1 Hpodin Hfin) as Hsep.
    unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. rewrite <- HeF in Hsep. change (fs_frame_bytes 4) with 1024 in Hsep.
    replace (req_size len) with len in Hsep by (unfold req_size; destruct (Z.eqb_spec len 0); lia).
    intros x Hx. apply KB; [lia | unfold shadow_addr, SHADOW_OFF; lia | lia]. }
(* the parse's string and doubles *)
assert (KS : forall x, hd_szone x -> aview rsegs (w_H W) (ms_mem ms) x = aview rsegs (w_H W) memc x).
{ intros x Hx. destruct (Hsz x Hx) as [Hx64 Hnz]. exact (KP x Hx64 Hnz). }
assert (Hkey : rl_cstr rsegs (w_H W) (ms_mem ms) RPgParseBase.A_KEY (map (fun x : byte => bv_unsigned x) Role.ROLE_KEY)).
{ rewrite role_B_key_text. apply (hd_cstr_kept _ _ _ _ _ _ KS); [unfold RPgParseBase.A_KEY; lia | cbn; unfold RPgParseBase.A_KEY; lia |].
  rewrite Forall_forall in Hstrs. apply (Hstrs (0x215e0, _)). unfold role_B_strs. cbn [In].
  repeat (first [left; reflexivity | right]). }
assert (Hdcs : rl_ro_cells rsegs (w_H W) (ms_mem ms) RPgParseBase.role_B_dcs).
{ unfold rl_ro_cells in Hcells |- *. rewrite Forall_forall in Hcells. unfold RPgParseBase.role_B_dcs.
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
  (eapply (val_mem_kept rsegs); [intros kk Hkk; apply KS; left; cbn in Hkk; lia |]);
  (refine (Hcells (_, _) _); unfold role_B_cells; cbn [In]; repeat (first [left; reflexivity | right])). }
pose proof (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) as Ems. cbn [ss_pc] in Ems.
rewrite Ems.
destruct (rm_blk_ra rsegs B lyc Sc W (ms_mem ms) _ pod len pod len (proj1 HJ) Hpodin ltac:(lia)
  ltac:(unfold req_size; destruct (Z.eqb_spec len 0); lia)) as (Hrad & Hhd).
eapply SRr_bind.
{ apply (PARSE STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms) (with_vm_backing (m_vm_lazy md1) mat md1) k
    (ms_regs ms) (Z.testbit fl 0) pod (F + 0x2a0) (buf rec)).
  - unfold rl_pre. split; [exact HJ|].
    split; [rewrite Rb1; vm_compute; reflexivity|].
    split; [unfold raZ; rewrite Rb1; unfold w64, HD_AFTER_PARSE; rewrite unsigned_lit_small; lia|].
    split; [rewrite <- (sk_getr_z (ms_regs ms) 3 3 eq_refl), (Rx 3 ltac:(cbn; tauto)), (sk_getr_z regs 3 3 eq_refl); exact H3|].
    split; [rewrite <- (sk_getr_z (ms_regs ms) 4 4 eq_refl), (Rx 4 ltac:(cbn; tauto)), (sk_getr_z regs 4 4 eq_refl); exact H4|].
    rewrite HspP. unfold T_parse_STK, ESTACK. split; [exact HR16|]. split; [lia|]. split; [lia | exact Hev].
  - exact Rb10.
  - rewrite Rb11, R20. reflexivity.
  - intros _. rewrite <- Hlen. split; [lia|]. split; [exact Qm16|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [exact Hbytes|]. split; [exact Hrad|]. split; [apply Hhd; lia|].
    split; [eapply amem_range_of_block; [exact LAWS | exact (proj1 HJ) | exact Hpodin | lia | unfold req_size; destruct (Z.eqb_spec len 0); lia]|].
    left. rewrite HspP. unfold T_parse_STK, ESTACK. lia.
  - unfold rl_wcell. split.
    + right. exists 4, pos. split; [exact Hown|]. split; [lia|]. rewrite <- HeF. change (fs_frame_bytes 4) with 1024. lia.
    + right. rewrite HspP. unfold T_parse_STK, ESTACK. lia.
  - rewrite F8. replace (8 * (F / 8) + 0x2a0) with ((2 * (F / 8) + 0xa8) * 4) by ring. apply Z.mod_mul. lia.
  - replace (F + 0x2a0) with (F + RM_ROLE + 0) by (unfold RM_ROLE; ring).
    apply (rm_B_ra_role rsegs (w_H W) (ms_mem ms) F false false false false false false 0 4); [|exact F8m | lia | lia].
    exact HfshP.
  - exact Hkey.
  - exact Hdcs.
  - exact Hfrm. }
cbv beta. intros W2 c2 _ (fx2 & ly2 & S2 & regs2 & mem2 & md2 & -> & HFX & HJ2 & Hpres & Hfr2 & Hperm & Hio2 & Hmo & Hkp & H10 & HRc).
rewrite Rb1. apply (K fx2 ly2 S2 W2 regs2 mem2 md2).
split; [exact HFX|].
split; [exact HJ2|].
split; [exact Hfr2|].
split; [exact Hperm|].
split; [eapply same_io_trans; [exact Hio1|]; eapply same_io_trans; [apply RPgSteps.same_io_wvb | exact Hio2]|].
split; [exact Hmo|].
split.
{ intros r Hr. rewrite (Hpres r) by (cbn [In] in Hr; unfold acallee_saved; lia). apply Rx. exact Hr. }
split.
{ rewrite (Hpres 18) by (unfold acallee_saved; lia). rewrite Rkb by (cbn; tauto). exact R18. }
split.
{ rewrite (Hpres 20) by (unfold acallee_saved; lia). rewrite Rkb by (cbn; tauto). exact R20. }
split.
{ rewrite (Hpres 21) by (unfold acallee_saved; lia). rewrite (sk_getr_z (ms_regs ms) 21 21 eq_refl). exact Rb21. }
split.
{ rewrite (Hpres 24) by (unfold acallee_saved; lia). rewrite (sk_getr_z (ms_regs ms) 24 24 eq_refl). exact Rb24. }
split.
{ rewrite (Hpres 26) by (unfold acallee_saved; lia). rewrite Rkb by (cbn; tauto). exact R26. }
split.
{ rewrite (sk_getr_z regs2 10 10 eq_refl). exact H10. }
assert (KQ : forall a, 0 <= a < 2 ^ 64 -> ~ (R - T_parse_STK <= a < R) -> ~ (F + 0x2a0 <= a < F + 0x2a4) ->
  aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W) (ms_mem ms) a).
{ intros a Ha H1 H2'. apply Hkp; [exact Ha | rewrite HspP; exact H1 | intros (_ & Hq); apply H2'; lia]. }
split.
{ intros a Ha Hz. rewrite KQ; [| exact Ha | | ].
  - apply KP; [exact Ha | exact Hz].
  - intros Hs. apply Hz. right. left. cbn [x_e]. unfold T_parse_STK, ESTACK in Hs. unfold T_SEG_STK, ASTACK. lia.
  - intros Hr. apply Hz. right. right. right. exact Hr. }
split.
{ apply (rm_fsh_kept rsegs (w_H W) (ms_mem ms) (w_H W2) mem2 F rs_PB HfshP).
  intros i Hi. change (length rs_PB) with 88%nat in Hi. cbn in Hi.
  apply KQ; unfold shadow_addr, SHADOW_OFF, T_parse_STK, ESTACK; lia. }
unfold rs_role_at, rs_PA. cbn [x_e]. fold F fl rec.
destruct (fst (rl_parse_res (Z.testbit fl 0) (buf rec))) as [w|] eqn:Ef.
- first [exact HRc | rewrite Ef in HRc; exact HRc].
- cbn [rs_rcell]. eapply (val_mem_kept rsegs); [|exact Hrc].
  intros kk Hkk. apply Hkp; [lia | rewrite HspP; unfold T_parse_STK, ESTACK; lia | intros (Hn & _); exact (Hn eq_refl)].
Qed.

(* ===================== the facts the three exits share ===================== *)
(* at an exit of the last run: rs_chk_base, the list hd_L and the role cell, at the memory of the parse's return
   (the last run stores nothing) *)
Lemma hd_common : forall cx inp (fx2 : YK11.FPState) ly2 S2 W2 regs2 mem2 md2 regsF mdF,
hd_c3 cx inp -> hd_B_post cx inp fx2 ly2 S2 W2 regs2 mem2 md2 ->
ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
  (x_own cx) ly2 S2 W2 mem2 mdF (x_k cx) ->
same_io md2 mdF ->
(forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 24; 26; 27] ->
 getr regsF (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r)) ->
getr regsF (Z_to_bv 5 25) = getr regs2 (Z_to_bv 5 10) ->
getr regsF (Z_to_bv 5 22) = w64 (e_pp (x_e cx)) ->
@rs_chk_base fx rc SK rsegs B MT cx fx2 (fst (pod_build inp)) ly2 S2 W2 regsF mem2 mdF /\
rs_at_cx rsegs cx W2 mem2 regsF (hd_L cx (fst (pod_build inp))) /\
rs_role_at rsegs cx (fst (pod_build inp)) W2 mem2.
Proof.
intros cx inp fx2 ly2 S2 W2 regs2 mem2 md2 regsF mdF HC HBp HJF HioF HrF H25 H22.
pose proof (hd_nz cx inp HC) as (NR & NP & NI).
pose proof (hd_bounds cx inp HC) as (Pm16 & P4096 & Pc & Papp & Qm16 & Q4096 & Qc & Qapp & Hlen8 &
  Fm32 & F4096 & Fc & Fapp & HRlo & HRS0 & H47 & Hs16 & HSTK0 & Hceil).
destruct (hd_m32 _ Fm32) as (F8 & _).
assert (Hfq : 0 <= e_F (x_e cx) / 8) by (apply Z.div_pos; lia).
pose proof (c3_S cx inp HC) as HS0.
unfold T_SEG_STK, ASTACK in HRlo. unfold HDCEIL_HI in Hceil.
pose proof (rk_wf inp) as Hwf.
destruct HBp as (HFX & HJ2 & Hfr2 & Hperm & Hio2 & Hmo & Rk2 & R18 & R20 & R21 & R24 & R26 & R10 & K2 & Hfsh2 & Hrole2).
assert (Hx : forall r, In r [2; 3; 4; 8; 9; 19; 27] ->
  getr regsF (Z_to_bv 5 r) = getr (x_regs cx) (Z_to_bv 5 r)).
{ intros r Hr. rewrite HrF by (cbn [In] in Hr |- *; tauto). apply Rk2. cbn [In] in Hr |- *; tauto. }
assert (KC : forall o v, 0 <= o -> o + 8 <= 0x200 ->
  val_mem rsegs (mrestrict (w_H (x_W cx)) (x_memc cx)) (e_R (x_e cx) + o) 8 v ->
  val_mem rsegs (mrestrict (w_H W2) mem2) (e_R (x_e cx) + o) 8 v).
{ intros o v Ho Ho8 Hv. eapply (val_mem_kept rsegs); [|exact Hv]. intros kk Hkk. cbn in Hkk.
  apply K2; [lia|]. apply NR. lia. }
destruct HC as [HJ Hev H2 H3 H4 HeS HR16 HRS HSTK Hown HeF Hppin Hfl Hstrs Hcells Hrom Hppnew Hfsh
  A10 A8 A9 A19 A23 A24 A27 C18 C20 C38 C40 Cc0 Ce8 C120 C140
  Hlen Hpp Hpod0 Hpodin Hpodnew Hfrm].
unfold rl_len in Hlen.
split; [|split].
- split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]].
  + split; [exact HJF|].
    split; [intros r Hr; apply Hx; cbn [In]; lia|].
    split; [exact Hfr2|]. split; [exact Hperm|].
    split; [eapply same_io_trans; [exact Hio2 | exact HioF]|]. split; [exact Hmo|].
    intros a Ha Hs He. apply K2; [exact Ha|]. intros Hz. destruct (hdZ_E2 cx a Hz) as [Hz'|Hz']; [|exact (He Hz')].
    apply Hs. unfold spZ. rewrite H2. unfold w64. rewrite unsigned_lit_small; [exact Hz'|]. lia.
  + destruct HFX as [HFk HFf]. split; [|exact HFf]. intros k0 Hk. apply HFk. intros Hin. apply Hk. right. exact Hin.
  + unfold rs_fsh_at. exact Hfsh2.
  + intros a Ha.
    assert (Hia : in_img rsegs a) by (destruct Ha as (sg' & Hsg' & _ & Hr'); exists sg'; split; [exact Hsg' | exact Hr']).
    pose proof (RPgSteps.rl_segs_low a Hia) as Hl.
    rewrite <- (Hrom a Ha). apply K2; [unfold kLowMemEnd in Hl; lia | exact (NI a Hia)].
  + unfold rs_pp_at, rs_u8s in Hpp |- *.
    fold (rm_bytes rsegs (w_H (x_W cx)) (x_memc cx) (e_pp (x_e cx)) (pp_bytes (fst (pod_build inp)))) in Hpp.
    fold (rm_bytes rsegs (w_H W2) mem2 (e_pp (x_e cx)) (pp_bytes (fst (pod_build inp)))).
    apply (rm_bytes_kept rsegs _ _ _ _ _ _ Hpp). intros x Hx'.
    assert (Hlp : Z.of_nat (length (pp_bytes (fst (pod_build inp)))) = Layout.PP_SIZE).
    { pose proof (Spa.buf_header _ Hwf) as (_ & _ & _ & Hbl).
      apply Layout.length_pp_image; [unfold Layout.POD_BUF_MAX; lia | exact (rk_nent_le _ Hwf) |].
      pose proof (rk_ents_wf _ Hwf) as Hew. rewrite Forall_forall in Hew |- *. intros x0 Hx0.
      destruct (Hew x0 Hx0) as (_ & Hb & Hs). rewrite Hb. lia. }
    rewrite Hlp in Hx'.
    apply K2; [change Layout.PP_SIZE with 19744 in *; lia|]. apply NP. exact Hx'.
  + exact Hwf.
  + exact Hlen.
  + exact Hpod0.
  + exact Hpodin.
  + exact Hpodnew.
- unfold rs_at_cx, rs_at, hd_L, rs_L_chk. cbn [app].
  repeat (apply Forall_cons; [cbn [fst snd rl_at rl_xv] |]); [..|apply Forall_nil].
  + rewrite Hx by (cbn; tauto). exact A8.
  + rewrite Hx by (cbn; tauto). exact A9.
  + rewrite Hx by (cbn; tauto). exact A19.
  + rewrite Hx by (cbn; tauto). exact A27.
  + rewrite HrF by (cbn; tauto). exact R18.
  + rewrite HrF by (cbn; tauto). exact R20.
  + apply KC; [lia | lia | exact C20].
  + apply KC; [lia | lia | exact C40].
  + rewrite H25. exact R10.
  + exact H22.
  + rewrite HrF by (cbn; tauto). exact R24.
  + rewrite HrF by (cbn; tauto). exact R26.
  + apply KC; [lia | lia | exact C38].
  + apply KC; [lia | lia | exact Ce8].
  + apply KC; [lia | lia | exact C120].
  + apply KC; [lia | lia | rewrite Z.add_0_r in C140; exact C140].
  + apply KC; [lia | lia | exact Cc0].
- exact Hrole2.
Qed.

(* at an exit of the last run: the state is written with its pc *)
Ltac hd_exit HS :=
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?m) =>
    let Ems := fresh "Ems" in
    pose proof (st_ok_restrict_mkst rsegs _ _ _ m HS eq_refl) as Ems; cbn [ss_pc] in Ems; rewrite Ems
  end.

(* ===================== block C: 0x821b4 .. E 0x821dc / MAL 0x824f8 / T 0x82504 ===================== *)
Lemma hd_C : forall cx inp POST (fx2 : YK11.FPState) ly2 S2 W2 regs2 mem2 md2,
hd_c3 cx inp -> hd_B_post cx inp fx2 ly2 S2 W2 regs2 mem2 md2 ->
@rs_from_E fx rc SK rsegs B MT cx POST -> @rs_from_MAL fx rc SK rsegs B MT cx POST ->
@rs_from_T fx rc SK rsegs B MT cx POST ->
SRr rsegs W2 (@cfg_at fx2 rsegs HD_AFTER_PARSE regs2 mem2 md2) POST.
Proof.
intros cx inp POST fx2 ly2 S2 W2 regs2 mem2 md2 HC HBp HE HM HT.
pose proof (hd_bounds cx inp HC) as (Pm16 & P4096 & Pc & Papp & Qm16 & Q4096 & Qc & Qapp & Hlen8 &
  Fm32 & F4096 & Fc & Fapp & HRlo & HRS & H47 & Hs16 & HSTK & Hceil).
pose proof (hd_nz cx inp HC) as (NR & NP & NI).
pose proof (rk_wf inp) as Hwf.
pose proof (Spa.buf_header _ Hwf) as (_ & _ & _ & Hblen).
pose proof HBp as (HFX & HJ2 & Hfr2 & Hperm & Hio2 & Hmo & Rk2 & R18 & R20 & R21 & R24 & R26 & R10 & K2 & Hfsh2 & Hrole2).
pose proof (AR_laws_ok rsegs B) as LAWS. pose proof RPgSteps.rl_wx as Hwx.
pose proof RPgSteps.rl_segs_low as Hsegs.
pose proof (c3_s7 cx inp HC) as S7. pose proof (c3_s11 cx inp HC) as S11r. pose proof (c3_s1 cx inp HC) as S1.
pose proof (c3_c18 cx inp HC) as C18. pose proof (c3_c140 cx inp HC) as C140.
pose proof (c3_pp cx inp HC) as Hpp. pose proof (c3_ppin cx inp HC) as Hppin.
set (rec := fst (pod_build inp)) in *.
set (pp := e_pp (x_e cx)) in *. set (fl := e_fl (x_e cx)) in *. set (F := e_F (x_e cx)) in *.
set (R := e_R (x_e cx)) in *. set (pod := e_pod (x_e cx)) in *.
unfold HDCEIL_HI, T_SEG_STK, ASTACK in Hceil, HRlo, HSTK. change Layout.PP_SIZE with 19744 in Pc.
(* pp->corrupt and its granule's shadow at the parse's return; pp + 0x4008 in R+0x18, pp in R+0x140 *)
assert (H23 : getr regs2 (Z_to_bv 5 23) = w64 (pp + 0x4d18)) by (rewrite Rk2 by (cbn; tauto); exact S7).
assert (H27 : getr regs2 (Z_to_bv 5 27) = w64 SHADOW_OFF) by (rewrite Rk2 by (cbn; tauto); exact S11r).
assert (H9 : getr regs2 (Z_to_bv 5 9) = w64 R) by (rewrite Rk2 by (cbn; tauto); exact S1).
assert (Hv18 : val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0x18) 8 (pp + 0x4008)).
{ rewrite (Z.mod_small (pp + 0x4008)) in C18 by lia.
  eapply (val_mem_kept rsegs); [|exact C18]. intros kk Hkk. cbn in Hkk. apply K2; [lia|]. apply NR. lia. }
assert (Hv140 : val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0x140) 8 pp).
{ rewrite Z.add_0_r, (Z.mod_small pp) in C140 by lia.
  eapply (val_mem_kept rsegs); [|exact C140]. intros kk Hkk. cbn in Hkk. apply K2; [lia|]. apply NR. lia. }
assert (Hpp2 : rm_bytes rsegs (w_H W2) mem2 pp (pp_bytes rec)).
{ unfold rs_pp_at, rs_u8s in Hpp. fold rec pp in Hpp.
  fold (rm_bytes rsegs (w_H (x_W cx)) (x_memc cx) pp (pp_bytes rec)) in Hpp.
  apply (rm_bytes_kept rsegs _ _ _ _ _ _ Hpp). intros x Hx.
  assert (Hlp : Z.of_nat (length (pp_bytes rec)) = Layout.PP_SIZE).
  { apply Layout.length_pp_image; [unfold Layout.POD_BUF_MAX; lia | exact (rk_nent_le _ Hwf) |].
    pose proof (rk_ents_wf _ Hwf) as Hew. rewrite Forall_forall in Hew |- *. intros x0 Hx0.
    destruct (Hew x0 Hx0) as (_ & Hb & Hs). rewrite Hb. lia. }
  rewrite Hlp in Hx. apply K2; [change Layout.PP_SIZE with 19744 in *; lia|]. apply NP. exact Hx. }
assert (Hcor : val_mem rsegs (mrestrict (w_H W2) mem2) (pp + 0x4d18) 4 (Z.b2z (corrupt rec))).
{ apply (rm_pp_corrupt rsegs (buf rec) (is_props rec) (has_params rec) (params_struct rec) (ents rec) (corrupt rec));
    [unfold Layout.POD_BUF_MAX; lia | exact (rk_nent_le _ Hwf) | | exact Hpp2].
  pose proof (rk_ents_wf _ Hwf) as Hew. rewrite Forall_forall in Hew |- *. intros x0 Hx0.
  destruct (Hew x0 Hx0) as (_ & Hb & Hs). rewrite Hb. lia. }
assert (Hppin2 : In (pp, Layout.PP_SIZE) (ablocks B ly2 S2))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); exact Hppin).
destruct (rm_blk_ra rsegs B ly2 S2 W2 mem2 md2 pp Layout.PP_SIZE (pp + 0x4d18) 8 (proj1 HJ2) Hppin2 ltac:(lia)
  ltac:(unfold req_size, Layout.PP_SIZE; cbn; lia)) as (Hra & _).
assert (Hpa : pp + 19744 <= 0x7fff7000 \/ 0x10007fff8000 <= pp)
  by (unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, Layout.PP_SIZE in Papp; lia).
(* the env of the run: pp (atom 32) and pp + 0x4008 (atom 33) as its extra atoms *)
assert (E32 : ew (Ereg regs2 [w64 pp; w64 (pp + 0x4008)]) 32 = Z_to_bv 64 pp)
  by (change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E33 : ew (Ereg regs2 [w64 pp; w64 (pp + 0x4008)]) 33 = Z_to_bv 64 (pp + 0x4008))
  by (change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; reflexivity).
(* the shadow entry of the check *)
assert (SHOK : sh_ok rsegs HDBx HDSH (Ereg regs2 [w64 pp; w64 (pp + 0x4008)]) (mrestrict (w_H W2) mem2)).
{ apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range rsegs (w_H W2) mem2 (Ereg regs2 [w64 pp; w64 (pp + 0x4008)]) HDBx 23 (pp + 0x4d18) 8
    (pp + 0x4d18) 0 8 Hra).
  - apply (U_atom _ 27 SHADOW_OFF); [rewrite (ew_Ereg_nat regs2 _ 27 (Z_to_bv 5 27) eq_refl); exact H27 | unfold SHADOW_OFF; lia].
  - apply (U_atom _ 23 (pp + 0x4d18)); [rewrite (ew_Ereg_nat regs2 _ 23 (Z_to_bv 5 23) eq_refl); exact H23 | lia].
  - lia.
  - lia.
  - intros x Hx. cbn in Hx. unfold SHADOW_OFF. lia. }
assert (HAE : env_agree 32 (Ereg regs2 [w64 pp; w64 (pp + 0x4008)]) (Ereg regs2 [w64 pp; w64 (pp + 0x4008)]))
  by apply env_agree_refl.
(* the registers every exit carries *)
assert (KR : forall (fx' : YK11.FPState) ss ms, @st_ok rsegs fx' (Ereg regs2 [w64 pp; w64 (pp + 0x4008)]) ss (restrict (w_H W2) ms) ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0))
    (map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 19; 20; 24; 26; 27]) = true ->
  forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 24; 26; 27] -> getr (ms_regs ms) (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r)).
{ intros fx' ss ms HS Hb r Hr. exact (YI04.regs_kept_of_st_ok rsegs _ ss _ regs2 [w64 pp; w64 (pp + 0x4008)]
    (map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 19; 20; 24; 26; 27]) HS HAE Hb (Z_to_bv 5 r) (in_map _ _ _ Hr)). }
unfold cfg_at. change (w64 HD_AFTER_PARSE) with (Z_to_bv 64 0x821b4).
destruct (corrupt rec) eqn:Hc; [| destruct (Z.testbit fl 0) eqn:Hb].
- (* pp->corrupt = 1: to T *)
  pose proof (hd_C_entry fx2 W2 regs2 mem2 [] 1 pp R (Forall_nil _) H23 H27 H9 ltac:(unfold HDCEIL_HI; lia) Pm16
    P4096 ltac:(lia) ltac:(lia) ltac:(lia) Hcor Hv18 Hv140) as HS.
  aj_run_tok hd_tbl_ok HS HJ2 SHOK HDspan.
  { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
  lazymatch goal with HF : frame_of ?E0 ?rs0 _ (ms_mem ?ms) |- _ =>
    pose proof (frame_of_read_only E0 rs0 _ _ eq_refl HF) as Hmem end.
  rewrite Hmem in HJ2.
  hd_exit HS. rewrite Hmem.
  apply (HT fx2 ly2 S2 W2 (ms_regs ms) mem2 _ rec).
  destruct (hd_common cx inp fx2 ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) _ HC HBp HJ2
    (RPgSteps.same_io_wvb _ _ _)) as (Hbase & Hat & Hrl).
  + exact (KR _ _ _ HS ltac:(vm_compute; reflexivity)).
  + eapply (sk_reg_is _ _ ms (w_H W2) regs2 _ _ _ 10%nat HS HAE); [vm_compute; reflexivity | reflexivity].
  + rewrite (st_ok_restrict_reg rsegs (w_H W2) _ _ ms _ HS).
    lazymatch type of HS with st_ok _ _ ?ss _ => let v := eval vm_compute in (sr_get (ss_regs ss) (Z_to_bv 5 22)) in
      change (sr_get (ss_regs ss) (Z_to_bv 5 22)) with v end.
    rewrite (sk_soff _ 32 pp 0 E32), Z.add_0_r. reflexivity.
  + split; [exact Hbase|]. split; [|exact Hrl].
    apply (sk_at_sub _ _ _ _ _ _ Hat). intros x Hx. unfold hd_L. fold rec. unfold rs_L_chk in Hx |- *.
    cbn [In app] in Hx |- *. tauto.
- (* corrupt = 0, flags bit 0 set: to MAL *)
  assert (Hv : getr regs2 21 = w64 1).
  { rewrite <- (sk_getr_z regs2 21 21 eq_refl). first [exact R21 | rewrite Hb in R21; exact R21]. }
  pose proof (hd_C_entry fx2 W2 regs2 mem2 [((21%bv : bv 5), SLit 1)] 0 pp R
    ltac:(apply Forall_cons; [split; [intros Hz; apply (f_equal (@bv_unsigned 5)) in Hz; vm_compute in Hz; discriminate Hz | symmetry; exact Hv] | apply Forall_nil])
    H23 H27 H9 ltac:(unfold HDCEIL_HI; lia) Pm16 P4096 ltac:(lia) ltac:(lia) ltac:(lia) Hcor Hv18 Hv140) as HS.
  aj_run_tok hd_tbl_ok HS HJ2 SHOK HDspan.
  { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
  lazymatch goal with HF : frame_of ?E0 ?rs0 _ (ms_mem ?ms) |- _ =>
    pose proof (frame_of_read_only E0 rs0 _ _ eq_refl HF) as Hmem end.
  rewrite Hmem in HJ2.
  hd_exit HS. rewrite Hmem.
  apply (HM fx2 ly2 S2 W2 (ms_regs ms) mem2 _ rec).
  destruct (hd_common cx inp fx2 ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) _ HC HBp HJ2
    (RPgSteps.same_io_wvb _ _ _)) as (Hbase & Hat & Hrl).
  + exact (KR _ _ _ HS ltac:(vm_compute; reflexivity)).
  + eapply (sk_reg_is _ _ ms (w_H W2) regs2 _ _ _ 10%nat HS HAE); [vm_compute; reflexivity | reflexivity].
  + rewrite (st_ok_restrict_reg rsegs (w_H W2) _ _ ms _ HS).
    lazymatch type of HS with st_ok _ _ ?ss _ => let v := eval vm_compute in (sr_get (ss_regs ss) (Z_to_bv 5 22)) in
      change (sr_get (ss_regs ss) (Z_to_bv 5 22)) with v end.
    rewrite (sk_soff _ 32 pp 0 E32), Z.add_0_r. reflexivity.
  + assert (HPA : rs_PA rsegs cx rec = (None, -1)) by (unfold rs_PA; fold fl; rewrite Hb; reflexivity).
    split; [exact Hbase|]. split; [|split; [exact Hrl | rewrite HPA; split; reflexivity]].
    apply (sk_at_sub _ _ _ _ _ _ Hat). intros x Hx. unfold hd_L. fold rec. rewrite HPA. unfold rs_L_chk in Hx |- *.
    cbn [In app snd] in Hx |- *. tauto.
- (* corrupt = 0, flags bit 0 clear: to E *)
  assert (Hv : getr regs2 21 = w64 0).
  { rewrite <- (sk_getr_z regs2 21 21 eq_refl). first [exact R21 | rewrite Hb in R21; exact R21]. }
  pose proof (hd_C_entry fx2 W2 regs2 mem2 [((21%bv : bv 5), SLit 0)] 0 pp R
    ltac:(apply Forall_cons; [split; [intros Hz; apply (f_equal (@bv_unsigned 5)) in Hz; vm_compute in Hz; discriminate Hz | symmetry; exact Hv] | apply Forall_nil])
    H23 H27 H9 ltac:(unfold HDCEIL_HI; lia) Pm16 P4096 ltac:(lia) ltac:(lia) ltac:(lia) Hcor Hv18 Hv140) as HS.
  aj_run_tok hd_tbl_ok HS HJ2 SHOK HDspan.
  { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
  lazymatch goal with HF : frame_of ?E0 ?rs0 _ (ms_mem ?ms) |- _ =>
    pose proof (frame_of_read_only E0 rs0 _ _ eq_refl HF) as Hmem end.
  rewrite Hmem in HJ2.
  assert (Ra0 : getr (ms_regs ms) (Z_to_bv 5 10) = w64 (pp + 0x4008)).
  { rewrite (st_ok_restrict_reg rsegs (w_H W2) _ _ ms _ HS).
    lazymatch type of HS with st_ok _ _ ?ss _ => let v := eval vm_compute in (sr_get (ss_regs ss) (Z_to_bv 5 10)) in
      change (sr_get (ss_regs ss) (Z_to_bv 5 10)) with v end.
    rewrite (sk_soff _ 33 (pp + 0x4008) 0 E33), Z.add_0_r. reflexivity. }
  hd_exit HS. rewrite Hmem.
  apply (HE fx2 ly2 S2 W2 (ms_regs ms) mem2 _ rec).
  destruct (hd_common cx inp fx2 ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) _ HC HBp HJ2
    (RPgSteps.same_io_wvb _ _ _)) as (Hbase & Hat & Hrl).
  + exact (KR _ _ _ HS ltac:(vm_compute; reflexivity)).
  + eapply (sk_reg_is _ _ ms (w_H W2) regs2 _ _ _ 10%nat HS HAE); [vm_compute; reflexivity | reflexivity].
  + rewrite (st_ok_restrict_reg rsegs (w_H W2) _ _ ms _ HS).
    lazymatch type of HS with st_ok _ _ ?ss _ => let v := eval vm_compute in (sr_get (ss_regs ss) (Z_to_bv 5 22)) in
      change (sr_get (ss_regs ss) (Z_to_bv 5 22)) with v end.
    rewrite (sk_soff _ 32 pp 0 E32), Z.add_0_r. reflexivity.
  + split; [exact Hbase|]. split.
    { unfold hd_L in Hat. unfold rs_at_cx, rs_at in Hat |- *.
      apply Forall_app in Hat as [Hl Hr]. apply Forall_app. split; [exact Hl|].
      apply Forall_cons; [cbn [fst snd rl_at]; exact Ra0 | exact Hr]. }
    split; [exact Hrl|].
    split; [exact Hb|]. split; [exact Hc|].
    exact (rk_parse_expect rec Hwf Hc).
Qed.

(* ===================== the piece ===================== *)
Theorem rk_head_B : rs_piece_W11a_head_stmt rsegs B MT.
Proof using AMEMCPY PARSE.
unfold rs_piece_W11a_head_stmt. intros cx POST inp Hst HE HM HT.
pose proof (hd_c3_of cx inp Hst) as HC.
apply (hd_A cx inp POST HC).
intros regs1 mem1 md1 HAp.
apply (hd_B cx inp regs1 mem1 md1 POST HC HAp).
intros fx2 ly2 S2 W2 regs2 mem2 md2 HBp.
exact (hd_C cx inp POST fx2 ly2 S2 W2 regs2 mem2 md2 HC HBp HE HM HT).
Qed.
End e.
End c.
