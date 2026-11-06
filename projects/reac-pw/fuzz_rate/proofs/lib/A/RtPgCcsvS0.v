(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of proofs/reac-pw/fuzz_rate/lib/A/RtPgLeaf.v at 09da091ee285
   (lf_kept_run, here ccs_kept_run) and of proofs/reac-pw/fuzz_rate/lib/A/RtPgCheckList.v at 09da091ee285 (the .got
   and cell regions of cl_entry, here in ccs_p1_entry), for the walk of check_csv's segment S0 on image A. *)
(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; every address below is measured on its unstripped
   twin sha256 0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3, whose loaded bytes are the same): segment
   S0 of the walk of check_csv (0x838e0), RtPgCcsvCut.CC_S0_stmt, from the entry 0x838e0 to the loop head 0x83a54.
   Proves no function (kind: segment lemma): ccsv_S0 is one of the four segment statements that RtPgCcsvCut.cc_chain
   composes into RtPgCSpec.rt_check_csv_specX rsegs B MT 0x838e0 2 T_csv_STK 0x21520.

   THE SEGMENT, in three steps.
   (1) 0x838e0 .. the call of the class-2 side-stack allocation entry 0x3d12c (ccs0_pro): `addi sp,sp,-160`,
       `sd zero,0(sp)`, the 13 saves ra, s0, s1, s2 .. s11 at sp - 8 .. sp - 104, `addi s0,sp,160` (s0 = sp),
       `andi sp,sp,-32` and `mv s1,sp` (the realigned base R1 = cc_rbase sp, sp - 176 or sp - 160), s6 = mask, s4 = the
       list length, the cell R1 + 16 := n, the two .got reads (0x9bec8 -> the use-after-return cell 0xa4c40, whose
       4-byte value is 1; 0x9be70 -> the shadow-offset cell 0xa4c38, whose 8-byte value SHADOW_OFF goes to s9), s3 =
       buf, `beqz a2` 0x83950 NOT taken (the flag reads 1, AR_const_law), `li a0,160`, `jal` 0x83958 with ra =
       0x8395c. One run of the shadow-aware engine under the caller's journal, in two cases of R1 - sp (-160 when
       sp mod 32 = 0, -176 when sp mod 32 = 16): the address R1 of `andi` is an alias fact of the state (the AND
       expression equals SOff 2 (R1 - sp)), so every store through s1 is an offset of sp's atom and lands in the one
       stack region [R1, sp).
   (2) the call (RtPgCcsvKit.rck_stack_malloc_at at cid 2, ASM2): the frame F = frame_addr lyc 2 pos in a0, its
       256 bytes' shadow zero, its flag pointer word at F + 248, the callee-saved registers kept, S2 = set_fs f Sc.
   (3) 0x8395c .. 0x83a54 (one run from a fresh state in the shape of ccsv_ss below): s2 = s8 = F, `sd s3,24(s1)`,
       `bnez s2` 0x83970 taken (F >= 4096, the atom fact of F), so the real-stack arm 0x83974 .. 0x8398c is never
       stepped; `sd s8,48(s1)`, a1 = F + 32, a5 = F + 112, s3 = F + 111, the frame header F[0] = 0x41b58ab3,
       F[8] = 0x1c15c, F[16] = 0x838e0, s7 = (F >> 3) + s9 (the alias of the shadow declaration turns it into the atom
       of SHADOW_OFF + F / 8), the 20 shadow granules 0xf1 x 4, 0x00 x 5, 0xf2 x 5, 0xf8, 0xf3 x 5, and the literals t0
       = 3, t1 = 10, t2 = 18, t3 = 0x21520, t4 = 0x66666667, t5 = 44, a3 = a4 = 0, a6 = -8.

   THE SHAPE THE OTHER SEGMENTS TAKE (section "the shared state"): the env ccsv_E regs buf n FL F = Ereg regs
   (ccsv_extra buf n FL F), atoms 32 = buf, 33 = n, 34 = FL (the flag address), 35 = F, 36 = SHADOW_OFF + F / 8 (the
   frame's shadow), on top of the 32 register atoms (s9 = atom 25 holds SHADOW_OFF); the regions ccsv_cells_r (the
   realigned frame's cells, base atom 9 = s1 = R1, [R1 + 16, R1 + 56)), ccsv_frame_r (base atom 35, the 256 frame
   bytes, the flag pointer word at + 248) and ccsv_fsh_r (base atom 36, the 32 shadow granules); the facts ccsv_facts:
   the atom fact ccsv_Ffact of F (4096 .. 2^47, 32-aligned) and the alias ccsv_alias ((SOff 35 0 >> 3) + SOff 25 0 =
   SOff 36 0), which RtPgCcsvKit.rck_shadow_decl adds (ccsv_ss). The state S0's run reaches at 0x83a54 is in that
   shape: s2 = s8 = SOff 35 0, s7 = SOff 36 0, a1 = SOff 35 32, a5 = SOff 35 112, s3 = SOff 35 111. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05 YG0s YF0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require RateCfg RateCsv.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgSiteA.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgSteps RtPgCcsvKit RtPgCcsvCut.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require RtPgMem.
Require OSSVerify.reac_pw.fuzz_rate.images.Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* image A's loaded segments, as lib/A/RtPgCcsvCut.v names them *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.Asan.M.loaded_segments.

(* ======================================== the constants ======================================== *)
(* check_csv's 312 words 0x838e0 .. 0x83dbc, the table the engine reads its code from *)
Definition ccsv_tbl : ctable := build_table rsegs CC_A 312 TEmpty.
Lemma ccsv_tbl_ok : table_ok rsegs ccsv_tbl.
Proof. apply build_table_ok0. unfold CC_A. lia. Qed.
(* the class-2 allocation entry (`jal` 0x83958) and its return pc *)
Definition CCS_SM2 : Z := 0x3d12c.
Definition CCS_RA : Z := 0x8395c.
(* the two .got words and the two runtime cells they point at (image A, measured on the pinned file) *)
Definition CCS_GOT_UAR : Z := 0x9bec8.
Definition CCS_GOT_SH : Z := 0x9be70.
Definition CCS_UAR_CELL : Z := 0xa4c40.
Definition CCS_SH_CELL : Z := 0xa4c38.

(* ======================================== the shared state ========================================
   The env, the regions and the facts of the walk from 0x8395c on (S0 step 3, and the entry states of S1 .. S3).
   Atoms: 0 .. 31 the registers of the state the env is made at, 32 = buf, 33 = n, 34 = FL (the flag address,
   flag_addr lyc 2 pos), 35 = F (frame_addr lyc 2 pos), 36 = SHADOW_OFF + F / 8 (= shadow_addr F). *)
Definition ccsv_extra (buf n FL F : Z) : list word := [w64 buf; w64 n; w64 FL; w64 F; w64 (SHADOW_OFF + F / 8)].
Definition ccsv_E (regs : bvmap 5 word) (buf n FL F : Z) : env := Ereg regs (ccsv_extra buf n FL F).
(* the realigned frame's cells, base atom 9 (s1 = R1): R1 + 16 = n, R1 + 24 = buf, R1 + 48 = F *)
Definition ccsv_cells_r (wlo whi : Z) (cs : list YP09.chunk) : YP09.region := YP09.mkRegion (Some 9%nat) 16 56 wlo whi cs.
(* the 256 frame bytes, base atom 35 (F): the header at + 0 .. + 24, want[40] at + 32, d[8] at + 112, the flag
   pointer word at + 248 *)
Definition ccsv_frame_r (wlo whi : Z) (cs : list YP09.chunk) : YP09.region := YP09.mkRegion (Some 35%nat) 0 256 wlo whi cs.
(* the 32 shadow granules of the frame, base atom 36 *)
Definition ccsv_fsh_r (wlo whi : Z) (cs : list YP09.chunk) : YP09.region := YP09.mkRegion (Some 36%nat) 0 32 wlo whi cs.
(* the atom fact of F (32-aligned, AR_frames_law; 4096 <= F and F + 256 <= alloc_ceiling < 2 ^ 47) and the alias of
   the shadow declaration (RtPgCcsvKit.rck_shadow_decl at p = 35, b = 25 (s9), s = 36) *)
Definition ccsv_Ffact : afact := mkAF 4096 (2 ^ 47) 5.
Definition ccsv_alias : sv * sv := (SAlu ALU_ADD (SAlu ALU_SRL (SOff 35 0) (SLit 3)) (SOff 25 0), SOff 36 0).
Definition ccsv_facts : facts := mkFacts [(35%nat, ccsv_Ffact)] [] [ccsv_alias].
(* the state at pc with registers sr and regions rs: the facts are the ones rck_shadow_decl adds *)
Definition ccsv_ss (pc : Z) (sr : list sv) (rs : smem) : sstate :=
add_alias (add_atom (mkSS pc sr rs None (mkFacts [] [] [])) 35 ccsv_Ffact) (fst ccsv_alias) (snd ccsv_alias).
Lemma ccsv_ss_facts : forall pc sr rs, ss_facts (ccsv_ss pc sr rs) = ccsv_facts.
Proof. reflexivity. Qed.

(* ======================================== step (1): the entry state ======================================== *)
(* env slot 32 = SHADOW_OFF; the stack region [sp + d, sp) (d = R1 - sp), the two .got words and the two cells *)
Definition ccs_p1_extra : list word := [w64 SHADOW_OFF].
Definition ccs_and_lhs : sv := SAlu ALU_AND (SOff 2 (-160)) (SLit (-32)).
Definition ccs_p1_regions (d : Z) : smem :=
[ YP09.mkRegion (Some 2%nat) d 0 d 0 [];
  YP09.mkRegion None CCS_GOT_UAR (CCS_GOT_UAR + 8) 0 0 [YP09.mkChunk CCS_GOT_UAR (CVal 8 (SLit CCS_UAR_CELL))];
  YP09.mkRegion None CCS_GOT_SH (CCS_GOT_SH + 8) 0 0 [YP09.mkChunk CCS_GOT_SH (CVal 8 (SLit CCS_SH_CELL))];
  YP09.mkRegion None CCS_UAR_CELL (CCS_UAR_CELL + 4) 0 0 [YP09.mkChunk CCS_UAR_CELL (CVal 4 (SLit 1))];
  YP09.mkRegion None CCS_SH_CELL (CCS_SH_CELL + 8) 0 0 [YP09.mkChunk CCS_SH_CELL (CVal 8 (SOff 32 0))] ].
Definition ccs_p1_facts (d : Z) : facts := mkFacts [] [] [(ccs_and_lhs, SOff 2 d)].
Definition ccs_p1_ss (d : Z) : sstate := mkSS CC_A sr_atoms (ccs_p1_regions d) None (ccs_p1_facts d).

(* ---- byte and word facts ---- *)
Lemma ccs_le8 : forall v, 0 <= v < 2 ^ 64 ->
le_byte v 8 0 + 256 * (le_byte v 8 1 + 256 * (le_byte v 8 2 + 256 * (le_byte v 8 3 + 256 * (le_byte v 8 4 +
256 * (le_byte v 8 5 + 256 * (le_byte v 8 6 + 256 * le_byte v 8 7)))))) = v.
Proof.
intros v Hv. unfold le_byte. rewrite (Z.mod_small v) by (cbn; lia). rewrite !Z.shiftr_div_pow2 by lia.
change (2 ^ (8 * Z.of_nat 0)) with 1. change (2 ^ (8 * Z.of_nat 1)) with 256.
change (2 ^ (8 * Z.of_nat 2)) with (256 * 256). change (2 ^ (8 * Z.of_nat 3)) with (256 * 256 * 256).
change (2 ^ (8 * Z.of_nat 4)) with (256 * 256 * 256 * 256). change (2 ^ (8 * Z.of_nat 5)) with (256 * 256 * 256 * 256 * 256).
change (2 ^ (8 * Z.of_nat 6)) with (256 * 256 * 256 * 256 * 256 * 256).
change (2 ^ (8 * Z.of_nat 7)) with (256 * 256 * 256 * 256 * 256 * 256 * 256).
rewrite Z.div_1_r. rewrite <- !Z.div_div by lia.
set (q1 := v / 256). set (q2 := q1 / 256). set (q3 := q2 / 256). set (q4 := q3 / 256).
set (q5 := q4 / 256). set (q6 := q5 / 256). set (q7 := q6 / 256).
assert (D0 := Z.div_mod v 256 ltac:(lia)). assert (D1 := Z.div_mod q1 256 ltac:(lia)).
assert (D2 := Z.div_mod q2 256 ltac:(lia)). assert (D3 := Z.div_mod q3 256 ltac:(lia)).
assert (D4 := Z.div_mod q4 256 ltac:(lia)). assert (D5 := Z.div_mod q5 256 ltac:(lia)).
assert (D6 := Z.div_mod q6 256 ltac:(lia)).
assert (Q7 : q7 < 256).
{ subst q7 q6 q5 q4 q3 q2 q1. rewrite !Z.div_div by lia. apply Z.div_lt_upper_bound; lia. }
assert (Q7p : 0 <= q7) by (subst q7 q6 q5 q4 q3 q2 q1; rewrite !Z.div_div by lia; apply Z.div_pos; lia).
rewrite (Z.mod_small q7) by lia.
fold q2 q3 q4 q5 q6 q7 in D0, D1, D2, D3, D4, D5, D6. lia.
Qed.
Lemma ccs_rdword_of_val : forall H mem a v, 0 <= v < 2 ^ 64 ->
val_mem rsegs (mrestrict H mem) a 8 v -> rdword (aview rsegs H mem) a = Some v.
Proof.
intros H mem a v Hv V. unfold rdword, aview.
pose proof (V 0%nat ltac:(lia)) as B0. pose proof (V 1%nat ltac:(lia)) as B1.
pose proof (V 2%nat ltac:(lia)) as B2. pose proof (V 3%nat ltac:(lia)) as B3.
pose proof (V 4%nat ltac:(lia)) as B4. pose proof (V 5%nat ltac:(lia)) as B5.
pose proof (V 6%nat ltac:(lia)) as B6. pose proof (V 7%nat ltac:(lia)) as B7.
change (Z.of_nat 0) with 0 in B0. rewrite Z.add_0_r in B0.
change (Z.of_nat 1) with 1 in B1. change (Z.of_nat 2) with 2 in B2. change (Z.of_nat 3) with 3 in B3.
change (Z.of_nat 4) with 4 in B4. change (Z.of_nat 5) with 5 in B5. change (Z.of_nat 6) with 6 in B6.
change (Z.of_nat 7) with 7 in B7.
rewrite B0, B1, B2, B3, B4, B5, B6, B7. cbn [option_map]. f_equal.
assert (LB : forall k, 0 <= le_byte v 8 k < 256) by (intros k; unfold le_byte; apply Z.mod_pos_bound; lia).
rewrite !RtPgMem.rtm_unsigned_byte. rewrite !(Z.mod_small (le_byte v 8 _)) by apply LB.
apply ccs_le8. exact Hv.
Qed.
(* a word the reader shows lies in [0, 2 ^ 64) *)
Lemma ccs_rdword_range : forall H mem a v, rdword (aview rsegs H mem) a = Some v -> 0 <= v < 2 ^ 64.
Proof.
intros H mem a v Hw. unfold rdword in Hw.
destruct (aview rsegs H mem a) as [b0|] eqn:E0; [|discriminate].
destruct (aview rsegs H mem (a + 1)) as [b1|] eqn:E1; [|discriminate].
destruct (aview rsegs H mem (a + 2)) as [b2|] eqn:E2; [|discriminate].
destruct (aview rsegs H mem (a + 3)) as [b3|] eqn:E3; [|discriminate].
destruct (aview rsegs H mem (a + 4)) as [b4|] eqn:E4; [|discriminate].
destruct (aview rsegs H mem (a + 5)) as [b5|] eqn:E5; [|discriminate].
destruct (aview rsegs H mem (a + 6)) as [b6|] eqn:E6; [|discriminate].
destruct (aview rsegs H mem (a + 7)) as [b7|] eqn:E7; [|discriminate].
injection Hw as <-.
apply aview_byte in E0 as (_ & _ & _ & R0). apply aview_byte in E1 as (_ & _ & _ & R1).
apply aview_byte in E2 as (_ & _ & _ & R2). apply aview_byte in E3 as (_ & _ & _ & R3).
apply aview_byte in E4 as (_ & _ & _ & R4). apply aview_byte in E5 as (_ & _ & _ & R5).
apply aview_byte in E6 as (_ & _ & _ & R6). apply aview_byte in E7 as (_ & _ & _ & R7).
lia.
Qed.
(* a 4-byte value a reader shows, as val_mem *)
Lemma ccs_val_of_rd32 : forall H mem a v, rd32 (aview rsegs H mem) a v -> val_mem rsegs (mrestrict H mem) a 4 v.
Proof.
intros H mem a v R k Hk. pose proof (R k Hk) as Rk.
apply (RtPgMem.rtm_aview_mbyte rsegs H mem). rewrite Rk. f_equal. rewrite RtPgMem.rtm_unsigned_byte.
symmetry. apply Z.mod_small. unfold le_byte. apply Z.mod_pos_bound. lia.
Qed.
(* an 8-byte chunk of a region whose value is an atom, as a word the reader shows *)
Lemma ccs_chunk_word : forall E H mem b cs off (r : nat) v,
(forall c, In c cs -> YP09.chunk_ok rsegs E (mrestrict H mem) b c) ->
In (YP09.mkChunk off (CVal 8 (SOff r 0))) cs -> ew E r = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
rdword (aview rsegs H mem) (b + off) = Some v.
Proof.
intros E H mem b cs off r v Hc Hin Hr Hv. apply ccs_rdword_of_val; [exact Hv|].
apply (val_of_chunk_ok rsegs E _ b off 8 (SOff r 0) v (Hc _ Hin)); [| cbn; lia | lia].
apply (rts_den_atom E r v Hr Hv).
Qed.
(* one-byte literal chunks, read back as shadow bytes: a boolean check that each pattern byte is a chunk *)
Definition ccs_byte_at (c : YP09.chunk) (o v : Z) : bool :=
(YP09.c_off c =? o) && match YP09.c_val c with CVal w (SLit z) => N.eqb w 1 && (z mod 256 =? v) | _ => false end.
Definition ccs_bytes_chk (cs : list YP09.chunk) (pat : list Z) : bool :=
forallb (fun i => existsb (fun c => ccs_byte_at c (Z.of_nat i) (nth i pat 0)) cs) (seq 0 (length pat)).
Lemma ccs_bytes_of_chunks : forall E H mem b cs pat,
(forall c, In c cs -> YP09.chunk_ok rsegs E (mrestrict H mem) b c) ->
Forall (fun v => 0 <= v < 256) pat -> ccs_bytes_chk cs pat = true ->
forall i, 0 <= i < Z.of_nat (length pat) -> aview rsegs H mem (b + i) = Some (nth (Z.to_nat i) pat 0).
Proof.
intros E H mem b cs pat Hc Hr Hk i Hi. unfold ccs_bytes_chk in Hk. rewrite forallb_forall in Hk.
specialize (Hk (Z.to_nat i) ltac:(apply in_seq; lia)). apply existsb_exists in Hk as (c & Hin & Hb).
unfold ccs_byte_at in Hb. apply andb_prop in Hb as [Ho Hv]. apply Z.eqb_eq in Ho. rewrite Z2Nat.id in Ho by lia.
destruct c as [co cv]. cbn [YP09.c_off YP09.c_val] in Ho, Hv. subst co.
destruct cv as [w e| | |]; try discriminate Hv. destruct e; try discriminate Hv.
apply andb_prop in Hv as [Hw Hz]. apply N.eqb_eq in Hw. apply Z.eqb_eq in Hz. subst w.
pose proof (Hc _ Hin 0 ltac:(cbn; lia)) as (bb & Hb1 & Hb2).
cbn [YP09.c_off YP09.c_val YP09.cbyte] in Hb1, Hb2. rewrite Z.add_0_r in Hb2. injection Hb1 as <-.
unfold aview. rewrite Hb2. cbn [option_map]. f_equal.
unfold YP09.byte_of_word. cbn [sv_denot]. rewrite Z.mul_0_r, Z.shiftr_0_r.
rewrite RtPgMem.rtm_unsigned_byte, unsigned_lit. unfold zcanon, M64.
rewrite (Z.mod_mod_divide z (2 ^ 64) 256) by (exists (2 ^ 56); reflexivity). exact Hz.
Qed.
(* a run keeps every byte outside the zone Zn its write windows lie in *)
Lemma ccs_kept_run : forall (Zn : Z -> Prop) E rs (H : word -> bool) (m1 m2 : word -> option byte),
frame_of E rs (mrestrict H m1) (mrestrict H m2) -> (forall a, in_wrange E rs a -> Zn a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ Zn a -> aview rsegs H m2 a = aview rsegs H m1 a.
Proof.
intros Zn E rs H m1 m2 HF HW a Ha Hz. unfold aview, mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by exact Ha. intros X. exact (Hz (HW a X)).
Qed.
(* an address outside [lo, hi) is below lo or at or above hi *)
Lemma ccs_not_in : forall lo hi a, ~ (lo <= a < hi) -> a < lo \/ hi <= a.
Proof.
intros lo hi a Hn. destruct (Z.lt_ge_cases a lo) as [H|H]; [left; exact H|]. right.
destruct (Z.lt_ge_cases a hi) as [H2|H2]; [exfalso; apply Hn; split; assumption | exact H2].
Qed.
(* the alias of `andi sp,sp,-32`: (sp - 160) and -32 is sp + (cc_rbase sp - sp) *)
Lemma ccs_and_ok : forall E sp, bv_unsigned (ew E 2) = sp -> 160 <= sp < 2 ^ 64 ->
sv_denot E ccs_and_lhs = sv_denot E (SOff 2 (cc_rbase sp - sp)).
Proof.
intros E sp Hsp Hr. apply U_inj. unfold ccs_and_lhs. rewrite U_SAlu, !U_SOff, U_SLit. cbn [zalu_raw]. rewrite Hsp.
rewrite (zcanon_id (sp + -160)) by (unfold M64; lia).
change (zcanon (-32)) with (Z.land (-32) (Z.ones 64)).
rewrite Z.land_assoc, Z.land_ones by lia. unfold zcanon, M64. rewrite Zmod_mod. f_equal.
replace (sp + (cc_rbase sp - sp)) with (cc_rbase sp) by lia. unfold cc_rbase, CC_FRAME.
f_equal.
Qed.
(* the push of a side-stack frame only shrinks the owned set (it adds client bytes, keeps the chunks and sections) *)
Lemma ccs_aowned_push : forall {rc : YM05.RunCeil} B ly f Sc cid pos a,
frames (set_fs f Sc) = (cid, pos) :: frames Sc -> aowned B ly (set_fs f Sc) a -> aowned B ly Sc a.
Proof.
intros rc B ly f Sc cid pos a Hf [H1 H2]. split; [exact H1|].
intros Hc. apply H2. destruct Hc as [Hk | (cp & Hin & Hr)]; [left; exact Hk|].
right. exists cp. split; [rewrite Hf; right; exact Hin | exact Hr].
Qed.

Section s0. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws rsegs B.
Hypothesis HAPI : api_env rsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASM2 : astack_malloc_realizes rsegs B 2.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTF : ameter_fs_laws MT.
Hypothesis HSM2 : pc_stack_malloc (as_code B) 2 = CCS_SM2.
Hypothesis HGOTS : as_got_shadow B = CCS_GOT_SH.
Hypothesis HGOTU : as_got_uar B = CCS_GOT_UAR.
Hypothesis HCELLS : as_shadow_cell B = CCS_SH_CELL.
Hypothesis HCELLU : as_uar_cell B = CCS_UAR_CELL.

(* ---- step (1) ---- *)
Lemma ccs_p1_entry : forall (W : world rsegs) regs memc d,
(d = -160 \/ d = -176) -> cc_rbase (spZ regs) = spZ regs + d ->
0xa4c48 <= spZ regs + d -> spZ regs <= 2 ^ 47 ->
(forall a, spZ regs + d <= a < spZ regs -> apresent (w_H W) memc a) ->
rdword (aview rsegs (w_H W) memc) CCS_GOT_UAR = Some CCS_UAR_CELL ->
rdword (aview rsegs (w_H W) memc) CCS_GOT_SH = Some CCS_SH_CELL ->
rd32 (aview rsegs (w_H W) memc) CCS_UAR_CELL 1 ->
rdword (aview rsegs (w_H W) memc) CCS_SH_CELL = Some SHADOW_OFF ->
st_ok rsegs (Ereg regs ccs_p1_extra) (ccs_p1_ss d) (restrict (w_H W) (mkst regs (Z_to_bv 64 CC_A) memc (seg_rom rsegs))).
Proof.
intros W regs memc d Hd Hcr Hlo Hhi Hpres Kgu Kgs Ku Kc.
rewrite restrict_mkst_fx.
set (E := Ereg regs ccs_p1_extra).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (subst E; exact (ew_Ereg_extra regs _ 0)).
unfold ccs_p1_ss. apply (entry_st_ok_full rsegs); change (Ereg regs ccs_p1_extra) with E.
- apply regs_ok_Ereg.
- destruct Hd as [-> | ->]; vm_compute; reflexivity.
- unfold ccs_p1_regions.
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]].
  + apply (region_ok_stack rsegs E _ 2 (spZ regs) d Usp); [lia | lia |].
    intros a Ha. apply (apresent_writable rsegs). apply Hpres. exact Ha.
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    unfold CCS_GOT_UAR, CCS_UAR_CELL in *.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val rsegs E _ 0 0x9bec8 8 (SLit 0xa4c40) 0xa4c40); [reflexivity | cbn; lia | lia |].
    exact (val_mem_of_rdword rsegs (w_H W) memc _ _ Kgu).
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    unfold CCS_GOT_SH, CCS_SH_CELL in *.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val rsegs E _ 0 0x9be70 8 (SLit 0xa4c38) 0xa4c38); [reflexivity | cbn; lia | lia |].
    exact (val_mem_of_rdword rsegs (w_H W) memc _ _ Kgs).
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    unfold CCS_UAR_CELL in *.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val rsegs E _ 0 0xa4c40 4 (SLit 1) 1); [reflexivity | cbn; lia | lia |].
    exact (ccs_val_of_rd32 (w_H W) memc _ _ Ku).
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    unfold CCS_SH_CELL in *.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val rsegs E _ 0 0xa4c38 8 (SOff 32 0) SHADOW_OFF);
    [ apply (rts_den_atom E 32 SHADOW_OFF E32); unfold SHADOW_OFF; lia | unfold SHADOW_OFF; cbn; lia | lia |].
    exact (val_mem_of_rdword rsegs (w_H W) memc _ _ Kc).
- apply pairwise_disjoint_of_extents. unfold ccs_p1_regions, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp.
  unfold CCS_GOT_UAR, CCS_GOT_SH, CCS_UAR_CELL, CCS_SH_CELL.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj; cbn [fst snd]. repeat split; lia.
- split; [exact I|]. split; [exact I|]. cbn [ccs_p1_facts f_alias alias_ok]. split; [|exact I].
  rewrite (ccs_and_ok E (spZ regs) Usp) by lia. rewrite Hcr. f_equal. f_equal. lia.
Qed.

(* the state at the call of the class-2 allocation: the journal, the registers the rest reads and the bytes the
   prologue wrote (the 13 saves, the cell R1 + 16 = n), every other byte outside [R1, sp) as at the entry *)
Definition ccs_p1_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate) (W : world rsegs)
(memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word) (buf n : Z) : world rsegs -> config -> Prop :=
fun W1 c1 => W1 = W /\ exists regsT memT mdT,
c1 = mkCfg (mkst regsT (Z_to_bv 64 CCS_SM2) memT (seg_rom rsegs)) mdT /\
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdT k /\ same_io mdc mdT /\
getr regsT 1 = w64 CCS_RA /\ getr regsT 2 = w64 (cc_rbase (spZ regs)) /\
getr regsT 3 = getr regs 3 /\ getr regsT 4 = getr regs 4 /\ getr regsT 8 = w64 (spZ regs) /\
getr regsT 9 = w64 (cc_rbase (spZ regs)) /\ getr regsT 19 = w64 buf /\
getr regsT 20 = getr regs 12 /\ getr regsT 22 = getr regs 13 /\ getr regsT 25 = w64 SHADOW_OFF /\
cc_saved regs (aview rsegs (w_H W) memT) /\
rdword (aview rsegs (w_H W) memT) (cc_rbase (spZ regs) + 16) = Some n /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (cc_rbase (spZ regs) <= a < spZ regs) ->
 aview rsegs (w_H W) memT a = aview rsegs (w_H W) memc a).

(* the write right of step (1): the stack region in the caller's window, the four read-only extents *)
Local Ltac ccs_p1_awr regs Usp :=
lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own);
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spZ regs - sp0));
[reflexivity | rewrite Usp; lia | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |];
repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]); apply awr_ok_nil
end.
(* one 8-byte slot of the stack region holding the atom of register r *)
Local Ltac ccs_slot HC regs Ex EE :=
lazymatch goal with |- rdword _ (spZ regs - 8 - 8 * Z.of_nat ?jj) = Some (bv_unsigned (getr regs (Z_to_bv 5 (nth ?jj ?l 0)))) =>
let od := eval vm_compute in (-8 - 8 * Z.of_nat jj) in
let rr := eval vm_compute in (nth jj l 0) in
let nn := eval vm_compute in (Z.to_nat rr) in
replace (spZ regs - 8 - 8 * Z.of_nat jj) with (spZ regs + od) by (cbn [Z.of_nat]; lia);
change (nth jj l 0) with rr;
apply (ccs_chunk_word Ex _ _ (spZ regs) _ od nn _ HC);
[ cbn [In]; tauto
| rewrite (EE nn (Z_to_bv 5 rr) eq_refl); symmetry; apply Z_to_bv_bv_unsigned
| pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 rr))) as Hbr; unfold bv_modulus in Hbr; cbn [Z.of_N] in Hbr; lia ]
end.
(* after the run of step (1): the state at 0x3d12c read back into ccs_p1_post *)
Local Ltac ccs_p1_finish regs Usp EE E3 E4 E10 E11 E12 E13 E32 Hcr H10 H11 :=
lazymatch goal with HS : st_ok _ ?E ?ss (restrict (w_H ?W) ?ms), HFr : frame_of _ ?rs0 (mrestrict _ ?mc) _ |- _ =>
let Ems := fresh "Ems" in
pose proof (st_ok_restrict_mkst rsegs (w_H W) E ss ms HS eq_refl) as Ems;
let R1 := fresh "R" in rreg HS (1%bv : bv 5) R1;
let R2 := fresh "R" in rreg HS (2%bv : bv 5) R2;
let R3 := fresh "R" in rreg HS (3%bv : bv 5) R3;
let R4 := fresh "R" in rreg HS (4%bv : bv 5) R4;
let R8 := fresh "R" in rreg HS (8%bv : bv 5) R8;
let R9 := fresh "R" in rreg HS (9%bv : bv 5) R9;
let R19 := fresh "R" in rreg HS (19%bv : bv 5) R19;
let R20 := fresh "R" in rreg HS (20%bv : bv 5) R20;
let R22 := fresh "R" in rreg HS (22%bv : bv 5) R22;
let R25 := fresh "R" in rreg HS (25%bv : bv 5) R25;
let rs := eval vm_compute in (ss_mem ss) in
let r0 := eval vm_compute in (nth 0 rs (YP09.mkRegion None 0 0 0 0 [])) in
let HR0 := fresh "HR0" in
pose proof (rts_region_nth E ss ms 0 r0 (w_H W) HS eq_refl) as HR0; cbn [ms_mem restrict mkst] in HR0;
let HC := fresh "HC" in
lazymatch r0 with YP09.mkRegion (Some 2%nat) ?lo ?hi ?wlo ?whi ?cs =>
pose proof (rts_chunks E _ 2 (spZ regs) cs lo hi wlo whi HR0 Usp) as HC end;
rewrite Ems; apply SRr_ret; split; [reflexivity|];
eexists; eexists; eexists; split; [reflexivity|];
split; [eassumption|];
split; [eapply same_io_trans; [apply same_io_refl | apply same_io_wvb]|];
split; [rewrite R1; reflexivity|];
split; [rewrite R2, Usp, Hcr; unfold w64; f_equal; try lia|];
split; [rewrite R3, E3; reflexivity|];
split; [rewrite R4, E4; reflexivity|];
split; [rewrite R8; unfold w64; rewrite <- Usp, Z_to_bv_bv_unsigned; reflexivity|];
split; [rewrite R9, Usp, Hcr; unfold w64; f_equal; try lia|];
split; [rewrite R19, E10, H10; reflexivity|];
split; [rewrite R20, E12; reflexivity|];
split; [rewrite R22, E13; reflexivity|];
split; [rewrite R25, E32; reflexivity|];
split;
[ intros j Hj; unfold cc_saved_regs;
  do 13 (destruct j as [|j]; [ccs_slot HC regs E EE|]); lia |];
split;
[ lazymatch goal with |- rdword _ (cc_rbase (spZ regs) + 16) = _ =>
  rewrite Hcr;
  lazymatch goal with |- rdword _ (spZ regs + ?D + 16) = _ =>
    let o := eval vm_compute in (D + 16) in replace (spZ regs + D + 16) with (spZ regs + o) by lia end;
  apply (ccs_chunk_word E _ _ (spZ regs) _ _ 11 _ HC);
  [cbn [In]; tauto | rewrite E11, H11; reflexivity | lia] end |];
intros a Ha Hz; apply (ccs_kept_run (fun x => cc_rbase (spZ regs) <= x < spZ regs) E rs0 (w_H W) mc _ HFr);
[ let x := fresh "x" in let r := fresh "r" in let Hin := fresh "Hin" in let Hx := fresh "Hx" in
  intros x (r & Hin & Hx);
  lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hin end;
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx;
    first [rewrite Usp in Hx; rewrite Hcr; lia | lia] |]);
  destruct Hin
| exact Ha | exact Hz ]
end.

Lemma ccs0_pro : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (buf n mask : Z),
cc_pre B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf n mask ->
SRr rsegs W (cfg_at rsegs CC_A regs memc mdc) (ccs_p1_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf n).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf n mask HP.
pose proof HP as ((HJ & Hra & Hra4 & Hgp & Htp & Hsp16 & Hwlo & Hwhi & Hev) & H10 & H11 & Hn & H12 & H13 & Hmask & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kc & Ku & Kgs & Kgu).
rewrite HGOTS, HCELLS in Kgs. rewrite HCELLS in Kc. rewrite HGOTU, HCELLU in Kgu. rewrite HCELLU in Ku.
unfold T_csv_STK, ESTACK in Hwlo.
destruct (cc_rbase_bounds (spZ regs) Hsp16) as (Hr32 & Hrlo & Hrhi). unfold CC_FRAME in Hrlo, Hrhi.
assert (HE : exists d, (d = -160 \/ d = -176) /\ cc_rbase (spZ regs) = spZ regs + d).
{ pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as D1. pose proof (Z.div_mod (cc_rbase (spZ regs)) 32 ltac:(lia)) as D2.
  assert (cc_rbase (spZ regs) = spZ regs - 160 \/ cc_rbase (spZ regs) = spZ regs - 176) as [X|X] by lia;
  [exists (-160) | exists (-176)]; split; lia. }
destruct HE as (d & Hd & Hcr).
pose proof (ccs_p1_entry W regs memc d Hd Hcr ltac:(lia) ltac:(lia) ltac:(intros a Ha; apply Hpres; lia) Kgu Kgs Ku Kc) as HS.
set (E := Ereg regs ccs_p1_extra) in HS.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E3 : ew E 3 = getr regs 3) by (subst E; exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (subst E; exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = getr regs 10) by (subst E; exact (ew_Ereg_nat regs _ 10 10%bv eq_refl)).
assert (E11 : ew E 11 = getr regs 11) by (subst E; exact (ew_Ereg_nat regs _ 11 11%bv eq_refl)).
assert (E12 : ew E 12 = getr regs 12) by (subst E; exact (ew_Ereg_nat regs _ 12 12%bv eq_refl)).
assert (E13 : ew E 13 = getr regs 13) by (subst E; exact (ew_Ereg_nat regs _ 13 13%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (EE : forall nn (q : bv 5), Z.of_nat nn = bv_unsigned q -> ew E nn = getr regs q)
by (intros nn q Hq; subst E; exact (ew_Ereg_nat regs _ nn q Hq)).
clearbody E.
unfold cfg_at. change (w64 CC_A) with (Z_to_bv 64 CC_A).
destruct Hd as [-> | ->].
- rck_aj_run_to_sh ccsv_tbl_ok HS HJ CCS_SM2; [ccs_p1_awr regs Usp|].
  ccs_p1_finish regs Usp EE E3 E4 E10 E11 E12 E13 E32 Hcr H10 H11.
- rck_aj_run_to_sh ccsv_tbl_ok HS HJ CCS_SM2; [ccs_p1_awr regs Usp|].
  ccs_p1_finish regs Usp EE E3 E4 E10 E11 E12 E13 E32 Hcr H10 H11.
Qed.

(* ---- step (3): the state at 0x8395c, in the shape of the shared state ---- *)
(* a0 = F as the atom 35; the cells region with the cell n written before the call, the frame's first 24 bytes
   (the header) writable with its flag pointer word, the frame's shadow (all 32 granules 0 after the allocation)
   writable at granules 0 .. 19 *)
Definition ccs_p2_sr : list sv := sr_set sr_atoms 10%bv (SOff 35 0).
Definition ccs_p2_regions : smem :=
[ ccsv_cells_r 24 56 [YP09.mkChunk 16 (CVal 8 (SOff 33 0))];
  ccsv_frame_r 0 24 [YP09.mkChunk 248 (CVal 8 (SOff 34 0))];
  ccsv_fsh_r 0 20 (RtPgMem.rtm_fsh_cs (repeat 0 32)) ].
Lemma ccs_p2_entry : forall (W : world rsegs) regs2 mem2 buf n FL F R1,
getr regs2 10 = w64 F -> getr regs2 9 = w64 R1 -> getr regs2 25 = w64 SHADOW_OFF ->
4096 <= F -> F + 256 <= alloc_ceiling -> in_app F 256 -> F mod 32 = 0 ->
alloc_ceiling <= R1 -> R1 + 56 <= 2 ^ 47 ->
0 <= buf < 2 ^ 64 -> 0 <= n < 2 ^ 64 -> 0 <= FL < 2 ^ 64 ->
(forall o, 24 <= o < 56 -> apresent (w_H W) mem2 (R1 + o)) ->
(forall o, 0 <= o < 24 -> apresent (w_H W) mem2 (F + o)) ->
(forall i, 0 <= i < 20 -> apresent (w_H W) mem2 (shadow_addr F + i)) ->
val_mem rsegs (mrestrict (w_H W) mem2) (R1 + 16) 8 n ->
val_mem rsegs (mrestrict (w_H W) mem2) (F + 248) 8 FL ->
rt_fsh rsegs (w_H W) mem2 F (repeat 0 32) ->
st_ok rsegs (ccsv_E regs2 buf n FL F) (ccsv_ss CCS_RA ccs_p2_sr ccs_p2_regions)
  (restrict (w_H W) (mkst regs2 (Z_to_bv 64 CCS_RA) mem2 (seg_rom rsegs))).
Proof.
intros W regs2 mem2 buf n FL F R1 G10 G9 G25 HF4096 HFceil HFapp HF32 HR1lo HR1hi Hbuf Hn HFL Hpc Hpf Hps Vn VFL Hz.
pose proof asan_consts as (C1 & _).
destruct (rck_fbounds 2 F ltac:(lia) HF32 ltac:(rewrite rck_fbytes2; exact HFapp)) as (_ & _ & HS0 & HS1 & HSd & _).
rewrite rck_fbytes2 in HS1, HSd. change (256 / 8) with 32 in HS1, HSd.
set (E := ccsv_E regs2 buf n FL F).
assert (EE : forall nn (q : bv 5), Z.of_nat nn = bv_unsigned q -> ew E nn = getr regs2 q)
by (intros nn q Hq; subst E; exact (ew_Ereg_nat regs2 _ nn q Hq)).
assert (E33 : ew E 33 = Z_to_bv 64 n) by (subst E; exact (ew_Ereg_extra regs2 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 FL) by (subst E; exact (ew_Ereg_extra regs2 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 F) by (subst E; exact (ew_Ereg_extra regs2 _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 (SHADOW_OFF + F / 8)) by (subst E; exact (ew_Ereg_extra regs2 _ 4)).
assert (U9 : bv_unsigned (ew E 9) = R1) by (rewrite (EE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = F) by (rewrite E35; apply unsigned_lit_small; lia).
assert (U36 : bv_unsigned (ew E 36) = shadow_addr F) by (rewrite E36; apply unsigned_lit_small; unfold shadow_addr in *; lia).
unfold ccsv_ss. apply (rck_shadow_decl E _ _ 35 25 36 F 4096 (2 ^ 47)).
2: exact E35. 2: lia. 2: exact HF32. 2: lia.
2: rewrite (EE 25%nat 25%bv eq_refl); exact G25.
2: exact E36.
rewrite restrict_mkst_fx. subst E.
apply (entry_st_ok_full rsegs).
all: try change (Ereg regs2 (ccsv_extra buf n FL F)) with (ccsv_E regs2 buf n FL F).
- unfold ccs_p2_sr. apply regs_ok_pin; [apply regs_ok_Ereg | |].
  + intros Hc. apply (f_equal (@bv_unsigned 5)) in Hc. vm_compute in Hc. discriminate Hc.
  + rewrite G10. symmetry. apply (rts_den_atom _ 35 F); [exact (ew_Ereg_extra regs2 _ 3) | lia].
- vm_compute. reflexivity.
- unfold ccs_p2_regions, ccsv_cells_r, ccsv_frame_r, ccsv_fsh_r.
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
  + apply (RtPgMem.rtm_rw_region rsegs _ (w_H W) mem2 9 R1); [exact U9 | lia | lia | exact Hpc |].
    constructor; [|constructor].
    apply (chunk_ok_val rsegs _ _ R1 16 8 (SOff 33 0) n); [apply (rts_den_atom _ 33 n E33 Hn) | cbn; lia | lia | exact Vn].
  + apply (RtPgMem.rtm_rw_region rsegs _ (w_H W) mem2 35 F); [exact U35 | lia | lia | exact Hpf |].
    constructor; [|constructor].
    apply (chunk_ok_val rsegs _ _ F 248 8 (SOff 34 0) FL); [apply (rts_den_atom _ 34 FL E34 HFL) | cbn; lia | lia | exact VFL].
  + apply (RtPgMem.rtm_rw_region rsegs _ (w_H W) mem2 36 (shadow_addr F)); [exact U36 | lia | lia | exact Hps |].
    apply (RtPgMem.rtm_fsh_chunks rsegs). exact Hz.
    apply Forall_forall. intros v Hv. apply repeat_spec in Hv. lia.
- apply pairwise_disjoint_of_extents. unfold ccs_p2_regions, ccsv_cells_r, ccsv_frame_r, ccsv_fsh_r, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U35, U36.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj; cbn [fst snd].
  destruct HSd as [HSd | HSd]; repeat split; lia.
- split; [exact I|]. split; exact I.
Qed.

(* ---- the segment ---- *)
Local Ltac ccs_in := cbn [In]; tauto.
Local Ltac ccs_bv := apply bv_eq; rewrite ?Z_to_bv_unsigned; reflexivity.

Theorem ccsv_S0 : CC_S0_stmt B MT.
Proof.
unfold CC_S0_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf n mask HP.
eapply SRr_bind; [exact (ccs0_pro STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf n mask HP)|].
intros W1 c1 _ (-> & regsT & memT & mdT & -> & HJT & HioT & T1 & T2 & T3 & T4 & T8 & T9 & T19 & T20 & T22 & T25 & Tsv & Tn & KT).
pose proof HP as ((HJ & Hra & Hra4 & Hgp & Htp & Hsp16 & Hwlo & Hwhi & Hev) & H10 & H11 & Hn & H12 & H13 & Hmask & Hbuf0 & Hbufhi
  & _ & _ & _ & _ & _ & _ & _ & Hcid & Hcnt & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
unfold T_csv_STK, ESTACK in Hwlo.
destruct (cc_rbase_bounds (spZ regs) Hsp16) as (Hr32 & Hrlo & Hrhi). unfold CC_FRAME in Hrlo, Hrhi.
pose proof (Z.div_mod (cc_rbase (spZ regs)) 32 ltac:(lia)) as D32. pose proof (Z.div_mod sp0 16 ltac:(lia)) as D16.
(* step (2): the call of the class-2 allocation *)
rewrite <- HSM2.
eapply SRr_bind.
{ eapply (rck_stack_malloc_at B LAWS HAPI ML SMP 2 ASM2 ltac:(lia) W regsT memT STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdT k
    (cc_rbase (spZ regs) - sp0) (w64 CCS_RA) HJT).
  - unfold spZ at 1. rewrite T2. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - symmetry. apply (Z.mod_unique (cc_rbase (spZ regs) - sp0) 16 (2 * (cc_rbase (spZ regs) / 32) - sp0 / 16) 0); [left; lia | lia].
  - lia.
  - unfold ESTACK. lia.
  - rewrite T3. exact Hgp.
  - rewrite T4. exact Htp.
  - exact T1.
  - vm_compute. reflexivity.
  - exact Hcnt. }
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & pos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & (f & ES2) & Hsame & Hfr
  & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK).
pose proof (proj1 HJ2) as HAR2.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
assert (Hfin2 : In (2, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 pos HAR2 Hfin2) as (HFal & HFapp & HFpres & HFSpres).
destruct (frames_bounds rsegs B LAWS _ _ _ _ _ 2 pos HAR2 Hfin2) as (HF4096 & HFceil & _).
destruct (frame_facts B lyc S2 _ 2 pos (proj1 HAR2) Hfin2) as (_ & Hpos & _).
rewrite rck_fbytes2 in HFapp, HFpres, HFSpres, HFceil, Hz, Hflag. change (256 / 8) with 32 in HFSpres, Hz.
destruct (rck_fbounds 2 (frame_addr lyc 2 pos) ltac:(lia) HFal ltac:(rewrite rck_fbytes2; exact HFapp))
  as (_ & _ & HS0 & HS1 & HSd & _).
rewrite rck_fbytes2 in HS1, HSd. change (256 / 8) with 32 in HS1, HSd.
set (F := frame_addr lyc 2 pos) in *. set (FL := flag_addr lyc 2 pos) in *.
assert (HFL : 0 <= FL < 2 ^ 64) by exact (ccs_rdword_range _ _ _ _ Hflag).
assert (P9 : getr regs2 9 = w64 (cc_rbase (spZ regs))) by (rewrite <- T9; exact (HP2 9 ltac:(unfold acallee_saved; lia))).
assert (P25 : getr regs2 25 = w64 SHADOW_OFF) by (rewrite <- T25; exact (HP2 25 ltac:(unfold acallee_saved; lia))).
destruct HK as (HK1 & _).
(* the call keeps every byte at or above R1 *)
assert (KC : forall a, cc_rbase (spZ regs) <= a < 2 ^ 64 -> aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) memT a).
{ intros a Ha. apply HK1; [lia|]. unfold ESTACK. lia. }
assert (Kn2 : rdword (aview rsegs (w_H W) mem2) (cc_rbase (spZ regs) + 16) = Some n).
{ rewrite (rdword_ext (aview rsegs (w_H W) memT) (aview rsegs (w_H W) mem2)); [exact Tn|]. intros kk Hkk. apply KC. lia. }
assert (Hfsh0 : rt_fsh rsegs (w_H W) mem2 F (repeat 0 32)).
{ intros i Hi. rewrite repeat_length in Hi. rewrite nth_repeat. unfold zero_shadow in Hz. change (256 / 8) with 32 in Hz.
  exact (Hz i ltac:(lia)). }
assert (VFL : val_mem rsegs (mrestrict (w_H W) mem2) (F + 248) 8 FL).
{ replace (F + 248) with (F + 256 - 8) by lia. exact (val_mem_of_rdword rsegs _ _ _ _ Hflag). }
pose proof (ccs_p2_entry W regs2 mem2 buf n FL F (cc_rbase (spZ regs)) Ha0 P9 P25 HF4096 HFceil HFapp HFal
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HFL
  ltac:(intros o Ho; apply Hpres2; lia) ltac:(intros o Ho; apply (proj1 (HFpres (F + o) ltac:(lia))))
  ltac:(intros i Hi; apply (proj1 (HFSpres i ltac:(lia))))
  (val_mem_of_rdword rsegs _ _ _ _ Kn2) VFL Hfsh0) as HS2.
set (E2 := ccsv_E regs2 buf n FL F) in HS2.
assert (EE2 : forall nn (q : bv 5), Z.of_nat nn = bv_unsigned q -> ew E2 nn = getr regs2 q)
by (intros nn q Hq; subst E2; exact (ew_Ereg_nat regs2 _ nn q Hq)).
assert (F35 : ew E2 35 = Z_to_bv 64 F) by (subst E2; exact (ew_Ereg_extra regs2 _ 3)).
assert (F36 : ew E2 36 = Z_to_bv 64 (SHADOW_OFF + F / 8)) by (subst E2; exact (ew_Ereg_extra regs2 _ 4)).
assert (F33 : ew E2 33 = Z_to_bv 64 n) by (subst E2; exact (ew_Ereg_extra regs2 _ 1)).
assert (U9 : bv_unsigned (ew E2 9) = cc_rbase (spZ regs)) by (rewrite (EE2 9%nat 9%bv eq_refl), P9; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E2 35) = F) by (rewrite F35; apply unsigned_lit_small; lia).
assert (U36 : bv_unsigned (ew E2 36) = shadow_addr F) by (rewrite F36; apply unsigned_lit_small; unfold shadow_addr in *; lia).
clearbody E2.
change (w64 CCS_RA) with (Z_to_bv 64 CCS_RA).
(* step (3): the run to the loop head *)
rck_aj_run_to_sh ccsv_tbl_ok HS2 HJ2 CC_PC1.
{ lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end.
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (cc_rbase (spZ regs) - sp0));
  [reflexivity | rewrite U9; lia | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |].
  eapply (rck_awr_ok_fobj _ _ _ _ _ _ _ _ _ _ 35%nat 2 pos 0);
  [reflexivity | rewrite U35; fold F; lia | left; reflexivity | cbn [YP09.r_wlo YP09.r_whi]; lia
  | cbn [YP09.r_wlo YP09.r_whi]; rewrite rck_fbytes2; lia |].
  eapply (rck_awr_ok_fsh _ _ _ _ _ _ _ _ _ _ 36%nat 2 pos);
  [reflexivity | rewrite U36; reflexivity | left; reflexivity | cbn [YP09.r_wlo YP09.r_whi]; lia
  | cbn [YP09.r_wlo YP09.r_whi]; rewrite rck_fbytes2; change (256 / 8) with 32; lia |].
  apply awr_ok_nil. }
lazymatch goal with HS : st_ok _ _ ?ss (restrict (w_H W) ?ms), HFr : frame_of _ ?rs0 (mrestrict _ mem2) _ |- _ =>
pose proof (st_ok_restrict_mkst rsegs (w_H W) E2 ss ms HS eq_refl) as Ems;
rreg HS (2%bv : bv 5) Q2; rreg HS (3%bv : bv 5) Q3; rreg HS (4%bv : bv 5) Q4; rreg HS (5%bv : bv 5) Q5;
rreg HS (6%bv : bv 5) Q6; rreg HS (7%bv : bv 5) Q7; rreg HS (8%bv : bv 5) Q8; rreg HS (9%bv : bv 5) Q9;
rreg HS (11%bv : bv 5) Q11; rreg HS (13%bv : bv 5) Q13; rreg HS (14%bv : bv 5) Q14; rreg HS (15%bv : bv 5) Q15;
rreg HS (16%bv : bv 5) Q16; rreg HS (18%bv : bv 5) Q18; rreg HS (19%bv : bv 5) Q19; rreg HS (20%bv : bv 5) Q20;
rreg HS (22%bv : bv 5) Q22; rreg HS (23%bv : bv 5) Q23; rreg HS (24%bv : bv 5) Q24; rreg HS (25%bv : bv 5) Q25;
rreg HS (28%bv : bv 5) Q28; rreg HS (29%bv : bv 5) Q29; rreg HS (30%bv : bv 5) Q30;
let rs := eval vm_compute in (ss_mem ss) in
let rc0 := eval vm_compute in (nth 0 rs (YP09.mkRegion None 0 0 0 0 [])) in
let rc2 := eval vm_compute in (nth 2 rs (YP09.mkRegion None 0 0 0 0 [])) in
pose proof (rts_region_nth E2 ss ms 0 rc0 (w_H W) HS eq_refl) as HRc; cbn [ms_mem restrict mkst] in HRc;
pose proof (rts_region_nth E2 ss ms 2 rc2 (w_H W) HS eq_refl) as HRs; cbn [ms_mem restrict mkst] in HRs;
lazymatch rc0 with YP09.mkRegion (Some 9%nat) ?lo ?hi ?wlo ?whi ?cs =>
pose proof (rts_chunks E2 _ 9 (cc_rbase (spZ regs)) cs lo hi wlo whi HRc U9) as HCc end;
lazymatch rc2 with YP09.mkRegion (Some 36%nat) ?lo ?hi ?wlo ?whi ?cs =>
pose proof (rts_chunks E2 _ 36 (shadow_addr F) cs lo hi wlo whi HRs U36) as HCs;
pose proof (ccs_bytes_of_chunks E2 (w_H W) (ms_mem ms) (shadow_addr F) cs (CC_SH_A ++ repeat 0 12) HCs
  ltac:(repeat constructor; lia) ltac:(vm_compute; reflexivity)) as Hsh end;
(* the bytes the run keeps: everything outside its three write windows *)
assert (KE3 : forall a, 0 <= a < 2 ^ 64 ->
  ~ ((cc_rbase (spZ regs) + 24 <= a < cc_rbase (spZ regs) + 56) \/ (F <= a < F + 24) \/ (shadow_addr F <= a < shadow_addr F + 20)) ->
  aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) mem2 a);
[ apply (ccs_kept_run _ E2 rs0 (w_H W) mem2 _ HFr);
  let x := fresh "x" in let r := fresh "r" in let Hin := fresh "Hin" in let Hx := fresh "Hx" in
  intros x (r & Hin & Hx);
  lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hin end;
  destruct Hin as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx;
  [left; rewrite U9 in Hx; lia | right; left; rewrite U35 in Hx; lia | right; right; rewrite U36 in Hx; lia] | ];
assert (Ec : mkCfg ms (with_vm_backing (m_vm_lazy md2) mat md2) = cfg_at rsegs CC_PC1 (ms_regs ms) (ms_mem ms) (with_vm_backing (m_vm_lazy md2) mat md2))
by (rewrite Ems at 1; reflexivity)
end.
apply SRr_ret. exists pos, S2, (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy md2) mat md2).
split; [exact Ec|].
unfold cc_st1, cc_frame. change CC_CID with 2. fold F. fold FL.
assert (HG3 : forall r : nat, (r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 19 \/ r = 20 \/ r = 22 \/ r = 25)%nat ->
  ew E2 r = getr regsT (Z_to_bv 5 (Z.of_nat r))).
{ intros r Hr. rewrite (EE2 r (Z_to_bv 5 (Z.of_nat r))) by (rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N];
    rewrite Z.mod_small; [reflexivity | destruct Hr as [->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]; cbn; lia]).
  apply HP2. unfold acallee_saved. destruct Hr as [->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]; cbn; lia. }
split; [exact HP|].
split.
{ 
  split; [exact HJ2|]. split; [exact Hfrs2|]. split; [exact Hnin|]. split; [exact Eab|].
  split; [rewrite ES2; reflexivity|]. split; [rewrite ES2; reflexivity|]. split; [rewrite ES2; reflexivity|].
  split; [exact Hnev2|]. split; [exact Hbb2|].
  split; [rewrite ES2; apply (mo_le_set_fs_r MT MTF); apply (mo_le_refl MT MTL)|].
  split; [eapply same_io_trans; [exact HioT|]; eapply same_io_trans; [apply same_io_materialized; exact Hsame | apply same_io_wvb]|].
  split.
  { intros a Ha Hw Hown.
    assert (Hw' : a < spZ regs - T_csv_STK \/ spZ regs <= a) by (apply ccs_not_in; exact Hw).
    unfold T_csv_STK, ESTACK in Hw'. clear Hw.
    rewrite (KE3 a Ha).
    2:{ intros [X|[X|X]]; [destruct Hw'; lia | | ].
      - apply Hown. apply (own_free_frame B lyc Sc _ 2 pos a (proj1 HAR) ltac:(lia) Hpos Hnin). rewrite rck_fbytes2. fold F. lia.
      - apply Hown. apply (own_free_frame_shadow B lyc Sc _ 2 pos a (proj1 HAR) ltac:(lia) Hpos Hnin).
        rewrite rck_fbytes2. change (256 / 8) with 32. fold F. lia. }
    rewrite (Hfr a Ha Hown).
    2:{ intros X. apply Hown. rewrite ES2 in X, Hfrs2. exact (ccs_aowned_push B lyc f Sc 2 pos a Hfrs2 X). }
    2:{ unfold ESTACK. destruct Hw'; lia. }
    apply KT; [exact Ha | destruct Hw'; lia]. }
  split; [exact HF4096|]. split; [exact HFceil|]. split; [exact HFapp|]. split; [exact HFal|].
  split.
  { rewrite (rdword_ext (aview rsegs (w_H W) mem2) (aview rsegs (w_H W) (ms_mem ms))).
    - replace (F + 248) with (F + 256 - 8) by lia. exact Hflag.
    - intros kk Hkk. apply KE3; [lia|]. intros [X|[X|X]]; lia. }
  split.
  { intros j Hj. rewrite (rdword_ext (aview rsegs (w_H W) memT) (aview rsegs (w_H W) (ms_mem ms))); [exact (Tsv j Hj)|].
    intros kk Hkk. rewrite (KE3 (spZ regs - 8 - 8 * Z.of_nat j + kk) ltac:(lia)); [apply KC; lia|]. intros [X|[X|X]]; lia. }
  split.
  { rewrite (rdword_ext (aview rsegs (w_H W) mem2) (aview rsegs (w_H W) (ms_mem ms))); [exact Kn2|].
    intros kk Hkk. apply KE3; [lia|]. intros [X|[X|X]]; lia. }
  split.
  { apply (ccs_chunk_word E2 _ _ _ _ 24 19 buf HCc); [ccs_in | | lia].
    rewrite (HG3 19%nat ltac:(tauto)). exact T19. }
  split.
  { apply (ccs_chunk_word E2 _ _ _ _ 48 35 F HCc); [ccs_in | exact F35 | lia]. }
  split; [rewrite Q3, (HG3 3%nat ltac:(tauto)); exact T3|].
  split; [rewrite Q4, (HG3 4%nat ltac:(tauto)); exact T4|].
  split; [rewrite Q8, (HG3 8%nat ltac:(tauto)); exact T8|].
  split; [rewrite Q18, F35; reflexivity|].
  split; [rewrite Q23, F36; reflexivity|].
  rewrite Q24, F35; reflexivity. }
split; [exact Hsh|].
split; [rewrite Q2, (HG3 2%nat ltac:(tauto)); exact T2|].
split; [rewrite Q9, (HG3 9%nat ltac:(tauto)); exact T9|].
split; [rewrite Q5; reflexivity|]. split; [rewrite Q6; reflexivity|]. split; [rewrite Q7; reflexivity|].
split; [rewrite Q11, U35; reflexivity|].
split; [rewrite Q13; reflexivity|]. split; [rewrite Q14; reflexivity|].
split; [rewrite Q15, U35; reflexivity|].
split; [rewrite Q16; ccs_bv|].
split; [rewrite Q19, U35; reflexivity|].
split; [rewrite Q20, (HG3 20%nat ltac:(tauto)); exact (eq_trans T20 H12)|].
split; [rewrite Q22, (HG3 22%nat ltac:(tauto)); exact (eq_trans T22 H13)|].
split; [rewrite Q25, (HG3 25%nat ltac:(tauto)); exact T25|].
split; [rewrite Q28; reflexivity|]. split; [rewrite Q29; reflexivity|].
rewrite Q30; reflexivity.
Qed.
End s0.

Print Assumptions ccsv_S0.
