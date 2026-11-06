(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of proofs/reac-pw/fuzz_rate/lib/Reusable/YCbq.v at 7379c28ff70f
   [Apache-2.0 OR MIT] (aj_bcmp_at, here with the callee's same_but_materialized in its post, which the cut's same_io
   needs), for reac-pw/fuzz_rate's image A. The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgCcsvS2.v (the draft over ae282742a698, not
   committed); the same segment for image B (fuzz_rate.asan-ubsan): the image is images.AsanUbsan, the step and memory
   kits lib/AU/RtPgStepsB.v and lib/AU/RtPgMemB.v, the cut lib/AU/RtPgCcsvCutB.v; buf, the list length and n are
   reloaded from the realigned frame's cells R1 + 56, R1 + 48 and R1 + 40; the n > 0 arm is finished (the bcmp wrapper
   at image B's entry 0x42200, image B's pointer-overflow test 0x83ac8, the check of buf + c and its slow block). *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; every address is measured on its unstripped twin
   sha256 a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1): segment S2 of the walk of check_csv
   (0x837c0), the tail 0x83a90 -> 0x83b38. Proves no function (kind: segment lemma): ccsv_S2 is
   RtPgCcsvCutB.CC_S2_stmt, which RtPgCcsvCutB.cc_chain composes with S0, S1 and S3.

   The code (neutral listing check_csv.fuzz_rate.asan-ubsan.s; s1 = R1, s7 = shadow_addr F, s8 = want = F + 32,
   s9 = SHADOW_OFF, t3 = |csv_list mask|):
     0x83a90 ld s2,56(s1)          s2 = buf (the cell R1 + 56)
     0x83a94 ld s3,48(s1)          s3 = the list length (the cell R1 + 48; the cell's chunk is t3's atom)
     0x83a98 bne s3,t3             not taken: both sides are the same atom
     0x83a9c ld a0,40(s1)          a0 = n (the cell R1 + 40)
     0x83aa0 beqz a0 -> 0x83b04    the n = 0 / n > 0 split, made before the run (the cell holds SLit 0, or an atom in
                                   [1, 23])
   n = 0 (c2_arm0, one run and one split):
     0x83b04-0x83b10               the instrumented 1-byte load check of buf: its shadow byte is a one-byte region at an
                                   atom declared equal to (s2 >> 3) + s9 (alias), holding an atom in [0, 7]; the
                                   `bnez` is split; when the byte is not 0 the slow block 0x83ca4 is decided by the
                                   engine (buf is 16-aligned, so `andi a1,s2,7` is 0) and the error arm 0x83cac is
                                   not reached
     0x83b14 lbu a0,0(s2)          buf[0] = 0x5a (the contract's garr8, kept from the call: buf is a live block)
     0x83b18-0x83b30               granules 4-8 of the frame's shadow := 0xf8 (want out of scope)
     0x83b34 bne a0,a2             a0 = 90 = a2: not taken; 0x83b38
   n > 0 (c2_arm1 to the `jal`, c2_call from it):
     0x83aa4 addi a0,a0,-1; 0x83aa8 bltu s3,a0 (split); 0x83aac mv s3,a0 when not taken: s3 = c = min(len, n - 1)
     0x83ab0-0x83ab8 a0 = buf, a1 = s8, a2 = c; 0x83abc jal 0x42200: the bcmp wrapper (abcmp_realizes, c2_bcmp_at) on
                                   (buf, want = F + 32, c); its answer is 0 (RtPgCcsvMB ccsv_bcmp_eq_av)
     0x83ac0 bnez a0               not taken (a0 pinned to the literal 0)
     0x83ac4 not a0,s2; 0x83ac8 bltu a0,s3 -> 0x83c70 (the undefined-behaviour check of buf + c): the engine cannot
                                   range ~buf and stops; the walk splits it, and the taken arm is refuted from
                                   ~buf = 2^64 - 1 - buf (YI08 U_not, RtPgStepsB rtb_lnot_w64 / rtb_not_ltu) and
                                   buf + c < buf + max n 1 <= 2^63 (cc_pre), so the `unimp` 0x83c70 is not reached
     0x83acc-0x83adc               the instrumented check of buf + c: (s2 + s3) and ((s2 + s3) >> 3) + s9 are two
                                   aliases to atoms; the shadow byte (an atom in [0, 7]) is split; when it is not 0 the
                                   slow block 0x83c98's `blt` is split too, and its error arm 0x83ca0 is refuted by the
                                   shadow byte's law ((buf + c) mod 8 < the byte, RtPgMemB rtmb_ra_slow)
     0x83ae0 lbu a0,0(a0)          buf[c] = 0 (ccsv_last_min)
     0x83ae4-0x83af8               granules 4-8 := 0xf8; 0x83afc beqz a0 taken: 0x83b38
   The error paths (0x83c74, 0x83c8c, 0x83ca0, 0x83cac) and the `unimp` 0x83c70 are not reached. Every state the
   walk passes keeps the journal's state S1 (no allocation), so the cut's state facts carry over; c2_fin rebuilds
   cc_st3 from what the runs and the call wrote (the bcmp wrapper's 2 ESTACK window below R1, granules 4-8 of the
   frame's shadow). buf's bytes after the frame call are the call's (cc_frame's keep clause: a client block's byte is
   not the runtime's) and its shadow is re-derived from the allocator's block law at the current state (RtPgMemB
   rtmb_blk_ra), which is why the contract asks for a live block.
   Section hypothesis: ABCMP, the bcmp wrapper's contract at its image-B entry 0x42200 (RtPgStepsB.RTSB_BCMP). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0s YG0q YF0v YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI0m.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require RateCsv.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgImgB RtPgStepsB RtPgMemB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgCcsvCutB RtPgCcsvMB RtPgCcsvKitB.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* image B's loaded segments, as lib/AU/RtPgCcsvCutB.v names them *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

(* ======================================== small facts ======================================== *)
(* the frame's shadow before and after the tail: only granules 4-8 differ *)
Lemma c2_sh_len : Z.of_nat (length (CC_SH_A ++ repeat 0 12)) = 32 /\ Z.of_nat (length (CC_SH_C ++ repeat 0 12)) = 32.
Proof. split; reflexivity. Qed.
Lemma c2_sh_AC : forall j, (j < 32)%nat -> ~ (4 <= j < 9)%nat ->
nth j (CC_SH_A ++ repeat 0 12) 0 = nth j (CC_SH_C ++ repeat 0 12) 0.
Proof. intros j Hj Hn. do 32 (destruct j as [|j]; [try reflexivity; exfalso; lia|]). lia. Qed.
Lemma c2_sh_C48 : forall j, (4 <= j < 9)%nat -> nth j (CC_SH_C ++ repeat 0 12) 0 = 248.
Proof. intros j Hj. do 9 (destruct j as [|j]; [try reflexivity; exfalso; lia|]). lia. Qed.
Lemma c2_sh_bytes : Forall (fun v => 0 <= v < 256) (CC_SH_A ++ repeat 0 12).
Proof. repeat constructor; lia. Qed.

(* ======================================== the engine states ======================================== *)
(* the instruction table: the tail 0x83a90 .. 0x83b34 and the slow blocks and error arms 0x83c98 .. 0x83cb0 *)
Definition c2_tbl : ctable := build_table rsegs 0x83c98 7 (build_table rsegs CC_PC2 42 TEmpty).
Lemma c2_tbl_ok : table_ok rsegs c2_tbl.
Proof. apply build_table_ok; [lia|]. apply build_table_ok0. unfold CC_PC2. lia. Qed.

(* the shadow declaration of the base object held by atom p: ((p >> 3) + s9) is the atom s *)
Definition c2_alias_sh (p s : nat) : sv * sv :=
(SAlu ALU_ADD (SAlu ALU_SRL (SOff p 0) (SLit 3)) (SOff 25 0), SOff s 0).
(* the frame's 32 shadow bytes, with the write window of the five `sb` stores (granules 4-8) *)
Definition c2_fsh_reg : YP09.region := YP09.mkRegion (Some 23%nat) 0 32 4 9 (rtmb_fsh_cs (CC_SH_A ++ repeat 0 12)).
(* one byte at the address held by atom b *)
Definition c2_cell (b : nat) (v : sv) : YP09.region := YP09.mkRegion (Some b) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 v)].
(* the realigned frame's cells R1 + 40 (n), R1 + 48 (the list length, held as t3's atom 28) and R1 + 56 (buf, atom 33) *)
Definition c2_stk_reg (en : sv) : YP09.region :=
YP09.mkRegion (Some 9%nat) 40 64 0 0
[YP09.mkChunk 40 (CVal 8 en); YP09.mkChunk 48 (CVal 8 (SOff 28 0)); YP09.mkChunk 56 (CVal 8 (SOff 33 0))].
(* n = 0: the cells, the frame's shadow, buf's shadow byte (atom 34, value atom 35) and buf's byte *)
Definition c2_mem_a (v : sv) : smem := [c2_stk_reg (SLit 0); c2_fsh_reg; c2_cell 34 v; c2_cell 33 (SLit 90)].
Definition c2_facts_a (fs : list (nat * afact)) : facts :=
mkFacts ((33%nat, mkAF 4096 (2 ^ 47) 4) :: fs) [] [c2_alias_sh 33 34].
(* n > 0, before the call: only the cells (n in atom 32, buf in atom 33) *)
Definition c2_mem_b : smem := [c2_stk_reg (SOff 32 0)].
Definition c2_facts_b : facts := mkFacts [(32%nat, mkAF 1 23 0); (33%nat, mkAF 4096 (2 ^ 47) 4)] [] [].
(* n > 0, after the call: the frame's shadow, the shadow byte of buf + c (atom 33, value atom 34) and the byte buf[c]
   (atom 32); s2 + s3 is the atom 32 *)
Definition c2_mem_c (v : sv) : smem := [c2_fsh_reg; c2_cell 33 v; c2_cell 32 (SLit 0)].
Definition c2_facts_c (fs : list (nat * afact)) : facts :=
mkFacts fs [] [(SAlu ALU_ADD (SOff 18 0) (SOff 19 0), SOff 32 0); c2_alias_sh 32 33].

(* after the call a0 is the wrapper's answer, 0 *)
Definition c2_sr_c : list sv := sr_set sr_atoms 10%bv (SLit 0).

Section s2. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
(* the bcmp wrapper's contract at image B's entry 0x42200 (RtPgStepsB.RTSB_BCMP, the `jal` 0x83abc): the field aa_bcmp of
   YG0d.AsanAPI at image B's record, whose pc_wrap_bcmp is 0x42200 *)
Hypothesis ABCMP : abcmp_realizes rsegs B 0x42200.

(* ======================================== generic lemmas ======================================== *)
(* an aview value kept gives the same byte *)
Lemma c2_mbyte_of_aview : forall H mem H' mem' a,
aview rsegs H' mem' a = aview rsegs H mem a -> mbyte rsegs (mrestrict H' mem') a = mbyte rsegs (mrestrict H mem) a.
Proof.
intros H mem H' mem' a E. unfold aview in E.
destruct (mbyte rsegs (mrestrict H' mem') a) as [b'|], (mbyte rsegs (mrestrict H mem) a) as [b|];
cbn in E; try discriminate; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.
(* a run's frame keeps every byte outside its write windows *)
Lemma c2_kept_of_frame : forall E rs H (m m' : word -> option byte) (P : Z -> Prop),
frame_of E rs (mrestrict H m) (mrestrict H m') -> (forall a, in_wrange E rs a -> P a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview rsegs H m' a = aview rsegs H m a.
Proof.
intros E rs H m m' P HF HP a Ha Hna. unfold aview, mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
intros Hin. apply Hna, HP. rewrite unsigned_lit_small in Hin by lia. exact Hin.
Qed.
(* a byte list kept under an aview equality *)
Lemma c2_garr8_kept : forall H mem H' mem' a l,
garr8 rsegs (mrestrict H mem) a l ->
(forall i, 0 <= i < Z.of_nat (length l) -> aview rsegs H' mem' (a + i) = aview rsegs H mem (a + i)) ->
garr8 rsegs (mrestrict H' mem') a l.
Proof.
intros H mem H' mem' a l G K j Hj. split; [|exact (proj2 (G j Hj))].
intros kk Hkk. destruct kk as [|kk]; [|exfalso; lia].
rewrite Z.add_0_r. rewrite (c2_mbyte_of_aview H mem H' mem' (a + Z.of_nat j) (K (Z.of_nat j) ltac:(lia))).
pose proof (proj1 (G j Hj) 0%nat ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X.
Qed.
(* the byte a one-byte chunk of a literal holds *)
Lemma c2_chunk_lit : forall E H mem base o v w,
YP09.chunk_ok rsegs E (mrestrict H mem) base (YP09.mkChunk o (CVal 1 (SLit v))) ->
bv_unsigned (YP09.byte_of_word (Z_to_bv 64 v) 0) = w ->
aview rsegs H mem (base + o) = Some w.
Proof.
intros E H mem base o v w Hc Hw. destruct (Hc 0 ltac:(cbn; lia)) as (b & Hb1 & Hb2).
assert (Hb3 : mbyte rsegs (mrestrict H mem) (base + o) = Some b) by (rewrite <- Hb2; f_equal; cbn; ring).
unfold aview. rewrite Hb3. cbn [option_map]. f_equal.
cbn [cbyte YP09.c_val] in Hb1. injection Hb1 as <-. exact Hw.
Qed.
(* a byte kept outside one window *)
Lemma c2_kept_win : forall E rs H (m m' : word -> option byte) (lo hi : Z),
frame_of E rs (mrestrict H m) (mrestrict H m') ->
(forall a, in_wrange E rs a -> lo <= a < hi) ->
forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview rsegs H m' a = aview rsegs H m a.
Proof.
intros E rs H m m' lo hi HF HP a Ha Hna.
exact (c2_kept_of_frame E rs H m m' (fun x => lo <= x < hi) HF HP a Ha Hna).
Qed.
(* the sum of two atoms is the atom an alias names *)
Lemma c2_denot_add : forall E (p q : nat) (x y : Z),
ew E p = Z_to_bv 64 x -> ew E q = Z_to_bv 64 y -> 0 <= x -> 0 <= y -> x + y < 2 ^ 64 ->
sv_denot E (SAlu ALU_ADD (SOff p 0) (SOff q 0)) = Z_to_bv 64 (x + y).
Proof.
intros E p q x y Hp Hq Hx Hy Hxy. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E p x Hp ltac:(lia)), (U_atom E q y Hq ltac:(lia)).
unfold zcanon, M64. apply Z.mod_small. lia.
Qed.
(* a register after a run, from the symbolic state; a register the run did not touch *)
Lemma c2_reg_sv : forall E ss ms (H : word -> bool) (r : bv 5) e,
st_ok rsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = e -> getr (ms_regs ms) r = sv_denot E e.
Proof. intros E ss ms H r e HS He. rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), He. reflexivity. Qed.
Lemma c2_reg_kept : forall regs extra ss ms (H : word -> bool) (r : bv 5),
st_ok rsegs (Ereg regs extra) ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff (Z.to_nat (bv_unsigned r)) 0 ->
getr (ms_regs ms) r = getr regs r.
Proof.
intros regs extra ss ms H r HS Hq.
rewrite (st_ok_restrict_reg rsegs H _ ss ms r HS), Hq. cbn [sv_denot]. rewrite Z.add_0_r.
rewrite ew_Ereg_reg, Z_to_bv_bv_unsigned. reflexivity.
Qed.
(* an atom register read through the env of a state *)
Lemma c2_den_reg : forall regs extra (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r ->
sv_denot (Ereg regs extra) (SOff n 0) = getr regs r.
Proof.
intros regs extra n r Hn. cbn [sv_denot]. rewrite Z.add_0_r, (ew_Ereg_nat regs extra n r Hn).
apply Z_to_bv_bv_unsigned.
Qed.
Lemma c2_den_off : forall E (p : nat) x c, ew E p = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> 0 <= x + c < 2 ^ 64 ->
sv_denot E (SOff p c) = Z_to_bv 64 (x + c).
Proof. intros E p x c Hp Hx Hc. rewrite denot_lit_U, (U_atom_off E p x c Hp Hx Hc). reflexivity. Qed.
(* want's bytes through aview, from the cut's mbytes_at *)
Lemma c2_want_av : forall H mem w (L : list Z), mbytes_at rsegs (mrestrict H mem) w (RateCsv.csv_bytes L) ->
Forall (fun c => 0 <= c < 256) L ->
forall i, 0 <= i < Z.of_nat (length L) -> aview rsegs H mem (w + i) = Some (nth (Z.to_nat i) L 0).
Proof.
intros H mem w L HM HL i Hi. unfold aview. pose proof (HM (Z.to_nat i)) as X.
rewrite RateCsv.csv_bytes_length in X. specialize (X ltac:(lia)). rewrite Z2Nat.id in X by lia. rewrite X.
unfold RateCsv.csv_bytes. rewrite nth_error_map, (nth_error_nth' L 0) by lia. cbn [option_map]. f_equal.
rewrite rtmb_unsigned_byte. apply Z.mod_small. rewrite Forall_forall in HL. apply HL. apply nth_In. lia.
Qed.
(* the shadow hull of c <= 17 bytes of want (frame offset 32) lies in the frame's 32 shadow bytes *)
Lemma c2_hull_in : forall F c, F mod 32 = 0 -> 0 <= F -> 0 <= c <= 17 -> forall s,
shadow_addr (F + 32) / 8 * 8 <= s < shadow_addr (F + 32 + c - 1) / 8 * 8 + 8 ->
shadow_addr F <= s < shadow_addr F + 32.
Proof. intros F c HF H0 Hc s Hs. unfold shadow_addr, shadow_of_addr, SHADOW_OFF in *. Z.div_mod_to_equations. lia. Qed.
(* one-byte literal chunks, read back as shadow bytes: a boolean check that each pattern byte is a chunk *)
Definition c2_byte_at (c : YP09.chunk) (o v : Z) : bool :=
(YP09.c_off c =? o) && match YP09.c_val c with CVal w (SLit z) => N.eqb w 1 && (z mod 256 =? v) | _ => false end.
Definition c2_bytes_chk (cs : list YP09.chunk) (pat : list Z) : bool :=
forallb (fun i => existsb (fun c => c2_byte_at c (Z.of_nat i) (nth i pat 0)) cs) (seq 0 (length pat)).
Lemma c2_bytes_of_chunks : forall E H mem b cs pat,
(forall c, In c cs -> YP09.chunk_ok rsegs E (mrestrict H mem) b c) ->
Forall (fun v => 0 <= v < 256) pat -> c2_bytes_chk cs pat = true ->
forall i, 0 <= i < Z.of_nat (length pat) -> aview rsegs H mem (b + i) = Some (nth (Z.to_nat i) pat 0).
Proof.
intros E H mem b cs pat Hc Hr Hk i Hi. unfold c2_bytes_chk in Hk. rewrite forallb_forall in Hk.
specialize (Hk (Z.to_nat i) ltac:(apply in_seq; lia)). apply existsb_exists in Hk as (c & Hin & Hb).
unfold c2_byte_at in Hb. apply andb_prop in Hb as [Ho Hv]. apply Z.eqb_eq in Ho. rewrite Z2Nat.id in Ho by lia.
destruct c as [co cv]. cbn [YP09.c_off YP09.c_val] in Ho, Hv. subst co.
destruct cv as [w e| | |]; try discriminate Hv. destruct e; try discriminate Hv.
apply andb_prop in Hv as [Hw Hz]. apply N.eqb_eq in Hw. apply Z.eqb_eq in Hz. subst w.
pose proof (Hc _ Hin 0 ltac:(cbn; lia)) as (bb & Hb1 & Hb2).
cbn [YP09.c_off YP09.c_val YP09.cbyte] in Hb1, Hb2. rewrite Z.add_0_r in Hb2. injection Hb1 as <-.
unfold aview. rewrite Hb2. cbn [option_map]. f_equal.
unfold YP09.byte_of_word. cbn [sv_denot]. rewrite Z.mul_0_r, Z.shiftr_0_r.
rewrite rtmb_unsigned_byte, unsigned_lit. unfold zcanon, M64.
rewrite (Z.mod_mod_divide z (2 ^ 64) 256) by (exists (2 ^ 56); reflexivity). exact Hz.
Qed.
Lemma c2_shC_bytes : Forall (fun v => 0 <= v < 256) (CC_SH_C ++ repeat 0 12).
Proof. repeat constructor; lia. Qed.
(* a shadow byte that allows an access lies in [0, 7] *)
Lemma c2_sok_range : forall x s, saddr_ok x s -> 0 <= s <= 7.
Proof. intros x s [H|[H1 H2]]; [lia|]. pose proof (Z.mod_pos_bound x 8 ltac:(lia)). lia. Qed.

(* ================================ the bcmp wrapper under the journal ================================ *)
Lemma c2_bcmp_at : forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y n (o : Z) raw,
ajournal rsegs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 x -> getr regsT 11 = w64 y -> getr regsT 12 = w64 n -> 0 <= n < 2 ^ 32 ->
0 <= x -> x + n <= 2 ^ 63 -> 0 <= y -> y + n <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
src_ok rsegs W regsT memT x n -> src_ok rsegs W regsT memT y n ->
(forall a, x <= a < x + n -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
(forall a, y <= a < y + n -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
amem_range x n -> amem_range y n ->
range_addressable (aview rsegs (w_H W) memT) SHADOW_OFF x n -> (0 < n -> shadow_hull_vis (aview rsegs (w_H W) memT) x n) ->
range_addressable (aview rsegs (w_H W) memT) SHADOW_OFF y n -> (0 < n -> shadow_hull_vis (aview rsegs (w_H W) memT) y n) ->
SRr rsegs W (mkCfg (mkst regsT (Z_to_bv 64 0x42200) memT (seg_rom rsegs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2 (v : word),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom rsegs)) md2 /\
ajournal rsegs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ same_but_materialized mdc md2 /\ getr regs2 10 = v /\
(v = w64 0 <-> forall i, 0 <= i < n -> aview rsegs (w_H W) memT (x + i) = aview rsegs (w_H W) memT (y + i)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) -> aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof using ABCMP.
intros W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y n o raw
HJ Ha0 Ha1 Ha2 Hn Hx0 Hxn Hy0 Hyn Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hsx Hsy Hbx Hby Hmx Hmy Hrx Hhx Hry Hhy.
pose proof (AR_laws_ok rsegs B) as LAWS. pose proof rtsb_segs_low as segs_low.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (ESTACK = 4096) as Hes by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
assert (HPRE : ecall_pre rsegs B lyc Sc W regsT memT mdc).
{ eapply ecall_pre_at; try eassumption; [zlia|]. rewrite Hra. exact Hraw. }
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (Hlo2 : ly_stk_lo lyc + 2 * ESTACK <= spZ regsT) by (rewrite Eslo, Hsp'; zlia).
assert (Hpres2E : forall a, spZ regsT - 2 * ESTACK <= a < spZ regsT -> apresent (w_H W) memT a)
by (intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia).
eapply SRr_mono.
{ exact (ABCMP lyc Sc W regsT memT mdc x y n HPRE Hlo2 Hpres2E Ha0 Ha1 Ha2 Hn Hx0 Hxn Hy0 Hyn Hsx Hsy
ltac:(rewrite Hsp'; exact Hbx) ltac:(rewrite Hsp'; exact Hby) Hmx Hmy Hrx Hhx Hry Hhy). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HAR2 & HP & Hsame & Hres & Hcmp & Hfr & Hpres2).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2, v.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write rsegs B LAWS segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
(fun a => sp0 + o - 2 * ESTACK <= a < sp0 + o) Sc own HJ).
- intros a Ha Hna. apply (Hfr a Ha). exact Hna.
- exact Hpres2.
- exact Hsame.
- intros a Ha; left; left; zlia.
- exact HAR2.
- reflexivity. - reflexivity. - zlia. - exact Hfrs. - exact HQT. }
split; [exact HP|]. split; [exact Hsame|]. split; [exact Hres|]. split; [exact Hcmp|]. split; [exact Hfr | exact Hpres2].
Qed.

(* ================================ the cut state at 0x83b38 from what the tail wrote ================================ *)
Lemma c2_fin : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (buf n mask : Z)
(fpos : Z) S1 W1 (regs1 : bvmap 5 word) mem1 md1 (regsF : bvmap 5 word) memF mdF,
cc_st2 B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf n mask fpos S1 W1 regs1 mem1 md1 ->
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 ((CC_CID, fpos) :: own) lyc S1 W1 memF mdF k ->
same_io md1 mdF ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (cc_rbase (spZ regs) - 2 * ESTACK <= a < cc_rbase (spZ regs)) ->
 ~ (shadow_addr (frame_addr lyc CC_CID fpos) + 4 <= a < shadow_addr (frame_addr lyc CC_CID fpos) + 9) ->
 aview rsegs (w_H W1) memF a = aview rsegs (w_H W1) mem1 a) ->
(forall i, 4 <= i < 9 -> aview rsegs (w_H W1) memF (shadow_addr (frame_addr lyc CC_CID fpos) + i) = Some 248) ->
getr regsF 3 = getr regs1 3 -> getr regsF 4 = getr regs1 4 -> getr regsF 8 = getr regs1 8 ->
getr regsF 9 = getr regs1 9 -> getr regsF 23 = getr regs1 23 -> getr regsF 24 = getr regs1 24 ->
cc_st3 B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf n mask fpos S1 W1 regsF memF mdF.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf n mask fpos S1 W1 regs1 mem1 md1 regsF memF mdF
H2 HJF HioF KEEP H248 R3 R4 R8 R9 R23 R24.
unfold cc_st3, cc_frame.
destruct H2 as (HP & HFR & HFSH & HWANT & G2 & G25 & G28).
pose proof HP as ((HJc & Hra & Hra4 & Hgp & Htp & Hsp16 & HspT & Hsp0 & Hev) & P10 & P11 & Pn & P12 & P13 & Pm
& Pb0 & Pb63 & Pblk & Pra & Phv & Pam & Pout & Pg0 & Pg1 & Pcid & Pcnt & Ptab).
destruct HFR as (HJ1 & Hfr & Hnin & Hab & Hch & Hsec & Hres & Hnev & Hbb & Hmo & Hio & Hcl & HF4 & HFc & HFapp & HF32
& Hflag & Hsav & H24 & H32 & H40 & H48 & H56 & R3' & R4' & R8' & R9' & R23' & R24').
set (F := frame_addr lyc CC_CID fpos) in *.
set (R1 := cc_rbase (spZ regs)) in *.
pose proof HJc as (HARc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _ & _).
destruct Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof (cc_rbase_bounds (spZ regs) Hsp16) as [HR32 HRb]. fold R1 in HR32, HRb.
unfold T_csv_STK_B in HspT. unfold CC_FRAME in HRb.
assert (Hes : ESTACK = 4096) by reflexivity. pose proof asan_consts as (C1 & _).
assert (FB : fs_frame_bytes CC_CID = 256) by reflexivity.
pose proof (rck_fbounds CC_CID F ltac:(unfold CC_CID; lia) HF32 ltac:(rewrite FB; exact HFapp))
as (_ & _ & HS0 & HSc & HSd & _).
rewrite FB in HSc, HSd. change (256 / 8) with 32 in HSc, HSd.
pose proof HJ1 as (HAR1 & _).
assert (Hfin : In (CC_CID, fpos) (frames S1)) by (rewrite Hfr; left; reflexivity).
destruct (frame_facts B lyc S1 _ CC_CID fpos (proj1 HAR1) Hfin) as (Hc10 & Hpos & _).
assert (OWN : forall a, shadow_addr F + 4 <= a < shadow_addr F + 9 -> aowned B lyc Sc a).
{ intros a Ha. apply (own_free_frame_shadow B lyc Sc _ CC_CID fpos a (proj1 HARc) Hc10 Hpos Hnin).
  rewrite FB. change (256 / 8) with 32. fold F. lia. }
assert (KST : forall a, R1 <= a < spZ regs -> aview rsegs (w_H W1) memF a = aview rsegs (w_H W1) mem1 a).
{ intros a Ha. apply KEEP; lia. }
assert (KFR : forall a, F <= a < F + 256 -> aview rsegs (w_H W1) memF a = aview rsegs (w_H W1) mem1 a).
{ intros a Ha. apply KEEP; lia. }
split; [exact HP|].
split.
{ split; [exact HJF|].
  split; [exact Hfr|]. split; [exact Hnin|]. split; [exact Hab|]. split; [exact Hch|]. split; [exact Hsec|].
  split; [exact Hres|]. split; [exact Hnev|]. split; [exact Hbb|]. split; [exact Hmo|].
  split; [exact (same_io_trans _ _ _ Hio HioF)|].
  split.
  { intros a Ha Hw Hno. rewrite (KEEP a Ha); [exact (Hcl a Ha Hw Hno)| |].
    - unfold T_csv_STK_B in Hw. lia.
    - intros Hg. exact (Hno (OWN a Hg)). }
  split; [exact HF4|]. split; [exact HFc|]. split; [exact HFapp|]. split; [exact HF32|].
  split; [rewrite <- Hflag; apply rdword_ext; intros j Hj; apply KFR; lia|].
  split.
  { unfold cc_saved in Hsav |- *. intros j Hj. rewrite <- (Hsav j Hj). apply rdword_ext. intros i Hi. apply KST. lia. }
  split; [rewrite <- H24; apply rdword_ext; intros j Hj; apply KST; lia|].
  split; [rewrite <- H32; apply rdword_ext; intros j Hj; apply KST; lia|].
  split; [rewrite <- H40; apply rdword_ext; intros j Hj; apply KST; lia|].
  split; [rewrite <- H48; apply rdword_ext; intros j Hj; apply KST; lia|].
  split; [rewrite <- H56; apply rdword_ext; intros j Hj; apply KST; lia|].
  rewrite R3, R4, R8, R9, R23, R24. repeat (split; [assumption|]). assumption. }
split.
{ unfold rt_fsh in HFSH |- *. destruct c2_sh_len as [LA LC]. rewrite LA in HFSH. rewrite LC. intros i Hi.
  destruct (Z_lt_le_dec i 4) as [Hi4|Hi4]; [|destruct (Z_lt_le_dec i 9) as [Hi9|Hi9]].
  - rewrite KEEP by lia. rewrite (HFSH i Hi). f_equal. apply c2_sh_AC; lia.
  - rewrite H248 by lia. f_equal. symmetry. apply c2_sh_C48. lia.
  - rewrite KEEP by lia. rewrite (HFSH i Hi). f_equal. apply c2_sh_AC; lia. }
{ unfold mbytes_at in HWANT |- *. intros j Hj. rewrite <- (HWANT j Hj). apply c2_mbyte_of_aview.
  pose proof (RateCsv.csv_list_length mask ltac:(lia)) as HL17.
  rewrite RateCsv.csv_bytes_length in Hj. apply KFR. lia. }
Qed.

(* shadow_addr and the engine's shadow_of_addr are the same map *)
Lemma c2_sh_eq : forall x, shadow_addr x = shadow_of_addr SHADOW_OFF x.
Proof. intros x. reflexivity. Qed.
Lemma c2_band : forall x, 0 <= x < 2 ^ 47 -> kLowMemEnd <= shadow_addr x < kHighMemBeg.
Proof. intros x Hx. rewrite c2_sh_eq. apply rtmb_shadow_band. unfold kHighMemEnd. lia. Qed.
Lemma c2_div_out : forall x F, F mod 8 = 0 -> 0 <= x -> 0 <= F -> ~ (F <= x < F + 256) ->
x / 8 < F / 8 \/ F / 8 + 32 <= x / 8.
Proof.
intros x F H8 Hx HF Hout.
pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Rx.
pose proof (Z.div_mod F 8 ltac:(lia)) as DF. rewrite H8, Z.add_0_r in DF.
remember (x / 8) as qx eqn:Hqx. remember (F / 8) as qF eqn:HqF. clear Hqx HqF.
destruct (Z_lt_le_dec qx qF) as [A|A]; [left; exact A|].
destruct (Z_lt_le_dec qx (qF + 32)) as [C|C]; [exfalso; apply Hout; lia | right; exact C].
Qed.
Lemma c2_out_disj : forall a lo hi, ~ (lo <= a < hi) -> a < lo \/ hi <= a.
Proof.
intros a lo hi H. destruct (Z_lt_le_dec a lo) as [X|X]; [left; exact X | right].
destruct (Z_lt_le_dec a hi) as [Y|Y]; [exfalso; apply H; lia | exact Y].
Qed.

(* ======================================== the two arms ======================================== *)
Section arms.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
(W : world rsegs) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word)
(buf n mask fpos : Z) (S1 : astate) (W1 : world rsegs) (regs1 : bvmap 5 word)
(mem1 : word -> option byte) (md1 : Model).
Hypothesis H2 : cc_st2 B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf n mask fpos S1 W1 regs1 mem1 md1.

Local Notation FA := (frame_addr lyc CC_CID fpos).
Local Notation RB := (cc_rbase (spZ regs)).
Local Notation LEN := (Z.of_nat (length (RateCsv.csv_list mask))).
Local Notation GOAL := (fun W2 c2 => exists S2 regs2 mem2 md2, c2 = cfg_at rsegs CC_PC3 regs2 mem2 md2 /\
cc_st3 B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf n mask fpos S2 W2 regs2 mem2 md2).

Ltac c2_names :=
pose proof H2 as (HP & HFR & HFSH & HWANT & G2 & G25 & G28);
pose proof HP as (HCPRE & P10 & P11 & Pn & P12 & P13 & Pmk & Pb0 & Pb63 & Pblk & Pra & Phv & Pam & Pout & Pg0 & Pg1 & Pcid & Pcnt & Ptab);
pose proof HCPRE as (HJc & Hrok & Hra4 & Hgp & Htp & Hsp16 & HspT & Hsp0 & Hev);
pose proof HFR as (HJ1 & Hfr & Hnin & Hab & Hch & Hsec & Hres & Hnev & Hbb & Hmo & Hio & Hcl & HF4 & HFc & HFapp & HF32
& Hflag & Hsav & H24 & H32 & H40 & H48 & H56 & QQ3 & QQ4 & QQ8 & QQ9 & QQ23 & QQ24).

(* the geometry of the frame, of the realigned base and of the stack, from the cut's journal *)
Lemma c2_base :
AR rsegs B lyc S1 W1 mem1 md1 /\ AR rsegs B lyc Sc W memc mdc /\ In (CC_CID, fpos) (frames S1) /\
FA mod 32 = 0 /\ 4096 <= FA /\ FA + 256 <= alloc_ceiling /\ in_app FA 256 /\
0 <= shadow_addr FA /\ shadow_addr FA + 32 <= alloc_ceiling /\
RB mod 32 = 0 /\ spZ regs - 208 <= RB /\ RB <= spZ regs - 192 /\
sp0 - STK + T_csv_STK_B <= spZ regs /\ spZ regs <= sp0 /\ spZ regs mod 16 = 0 /\
alloc_ceiling <= ly_stk_lo lyc /\ ly_stk_lo lyc + STK <= sp0 /\ sp0 <= 2 ^ 47 /\ sp0 mod 16 = 0.
Proof.
c2_names. pose proof (AR_laws_ok rsegs B) as LAWS. pose proof asan_consts as (C1 & _).
pose proof (proj1 HJ1) as HAR1. pose proof (proj1 HJc) as HARc.
assert (Hfin : In (CC_CID, fpos) (frames S1)) by (rewrite Hfr; left; reflexivity).
pose proof HJc as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _ & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (FB : fs_frame_bytes CC_CID = 256) by reflexivity.
pose proof (rck_fbounds CC_CID FA ltac:(unfold CC_CID; lia) HF32 ltac:(rewrite FB; exact HFapp)) as (_ & _ & BS0 & BSc & _ & _).
rewrite FB in BSc. change (256 / 8) with 32 in BSc.
pose proof (cc_rbase_bounds (spZ regs) Hsp16) as [HR32 HRb]. unfold CC_FRAME in HRb.
split; [exact HAR1|]. split; [exact HARc|]. split; [exact Hfin|].
split; [exact HF32|]. split; [exact HF4|]. split; [exact HFc|]. split; [exact HFapp|].
split; [exact BS0|]. split; [exact BSc|].
split; [exact HR32|]. split; [lia|]. split; [lia|].
split; [lia|]. split; [exact Hsp0|]. split; [exact Hsp16|].
split; [rewrite Eslo; exact Hceil|]. split; [rewrite Eslo; exact Hslo|]. split; [lia | exact Hal16].
Qed.

(* the state at 0x83b38, from the journal and what the runs and the call wrote *)
Lemma c2_close : forall (regsF : bvmap 5 word) memF mdF,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 ((CC_CID, fpos) :: own) lyc S1 W1 memF mdF k ->
same_io md1 mdF ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (RB - 2 * ESTACK <= a < RB) ->
 ~ (shadow_addr FA + 4 <= a < shadow_addr FA + 9) -> aview rsegs (w_H W1) memF a = aview rsegs (w_H W1) mem1 a) ->
(forall i, 4 <= i < 9 -> aview rsegs (w_H W1) memF (shadow_addr FA + i) = Some 248) ->
getr regsF 3 = getr regs1 3 -> getr regsF 4 = getr regs1 4 -> getr regsF 8 = getr regs1 8 ->
getr regsF 9 = getr regs1 9 -> getr regsF 23 = getr regs1 23 -> getr regsF 24 = getr regs1 24 ->
SRr rsegs W1 (mkCfg (mkst regsF (Z_to_bv 64 CC_PC3) memF (seg_rom rsegs)) mdF) GOAL.
Proof.
intros regsF memF mdF HJF HioF KEEP H248 Q3 Q4 Q8 Q9 Q23 Q24.
apply SRr_ret. exists S1, regsF, memF, mdF. split; [reflexivity|].
eapply c2_fin; [exact H2 | exact HJF | exact HioF | exact KEEP | exact H248
| exact Q3 | exact Q4 | exact Q8 | exact Q9 | exact Q23 | exact Q24].
Qed.

(* the write window of a run of the tail: granules 4-8 of the frame's shadow *)
Ltac c2_wrtac Ew :=
intros aa HH; destruct HH as (rr & Hin & Hr);
lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In rr l') in Hin end;
repeat (destruct Hin as [<-|Hin]); try (destruct Hin);
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
rewrite ?Ew in Hr; lia.
(* the write rights of a run of the tail: the frame's shadow granules, every other region read-only *)
Ltac c2_awr Ev Ew :=
lazymatch goal with
| |- awr_ok ?Ex ?rs ?stk ?spx ?fpx ?b0 ?bc ?lyx ?ownx =>
  let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fpx b0 bc lyx ownx)
end;
repeat first
[ apply awr_ok_nil
| apply awr_ok_cons_ro; [cbn; lia|]
| eapply (rck_awr_ok_fsh Ev _ _ STK sp0 FP _ _ lyc _ 23%nat CC_CID fpos);
  [reflexivity | exact Ew | left; reflexivity | cbn; lia
  | cbn; change (fs_frame_bytes CC_CID / 8) with 32; lia |] ].
(* the five shadow bytes the run wrote, read back from the region's chunks *)
Ltac c2_h248 HSx Ev Ew idx Hname :=
lazymatch type of HSx with
| st_ok _ _ ?ssf (restrict (w_H ?Wx) ?msx) =>
  let rc := eval vm_compute in (nth idx (ss_mem ssf) (YP09.mkRegion None 0 0 0 0 [])) in
  let HR := fresh "HR" in let HC := fresh "HC" in let HB := fresh "HB" in
  pose proof (rtsb_region_nth Ev ssf msx idx rc (w_H Wx) HSx eq_refl) as HR;
  lazymatch rc with YP09.mkRegion (Some 23%nat) ?lo ?hi ?wlo ?whi ?cs =>
    pose proof (rtsb_chunks Ev _ 23 (shadow_addr FA) cs lo hi wlo whi HR Ew) as HC;
    pose proof (c2_bytes_of_chunks Ev (w_H Wx) (ms_mem msx) (shadow_addr FA) cs (CC_SH_C ++ repeat 0 12) HC
      c2_shC_bytes ltac:(vm_compute; reflexivity)) as HB
  end;
  assert (Hname : forall i, 4 <= i < 9 -> aview rsegs (w_H Wx) (ms_mem msx) (shadow_addr FA + i) = Some 248)
    by (let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi;
        rewrite (HB i ltac:(destruct c2_sh_len as [_ LC]; rewrite LC; lia)); f_equal; apply c2_sh_C48; lia);
  clear HR HC HB
end.
(* every model a run or the call leaves keeps the I/O state *)
Ltac c2_io := first [ apply same_io_refl | assumption | eapply same_io_trans; [| apply same_io_wvb]; c2_io ].
(* the machine state a run ends in, as the configuration at 0x83b38 *)
Ltac c2_at_pc3 HS :=
lazymatch goal with |- SRr _ _ (mkCfg ?msx ?mdx) _ =>
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict (w_H ?Wx) msx) =>
let Ems := fresh "Ems" in
assert (Ems : msx = mkst (ms_regs msx) (Z_to_bv 64 CC_PC3) (ms_mem msx) (seg_rom rsegs))
  by exact (st_ok_restrict_mkst rsegs (w_H Wx) Ex ssx msx HS eq_refl);
rewrite Ems; clear Ems
end end.

Ltac c2_at_bcmp HS :=
lazymatch goal with |- SRr _ _ (mkCfg ?msx ?mdx) _ =>
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict (w_H ?Wx) msx) =>
let Ems := fresh "Ems" in
assert (Ems : msx = mkst (ms_regs msx) (Z_to_bv 64 0x42200) (ms_mem msx) (seg_rom rsegs))
  by exact (st_ok_restrict_mkst rsegs (w_H Wx) Ex ssx msx HS eq_refl);
rewrite Ems; clear Ems
end end.

(* ---- n = 0: the instrumented check of buf, the compare with 0x5a, granules 4-8 out of scope ---- *)
Lemma c2_arm0 : n = 0 -> SRr rsegs W1 (cfg_at rsegs CC_PC2 regs1 mem1 md1) GOAL.
Proof.
intros Hn0. c2_names.
pose proof c2_base as (HAR1 & HARc & Hfin & BF32 & BF4 & BFc & BFapp & BSH0 & BSHc & BRB32 & BRBlo & BRBhi
& BspA & BspB & Bsp16 & BlycA & BlycB & Bsp47 & Bsp0m).
pose proof (AR_laws_ok rsegs B) as LAWS. pose proof rtsb_segs_low as Hsegs. pose proof rtsb_wx as Hwx.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof c2_tbl_ok as TBL.
assert (Hes : ESTACK = 4096) by reflexivity. unfold T_csv_STK_B in BspA.
destruct Pblk as (m & Hinb & Hmge).
assert (Hm1 : 1 <= m) by (pose proof (Z.le_max_r n 1); lia).
assert (Hrq : req_size m = m) by (unfold req_size; replace (m =? 0) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
assert (Hinb1 : In (buf, m) (ablocks B lyc S1)) by (rewrite Hab; exact Hinb).
destruct (al_blocks _ _ LAWS lyc S1 W1 mem1 md1 buf m HAR1 Hinb1) as (Hb16 & Hb4096 & Hbceil & Hbapp & Hbpres & _ & _).
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc buf m HARc Hinb) as (_ & _ & _ & _ & Hbpresc & _ & _).
rewrite Hrq in Hbceil, Hbapp, Hbpres, Hbpresc.
destruct (al_frames _ _ LAWS lyc S1 W1 mem1 md1 CC_CID fpos HAR1 Hfin) as (_ & _ & _ & Hfspres).
change (fs_frame_bytes CC_CID / 8) with 32 in Hfspres.
assert (Hb8 : buf mod 8 = 0).
{ pose proof Hb16 as HH. apply Z.mod_divide in HH as [q Hq]; [|lia].
  rewrite Hq. replace (q * 16) with ((2 * q) * 8) by ring. apply Z_mod_mult. }
assert (Hd : zdisjoint (buf, req_size m) (FA, fs_frame_bytes CC_CID)).
{ eapply sep_block_frame with (S := S1) (W := W1) (mem := mem1) (md := md1); try eassumption. }
unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Hrq in Hd. change (fs_frame_bytes CC_CID) with 256 in Hd.
assert (HF8 : FA mod 8 = 0).
{ pose proof BF32 as HH. apply Z.mod_divide in HH as [q Hq]; [|lia].
  rewrite Hq. replace (q * 32) with ((4 * q) * 8) by ring. apply Z_mod_mult. }
assert (Hsep : ~ (FA <= buf < FA + 256)) by (destruct Hd as [Hd|Hd]; lia).
clear Hd Pout.
pose proof (c2_band buf ltac:(lia)) as Hband.
(* buf's byte and its shadow byte at the cut's memory *)
assert (Hkeep1 : forall i, 0 <= i < 1 -> aview rsegs (w_H W1) mem1 (buf + i) = aview rsegs (w_H W) memc (buf + i)).
{ intros i Hi. apply Hcl; [lia | lia |].
  intros Ho. exact (proj2 (Hbpresc (buf + i) ltac:(lia)) Ho). }
assert (Hg0 : garr8 rsegs (mrestrict (w_H W1) mem1) buf [0x5a]).
{ apply (c2_garr8_kept (w_H W) memc (w_H W1) mem1 buf [0x5a] (Pg0 Hn0)).
  intros i Hi. cbn [length] in Hi. apply Hkeep1. lia. }
assert (Hbv : aview rsegs (w_H W1) mem1 buf = Some 90) by (apply ccsv_buf0; exact Hg0).
destruct (rtmb_blk_ra rsegs B lyc S1 W1 mem1 md1 buf m buf 1 HAR1 Hinb1 ltac:(lia) ltac:(lia)) as (Hra1 & _).
assert (HRC : exists sb, aview rsegs (w_H W1) mem1 (shadow_of_addr SHADOW_OFF buf) = Some sb /\ saddr_ok buf sb)
by (eapply rtmb_ra_cell; exact Hra1).
destruct HRC as (sb & Hsb & Hsok). pose proof (rtmb_sok_range buf sb Hb8 Hsok) as Hsb7.
rewrite <- c2_sh_eq in Hsb.
(* the symbolic state at 0x83a90 *)
set (EX := [w64 0; w64 buf; w64 (shadow_addr buf); w64 sb]).
assert (Ew33 : ew (Ereg regs1 EX) 33%nat = Z_to_bv 64 buf) by reflexivity.
assert (Ew34 : ew (Ereg regs1 EX) 34%nat = Z_to_bv 64 (shadow_addr buf)) by reflexivity.
assert (Ew35 : ew (Ereg regs1 EX) 35%nat = Z_to_bv 64 sb) by reflexivity.
assert (Ew25 : ew (Ereg regs1 EX) 25%nat = Z_to_bv 64 SHADOW_OFF)
by (rewrite (ew_Ereg_nat regs1 EX 25%nat (25%bv : bv 5) eq_refl); exact G25).
assert (Ew28 : ew (Ereg regs1 EX) 28%nat = Z_to_bv 64 LEN)
by (rewrite (ew_Ereg_nat regs1 EX 28%nat (28%bv : bv 5) eq_refl); exact G28).
assert (Ew9 : bv_unsigned (ew (Ereg regs1 EX) 9%nat) = RB)
by (rewrite (ew_Ereg_nat regs1 EX 9%nat (9%bv : bv 5) eq_refl), QQ9; apply unsigned_lit_small; lia).
assert (Ew23 : bv_unsigned (ew (Ereg regs1 EX) 23%nat) = shadow_addr FA)
by (rewrite (ew_Ereg_nat regs1 EX 23%nat (23%bv : bv 5) eq_refl), QQ23; apply unsigned_lit_small; lia).
assert (Eb23 : base_val (Ereg regs1 EX) (Some 23%nat) = shadow_addr FA) by exact Ew23.
assert (Vw33 : bv_unsigned (ew (Ereg regs1 EX) 33%nat) = buf) by (rewrite Ew33; apply unsigned_lit_small; lia).
assert (Vw34 : bv_unsigned (ew (Ereg regs1 EX) 34%nat) = shadow_addr buf) by (rewrite Ew34; apply unsigned_lit_small; lia).
assert (HFAband : kLowMemEnd <= shadow_addr FA < kHighMemBeg) by (apply c2_band; lia).
pose proof (RateCsv.csv_list_length mask ltac:(lia)) as HL17.
assert (HSL : rtmb_slots rsegs (w_H W1) mem1 RB [(40, n); (48, LEN); (56, buf)]).
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; cbn [fst snd].
  - replace (n mod 2 ^ 64) with n by (symmetry; apply Z.mod_small; lia).
    apply val_mem_of_rdword. exact H40.
  - replace (LEN mod 2 ^ 64) with LEN by (symmetry; apply Z.mod_small; lia).
    apply val_mem_of_rdword. exact H48.
  - replace (buf mod 2 ^ 64) with buf by (symmetry; apply Z.mod_small; lia).
    apply val_mem_of_rdword. exact H56. }
assert (HS : st_ok rsegs (Ereg regs1 EX) (mkSS CC_PC2 sr_atoms (c2_mem_a (SOff 35 0)) None (c2_facts_a [(35%nat, mkAF 0 7 0)]))
(restrict (w_H W1) (mkst regs1 (Z_to_bv 64 CC_PC2) mem1 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute; reflexivity.
  - unfold c2_mem_a, c2_stk_reg, c2_fsh_reg, c2_cell.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
    + apply (rtmb_ro_region rsegs (Ereg regs1 EX) (w_H W1) mem1 9%nat RB 40 64); [exact Ew9 | lia | lia |].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
      * apply (rtmb_slots_chunk rsegs (Ereg regs1 EX) (w_H W1) mem1 RB _ 40 n (SLit 0) HSL);
        [left; reflexivity | rewrite Hn0; reflexivity | lia].
      * apply (rtmb_slots_chunk rsegs (Ereg regs1 EX) (w_H W1) mem1 RB _ 48 LEN (SOff 28 0) HSL);
        [right; left; reflexivity | apply rtsb_den_atom; [exact Ew28 | lia] | lia].
      * apply (rtmb_slots_chunk rsegs (Ereg regs1 EX) (w_H W1) mem1 RB _ 56 buf (SOff 33 0) HSL);
        [right; right; left; reflexivity | apply rtsb_den_atom; [exact Ew33 | lia] | lia].
    + apply (rtmb_rw_region rsegs (Ereg regs1 EX) (w_H W1) mem1 23%nat (shadow_addr FA) 0 32 4 9);
      [exact Ew23 | lia | lia | | ].
      * intros o Ho. exact (proj1 (Hfspres o ltac:(lia))).
      * apply (rtmb_fsh_chunks rsegs (Ereg regs1 EX) (w_H W1) mem1 FA (CC_SH_A ++ repeat 0 12) HFSH c2_sh_bytes).
    + apply (rtmb_cell_region rsegs (Ereg regs1 EX) (w_H W1) mem1 34%nat (shadow_addr buf) sb (SOff 35 0));
      [exact Vw34 | exact Hsb | apply rtsb_den_atom; [exact Ew35 | lia] | lia | lia].
    + apply (rtmb_cell_region rsegs (Ereg regs1 EX) (w_H W1) mem1 33%nat buf 90 (SLit 90));
      [exact Vw33 | exact Hbv | reflexivity | lia | lia].
  - assert (Dsf : RB + 64 <= shadow_addr FA + 0 \/ shadow_addr FA + 32 <= RB + 40) by (try clear Dsf; try clear Dsb; try clear Dsc; try clear Dfb; try clear Dfc; right; lia).
    assert (Dsb : RB + 64 <= shadow_addr buf + 0 \/ shadow_addr buf + 1 <= RB + 40) by (try clear Dsf; try clear Dsb; try clear Dsc; try clear Dfb; try clear Dfc; right; lia).
    assert (Dsc : RB + 64 <= buf + 0 \/ buf + 1 <= RB + 40) by (try clear Dsf; try clear Dsb; try clear Dsc; try clear Dfb; try clear Dfc; right; lia).
    assert (Dfb : shadow_addr FA + 32 <= shadow_addr buf + 0 \/ shadow_addr buf + 1 <= shadow_addr FA + 0).
    { try clear Dsf; try clear Dsb; try clear Dsc; try clear Dfb; try clear Dfc; pose proof (c2_div_out buf FA HF8 ltac:(lia) ltac:(lia) Hsep) as X.
      unfold shadow_addr. destruct X as [X|X]; [right; lia | left; lia]. }
    assert (Dfc : shadow_addr FA + 32 <= buf + 0 \/ buf + 1 <= shadow_addr FA + 0).
    { try clear Dsf; try clear Dsb; try clear Dsc; try clear Dfb; try clear Dfc; pose proof (app_vs_shadow buf m FA 256 buf Hbapp BFapp ltac:(lia) ltac:(lia)) as Y.
      change (256 / 8) with 32 in Y.
      destruct (c2_out_disj buf (shadow_addr FA) (shadow_addr FA + 32) Y) as [Z1|Z1]; [right; lia | left; lia]. }
    assert (Dbc : shadow_addr buf + 1 <= buf + 0 \/ buf + 1 <= shadow_addr buf + 0).
    { try clear Dsf; try clear Dsb; try clear Dsc; try clear Dfb; try clear Dfc; unfold in_app in Hbapp. destruct Hbapp as (_ & [Hlow | [Hhigh _]]); [right | left];
      unfold shadow_addr, shadow_of_addr, SHADOW_OFF, kLowShadowBeg, kLowMemEnd, kHighMemBeg in *; lia. }
    unfold c2_mem_a, c2_stk_reg, c2_fsh_reg, c2_cell.
    cbv [pairwise_disjoint all_disjoint extent_disjoint YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite Ew9, Ew23, Vw33, Vw34.
    repeat split; try exact I;
    first [exact Dsf | exact Dsb | exact Dsc | exact Dfb | exact Dfc | exact Dbc].
  - unfold c2_facts_a, c2_alias_sh. split; [|split].
    + cbn [f_atoms atoms_ok]. split; [|split; [|exact I]].
      * unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Ew33, (unsigned_lit_small buf) by lia.
        change (2 ^ 4) with 16. split; [lia|]. split; [exact Hb16 | lia].
      * unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Ew35, (unsigned_lit_small sb) by lia.
        change (2 ^ 0) with 1. rewrite Z.mod_1_r. split; [lia|]. split; [reflexivity | lia].
    + exact I.
    + cbn [f_alias alias_ok]. split; [|exact I].
      exact (shadow_decl_ok (Ereg regs1 EX) 33%nat 25%nat 34%nat buf SHADOW_OFF Ew33 ltac:(lia) Ew25 Ew34). }
unfold cfg_at. change (w64 CC_PC2) with (Z_to_bv 64 CC_PC2).
Time aj_run_to TBL HS HJ1 CC_PC3.
{ c2_awr (Ereg regs1 EX) Ew23. }
rename HFr into FR1. clear HF HG.
lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (shadow_addr FA + 4 <= a < shadow_addr FA + 9) ->
aview rsegs (w_H W1) (ms_mem msx) a = aview rsegs (w_H W1) mem1 a) end.
{ intros a Ha Hw. refine (c2_kept_win _ _ (w_H W1) mem1 _ _ _ FR1 _ a Ha Hw). c2_wrtac Eb23. }
srr_branch_with TBL HS.
- (* the shadow byte is not 0: its range makes the slow block's compare pass *)
  assert (Hsb1 : 1 <= sb <= 7).
  { rewrite branch_ne_U in Hc. rewrite (U_atom (Ereg regs1 EX) 35%nat sb Ew35 ltac:(lia)), U_SLit in Hc.
    change (zcanon 0) with 0 in Hc. apply negb_true_iff, Z.eqb_neq in Hc. lia. }
  pose proof (st_ok_add_fact rsegs (Ereg regs1 EX) _ _ 35%nat (mkAF 1 7 0) HS
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Ew35, (unsigned_lit_small sb) by lia;
        change (2 ^ 0) with 1; rewrite Z.mod_1_r; split; [lia|]; split; [reflexivity | lia])) as HS2.
  clear HS. rename HS2 into HS.
  Time aj_run_to TBL HS HJ1 CC_PC3.
  { c2_awr (Ereg regs1 EX) Ew23. }
  rename HFr into FR2. clear HF HG.
  lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
  assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (shadow_addr FA + 4 <= a < shadow_addr FA + 9) ->
  aview rsegs (w_H W1) (ms_mem msx) a = aview rsegs (w_H W1) mem1 a) end.
  { intros a Ha Hw. etransitivity;
    [refine (c2_kept_win _ _ (w_H W1) _ _ _ _ FR2 _ a Ha Hw) | exact (KA a Ha Hw)]. c2_wrtac Eb23. }
  c2_h248 HS (Ereg regs1 EX) Ew23 1%nat H248.
  c2_at_pc3 HS.
  apply c2_close.
  1: exact HJ1. 1: c2_io. 1: (intros a Ha _ Hw; exact (KB a Ha Hw)). 1: exact H248.
  all: eapply (c2_reg_kept regs1 EX _ _ (w_H W1)); [exact HS | vm_compute; reflexivity].
- (* the shadow byte is 0: the load is allowed at once *)
  Time aj_run_to TBL HS HJ1 CC_PC3.
  { c2_awr (Ereg regs1 EX) Ew23. }
  rename HFr into FR2. clear HF HG.
  lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
  assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (shadow_addr FA + 4 <= a < shadow_addr FA + 9) ->
  aview rsegs (w_H W1) (ms_mem msx) a = aview rsegs (w_H W1) mem1 a) end.
  { intros a Ha Hw. etransitivity;
    [refine (c2_kept_win _ _ (w_H W1) _ _ _ _ FR2 _ a Ha Hw) | exact (KA a Ha Hw)]. c2_wrtac Eb23. }
  c2_h248 HS (Ereg regs1 EX) Ew23 1%nat H248.
  c2_at_pc3 HS.
  apply c2_close.
  1: exact HJ1. 1: c2_io. 1: (intros a Ha _ Hw; exact (KB a Ha Hw)). 1: exact H248.
  all: eapply (c2_reg_kept regs1 EX _ _ (w_H W1)); [exact HS | vm_compute; reflexivity].
Qed.


(* ---- n > 0, from the `jal` 0x83abc on: the bcmp wrapper, the pointer-overflow test, the check of buf + c ---- *)
Lemma c2_call : forall (c : Z) (regsT : bvmap 5 word) memT mdT,
1 <= n -> c = Z.min LEN (n - 1) ->
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 ((CC_CID, fpos) :: own) lyc S1 W1 memT mdT k ->
same_io md1 mdT ->
(forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W1) memT a = aview rsegs (w_H W1) mem1 a) ->
getr regsT 10 = w64 buf -> getr regsT 11 = w64 (FA + 32) -> getr regsT 12 = w64 c ->
getr regsT 1 = w64 0x83ac0 -> getr regsT 2 = w64 RB ->
getr regsT 3 = getr regs1 3 -> getr regsT 4 = getr regs1 4 -> getr regsT 8 = getr regs1 8 ->
getr regsT 9 = getr regs1 9 -> getr regsT 23 = getr regs1 23 -> getr regsT 24 = getr regs1 24 ->
getr regsT 25 = w64 SHADOW_OFF -> getr regsT 18 = w64 buf -> getr regsT 19 = w64 c ->
SRr rsegs W1 (mkCfg (mkst regsT (Z_to_bv 64 0x42200) memT (seg_rom rsegs)) mdT) GOAL.
Proof using ABCMP H2.
intros c regsT memT mdT Hn1 Ec HJT HioT KT T10 T11 T12 T1 T2 T3 T4 T8 T9 T23 T24 T25 T18 T19.
c2_names.
pose proof c2_base as (HAR1 & HARc & Hfin & BF32 & BF4 & BFc & BFapp & BSH0 & BSHc & BRB32 & BRBlo & BRBhi
& BspA & BspB & Bsp16 & BlycA & BlycB & Bsp47 & Bsp0m).
pose proof (AR_laws_ok rsegs B) as LAWS. pose proof rtsb_segs_low as Hsegs. pose proof rtsb_wx as Hwx.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof c2_tbl_ok as TBL.
assert (Hes : ESTACK = 4096) by reflexivity. unfold T_csv_STK_B in BspA.
pose proof (proj1 HJT) as HART.
destruct Pblk as (m & Hinb & Hmge).
assert (Hmn : n <= m) by (pose proof (Z.le_max_l n 1); lia).
assert (Hrq : req_size m = m) by (unfold req_size; replace (m =? 0) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
assert (Hinb1 : In (buf, m) (ablocks B lyc S1)) by (rewrite Hab; exact Hinb).
destruct (al_blocks _ _ LAWS lyc S1 W1 mem1 md1 buf m HAR1 Hinb1) as (Hb16 & Hb4096 & Hbceil & Hbapp & _ & _ & _).
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc buf m HARc Hinb) as (_ & _ & _ & _ & Hbpresc & _ & _).
rewrite Hrq in Hbceil, Hbapp, Hbpresc.
assert (Hd : zdisjoint (buf, req_size m) (FA, fs_frame_bytes CC_CID)).
{ eapply sep_block_frame with (S := S1) (W := W1) (mem := mem1) (md := md1); try eassumption. }
unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Hrq in Hd. change (fs_frame_bytes CC_CID) with 256 in Hd.
assert (HF8 : FA mod 8 = 0).
{ pose proof BF32 as HH. apply Z.mod_divide in HH as [q Hq]; [|lia].
  rewrite Hq. replace (q * 32) with ((4 * q) * 8) by ring. apply Z_mod_mult. }
pose proof (RateCsv.csv_list_length mask ltac:(lia)) as HL17.
assert (Hc0 : 0 <= c <= 17 /\ c <= n - 1) by (rewrite Ec; lia).
destruct Hc0 as (Hc0 & Hcn).
assert (Hsepc : ~ (FA <= buf + c < FA + 256)) by (destruct Hd as [Hd|Hd]; lia).
clear Hd Pout.
(* buf's bytes at the call's memory: a client block's bytes are not the runtime's *)
assert (Hlen : Z.of_nat (length (RateCsv.csv_cut (RateCsv.csv_list mask) n ++ [0])) = c + 1).
{ rewrite length_app, Nat2Z.inj_add, (proj2 (ccsv_c_min (RateCsv.csv_list mask) n Hn1)).
  change (length [0]) with 1%nat. rewrite Ec. lia. }
assert (Kbuf : forall i, 0 <= i < Z.of_nat (length (RateCsv.csv_cut (RateCsv.csv_list mask) n ++ [0])) ->
  aview rsegs (w_H W1) memT (buf + i) = aview rsegs (w_H W) memc (buf + i)).
{ intros i Hi. rewrite Hlen in Hi. rewrite (KT (buf + i)) by lia. apply Hcl; [lia | lia |].
  intros Ho. exact (proj2 (Hbpresc (buf + i) ltac:(lia)) Ho). }
assert (GT : garr8 rsegs (mrestrict (w_H W1) memT) buf (RateCsv.csv_cut (RateCsv.csv_list mask) n ++ [0])).
{ apply (c2_garr8_kept (w_H W) memc (w_H W1) memT buf _ (Pg1 ltac:(lia))). exact Kbuf. }
(* want's bytes at the call's memory *)
assert (HWT : mbytes_at rsegs (mrestrict (w_H W1) memT) (FA + 32) (RateCsv.csv_bytes (RateCsv.csv_list mask))).
{ unfold mbytes_at in HWANT |- *. intros j Hj. rewrite <- (HWANT j Hj). apply c2_mbyte_of_aview.
  rewrite RateCsv.csv_bytes_length in Hj. apply KT. lia. }
assert (Wv : forall i, 0 <= i < LEN ->
  aview rsegs (w_H W1) memT (FA + 32 + i) = Some (nth (Z.to_nat i) (RateCsv.csv_list mask) 0)).
{ apply c2_want_av; [exact HWT|].
  eapply Forall_impl; [|exact (RateCsv.csv_list_chars mask ltac:(lia))]. intros x Hx. cbv beta in Hx |- *. lia. }
assert (EQ : forall i, 0 <= i < c -> aview rsegs (w_H W1) memT (buf + i) = aview rsegs (w_H W1) memT (FA + 32 + i)).
{ intros i Hi. apply (ccsv_bcmp_eq_av rsegs (w_H W1) memT buf (FA + 32) (RateCsv.csv_list mask) n GT Wv).
  rewrite (proj2 (ccsv_c_min (RateCsv.csv_list mask) n Hn1)). rewrite <- Ec. exact Hi. }
(* the frame's shadow at the call's memory *)
assert (HFSHT : rt_fsh rsegs (w_H W1) memT FA (CC_SH_A ++ repeat 0 12)).
{ apply (rtmb_fsh_kept rsegs (w_H W1) mem1 (w_H W1) memT FA _ HFSH). intros i Hi.
  destruct c2_sh_len as [LA _]. rewrite LA in Hi. apply KT. lia. }
assert (SPT : spZ regsT = RB).
{ unfold spZ at 1. rewrite T2. unfold w64. apply unsigned_lit_small. lia. }
(* ---- the call ---- *)
eapply SRr_bind.
{ eapply (c2_bcmp_at W1 regsT memT STK sp0 FP ly S W0 mem0 md0 ((CC_CID, fpos) :: own) lyc S1 mdT k
    buf (FA + 32) c (RB - sp0) (w64 0x83ac0) HJT T10 T11 T12).
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - rewrite SPT. lia.
  - pose proof (Z.div_mod RB 32 ltac:(lia)) as D32. pose proof (Z.div_mod sp0 16 ltac:(lia)) as D16.
    symmetry. apply (Z.mod_unique (RB - sp0) 16 (2 * (RB / 32) - sp0 / 16) 0); [left; lia | lia].
  - lia.
  - lia.
  - rewrite T3, QQ3. exact Hgp.
  - rewrite T4, QQ4. exact Htp.
  - exact T1.
  - vm_compute. reflexivity.
  - intros a Ha. rewrite SPT. split; [|lia].
    replace a with (buf + Z.of_nat (Z.to_nat (a - buf))) by lia.
    rewrite (ccsv_garr8_aview rsegs (w_H W1) memT buf _ (Z.to_nat (a - buf)) GT) by lia. discriminate.
  - intros a Ha. rewrite SPT. split; [|lia].
    replace a with (FA + 32 + (a - FA - 32)) by lia. rewrite (Wv (a - FA - 32)) by lia. discriminate.
  - intros a Ha. lia.
  - intros a Ha. lia.
  - unfold amem_range in Pam |- *. lia.
  - destruct (rck_fbounds CC_CID FA ltac:(unfold CC_CID; lia) BF32
      ltac:(change (fs_frame_bytes CC_CID) with 256; exact BFapp)) as (_ & _ & _ & _ & _ & HAM).
    apply HAM; change (fs_frame_bytes CC_CID) with 256; lia.
  - exact (proj1 (rtmb_blk_ra rsegs B lyc S1 W1 memT mdT buf m buf c HART Hinb1 ltac:(lia) ltac:(lia))).
  - exact (proj2 (rtmb_blk_ra rsegs B lyc S1 W1 memT mdT buf m buf c HART Hinb1 ltac:(lia) ltac:(lia))).
  - replace (FA + 32) with (FA + 8 * Z.of_nat 4 + 0) by lia.
    apply (rtmb_fsh_ra_obj rsegs (w_H W1) memT FA (CC_SH_A ++ repeat 0 12) 4 5 0 0 c HFSHT HF8);
    [cbn; lia | | lia | cbn; lia | left; reflexivity].
    intros g Hg. do 9 (destruct g as [|g]; [try reflexivity; lia|]). lia.
  - intros _ s Hs. pose proof (c2_hull_in FA c BF32 ltac:(lia) ltac:(lia) s Hs) as Hs'.
    replace s with (shadow_addr FA + (s - shadow_addr FA)) by lia.
    rewrite (HFSHT (s - shadow_addr FA)) by (destruct c2_sh_len as [LA _]; rewrite LA; lia). discriminate. }
cbv beta. intros W2 cf _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HPR & Hsame & Hv & Hcmp & Hfr2 & Hpres2).
assert (Hv0 : v = w64 0) by (apply (proj2 Hcmp); exact EQ).
assert (Hio2 : same_io md1 md2) by (eapply same_io_trans; [exact HioT | apply same_io_materialized; exact Hsame]).
assert (P18 : getr regs2 18 = w64 buf) by (rewrite <- T18; exact (HPR 18 ltac:(unfold acallee_saved; lia))).
assert (P19 : getr regs2 19 = w64 c) by (rewrite <- T19; exact (HPR 19 ltac:(unfold acallee_saved; lia))).
assert (P25 : getr regs2 25 = w64 SHADOW_OFF) by (rewrite <- T25; exact (HPR 25 ltac:(unfold acallee_saved; lia))).
assert (P3 : getr regs2 3 = getr regs1 3) by (rewrite <- T3; exact (HPR 3 ltac:(unfold acallee_saved; lia))).
assert (P4 : getr regs2 4 = getr regs1 4) by (rewrite <- T4; exact (HPR 4 ltac:(unfold acallee_saved; lia))).
assert (P8 : getr regs2 8 = getr regs1 8) by (rewrite <- T8; exact (HPR 8 ltac:(unfold acallee_saved; lia))).
assert (P9 : getr regs2 9 = getr regs1 9) by (rewrite <- T9; exact (HPR 9 ltac:(unfold acallee_saved; lia))).
assert (P23 : getr regs2 23 = getr regs1 23) by (rewrite <- T23; exact (HPR 23 ltac:(unfold acallee_saved; lia))).
assert (P24 : getr regs2 24 = getr regs1 24) by (rewrite <- T24; exact (HPR 24 ltac:(unfold acallee_saved; lia))).
assert (Pa0 : getr regs2 10 = Z_to_bv 64 0) by (rewrite Hv, Hv0; reflexivity).
(* the bytes after the call: all but its 2 ESTACK below R1 *)
assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (RB - 2 * ESTACK <= a < RB) ->
  aview rsegs (w_H W1) mem2 a = aview rsegs (w_H W1) mem1 a).
{ intros a Ha Hw. rewrite (Hfr2 a Ha) by lia. exact (KT a Ha). }
pose proof (proj1 HJ2) as HAR2.
destruct (al_frames _ _ LAWS lyc S1 W1 mem2 md2 CC_CID fpos HAR2 Hfin) as (_ & _ & _ & Hfspres2).
change (fs_frame_bytes CC_CID / 8) with 32 in Hfspres2.
assert (GB2 : garr8 rsegs (mrestrict (w_H W1) mem2) buf (RateCsv.csv_cut (RateCsv.csv_list mask) n ++ [0])).
{ apply (c2_garr8_kept (w_H W1) memT (w_H W1) mem2 buf _ GT). intros i Hi. rewrite Hlen in Hi. apply Hfr2; lia. }
assert (Hlast : aview rsegs (w_H W1) mem2 (buf + c) = Some 0).
{ rewrite Ec. exact (ccsv_last_min rsegs (w_H W1) mem2 buf (RateCsv.csv_list mask) n Hn1 GB2). }
destruct (rtmb_blk_ra rsegs B lyc S1 W1 mem2 md2 buf m (buf + c) 1 HAR2 Hinb1 ltac:(lia) ltac:(lia)) as (Hra2 & _).
destruct (rtmb_ra_cell _ _ _ Hra2) as (sb & Hsb & Hsok).
pose proof (c2_sok_range _ _ Hsok) as Hsb7.
rewrite <- c2_sh_eq in Hsb.
assert (HFSH2 : rt_fsh rsegs (w_H W1) mem2 FA (CC_SH_A ++ repeat 0 12)).
{ apply (rtmb_fsh_kept rsegs (w_H W1) mem1 (w_H W1) mem2 FA _ HFSH). intros i Hi.
  destruct c2_sh_len as [LA _]. rewrite LA in Hi. apply K2; lia. }
pose proof (c2_band (buf + c) ltac:(lia)) as Hbandc.
assert (HFAband : kLowMemEnd <= shadow_addr FA < kHighMemBeg) by (apply c2_band; lia).
(* ---- the state at 0x83ac0 ---- *)
set (EX2 := [w64 (buf + c); w64 (shadow_addr (buf + c)); w64 sb]).
assert (Ew32 : ew (Ereg regs2 EX2) 32%nat = Z_to_bv 64 (buf + c)) by reflexivity.
assert (Ew33 : ew (Ereg regs2 EX2) 33%nat = Z_to_bv 64 (shadow_addr (buf + c))) by reflexivity.
assert (Ew34 : ew (Ereg regs2 EX2) 34%nat = Z_to_bv 64 sb) by reflexivity.
assert (Ew18 : ew (Ereg regs2 EX2) 18%nat = Z_to_bv 64 buf)
by (rewrite (ew_Ereg_nat regs2 EX2 18%nat (18%bv : bv 5) eq_refl); exact P18).
assert (Ew19 : ew (Ereg regs2 EX2) 19%nat = Z_to_bv 64 c)
by (rewrite (ew_Ereg_nat regs2 EX2 19%nat (19%bv : bv 5) eq_refl); exact P19).
assert (Ew25 : ew (Ereg regs2 EX2) 25%nat = Z_to_bv 64 SHADOW_OFF)
by (rewrite (ew_Ereg_nat regs2 EX2 25%nat (25%bv : bv 5) eq_refl); exact P25).
assert (Ew23 : bv_unsigned (ew (Ereg regs2 EX2) 23%nat) = shadow_addr FA)
by (rewrite (ew_Ereg_nat regs2 EX2 23%nat (23%bv : bv 5) eq_refl), P23, QQ23; apply unsigned_lit_small; lia).
assert (Eb23 : base_val (Ereg regs2 EX2) (Some 23%nat) = shadow_addr FA) by exact Ew23.
assert (Vw32 : bv_unsigned (ew (Ereg regs2 EX2) 32%nat) = buf + c) by (rewrite Ew32; apply unsigned_lit_small; lia).
assert (Vw33 : bv_unsigned (ew (Ereg regs2 EX2) 33%nat) = shadow_addr (buf + c))
by (rewrite Ew33; apply unsigned_lit_small; lia).
assert (HS : st_ok rsegs (Ereg regs2 EX2) (mkSS 0x83ac0 c2_sr_c (c2_mem_c (SOff 34 0)) None (c2_facts_c [(34%nat, mkAF 0 7 0)]))
  (restrict (w_H W1) (mkst regs2 (Z_to_bv 64 0x83ac0) mem2 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - unfold c2_sr_c. apply regs_ok_pin; [apply regs_ok_Ereg | |].
    + intros Hc. apply (f_equal (@bv_unsigned 5)) in Hc. vm_compute in Hc. discriminate Hc.
    + rewrite Pa0. reflexivity.
  - vm_compute; reflexivity.
  - unfold c2_mem_c, c2_fsh_reg, c2_cell.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    + apply (rtmb_rw_region rsegs (Ereg regs2 EX2) (w_H W1) mem2 23%nat (shadow_addr FA) 0 32 4 9);
      [exact Ew23 | lia | lia | |].
      * intros o Ho. exact (proj1 (Hfspres2 o ltac:(lia))).
      * apply (rtmb_fsh_chunks rsegs (Ereg regs2 EX2) (w_H W1) mem2 FA (CC_SH_A ++ repeat 0 12) HFSH2 c2_sh_bytes).
    + apply (rtmb_cell_region rsegs (Ereg regs2 EX2) (w_H W1) mem2 33%nat (shadow_addr (buf + c)) sb (SOff 34 0));
      [exact Vw33 | exact Hsb | apply rtsb_den_atom; [exact Ew34 | lia] | lia | lia].
    + apply (rtmb_cell_region rsegs (Ereg regs2 EX2) (w_H W1) mem2 32%nat (buf + c) 0 (SLit 0));
      [exact Vw32 | exact Hlast | reflexivity | lia | lia].
  - assert (Dfb : shadow_addr FA + 32 <= shadow_addr (buf + c) + 0 \/ shadow_addr (buf + c) + 1 <= shadow_addr FA + 0).
    { pose proof (c2_div_out (buf + c) FA HF8 ltac:(lia) ltac:(lia) Hsepc) as X.
      unfold shadow_addr. destruct X as [X|X]; [right; lia | left; lia]. }
    assert (Dfc : shadow_addr FA + 32 <= buf + c + 0 \/ buf + c + 1 <= shadow_addr FA + 0).
    { try clear Dfb. pose proof (app_vs_shadow buf m FA 256 (buf + c) Hbapp BFapp ltac:(lia) ltac:(lia)) as Y.
      change (256 / 8) with 32 in Y.
      destruct (c2_out_disj (buf + c) (shadow_addr FA) (shadow_addr FA + 32) Y) as [Z1|Z1]; [right; lia | left; lia]. }
    assert (Dbc : shadow_addr (buf + c) + 1 <= buf + c + 0 \/ buf + c + 1 <= shadow_addr (buf + c) + 0).
    { try clear Dfb; try clear Dfc. unfold in_app in Hbapp. destruct Hbapp as (_ & [Hlow | [Hhigh _]]); [right | left];
      unfold shadow_addr, shadow_of_addr, SHADOW_OFF, kLowShadowBeg, kLowMemEnd, kHighMemBeg in *; lia. }
    unfold c2_mem_c, c2_fsh_reg, c2_cell.
    cbv [pairwise_disjoint all_disjoint extent_disjoint YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite Ew23, Vw33, Vw32.
    repeat split; try exact I;
    first [exact Dfb | exact Dfc | exact Dbc].
  - unfold c2_facts_c, c2_alias_sh. split; [|split].
    + cbn [f_atoms atoms_ok]. split; [|exact I].
      unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Ew34, (unsigned_lit_small sb) by lia.
      change (2 ^ 0) with 1. rewrite Z.mod_1_r. split; [lia|]. split; [reflexivity | lia].
    + exact I.
    + cbn [f_alias alias_ok]. split; [|split; [|exact I]].
      * rewrite (c2_denot_add (Ereg regs2 EX2) 18 19 buf c Ew18 Ew19 ltac:(lia) ltac:(lia) ltac:(lia)).
        symmetry. apply rtsb_den_atom; [exact Ew32 | lia].
      * exact (shadow_decl_ok (Ereg regs2 EX2) 32%nat 25%nat 33%nat (buf + c) SHADOW_OFF Ew32 ltac:(lia) Ew25 Ew33). }
change (w64 0x83ac0) with (Z_to_bv 64 0x83ac0).
Time aj_run_to TBL HS HJ2 CC_PC3.
{ c2_awr (Ereg regs2 EX2) Ew23. }
rename HFr into FR1. clear HF HG.
lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (shadow_addr FA + 4 <= a < shadow_addr FA + 9) ->
aview rsegs (w_H W1) (ms_mem msx) a = aview rsegs (w_H W1) mem2 a) end.
{ intros a Ha Hw. refine (c2_kept_win _ _ (w_H W1) mem2 _ _ _ FR1 _ a Ha Hw). c2_wrtac Eb23. }
srr_branch_with TBL HS.
- (* 0x83ac8 `bltu a0,s3` with a0 = ~buf, s3 = c: taken only if buf + c wraps, and buf + c < 2 ^ 63 *)
  exfalso.
  assert (Enot : sv_denot (Ereg regs2 EX2) (SAlu ALU_XOR (SOff 18 0) (SLit (-1))) = w64 (Z.lnot buf)).
  { rewrite (rtb_lnot_w64 buf) by lia. rewrite denot_lit_U, (U_not (Ereg regs2 EX2) 18 buf Ew18 ltac:(lia)). reflexivity. }
  rewrite Enot, (rtsb_den_atom _ 19 c Ew19 ltac:(lia)) in Hc. change (Z_to_bv 64 c) with (w64 c) in Hc.
  rewrite (rtb_not_ltu buf c ltac:(lia) ltac:(lia) ltac:(lia)) in Hc. discriminate Hc.
- clear Hc.
  Time aj_run_to TBL HS HJ2 CC_PC3.
  { c2_awr (Ereg regs2 EX2) Ew23. }
  rename HFr into FR2. clear HF HG.
  lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
  assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (shadow_addr FA + 4 <= a < shadow_addr FA + 9) ->
  aview rsegs (w_H W1) (ms_mem msx) a = aview rsegs (w_H W1) mem2 a) end.
  { intros a Ha Hw. etransitivity;
    [refine (c2_kept_win _ _ (w_H W1) _ _ _ _ FR2 _ a Ha Hw) | exact (KA a Ha Hw)]. c2_wrtac Eb23. }
  srr_branch_with TBL HS.
  + (* the shadow byte of buf + c is not 0: the slow block *)
    assert (Hsb1 : 1 <= sb <= 7).
    { rewrite branch_ne_U in Hc. rewrite (U_atom (Ereg regs2 EX2) 34%nat sb Ew34 ltac:(lia)), U_SLit in Hc.
      change (zcanon 0) with 0 in Hc. apply negb_true_iff, Z.eqb_neq in Hc. lia. }
    pose proof (st_ok_add_fact rsegs (Ereg regs2 EX2) _ _ 34%nat (mkAF 1 7 0) HS
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Ew34, (unsigned_lit_small sb) by lia;
          change (2 ^ 0) with 1; rewrite Z.mod_1_r; split; [lia|]; split; [reflexivity | lia])) as HS2.
    clear HS Hc. rename HS2 into HS.
    Time aj_run_to TBL HS HJ2 CC_PC3.
    { c2_awr (Ereg regs2 EX2) Ew23. }
    rename HFr into FR3. clear HF HG.
    lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (KC : forall a, 0 <= a < 2 ^ 64 -> ~ (shadow_addr FA + 4 <= a < shadow_addr FA + 9) ->
    aview rsegs (w_H W1) (ms_mem msx) a = aview rsegs (w_H W1) mem2 a) end.
    { intros a Ha Hw. etransitivity;
      [refine (c2_kept_win _ _ (w_H W1) _ _ _ _ FR3 _ a Ha Hw) | exact (KB a Ha Hw)]. c2_wrtac Eb23. }
    srr_branch_with TBL HS.
    * (* (buf + c) mod 8 < the shadow byte: the load is allowed *)
      Time aj_run_to TBL HS HJ2 CC_PC3.
      { c2_awr (Ereg regs2 EX2) Ew23. }
      rename HFr into FR4. clear HF HG.
      lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
      assert (KD : forall a, 0 <= a < 2 ^ 64 -> ~ (shadow_addr FA + 4 <= a < shadow_addr FA + 9) ->
      aview rsegs (w_H W1) (ms_mem msx) a = aview rsegs (w_H W1) mem2 a) end.
      { intros a Ha Hw. etransitivity;
        [refine (c2_kept_win _ _ (w_H W1) _ _ _ _ FR4 _ a Ha Hw) | exact (KC a Ha Hw)]. c2_wrtac Eb23. }
      c2_h248 HS (Ereg regs2 EX2) Ew23 0%nat H248.
      c2_at_pc3 HS.
      apply c2_close.
      1: exact HJ2. 1: c2_io. 1: (intros a Ha Hw1 Hw; rewrite (KD a Ha Hw); exact (K2 a Ha Hw1)). 1: exact H248.
      all: (etransitivity; [eapply (c2_reg_kept regs2 EX2 _ _ (w_H W1)); [exact HS | vm_compute; reflexivity] | assumption]).
    * (* the error arm: the shadow byte allows the byte buf + c *)
      exfalso.
      pose proof (rtmb_ra_slow _ _ Hsok ltac:(lia)) as (_ & Hlt).
      pose proof (Z.mod_pos_bound (buf + c) 8 ltac:(lia)) as Hm8.
      assert (Eand : sv_denot (Ereg regs2 EX2) (SAlu ALU_AND (SOff 32 0) (SLit 7)) = w64 ((buf + c) mod 8)).
      { rewrite denot_lit_U, U_SAlu. cbn [zalu_raw]. rewrite (U_atom (Ereg regs2 EX2) 32 (buf + c) Ew32 ltac:(lia)), U_SLit.
        change (zcanon 7) with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
        rewrite zcanon_id; [reflexivity|]. unfold M64. lia. }
      rewrite Eand, (rtsb_den_atom _ 34 sb Ew34 ltac:(lia)) in Hc. change (Z_to_bv 64 sb) with (w64 sb) in Hc.
      cbn [branch_taken] in Hc. rewrite bv_lts_signed in Hc.
      rewrite (rtb_sext32_small ((buf + c) mod 8)), (rtb_sext32_small sb) in Hc by lia.
      apply Z.ltb_ge in Hc. lia.
  + (* the shadow byte of buf + c is 0 *)
    Time aj_run_to TBL HS HJ2 CC_PC3.
    { c2_awr (Ereg regs2 EX2) Ew23. }
    rename HFr into FR3. clear HF HG.
    lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (KC : forall a, 0 <= a < 2 ^ 64 -> ~ (shadow_addr FA + 4 <= a < shadow_addr FA + 9) ->
    aview rsegs (w_H W1) (ms_mem msx) a = aview rsegs (w_H W1) mem2 a) end.
    { intros a Ha Hw. etransitivity;
      [refine (c2_kept_win _ _ (w_H W1) _ _ _ _ FR3 _ a Ha Hw) | exact (KB a Ha Hw)]. c2_wrtac Eb23. }
    c2_h248 HS (Ereg regs2 EX2) Ew23 0%nat H248.
    c2_at_pc3 HS.
    apply c2_close.
    1: exact HJ2. 1: c2_io. 1: (intros a Ha Hw1 Hw; rewrite (KC a Ha Hw); exact (K2 a Ha Hw1)). 1: exact H248.
    all: (etransitivity; [eapply (c2_reg_kept regs2 EX2 _ _ (w_H W1)); [exact HS | vm_compute; reflexivity] | assumption]).
Qed.

(* ---- n > 0: the reloads, the length test and c = min(len, n - 1), up to the `jal` 0x83abc ---- *)
Lemma c2_arm1 : 1 <= n -> SRr rsegs W1 (cfg_at rsegs CC_PC2 regs1 mem1 md1) GOAL.
Proof using ABCMP H2.
intros Hn1. c2_names.
pose proof c2_base as (HAR1 & HARc & Hfin & BF32 & BF4 & BFc & BFapp & BSH0 & BSHc & BRB32 & BRBlo & BRBhi
& BspA & BspB & Bsp16 & BlycA & BlycB & Bsp47 & Bsp0m).
pose proof (AR_laws_ok rsegs B) as LAWS. pose proof rtsb_segs_low as Hsegs. pose proof rtsb_wx as Hwx.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof c2_tbl_ok as TBL.
assert (Hes : ESTACK = 4096) by reflexivity. unfold T_csv_STK_B in BspA.
destruct Pblk as (m & Hinb & Hmge).
assert (Hm1 : 1 <= m) by (pose proof (Z.le_max_r n 1); lia).
assert (Hrq : req_size m = m) by (unfold req_size; replace (m =? 0) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
assert (Hinb1 : In (buf, m) (ablocks B lyc S1)) by (rewrite Hab; exact Hinb).
destruct (al_blocks _ _ LAWS lyc S1 W1 mem1 md1 buf m HAR1 Hinb1) as (Hb16 & Hb4096 & Hbceil & _ & _ & _ & _).
rewrite Hrq in Hbceil.
clear Pout.
pose proof (RateCsv.csv_list_length mask ltac:(lia)) as HL17.
set (EX := [w64 n; w64 buf]).
assert (Ew32 : ew (Ereg regs1 EX) 32%nat = Z_to_bv 64 n) by reflexivity.
assert (Ew33 : ew (Ereg regs1 EX) 33%nat = Z_to_bv 64 buf) by reflexivity.
assert (Ew28 : ew (Ereg regs1 EX) 28%nat = Z_to_bv 64 LEN)
by (rewrite (ew_Ereg_nat regs1 EX 28%nat (28%bv : bv 5) eq_refl); exact G28).
assert (Ew9 : bv_unsigned (ew (Ereg regs1 EX) 9%nat) = RB)
by (rewrite (ew_Ereg_nat regs1 EX 9%nat (9%bv : bv 5) eq_refl), QQ9; apply unsigned_lit_small; lia).
assert (HSL : rtmb_slots rsegs (w_H W1) mem1 RB [(40, n); (48, LEN); (56, buf)]).
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; cbn [fst snd].
  - replace (n mod 2 ^ 64) with n by (symmetry; apply Z.mod_small; lia).
    apply val_mem_of_rdword. exact H40.
  - replace (LEN mod 2 ^ 64) with LEN by (symmetry; apply Z.mod_small; lia).
    apply val_mem_of_rdword. exact H48.
  - replace (buf mod 2 ^ 64) with buf by (symmetry; apply Z.mod_small; lia).
    apply val_mem_of_rdword. exact H56. }
assert (HS : st_ok rsegs (Ereg regs1 EX) (mkSS CC_PC2 sr_atoms c2_mem_b None c2_facts_b)
(restrict (w_H W1) (mkst regs1 (Z_to_bv 64 CC_PC2) mem1 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute; reflexivity.
  - unfold c2_mem_b, c2_stk_reg. apply Forall_cons; [|apply Forall_nil].
    apply (rtmb_ro_region rsegs (Ereg regs1 EX) (w_H W1) mem1 9%nat RB 40 64); [exact Ew9 | lia | lia |].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    + apply (rtmb_slots_chunk rsegs (Ereg regs1 EX) (w_H W1) mem1 RB _ 40 n (SOff 32 0) HSL);
      [left; reflexivity | apply rtsb_den_atom; [exact Ew32 | lia] | lia].
    + apply (rtmb_slots_chunk rsegs (Ereg regs1 EX) (w_H W1) mem1 RB _ 48 LEN (SOff 28 0) HSL);
      [right; left; reflexivity | apply rtsb_den_atom; [exact Ew28 | lia] | lia].
    + apply (rtmb_slots_chunk rsegs (Ereg regs1 EX) (w_H W1) mem1 RB _ 56 buf (SOff 33 0) HSL);
      [right; right; left; reflexivity | apply rtsb_den_atom; [exact Ew33 | lia] | lia].
  - unfold c2_mem_b. cbv [pairwise_disjoint all_disjoint]. split; exact I.
  - unfold c2_facts_b. split; [|split; exact I].
    cbn [f_atoms atoms_ok]. split; [|split; [|exact I]].
    + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Ew32, (unsigned_lit_small n) by lia.
      change (2 ^ 0) with 1. rewrite Z.mod_1_r. split; [lia|]. split; [reflexivity | lia].
    + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Ew33, (unsigned_lit_small buf) by lia.
      change (2 ^ 4) with 16. split; [lia|]. split; [exact Hb16 | lia]. }
unfold cfg_at. change (w64 CC_PC2) with (Z_to_bv 64 CC_PC2).
Time aj_run_to TBL HS HJ1 0x42200.
{ c2_awr (Ereg regs1 EX) Ew9. }
rename HFr into FR1. clear HF HG.
lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
assert (K0 : forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W1) (ms_mem msx) a = aview rsegs (w_H W1) mem1 a) end.
{ intros a Ha. refine (c2_kept_of_frame _ _ (w_H W1) mem1 _ (fun _ => False) FR1 _ a Ha (fun x => x)). c2_wrtac Ew9. }
srr_branch_with TBL HS.
- (* `bltu s3,a0` taken: len < n - 1, c = len *)
  rewrite branch_ltu_U, (U_atom (Ereg regs1 EX) 28%nat LEN Ew28 ltac:(lia)),
    (U_atom_off (Ereg regs1 EX) 32%nat n (-1) Ew32 ltac:(lia) ltac:(lia)) in Hc.
  apply Z.ltb_lt in Hc.
  Time aj_run_to TBL HS HJ1 0x42200.
  { c2_awr (Ereg regs1 EX) Ew9. }
  rename HFr into FR2. clear HF HG.
  lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
  assert (K1 : forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W1) (ms_mem msx) a = aview rsegs (w_H W1) mem1 a) end.
  { intros a Ha. etransitivity; [refine (c2_kept_of_frame _ _ (w_H W1) _ _ (fun _ => False) FR2 _ a Ha (fun x => x)) | exact (K0 a Ha)].
    c2_wrtac Ew9. }
  c2_at_bcmp HS.
  apply (c2_call LEN _ _ _ Hn1 ltac:(lia) HJ1 ltac:(c2_io) K1).
  + rewrite (c2_reg_sv _ _ _ _ _ (SOff 33 0) HS) by (vm_compute; reflexivity). apply rtsb_den_atom; [exact Ew33 | lia].
  + rewrite (c2_reg_sv _ _ _ _ _ (SOff 24 0) HS) by (vm_compute; reflexivity).
    rewrite (c2_den_reg regs1 EX 24 24%bv eq_refl). exact QQ24.
  + rewrite (c2_reg_sv _ _ _ _ _ (SOff 28 0) HS) by (vm_compute; reflexivity).
    rewrite (c2_den_reg regs1 EX 28 28%bv eq_refl). exact G28.
  + rewrite (c2_reg_sv _ _ _ _ _ (SLit 539328) HS) by (vm_compute; reflexivity). reflexivity.
  + rewrite (c2_reg_sv _ _ _ _ _ (SOff 2 0) HS) by (vm_compute; reflexivity).
    rewrite (c2_den_reg regs1 EX 2 2%bv eq_refl). exact G2.
  + eapply (c2_reg_kept regs1 EX _ _ (w_H W1)); [exact HS | vm_compute; reflexivity].
  + eapply (c2_reg_kept regs1 EX _ _ (w_H W1)); [exact HS | vm_compute; reflexivity].
  + eapply (c2_reg_kept regs1 EX _ _ (w_H W1)); [exact HS | vm_compute; reflexivity].
  + eapply (c2_reg_kept regs1 EX _ _ (w_H W1)); [exact HS | vm_compute; reflexivity].
  + eapply (c2_reg_kept regs1 EX _ _ (w_H W1)); [exact HS | vm_compute; reflexivity].
  + eapply (c2_reg_kept regs1 EX _ _ (w_H W1)); [exact HS | vm_compute; reflexivity].
  + rewrite (c2_reg_sv _ _ _ _ _ (SOff 25 0) HS) by (vm_compute; reflexivity).
    rewrite (c2_den_reg regs1 EX 25 25%bv eq_refl). exact G25.
  + rewrite (c2_reg_sv _ _ _ _ _ (SOff 33 0) HS) by (vm_compute; reflexivity). apply rtsb_den_atom; [exact Ew33 | lia].
  + rewrite (c2_reg_sv _ _ _ _ _ (SOff 28 0) HS) by (vm_compute; reflexivity).
    rewrite (c2_den_reg regs1 EX 28 28%bv eq_refl). exact G28.
- (* `bltu s3,a0` not taken: n - 1 <= len, `mv s3,a0`, c = n - 1 *)
  rewrite branch_ltu_U, (U_atom (Ereg regs1 EX) 28%nat LEN Ew28 ltac:(lia)),
    (U_atom_off (Ereg regs1 EX) 32%nat n (-1) Ew32 ltac:(lia) ltac:(lia)) in Hc.
  apply Z.ltb_ge in Hc.
  Time aj_run_to TBL HS HJ1 0x42200.
  { c2_awr (Ereg regs1 EX) Ew9. }
  rename HFr into FR2. clear HF HG.
  lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
  assert (K1 : forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W1) (ms_mem msx) a = aview rsegs (w_H W1) mem1 a) end.
  { intros a Ha. etransitivity; [refine (c2_kept_of_frame _ _ (w_H W1) _ _ (fun _ => False) FR2 _ a Ha (fun x => x)) | exact (K0 a Ha)].
    c2_wrtac Ew9. }
  c2_at_bcmp HS.
  apply (c2_call (n - 1) _ _ _ Hn1 ltac:(lia) HJ1 ltac:(c2_io) K1).
  + rewrite (c2_reg_sv _ _ _ _ _ (SOff 33 0) HS) by (vm_compute; reflexivity). apply rtsb_den_atom; [exact Ew33 | lia].
  + rewrite (c2_reg_sv _ _ _ _ _ (SOff 24 0) HS) by (vm_compute; reflexivity).
    rewrite (c2_den_reg regs1 EX 24 24%bv eq_refl). exact QQ24.
  + rewrite (c2_reg_sv _ _ _ _ _ (SOff 32 (-1)) HS) by (vm_compute; reflexivity).
    rewrite (c2_den_off _ 32 n (-1) Ew32 ltac:(lia) ltac:(lia)). unfold w64. f_equal; lia.
  + rewrite (c2_reg_sv _ _ _ _ _ (SLit 539328) HS) by (vm_compute; reflexivity). reflexivity.
  + rewrite (c2_reg_sv _ _ _ _ _ (SOff 2 0) HS) by (vm_compute; reflexivity).
    rewrite (c2_den_reg regs1 EX 2 2%bv eq_refl). exact G2.
  + eapply (c2_reg_kept regs1 EX _ _ (w_H W1)); [exact HS | vm_compute; reflexivity].
  + eapply (c2_reg_kept regs1 EX _ _ (w_H W1)); [exact HS | vm_compute; reflexivity].
  + eapply (c2_reg_kept regs1 EX _ _ (w_H W1)); [exact HS | vm_compute; reflexivity].
  + eapply (c2_reg_kept regs1 EX _ _ (w_H W1)); [exact HS | vm_compute; reflexivity].
  + eapply (c2_reg_kept regs1 EX _ _ (w_H W1)); [exact HS | vm_compute; reflexivity].
  + eapply (c2_reg_kept regs1 EX _ _ (w_H W1)); [exact HS | vm_compute; reflexivity].
  + rewrite (c2_reg_sv _ _ _ _ _ (SOff 25 0) HS) by (vm_compute; reflexivity).
    rewrite (c2_den_reg regs1 EX 25 25%bv eq_refl). exact G25.
  + rewrite (c2_reg_sv _ _ _ _ _ (SOff 33 0) HS) by (vm_compute; reflexivity). apply rtsb_den_atom; [exact Ew33 | lia].
  + rewrite (c2_reg_sv _ _ _ _ _ (SOff 32 (-1)) HS) by (vm_compute; reflexivity).
    rewrite (c2_den_off _ 32 n (-1) Ew32 ltac:(lia) ltac:(lia)). unfold w64. f_equal; lia.
Qed.

End arms.

Theorem ccsv_S2 : CC_S2_stmt B MT.
Proof using ABCMP.
unfold CC_S2_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf n mask fpos S1 W1 regs1 mem1 md1 H2.
pose proof H2 as ((_ & _ & _ & Hn & _) & _).
destruct (Z.eq_dec n 0) as [Hn0|Hn0].
- exact (c2_arm0 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf n mask fpos S1 W1 regs1 mem1 md1 H2 Hn0).
- exact (c2_arm1 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf n mask fpos S1 W1 regs1 mem1 md1 H2
    ltac:(lia)).
Qed.

End s2.

About ccsv_S2.
Print Assumptions ccsv_S2.
