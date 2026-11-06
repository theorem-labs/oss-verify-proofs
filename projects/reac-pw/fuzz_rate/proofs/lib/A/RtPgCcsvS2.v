(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/Reusable/YCbq.v at 7379c28ff70f; aj_bcmp_at restated
   as c2_bcmp_at at the bcmp wrapper's image-A entry 0x421a8 with the callee's same_but_materialized kept in its post,
   and the image-A walk of check_csv's tail added. *)
(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; every address is measured on its unstripped twin
   sha256 0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3): segment S2 of the walk of check_csv
   (0x838e0), the tail 0x83ba8 -> 0x83c40. Proves no function (kind: segment lemma): ccsv_S2 is
   RtPgCcsvCut.CC_S2_stmt, which RtPgCcsvCut.cc_chain composes with the other three segment statements.
   c2_bcmp_at restates YCbq.v aj_bcmp_at at the bcmp wrapper's image-A entry 0x421a8 and keeps the callee's
   same_but_materialized in its post (cc_frame's same_io needs it across the call).

   The code (neutral listing of check_csv):
     0x83ba8 ld s3,24(s1)          s3 = buf (the realigned frame's cell R1 + 24)
     0x83bac bne s4,a4             not taken: a4 is pinned to s4's atom |csv_list mask| (the abort arm 0x83d70 is dead)
     0x83bb0 ld a0,16(s1)          a0 = n (cell R1 + 16)
     0x83bb4 beqz a0 -> 0x83c0c    the n = 0 / n > 0 split is made before the run: the cell holds SLit 0 (c2_arm0)
                                   or an atom in [1, 23] (c2_arm1)
   n = 0 (c2_arm0):
     0x83c0c-0x83c18               the instrumented 1-byte load check of buf: its shadow byte is a one-byte region at
                                   an atom declared equal to (s3 >> 3) + s9, holding an atom in [0, 7] (al_shadow by
                                   RtPgMem rtm_blk_ra); `bnez` is split, and on the slow block the atom range [1, 7]
                                   decides `blt` (buf is 16-aligned, so the AND folds to 0)
     0x83c1c lbu a0,0(s3)          buf[0] = 0x5a (the contract's garr8, kept by cc_frame's keep clause on
                                   [buf, buf + max n 1))
     0x83c20-0x83c38               granules 4-8 of the frame's shadow := 0xf8 (want out of scope)
     0x83c3c bne a0,a2             a0 = 90 = a2: not taken; 0x83c40
   n > 0 (c2_arm1, then c2_tail1 after the call):
     0x83bb8 addi a0,a0,-1; 0x83bbc bltu s4,a0 (split: ccsv_c_lt / ccsv_c_ge); 0x83bc0 mv s4,a0 when not taken:
                                   s4 = c = min(len, n - 1)
     0x83bc4 mv a0,s3; 0x83bc8 mv a2,s4; 0x83bcc jal 0x421a8: the bcmp wrapper (abcmp_realizes, c2_bcmp_at) on
                                   (buf, want = F + 32, c); its answer is 0 (RtPgCcsvM ccsv_bcmp_eq_av)
     0x83bd0 bnez a0               not taken (a0 pinned to 0)
     0x83bd4-0x83be4               the instrumented check of buf + c: s3 + s4 and ((s3 + s4) >> 3) + s9 are two
                                   aliases to atoms; `bnez` is split, the slow block's `blt` is split and its error
                                   arm dies by saddr_ok (c2_and7_lt)
     0x83be8 lbu a0,0(a0)          buf[c] = 0 (ccsv_last)
     0x83bec-0x83c00               granules 4-8 := 0xf8; 0x83c04 beqz a0 taken: 0x83c40
   The abort arms 0x83d70 / 0x83d88 and the error paths are not reached. Every state the walk passes keeps the
   journal's state S1 (no allocation), so the cut's state facts carry over; c2_fin rebuilds cc_st3 from what the
   runs and the call wrote (the bcmp wrapper's 2 ESTACK window below R1, granules 4-8 of the frame's shadow).
   Section hypothesis: ABCMP, the bcmp wrapper's contract at its image-A entry 0x421a8. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgSiteA RtPgSteps RtPgMem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgCcsvCut RtPgCcsvM RtPgCcsvKit RtPgCcsvS0.
Require OSSVerify.reac_pw.fuzz_rate.images.Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* image A's loaded segments, as lib/A/RtPgCcsvCut.v names them *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.Asan.M.loaded_segments.

(* ======================================== small facts ======================================== *)
(* the frame's shadow pattern before the tail is bytes *)
Lemma c2_sh_bytes : Forall (fun v => 0 <= v < 256) (CC_SH_A ++ repeat 0 12).
Proof. repeat constructor; lia. Qed.

(* ======================================== the engine states ======================================== *)
(* the instruction table: the tail 0x83ba8 .. 0x83c3c and the two slow blocks 0x83d90 / 0x83d9c *)
Definition c2_tbl : ctable := build_table rsegs 0x83d90 7 (build_table rsegs 0x83ba8 38 TEmpty).
Lemma c2_tbl_ok : table_ok rsegs c2_tbl.
Proof. apply build_table_ok; [lia|]. apply build_table_ok0. lia. Qed.

(* the shadow declaration of the base object held by atom p: ((p >> 3) + s9) is the atom s *)
Definition c2_alias_sh (p s : nat) : sv * sv :=
(SAlu ALU_ADD (SAlu ALU_SRL (SOff p 0) (SLit 3)) (SOff 25 0), SOff s 0).
(* the frame's 32 shadow bytes, with the write window of the five `sb` stores (granules 4-8) *)
Definition c2_fsh_reg : YP09.region := YP09.mkRegion (Some 23%nat) 0 32 4 9 (rtm_fsh_cs (CC_SH_A ++ repeat 0 12)).
(* one byte at the address held by atom b *)
Definition c2_cell (b : nat) (v : sv) : YP09.region := YP09.mkRegion (Some b) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 v)].
(* the realigned frame's cells R1 + 16 (n) and R1 + 24 (buf) *)
Definition c2_stk_reg (en : sv) : YP09.region :=
YP09.mkRegion (Some 9%nat) 16 32 0 0 [YP09.mkChunk 16 (CVal 8 en); YP09.mkChunk 24 (CVal 8 (SOff 33 0))].
(* n = 0: the stack cells, the frame's shadow, buf's shadow byte (atom 34) and buf's byte *)
Definition c2_mem_a (v : sv) : smem := [c2_stk_reg (SLit 0); c2_fsh_reg; c2_cell 34 v; c2_cell 33 (SLit 90)].
Definition c2_facts_a (fs : list (nat * afact)) : facts :=
mkFacts ((33%nat, mkAF 4096 (2 ^ 47) 4) :: fs) [] [c2_alias_sh 33 34].
(* n > 0, before the call: only the stack cells (n in atom 32, buf in atom 33) *)
Definition c2_mem_b : smem := [c2_stk_reg (SOff 32 0)].
Definition c2_facts_b : facts := mkFacts [(32%nat, mkAF 1 23 0); (33%nat, mkAF 4096 (2 ^ 47) 4)] [] [].
(* n > 0, after the call: the frame's shadow, the shadow byte of buf + c (atom 33) and the byte buf[c] (atom 32) *)
Definition c2_mem_c (v : sv) : smem := [c2_fsh_reg; c2_cell 33 v; c2_cell 32 (SLit 0)].
Definition c2_facts_c (fs : list (nat * afact)) : facts :=
mkFacts fs [] [(SAlu ALU_ADD (SOff 19 0) (SOff 20 0), SOff 32 0); c2_alias_sh 32 33].

Section s2. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis ABCMP : abcmp_realizes rsegs B 0x421a8.

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
(* a run keeps every byte outside one window *)
Lemma c2_kept_win : forall E rs H (m m' : word -> option byte) (lo hi : Z),
frame_of E rs (mrestrict H m) (mrestrict H m') ->
(forall a, in_wrange E rs a -> lo <= a < hi) ->
forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview rsegs H m' a = aview rsegs H m a.
Proof.
intros E rs H m m' lo hi HF HP a Ha Hna.
exact (c2_kept_of_frame E rs H m m' (fun x => lo <= x < hi) HF HP a Ha Hna).
Qed.
(* a register outside the clobbered list *)
Lemma c2_notin : forall (r : bv 5) (l : list (bv 5)), existsb (fun c => bv_eqb c r) l = false -> ~ In r l.
Proof.
intros r l. induction l as [|c l IH]; cbn [existsb In]; [tauto|].
intros Hb [Hc|Hin]; apply orb_false_elim in Hb as [H1 H2].
- rewrite Hc, bv_eqb_refl in H1. discriminate H1.
- exact (IH H2 Hin).
Qed.
(* the frame's shadow read back from a region of one-byte literal chunks (S0's ccs_bytes_of_chunks) *)
Lemma c2_fsh_of_region : forall E (H : word -> bool) mem (nn : nat) lo hi wlo whi cs F pat,
region_ok rsegs E (mrestrict H mem) (YP09.mkRegion (Some nn) lo hi wlo whi cs) ->
bv_unsigned (ew E nn) = shadow_addr F ->
Forall (fun v => 0 <= v < 256) pat -> ccs_bytes_chk cs pat = true ->
rt_fsh rsegs H mem F pat.
Proof.
intros E H mem nn lo hi wlo whi cs F pat HR Hew Hfa Hchk.
exact (ccs_bytes_of_chunks E H mem (shadow_addr F) cs pat
  (rts_chunks E (mrestrict H mem) nn (shadow_addr F) cs lo hi wlo whi HR Hew) Hfa Hchk).
Qed.
Lemma c2_fsh_of_reg2 : forall E (H : word -> bool) mem (r : YP09.region) (nn : nat) F pat,
YP09.r_base r = Some nn -> region_ok rsegs E (mrestrict H mem) r ->
bv_unsigned (ew E nn) = shadow_addr F ->
Forall (fun v => 0 <= v < 256) pat -> ccs_bytes_chk (YP09.r_chunks r) pat = true ->
rt_fsh rsegs H mem F pat.
Proof.
intros E H mem r nn F pat Hb HR Hew Hfa Hchk. destruct r as [b lo hi wlo whi cs].
cbn [YP09.r_base YP09.r_chunks] in *. rewrite Hb in HR.
exact (c2_fsh_of_region E H mem nn lo hi wlo whi cs F pat HR Hew Hfa Hchk).
Qed.
Lemma c2_shC_bytes : Forall (fun v => 0 <= v < 256) (CC_SH_C ++ repeat 0 12).
Proof. repeat constructor; lia. Qed.

(* a granule-rounded address and its bounds *)
Lemma c2_round : forall z, z / 8 * 8 <= z < z / 8 * 8 + 8.
Proof.
intros z. pose proof (Z.div_mod z 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound z 8 ltac:(lia)) as R.
remember (z / 8) as q eqn:Hq. clear Hq. lia.
Qed.
Lemma c2_hull_lo : forall q, q mod 4 = 0 -> q <= (q + 4) / 8 * 8.
Proof.
intros q H4. pose proof (c2_round (q + 4)) as [R1 R2].
assert (Hm : ((q + 4) / 8 * 8) mod 8 = 0) by (apply Z_mod_mult).
remember ((q + 4) / 8 * 8) as u eqn:Hu. clear Hu.
apply Z.mod_divide in H4 as [b Hb]; [|lia]. apply Z.mod_divide in Hm as [a Ha]; [|lia].
subst u. subst q. lia.
Qed.
(* want (F + 32, c bytes) lies in the frame's own 32 shadow bytes, hull included *)
Lemma c2_want_hull : forall H mem F pat c,
rt_fsh rsegs H mem F pat -> (length pat = 32)%nat -> F mod 32 = 0 -> 0 < c <= 17 ->
shadow_hull_vis (aview rsegs H mem) (F + 32) c.
Proof.
intros H mem F pat c P Hlen H32 Hc s Hs.
pose proof (rts_fsh_addr F 32 H32 ltac:(lia)) as E1. change (32 / 8) with 4 in E1.
pose proof (rts_fsh_addr F (31 + c) H32 ltac:(lia)) as E2.
replace (F + 32 + c - 1) with (F + (31 + c)) in Hs by lia. rewrite E1, E2 in Hs.
assert (Hj : 3 <= (31 + c) / 8 <= 6)
by (split; [apply Z.div_le_lower_bound | apply Z.div_le_upper_bound]; lia).
assert (Hq4 : shadow_addr F mod 4 = 0).
{ unfold shadow_addr. pose proof H32 as HH. apply Z.mod_divide in HH as [t Ht]; [|lia].
  rewrite Ht. replace (t * 32) with ((t * 4) * 8) by ring. rewrite Z.div_mul by lia.
  unfold SHADOW_OFF. replace (2147450880 + t * 4) with ((536862720 + t) * 4) by ring. apply Z_mod_mult. }
pose proof (c2_hull_lo (shadow_addr F) Hq4) as Hlo.
pose proof (c2_round (shadow_addr F + (31 + c) / 8)) as [Hr1 Hr2].
assert (Hin : 0 <= s - shadow_addr F < Z.of_nat (length pat)) by (rewrite Hlen; lia).
pose proof (P (s - shadow_addr F) Hin) as Pv.
replace (shadow_addr F + (s - shadow_addr F)) with s in Pv by lia. rewrite Pv. discriminate.
Qed.
(* the slow block's `blt (a & 7), s` as plain arithmetic *)
Lemma c2_and7_lt : forall E (q : nat) (x s : Z),
ew E q = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> ew E 34%nat = Z_to_bv 64 s -> 0 <= s < 128 ->
branch_taken BC_LT (sv_denot E (SAlu ALU_AND (SOff q 0) (SLit 7))) (sv_denot E (SOff 34 0))
= (x mod 8 <? s).
Proof.
intros E q x s Hq Hx H34 Hs.
assert (E1 : sv_denot E (SAlu ALU_AND (SOff q 0) (SLit 7)) = Z_to_bv 64 (x mod 8)).
{ cbn [sv_denot]. rewrite Hq, (unsigned_lit_small x) by lia. rewrite Z.add_0_r.
  rewrite <- (Z_to_bv_bv_unsigned 64 (Z_to_bv 64 x)) at 1. rewrite (unsigned_lit_small x) by lia.
  apply YCbn.alu_and7. unfold M64. lia. }
assert (E2 : sv_denot E (SOff 34 0) = Z_to_bv 64 s) by (apply rts_den_atom; [exact H34 | lia]).
rewrite E1, E2. cbv [branch_taken]. apply YCbn.bv_lts_small;
[pose proof (Z.mod_pos_bound x 8 ltac:(lia)); lia | lia].
Qed.

(* a machine register read back from the symbolic state *)
Lemma c2_reg_den : forall E ss ms (H : word -> bool) (r : bv 5) e v,
st_ok rsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = e -> sv_denot E e = v -> getr (ms_regs ms) r = v.
Proof. intros E ss ms H r e v HS He Hv. rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), He. exact Hv. Qed.
(* an atom plus an offset *)
Lemma c2_den_off : forall E n v x w, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> v + x = w -> 0 <= w < 2 ^ 64 ->
sv_denot E (SOff n x) = Z_to_bv 64 w.
Proof.
intros E n v x w H Hv Hw Hw64. subst w. apply bv_eq. rewrite denot_SOff, H. rewrite !unsigned_lit_small by lia.
apply zcanon_id. unfold M64. lia.
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

(* ================================ the bcmp wrapper under the journal ================================ *)
(* YCbq aj_bcmp_at at the image-A entry 0x421a8, also keeping the callee's same_but_materialized *)
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
SRr rsegs W (mkCfg (mkst regsT (Z_to_bv 64 0x421a8) memT (seg_rom rsegs)) mdc)
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
pose proof (AR_laws_ok rsegs B) as LAWS. pose proof rts_segs_low as segs_low.
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

(* ================================ the cut state at 0x83c40 from what the tail wrote ================================ *)
Lemma c2_fin : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (buf n mask : Z)
(fpos : Z) S1 W1 (regs1 : bvmap 5 word) mem1 md1 (regsF : bvmap 5 word) memF mdF,
cc_st2 B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf n mask fpos S1 W1 regs1 mem1 md1 ->
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 ((CC_CID, fpos) :: own) lyc S1 W1 memF mdF k ->
same_io md1 mdF ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (cc_rbase (spZ regs) - 2 * ESTACK <= a < cc_rbase (spZ regs)) ->
 ~ (shadow_addr (frame_addr lyc CC_CID fpos) + 4 <= a < shadow_addr (frame_addr lyc CC_CID fpos) + 9) ->
 aview rsegs (w_H W1) memF a = aview rsegs (w_H W1) mem1 a) ->
rt_fsh rsegs (w_H W1) memF (frame_addr lyc CC_CID fpos) (CC_SH_C ++ repeat 0 12) ->
getr regsF 3 = getr regs1 3 -> getr regsF 4 = getr regs1 4 -> getr regsF 8 = getr regs1 8 ->
getr regsF 18 = getr regs1 18 -> getr regsF 23 = getr regs1 23 -> getr regsF 24 = getr regs1 24 ->
cc_st3 B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf n mask fpos S1 W1 regsF memF mdF.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf n mask fpos S1 W1 regs1 mem1 md1 regsF memF mdF
H2 HJF HioF KEEP FSHF R3 R4 R8 R18 R23 R24.
unfold cc_st3, cc_frame.
destruct H2 as (HP & HFR & HFSH & HWANT & G2 & G9 & G11 & G14 & G20 & G25).
pose proof HP as ((HJc & Hra & Hra4 & Hgp & Htp & Hsp16 & HspT & Hsp0 & Hev) & P10 & P11 & Pn & P12 & P13 & Pm
& Pb0 & Pb63 & Pblk & Pra & Phv & Pam & Pout & Pg0 & Pg1 & Pcid & Pcnt & Ptab).
destruct HFR as (HJ1 & Hfr & Hnin & Hab & Hch & Hsec & Hres & Hnev & Hbb & Hmo & Hio & Hcl & HF4 & HFc & HFapp & HF32
& Hflag & Hsav & H16 & H24 & H48 & R3' & R4' & R8' & R18' & R23' & R24').
set (F := frame_addr lyc CC_CID fpos) in *.
set (R1 := cc_rbase (spZ regs)) in *.
pose proof HJc as (HARc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _ & _).
destruct Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof (cc_rbase_bounds (spZ regs) Hsp16) as [HR32 HRb]. fold R1 in HR32, HRb.
unfold T_csv_STK in HspT. unfold CC_FRAME in HRb.
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
(* every address the walk keeps: in [alloc_ceiling, sp), above R1, or below the frame's shadow / in the frame *)
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
    - unfold T_csv_STK in Hw. lia.
    - intros Hg. exact (Hno (OWN a Hg)). }
  split; [exact HF4|]. split; [exact HFc|]. split; [exact HFapp|]. split; [exact HF32|].
  split; [rewrite <- Hflag; apply rdword_ext; intros j Hj; apply KFR; lia|].
  split.
  { unfold cc_saved in Hsav |- *. intros j Hj. rewrite <- (Hsav j Hj). apply rdword_ext. intros i Hi. apply KST. lia. }
  split; [rewrite <- H16; apply rdword_ext; intros j Hj; apply KST; lia|].
  split; [rewrite <- H24; apply rdword_ext; intros j Hj; apply KST; lia|].
  split; [rewrite <- H48; apply rdword_ext; intros j Hj; apply KST; lia|].
  rewrite R3, R4, R8, R18, R23, R24. repeat (split; [assumption|]). assumption. }
split; [exact FSHF|].
{ unfold mbytes_at in HWANT |- *. intros j Hj. rewrite <- (HWANT j Hj). apply c2_mbyte_of_aview.
  pose proof (RateCsv.csv_list_length mask ltac:(lia)) as HL17.
  rewrite RateCsv.csv_bytes_length in Hj. apply KFR. lia. }
Qed.

(* ======================================== the two arms ======================================== *)
Section arms.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
(W : world rsegs) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word)
(buf n mask fpos : Z) (S1 : astate) (W1 : world rsegs) (regs1 : bvmap 5 word)
(mem1 : word -> option byte) (md1 : Model).
Hypothesis H2 : cc_st2 B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf n mask fpos S1 W1 regs1 mem1 md1.

Local Abbreviation FA := (frame_addr lyc CC_CID fpos).
Local Abbreviation RB := (cc_rbase (spZ regs)).
Local Abbreviation GOAL := (fun W2 c2 => exists S2 regs2 mem2 md2, c2 = cfg_at rsegs CC_PC3 regs2 mem2 md2 /\
cc_st3 B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf n mask fpos S2 W2 regs2 mem2 md2).

Ltac c2_names :=
pose proof H2 as (HP & HFR & HFSH & HWANT & G2 & G9 & G11 & G14 & G20 & G25);
pose proof HP as (HCPRE & P10 & P11 & Pn & P12 & P13 & Pmk & Pb0 & Pb63 & Pblk & Pra & Phv & Pam & Pout & Pg0 & Pg1 & Pcid & Pcnt & Ptab);
pose proof HCPRE as (HJc & Hrok & Hra4 & Hgp & Htp & Hsp16 & HspT & Hsp0 & Hev);
pose proof HFR as (HJ1 & Hfr & Hnin & Hab & Hch & Hsec & Hres & Hnev & Hbb & Hmo & Hio & Hcl & HF4 & HFc & HFapp & HF32 & Hflag & Hsav & H16 & H24 & H48 & QQ3 & QQ4 & QQ8 & QQ18 & QQ23 & QQ24).

(* the geometry of the frame, of the realigned base and of the stack, from the cut's journal *)
Lemma c2_base :
AR rsegs B lyc S1 W1 mem1 md1 /\ AR rsegs B lyc Sc W memc mdc /\ In (CC_CID, fpos) (frames S1) /\
FA mod 32 = 0 /\ 4096 <= FA /\ FA + 256 <= alloc_ceiling /\ in_app FA 256 /\
0 <= shadow_addr FA /\ shadow_addr FA + 32 <= alloc_ceiling /\
RB mod 32 = 0 /\ spZ regs - 176 <= RB /\ RB <= spZ regs - 160 /\
sp0 - STK + T_csv_STK <= spZ regs /\ spZ regs <= sp0 /\ spZ regs mod 16 = 0 /\
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

(* the write window of a run of the tail: granules 4-8 of the frame's shadow *)
Ltac c2_wrtac Ew :=
intros aa HH; destruct HH as (rr & Hin & Hr);
cbn [In ss_mem c2_mem_a c2_mem_b c2_mem_c c2_stk_reg c2_fsh_reg c2_cell] in Hin;
repeat (destruct Hin as [<-|Hin]); try (destruct Hin);
cbn [YP09.r_base YP09.r_wlo YP09.r_whi c2_stk_reg c2_fsh_reg c2_cell] in Hr;
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
(* shadow_addr and the engine's shadow_of_addr are the same map *)
Lemma c2_sh_eq : forall x, shadow_addr x = shadow_of_addr SHADOW_OFF x.
Proof. intros x. reflexivity. Qed.
(* a shadow byte lies in the band, apart from every application range *)
Lemma c2_band : forall x, 0 <= x < 2 ^ 47 -> kLowMemEnd <= shadow_addr x < kHighMemBeg.
Proof. intros x Hx. rewrite c2_sh_eq. apply rtm_shadow_band. unfold kHighMemEnd. lia. Qed.
(* a granule index outside the frame's 32 granules *)
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
(* a point outside a range is on one of its two sides *)
Lemma c2_out_disj : forall a lo hi, ~ (lo <= a < hi) -> a < lo \/ hi <= a.
Proof.
intros a lo hi H. destruct (Z_lt_le_dec a lo) as [X|X]; [left; exact X | right].
destruct (Z_lt_le_dec a hi) as [Y|Y]; [exfalso; apply H; lia | exact Y].
Qed.

(* the state at 0x83c40 from an arbitrary final state, as arm0's CLOSE but usable by both arms *)
Lemma c2_close : forall (regsF : bvmap 5 word) memF mdF,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 ((CC_CID, fpos) :: own) lyc S1 W1 memF mdF k ->
same_io md1 mdF ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (RB - 2 * ESTACK <= a < RB) ->
 ~ (shadow_addr FA + 4 <= a < shadow_addr FA + 9) -> aview rsegs (w_H W1) memF a = aview rsegs (w_H W1) mem1 a) ->
rt_fsh rsegs (w_H W1) memF FA (CC_SH_C ++ repeat 0 12) ->
getr regsF 3 = getr regs1 3 -> getr regsF 4 = getr regs1 4 -> getr regsF 8 = getr regs1 8 ->
getr regsF 18 = getr regs1 18 -> getr regsF 23 = getr regs1 23 -> getr regsF 24 = getr regs1 24 ->
SRr rsegs W1 (mkCfg (mkst regsF (Z_to_bv 64 CC_PC3) memF (seg_rom rsegs)) mdF) GOAL.
Proof.
intros regsF memF mdF HJF HioF KEEP FSHF Q3 Q4 Q8 Q18 Q23 Q24.
apply SRr_ret. exists S1, regsF, memF, mdF. split; [reflexivity|].
eapply c2_fin; [exact H2 | exact HJF | exact HioF | exact KEEP | exact FSHF
| exact Q3 | exact Q4 | exact Q8 | exact Q18 | exact Q23 | exact Q24].
Qed.

(* the close of a leaf of the n > 0 arm: the frame's shadow from the region the run leaves, then c2_close.
   Kname keeps the bytes of the runs after the call, K2 those of the call, KT those of the runs before it. *)
Ltac c2_finish Kname K2 KT Ev Ew :=
lazymatch goal with
| HSx : st_ok _ _ ?ssf (restrict (w_H ?Wx) ?msx) |- _ =>
  let rr := eval vm_compute in (nth 0 (ss_mem ssf) (YP09.mkRegion None 0 0 0 0 [])) in
  let HRg := fresh "HRg" in let HSHC := fresh "HSHC" in let Ems := fresh "Ems" in
  pose proof (rts_region_nth Ev ssf msx 0%nat rr (w_H Wx) HSx eq_refl) as HRg;
  assert (HSHC : rt_fsh rsegs (w_H Wx) (ms_mem msx) FA (CC_SH_C ++ repeat 0 12))
    by (exact (c2_fsh_of_reg2 Ev (w_H Wx) (ms_mem msx) rr 23%nat FA
        (CC_SH_C ++ repeat 0 12) ltac:(vm_compute; reflexivity) HRg Ew c2_shC_bytes
        ltac:(vm_compute; reflexivity)));
  pose proof (st_ok_restrict_mkst rsegs (w_H Wx) Ev ssf msx HSx eq_refl) as Ems;
  rewrite Ems at 1;
  apply c2_close;
  [ assumption
  | eapply same_io_trans; [eassumption|];
    eapply same_io_trans; [apply same_io_materialized; eassumption|];
    first [apply same_io_refl | apply same_io_wvb]
  | let a := fresh "a" in let Ha := fresh "Ha" in let Hw := fresh "Hw" in let Hg := fresh "Hg" in
    intros a Ha Hw Hg; etransitivity; [exact (Kname a Ha Hg)|];
    etransitivity; [exact (K2 a Ha Hw) | exact (KT a Ha)]
  | exact HSHC
  | .. ];
  (eapply eq_trans;
   [ eapply (regs_kept_of_st_ok rsegs Ev _ _ _ _ (w_H Wx) [1; 10; 11; 12]%bv HSx);
     [apply env_agree_refl | vm_compute; reflexivity | vm_compute; discriminate
      | apply c2_notin; vm_compute; reflexivity]
   | assumption ])
end.

(* ---- n = 0: the instrumented check of buf, the compare with 0x5a, granules 4-8 out of scope ---- *)
Lemma c2_arm0 : n = 0 -> SRr rsegs W1 (cfg_at rsegs CC_PC2 regs1 mem1 md1) GOAL.
Proof.
intros Hn0. c2_names.
pose proof c2_base as (HAR1 & HARc & Hfin & BF32 & BF4 & BFc & BFapp & BSH0 & BSHc & BRB32 & BRBlo & BRBhi
& BspA & BspB & Bsp16 & BlycA & BlycB & Bsp47 & Bsp0m).
pose proof (AR_laws_ok rsegs B) as LAWS. pose proof rts_segs_low as Hsegs. pose proof rts_wx as Hwx.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof c2_tbl_ok as TBL.
assert (Hes : ESTACK = 4096) by reflexivity. unfold T_csv_STK in BspA.
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
pose proof (c2_band buf ltac:(lia)) as Hband.
(* buf's byte and its shadow byte at the cut's memory *)
assert (Hkeep1 : forall i, 0 <= i < 1 -> aview rsegs (w_H W1) mem1 (buf + i) = aview rsegs (w_H W) memc (buf + i)).
{ intros i Hi. apply Hcl; [lia | |].
  - rewrite Hn0 in Pout. rewrite Z.max_r in Pout by lia. unfold T_csv_STK in Pout. lia.
  - intros Ho. exact (proj2 (Hbpresc (buf + i) ltac:(lia)) Ho). }
assert (Hg0 : garr8 rsegs (mrestrict (w_H W1) mem1) buf [0x5a]).
{ apply (c2_garr8_kept (w_H W) memc (w_H W1) mem1 buf [0x5a] (Pg0 Hn0)).
  intros i Hi. cbn [length] in Hi. apply Hkeep1. lia. }
assert (Hbv : aview rsegs (w_H W1) mem1 buf = Some 90) by (apply ccsv_buf0; exact Hg0).
destruct (rtm_blk_ra rsegs B lyc S1 W1 mem1 md1 buf m buf 1 HAR1 Hinb1 ltac:(lia) ltac:(lia)) as (Hra1 & _).
assert (HRC : exists sb, aview rsegs (w_H W1) mem1 (shadow_of_addr SHADOW_OFF buf) = Some sb /\ saddr_ok buf sb)
by (eapply rtm_ra_cell; exact Hra1).
destruct HRC as (sb & Hsb & Hsok). pose proof (rtm_sok_range buf sb Hb8 Hsok) as Hsb7.
rewrite <- c2_sh_eq in Hsb.
(* the symbolic state at 0x83ba8 *)
set (EX := [w64 0; w64 buf; w64 (shadow_addr buf); w64 sb]).
assert (Ew33 : ew (Ereg regs1 EX) 33%nat = Z_to_bv 64 buf) by reflexivity.
assert (Ew34 : ew (Ereg regs1 EX) 34%nat = Z_to_bv 64 (shadow_addr buf)) by reflexivity.
assert (Ew35 : ew (Ereg regs1 EX) 35%nat = Z_to_bv 64 sb) by reflexivity.
assert (Ew25 : ew (Ereg regs1 EX) 25%nat = Z_to_bv 64 SHADOW_OFF)
by (rewrite (ew_Ereg_nat regs1 EX 25%nat (25%bv : bv 5) eq_refl); exact G25).
assert (Ew9 : bv_unsigned (ew (Ereg regs1 EX) 9%nat) = RB)
by (rewrite (ew_Ereg_nat regs1 EX 9%nat (9%bv : bv 5) eq_refl), G9; apply unsigned_lit_small; lia).
assert (Ew23 : bv_unsigned (ew (Ereg regs1 EX) 23%nat) = shadow_addr FA)
by (rewrite (ew_Ereg_nat regs1 EX 23%nat (23%bv : bv 5) eq_refl), QQ23; apply unsigned_lit_small; lia).
assert (Eb23 : base_val (Ereg regs1 EX) (Some 23%nat) = shadow_addr FA) by exact Ew23.
assert (Ew20 : ew (Ereg regs1 EX) 20%nat = w64 (Z.of_nat (length (RateCsv.csv_list mask))))
by (rewrite (ew_Ereg_nat regs1 EX 20%nat (20%bv : bv 5) eq_refl); exact G20).
assert (Vw33 : bv_unsigned (ew (Ereg regs1 EX) 33%nat) = buf) by (rewrite Ew33; apply unsigned_lit_small; lia).
assert (Vw34 : bv_unsigned (ew (Ereg regs1 EX) 34%nat) = shadow_addr buf) by (rewrite Ew34; apply unsigned_lit_small; lia).
assert (HFAband : kLowMemEnd <= shadow_addr FA < kHighMemBeg) by (apply c2_band; lia).
assert (Dsf : RB + 32 <= shadow_addr FA + 0 \/ shadow_addr FA + 32 <= RB + 16) by (right; lia).
assert (Dsb : RB + 32 <= shadow_addr buf + 0 \/ shadow_addr buf + 1 <= RB + 16) by (right; lia).
assert (Dsc : RB + 32 <= buf + 0 \/ buf + 1 <= RB + 16) by (right; lia).
assert (Dfb : shadow_addr FA + 32 <= shadow_addr buf + 0 \/ shadow_addr buf + 1 <= shadow_addr FA + 0).
{ pose proof (c2_div_out buf FA HF8 ltac:(lia) ltac:(lia) Hsep) as X.
  unfold shadow_addr. destruct X as [X|X]; [right; lia | left; lia]. }
assert (Dfc : shadow_addr FA + 32 <= buf + 0 \/ buf + 1 <= shadow_addr FA + 0).
{ pose proof (app_vs_shadow buf m FA 256 buf Hbapp BFapp ltac:(lia) ltac:(lia)) as Y.
  change (256 / 8) with 32 in Y.
  destruct (c2_out_disj buf (shadow_addr FA) (shadow_addr FA + 32) Y) as [Z1|Z1]; [right; lia | left; lia]. }
assert (Dbc : shadow_addr buf + 1 <= buf + 0 \/ buf + 1 <= shadow_addr buf + 0).
{ unfold in_app in Hbapp. destruct Hbapp as (_ & [Hlow | [Hhigh _]]); [right | left];
  unfold kLowShadowBeg, kLowMemEnd, kHighMemBeg in *; lia. }
assert (HSL : rtm_slots rsegs (w_H W1) mem1 RB [(16, n); (24, buf)]).
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd].
  - replace (n mod 2 ^ 64) with n by (symmetry; apply Z.mod_small; lia).
    apply val_mem_of_rdword. exact H16.
  - replace (buf mod 2 ^ 64) with buf by (symmetry; apply Z.mod_small; lia).
    apply val_mem_of_rdword. exact H24. }
assert (HS : st_ok rsegs (Ereg regs1 EX) (mkSS CC_PC2 sr_atoms (c2_mem_a (SOff 35 0)) None (c2_facts_a [(35%nat, mkAF 0 7 0)]))
(restrict (w_H W1) (mkst regs1 (Z_to_bv 64 CC_PC2) mem1 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute; reflexivity.
  - unfold c2_mem_a, c2_stk_reg, c2_fsh_reg, c2_cell.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
    + apply (rtm_ro_region rsegs (Ereg regs1 EX) (w_H W1) mem1 9%nat RB 16 32); [exact Ew9 | lia | lia |].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (rtm_slots_chunk rsegs (Ereg regs1 EX) (w_H W1) mem1 RB [(16, n); (24, buf)] 16 n (SLit 0) HSL);
        [left; reflexivity | rewrite Hn0; reflexivity | lia].
      * apply (rtm_slots_chunk rsegs (Ereg regs1 EX) (w_H W1) mem1 RB [(16, n); (24, buf)] 24 buf (SOff 33 0) HSL);
        [right; left; reflexivity | apply rts_den_atom; [exact Ew33 | lia] | lia].
    + apply (rtm_rw_region rsegs (Ereg regs1 EX) (w_H W1) mem1 23%nat (shadow_addr FA) 0 32 4 9);
      [exact Ew23 | lia | lia | | ].
      * intros o Ho. exact (proj1 (Hfspres o ltac:(lia))).
      * apply (rtm_fsh_chunks rsegs (Ereg regs1 EX) (w_H W1) mem1 FA (CC_SH_A ++ repeat 0 12) HFSH c2_sh_bytes).
    + apply (rtm_cell_region rsegs (Ereg regs1 EX) (w_H W1) mem1 34%nat (shadow_addr buf) sb (SOff 35 0));
      [exact Vw34 | exact Hsb | apply rts_den_atom; [exact Ew35 | lia] | lia | lia].
    + apply (rtm_cell_region rsegs (Ereg regs1 EX) (w_H W1) mem1 33%nat buf 90 (SLit 90));
      [exact Vw33 | exact Hbv | reflexivity | lia | lia].
  - unfold c2_mem_a, c2_stk_reg, c2_fsh_reg, c2_cell.
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
(* a4 is s4's atom, so `bne s4,a4` is decided *)
pose proof (RateCsv.csv_list_length mask ltac:(lia)) as HL17.
assert (Hpin : sv_denot (Ereg regs1 EX) (SOff 20 0) = getr regs1 14).
{ rewrite G14. apply rts_den_atom; [exact Ew20 | lia]. }
pose proof (st_ok_pin_sv rsegs (Ereg regs1 EX) _ _ (14%bv : bv 5) (SOff 20 0) HS eq_refl Hpin) as HSp.
clear HS. rename HSp into HS.
(* the state at 0x83c40, from the journal and what the run wrote *)
assert (CLOSE : forall (regsF : bvmap 5 word) memF mdF,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 ((CC_CID, fpos) :: own) lyc S1 W1 memF mdF k ->
same_io md1 mdF ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (RB - 2 * ESTACK <= a < RB) ->
 ~ (shadow_addr FA + 4 <= a < shadow_addr FA + 9) -> aview rsegs (w_H W1) memF a = aview rsegs (w_H W1) mem1 a) ->
rt_fsh rsegs (w_H W1) memF FA (CC_SH_C ++ repeat 0 12) ->
getr regsF 3 = getr regs1 3 -> getr regsF 4 = getr regs1 4 -> getr regsF 8 = getr regs1 8 ->
getr regsF 18 = getr regs1 18 -> getr regsF 23 = getr regs1 23 -> getr regsF 24 = getr regs1 24 ->
SRr rsegs W1 (mkCfg (mkst regsF (Z_to_bv 64 CC_PC3) memF (seg_rom rsegs)) mdF) GOAL).
{ intros regsF memF mdF HJF HioF KEEP FSHF Q3 Q4 Q8 Q18 Q23 Q24.
  apply SRr_ret. exists S1, regsF, memF, mdF. split; [reflexivity|].
  eapply c2_fin; [exact H2 | exact HJF | exact HioF | exact KEEP | exact FSHF
  | exact Q3 | exact Q4 | exact Q8 | exact Q18 | exact Q23 | exact Q24]. }
unfold cfg_at. change (w64 CC_PC2) with (Z_to_bv 64 CC_PC2).
aj_run_to TBL HS HJ1 CC_PC3.
{ c2_awr (Ereg regs1 EX) Ew23. }
rename HFr into FR1. clear HF HG.
lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (shadow_addr FA + 4 <= a < shadow_addr FA + 9) ->
aview rsegs (w_H W1) (ms_mem msx) a = aview rsegs (w_H W1) mem1 a) end.
{ intros a Ha Hw. refine (c2_kept_win _ _ (w_H W1) mem1 _ _ _ FR1 _ a Ha Hw).
  c2_wrtac Eb23. }
srr_branch_with TBL HS.
- (* the shadow byte is not 0: its range makes the slow block's compare pass *)
  assert (Hsb1 : 1 <= sb <= 7).
  { rewrite branch_ne_U in Hc. rewrite (U_atom (Ereg regs1 EX) 35%nat sb Ew35 ltac:(lia)), U_SLit in Hc.
    change (zcanon 0) with 0 in Hc. apply negb_true_iff, Z.eqb_neq in Hc. lia. }
  pose proof (st_ok_add_fact rsegs (Ereg regs1 EX) _ _ 35%nat (mkAF 1 7 0) HS
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Ew35, (unsigned_lit_small sb) by lia;
        change (2 ^ 0) with 1; rewrite Z.mod_1_r; split; [lia|]; split; [reflexivity | lia])) as HS2.
  clear HS. rename HS2 into HS.
  aj_run_to TBL HS HJ1 CC_PC3.
  { c2_awr (Ereg regs1 EX) Ew23. }
  rename HFr into FR2. clear HF HG.
  lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
  assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (shadow_addr FA + 4 <= a < shadow_addr FA + 9) ->
  aview rsegs (w_H W1) (ms_mem msx) a = aview rsegs (w_H W1) mem1 a) end.
  { intros a Ha Hw. etransitivity;
    [refine (c2_kept_win _ _ (w_H W1) _ _ _ _ FR2 _ a Ha Hw) | exact (KA a Ha Hw)]. c2_wrtac Eb23. }
  lazymatch type of HS with
  | st_ok _ _ ?ssf (restrict (w_H ?Wx) ?msx) =>
    let rr := eval vm_compute in (nth 1 (ss_mem ssf) (YP09.mkRegion None 0 0 0 0 [])) in
    pose proof (rts_region_nth (Ereg regs1 EX) ssf msx 1%nat rr (w_H Wx) HS eq_refl) as HRg;
    assert (HSHC : rt_fsh rsegs (w_H Wx) (ms_mem msx) FA (CC_SH_C ++ repeat 0 12))
      by (exact (c2_fsh_of_reg2 (Ereg regs1 EX) (w_H Wx) (ms_mem msx) rr 23%nat FA
          (CC_SH_C ++ repeat 0 12) ltac:(vm_compute; reflexivity) HRg Ew23 c2_shC_bytes
          ltac:(vm_compute; reflexivity)))
  end.
  pose proof (st_ok_restrict_mkst rsegs (w_H W1) (Ereg regs1 EX) _ _ HS eq_refl) as Ems. rewrite Ems at 1.
  apply CLOSE;
  [ exact HJ1
  | let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio
  | intros a Ha _ Hw; exact (KB a Ha Hw)
  | exact HSHC
  | .. ];
  (eapply (regs_kept_of_st_ok rsegs (Ereg regs1 EX) _ _ regs1 EX (w_H W1) [10; 11; 12; 14; 19]%bv HS);
   [apply env_agree_refl | vm_compute; reflexivity | vm_compute; discriminate
    | apply c2_notin; vm_compute; reflexivity]).
- (* the shadow byte is 0: the check passes at once *)
  aj_run_to TBL HS HJ1 CC_PC3.
  { c2_awr (Ereg regs1 EX) Ew23. }
  rename HFr into FR2. clear HF HG.
  lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
  assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (shadow_addr FA + 4 <= a < shadow_addr FA + 9) ->
  aview rsegs (w_H W1) (ms_mem msx) a = aview rsegs (w_H W1) mem1 a) end.
  { intros a Ha Hw. etransitivity;
    [refine (c2_kept_win _ _ (w_H W1) _ _ _ _ FR2 _ a Ha Hw) | exact (KA a Ha Hw)]. c2_wrtac Eb23. }
  lazymatch type of HS with
  | st_ok _ _ ?ssf (restrict (w_H ?Wx) ?msx) =>
    let rr := eval vm_compute in (nth 1 (ss_mem ssf) (YP09.mkRegion None 0 0 0 0 [])) in
    pose proof (rts_region_nth (Ereg regs1 EX) ssf msx 1%nat rr (w_H Wx) HS eq_refl) as HRg;
    assert (HSHC : rt_fsh rsegs (w_H Wx) (ms_mem msx) FA (CC_SH_C ++ repeat 0 12))
      by (exact (c2_fsh_of_reg2 (Ereg regs1 EX) (w_H Wx) (ms_mem msx) rr 23%nat FA
          (CC_SH_C ++ repeat 0 12) ltac:(vm_compute; reflexivity) HRg Ew23 c2_shC_bytes
          ltac:(vm_compute; reflexivity)))
  end.
  pose proof (st_ok_restrict_mkst rsegs (w_H W1) (Ereg regs1 EX) _ _ HS eq_refl) as Ems. rewrite Ems at 1.
  apply CLOSE;
  [ exact HJ1
  | let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio
  | intros a Ha _ Hw; exact (KB a Ha Hw)
  | exact HSHC
  | .. ];
  (eapply (regs_kept_of_st_ok rsegs (Ereg regs1 EX) _ _ regs1 EX (w_H W1) [10; 11; 12; 14; 19]%bv HS);
   [apply env_agree_refl | vm_compute; reflexivity | vm_compute; discriminate
    | apply c2_notin; vm_compute; reflexivity]).
Qed.

(* ---- n > 0: c = min(len, n - 1), the bcmp wrapper at 0x421a8, the last byte, granules 4-8 out of scope ---- *)
(* the call at 0x421a8 and the tail after it, shared by the two arms of `bltu s4,a0` *)
Lemma c2_tail1 : forall (c : Z) (regsT : bvmap 5 word) memT mdT,
0 < n -> c = Z.of_nat (length (RateCsv.csv_cut (RateCsv.csv_list mask) n)) ->
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 ((CC_CID, fpos) :: own) lyc S1 W1 memT mdT k ->
same_io md1 mdT ->
(forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W1) memT a = aview rsegs (w_H W1) mem1 a) ->
getr regsT 1 = w64 539600 -> getr regsT 2 = w64 RB ->
getr regsT 3 = getr regs1 3 -> getr regsT 4 = getr regs1 4 -> getr regsT 8 = getr regs1 8 ->
getr regsT 10 = w64 buf -> getr regsT 11 = w64 (FA + 32) -> getr regsT 12 = w64 c ->
getr regsT 18 = getr regs1 18 -> getr regsT 19 = w64 buf -> getr regsT 20 = w64 c ->
getr regsT 23 = getr regs1 23 -> getr regsT 24 = getr regs1 24 -> getr regsT 25 = w64 SHADOW_OFF ->
SRr rsegs W1 (mkCfg (mkst regsT (Z_to_bv 64 270760) memT (seg_rom rsegs)) mdT) GOAL.
Proof.
intros c regsT memT mdT Hnpos Hceq HJT HioT KEEPT R1v R2v R3v R4v R8v R10v R11v R12v R18v R19v R20v R23v R24v R25v.
c2_names.
pose proof c2_base as (HAR1 & HARc & Hfin & BF32 & BF4 & BFc & BFapp & BSH0 & BSHc & BRB32 & BRBlo & BRBhi
& BspA & BspB & Bsp16 & BlycA & BlycB & Bsp47 & Bsp0m).
pose proof (AR_laws_ok rsegs B) as LAWS. pose proof rts_segs_low as Hsegs. pose proof rts_wx as Hwx.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof c2_tbl_ok as TBL.
assert (Hes : ESTACK = 4096) by reflexivity. unfold T_csv_STK in BspA.
destruct Pblk as (m & Hinb & Hmge).
assert (Hmn : n <= m) by (pose proof (Z.le_max_l n 1); lia).
assert (Hrq : req_size m = m) by (unfold req_size; replace (m =? 0) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
assert (Hinb1 : In (buf, m) (ablocks B lyc S1)) by (rewrite Hab; exact Hinb).
pose proof (proj1 HJT) as HART.
destruct (al_blocks _ _ LAWS lyc S1 W1 memT mdT buf m HART Hinb1) as (Hb16 & Hb4096 & Hbceil & Hbapp & HbpresT & _ & _).
rewrite Hrq in Hbceil, Hbapp, HbpresT.
destruct (al_frames _ _ LAWS lyc S1 W1 memT mdT CC_CID fpos HART Hfin) as (_ & _ & HfpresT & HfspresT).
change (fs_frame_bytes CC_CID / 8) with 32 in HfspresT. change (fs_frame_bytes CC_CID) with 256 in HfpresT.
pose proof (ccsv_c_bound mask n ltac:(lia) ltac:(lia)) as (Hc17 & Hcn). rewrite <- Hceq in Hc17, Hcn.
pose proof (RateCsv.csv_list_length mask ltac:(lia)) as HL17.
assert (HRB64 : 0 <= RB < 2 ^ 64) by lia.
assert (HspR : spZ regsT = RB).
{ unfold spZ. rewrite R2v. apply unsigned_lit_small. exact HRB64. }
assert (Hb8 : buf mod 8 = 0).
{ pose proof Hb16 as HH. apply Z.mod_divide in HH as [q Hq]; [|lia].
  rewrite Hq. replace (q * 16) with ((2 * q) * 8) by ring. apply Z_mod_mult. }
assert (HF8 : FA mod 8 = 0).
{ pose proof BF32 as HH. apply Z.mod_divide in HH as [q Hq]; [|lia].
  rewrite Hq. replace (q * 32) with ((4 * q) * 8) by ring. apply Z_mod_mult. }
assert (Hd : zdisjoint (buf, req_size m) (FA, fs_frame_bytes CC_CID)).
{ eapply sep_block_frame with (S := S1) (W := W1) (mem := memT) (md := mdT); try eassumption. }
unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Hrq in Hd. change (fs_frame_bytes CC_CID) with 256 in Hd.
(* the frame's shadow and buf's bytes at the call's memory *)
assert (HFSHT : rt_fsh rsegs (w_H W1) memT FA (CC_SH_A ++ repeat 0 12)).
{ apply (rtm_fsh_kept rsegs (w_H W1) mem1 (w_H W1) memT FA _ HFSH).
  intros i Hi. change (Z.of_nat (length (CC_SH_A ++ repeat 0 12))) with 32 in Hi.
  apply KEEPT. lia. }
assert (Hkeep1 : forall i, 0 <= i < n -> aview rsegs (w_H W1) memT (buf + i) = aview rsegs (w_H W) memc (buf + i)).
{ intros i Hi. rewrite KEEPT by lia. apply Hcl; [lia | |].
  - rewrite Z.max_l in Pout by lia. unfold T_csv_STK in Pout. lia.
  - destruct (al_blocks _ _ LAWS lyc Sc W memc mdc buf m HARc Hinb) as (_ & _ & _ & _ & Hbpresc & _ & _).
    rewrite Hrq in Hbpresc. intros Ho. exact (proj2 (Hbpresc (buf + i) ltac:(lia)) Ho). }
assert (Hg1 : garr8 rsegs (mrestrict (w_H W1) memT) buf (RateCsv.csv_cut (RateCsv.csv_list mask) n ++ [0])).
{ apply (c2_garr8_kept (w_H W) memc (w_H W1) memT buf _ (Pg1 Hnpos)).
  intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. apply Hkeep1. lia. }
(* the bytes of want at the call's memory *)
assert (HWT : forall i, 0 <= i < Z.of_nat (length (RateCsv.csv_list mask)) ->
  aview rsegs (w_H W1) memT (FA + 32 + i) = Some (nth (Z.to_nat i) (RateCsv.csv_list mask) 0)).
{ intros i Hi.
  pose proof (HWANT (Z.to_nat i) ltac:(rewrite RateCsv.csv_bytes_length; lia)) as HM.
  rewrite Z2Nat.id in HM by lia.
  assert (Hne : nth_error (RateCsv.csv_bytes (RateCsv.csv_list mask)) (Z.to_nat i)
    = Some (Z_to_bv 8 (nth (Z.to_nat i) (RateCsv.csv_list mask) 0))).
  { unfold RateCsv.csv_bytes. apply map_nth_error. apply nth_error_nth'. lia. }
  rewrite Hne in HM. rewrite KEEPT by lia. unfold aview. rewrite HM. cbn [option_map]. f_equal.
  rewrite rtm_unsigned_byte. apply Z.mod_small.
  assert (Hlen2 : (Z.to_nat i < length (RateCsv.csv_list mask))%nat) by lia.
  assert (Hm0 : 0 <= mask) by lia.
  pose proof (proj1 (Forall_nth _ _) (RateCsv.csv_list_chars mask Hm0) (Z.to_nat i) 0 Hlen2) as Hchw. cbv beta in Hchw. lia. }
(* the bcmp wrapper's premises *)
assert (Pc32 : 0 <= c < 2 ^ 32) by lia.
assert (Psx : src_ok rsegs W1 regsT memT buf c).
{ intros a Ha. split.
  - apply (aview_some_of_apresent rsegs). exact (proj1 (HbpresT a ltac:(lia))).
  - rewrite HspR. lia. }
assert (Psy : src_ok rsegs W1 regsT memT (FA + 32) c).
{ intros a Ha. split.
  - apply (aview_some_of_apresent rsegs). apply HfpresT. lia.
  - rewrite HspR. lia. }
assert (Pbx : forall a, buf <= a < buf + c -> ~ (sp0 + (RB - sp0) - 2 * ESTACK <= a < sp0 + (RB - sp0))) by lia.
assert (Pby : forall a, FA + 32 <= a < FA + 32 + c -> ~ (sp0 + (RB - sp0) - 2 * ESTACK <= a < sp0 + (RB - sp0))) by lia.
assert (Pmx : amem_range buf c).
{ eapply (amem_range_of_block rsegs B LAWS lyc S1 W1 memT mdT buf m buf c HART Hinb1); lia. }
assert (Pmy : amem_range (FA + 32) c).
{ pose proof (rck_fbounds CC_CID FA ltac:(unfold CC_CID; lia) BF32
    ltac:(change (fs_frame_bytes CC_CID) with 256; exact BFapp)) as (_ & _ & _ & _ & _ & Hmr).
  change (fs_frame_bytes CC_CID) with 256 in Hmr. apply Hmr; lia. }
destruct (rtm_blk_ra rsegs B lyc S1 W1 memT mdT buf m buf c HART Hinb1 ltac:(lia) ltac:(lia)) as (Prx & Phx).
assert (Pry : range_addressable (aview rsegs (w_H W1) memT) SHADOW_OFF (FA + 32) c).
{ replace (FA + 32) with (FA + 8 * Z.of_nat 4 + 0) by (cbn [Z.of_nat]; lia).
  apply (rtm_fsh_ra_obj rsegs (w_H W1) memT FA (CC_SH_A ++ repeat 0 12) 4 5 0 0 c HFSHT HF8);
  [change (length (CC_SH_A ++ repeat 0 12)) with 32%nat; lia | | lia | cbn [Z.of_nat]; lia | left; reflexivity].
  intros g Hg. apply (rtm_nth_range (CC_SH_A ++ repeat 0 12) 4 5 0); [vm_compute; reflexivity | lia]. }
assert (Phy : 0 < c -> shadow_hull_vis (aview rsegs (w_H W1) memT) (FA + 32) c)
  by (intros Hc0; apply (c2_want_hull (w_H W1) memT FA (CC_SH_A ++ repeat 0 12) c HFSHT
      ltac:(reflexivity) BF32 ltac:(lia))).
(* the call *)
eapply SRr_bind.
{ exact (c2_bcmp_at W1 regsT memT STK sp0 FP ly S W0 mem0 md0 ((CC_CID, fpos) :: own) lyc S1 mdT k
  buf (FA + 32) c (RB - sp0) (w64 539600) HJT R10v R11v R12v Pc32
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(rewrite HspR; lia) ltac:(rewrite Zminus_mod, Bsp0m; apply Z.mod_divide in BRB32 as [q Hq];
    [rewrite Hq; replace (q * 32) with ((2 * q) * 16) by ring; rewrite Z_mod_mult; reflexivity | lia])
  ltac:(lia) ltac:(lia)
  ltac:(rewrite R3v, QQ3; exact Hgp) ltac:(rewrite R4v, QQ4; exact Htp) R1v
  ltac:(vm_compute; reflexivity)
  Psx Psy Pbx Pby Pmx Pmy Prx Phx Pry Phy). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hsame2 & Hv2 & Hcmp & Hfr2 & Hpres2).
(* the answer is 0: the first c bytes of buf and of want agree *)
assert (Hv0 : v = w64 0).
{ apply (proj2 Hcmp). intros i Hi.
  apply (ccsv_bcmp_eq_av rsegs (w_H W1) memT buf (FA + 32) (RateCsv.csv_list mask) n Hg1 HWT).
  lia. }
(* what the call kept *)
assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (RB - 2 * ESTACK <= a < RB) ->
  aview rsegs (w_H W1) mem2 a = aview rsegs (w_H W1) memT a) by (intros a Ha Hw; apply Hfr2; lia).
assert (HFSH2 : rt_fsh rsegs (w_H W1) mem2 FA (CC_SH_A ++ repeat 0 12)).
{ apply (rtm_fsh_kept rsegs (w_H W1) memT (w_H W1) mem2 FA _ HFSHT).
  intros i Hi. change (Z.of_nat (length (CC_SH_A ++ repeat 0 12))) with 32 in Hi.
  apply KEEP2; lia. }
assert (Hg2 : garr8 rsegs (mrestrict (w_H W1) mem2) buf (RateCsv.csv_cut (RateCsv.csv_list mask) n ++ [0])).
{ apply (c2_garr8_kept (w_H W1) memT (w_H W1) mem2 buf _ Hg1).
  intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. apply KEEP2; lia. }
assert (Hlast : aview rsegs (w_H W1) mem2 (buf + c) = Some 0)
  by (rewrite Hceq; exact (ccsv_last rsegs (w_H W1) mem2 buf (RateCsv.csv_list mask) n Hg2)).
assert (Q3 : getr regs2 3 = getr regs1 3) by (etransitivity; [apply (HP2 3); unfold acallee_saved; lia | exact R3v]).
assert (Q4 : getr regs2 4 = getr regs1 4) by (etransitivity; [apply (HP2 4); unfold acallee_saved; lia | exact R4v]).
assert (Q8 : getr regs2 8 = getr regs1 8) by (etransitivity; [apply (HP2 8); unfold acallee_saved; lia | exact R8v]).
assert (Q18 : getr regs2 18 = getr regs1 18) by (etransitivity; [apply (HP2 18); unfold acallee_saved; lia | exact R18v]).
assert (Q23 : getr regs2 23 = getr regs1 23) by (etransitivity; [apply (HP2 23); unfold acallee_saved; lia | exact R23v]).
assert (Q24 : getr regs2 24 = getr regs1 24) by (etransitivity; [apply (HP2 24); unfold acallee_saved; lia | exact R24v]).
pose proof (proj1 HJ2) as HAR2.
destruct (rtm_blk_ra rsegs B lyc S1 W1 mem2 md2 buf m (buf + c) 1 HAR2 Hinb1 ltac:(lia) ltac:(lia)) as (Hra2 & _).
assert (HRC : exists sb, aview rsegs (w_H W1) mem2 (shadow_of_addr SHADOW_OFF (buf + c)) = Some sb /\ saddr_ok (buf + c) sb)
by (eapply rtm_ra_cell; exact Hra2).
destruct HRC as (sb & Hsb & Hsok). rewrite <- c2_sh_eq in Hsb.
assert (Hsb7 : 0 <= sb <= 7).
{ destruct Hsok as [Hz|[Hm1 Hm2]]; [rewrite Hz; lia | pose proof (Z.mod_pos_bound (buf + c) 8 ltac:(lia)); lia]. }
destruct (al_frames _ _ LAWS lyc S1 W1 mem2 md2 CC_CID fpos HAR2 Hfin) as (_ & _ & Hfpres2 & Hfspres2).
change (fs_frame_bytes CC_CID / 8) with 32 in Hfspres2. change (fs_frame_bytes CC_CID) with 256 in Hfpres2.
(* the engine state at 0x83bd0 *)
set (EX := [w64 (buf + c); w64 (shadow_addr (buf + c)); w64 sb]).
assert (Ew32 : ew (Ereg regs2 EX) 32%nat = Z_to_bv 64 (buf + c)) by reflexivity.
assert (Ew33 : ew (Ereg regs2 EX) 33%nat = Z_to_bv 64 (shadow_addr (buf + c))) by reflexivity.
assert (Ew34 : ew (Ereg regs2 EX) 34%nat = Z_to_bv 64 sb) by reflexivity.
assert (Rk : forall r, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr regsT (Z_to_bv 5 r)) by exact HP2.
assert (N19 : getr regs2 19 = w64 buf)
by (etransitivity; [apply (Rk 19); unfold acallee_saved; lia | exact R19v]).
assert (N20 : getr regs2 20 = w64 c)
by (etransitivity; [apply (Rk 20); unfold acallee_saved; lia | exact R20v]).
assert (N25 : getr regs2 25 = w64 SHADOW_OFF)
by (etransitivity; [apply (Rk 25); unfold acallee_saved; lia | exact R25v]).
assert (N23 : getr regs2 23 = w64 (shadow_addr FA)).
{ etransitivity; [apply (Rk 23); unfold acallee_saved; lia|].
  etransitivity; [apply R23v | exact QQ23]. }
assert (Ew19 : ew (Ereg regs2 EX) 19%nat = Z_to_bv 64 buf)
by (rewrite (ew_Ereg_nat regs2 EX 19%nat (19%bv : bv 5) eq_refl); exact N19).
assert (Ew20 : ew (Ereg regs2 EX) 20%nat = Z_to_bv 64 c)
by (rewrite (ew_Ereg_nat regs2 EX 20%nat (20%bv : bv 5) eq_refl); exact N20).
assert (Ew25 : ew (Ereg regs2 EX) 25%nat = Z_to_bv 64 SHADOW_OFF)
by (rewrite (ew_Ereg_nat regs2 EX 25%nat (25%bv : bv 5) eq_refl); exact N25).
assert (Ew23 : bv_unsigned (ew (Ereg regs2 EX) 23%nat) = shadow_addr FA).
{ rewrite (ew_Ereg_nat regs2 EX 23%nat (23%bv : bv 5) eq_refl), N23. apply unsigned_lit_small; lia. }
assert (Eb23 : base_val (Ereg regs2 EX) (Some 23%nat) = shadow_addr FA) by exact Ew23.
assert (Vw32 : bv_unsigned (ew (Ereg regs2 EX) 32%nat) = buf + c) by (rewrite Ew32; apply unsigned_lit_small; lia).
assert (Vw33 : bv_unsigned (ew (Ereg regs2 EX) 33%nat) = shadow_addr (buf + c))
  by (rewrite Ew33; apply unsigned_lit_small; pose proof (c2_band (buf + c) ltac:(lia)); lia).
pose proof (c2_band (buf + c) ltac:(lia)) as Hband.
pose proof (c2_band FA ltac:(lia)) as HFAband.
assert (Hsep : ~ (FA <= buf + c < FA + 256)) by (destruct Hd as [Hd|Hd]; lia).
assert (Dfb : shadow_addr FA + 32 <= shadow_addr (buf + c) + 0 \/ shadow_addr (buf + c) + 1 <= shadow_addr FA + 0).
{ pose proof (c2_div_out (buf + c) FA HF8 ltac:(lia) ltac:(lia) Hsep) as X.
  unfold shadow_addr. destruct X as [X|X]; [right; lia | left; lia]. }
assert (Dfc : shadow_addr FA + 32 <= buf + c + 0 \/ buf + c + 1 <= shadow_addr FA + 0).
{ pose proof (app_vs_shadow buf m FA 256 (buf + c) Hbapp BFapp ltac:(lia) ltac:(lia)) as Y.
  change (256 / 8) with 32 in Y.
  destruct (c2_out_disj (buf + c) (shadow_addr FA) (shadow_addr FA + 32) Y) as [Z1|Z1]; [right; lia | left; lia]. }
assert (Dbc : shadow_addr (buf + c) + 1 <= buf + c + 0 \/ buf + c + 1 <= shadow_addr (buf + c) + 0).
{ unfold in_app in Hbapp. destruct Hbapp as (_ & [Hlow | [Hhigh _]]); [right | left];
  unfold kLowShadowBeg, kLowMemEnd, kHighMemBeg in *; lia. }
assert (HS : st_ok rsegs (Ereg regs2 EX)
  (mkSS 539600 sr_atoms (c2_mem_c (SOff 34 0)) None (c2_facts_c [(34%nat, mkAF 0 7 0)]))
  (restrict (w_H W1) (mkst regs2 (Z_to_bv 64 539600) mem2 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute; reflexivity.
  - unfold c2_mem_c, c2_fsh_reg, c2_cell.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    + apply (rtm_rw_region rsegs (Ereg regs2 EX) (w_H W1) mem2 23%nat (shadow_addr FA) 0 32 4 9);
      [exact Ew23 | lia | lia | |].
      * intros o Ho. exact (proj1 (Hfspres2 o ltac:(lia))).
      * apply (rtm_fsh_chunks rsegs (Ereg regs2 EX) (w_H W1) mem2 FA (CC_SH_A ++ repeat 0 12) HFSH2 c2_sh_bytes).
    + apply (rtm_cell_region rsegs (Ereg regs2 EX) (w_H W1) mem2 33%nat (shadow_addr (buf + c)) sb (SOff 34 0));
      [exact Vw33 | exact Hsb | apply rts_den_atom; [exact Ew34 | lia] | lia | lia].
    + apply (rtm_cell_region rsegs (Ereg regs2 EX) (w_H W1) mem2 32%nat (buf + c) 0 (SLit 0));
      [exact Vw32 | exact Hlast | reflexivity | lia | lia].
  - unfold c2_mem_c, c2_fsh_reg, c2_cell.
    cbv [pairwise_disjoint all_disjoint extent_disjoint YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite Ew23, Vw32, Vw33.
    repeat split; try exact I; first [exact Dfb | exact Dfc | exact Dbc].
  - unfold c2_facts_c, c2_alias_sh. split; [|split].
    + cbn [f_atoms atoms_ok]. split; [|exact I].
      unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Ew34, (unsigned_lit_small sb) by lia.
      change (2 ^ 0) with 1. rewrite Z.mod_1_r. split; [lia|]. split; [reflexivity | lia].
    + exact I.
    + cbn [f_alias alias_ok]. split; [|split; [|exact I]].
      * rewrite (c2_denot_add (Ereg regs2 EX) 19%nat 20%nat buf c Ew19 Ew20 ltac:(lia) ltac:(lia) ltac:(lia)).
        symmetry. apply rts_den_atom; [exact Ew32 | lia].
      * exact (shadow_decl_ok (Ereg regs2 EX) 32%nat 25%nat 33%nat (buf + c) SHADOW_OFF Ew32 ltac:(lia) Ew25 Ew33). }
(* a0 is 0, so `bnez a0` is not taken *)
assert (Hpin : getr (ms_regs (mkst regs2 (Z_to_bv 64 539600) mem2 (seg_rom rsegs))) (10%bv : bv 5) = Z_to_bv 64 0)
  by (cbn [ms_regs mkst]; rewrite Hv2, Hv0; reflexivity).
pose proof (st_ok_pin_lit rsegs (Ereg regs2 EX) _ _ (10%bv : bv 5) 0 HS eq_refl
  ltac:(cbn [ms_regs restrict mkst]; rewrite Hv2, Hv0; reflexivity)) as HSp.
clear HS. rename HSp into HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
(* the run to 0x83c40 *)
change (w64 539600) with (Z_to_bv 64 539600).
aj_run_to TBL HS HJ2 CC_PC3.
{ c2_awr (Ereg regs2 EX) Ew23. }
rename HFr into FR1. clear HF HG.
lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (shadow_addr FA + 4 <= a < shadow_addr FA + 9) ->
aview rsegs (w_H W1) (ms_mem msx) a = aview rsegs (w_H W1) mem2 a) end.
{ intros a Ha Hw. refine (c2_kept_win _ _ (w_H W1) mem2 _ _ _ FR1 _ a Ha Hw). c2_wrtac Eb23. }
srr_branch_with TBL HS.
- (* the shadow byte is not 0: the slow block's compare passes by saddr_ok *)
  assert (Hsbne : sb <> 0).
  { rewrite branch_ne_U in Hc. rewrite (U_atom (Ereg regs2 EX) 34%nat sb Ew34 ltac:(lia)), U_SLit in Hc.
    change (zcanon 0) with 0 in Hc. apply negb_true_iff, Z.eqb_neq in Hc. exact Hc. }
  assert (Hmod : (buf + c) mod 8 < sb) by (destruct Hsok as [Hz|[Hm1 Hm2]]; [contradiction | lia]).
  aj_run_to TBL HS HJ2 CC_PC3.
  { c2_awr (Ereg regs2 EX) Ew23. }
  rename HFr into FR2. clear HF HG.
  lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
  assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (shadow_addr FA + 4 <= a < shadow_addr FA + 9) ->
  aview rsegs (w_H W1) (ms_mem msx) a = aview rsegs (w_H W1) mem2 a) end.
  { intros a Ha Hw. etransitivity;
    [refine (c2_kept_win _ _ (w_H W1) _ _ _ _ FR2 _ a Ha Hw) | exact (KA a Ha Hw)]. c2_wrtac Eb23. }
  srr_branch_with TBL HS.
  + (* the check passes *)
    aj_run_to TBL HS HJ2 CC_PC3.
    { c2_awr (Ereg regs2 EX) Ew23. }
    rename HFr into FR3. clear HF HG.
    lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
    assert (KC : forall a, 0 <= a < 2 ^ 64 -> ~ (shadow_addr FA + 4 <= a < shadow_addr FA + 9) ->
    aview rsegs (w_H W1) (ms_mem msx) a = aview rsegs (w_H W1) mem2 a) end.
    { intros a Ha Hw. etransitivity;
      [refine (c2_kept_win _ _ (w_H W1) _ _ _ _ FR3 _ a Ha Hw) | exact (KB a Ha Hw)]. c2_wrtac Eb23. }
    c2_finish KC KEEP2 KEEPT (Ereg regs2 EX) Ew23.
  + (* the error arm: saddr_ok refuses it *)
    exfalso. rewrite (c2_and7_lt (Ereg regs2 EX) 32%nat (buf + c) sb Ew32 ltac:(lia) Ew34 ltac:(lia)) in Hc0.
    apply Z.ltb_ge in Hc0. lia.
- (* the shadow byte is 0: the check passes at once *)
  aj_run_to TBL HS HJ2 CC_PC3.
  { c2_awr (Ereg regs2 EX) Ew23. }
  rename HFr into FR2. clear HF HG.
  lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
  assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (shadow_addr FA + 4 <= a < shadow_addr FA + 9) ->
  aview rsegs (w_H W1) (ms_mem msx) a = aview rsegs (w_H W1) mem2 a) end.
  { intros a Ha Hw. etransitivity;
    [refine (c2_kept_win _ _ (w_H W1) _ _ _ _ FR2 _ a Ha Hw) | exact (KA a Ha Hw)]. c2_wrtac Eb23. }
  c2_finish KB KEEP2 KEEPT (Ereg regs2 EX) Ew23.
Qed.


(* ---- n > 0: from 0x83ba8 to the call at 0x421a8, c = min(len, n - 1) ---- *)
Lemma c2_arm1 : 0 < n -> SRr rsegs W1 (cfg_at rsegs CC_PC2 regs1 mem1 md1) GOAL.
Proof.
intros Hnpos. c2_names.
pose proof c2_base as (HAR1 & HARc & Hfin & BF32 & BF4 & BFc & BFapp & BSH0 & BSHc & BRB32 & BRBlo & BRBhi
& BspA & BspB & Bsp16 & BlycA & BlycB & Bsp47 & Bsp0m).
pose proof (AR_laws_ok rsegs B) as LAWS. pose proof rts_segs_low as Hsegs. pose proof rts_wx as Hwx.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof c2_tbl_ok as TBL.
assert (Hes : ESTACK = 4096) by reflexivity. unfold T_csv_STK in BspA.
destruct Pblk as (m & Hinb & Hmge).
assert (Hm1 : 1 <= m) by (pose proof (Z.le_max_r n 1); lia).
assert (Hrq : req_size m = m) by (unfold req_size; replace (m =? 0) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
assert (Hinb1 : In (buf, m) (ablocks B lyc S1)) by (rewrite Hab; exact Hinb).
destruct (al_blocks _ _ LAWS lyc S1 W1 mem1 md1 buf m HAR1 Hinb1) as (Hb16 & Hb4096 & Hbceil & Hbapp & Hbpres & _ & _).
rewrite Hrq in Hbceil, Hbapp, Hbpres.
pose proof (RateCsv.csv_list_length mask ltac:(lia)) as HL17.
(* the symbolic state at 0x83ba8: n in atom 32, buf in atom 33 *)
set (EX := [w64 n; w64 buf]).
assert (Ew32 : ew (Ereg regs1 EX) 32%nat = Z_to_bv 64 n) by reflexivity.
assert (Ew33 : ew (Ereg regs1 EX) 33%nat = Z_to_bv 64 buf) by reflexivity.
assert (Ew9 : bv_unsigned (ew (Ereg regs1 EX) 9%nat) = RB)
by (rewrite (ew_Ereg_nat regs1 EX 9%nat (9%bv : bv 5) eq_refl), G9; apply unsigned_lit_small; lia).
assert (Eb9 : base_val (Ereg regs1 EX) (Some 9%nat) = RB) by exact Ew9.
assert (Ew20 : ew (Ereg regs1 EX) 20%nat = w64 (Z.of_nat (length (RateCsv.csv_list mask))))
by (rewrite (ew_Ereg_nat regs1 EX 20%nat (20%bv : bv 5) eq_refl); exact G20).
assert (HSL : rtm_slots rsegs (w_H W1) mem1 RB [(16, n); (24, buf)]).
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd].
  - replace (n mod 2 ^ 64) with n by (symmetry; apply Z.mod_small; lia).
    apply val_mem_of_rdword. exact H16.
  - replace (buf mod 2 ^ 64) with buf by (symmetry; apply Z.mod_small; lia).
    apply val_mem_of_rdword. exact H24. }
assert (HS : st_ok rsegs (Ereg regs1 EX) (mkSS CC_PC2 sr_atoms c2_mem_b None c2_facts_b)
(restrict (w_H W1) (mkst regs1 (Z_to_bv 64 CC_PC2) mem1 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute; reflexivity.
  - unfold c2_mem_b, c2_stk_reg.
    apply Forall_cons; [|apply Forall_nil].
    apply (rtm_ro_region rsegs (Ereg regs1 EX) (w_H W1) mem1 9%nat RB 16 32); [exact Ew9 | lia | lia |].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + apply (rtm_slots_chunk rsegs (Ereg regs1 EX) (w_H W1) mem1 RB [(16, n); (24, buf)] 16 n (SOff 32 0) HSL);
      [left; reflexivity | apply rts_den_atom; [exact Ew32 | lia] | lia].
    + apply (rtm_slots_chunk rsegs (Ereg regs1 EX) (w_H W1) mem1 RB [(16, n); (24, buf)] 24 buf (SOff 33 0) HSL);
      [right; left; reflexivity | apply rts_den_atom; [exact Ew33 | lia] | lia].
  - unfold c2_mem_b, c2_stk_reg.
    cbv [pairwise_disjoint all_disjoint extent_disjoint]. repeat split; try exact I.
  - unfold c2_facts_b. split; [|split].
    + cbn [f_atoms atoms_ok]. split; [|split; [|exact I]].
      * unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Ew32, (unsigned_lit_small n) by lia.
        change (2 ^ 0) with 1. rewrite Z.mod_1_r. split; [lia|]. split; [reflexivity | lia].
      * unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Ew33, (unsigned_lit_small buf) by lia.
        change (2 ^ 4) with 16. split; [lia|]. split; [exact Hb16 | lia].
    + exact I.
    + exact I. }
(* a4 is s4's atom, so `bne s4,a4` is decided *)
assert (Hpin : sv_denot (Ereg regs1 EX) (SOff 20 0) = getr regs1 14).
{ rewrite G14. apply rts_den_atom; [exact Ew20 | lia]. }
pose proof (st_ok_pin_sv rsegs (Ereg regs1 EX) _ _ (14%bv : bv 5) (SOff 20 0) HS eq_refl Hpin) as HSp.
clear HS. rename HSp into HS.
unfold cfg_at. change (w64 CC_PC2) with (Z_to_bv 64 CC_PC2).
aj_run_to TBL HS HJ1 270760.
{ c2_awr (Ereg regs1 EX) Eb9. }
rename HFr into FR1. clear HF HG.
lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
assert (KA : forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W1) (ms_mem msx) a = aview rsegs (w_H W1) mem1 a) end.
{ intros a Ha. refine (c2_kept_win _ _ (w_H W1) mem1 _ 0 0 FR1 _ a Ha ltac:(lia)). c2_wrtac Eb9. }
srr_branch_with TBL HS.
- (* `bltu s4,a0` taken: len < n - 1, c = len *)
  assert (Hlt : Z.of_nat (length (RateCsv.csv_list mask)) < n - 1).
  { rewrite branch_ltu_U in Hc. rewrite (U_atom (Ereg regs1 EX) 20%nat _ Ew20 ltac:(lia)) in Hc.
    rewrite (YN3v.U_off (Ereg regs1 EX) 32%nat (-1)) in Hc
      by (rewrite Ew32, (unsigned_lit_small n) by lia; unfold M64; lia).
    rewrite Ew32, (unsigned_lit_small n) in Hc by lia. apply Z.ltb_lt in Hc. lia. }
  aj_run_to TBL HS HJ1 270760.
  { c2_awr (Ereg regs1 EX) Eb9. }
  rename HFr into FR2. clear HF HG.
  lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
  assert (KB : forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W1) (ms_mem msx) a = aview rsegs (w_H W1) mem1 a) end.
  { intros a Ha. etransitivity;
    [refine (c2_kept_win _ _ (w_H W1) _ _ 0 0 FR2 _ a Ha ltac:(lia)) | exact (KA a Ha)]. c2_wrtac Eb9. }
  pose proof (st_ok_restrict_mkst rsegs (w_H W1) (Ereg regs1 EX) _ _ HS eq_refl) as Ems. rewrite Ems at 1.
  apply (c2_tail1 (Z.of_nat (length (RateCsv.csv_list mask)))).
  + exact Hnpos.
  + rewrite (ccsv_c_lt (RateCsv.csv_list mask) n Hlt). reflexivity.
  + exact HJ1.
  + let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio.
  + exact KB.
  + eapply (c2_reg_den (Ereg regs1 EX) _ _ (w_H W1) _ (SLit 539600)); [exact HS | vm_compute; reflexivity | reflexivity].
  + etransitivity; [eapply (regs_kept_of_st_ok rsegs (Ereg regs1 EX) _ _ regs1 EX (w_H W1) [1; 10; 12; 14; 19; 20]%bv HS); [apply env_agree_refl | vm_compute; reflexivity | vm_compute; discriminate | apply c2_notin; vm_compute; reflexivity] | exact G2].
  + eapply (regs_kept_of_st_ok rsegs (Ereg regs1 EX) _ _ regs1 EX (w_H W1) [1; 10; 12; 14; 19; 20]%bv HS); [apply env_agree_refl | vm_compute; reflexivity | vm_compute; discriminate | apply c2_notin; vm_compute; reflexivity].
  + eapply (regs_kept_of_st_ok rsegs (Ereg regs1 EX) _ _ regs1 EX (w_H W1) [1; 10; 12; 14; 19; 20]%bv HS); [apply env_agree_refl | vm_compute; reflexivity | vm_compute; discriminate | apply c2_notin; vm_compute; reflexivity].
  + eapply (regs_kept_of_st_ok rsegs (Ereg regs1 EX) _ _ regs1 EX (w_H W1) [1; 10; 12; 14; 19; 20]%bv HS); [apply env_agree_refl | vm_compute; reflexivity | vm_compute; discriminate | apply c2_notin; vm_compute; reflexivity].
  + eapply (c2_reg_den (Ereg regs1 EX) _ _ (w_H W1) _ (SOff 33 0));
    [exact HS | vm_compute; reflexivity | apply rts_den_atom; [exact Ew33 | lia]].
  + etransitivity; [eapply (regs_kept_of_st_ok rsegs (Ereg regs1 EX) _ _ regs1 EX (w_H W1) [1; 10; 12; 14; 19; 20]%bv HS); [apply env_agree_refl | vm_compute; reflexivity | vm_compute; discriminate | apply c2_notin; vm_compute; reflexivity] | exact G11].
  + eapply (c2_reg_den (Ereg regs1 EX) _ _ (w_H W1) _ (SOff 20 0));
    [exact HS | vm_compute; reflexivity | apply rts_den_atom; [exact Ew20 | lia]].
  + eapply (regs_kept_of_st_ok rsegs (Ereg regs1 EX) _ _ regs1 EX (w_H W1) [1; 10; 12; 14; 19; 20]%bv HS); [apply env_agree_refl | vm_compute; reflexivity | vm_compute; discriminate | apply c2_notin; vm_compute; reflexivity].
  + eapply (c2_reg_den (Ereg regs1 EX) _ _ (w_H W1) _ (SOff 33 0));
    [exact HS | vm_compute; reflexivity | apply rts_den_atom; [exact Ew33 | lia]].
  + eapply (c2_reg_den (Ereg regs1 EX) _ _ (w_H W1) _ (SOff 20 0));
    [exact HS | vm_compute; reflexivity | apply rts_den_atom; [exact Ew20 | lia]].
  + eapply (regs_kept_of_st_ok rsegs (Ereg regs1 EX) _ _ regs1 EX (w_H W1) [1; 10; 12; 14; 19; 20]%bv HS); [apply env_agree_refl | vm_compute; reflexivity | vm_compute; discriminate | apply c2_notin; vm_compute; reflexivity].
  + eapply (regs_kept_of_st_ok rsegs (Ereg regs1 EX) _ _ regs1 EX (w_H W1) [1; 10; 12; 14; 19; 20]%bv HS); [apply env_agree_refl | vm_compute; reflexivity | vm_compute; discriminate | apply c2_notin; vm_compute; reflexivity].
  + etransitivity; [eapply (regs_kept_of_st_ok rsegs (Ereg regs1 EX) _ _ regs1 EX (w_H W1) [1; 10; 12; 14; 19; 20]%bv HS); [apply env_agree_refl | vm_compute; reflexivity | vm_compute; discriminate | apply c2_notin; vm_compute; reflexivity] | exact G25].
- (* `bltu s4,a0` not taken: n - 1 <= len, `mv s4,a0` makes c = n - 1 *)
  assert (Hge : n - 1 <= Z.of_nat (length (RateCsv.csv_list mask))).
  { rewrite branch_ltu_U in Hc. rewrite (U_atom (Ereg regs1 EX) 20%nat _ Ew20 ltac:(lia)) in Hc.
    rewrite (YN3v.U_off (Ereg regs1 EX) 32%nat (-1)) in Hc
      by (rewrite Ew32, (unsigned_lit_small n) by lia; unfold M64; lia).
    rewrite Ew32, (unsigned_lit_small n) in Hc by lia. apply Z.ltb_ge in Hc. lia. }
  aj_run_to TBL HS HJ1 270760.
  { c2_awr (Ereg regs1 EX) Eb9. }
  rename HFr into FR2. clear HF HG.
  lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
  assert (KB : forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W1) (ms_mem msx) a = aview rsegs (w_H W1) mem1 a) end.
  { intros a Ha. etransitivity;
    [refine (c2_kept_win _ _ (w_H W1) _ _ 0 0 FR2 _ a Ha ltac:(lia)) | exact (KA a Ha)]. c2_wrtac Eb9. }
  pose proof (st_ok_restrict_mkst rsegs (w_H W1) (Ereg regs1 EX) _ _ HS eq_refl) as Ems. rewrite Ems at 1.
  apply (c2_tail1 (n - 1)).
  + exact Hnpos.
  + symmetry. exact (ccsv_c_ge (RateCsv.csv_list mask) n ltac:(lia) Hge).
  + exact HJ1.
  + let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio.
  + exact KB.
  + eapply (c2_reg_den (Ereg regs1 EX) _ _ (w_H W1) _ (SLit 539600)); [exact HS | vm_compute; reflexivity | reflexivity].
  + etransitivity; [eapply (regs_kept_of_st_ok rsegs (Ereg regs1 EX) _ _ regs1 EX (w_H W1) [1; 10; 12; 14; 19; 20]%bv HS); [apply env_agree_refl | vm_compute; reflexivity | vm_compute; discriminate | apply c2_notin; vm_compute; reflexivity] | exact G2].
  + eapply (regs_kept_of_st_ok rsegs (Ereg regs1 EX) _ _ regs1 EX (w_H W1) [1; 10; 12; 14; 19; 20]%bv HS); [apply env_agree_refl | vm_compute; reflexivity | vm_compute; discriminate | apply c2_notin; vm_compute; reflexivity].
  + eapply (regs_kept_of_st_ok rsegs (Ereg regs1 EX) _ _ regs1 EX (w_H W1) [1; 10; 12; 14; 19; 20]%bv HS); [apply env_agree_refl | vm_compute; reflexivity | vm_compute; discriminate | apply c2_notin; vm_compute; reflexivity].
  + eapply (regs_kept_of_st_ok rsegs (Ereg regs1 EX) _ _ regs1 EX (w_H W1) [1; 10; 12; 14; 19; 20]%bv HS); [apply env_agree_refl | vm_compute; reflexivity | vm_compute; discriminate | apply c2_notin; vm_compute; reflexivity].
  + eapply (c2_reg_den (Ereg regs1 EX) _ _ (w_H W1) _ (SOff 33 0));
    [exact HS | vm_compute; reflexivity | apply rts_den_atom; [exact Ew33 | lia]].
  + etransitivity; [eapply (regs_kept_of_st_ok rsegs (Ereg regs1 EX) _ _ regs1 EX (w_H W1) [1; 10; 12; 14; 19; 20]%bv HS); [apply env_agree_refl | vm_compute; reflexivity | vm_compute; discriminate | apply c2_notin; vm_compute; reflexivity] | exact G11].
  + eapply (c2_reg_den (Ereg regs1 EX) _ _ (w_H W1) _ (SOff 32 (-1)));
    [exact HS | vm_compute; reflexivity | apply (c2_den_off _ 32%nat n (-1) (n - 1)); [exact Ew32 | lia | lia | lia]].
  + eapply (regs_kept_of_st_ok rsegs (Ereg regs1 EX) _ _ regs1 EX (w_H W1) [1; 10; 12; 14; 19; 20]%bv HS); [apply env_agree_refl | vm_compute; reflexivity | vm_compute; discriminate | apply c2_notin; vm_compute; reflexivity].
  + eapply (c2_reg_den (Ereg regs1 EX) _ _ (w_H W1) _ (SOff 33 0));
    [exact HS | vm_compute; reflexivity | apply rts_den_atom; [exact Ew33 | lia]].
  + eapply (c2_reg_den (Ereg regs1 EX) _ _ (w_H W1) _ (SOff 32 (-1)));
    [exact HS | vm_compute; reflexivity | apply (c2_den_off _ 32%nat n (-1) (n - 1)); [exact Ew32 | lia | lia | lia]].
  + eapply (regs_kept_of_st_ok rsegs (Ereg regs1 EX) _ _ regs1 EX (w_H W1) [1; 10; 12; 14; 19; 20]%bv HS); [apply env_agree_refl | vm_compute; reflexivity | vm_compute; discriminate | apply c2_notin; vm_compute; reflexivity].
  + eapply (regs_kept_of_st_ok rsegs (Ereg regs1 EX) _ _ regs1 EX (w_H W1) [1; 10; 12; 14; 19; 20]%bv HS); [apply env_agree_refl | vm_compute; reflexivity | vm_compute; discriminate | apply c2_notin; vm_compute; reflexivity].
  + etransitivity; [eapply (regs_kept_of_st_ok rsegs (Ereg regs1 EX) _ _ regs1 EX (w_H W1) [1; 10; 12; 14; 19; 20]%bv HS); [apply env_agree_refl | vm_compute; reflexivity | vm_compute; discriminate | apply c2_notin; vm_compute; reflexivity] | exact G25].
Qed.

End arms.



Theorem ccsv_S2 : CC_S2_stmt B MT.
Proof.
unfold CC_S2_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf n mask fpos S1 W1 regs1 mem1 md1 H2.
pose proof H2 as ((_ & _ & _ & Pn & _) & _).
destruct (Z.eq_dec n 0) as [Hn0|Hn0].
- exact (c2_arm0 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf n mask fpos S1 W1 regs1 mem1 md1 H2 Hn0).
- exact (c2_arm1 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf n mask fpos S1 W1 regs1 mem1 md1 H2
    ltac:(lia)).
Qed.

End s2.

Print Assumptions ccsv_S2.
