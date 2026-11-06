(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/cgif/cgif_file_fuzzer/lib/A/AC8j.v at c8557374ad2e (st_ok_region_nth, field_of_region, as pa_i_region_nth over a restricted state and pa_i_field) and proofs/reac-pw/fuzz_role/lib/Reusable/YCbq.v at a0d3fb0309b (aj_intrin_at, as pa_i_memset_at: at OSet on rsegs, its post adds same_io from the contract's same_but_materialized); the rest of the file is new: the block lemma pa_int7 of LLVMFuzzerTestOneInput's shape-7 Int pod block and its helpers. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPropIntB.v at a529a88a6181 (the block lemma pa_int7 and its helpers) and the piece pa_piece_int7 of proofs/reac-pw/fuzz_role/lib/A/RPgProp.v at the same commit, for reac-pw/fuzz_rate image A: rate's pcs (SEL7 0x80e6c, the memset call 0x80fec to 0x51cfc with return 0x80ff0, LATCH7 0x82530), registers (s6 / s7 / s2 for role's s4 / s5 / s7) and real-frame cells (i at R+0xf8, -0x3ffd at R+0x130, -0x4001 at R+0x118 and in s10); rate's block keeps what is left of the input (s8) in s10 across the pad and restores s8 and s10 at its end, so both join the clobbered set and the block's relation states their end values; the call is lib/A/RtPgSteps.v rts_intrin_at (in place of pa_i_memset_at), the region lemma its rts_region_nth (in place of pa_i_region_nth); the block post is RtPgSteps' rts_post; the cut lists of the piece are lib/A/RtPgSeg.v's. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgPropIntB.v, with its module paths and module names changed; 384 of its 463 lines of code are new or changed and 511 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPropSelB.v (the sel block pa_sel) and the sel
   piece pa_piece_sel of proofs/reac-pw/fuzz_role/lib/A/RPgProp.v, both at a529a88a6181, for reac-pw/fuzz_rate image A:
   rate's pcs, registers (in.n in s8, the shadow offset in s2, the shadow address of pp + 0x4000 in s6, pp + 0x4000
   in s7) and real-frame cells (i R+0xf8, the cursor R+0x100, sh R+0xd8, -0x3ffd R+0x130); with no input left the
   block stores nothing but i (rate's code does not write in.n there); the block post is lib/A/RtPgSteps.v rts_post;
   the cut lists are lib/A/RtPgSeg.v's. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgPropSelB.v at 533bf30ff015 for image B
   (fuzz_rate.asan-ubsan): image B's pcs and registers (the cursor in s2, what is left in t4, the shadow offset in s4,
   s9 = 1, the cursor after the byte in s10), the shape-7 flag in R+0x110 tested by `beqz`, the UBSan pointer test
   0x80fbc decided from the cursor's closed atom range, the slow block's `blt; j report; j back` form; the block reads
   no pp->len and writes no memory; the block post is lib/AU/RtPgStepsB.v rtsb_post, the kit lib/AU/RtPgPropBKit.v and
   lib/AU/RtPgPropBLib.v, the cut lists lib/AU/RtPgSegB.v's. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; every address below is measured on its unstripped
   twin sha256 a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1): the sel block N 0x80fb4 of
   LLVMFuzzerTestOneInput's property loop, to SEL7 0x80ff4 (sh = 7) or SELK 0x810a4, as a block lemma over
   lib/AU/RtPgPropBKit.v, and the piece rsb_piece_W4_sel_stmt (N -> SEL7 / SELK) of lib/AU/RtPgSegB.v. Proves no
   function (kind: segment lemma).
     0x80fb4 beqz t4                              no input left: 0x80fe4 a1 = 0; 0x80fe8 s10 = s2; -> 0x80fec
     0x80fb8 addi s10,s2,1; 0x80fbc bltu s9,s10   s9 = 1: taken for every cursor in [1, 2^63 - 1] (else j 0x83098)
     0x80fc4 .. 0x80fd4 the check of the byte at the cursor (lb a0 of (s2 >> 3) + s4; beqz a0 -> 0x80fd8; else
                                                  j 0x82594 = andi a1,s2,7; blt a1,a0 -> 0x825a0 j 0x80fd8; else
                                                  j 0x83440, the report)
     0x80fd8 lbu a1,0(s2); t4 - 1; j 0x80fec
     0x80fec ld a0,0x110(s1) = the shape-7 flag; 0x80ff0 beqz a0 -> 0x810a4 (SELK), else 0x80ff4 (SEL7).
   The walk splits on nl = 0 before its entry state. With nl > 0 the input byte b is a region based at the cursor's
   atom and its shadow byte s a region based at a fresh atom (the cursor's shadow address, tied to the cursor by an
   alias fact); s = 0 runs on, s <> 0 goes through 0x82594, whose report arm dies by saddr_ok. The block writes no
   memory: the cursor after the byte is s10 and what is left t4. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgImgB RtPgStepsB RtPgMemB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgSegB RtPgPropBKit RtPgPropBLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* image B's loaded segments, as lib/AU/RtPgStepsB.v names them *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

Local Arguments x_STK {segs} _.
Local Arguments x_sp0 {segs} _.
Local Arguments x_FP {segs} _.
Local Arguments x_ly {segs} _.
Local Arguments x_S {segs} _.
Local Arguments x_W0 {segs} _.
Local Arguments x_mem0 {segs} _.
Local Arguments x_md0 {segs} _.
Local Arguments x_own {segs} _.
Local Arguments x_k {segs} _.
Local Arguments x_regs {segs} _.
Local Arguments x_lyc {segs} _.
Local Arguments x_Sc {segs} _.
Local Arguments x_W {segs} _.
Local Arguments x_memc {segs} _.
Local Arguments x_mdc {segs} _.
Local Arguments x_RLO {segs} _.
Local Arguments x_RHI {segs} _.
Local Arguments x_e {segs} _.
Local Arguments x_pos {segs} _.

(* ---- the entry states ----
   env slots (pab_extra): 32 K, 33 nl, 34 cur, 35 the shape-7 flag f, 36 b, 37 the cursor's shadow address, 38 its
   byte s *)
(* s4 = K, s9 = 1, s2 = cur, t4 = nlv (in.n) *)
Definition pab_s_sr (nlv : sv) : list sv :=
  sr_set (sr_set (sr_set (sr_set sr_atoms (20%bv : bv 5) (SOff 32 0)) (25%bv : bv 5) (SLit 1))
    (18%bv : bv 5) (SOff 34 0)) (29%bv : bv 5) nlv.
(* the one cell of R the block reads: the shape-7 flag *)
Definition pab_s_r110 : YP09.region := YP09.mkRegion (Some 9%nat) 0x110 0x118 0 0 [ YP09.mkChunk 0x110 (CVal 8 (SOff 35 0)) ].
(* the input byte at the cursor and its shadow byte *)
Definition pab_s_rin : YP09.region := YP09.mkRegion (Some 34%nat) 0 1 0 0 [ YP09.mkChunk 0 (CVal 1 (SOff 36 0)) ].
Definition pab_s_rcell : YP09.region := YP09.mkRegion (Some 37%nat) 0 1 0 0 [ YP09.mkChunk 0 (CVal 1 (SOff 38 0)) ].
(* R lies in the stack above the allocator's ceiling; every bound is a closed numeral *)
Definition pab_s_G1 : facts := mkFacts
  [ (9%nat, mkAF 70368744177664 140737488355328 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
    (33%nat, mkAF 1 9223372036854775807 0); (34%nat, mkAF 1 9223372036854775807 0); (35%nat, mkAF 0 1 0);
    (36%nat, mkAF 0 255 0); (38%nat, mkAF 0 7 0) ] []
  [ (SAlu ALU_ADD (SAlu ALU_SRL (SOff 34 0) (SLit 3)) (SOff 32 0), SOff 37 0) ].
Definition pab_s_G0 : facts := mkFacts
  [ (9%nat, mkAF 70368744177664 140737488355328 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
    (34%nat, mkAF 1 9223372036854775808 0); (35%nat, mkAF 0 1 0) ] [] [].
Definition ss_s1 : sstate :=
  mkSS PAB_N (pab_s_sr (SOff 33 0)) [pab_s_r110; pab_s_rin; pab_s_rcell] None pab_s_G1.
Definition ss_s0 : sstate :=
  mkSS PAB_N (pab_s_sr (SLit 0)) [pab_s_r110] None pab_s_G0.

(* ---- small facts ---- *)
(* an override of a register by a value it already has keeps regs_ok *)
Lemma pab_s_override : forall E sr regs (r : bv 5) e,
regs_ok E sr regs -> r <> 0%bv -> sv_denot E e = getr regs r -> regs_ok E (sr_set sr r e) regs.
Proof.
intros E sr regs r e Hr Hr0 Hv r'.
unfold sr_set. destruct (bv_eqb r 0) eqn:Hb0.
{ exfalso. apply Hr0. unfold bv_eqb in Hb0. apply Z.eqb_eq in Hb0. apply bv_eq. exact Hb0. }
specialize (Hr r'). unfold sr_get in *.
destruct (bv_eqb r' 0) eqn:Hr'0; [exact Hr|].
rewrite nth_sr_upd.
destruct (Nat.eqb (ridx r') (ridx r)) eqn:Hi; [|exact Hr].
apply Nat.eqb_eq in Hi. apply ridx_inj in Hi. subst r'. symmetry. exact Hv.
Qed.
(* the value of the shadow address expression (x >> 3) + k *)
Lemma pab_s_shU : forall E a k, U E k + U E a / 8 < 2 ^ 64 ->
U E (SAlu ALU_ADD (SAlu ALU_SRL a (SLit 3)) k) = U E k + U E a / 8.
Proof.
intros E a k Hlt. rewrite !U_SAlu, U_SLit. cbn [zalu_raw].
rewrite (zcanon_id 3) by (unfold M64; lia). change (Z.land 3 63) with 3.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
pose proof (U_range E a) as Ha. pose proof (U_range E k) as Hk. unfold M64 in *.
assert (0 <= U E a / 8) by (apply Z.div_pos; lia).
rewrite (zcanon_id (U E a / 8)) by (unfold M64; lia).
rewrite Z.add_comm. apply zcanon_id. unfold M64. lia.
Qed.
Lemma pab_s_den : forall E v z, U E v = z -> sv_denot E v = Z_to_bv 64 z.
Proof. intros E v z H. rewrite denot_lit_U, H. reflexivity. Qed.
Lemma pab_s_Uoff : forall E n x c, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> 0 <= x + c < 2 ^ 64 ->
U E (SOff n c) = x + c.
Proof. intros E n x c H Hx Hc. rewrite U_SOff, H, unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia. Qed.
Lemma pab_s_doff : forall E n x c, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> sv_denot E (SOff n c) = Z_to_bv 64 (x + c).
Proof. intros E n x c H Hx. cbn [sv_denot]. rewrite H, unsigned_lit_small by lia. reflexivity. Qed.
(* x / 8 as an atom lia can use *)
Lemma pab_s_div8 : forall x, 0 <= x -> 0 <= x / 8 /\ 8 * (x / 8) <= x /\ x < 8 * (x / 8) + 8.
Proof.
intros x Hx. pose proof (Z.div_mod x 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as M.
split; [apply Z.div_pos; lia | lia].
Qed.
(* the entry registers: sr_atoms with s4, s9, s2 and t4 as K, 1, cur and nlv *)
Lemma pab_s_regs_ok : forall regs l cur nlv,
getr regs 20 = w64 SHADOW_OFF -> getr regs 25 = w64 1 -> getr regs 18 = w64 cur -> 0 <= cur < 2 ^ 64 ->
ew (Ereg regs (pab_extra l)) 34 = Z_to_bv 64 cur ->
sv_denot (Ereg regs (pab_extra l)) nlv = getr regs 29 ->
regs_ok (Ereg regs (pab_extra l)) (pab_s_sr nlv) regs.
Proof.
intros regs l cur nlv H20 H25 H18 Hcur E34 H29. set (E := Ereg regs (pab_extra l)) in *.
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by reflexivity.
unfold pab_s_sr. apply pab_s_override; [apply pab_s_override; [apply pab_s_override; [apply pab_s_override;
  [apply regs_ok_Ereg | | ] | | ] | | ] | | ].
- intros Hz. apply (f_equal (@bv_unsigned 5)) in Hz. vm_compute in Hz. discriminate Hz.
- rewrite H20. unfold w64. rewrite (pab_s_doff E 32 SHADOW_OFF 0 E32) by (unfold SHADOW_OFF; lia).
  rewrite Z.add_0_r. reflexivity.
- intros Hz. apply (f_equal (@bv_unsigned 5)) in Hz. vm_compute in Hz. discriminate Hz.
- rewrite H25. reflexivity.
- intros Hz. apply (f_equal (@bv_unsigned 5)) in Hz. vm_compute in Hz. discriminate Hz.
- rewrite H18. unfold w64. rewrite (pab_s_doff E 34 cur 0 E34) by lia. rewrite Z.add_0_r. reflexivity.
- intros Hz. apply (f_equal (@bv_unsigned 5)) in Hz. vm_compute in Hz. discriminate Hz.
- exact H29.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* every register outside clob keeps its entry value: its symbolic value is still the entry one *)
Lemma pab_s_kept : forall E ss ms sr0 regs0 (H : word -> bool) (clob : list (bv 5)),
st_ok rsegs E ss (restrict H ms) -> regs_ok E sr0 regs0 ->
forallb (fun r : bv 5 => existsb (fun c => bv_eqb c r) clob || sv_eqb (sr_get (ss_regs ss) r) (sr_get sr0 r)) nz_regs = true ->
forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob -> getr (ms_regs ms) r = getr regs0 r.
Proof.
intros E ss ms sr0 regs0 H clob HS HR Hck r Hr0 Hn.
pose proof (proj1 (forallb_forall _ _) Hck r (in_nz_regs r Hr0)) as Hq. cbn beta in Hq.
apply orb_prop in Hq as [Hq|Hq].
- exfalso. apply existsb_exists in Hq as (c & Hc & Hb). apply bv_eqb_eq in Hb. subst c. exact (Hn Hc).
- apply sv_eqb_eq in Hq.
  rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), Hq. symmetry. exact (HR r).
Qed.
End b.

(* ---- the walk's plumbing ---- *)
(* the leaf: rtsb_post's first eight clauses (RtPgPropBKit's pab_leaf, with the registers kept against the entry's
   symbolic registers HR0, which override s2, s4, s9 and t4); the relation is left *)
Ltac pab_s_leaf HR0 :=
lazymatch goal with
| HS : st_ok _ ?E _ (restrict (w_H ?W) ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyc ?Sc _ _ _ _,
  KE : forall a, _ -> ~ _ -> aview _ _ _ a = _ |- _ =>
apply SRr_ret;
red; exists lyc, Sc, (ms_regs ms), (ms_mem ms); eexists;
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|];
split; [exact HJ|];
split; [eapply (pab_s_kept _ _ ms _ _ (w_H W) _ HS HR0); vm_compute; reflexivity|];
split; [reflexivity|];
split; [apply Permutation_refl|];
split; [let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio|];
split; [apply mo_le_refl; assumption|];
split; [intros a Ha Hz; exact (KE a Ha Hz)|]
end.
(* the relation at the end, nl > 0: a1 = b, s10 = cur + 1, t4 = nl - 1 *)
Ltac pab_s_rel1 E33 E34 E36 :=
cbv beta;
pab_reg (11%bv : bv 5); pab_reg (26%bv : bv 5); pab_reg (29%bv : bv 5);
refine (conj _ (conj _ _));
[ unfold w64; rewrite (pab_s_doff _ 36 _ 0 E36) by lia; rewrite Z.add_0_r; reflexivity
| unfold w64; rewrite (pab_s_doff _ 34 _ 1 E34) by lia; reflexivity
| unfold w64; rewrite (pab_s_doff _ 33 _ (-1) E33) by lia; reflexivity ].
(* the relation at the end, nl = 0: a1 = 0, s10 = cur, t4 = 0 (not written) *)
Ltac pab_s_rel0 E34 :=
cbv beta;
pab_reg (11%bv : bv 5); pab_reg (26%bv : bv 5); pab_reg (29%bv : bv 5);
refine (conj _ (conj _ _));
[ reflexivity
| unfold w64; rewrite (pab_s_doff _ 34 _ 0 E34) by lia; rewrite Z.add_0_r; reflexivity
| reflexivity ].
(* 0x80ff0 beqz a0 (the shape-7 flag f): taken -> SELK 0x810a4, else SEL7 0x80ff4; run to the target, leaf; the
   relation is left in both goals *)
Ltac pab_s_fin E35 HR0 :=
lazymatch type of E35 with ew _ 35 = Z_to_bv 64 ?fv =>
let Hc7 := fresh "Hc7" in
pab_branch Hc7; rewrite branch_eq_U, (pab_s_Uoff _ 35 _ 0 E35), U_SLit, (zcanon_id 0) in Hc7 by (unfold M64; lia);
rewrite Z.add_0_r in Hc7;
first [ apply (proj1 (Z.eqb_eq _ _)) in Hc7 | apply (proj1 (Z.eqb_neq _ _)) in Hc7 ];
[ replace (if fv =? 0 then PAB_SELK else PAB_SEL7) with PAB_SELK by (destruct (Z.eqb_spec fv 0); [reflexivity | lia]);
  pab_run PAB_SELK; pab_keep pab_kwr_ro; pab_s_leaf HR0
| replace (if fv =? 0 then PAB_SELK else PAB_SEL7) with PAB_SEL7 by (destruct (Z.eqb_spec fv 0); [lia | reflexivity]);
  pab_run PAB_SEL7; pab_keep pab_kwr_ro; pab_s_leaf HR0 ]
end.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.
Local Abbreviation pab_post := (rtsb_post B MT).

(* the goal of the block, for both entry states *)
Definition pab_s_goal STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (f nl cur b : Z) : Prop :=
SRr rsegs W (cfg_at rsegs PAB_N regs memc mdc)
(pab_post STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc (if f =? 0 then PAB_SELK else PAB_SEL7)
 [10; 11; 26; 29]%bv (fun _ => False)
 (fun W2 regs2 mem2 =>
   getr regs2 11 = w64 (if nl =? 0 then 0 else b) /\
   getr regs2 26 = w64 (if nl =? 0 then cur else cur + 1) /\
   getr regs2 29 = w64 (if nl =? 0 then 0 else nl - 1))).

(* nl > 0: the byte at the cursor is read *)
Lemma pab_s_sel1 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (R f nl cur b : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 9 = w64 R -> getr regs 20 = w64 SHADOW_OFF -> getr regs 25 = w64 1 ->
getr regs 18 = w64 cur -> getr regs 29 = w64 nl ->
2 ^ 46 <= R -> R + 0x220 <= 2 ^ 47 -> R mod 16 = 0 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x110) 8 f -> 0 <= f <= 1 ->
0 < nl -> 0 < cur -> cur + nl <= 2 ^ 63 ->
val_mem rsegs (mrestrict (w_H W) memc) cur 1 b -> 0 <= b < 256 ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF cur 1 ->
amem_range cur 1 -> ~ (R + 0x110 <= cur < R + 0x118) ->
pab_s_goal STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs f nl cur b.
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R f nl cur b
  HJ H9 H20 H25 H18 H29 HRlo HRhi HR16 Vf Hf Hnl Hcur0 Hcurn Vb Hb HRAc Hamr HnR.
unfold pab_s_goal.
pose proof rtsb_wx as Hwx. pose proof rtsb_segs_low as Hsegs.
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr.
destruct (rtmb_ra_cell _ _ _ HRAc) as (s & Hs & Hsok).
destruct (rtmb_aview_val1 rsegs _ _ _ _ Hs) as (_ & Hs256).
assert (Hs8 : 0 <= s < 8) by (destruct Hsok as [-> | [_ Hs8]]; lia).
set (sa := shadow_of_addr SHADOW_OFF cur) in Hs.
assert (Hsa : sa = 0x7fff8000 + cur / 8) by reflexivity.
pose proof (pab_s_div8 cur ltac:(lia)) as Hcur8.
set (E := Ereg regs (pab_extra [nl; cur; f; b; sa; s])).
assert (E9 : bv_unsigned (ew E 9) = R) by (unfold E; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), H9; unfold w64; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by reflexivity.
assert (E33 : ew E 33 = Z_to_bv 64 nl) by reflexivity.
assert (E34 : ew E 34 = Z_to_bv 64 cur) by reflexivity.
assert (E35 : ew E 35 = Z_to_bv 64 f) by reflexivity.
assert (E36 : ew E 36 = Z_to_bv 64 b) by reflexivity.
assert (E37 : ew E 37 = Z_to_bv 64 sa) by reflexivity.
assert (E38 : ew E 38 = Z_to_bv 64 s) by reflexivity.
assert (U32 : U E (SOff 32 0) = SHADOW_OFF) by (apply (pab_s_Uoff E 32 SHADOW_OFF 0 E32); unfold SHADOW_OFF; lia).
(* the entry registers *)
assert (D29 : sv_denot E (SOff 33 0) = getr regs 29).
{ rewrite H29. unfold w64. rewrite (pab_s_doff E 33 nl 0 E33) by lia. rewrite Z.add_0_r. reflexivity. }
assert (HR0 : regs_ok E (pab_s_sr (SOff 33 0)) regs)
  by (exact (pab_s_regs_ok regs _ cur _ H20 H25 H18 ltac:(lia) E34 D29)).
(* the entry state *)
assert (HS : st_ok rsegs E ss_s1 (restrict (w_H W) (mkst regs (Z_to_bv 64 PAB_N) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs); fold E.
  - exact HR0.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil.
    + apply (rtmb_ro_region rsegs E _ _ 9 R); [exact E9 | lia | lia |].
      constructor; [|constructor]. eapply pab_chunk8; [apply pab_s_doff; [exact E35 | lia] | lia | rewrite Z.add_0_r; exact Vf].
    + apply (rtmb_cell_region rsegs E _ _ 34 cur b); [rewrite E34; apply unsigned_lit_small; lia | | | lia | lia].
      * apply (rtmb_val1_aview rsegs); assumption.
      * rewrite (pab_s_doff E 36 b 0 E36) by lia. rewrite Z.add_0_r. reflexivity.
    + apply (rtmb_cell_region rsegs E _ _ 37 sa s); [rewrite E37; apply unsigned_lit_small; lia | exact Hs | | lia | lia].
      rewrite (pab_s_doff E 38 s 0 E38) by lia. rewrite Z.add_0_r. reflexivity.
  - unfold pab_s_r110, pab_s_rin, pab_s_rcell.
    cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite !E9, E34, E37, !unsigned_lit_small by lia.
    repeat split; lia.
  - split; [|split; [exact I|]].
    + cbn [pab_s_G1 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E9, E32, E33, E34, E35, E36, E38, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
      change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. unfold SHADOW_OFF.
      repeat split; lia.
    + cbn [pab_s_G1 f_alias alias_ok]. split; [|exact I].
      assert (U34 : U E (SOff 34 0) = cur) by (rewrite (pab_s_Uoff E 34 cur 0 E34) by lia; apply Z.add_0_r).
      assert (Hlt : U E (SOff 32 0) + U E (SOff 34 0) / 8 < 2 ^ 64) by (rewrite U32, U34; unfold SHADOW_OFF; lia).
      rewrite (pab_s_den E _ sa); [rewrite (pab_s_den E (SOff 37 0) sa); [reflexivity |] |].
      * rewrite (pab_s_Uoff E 37 sa 0 E37) by lia. apply Z.add_0_r.
      * rewrite (pab_s_shU E _ _ Hlt), U32, U34. exact (eq_sym Hsa). }
clearbody E.
assert (SHOK : sh_ok rsegs PABBx [] E (mrestrict (w_H W) memc)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a)
  by (intros; reflexivity).
assert (Hnz : (nl =? 0) = false) by (apply Z.eqb_neq; lia). rewrite !Hnz.
unfold cfg_at. change (w64 PAB_N) with (Z_to_bv 64 PAB_N).
(* 0x80fb4 .. 0x80fcc (the pointer test 0x80fbc decided taken), stop at the beqz 0x80fd0 on the cursor's shadow
   byte s *)
pab_runb. pab_keep pab_kwr_ro.
pab_branch Hc; rewrite branch_eq_U, (pab_s_Uoff _ 38 _ 0 E38), U_SLit, (zcanon_id 0) in Hc by (unfold M64; lia);
rewrite Z.add_0_r in Hc;
first [apply (proj1 (Z.eqb_eq _ _)) in Hc | apply (proj1 (Z.eqb_neq _ _)) in Hc].
- (* s = 0: 0x80fd8 .. 0x80fec, stop at the beqz 0x80ff0 *)
  pab_runb. pab_keep pab_kwr_ro.
  pab_s_fin E35 HR0; pab_s_rel1 E33 E34 E36.
- (* s <> 0: 0x80fd4 j 0x82594, andi a1,s2,7; stop at the blt 0x82598 *)
  pab_runb. pab_keep pab_kwr_ro.
  pab_branch Hg.
  + (* cur mod 8 < s: 0x825a0 j 0x80fd8 .. 0x80fec, stop at the beqz 0x80ff0 *)
    pab_runb. pab_keep pab_kwr_ro.
    pab_s_fin E35 HR0; pab_s_rel1 E33 E34 E36.
  + (* the report arm 0x8259c: cur mod 8 >= s contradicts saddr_ok *)
    exfalso.
    assert (G : sv_denot E (SAlu ALU_AND (SOff 34 0) (SLit 7)) = Z_to_bv 64 (cur mod 8)).
    { cbn [sv_denot]. rewrite E34, unsigned_lit_small, Z.add_0_r by lia. apply alu_and7. unfold M64. lia. }
    rewrite G, (pab_s_doff E 38 s 0 E38), Z.add_0_r in Hg by lia.
    cbn [branch_taken] in Hg. rewrite (rtmb_ra_slow_bv cur s Hsok Hc) in Hg. discriminate Hg.
Qed.

(* nl = 0: no input is left; a1 = 0 and s10 = the cursor *)
Lemma pab_s_sel0 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (R f cur b : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 9 = w64 R -> getr regs 20 = w64 SHADOW_OFF -> getr regs 25 = w64 1 ->
getr regs 18 = w64 cur -> getr regs 29 = w64 0 ->
2 ^ 46 <= R -> R + 0x220 <= 2 ^ 47 -> R mod 16 = 0 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x110) 8 f -> 0 <= f <= 1 ->
0 < cur -> cur <= 2 ^ 63 ->
pab_s_goal STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs f 0 cur b.
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R f cur b
  HJ H9 H20 H25 H18 H29 HRlo HRhi HR16 Vf Hf Hcur0 Hcurn.
unfold pab_s_goal. rewrite !Z.eqb_refl.
pose proof rtsb_wx as Hwx. pose proof rtsb_segs_low as Hsegs.
set (E := Ereg regs (pab_extra [0; cur; f])).
assert (E9 : bv_unsigned (ew E 9) = R) by (unfold E; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), H9; unfold w64; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by reflexivity.
assert (E34 : ew E 34 = Z_to_bv 64 cur) by reflexivity.
assert (E35 : ew E 35 = Z_to_bv 64 f) by reflexivity.
assert (D29 : sv_denot E (SLit 0) = getr regs 29) by (rewrite H29; reflexivity).
assert (HR0 : regs_ok E (pab_s_sr (SLit 0)) regs)
  by (exact (pab_s_regs_ok regs _ cur _ H20 H25 H18 ltac:(lia) E34 D29)).
(* the entry state *)
assert (HS : st_ok rsegs E ss_s0 (restrict (w_H W) (mkst regs (Z_to_bv 64 PAB_N) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs); fold E.
  - exact HR0.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil.
    apply (rtmb_ro_region rsegs E _ _ 9 R); [exact E9 | lia | lia |].
    constructor; [|constructor]. eapply pab_chunk8; [apply pab_s_doff; [exact E35 | lia] | lia | rewrite Z.add_0_r; exact Vf].
  - unfold pab_s_r110. cbn [pairwise_disjoint all_disjoint]. tauto.
  - split; [|split; exact I].
    cbn [pab_s_G0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E9, E32, E34, E35, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. unfold SHADOW_OFF.
    repeat split; lia. }
clearbody E.
assert (SHOK : sh_ok rsegs PABBx [] E (mrestrict (w_H W) memc)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a)
  by (intros; reflexivity).
unfold cfg_at. change (w64 PAB_N) with (Z_to_bv 64 PAB_N).
(* 0x80fb4 .. 0x80fec (the beqz 0x80fb4 taken: 0x80fe4 a1 = 0, 0x80fe8 s10 = s2), stop at the beqz 0x80ff0 *)
pab_runb. pab_keep pab_kwr_ro.
pab_s_fin E35 HR0; pab_s_rel0 E34.
Qed.

(* ---- the sel block 0x80fb4 -> SEL7 0x80ff4 (the shape-7 flag f <> 0) / SELK 0x810a4 (f = 0) ---- *)
Lemma pab_sel : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (R f nl cur b : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 9 = w64 R -> getr regs 20 = w64 SHADOW_OFF -> getr regs 25 = w64 1 ->
getr regs 18 = w64 cur -> getr regs 29 = w64 nl ->
2 ^ 46 <= R -> R + 0x220 <= 2 ^ 47 -> R mod 16 = 0 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x110) 8 f -> 0 <= f <= 1 ->
0 <= nl -> 0 < cur -> cur + nl <= 2 ^ 63 ->
(0 < nl -> val_mem rsegs (mrestrict (w_H W) memc) cur 1 b /\ 0 <= b < 256 /\
  range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF cur 1 /\
  amem_range cur 1 /\ ~ (R + 0x110 <= cur < R + 0x118)) ->
SRr rsegs W (cfg_at rsegs PAB_N regs memc mdc)
(pab_post STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc (if f =? 0 then PAB_SELK else PAB_SEL7)
 [10; 11; 26; 29]%bv (fun _ => False)
 (fun W2 regs2 mem2 =>
   getr regs2 11 = w64 (if nl =? 0 then 0 else b) /\
   getr regs2 26 = w64 (if nl =? 0 then cur else cur + 1) /\
   getr regs2 29 = w64 (if nl =? 0 then 0 else nl - 1))).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R f nl cur b
  HJ H9 H20 H25 H18 H29 HRlo HRhi HR16 Vf Hf Hnl Hcur0 Hcurn Hin.
destruct (Z.eq_dec nl 0) as [-> | Hnz].
- exact (pab_s_sel0 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R f cur b
    HJ H9 H20 H25 H18 H29 HRlo HRhi HR16 Vf Hf Hcur0 ltac:(lia)).
- destruct (Hin ltac:(lia)) as (Vb & Hb & HRAc & Hamr & HnR).
  exact (pab_s_sel1 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R f nl cur b
    HJ H9 H20 H25 H18 H29 HRlo HRhi HR16 Vf Hf ltac:(lia) Hcur0 Hcurn Vb Hb HRAc Hamr HnR).
Qed.

End d.
End c.

(* ================================ the selector piece: N -> SEL7 / SELK ================================ *)
Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.

Lemma pab_piece_sel : rsb_piece_W4_sel_stmt rsegs B MT.
Proof using MTL LAWS.
unfold rsb_piece_W4_sel_stmt. intros cx POST rest i Hst HS7 HSK.
destruct Hst as (Hpre & Hfsh0 & Hc1 & Hlen0 & Hin0).
pose proof (pab_R_bounds B cx Hpre) as (RB1 & RB2 & RB3 & RB4 & RB5 & RB6 & RB7).
unfold rsb_from_N. intros ly2 S2 W2 regs2 mem2 md2 sh np ps r Hlen Hcut.
destruct Hcut as (Hcore & Hat & Hfsh & Hpp & Hin & Hsuf & Hwf & Hsh & Hnp & Hps & Hnp3 & Hloop).
pose proof Hcore as (HJ & _).
pose proof Hin as (Hleft & Hgarr & Hra & Hhull & Hamr & Hsrc0 & Hsrcn & Hapart).
pose proof Hsuf as (j & Hj & Er).
assert (Lr : length r = (length rest - j)%nat) by (rewrite Er; apply length_skipn).
assert (Hcur : rsb_cur rsegs cx rest r = q_src (x_e cx) + Z.of_nat j) by (unfold rsb_cur; rewrite Lr; lia).
assert (Hf01 : 0 <= Z.b2z (sh =? 7) <= 1) by (destruct (sh =? 7); cbn; lia).
unfold rsb_at_cx in Hat.
pab_take Hat (LReg 9) (q_R (x_e cx)) A9. pab_take Hat (LReg 20) SHADOW_OFF A20.
pab_take Hat (LReg 25) 1 A25. pab_take Hat (LReg 18) (rsb_cur rsegs cx rest r) A18.
pab_take Hat (LReg 29) (Z.of_nat (length r)) A29.
pab_take Hat (LCell XR 0x110) (Z.b2z (sh =? 7)) A110.
rewrite Z.mod_small in A110 by lia.
(* the byte at the cursor, its shadow and where it lies, when input is left *)
assert (Hinp : 0 < Z.of_nat (length r) ->
  val_mem rsegs (mrestrict (w_H W2) mem2) (rsb_cur rsegs cx rest r) 1 (fst (fuzz_u8 r)) /\ 0 <= fst (fuzz_u8 r) < 256 /\
  range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF (rsb_cur rsegs cx rest r) 1 /\
  amem_range (rsb_cur rsegs cx rest r) 1 /\
  ~ (q_R (x_e cx) + 0x110 <= rsb_cur rsegs cx rest r < q_R (x_e cx) + 0x118)).
{ intros Hnz. rewrite Hcur. destruct r as [|bb r''] eqn:Er'; [cbn in Hnz; lia|]. cbn [fuzz_u8 fst].
  destruct (pab_nth_skipn rest j bb r'' (eq_sym Er)) as (Hjl & Hnth).
  destruct (pab_input_now B MT LAWS cx rest ly2 S2 W2 regs2 mem2 md2 (Z.of_nat j) Hpre Hfsh0 Hin Hcore Hfsh ltac:(lia))
    as (V & RA).
  assert (Hb : nth (Z.to_nat (Z.of_nat j)) (rsb_u8s rest) 0 = bv_unsigned bb).
  { rewrite Nat2Z.id. unfold rsb_u8s. rewrite (nth_indep _ _ ((fun x : byte => bv_unsigned x) (Z_to_bv 8 0))) by (rewrite length_map; lia).
    rewrite map_nth, Hnth. reflexivity. }
  rewrite Hb in V. destruct (Hapart (q_src (x_e cx) + Z.of_nat j) ltac:(lia)) as (N1 & N2 & N3).
  split; [exact V|]. split; [pose proof (bv_unsigned_in_range 8 bb) as X; change (bv_modulus 8) with 256 in X; lia|].
  split; [exact RA|]. split; [unfold amem_range in *; lia|].
  intros X. apply N2. unfold rt_inw. cbn [hi_w1 rate_himg_B].
  apply Exists_cons_tl. apply Exists_cons_tl. apply Exists_cons_tl. apply Exists_cons_hd. cbn [fst snd rt_xv]. lia. }
eapply SRr_bind.
{ refine (pab_sel B MT MTL LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 (q_R (x_e cx)) (Z.b2z (sh =? 7))
    (Z.of_nat (length r)) (rsb_cur rsegs cx rest r) (fst (fuzz_u8 r))
    HJ A9 A20 A25 A18 A29 RB4 ltac:(lia) RB3 A110 Hf01 ltac:(lia) _ _ Hinp); rewrite Hcur; lia. }
intros W3 c3 Hle (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & Hkeep & Hfr & Hperm & Hio & Hmo & Hmem & HR).
destruct HR as (R11 & R26 & R29).
pose proof (pab_mem_all _ _ _ _ Hmem) as Hall.
(* the cursor after the selector byte *)
assert (Hstep : getr regs3 11 = w64 (fst (fuzz_u8 r)) /\
  getr regs3 26 = w64 (rsb_cur rsegs cx rest (snd (fuzz_u8 r))) /\
  getr regs3 29 = w64 (Z.of_nat (length (snd (fuzz_u8 r))))).
{ destruct r as [|bb r''] eqn:Er'.
  - cbn [fuzz_u8 fst snd length Z.of_nat Z.eqb] in R11, R26, R29 |- *.
    split; [exact R11|]. split; [exact R26 | exact R29].
  - cbn [fuzz_u8 fst snd length] in R11, R26, R29 |- *.
    replace (Z.of_nat (S (length r'')) =? 0) with false in R11, R26, R29 by (symmetry; apply Z.eqb_neq; lia).
    split; [exact R11|]. split.
    + replace (rsb_cur rsegs cx rest r'') with (rsb_cur rsegs cx rest (bb :: r'') + 1)
        by (unfold rsb_cur; cbn [length]; lia).
      exact R26.
    + replace (Z.of_nat (length r'')) with (Z.of_nat (S (length r'')) - 1) by lia. exact R29. }
destruct Hstep as (R11' & R26' & R29').
assert (Hcore3 : rsb_core rsegs B MT cx (rsb_E1 rsegs cx) ly3 S3 W3 regs3 mem3 md3).
{ refine (pab_core_step B MT MTL cx _ (fun _ => False) _ _ _ _ _ _ _ _ _ _ _ _ Hcore HJ3 _ Hfr Hperm Hio Hmo Hmem _).
  - pab_regs234 Hkeep.
  - intros a []. }
assert (Hfsh3 : rsb_fsh_at rsegs cx W3 mem3 rsb_P0).
{ unfold rsb_fsh_at in *. eapply rtmb_fsh_kept; [exact Hfsh|]. intros jj Hjj. apply Hall. }
assert (Hpp3 : rsb_pp_at rsegs cx W3 mem3 (pc_image (PbCut sh ps None))).
{ unfold rsb_pp_at in *. eapply (rtmb_bytes_kept rsegs); [exact Hpp|]. intros x Hx. apply Hall. }
(* every location of N but the cursor pair, kept: the block writes no memory and only a0, a1, s10, t4 *)
assert (Hat3 : rsb_at rsegs (w_H W3) mem3 regs3 (x_e cx)
  (rsb_Rc rsegs cx ++ [(LReg 25, 1); (LReg 5, Z.of_nat (length ps)); (LReg 22, rsb_seen ps)]
   ++ rsb_Kc rsegs cx sh np ++ rsb_Hc rsegs cx)).
{ eapply pab_at_move; [pab_list; pab_from Hat|]. pab_kept Hkeep ltac:(apply Hall). }
assert (HatS : rsb_at rsegs (w_H W3) mem3 regs3 (x_e cx) (rsb_L_SEL rsegs cx sh np ps rest (snd (fuzz_u8 r)))).
{ pab_list; first [pab_from Hat3 | idtac].
  - cbn [rt_at]. exact R26'.
  - cbn [rt_at]. exact R29'. }
assert (Hbase : forall sh', sh' = sh -> rsb_prop_base rsegs B MT cx sh' np ps rest (snd (fuzz_u8 r)) ly3 S3 W3 regs3 mem3 md3).
{ intros sh' ->. split; [exact Hcore3|]. split; [exact Hfsh3|]. split; [exact Hin|].
  split; [apply pab_suffix_step; exact Hsuf|]. split; [exact Hwf|]. split; [exact Hlen0|].
  split; [rewrite <- Hloop; reflexivity|]. split; [exact Hsh|]. split; [exact Hnp|]. split; [exact Hps | exact Hnp3]. }
destruct (Z.eqb_spec sh 7) as [E7|E7].
- replace (if Z.b2z (sh =? 7) =? 0 then PAB_SELK else PAB_SEL7) with PAB_SEL7 by (rewrite E7; reflexivity).
  change (mkCfg (mkst regs3 (w64 PAB_SEL7) mem3 (seg_rom rsegs)) md3) with (cfg_at rsegs RSB_SEL7 regs3 mem3 md3).
  apply (HS7 ly3 S3 W3 regs3 mem3 md3 np ps (snd (fuzz_u8 r)) Hlen).
  rewrite E7 in HatS, Hpp3.
  split; [exact (Hbase 7 (eq_sym E7))|]. split; [exact HatS|]. split; [exact Hpp3|].
  rewrite <- E7, <- Hloop. reflexivity.
- replace (if Z.b2z (sh =? 7) =? 0 then PAB_SELK else PAB_SEL7) with PAB_SELK
    by (apply Z.eqb_neq in E7; rewrite E7; reflexivity).
  change (mkCfg (mkst regs3 (w64 PAB_SELK) mem3 (seg_rom rsegs)) md3) with (cfg_at rsegs RSB_SELK regs3 mem3 md3).
  apply (HSK ly3 S3 W3 regs3 mem3 md3 sh np (fst (fuzz_u8 r)) ps (snd (fuzz_u8 r)) Hlen).
  split; [exact (Hbase sh eq_refl)|]. split.
  + unfold rsb_at_cx. apply pab_at_app; [exact HatS|].
    unfold rsb_at. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    * pab_from Hat3.
    * cbn [rt_at]. exact R11'.
  + split; [exact Hpp3|]. split; [exact E7|].
    split; [destruct r as [|bb r'']; cbn [fuzz_u8 fst]; [lia | pose proof (bv_unsigned_in_range 8 bb) as X; change (bv_modulus 8) with 256 in X; lia]|].
    rewrite <- Hloop. cbn [snd]. destruct (fuzz_u8 r); reflexivity.
Qed.
End p.

Print Assumptions pab_piece_sel.
