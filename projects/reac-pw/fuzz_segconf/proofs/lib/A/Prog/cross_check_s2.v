(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment 3 of the walk of chain_words (0x8dfd4) on the ASan build of
   plugin-hostd/fuzz_command (interface chain_words_d.v): one pass of the member loop, from the loop head KL
   (0x8e234) at pass j: the inline load8 check of &tok[2 + j] (0x8e234-0x8e238), the call of number at 0x8e244
   (through cl_callS_wide, PaNoChain.v) that writes ids[j] in this walk's class-3 side-stack frame, the refusal edge
   `beqz a0` at 0x8e248 (to KR, 0x8e278), the advance 0x8e24c-0x8e25c and `bnez s11` at 0x8e260, which re-enters
   KL at pass j + 1 or falls through to KD (0x8e264). The symbolic machinery (the cut-point seed, the call, the
   re-seat after it) is the one of the sibling segment chain_words_s2.v (KC -> KL 0), which walks the same inline
   check and the same call once, for the first word; its lemmas are copied here with the prefix cw3_ and generalised
   over the pass index. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/chain_words_s3.v, with its module paths and module names changed; 1876 of its 1987 lines of code are new or changed and 762 lines of the source are left out. *)
(* Segment S2 of the walk of cross_check (image A fuzz_segconf.asan 0x89218), interface cross_check_d.v:
   ONE PASS of the segment loop, from its head CC_LOOP (0x892ac, pass i) to the head again (pass i + 1) or to
   the epilogue CC_EPI (0x89460).

   The pass (the unit's internal record, commit dfb49d6ad789, path records/segp/plans/
   PLAN-small-asan.md sections 4.2, 4.4; the same record, commit dfb49d6ad789, path records/segp/
   dis/cross_check.fuzz_segconf.asan.s lines 39-147):
     0x892ac-0x892c8  s4 = &seg[i], s5 = &s->role_set, check 2 (load4 role_set), `beqz` role_set
     0x892cc-0x89318  role_set != 0: check 3 (load4 role), check 4 (load4 model_set), the two branches on
                      model_set and on role = BOX, and the recompute of s5 on the way to the model-drop arm
     0x8931c-0x89334  role_set = 0: s5 = &model_set, check 5 (load4 model_set), `beqz`
     0x89338-0x8937c  the model-drop arm: refuse(c, 0, F_xmodel, s->name, s->model) at 0x89350, then check 6
                      and `sw zero` model_set, check 7 and `sb zero` model[0]
     0x89380-0x893b4  the box arm: refuse(c, 0, F_xbox, s->name) at 0x8939c, then check 8 and `sw zero`
                      role_set, check 9 and `sw zero` role
     0x893b8-0x893d0  the latch: check 10 (load4 c->n), `lw` n, i++, s9 += 356, `blt` back or `j` to CC_EPI
   The check stubs 0x893d4-0x8945c and the error calls 0x894b0-0x894e8 are unreachable: every one of the ten
   inline checks reads a byte of the live heap block at c, whose shadow the allocator record pins
   (cross_check_r.v cc_block_addr over YCbq.v range_addressable_of_block), so the token executor decides each
   check with a zero shadow byte and never enters a stub.

   SHAPE. The pass is cut again at the latch (CC_LATCH 0x893b8) and after each of the two refuse calls
   (CC_RET1 0x89354, CC_RET2 0x893a0), so the walk is four token runs, none longer than 30 instructions:
     cc2_latch  CC_LATCH -> the head at i + 1 (INV_LOOP) or CC_EPI (INV_EPI)
     cc2_arm1   CC_RET1  -> CC_LATCH, through check 6, `sw zero` model_set, check 7, `sb zero` model[0]
     cc2_arm2   CC_RET2  -> CC_LATCH, through check 8, `sw zero` role_set, check 9, `sw zero` role
     cc_s2      CC_LOOP  -> CC_LATCH (the three keep paths) or a refuse call (the two arms)
   A refuse call returns at some FP state fx1 with fxrel fx fx1 (refuse's post is apost_baseF), so cc2_latch,
   cc2_arm1 and cc2_arm2 are lemmas of a section CLOSED before cc_s2 and are applied there with (fx := fx1);
   PaFx.srr_after_callF lifts their apost_baseF at fx1 to the pass's apost_baseF at fx, and PaFx.fxrel_frm0
   carries the rounding mode to the next pass's premise.

   THE SEED. The executor cannot build &seg[i] by itself: `add s4,s0,s9` adds two atoms (c and 356 i) and
   `mul a0,s10,a0` multiplies an atom by 356, and neither is an `SOff`, so every later load or store through
   s4, s5 or s6 would stop the run. The cut seeds therefore carry a fresh atom 32 for c + 356 i and the two
   aliases that send both forms to it (numberE.v:37 aliases the realigned sp the same way). The other atoms
   are the registers themselves (0..31 through Ereg) plus 33 = F_xbox (the spill at sp + 0x10), 34 = s->role,
   35 = s->role_set, 36 = s->model_set, 37 = c->n. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From Stdlib Require Import FunctionalExtensionality.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI09 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q YN01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaLibF PaLibG PaLibH
PaDenot PaSB PaCall PaCallRun PaNoChain PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegObj SegGlob SegPgBase SegBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import refuse_c cross_check_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import cross_check_d cross_check_f cross_check_r.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================= 1. the cut points inside the pass ======================= *)
Definition CC_LATCH : Z := AF_cross_check + 0x1a0.  (* 0x893b8, the latch *)

(* ======================= 2. pure helpers over readers and states ======================= *)
(* a reader fact about a field is a val_mem fact about the machine's memory (chain_words_s3.v:46) *)
Lemma cc2_val_mem : forall segs H mem a n v,
sa_val (aview segs H mem) a n v -> val_mem segs (mrestrict H mem) a n v.
Proof.
intros segs H mem a n v Hv k Hk. pose proof (Hv k Hk) as Hb. unfold aview in Hb.
unfold val_mem.
destruct (mbyte segs (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:Eb;
  cbn [option_map] in Hb; [|discriminate Hb].
injection Hb as Hb. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned, Hb. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
cbv [YO0f.le_byte YG0f.le_byte]. symmetry. apply Z.mod_mod. lia.
Qed.
(* a run that wrote nothing leaves every byte of the reader where it was (chain_words_s3.v:203, :209) *)
Lemma cc2_frame_ro : forall E rs (m m' : word -> option byte),
Forall (fun r => YP09.r_whi r <= YP09.r_wlo r) rs -> frame_of E rs m m' -> forall x, m' x = m x.
Proof.
intros E rs m m' Hro H x. apply H. intros (r & Hr & Ha).
pose proof (proj1 (Forall_forall _ _) Hro r Hr) as Hw. cbn beta in Hw. lia.
Qed.
Lemma cc2_aview_ext : forall segs H (m m' : word -> option byte), (forall x, m' x = m x) ->
forall a, aview segs H m' a = aview segs H m a.
Proof. intros segs H m m' He a. unfold aview, mbyte, mrestrict. cbv beta. rewrite (He (Z_to_bv 64 a)). reflexivity. Qed.
Lemma cc2_pres : forall regs regs' (r : bv 5), aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) ->
getr regs' r = getr regs r.
Proof. intros regs regs' r H Hr. pose proof (H _ Hr) as E. rewrite Z_to_bv_bv_unsigned in E. exact E. Qed.
Lemma cc2_afact : forall E m v lo hi al,
ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> lo <= v <= hi -> v mod 2 ^ al = 0 -> 0 <= al <= 64 ->
afact_ok E m (mkAF lo hi al).
Proof.
intros E m v lo hi al Hm Hv Hlh Hal Hal2. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Hm, unsigned_lit_small by exact Hv. split; [exact Hlh | split; [exact Hal | exact Hal2]].
Qed.
(* the shadow byte of an 8-aligned pointer kept in a register, as the executor writes it *)
Lemma cc2_shadow_denot : forall E n m x, ew E n = Z_to_bv 64 x -> ew E m = Z_to_bv 64 SB -> 0 <= x < 2 ^ 64 ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n 0) (SLit 3)) (SOff m 0)) = Z_to_bv 64 (SB + x / 8).
Proof.
intros E n m x Hn Hm Hx. cbn [sv_denot]. rewrite Hn, Hm, !unsigned_lit_small by (unfold SB; lia). rewrite !Z.add_0_r.
rewrite !zalu64_sound. unfold zalu64. rewrite Z_to_bv64_canon. cbn [zalu_raw].
rewrite (zcanon_id x) by (unfold M64; lia). change (zcanon 3) with 3. change (Z.land 3 63) with 3.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
assert (Hx8 : 0 <= x / 8 < M64) by (unfold M64; split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
rewrite !(zcanon_id (x / 8) Hx8).
rewrite !(zcanon_id SB) by (unfold SB, M64; lia). f_equal. lia.
Qed.
(* the same for a pointer the code forms as an offset of the entry *)
Lemma cc2_shadow_denot_off : forall E n m x off, ew E n = Z_to_bv 64 x -> ew E m = Z_to_bv 64 SB ->
0 <= x < 2 ^ 64 -> 0 <= x + off < 2 ^ 64 ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n off) (SLit 3)) (SOff m 0))
  = Z_to_bv 64 (SB + (x + off) / 8).
Proof.
intros E n m x off Hn Hm Hx Hxo. cbn [sv_denot]. rewrite Hn, Hm, !unsigned_lit_small by (unfold SB; lia).
rewrite !Z.add_0_r.
rewrite !zalu64_sound. unfold zalu64. rewrite Z_to_bv64_canon. cbn [zalu_raw].
rewrite (zcanon_id (x + off)) by (unfold M64; lia). change (zcanon 3) with 3. change (Z.land 3 63) with 3.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
assert (Hx8 : 0 <= (x + off) / 8 < M64)
  by (unfold M64; split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
rewrite !(zcanon_id ((x + off) / 8) Hx8).
rewrite !(zcanon_id SB) by (unfold SB, M64; lia). f_equal. lia.
Qed.
(* a memory fact of the executor's state, read back through the reader *)
Lemma cc2_val_rd : forall segs H mem a n v,
val_mem segs (mrestrict H mem) a n v -> sa_val (aview segs H mem) a n v.
Proof.
intros segs H mem a n v Hv k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
cbv [YO0f.le_byte YG0f.le_byte]. apply Z.mod_mod. lia.
Qed.
Lemma cc2_le_byte_0 : forall (n k : nat), le_byte 0 n k = 0.
Proof.
intros n k. unfold le_byte. rewrite Zmod_0_l, Z.shiftr_0_l. apply Zmod_0_l.
Qed.
(* the four or one bytes a `sw zero` / `sb zero` left behind *)
Lemma cc2_zero_rd : forall segs H mem a n, val_mem segs (mrestrict H mem) a n 0 ->
forall k, (k < n)%nat -> aview segs H mem (a + Z.of_nat k) = Some 0.
Proof.
intros segs H mem a n Hv k Hk.
pose proof (cc2_val_rd segs H mem a n 0 Hv k Hk) as Hb.
rewrite cc2_le_byte_0 in Hb. exact Hb.
Qed.

(* reading a register of a run's end state *)
Ltac cc2_rg HS r Hr :=
lazymatch type of HS with
| st_ok_pi _ _ ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    change (sr_get (ss_regs ss) r) with e in Hr;
  cbn [ms_regs restrict mkst] in Hr
end.
(* the model the executor leaves behind *)
Ltac cc2_mdv nm :=
lazymatch goal with |- context [with_vm_backing (m_vm_lazy ?md) ?mt ?md] =>
  set (nm := with_vm_backing (m_vm_lazy md) mt md) in *; clearbody nm end.
Lemma cc2_den_off : forall E k x val, ew E k = Z_to_bv 64 val -> 0 <= val < 2 ^ 64 ->
  0 <= val + x < 2 ^ 64 -> sv_denot E (SOff k x) = Z_to_bv 64 (val + x).
Proof.
intros E k x val Hk Hv Hvx. apply bv_eq.
change (U E (SOff k x) = bv_unsigned (Z_to_bv 64 (val + x))).
rewrite (U_atom_off E k val x Hk Hv Hvx), unsigned_lit_small by lia. reflexivity.
Qed.
(* `blt` on two small non-negative values is the unsigned compare *)
Lemma cc2_branch_lt_U : forall E a b, U E a < 2 ^ 63 -> U E b < 2 ^ 63 ->
  branch_taken BC_LT (sv_denot E a) (sv_denot E b) = (U E a <? U E b).
Proof.
intros E a b Ha Hb.
pose proof (c_lts_small (sv_denot E a) (sv_denot E b) Ha Hb) as H. unfold c_lts in H.
cbn [branch_taken]. rewrite H. unfold bv_ltu, U. reflexivity.
Qed.
(* the reader facts of a cut are pointwise, so a run that wrote nothing carries each of them *)
Lemma cc2_zs_ext : forall (rd rd' : reader) p l, (forall a, rd' a = rd a) -> sa_zs rd p l -> sa_zs rd' p l.
Proof. intros rd rd' p l He H k Hk. rewrite He. exact (H k Hk). Qed.
Lemma cc2_bytes_ext : forall (rd rd' : reader) p l, (forall a, rd' a = rd a) ->
  sa_bytes rd p l -> sa_bytes rd' p l.
Proof. intros rd rd' p l He H k Hk. rewrite He. exact (H k Hk). Qed.
Lemma cc2_str_ext : forall (rd rd' : reader) p s, (forall a, rd' a = rd a) -> sa_str rd p s -> sa_str rd' p s.
Proof.
intros rd rd' p s He ((H1 & H2) & H3). split; [split|].
- exact (cc2_zs_ext rd rd' p (s ++ [0]) He H1).
- exact H2.
- intros x Hx. rewrite He. exact (H3 x Hx).
Qed.
Lemma cc2_rconf_ext : forall (rd rd' : reader) c rcs, (forall a, rd' a = rd a) ->
  sa_rconf rd c rcs -> sa_rconf rd' c rcs.
Proof.
intros rd rd' c rcs He (bs & Hb & Henc). exists bs.
split; [exact (cc2_bytes_ext rd rd' c bs He Hb) | exact Henc].
Qed.
Lemma cc2_val_ext : forall (rd rd' : reader) p n w, (forall a, rd' a = rd a) ->
  sa_val rd p n w -> sa_val rd' p n w.
Proof. intros rd rd' p n w He H k Hk. rewrite He. exact (H k Hk). Qed.
Lemma cc2_trans : forall (m1 m2 m3 : word -> option byte),
  (forall x, m1 x = m2 x) -> (forall x, m2 x = m3 x) -> forall x, m1 x = m3 x.
Proof. intros m1 m2 m3 H1 H2 x. rewrite H1. apply H2. Qed.
Lemma cc2_rdw_ext : forall (rd rd' : reader), (forall a, rd' a = rd a) ->
  forall a w, rdword rd a = Some w -> rdword rd' a = Some w.
Proof.
intros rd rd' He a w Ha. rewrite (rdword_ext rd rd' a ltac:(intros k Hk; apply He)). exact Ha.
Qed.
Lemma cc2_rdw_on : forall (rd rd' : reader) a w, (forall x, a <= x < a + 8 -> rd' x = rd x) ->
  rdword rd a = Some w -> rdword rd' a = Some w.
Proof.
intros rd rd' a w He Ha. rewrite (rdword_ext rd rd' a ltac:(intros k Hk; apply He; lia)). exact Ha.
Qed.
(* a region of a run's end state, computed BEFORE it is named: with the region left an evar, vm_compute
   falls back to cbv and reduces the whole symbolic run *)
Ltac cc2_rgn HS n RG :=
lazymatch type of HS with
| st_ok_pi _ _ ?E ?ss ?ms =>
  let r := eval vm_compute in (nth n (ss_mem ss) (YP09.mkRegion None 0 0 0 0 [])) in
  pose proof (st_ok_pi_region_nth E ss ms n r HS ltac:(vm_compute; reflexivity)) as RG;
  cbn [ms_mem restrict mkst] in RG
end.
Ltac cc2_in := solve [repeat (first [apply in_eq | apply in_cons])].
(* ======================= 3. the symbolic vocabulary of the pass ======================= *)
(* the allocator's highest ceiling (YCbq.v asan_consts): every pointer the pass holds is below it *)
Definition CC2_CEIL : Z := 140737479966720.
(* the shadow base the code adds, as the executor sees it: s3 is atom 19 *)
Definition cc2_Bx : sv := SOff 19 0.
(* the shadow knowledge: the whole seg entry at atom 32, and the four bytes of c->n at atom 9. Every one of
   the ten inline checks of a pass reads a shadow byte of one of these two ranges, so each is `covered`. *)
Definition cc2_SH : list shent := [mkSHE 32 0 356; mkSHE 9 0 8].
(* s11 at every cut: the shadow byte address of &c->n *)
Definition cc2_sh11 : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 9 0) (SLit 3)) (SOff 19 0).
Definition cc2_atoms : list (nat * afact) :=
[ (8%nat, mkAF 4096 CC2_CEIL 4); (9%nat, mkAF 4096 CC2_CEIL 3); (19%nat, mkAF SB SB 0);
  (25%nat, mkAF 0 11392 2); (26%nat, mkAF 0 31 0); (32%nat, mkAF 4096 CC2_CEIL 2);
  (34%nat, mkAF 0 (2 ^ 31 - 1) 0); (35%nat, mkAF 0 1 0); (36%nat, mkAF 0 1 0); (37%nat, mkAF 0 32 0) ].
(* `add s4,s0,s9` at 0x892ac and `mul a0,s10,0x164; add a0,s0,a0` at 0x8930c-0x89310 both give &seg[i] *)
Definition cc2_alias : list (sv * sv) :=
[ (SAlu ALU_ADD (SOff 8 0) (SOff 25 0), SOff 32 0);
  (SAlu ALU_ADD (SOff 8 0) (SMd M_MUL (SOff 26 0) (SLit 356)), SOff 32 0) ].
Definition cc2_facts : facts := mkFacts cc2_atoms [] cc2_alias.
(* the three regions of the head run: the entry's fields, c->n and the F_xbox spill, all read-only (the run
   from the head writes nothing: the two stores of each arm are after its refuse call) *)
Definition cc2_segR : YP09.region :=
YP09.mkRegion (Some 32%nat) 16 64 16 16
[YP09.mkChunk 16 (CVal 4 (SOff 34 0)); YP09.mkChunk 20 (CVal 4 (SOff 35 0));
 YP09.mkChunk 60 (CVal 4 (SOff 36 0))].
Definition cc2_nR : YP09.region :=
YP09.mkRegion (Some 9%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 37 0))].
Definition cc2_spR : YP09.region :=
YP09.mkRegion (Some 2%nat) 16 24 16 16 [YP09.mkChunk 16 (CVal 8 (SOff 33 0))].
Definition ss_cc2L : sstate :=
mkSS CC_LOOP (sr_set sr_atoms 27 cc2_sh11) [cc2_segR; cc2_nR; cc2_spR] None cc2_facts.
Definition ss_cc2T : sstate :=
mkSS CC_LATCH (sr_set sr_atoms 27 cc2_sh11) [cc2_nR] None cc2_facts.
(* the two writable cells of the model-drop arm (model_set at 0x3c, model[0] at 0x24) and the eight bytes of
   the box arm (role at 0x10 and role_set at 0x14, what rs_drop_role writes) *)
Definition cc2_msR : YP09.region := YP09.mkRegion (Some 32%nat) 60 64 60 64 [].
Definition cc2_mR : YP09.region := YP09.mkRegion (Some 32%nat) 36 37 36 37 [].
Definition cc2_rR : YP09.region := YP09.mkRegion (Some 32%nat) 16 24 16 24 [].
Definition cc2_A1mem : smem := [cc2_msR; cc2_mR].
Definition cc2_A2mem : smem := [cc2_rR].
Definition cc2_shx (off : Z) : sv :=
SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 off) (SLit 3)) (SOff 19 0).
Definition ss_cc2A1 : sstate :=
mkSS CC_RET1 (sr_set (sr_set sr_atoms 21 (SOff 32 60)) 22 (SOff 32 36)) cc2_A1mem None cc2_facts.
Definition ss_cc2A2 : sstate :=
mkSS CC_RET2 (sr_set (sr_set (sr_set sr_atoms 20 (SOff 32 0)) 23 (cc2_shx 20)) 24 (cc2_shx 16))
  cc2_A2mem None cc2_facts.
Definition cc2_Bspan : Z * Z := Bspan.
(* a run of the pass that writes nothing: every region of its state is read-only *)
Ltac cc2_ro :=
try unfold ss_cc2L; try unfold ss_cc2T; cbn [ss_mem add_cond];
repeat (apply Forall_cons;
  [try unfold cc2_segR; try unfold cc2_nR; try unfold cc2_spR; cbn [YP09.r_wlo YP09.r_whi]; lia|]);
apply Forall_nil.
Ltac cc2_ro_awr :=
try unfold ss_cc2L; try unfold ss_cc2T; cbn [ss_mem add_cond];
repeat (apply awr_ok_cons_ro;
  [try unfold cc2_segR; try unfold cc2_nR; try unfold cc2_spR; cbn [YP09.r_wlo YP09.r_whi]; lia|]);
apply awr_ok_nil.
(* from a run's frame fact to "the memory is the one the run started from" *)
Ltac cc2_frame HFn HEQn :=
lazymatch type of HFn with
| frame_of _ ?rs _ _ =>
  let HRO := fresh "HRO" in
  assert (HRO : Forall (fun r : YP09.region => YP09.r_whi r <= YP09.r_wlo r) rs) by cc2_ro;
  pose proof (cc2_frame_ro _ _ _ _ HRO HFn) as HEQn; clear HRO
end.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
(* the environment of a cut: the registers as atoms 0..31, then &seg[i], the F_xbox spill and the four
   values the pass reads out of the record *)
Definition cc2_EL (regs : bvmap 5 word) (sg xbox role rset mset n : Z) : env :=
Eimg (Ereg regs [Z_to_bv 64 sg; Z_to_bv 64 xbox; Z_to_bv 64 role; Z_to_bv 64 rset;
                 Z_to_bv 64 mset; Z_to_bv 64 n]).
(* the entry the pass runs over, the two flags as the record's bytes hold them, and the environment of a cut *)
Definition cc2_sgi (v : ccx) (i : Z) : rseg := nth (Z.to_nat i) (rc_seg (cc_at v i)) rseg_d.
Definition cc2_bz (b : bool) : Z := if b then 1 else 0.
Definition cc2_El (lt : list Z -> Z) (v : ccx) (i : Z) (regs : bvmap 5 word) : env :=
cc2_EL regs (x_c v + 356 * i) (lt F_xbox) (rs_role (cc2_sgi v i))
  (cc2_bz (rs_role_set (cc2_sgi v i))) (cc2_bz (rs_model_set (cc2_sgi v i)))
  (Z.of_nat (length (rc_seg (cc_at v i)))).
(* the environment of the latch: the record's three fields are not read there, so their atoms are 0 *)
Definition cc2_Et (lt : list Z -> Z) (v : ccx) (i : Z) (regs : bvmap 5 word) : env :=
cc2_EL regs (x_c v + 356 * i) (lt F_xbox) 0 0 0 (Z.of_nat (length (rc_seg (x_rcs v)))).
(* an atom's own value, as the executor leaves a register that no instruction of the pass touched *)
Lemma cc2_den_atom : forall E k, sv_denot E (SOff k 0) = ew E k.
Proof. intros E k. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Lemma cc2_den_lit : forall E z, 0 <= z < 2 ^ 64 -> sv_denot E (SLit z) = Z_to_bv 64 z.
Proof.
intros E z Hz. apply bv_eq. change (U E (SLit z) = bv_unsigned (Z_to_bv 64 z)).
rewrite U_lit by lia. rewrite unsigned_lit_small by lia. reflexivity.
Qed.
(* the two flags the pass branches on, as `beqz` reads them, and the role against BOX = 4 *)
Lemma cc2_br_flag : forall E k (b : bool) (r : bool),
  ew E k = Z_to_bv 64 (cc2_bz b) ->
  branch_taken BC_EQ (sv_denot E (SOff k 0)) (sv_denot E (SLit 0)) = r -> negb b = r.
Proof.
intros E k b r Hk Hc. rewrite branch_eq_U, (U_atom E k (cc2_bz b) Hk), U_lit in Hc;
  [|lia | unfold cc2_bz; destruct b; lia].
rewrite <- Hc. unfold cc2_bz. destruct b; reflexivity.
Qed.
Lemma cc2_br_role : forall E k (z : Z) (r : bool), ew E k = Z_to_bv 64 z -> 0 <= z < 2 ^ 31 ->
  branch_taken BC_EQ (sv_denot E (SOff k 0)) (sv_denot E (SLit 4)) = r -> (z =? 4) = r.
Proof.
intros E k z r Hk Hz Hc. rewrite branch_eq_U, (U_atom E k z Hk ltac:(lia)), U_lit in Hc by lia. exact Hc.
Qed.
Lemma cc2_br_role_ne : forall E k (z : Z) (r : bool), ew E k = Z_to_bv 64 z -> 0 <= z < 2 ^ 31 ->
  branch_taken BC_NE (sv_denot E (SOff k 0)) (sv_denot E (SLit 4)) = r -> negb (z =? 4) = r.
Proof.
intros E k z r Hk Hz Hc. rewrite branch_ne_U, (U_atom E k z Hk ltac:(lia)), U_lit in Hc by lia. exact Hc.
Qed.
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable lit : list Z -> Z.
Variables gotw guard STK_REF : Z.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis VOBJ : seg_val_objs.
Hypothesis SIGP : seg_sig_prog.
Hypothesis ROIMG : forall a, SEG_RLO <= a < SEG_RHI -> in_img SEGS a.
Hypothesis SSPAR : forall ly S (W : world SEGS) mem md,
  AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) gotw guard.
Hypothesis LITM : lit F_xmodel = VAL (A_OBJ 73).
Hypothesis LITB : lit F_xbox = VAL (A_OBJ 74).
Hypothesis STKR : 0 <= STK_REF.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
(* the atoms of the head's environment *)
Lemma cc2_ewL : forall (v : ccx) i regs (m : nat) (r : bv 5), Z.of_nat m = bv_unsigned r ->
  ew (cc2_El lit v i regs) m = getr regs r.
Proof. intros v i regs m r Hm. unfold cc2_El, cc2_EL. apply ew_Eimg_Ereg_nat. exact Hm. Qed.
Lemma cc2_exL : forall (v : ccx) i regs j, (j < 6)%nat ->
  ew (cc2_El lit v i regs) (32 + j)%nat =
  nth j [Z_to_bv 64 (x_c v + 356 * i); Z_to_bv 64 (lit F_xbox); Z_to_bv 64 (rs_role (cc2_sgi v i));
         Z_to_bv 64 (cc2_bz (rs_role_set (cc2_sgi v i)));
         Z_to_bv 64 (cc2_bz (rs_model_set (cc2_sgi v i)));
         Z_to_bv 64 (Z.of_nat (length (rc_seg (cc_at v i))))] (Z_to_bv 64 0).
Proof.
intros v i regs j Hj. unfold cc2_El, cc2_EL. rewrite Eimg_low by (unfold A_TEXT; lia).
apply ew_Ereg_extra.
Qed.
(* reading a register of a call state, where the executor leaves `st_ok`, not `st_ok_pi` *)
Ltac cc2_rgS HS r Hr :=
lazymatch type of HS with
| st_ok ?sg ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_restrict_reg sg H E ss ms r HS) as Hr;
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    change (sr_get (ss_regs ss) r) with e in Hr;
  cbn [ms_regs restrict mkst] in Hr
end.
(* the walk of one pass at a fixed FP state; closed below, so that the head (section c) applies the arms and the
   latch at the FP state refuse returned *)
Section a. Context {fx : YK11.FPState}.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* ===================== 4. what every cut of the pass knows about the block ===================== *)
(* the entry's own bounds, from the live block of cc_un *)
Lemma cc2_blk : forall (v : ccx) ly3 S3 (W3 : world SEGS) mem3 md3,
  AR SEGS B ly3 S3 W3 mem3 md3 -> sa_heap B ly3 S3 (x_c v) seg_spec.SEG_C_SIZE ->
  4096 <= x_c v /\ x_c v + seg_spec.SEG_C_SIZE <= alloc_ceiling /\
  (forall a, x_c v <= a < x_c v + seg_spec.SEG_C_SIZE -> apresent (w_H W3) mem3 a) /\
  in_app (x_c v) seg_spec.SEG_C_SIZE /\
  sa_addr (rdW W3 mem3) (x_c v) seg_spec.SEG_C_SIZE.
Proof.
intros v ly3 S3 W3 mem3 md3 HAR HH.
pose proof asan_consts as (C1 & _).
pose proof HH as (b & m & Hin & Hlo & Hhi).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & Hb4 & Hbc & Hbapp & Hpres & _ & Hm).
pose proof (req_size_pos0 m ltac:(lia)) as (Hrq1 & Hrq2).
split; [unfold seg_spec.SEG_C_SIZE in *; lia|].
split; [unfold seg_spec.SEG_C_SIZE in *; lia|].
split; [intros a Ha; exact (proj1 (Hpres a ltac:(unfold seg_spec.SEG_C_SIZE in *; lia)))|].
split.
- apply (in_app_sub b (req_size m)); [exact Hbapp | lia | unfold seg_spec.SEG_C_SIZE; lia | lia].
- exact (cc_block_addr B ly3 S3 W3 mem3 md3 (x_c v) seg_spec.SEG_C_SIZE HAR HH
    ltac:(unfold seg_spec.SEG_C_SIZE; lia)).
Qed.
(* the two shadow entries of a cut, from the block's shadow *)
Lemma cc2_shok : forall (v : ccx) (i : Z) (W3 : world SEGS) mem3 E,
  4096 <= x_c v -> x_c v + seg_spec.SEG_C_SIZE <= CC2_CEIL -> 0 <= i <= 31 ->
  in_app (x_c v) seg_spec.SEG_C_SIZE ->
  sa_addr (rdW W3 mem3) (x_c v) seg_spec.SEG_C_SIZE ->
  U E cc2_Bx = SHADOW_OFF ->
  ew E 32%nat = Z_to_bv 64 (x_c v + 356 * i) ->
  ew E 9%nat = Z_to_bv 64 (x_c v + seg_spec.RC_N) ->
  sh_ok SEGS cc2_Bx cc2_SH E (mrestrict (w_H W3) mem3).
Proof.
intros v i W3 mem3 E Hc4 Hcc Hi Happ HRA HBx E32 E9.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HRA as (_ & _ & _ & Hra & _).
unfold sh_ok, cc2_SH. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
- apply (shent_ok_of_range SEGS (w_H W3) mem3 E cc2_Bx 32 (x_c v) seg_spec.SEG_C_SIZE
    (x_c v + 356 * i) 0 356 Hra HBx).
  + apply U_atom; [exact E32 | unfold seg_spec.SEG_C_SIZE, CC2_CEIL in *; lia].
  + lia.
  + unfold seg_spec.SEG_C_SIZE; lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold SHADOW_OFF.
    unfold seg_spec.SEG_C_SIZE in *. lia.
- apply (shent_ok_of_range SEGS (w_H W3) mem3 E cc2_Bx 9 (x_c v) seg_spec.SEG_C_SIZE
    (x_c v + seg_spec.RC_N) 0 8 Hra HBx).
  + apply U_atom; [exact E9 | unfold seg_spec.RC_N, seg_spec.SEG_C_SIZE, CC2_CEIL in *; lia].
  + unfold seg_spec.RC_N; lia.
  + unfold seg_spec.RC_N, seg_spec.SEG_C_SIZE; lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold SHADOW_OFF.
    unfold seg_spec.RC_N, seg_spec.SEG_C_SIZE in *. lia.
Qed.
(* the literals cross_check passes are image bytes, so their addresses are positive and below the shadow *)
Lemma cc2_lit_lo : forall (v : ccx) ly3 S3 (W3 : world SEGS) mem3 x,
  cc_un B lit gotw guard STK_REF v ly3 S3 W3 mem3 -> In x CROSS_CHECK_LITS ->
  0 < lit x < kLowMemEnd.
Proof.
intros v ly3 S3 W3 mem3 x HUN Hx.
pose proof (un_lit _ _ _ _ _ _ _ _ _ _ HUN x Hx) as (Hpos & _ & _ & _ & Himg).
destruct (Himg (lit x) ltac:(lia)) as (Hin & _ & _).
pose proof (pa_segs_low (lit x) Hin). lia.
Qed.
(* the numbers every cut of the pass runs on *)
Lemma cc2_bounds : forall (v : ccx) (i : Z) ly3 S3 (W3 : world SEGS) regs3 mem3 md3,
  cc_pre B lit gotw guard STK_REF v ->
  cc_fi B lit gotw guard STK_REF v ly3 S3 W3 regs3 mem3 md3 ->
  cc_un B lit gotw guard STK_REF v ly3 S3 W3 mem3 ->
  0 <= i < cc_n v ->
  4096 <= x_c v /\ x_c v + seg_spec.SEG_C_SIZE <= alloc_ceiling /\ x_c v mod 16 = 0 /\ 0 <= i <= 31 /\
  in_app (x_c v) seg_spec.SEG_C_SIZE /\ sa_addr (rdW W3 mem3) (x_c v) seg_spec.SEG_C_SIZE /\
  (forall a, x_c v <= a < x_c v + seg_spec.SEG_C_SIZE -> apresent (w_H W3) mem3 a) /\
  alloc_ceiling + 128 <= cc_sp0 v /\ cc_sp0 v <= 2 ^ 47 /\ 0 < lit F_xbox < kLowMemEnd /\
  (length (rc_seg (cc_at v i)) <= 32)%nat.
Proof.
intros v i ly3 S3 W3 regs3 mem3 md3 HPRE HFI HUN Hi.
pose proof (proj1 (fi_j _ _ _ _ _ _ _ _ _ _ _ _ HFI)) as HAR.
destruct (cc2_blk v ly3 S3 W3 mem3 md3 HAR (un_heap _ _ _ _ _ _ _ _ _ _ HUN))
  as (Hc4 & Hcc & Hpres & Happ & HSA).
pose proof (cp_c16 _ _ _ _ _ _ HPRE) as Hc16.
destruct (sa_rconf_n (rdW (x_W v) (x_mem v)) (x_c v) (x_rcs v) (cp_rconf _ _ _ _ _ _ HPRE))
  as (_ & Hlen32 & _).
assert (Hlf : length (rc_seg (cc_at v i)) = length (rc_seg (x_rcs v))).
{ unfold cc_at. apply cc_fold_len. lia. }
pose proof (cp_afn _ _ _ _ _ _ HPRE) as (_ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
unfold cc_n in Hi.
split; [exact Hc4|]. split; [exact Hcc|]. split; [exact Hc16|].
split; [lia|]. split; [exact Happ|]. split; [exact HSA|]. split; [exact Hpres|].
split; [unfold cc_STK in *; unfold cc_sp0 in *; lia|].
split; [unfold cc_sp0 in *; lia|].
split; [apply (cc2_lit_lo v ly3 S3 W3 mem3); [exact HUN | unfold CROSS_CHECK_LITS; right; left; reflexivity]|].
lia.
Qed.
(* the facts of a cut's symbolic state *)
Lemma cc2_factsok : forall E c i role rset mset n,
  ew E 8%nat = Z_to_bv 64 c -> ew E 9%nat = Z_to_bv 64 (c + seg_spec.RC_N) ->
  ew E 19%nat = Z_to_bv 64 SHADOW_OFF -> ew E 25%nat = Z_to_bv 64 (356 * i) ->
  ew E 26%nat = Z_to_bv 64 i -> ew E 32%nat = Z_to_bv 64 (c + 356 * i) ->
  ew E 34%nat = Z_to_bv 64 role -> ew E 35%nat = Z_to_bv 64 rset ->
  ew E 36%nat = Z_to_bv 64 mset -> ew E 37%nat = Z_to_bv 64 n ->
  4096 <= c -> c + seg_spec.SEG_C_SIZE <= CC2_CEIL -> c mod 16 = 0 -> 0 <= i <= 31 ->
  0 <= role < 2 ^ 31 -> 0 <= rset <= 1 -> 0 <= mset <= 1 -> 0 <= n <= 32 ->
  facts_ok E cc2_facts.
Proof.
intros E c i role rset mset n E8 E9 E19 E25 E26 E32 E34 E35 E36 E37
  Hc4 Hcc Hc16 Hi Hrole Hrset Hmset Hn.
assert (Hc8 : c mod 8 = 0).
{ pose proof (Z.div_mod c 16 ltac:(lia)) as D. rewrite Hc16, Z.add_0_r in D.
  rewrite D. replace (16 * (c / 16)) with (8 * (2 * (c / 16))) by lia.
  rewrite Z.mul_comm. apply Z_mod_mult. }
assert (Hc4m : c mod 4 = 0).
{ pose proof (Z.div_mod c 16 ltac:(lia)) as D. rewrite Hc16, Z.add_0_r in D.
  rewrite D. replace (16 * (c / 16)) with (4 * (4 * (c / 16))) by lia.
  rewrite Z.mul_comm. apply Z_mod_mult. }
assert (Hs4 : (356 * i) mod 4 = 0).
{ replace (356 * i) with (89 * i * 4) by lia. apply Z_mod_mult. }
unfold facts_ok, cc2_facts. cbn [f_atoms f_conds f_alias].
split; [|split; [exact I|]].
- cbn [atoms_ok cc2_atoms].
  split; [apply (cc2_afact E 8%nat c);
          [exact E8 | unfold CC2_CEIL, seg_spec.SEG_C_SIZE in *; lia
          | unfold CC2_CEIL, seg_spec.SEG_C_SIZE in *; lia
          | change (2 ^ 4) with 16; exact Hc16 | lia]|].
  split; [apply (cc2_afact E 9%nat (c + seg_spec.RC_N));
          [exact E9 | unfold CC2_CEIL, seg_spec.SEG_C_SIZE, seg_spec.RC_N in *; lia
          | unfold CC2_CEIL, seg_spec.SEG_C_SIZE, seg_spec.RC_N in *; lia
          | change (2 ^ 3) with 8; unfold seg_spec.RC_N;
            replace (c + 11392) with (c + 1424 * 8) by lia; rewrite Z_mod_plus_full; exact Hc8
          | lia]|].
  split; [apply (cc2_afact E 19%nat SHADOW_OFF);
          [exact E19 | unfold SHADOW_OFF; lia | unfold SB, SHADOW_OFF; lia
          | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]|].
  split; [apply (cc2_afact E 25%nat (356 * i));
          [exact E25 | lia | lia | change (2 ^ 2) with 4; exact Hs4 | lia]|].
  split; [apply (cc2_afact E 26%nat i);
          [exact E26 | lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]|].
  split; [apply (cc2_afact E 32%nat (c + 356 * i));
          [exact E32 | unfold CC2_CEIL, seg_spec.SEG_C_SIZE in *; lia
          | unfold CC2_CEIL, seg_spec.SEG_C_SIZE in *; lia
          | change (2 ^ 2) with 4; rewrite Z.add_mod by lia; rewrite Hc4m, Hs4; reflexivity
          | lia]|].
  split; [apply (cc2_afact E 34%nat role);
          [exact E34 | lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]|].
  split; [apply (cc2_afact E 35%nat rset);
          [exact E35 | lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]|].
  split; [apply (cc2_afact E 36%nat mset);
          [exact E36 | lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]|].
  split; [apply (cc2_afact E 37%nat n);
          [exact E37 | lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]|].
  exact I.
- cbn [cc2_alias alias_ok].
  split; [|split; [|exact I]].
  + apply bv_eq.
    change (U E (SAlu ALU_ADD (SOff 8 0) (SOff 25 0)) = U E (SOff 32 0)).
    rewrite U_SAlu, (U_atom E 8%nat c E8 ltac:(unfold CC2_CEIL, seg_spec.SEG_C_SIZE in *; lia)),
      (U_atom E 25%nat (356 * i) E25 ltac:(lia)),
      (U_atom E 32%nat (c + 356 * i) E32 ltac:(unfold CC2_CEIL, seg_spec.SEG_C_SIZE in *; lia)).
    cbv [zalu_raw]. apply zcanon_id. unfold M64, CC2_CEIL, seg_spec.SEG_C_SIZE in *. lia.
  + apply bv_eq.
    change (U E (SAlu ALU_ADD (SOff 8 0) (SMd M_MUL (SOff 26 0) (SLit 356))) = U E (SOff 32 0)).
    rewrite U_SAlu, U_SMd, U_SLit,
      (U_atom E 8%nat c E8 ltac:(unfold CC2_CEIL, seg_spec.SEG_C_SIZE in *; lia)),
      (U_atom E 26%nat i E26 ltac:(lia)),
      (U_atom E 32%nat (c + 356 * i) E32 ltac:(unfold CC2_CEIL, seg_spec.SEG_C_SIZE in *; lia)).
    cbv [zalu_raw zmd_raw].
    rewrite (zcanon_id 356) by (unfold M64; lia).
    rewrite (zcanon_id (i * 356)) by (unfold M64; lia).
    replace (c + i * 356) with (c + 356 * i) by lia.
    apply zcanon_id. unfold M64, CC2_CEIL, seg_spec.SEG_C_SIZE in *. lia.
Qed.
(* the three regions of a cut *)
Lemma cc2_regseg : forall E (W3 : world SEGS) mem3 c i role rset mset,
  ew E 32%nat = Z_to_bv 64 (c + 356 * i) ->
  ew E 34%nat = Z_to_bv 64 role -> ew E 35%nat = Z_to_bv 64 rset -> ew E 36%nat = Z_to_bv 64 mset ->
  4096 <= c -> c + seg_spec.SEG_C_SIZE <= CC2_CEIL -> 0 <= i <= 31 ->
  0 <= role < 2 ^ 31 -> 0 <= rset <= 1 -> 0 <= mset <= 1 ->
  sa_val (rdW W3 mem3) (c + 356 * i + seg_spec.RS_ROLE) 4 role ->
  sa_val (rdW W3 mem3) (c + 356 * i + seg_spec.RS_ROLE_SET) 4 rset ->
  sa_val (rdW W3 mem3) (c + 356 * i + seg_spec.RS_MODEL_SET) 4 mset ->
  region_ok SEGS E (mrestrict (w_H W3) mem3) cc2_segR.
Proof.
intros E W3 mem3 c i role rset mset E32 E34 E35 E36 Hc4 Hcc Hi Hrole Hrset Hmset VR VS VM.
assert (U32 : base_val E (Some 32%nat) = c + 356 * i).
{ cbn [base_val]. rewrite E32. apply unsigned_lit_small.
  unfold CC2_CEIL, seg_spec.SEG_C_SIZE in *. lia. }
unfold cc2_segR, region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
rewrite U32.
split; [lia|]. split; [unfold CC2_CEIL, seg_spec.SEG_C_SIZE in *; lia|].
split; [intros o Ho; lia|].
unfold seg_spec.RS_ROLE in VR. unfold seg_spec.RS_ROLE_SET in VS. unfold seg_spec.RS_MODEL_SET in VM.
repeat apply Forall_cons; try apply Forall_nil.
- apply (chunk_ok_val SEGS E _ (c + 356 * i) 16 4 (SOff 34 0) role);
  [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | cbn; lia |].
  exact (cc2_val_mem SEGS (w_H W3) mem3 _ 4%nat role VR).
- apply (chunk_ok_val SEGS E _ (c + 356 * i) 20 4 (SOff 35 0) rset);
  [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | cbn; lia |].
  exact (cc2_val_mem SEGS (w_H W3) mem3 _ 4%nat rset VS).
- apply (chunk_ok_val SEGS E _ (c + 356 * i) 60 4 (SOff 36 0) mset);
  [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | cbn; lia |].
  exact (cc2_val_mem SEGS (w_H W3) mem3 _ 4%nat mset VM).
Qed.
Lemma cc2_regn : forall E (W3 : world SEGS) mem3 c n,
  ew E 9%nat = Z_to_bv 64 (c + seg_spec.RC_N) -> ew E 37%nat = Z_to_bv 64 n ->
  4096 <= c -> c + seg_spec.SEG_C_SIZE <= CC2_CEIL -> 0 <= n <= 32 ->
  sa_val (rdW W3 mem3) (c + seg_spec.RC_N) 4 n ->
  region_ok SEGS E (mrestrict (w_H W3) mem3) cc2_nR.
Proof.
intros E W3 mem3 c n E9 E37 Hc4 Hcc Hn VN.
assert (U9 : base_val E (Some 9%nat) = c + seg_spec.RC_N).
{ cbn [base_val]. rewrite E9. apply unsigned_lit_small.
  unfold CC2_CEIL, seg_spec.SEG_C_SIZE, seg_spec.RC_N in *. lia. }
unfold cc2_nR, region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
rewrite U9.
split; [unfold seg_spec.RC_N; lia|].
split; [unfold CC2_CEIL, seg_spec.SEG_C_SIZE, seg_spec.RC_N in *; lia|].
split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val SEGS E _ (c + seg_spec.RC_N) 0 4 (SOff 37 0) n);
  [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | cbn; lia |].
rewrite Z.add_0_r. exact (cc2_val_mem SEGS (w_H W3) mem3 _ 4%nat n VN).
Qed.
Lemma cc2_regsp : forall E (W3 : world SEGS) mem3 sp0,
  ew E 2%nat = Z_to_bv 64 (sp0 - 128) -> ew E 33%nat = Z_to_bv 64 (lit F_xbox) ->
  0 < lit F_xbox < kLowMemEnd -> alloc_ceiling + 128 <= sp0 -> sp0 <= 2 ^ 47 ->
  rdword (rdW W3 mem3) (sp0 - 112) = Some (lit F_xbox) ->
  region_ok SEGS E (mrestrict (w_H W3) mem3) cc2_spR.
Proof.
intros E W3 mem3 sp0 E2 E33 Hxb Hsp Hsp47 HW.
pose proof asan_consts as (C1 & _).
assert (U2 : base_val E (Some 2%nat) = sp0 - 128).
{ cbn [base_val]. rewrite E2. apply unsigned_lit_small. lia. }
unfold cc2_spR, region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
rewrite U2.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val SEGS E _ (sp0 - 128) 16 8 (SOff 33 0) (lit F_xbox));
  [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold kLowMemEnd in *; lia | cbn; lia |].
replace (sp0 - 128 + 16) with (sp0 - 112) by lia.
exact (val_mem_of_rdword SEGS (w_H W3) mem3 _ _ HW).
Qed.
(* ===================== 5. the seed at the head of a pass ===================== *)
Lemma cc2_seedL : forall (v : ccx) (i : Z) ly3 S3 (W3 : world SEGS) regs3 mem3 md3,
  cc_pre B lit gotw guard STK_REF v ->
  INV_LOOP B lit gotw guard STK_REF v i ly3 S3 W3 regs3 mem3 md3 ->
  img_env VAL A_LIM (cc2_El lit v i regs3) /\
  st_ok_pi SEGS VAL (cc2_El lit v i regs3) ss_cc2L
    (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 (BASE + CC_LOOP)) mem3 (seg_rom SEGS))) /\
  sh_ok SEGS cc2_Bx cc2_SH (cc2_El lit v i regs3) (mrestrict (w_H W3) mem3).
Proof.
intros v i ly3 S3 W3 regs3 mem3 md3 HPRE HINV.
pose proof HINV as (HFI & HUN & Hi & HRC & R8 & R9 & R18 & R19 & R25 & R26 & R27 & Hsp8 & Hsp10).
destruct (cc2_bounds v i ly3 S3 W3 regs3 mem3 md3 HPRE HFI HUN Hi)
  as (Hc4 & Hcc & Hc16 & Hi31 & Happ & HSA & Hpres & Hsp & Hsp47 & Hxb & Hl32).
pose proof asan_consts as (C1 & _).
pose proof (fi_sp _ _ _ _ _ _ _ _ _ _ _ _ HFI) as R2.
assert (Hlt : (Z.to_nat i < length (rc_seg (cc_at v i)))%nat).
{ unfold cc_n in Hi.
  assert (Hlf : length (rc_seg (cc_at v i)) = length (rc_seg (x_rcs v)))
    by (unfold cc_at; apply cc_fold_len; lia).
  lia. }
destruct (sa_rconf_fields (rdW W3 mem3) (x_c v) (cc_at v i) (Z.to_nat i) HRC Hlt)
  as (_ & _ & _ & _ & VR & HRr & VS & VM).
destruct (sa_rconf_n (rdW W3 mem3) (x_c v) (cc_at v i) HRC) as (VN & _ & _).
rewrite Z2Nat.id in VR, VS, VM by lia.
unfold cc2_El, cc2_EL.
pose proof (fun (m : nat) (r : bv 5) (Hm : Z.of_nat m = bv_unsigned r) =>
  ew_Eimg_Ereg_nat regs3
    [Z_to_bv 64 (x_c v + 356 * i); Z_to_bv 64 (lit F_xbox); Z_to_bv 64 (rs_role (cc2_sgi v i));
     Z_to_bv 64 (cc2_bz (rs_role_set (cc2_sgi v i))); Z_to_bv 64 (cc2_bz (rs_model_set (cc2_sgi v i)));
     Z_to_bv 64 (Z.of_nat (length (rc_seg (cc_at v i))))] m r Hm) as EE.
assert (EXT : forall j, (j < 6)%nat ->
  ew (Eimg (Ereg regs3
    [Z_to_bv 64 (x_c v + 356 * i); Z_to_bv 64 (lit F_xbox); Z_to_bv 64 (rs_role (cc2_sgi v i));
     Z_to_bv 64 (cc2_bz (rs_role_set (cc2_sgi v i))); Z_to_bv 64 (cc2_bz (rs_model_set (cc2_sgi v i)));
     Z_to_bv 64 (Z.of_nat (length (rc_seg (cc_at v i))))])) (32 + j)%nat
  = nth j
    [Z_to_bv 64 (x_c v + 356 * i); Z_to_bv 64 (lit F_xbox); Z_to_bv 64 (rs_role (cc2_sgi v i));
     Z_to_bv 64 (cc2_bz (rs_role_set (cc2_sgi v i))); Z_to_bv 64 (cc2_bz (rs_model_set (cc2_sgi v i)));
     Z_to_bv 64 (Z.of_nat (length (rc_seg (cc_at v i))))] (Z_to_bv 64 0)).
{ intros j Hj. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
pose proof (EXT 0%nat ltac:(lia)) as E32. pose proof (EXT 1%nat ltac:(lia)) as E33.
pose proof (EXT 2%nat ltac:(lia)) as E34. pose proof (EXT 3%nat ltac:(lia)) as E35.
pose proof (EXT 4%nat ltac:(lia)) as E36. pose proof (EXT 5%nat ltac:(lia)) as E37.
cbn [Nat.add nth] in E32, E33, E34, E35, E36, E37. clear EXT.
assert (E2 : ew _ 2%nat = Z_to_bv 64 (cc_sp0 v - 128)) by (rewrite (EE 2%nat 2%bv eq_refl); exact R2).
assert (E8 : ew _ 8%nat = Z_to_bv 64 (x_c v)) by (rewrite (EE 8%nat 8%bv eq_refl); exact R8).
assert (E9 : ew _ 9%nat = Z_to_bv 64 (x_c v + seg_spec.RC_N))
  by (rewrite (EE 9%nat 9%bv eq_refl); exact R9).
assert (E19 : ew _ 19%nat = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 19%nat 19%bv eq_refl); exact R19).
assert (E25 : ew _ 25%nat = Z_to_bv 64 (356 * i)) by (rewrite (EE 25%nat 25%bv eq_refl); exact R25).
assert (E26 : ew _ 26%nat = Z_to_bv 64 i) by (rewrite (EE 26%nat 26%bv eq_refl); exact R26).
assert (Hrole : 0 <= rs_role (cc2_sgi v i) < 2 ^ 31) by (unfold cc2_sgi; exact HRr).
assert (Hrset : 0 <= cc2_bz (rs_role_set (cc2_sgi v i)) <= 1)
  by (unfold cc2_bz; destruct (rs_role_set (cc2_sgi v i)); lia).
assert (Hmset : 0 <= cc2_bz (rs_model_set (cc2_sgi v i)) <= 1)
  by (unfold cc2_bz; destruct (rs_model_set (cc2_sgi v i)); lia).
assert (Hn32 : 0 <= Z.of_nat (length (rc_seg (cc_at v i))) <= 32) by lia.
assert (HBx : U (Eimg (Ereg regs3
    [Z_to_bv 64 (x_c v + 356 * i); Z_to_bv 64 (lit F_xbox); Z_to_bv 64 (rs_role (cc2_sgi v i));
     Z_to_bv 64 (cc2_bz (rs_role_set (cc2_sgi v i))); Z_to_bv 64 (cc2_bz (rs_model_set (cc2_sgi v i)));
     Z_to_bv 64 (Z.of_nat (length (rc_seg (cc_at v i))))])) cc2_Bx = SHADOW_OFF).
{ unfold cc2_Bx. apply U_atom; [exact E19 | unfold SHADOW_OFF; lia]. }
assert (U32 : base_val _ (Some 32%nat) = x_c v + 356 * i)
  by (cbn [base_val]; rewrite E32; apply unsigned_lit_small;
      unfold seg_spec.SEG_C_SIZE in *; lia).
assert (U9 : base_val _ (Some 9%nat) = x_c v + seg_spec.RC_N)
  by (cbn [base_val]; rewrite E9; apply unsigned_lit_small;
      unfold seg_spec.RC_N, seg_spec.SEG_C_SIZE in *; lia).
assert (U2 : base_val _ (Some 2%nat) = cc_sp0 v - 128)
  by (cbn [base_val]; rewrite E2; apply unsigned_lit_small; lia).
split; [apply Eimg_env|].
split.
- rewrite restrict_mkst_fx. unfold ss_cc2L. apply pa_entry_st_ok_full.
  + apply regs_ok_rereg; [apply regs_ok_Eimg_Ereg | reflexivity |].
    rewrite R27. unfold cc2_sh11.
    rewrite (cc2_shadow_denot _ 9%nat 19%nat (x_c v + seg_spec.RC_N) E9 E19
      ltac:(unfold seg_spec.RC_N, seg_spec.SEG_C_SIZE in *; lia)).
    reflexivity.
  + vm_compute. reflexivity.
  + apply Forall_cons;
      [exact (cc2_regseg _ W3 mem3 (x_c v) i _ _ _ E32 E34 E35 E36 Hc4
                ltac:(unfold CC2_CEIL; lia) Hi31 Hrole Hrset Hmset VR VS VM)|].
    apply Forall_cons;
      [exact (cc2_regn _ W3 mem3 (x_c v) _ E9 E37 Hc4 ltac:(unfold CC2_CEIL; lia) Hn32 VN)|].
    apply Forall_cons; [|apply Forall_nil].
    exact (cc2_regsp _ W3 mem3 (cc_sp0 v) E2 E33 Hxb Hsp Hsp47 Hsp10).
  + cbn [pairwise_disjoint all_disjoint].
    unfold cc2_segR, cc2_nR, cc2_spR, extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite U32, U9, U2.
    repeat split; try exact I; unfold seg_spec.RC_N, seg_spec.SEG_C_SIZE in *; lia.
  + exact (cc2_factsok _ (x_c v) i _ _ _ _ E8 E9 E19 E25 E26 E32 E34 E35 E36 E37 Hc4
             ltac:(unfold CC2_CEIL; lia) Hc16 Hi31 Hrole Hrset Hmset Hn32).
- exact (cc2_shok v i W3 mem3 _ Hc4 ltac:(unfold CC2_CEIL; lia) Hi31 Happ HSA HBx E32 E9).
Qed.
(* ===================== 6. the latch ===================== *)
(* the cut at 0x893b8: the pass has run, so the block holds the record after i + 1 passes; every register of
   the head is still there, and the loop counters still say i *)
Definition cc2_INV_LATCH (v : ccx) (i : Z)
  (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (regs3 : bvmap 5 word) (mem3 : word -> option byte)
  (md3 : Model) : Prop :=
  cc_fi B lit gotw guard STK_REF v ly3 S3 W3 regs3 mem3 md3 /\
  cc_un B lit gotw guard STK_REF v ly3 S3 W3 mem3 /\
  0 <= i < cc_n v /\
  sa_rconf (rdW W3 mem3) (x_c v) (cc_at v (i + 1)) /\
  getr regs3 8 = w64 (x_c v) /\
  getr regs3 9 = w64 (x_c v + seg_spec.RC_N) /\
  getr regs3 18 = w64 (lit F_xmodel) /\
  getr regs3 19 = w64 SHADOW_OFF /\
  getr regs3 25 = w64 (356 * i) /\
  getr regs3 26 = w64 i /\
  getr regs3 27 = w64 (SHADOW_OFF + (x_c v + seg_spec.RC_N) / 8) /\
  rdword (rdW W3 mem3) (cc_sp0 v - 120) = Some 3 /\
  rdword (rdW W3 mem3) (cc_sp0 v - 112) = Some (lit F_xbox).
(* the frame part and the untouched part of a cut carried over a run that wrote nothing *)
Lemma cc2_fi_ext : forall (v : ccx) ly S (W : world SEGS) regs m md regs' m' md',
  cc_fi B lit gotw guard STK_REF v ly S W regs m md ->
  ajournal SEGS B (cc_STK STK_REF) (cc_sp0 v) (cc_FP v) (x_ly v) (x_S v) (x_W v) (x_mem v) (x_md v) []
    ly S W m' md' 0 ->
  (forall x, m' x = m x) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  cc_fi B lit gotw guard STK_REF v ly S W regs' m' md'.
Proof.
intros v ly S W regs m md regs' m' md' [J1 G2 G3 G4 GSV GNO] HJ He E2 E3 E4. constructor.
- exact HJ.
- rewrite E2; exact G2.
- rewrite E3; exact G3.
- rewrite E4; exact G4.
- intros j r Hj. rewrite <- (GSV j r Hj). apply rdword_ext. intros k Hk.
  apply (cc2_aview_ext SEGS (w_H W) m m' He).
- exact GNO.
Qed.
Lemma cc2_un_ext : forall (v : ccx) ly S (W : world SEGS) (m m' : word -> option byte),
  (forall x, m' x = m x) ->
  cc_un B lit gotw guard STK_REF v ly S W m -> cc_un B lit gotw guard STK_REF v ly S W m'.
Proof.
intros v ly S W m m' He HUN.
assert (HR : forall a, rdW W m' a = rdW W m a)
  by (intros a; exact (cc2_aview_ext SEGS (w_H W) m m' He a)).
assert (HQ : forall a w, rdword (rdW W m) a = Some w -> rdword (rdW W m') a = Some w)
  by (intros a w Ha;
      rewrite (rdword_ext (rdW W m) (rdW W m') a ltac:(intros k Hk; apply HR)); exact Ha).
destruct HUN as [U1 U2 U3 U4]. constructor.
- intros a Ha Hb Hc. rewrite HR. exact (U1 a Ha Hb Hc).
- intros x Hx. pose proof (U2 x Hx) as (P1 & P2 & P3 & P4 & P5).
  split; [exact P1|]. split; [exact (cc2_str_ext _ _ _ _ HR P2)|].
  split; [exact P3|]. split; [exact P4 | exact P5].
- destruct U3 as (S1 & g & S2). split; [exact (HQ _ _ S1) | exists g; exact (HQ _ _ S2)].
- exact U4.
Qed.
(* the atoms of the latch's environment *)
Lemma cc2_ewT : forall (v : ccx) i regs (m : nat) (r : bv 5), Z.of_nat m = bv_unsigned r ->
  ew (cc2_Et lit v i regs) m = getr regs r.
Proof. intros v i regs m r Hm. unfold cc2_Et, cc2_EL. apply ew_Eimg_Ereg_nat. exact Hm. Qed.
Lemma cc2_exT : forall (v : ccx) i regs j, (j < 6)%nat ->
  ew (cc2_Et lit v i regs) (32 + j)%nat =
  nth j [Z_to_bv 64 (x_c v + 356 * i); Z_to_bv 64 (lit F_xbox); Z_to_bv 64 0; Z_to_bv 64 0;
         Z_to_bv 64 0; Z_to_bv 64 (Z.of_nat (length (rc_seg (x_rcs v))))] (Z_to_bv 64 0).
Proof.
intros v i regs j Hj. unfold cc2_Et, cc2_EL. rewrite Eimg_low by (unfold A_TEXT; lia).
apply ew_Ereg_extra.
Qed.
Lemma cc2_seedT : forall (v : ccx) (i : Z) ly3 S3 (W3 : world SEGS) regs3 mem3 md3,
  cc_pre B lit gotw guard STK_REF v ->
  cc2_INV_LATCH v i ly3 S3 W3 regs3 mem3 md3 ->
  img_env VAL A_LIM (cc2_Et lit v i regs3) /\
  st_ok_pi SEGS VAL (cc2_Et lit v i regs3) ss_cc2T
    (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 (BASE + CC_LATCH)) mem3 (seg_rom SEGS))) /\
  sh_ok SEGS cc2_Bx cc2_SH (cc2_Et lit v i regs3) (mrestrict (w_H W3) mem3).
Proof.
intros v i ly3 S3 W3 regs3 mem3 md3 HPRE HINV.
pose proof HINV as (HFI & HUN & Hi & HRC & R8 & R9 & R18 & R19 & R25 & R26 & R27 & Hsp8 & Hsp10).
destruct (cc2_bounds v i ly3 S3 W3 regs3 mem3 md3 HPRE HFI HUN Hi)
  as (Hc4 & Hcc & Hc16 & Hi31 & Happ & HSA & Hpres & Hsp & Hsp47 & Hxb & Hl32).
pose proof asan_consts as (C1 & _).
assert (Hlen : length (rc_seg (cc_at v (i + 1))) = length (rc_seg (x_rcs v)))
  by (unfold cc_at; apply cc_fold_len; lia).
destruct (sa_rconf_n (rdW W3 mem3) (x_c v) (cc_at v (i + 1)) HRC) as (VN & Hl32' & _).
rewrite Hlen in VN, Hl32'.
pose proof (cc2_ewT v i regs3) as EE.
pose proof (cc2_exT v i regs3 0%nat ltac:(lia)) as E32.
pose proof (cc2_exT v i regs3 2%nat ltac:(lia)) as E34.
pose proof (cc2_exT v i regs3 3%nat ltac:(lia)) as E35.
pose proof (cc2_exT v i regs3 4%nat ltac:(lia)) as E36.
pose proof (cc2_exT v i regs3 5%nat ltac:(lia)) as E37.
cbn [Nat.add nth] in E32, E34, E35, E36, E37.
assert (E8 : ew (cc2_Et lit v i regs3) 8%nat = Z_to_bv 64 (x_c v))
  by (rewrite (EE 8%nat 8%bv eq_refl); exact R8).
assert (E9 : ew (cc2_Et lit v i regs3) 9%nat = Z_to_bv 64 (x_c v + seg_spec.RC_N))
  by (rewrite (EE 9%nat 9%bv eq_refl); exact R9).
assert (E19 : ew (cc2_Et lit v i regs3) 19%nat = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (EE 19%nat 19%bv eq_refl); exact R19).
assert (E25 : ew (cc2_Et lit v i regs3) 25%nat = Z_to_bv 64 (356 * i))
  by (rewrite (EE 25%nat 25%bv eq_refl); exact R25).
assert (E26 : ew (cc2_Et lit v i regs3) 26%nat = Z_to_bv 64 i)
  by (rewrite (EE 26%nat 26%bv eq_refl); exact R26).
assert (HBx : U (cc2_Et lit v i regs3) cc2_Bx = SHADOW_OFF)
  by (unfold cc2_Bx; apply U_atom; [exact E19 | unfold SHADOW_OFF; lia]).
split; [unfold cc2_Et, cc2_EL; apply Eimg_env|].
split.
- rewrite restrict_mkst_fx. unfold ss_cc2T. apply pa_entry_st_ok_full.
  + apply regs_ok_rereg; [unfold cc2_Et, cc2_EL; apply regs_ok_Eimg_Ereg | reflexivity |].
    rewrite R27. unfold cc2_sh11.
    rewrite (cc2_shadow_denot _ 9%nat 19%nat (x_c v + seg_spec.RC_N) E9 E19
      ltac:(unfold seg_spec.RC_N, seg_spec.SEG_C_SIZE in *; lia)).
    reflexivity.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_nil].
    exact (cc2_regn _ W3 mem3 (x_c v) _ E9 E37 Hc4 ltac:(unfold CC2_CEIL; lia) ltac:(lia) VN).
  + cbn [pairwise_disjoint all_disjoint]. tauto.
  + exact (cc2_factsok _ (x_c v) i 0 0 0 _ E8 E9 E19 E25 E26 E32 E34 E35 E36 E37 Hc4
             ltac:(unfold CC2_CEIL; lia) Hc16 Hi31 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
- exact (cc2_shok v i W3 mem3 _ Hc4 ltac:(unfold CC2_CEIL; lia) Hi31 Happ HSA HBx E32 E9).
Qed.
(* 0x893b8-0x893d0: check 10, the reload of c->n, i++, s9 += 356, the back edge or the jump to CC_EPI *)
Lemma cc2_latch : forall (v : ccx) (i : Z) ly3 S3 (W3 : world SEGS) regs3 mem3 md3,
  cc_pre B lit gotw guard STK_REF v ->
  (forall fx0 : YK11.FPState, from_EPI (fx := fx0) B lit gotw guard STK_REF v) ->
  (forall fx0 : YK11.FPState, frm0 fx0 -> from_LOOP (fx := fx0) B lit gotw guard STK_REF v (i + 1)) ->
  frm0 fx ->
  cc2_INV_LATCH v i ly3 S3 W3 regs3 mem3 md3 ->
  SRr SEGS W3 (cfg_at SEGS (BASE + CC_LATCH) regs3 mem3 md3) (cc_post B lit gotw guard STK_REF v).
Proof.
intros v i ly3 S3 W3 regs3 mem3 md3 HPRE HEPI HLOOP HFRM HINV.
pose proof HINV as (HFI & HUN & Hi & HRC & R8 & R9 & R18 & R19 & R25 & R26 & R27 & Hsp8 & Hsp10).
destruct (cc2_bounds v i ly3 S3 W3 regs3 mem3 md3 HPRE HFI HUN Hi)
  as (Hc4 & Hcc & Hc16 & Hi31 & Happ & HSA & Hpres & Hsp & Hsp47 & Hxb & Hl32).
destruct (cc2_seedT v i ly3 S3 W3 regs3 mem3 md3 HPRE HINV) as (HEI & HS & SHOK).
pose proof (fi_j _ _ _ _ _ _ _ _ _ _ _ _ HFI) as HJ.
pose proof (cc2_ewT v i regs3) as EE.
pose proof (cc2_exT v i regs3 5%nat ltac:(lia)) as E37. cbn [Nat.add nth] in E37.
assert (E26 : ew (cc2_Et lit v i regs3) 26%nat = Z_to_bv 64 i)
  by (rewrite (EE 26%nat 26%bv eq_refl); exact R26).
assert (E25 : ew (cc2_Et lit v i regs3) 25%nat = Z_to_bv 64 (356 * i))
  by (rewrite (EE 25%nat 25%bv eq_refl); exact R25).
assert (E9 : ew (cc2_Et lit v i regs3) 9%nat = Z_to_bv 64 (x_c v + seg_spec.RC_N))
  by (rewrite (EE 9%nat 9%bv eq_refl); exact R9).
assert (E19 : ew (cc2_Et lit v i regs3) 19%nat = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (EE 19%nat 19%bv eq_refl); exact R19).
assert (HAG : env_agree 32 (Ereg regs3
    [Z_to_bv 64 (x_c v + 356 * i); Z_to_bv 64 (lit F_xbox); Z_to_bv 64 0; Z_to_bv 64 0;
     Z_to_bv 64 0; Z_to_bv 64 (Z.of_nat (length (rc_seg (x_rcs v))))]) (cc2_Et lit v i regs3))
  by (unfold cc2_Et, cc2_EL; split;
      [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (Hlen : length (rc_seg (cc_at v (i + 1))) = length (rc_seg (x_rcs v)))
  by (unfold cc_at; apply cc_fold_len; lia).
destruct (sa_rconf_n (rdW W3 mem3) (x_c v) (cc_at v (i + 1)) HRC) as (_ & Hl32' & _).
rewrite Hlen in Hl32'.
assert (Ua : U (cc2_Et lit v i regs3) (SOff 26 1) = i + 1)
  by (apply (U_atom_off _ 26%nat i 1 E26); lia).
assert (Ub : U (cc2_Et lit v i regs3) (SOff 37 0) = Z.of_nat (length (rc_seg (x_rcs v))))
  by (apply (U_atom _ 37%nat _ E37); lia).
unfold cfg_at, w64.
paj_run_tok RUN HS HJ SHOK cc2_Bspan.
{ cc2_ro_awr. }
cc2_mdv mdv.
cc2_frame HF HEQ1.
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK cc2_Bspan.
- (* the back edge: i + 1 < n *)
  rewrite (cc2_branch_lt_U _ _ _ ltac:(rewrite Ua; lia) ltac:(rewrite Ub; lia)), Ua, Ub in Hc.
  apply Z.ltb_lt in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK cc2_Bspan CC_LOOP.
  { cc2_ro_awr. }
  pmkst HS. cc2_mdv mdk.
  cc2_frame HF HEQ2.
  pose proof (cc2_trans _ _ _ HEQ2 HEQ1) as HEQ.
  pose proof (cc2_aview_ext SEGS (w_H W3) mem3 _ HEQ) as HRD.
  pose proof (cc2_rdw_ext _ _ HRD) as HWD.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs3 _
    [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv] HS HAG ltac:(vm_compute; reflexivity)) as KEPT.
  cbn [ms_regs restrict mkst] in KEPT.
  cc2_rg HS (25%bv : bv 5) T25. cc2_rg HS (26%bv : bv 5) T26.
  cc2_rg HS (27%bv : bv 5) T27.
  rewrite (cc2_shadow_denot _ 9%nat 19%nat (x_c v + seg_spec.RC_N) E9 E19
    ltac:(unfold seg_spec.RC_N, seg_spec.SEG_C_SIZE in *; lia)) in T27.
  rewrite (cc2_den_off _ 25%nat 356 (356 * i) E25 ltac:(lia) ltac:(lia)) in T25.
  rewrite (cc2_den_off _ 26%nat 1 i E26 ltac:(lia) ltac:(lia)) in T26.
  pose proof (HLOOP fx HFRM) as HL. unfold from_LOOP, cc_from in HL.
  apply (HL ly3 S3 W3 _ _ mdk).
  unfold INV_LOOP.
  split; [exact (cc2_fi_ext v ly3 S3 W3 regs3 mem3 md3 _ _ mdk HFI HJ HEQ
                   (KEPT 2%bv ltac:(cbn; tauto)) (KEPT 3%bv ltac:(cbn; tauto))
                   (KEPT 4%bv ltac:(cbn; tauto)))|].
  split; [exact (cc2_un_ext v ly3 S3 W3 mem3 _ HEQ HUN)|].
  split; [unfold cc_n in *; lia|].
  split; [exact (cc2_rconf_ext _ _ _ _ HRD HRC)|].
  split; [rewrite (KEPT 8%bv ltac:(cbn; tauto)); exact R8|].
  split; [rewrite (KEPT 9%bv ltac:(cbn; tauto)); exact R9|].
  split; [rewrite (KEPT 18%bv ltac:(cbn; tauto)); exact R18|].
  split; [rewrite (KEPT 19%bv ltac:(cbn; tauto)); exact R19|].
  split; [rewrite T25; unfold w64; f_equal; lia|].
  split; [rewrite T26; unfold w64; f_equal; lia|].
  split; [exact T27|].
  split; [exact (HWD _ _ Hsp8) | exact (HWD _ _ Hsp10)].
- (* the exit: i + 1 = n, on to the epilogue *)
  rewrite (cc2_branch_lt_U _ _ _ ltac:(rewrite Ua; lia) ltac:(rewrite Ub; lia)), Ua, Ub in Hc.
  apply Z.ltb_ge in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK cc2_Bspan CC_EPI.
  { cc2_ro_awr. }
  pmkst HS. cc2_mdv mdk.
  cc2_frame HF HEQ2.
  pose proof (cc2_trans _ _ _ HEQ2 HEQ1) as HEQ.
  pose proof (cc2_aview_ext SEGS (w_H W3) mem3 _ HEQ) as HRD.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs3 _
    [2%bv; 3%bv; 4%bv] HS HAG ltac:(vm_compute; reflexivity)) as KEPT.
  cbn [ms_regs restrict mkst] in KEPT.
  assert (HE : cc_at v (i + 1) = SegModel.cross_check (x_rcs v)).
  { unfold cc_at. replace (i + 1) with (Z.of_nat (length (rc_seg (x_rcs v))))
      by (unfold cc_n in *; lia).
    apply cc_fold_all. }
  pose proof (HEPI fx) as HEp. unfold from_EPI, cc_from in HEp.
  apply (HEp ly3 S3 W3 _ _ mdk).
  unfold INV_EPI.
  split; [exact (cc2_fi_ext v ly3 S3 W3 regs3 mem3 md3 _ _ mdk HFI HJ HEQ
                   (KEPT 2%bv ltac:(cbn; tauto)) (KEPT 3%bv ltac:(cbn; tauto))
                   (KEPT 4%bv ltac:(cbn; tauto)))|].
  rewrite <- HE. exact (cc2_rconf_ext _ _ _ _ HRD HRC).
Qed.



(* ===================== 7. what a store inside the block keeps ===================== *)
Lemma cc2_rd_out : forall (H : word -> bool) rs E (m m' : word -> option byte),
  frame_of E rs m m' -> forall a, 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a ->
  aview SEGS H m' a = aview SEGS H m a.
Proof.
intros H rs E m m' HF a Ha Hno.
assert (Hno' : ~ in_wrange E rs (bv_unsigned (Z_to_bv 64 a)))
  by (rewrite unsigned_lit_small by lia; exact Hno).
unfold aview, mbyte, mrestrict. cbv beta. rewrite (HF (Z_to_bv 64 a) Hno'). reflexivity.
Qed.
(* a byte of a live block is no image byte, so no store in the block touches the image *)
Lemma cc2_blk_noimg : forall ly S (W : world SEGS) mem md a p n,
  AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) -> p <= a < p + req_size n -> ~ in_img SEGS a.
Proof.
intros ly S W mem md a p n HAR Hin Ha.
destruct (al_client_img _ _ LAWS ly S W mem md a HAR
  (or_introl (ex_intro _ p (ex_intro _ n (conj Hin Ha))))) as [_ Hni]. exact Hni.
Qed.
Lemma cc2_strz_ext_r : forall (rd rd' : reader) p s,
  (forall k, (k < length s + 1)%nat -> rd' (p + Z.of_nat k) = rd (p + Z.of_nat k)) ->
  sa_strz rd p s -> sa_strz rd' p s.
Proof.
intros rd rd' p s He (H1 & H2). split; [|exact H2].
intros k Hk. rewrite length_app in Hk. cbn [length] in Hk. rewrite He by lia.
exact (H1 k ltac:(rewrite length_app; cbn [length]; lia)).
Qed.
(* the facts of a cut after a store inside the block: the read-only bytes and the literals are image bytes,
   which no byte of a live block is; the stack-protector cells come from AR at the new state *)
Lemma cc2_un_store : forall (v : ccx) ly S (W : world SEGS) m md m' md',
  AR SEGS B ly S W m md -> AR SEGS B ly S W m' md' ->
  cc_un B lit gotw guard STK_REF v ly S W m ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (x_c v <= a < x_c v + seg_spec.SEG_C_SIZE) -> rdW W m' a = rdW W m a) ->
  cc_un B lit gotw guard STK_REF v ly S W m'.
Proof.
intros v ly S W m md m' md' HAR HAR' HUN Hext.
pose proof (un_heap _ _ _ _ _ _ _ _ _ _ HUN) as HH.
pose proof HH as (b & n & Hin & Hlo & Hhi).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & Hb4 & Hbc & _ & _ & _ & Hn0).
pose proof (req_size_pos0 n ltac:(lia)) as (Hrq1 & Hrq2).
assert (HNI : forall a, x_c v <= a < x_c v + seg_spec.SEG_C_SIZE -> ~ in_img SEGS a)
  by (intros a Ha; apply (cc2_blk_noimg ly S W m md a b n HAR Hin); lia).
assert (HIMG : forall a, in_img SEGS a ->
  0 <= a < 2 ^ 64 /\ ~ (x_c v <= a < x_c v + seg_spec.SEG_C_SIZE)).
{ intros a Hi. pose proof (pa_segs_low a Hi) as Hlow. unfold kLowMemEnd in Hlow.
  split; [lia|]. intros Hb'. exact (HNI a Hb' Hi). }
destruct HUN as [U1 U2 U3 U4]. constructor.
- intros a Ha Hb' Hc.
  assert (Himg : in_img SEGS a).
  { destruct Ha as [(s & Hs & Hw & Hr) | Hr];
      [exists s; split; [exact Hs | exact Hr] | exact (ROIMG a Hr)]. }
  destruct (HIMG a Himg) as (Ha1 & Ha2). rewrite (Hext a Ha1 Ha2). exact (U1 a Ha Hb' Hc).
- intros x Hx. pose proof (U2 x Hx) as (P1 & P2 & P3 & P4 & P5).
  split; [exact P1|]. split.
  + split.
    * apply (cc2_strz_ext_r (rdW W m)); [|exact (proj1 P2)].
      intros k Hk. destruct (P5 (lit x + Z.of_nat k) ltac:(lia)) as (Hi & _ & _).
      destruct (HIMG _ Hi) as (Ha1 & Ha2). exact (Hext _ Ha1 Ha2).
    * exact (sa_tail_of_romtail SEGS (w_H W) m' _ P4).
  + split; [exact P3|]. split; [exact P4 | exact P5].
- exact (SSPAR ly S W m' md' HAR').
- exact U4.
Qed.
(* the frame part of a cut after a run that wrote only inside the block *)
Lemma cc2_fi_stk : forall (v : ccx) ly S (W : world SEGS) regs m md regs' m' md',
  cc_fi B lit gotw guard STK_REF v ly S W regs m md ->
  ajournal SEGS B (cc_STK STK_REF) (cc_sp0 v) (cc_FP v) (x_ly v) (x_S v) (x_W v) (x_mem v) (x_md v) []
    ly S W m' md' 0 ->
  (forall a, cc_sp0 v - 128 <= a < cc_sp0 v -> rdW W m' a = rdW W m a) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  cc_fi B lit gotw guard STK_REF v ly S W regs' m' md'.
Proof.
intros v ly S W regs m md regs' m' md' [J1 G2 G3 G4 GSV GNO] HJ He E2 E3 E4. constructor.
- exact HJ.
- rewrite E2; exact G2.
- rewrite E3; exact G3.
- rewrite E4; exact G4.
- intros j r Hj.
  assert (Hj13 : (j < 13)%nat).
  { pose proof (proj1 (nth_error_Some cc_saved j) ltac:(rewrite Hj; discriminate)) as Hl.
    unfold cc_saved in Hl. cbn [length] in Hl. lia. }
  rewrite <- (GSV j r Hj). apply rdword_ext. intros k Hk. apply He. lia.
- exact GNO.
Qed.
(* every byte of the segment array is a byte this call may write *)
Lemma cc2_awr_blk : forall (v : ccx) ly S (W : world SEGS) mem md STK sp0 bl0 fr0 own a,
  AR SEGS B ly S W mem md -> sa_heap B ly S (x_c v) seg_spec.SEG_C_SIZE ->
  x_c v <= a < x_c v + seg_spec.RSEG_SIZE * 32 ->
  awr_byte SEGS B STK sp0 (cc_FP v) bl0 (ablocks B ly S) fr0 ly own a.
Proof.
intros v ly S W mem md STK sp0 bl0 fr0 own a HAR HH Ha.
pose proof HH as (b & n & Hin & Hlo & Hhi).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn0).
pose proof (req_size_pos0 n ltac:(lia)) as (Hrq1 & Hrq2).
right. left. split.
- unfold cc_FP, cross_check_W, inFP.
  exists (x_c v, x_c v + seg_spec.RSEG_SIZE * 32).
  split; [left; reflexivity | cbn [fst snd]; lia].
- exists b, n. split; [exact Hin|].
  unfold seg_spec.SEG_C_SIZE, seg_spec.RSEG_SIZE in *. lia.
Qed.

(* ===================== 8. the model-drop arm, 0x89354-0x8937c ===================== *)
Definition cc2_INV_A1 (v : ccx) (i : Z)
  (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (regs3 : bvmap 5 word) (mem3 : word -> option byte)
  (md3 : Model) : Prop :=
  cc_fi B lit gotw guard STK_REF v ly3 S3 W3 regs3 mem3 md3 /\
  cc_un B lit gotw guard STK_REF v ly3 S3 W3 mem3 /\
  0 <= i < cc_n v /\
  rs_model_set (cc2_sgi v i) = true /\
  rs_role_set (cc2_sgi v i) && (rs_role (cc2_sgi v i) =? 4) = false /\
  sa_rconf (rdW W3 mem3) (x_c v)
    (SegModel.refuse (cc_at v i) 0 F_xmodel
       [AS (rs_name (cc2_sgi v i)); AS (rs_model (cc2_sgi v i))]) /\
  getr regs3 8 = w64 (x_c v) /\
  getr regs3 9 = w64 (x_c v + seg_spec.RC_N) /\
  getr regs3 18 = w64 (lit F_xmodel) /\
  getr regs3 19 = w64 SHADOW_OFF /\
  getr regs3 21 = w64 (x_c v + 356 * i + seg_spec.RS_MODEL_SET) /\
  getr regs3 22 = w64 (x_c v + 356 * i + seg_spec.RS_MODEL) /\
  getr regs3 25 = w64 (356 * i) /\
  getr regs3 26 = w64 i /\
  getr regs3 27 = w64 (SHADOW_OFF + (x_c v + seg_spec.RC_N) / 8) /\
  rdword (rdW W3 mem3) (cc_sp0 v - 120) = Some 3 /\
  rdword (rdW W3 mem3) (cc_sp0 v - 112) = Some (lit F_xbox).
Lemma cc2_arm1 : forall (v : ccx) (i : Z) ly3 S3 (W3 : world SEGS) regs3 mem3 md3,
  cc_pre B lit gotw guard STK_REF v ->
  (forall fx0 : YK11.FPState, from_EPI (fx := fx0) B lit gotw guard STK_REF v) ->
  (forall fx0 : YK11.FPState, frm0 fx0 -> from_LOOP (fx := fx0) B lit gotw guard STK_REF v (i + 1)) ->
  frm0 fx ->
  cc2_INV_A1 v i ly3 S3 W3 regs3 mem3 md3 ->
  SRr SEGS W3 (cfg_at SEGS (BASE + CC_RET1) regs3 mem3 md3) (cc_post B lit gotw guard STK_REF v).
Proof.
intros v i ly3 S3 W3 regs3 mem3 md3 HPRE HEPI HLOOP HFRM HINV.
pose proof HINV as (HFI & HUN & Hi & HMS & HRS & HRC & R8 & R9 & R18 & R19 & R21 & R22 & R25 & R26 & R27
                    & Hsp8 & Hsp10).
destruct (cc2_bounds v i ly3 S3 W3 regs3 mem3 md3 HPRE HFI HUN Hi)
  as (Hc4 & Hcc & Hc16 & Hi31 & Happ & HSA & Hpres & Hsp & Hsp47 & Hxb & Hl32).
pose proof asan_consts as (C1 & _).
pose proof (fi_j _ _ _ _ _ _ _ _ _ _ _ _ HFI) as HJ.
pose proof (proj1 HJ) as HAR.
pose proof (un_heap _ _ _ _ _ _ _ _ _ _ HUN) as HH.
assert (Hseg : rc_seg (SegModel.refuse (cc_at v i) 0 F_xmodel
                 [AS (rs_name (cc2_sgi v i)); AS (rs_model (cc2_sgi v i))]) = rc_seg (cc_at v i))
  by apply refuse_seg.
assert (Hlf : length (rc_seg (cc_at v i)) = length (rc_seg (x_rcs v)))
  by (unfold cc_at; apply cc_fold_len; lia).
assert (Hlt : (Z.to_nat i < length (rc_seg (cc_at v i)))%nat) by (unfold cc_n in Hi; lia).
pose proof (cc2_ewT v i regs3) as EE.
pose proof (cc2_exT v i regs3 0%nat ltac:(lia)) as E32.
pose proof (cc2_exT v i regs3 2%nat ltac:(lia)) as E34.
pose proof (cc2_exT v i regs3 3%nat ltac:(lia)) as E35.
pose proof (cc2_exT v i regs3 4%nat ltac:(lia)) as E36.
pose proof (cc2_exT v i regs3 5%nat ltac:(lia)) as E37.
cbn [Nat.add nth] in E32, E34, E35, E36, E37.
assert (E8 : ew (cc2_Et lit v i regs3) 8%nat = Z_to_bv 64 (x_c v))
  by (rewrite (EE 8%nat 8%bv eq_refl); exact R8).
assert (E9 : ew (cc2_Et lit v i regs3) 9%nat = Z_to_bv 64 (x_c v + seg_spec.RC_N))
  by (rewrite (EE 9%nat 9%bv eq_refl); exact R9).
assert (E19 : ew (cc2_Et lit v i regs3) 19%nat = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (EE 19%nat 19%bv eq_refl); exact R19).
assert (E25 : ew (cc2_Et lit v i regs3) 25%nat = Z_to_bv 64 (356 * i))
  by (rewrite (EE 25%nat 25%bv eq_refl); exact R25).
assert (E26 : ew (cc2_Et lit v i regs3) 26%nat = Z_to_bv 64 i)
  by (rewrite (EE 26%nat 26%bv eq_refl); exact R26).
assert (U32 : base_val (cc2_Et lit v i regs3) (Some 32%nat) = x_c v + 356 * i)
  by (cbn [base_val]; rewrite E32; apply unsigned_lit_small;
      unfold seg_spec.SEG_C_SIZE in *; lia).
assert (HBx : U (cc2_Et lit v i regs3) cc2_Bx = SHADOW_OFF)
  by (unfold cc2_Bx; apply U_atom; [exact E19 | unfold SHADOW_OFF; lia]).
assert (HEI : img_env VAL A_LIM (cc2_Et lit v i regs3))
  by (unfold cc2_Et, cc2_EL; apply Eimg_env).
assert (SHOK : sh_ok SEGS cc2_Bx cc2_SH (cc2_Et lit v i regs3) (mrestrict (w_H W3) mem3))
  by exact (cc2_shok v i W3 mem3 _ Hc4 ltac:(unfold CC2_CEIL; lia) Hi31 Happ HSA HBx E32 E9).
assert (HAG : env_agree 32 (Ereg regs3
    [Z_to_bv 64 (x_c v + 356 * i); Z_to_bv 64 (lit F_xbox); Z_to_bv 64 0; Z_to_bv 64 0;
     Z_to_bv 64 0; Z_to_bv 64 (Z.of_nat (length (rc_seg (x_rcs v))))]) (cc2_Et lit v i regs3))
  by (unfold cc2_Et, cc2_EL; split;
      [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (HS : st_ok_pi SEGS VAL (cc2_Et lit v i regs3) ss_cc2A1
   (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 (BASE + CC_RET1)) mem3 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_cc2A1. apply pa_entry_st_ok_full.
  - apply regs_ok_rereg; [ | reflexivity | ].
    + apply regs_ok_rereg; [unfold cc2_Et, cc2_EL; apply regs_ok_Eimg_Ereg | reflexivity | ].
      rewrite R21.
      rewrite (cc2_den_off _ 32%nat 60 (x_c v + 356 * i) E32
        ltac:(unfold seg_spec.SEG_C_SIZE in *; lia) ltac:(unfold seg_spec.SEG_C_SIZE in *; lia)).
      unfold seg_spec.RS_MODEL_SET. reflexivity.
    + rewrite R22.
      rewrite (cc2_den_off _ 32%nat 36 (x_c v + 356 * i) E32
        ltac:(unfold seg_spec.SEG_C_SIZE in *; lia) ltac:(unfold seg_spec.SEG_C_SIZE in *; lia)).
      unfold seg_spec.RS_MODEL. reflexivity.
  - vm_compute. reflexivity.
  - unfold cc2_A1mem. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold cc2_msR, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite U32. split; [lia|]. split; [unfold seg_spec.SEG_C_SIZE in *; lia|].
      split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres.
      unfold seg_spec.SEG_C_SIZE; lia.
    + unfold cc2_mR, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite U32. split; [lia|]. split; [unfold seg_spec.SEG_C_SIZE in *; lia|].
      split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres.
      unfold seg_spec.SEG_C_SIZE; lia.
  - unfold cc2_A1mem. cbn [pairwise_disjoint all_disjoint].
    unfold cc2_msR, cc2_mR, extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite U32. repeat split; try exact I. lia.
  - exact (cc2_factsok _ (x_c v) i 0 0 0 _ E8 E9 E19 E25 E26 E32 E34 E35 E36 E37 Hc4
             ltac:(unfold CC2_CEIL; lia) Hc16 Hi31 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). }
unfold cfg_at, w64.
paj_run_to_tok RUNTO HS HJ SHOK cc2_Bspan CC_LATCH.
{ unfold ss_cc2A1, cc2_A1mem. cbn [ss_mem].
  apply (YCbq.awr_ok_cons_gen SEGS B _ _ _ _ _ _ _ _ _ _ _ 32%nat (x_c v + 356 * i));
    [reflexivity | exact U32 | | ].
  - intros a Ha. unfold cc2_msR in Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
    apply (cc2_awr_blk v ly3 S3 W3 mem3 md3 _ _ _ _ _ a HAR HH).
    unfold seg_spec.RSEG_SIZE; lia.
  - apply (YCbq.awr_ok_cons_gen SEGS B _ _ _ _ _ _ _ _ _ _ _ 32%nat (x_c v + 356 * i));
      [reflexivity | exact U32 | | apply awr_ok_nil].
    intros a Ha. unfold cc2_mR in Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
    apply (cc2_awr_blk v ly3 S3 W3 mem3 md3 _ _ _ _ _ a HAR HH).
    unfold seg_spec.RSEG_SIZE; lia. }
pmkst HS. cc2_mdv mdk.
assert (HOUT : forall a, 0 <= a < 2 ^ 64 ->
  ~ (x_c v + 356 * i + 36 <= a < x_c v + 356 * i + 37) ->
  ~ (x_c v + 356 * i + 60 <= a < x_c v + 356 * i + 64) ->
  rdW W3 (ms_mem ms) a = rdW W3 mem3 a).
{ intros a Ha H1 H2. apply (cc2_rd_out (w_H W3) (ss_mem ss_cc2A1) _ _ _ HF a Ha).
  intros (r & Hr & Hw). unfold ss_cc2A1, cc2_A1mem in Hr. cbn [ss_mem] in Hr.
  destruct Hr as [<- | [<- | []]];
    [unfold cc2_msR in Hw | unfold cc2_mR in Hw];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hw; rewrite U32 in Hw;
    [apply H2 | apply H1]; lia. }
assert (HSTK : forall a, cc_sp0 v - 128 <= a < cc_sp0 v -> rdW W3 (ms_mem ms) a = rdW W3 mem3 a)
  by (intros a Ha; apply HOUT; unfold seg_spec.SEG_C_SIZE in *; lia).
assert (HOUTB : forall a, 0 <= a < 2 ^ 64 ->
  ~ (x_c v <= a < x_c v + seg_spec.SEG_C_SIZE) -> rdW W3 (ms_mem ms) a = rdW W3 mem3 a)
  by (intros a Ha Hb'; apply HOUT; unfold seg_spec.SEG_C_SIZE in *; lia).
cc2_rgn HS 0%nat RG0.
cc2_rgn HS 1%nat RG1.
pose proof (field_of_region _ _ 32%nat (x_c v + 356 * i) _ _ _ _ _ 60 4%N (SLit 0) 0 RG0 U32
  ltac:(cc2_in) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as VMS.
pose proof (field_of_region _ _ 32%nat (x_c v + 356 * i) _ _ _ _ _ 36 1%N (SLit 0) 0 RG1 U32
  ltac:(cc2_in) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as VMM.
pose proof (regs_kept_of_st_ok_pi _ _ _ regs3 _
  [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 25%bv; 26%bv; 27%bv] HS HAG
  ltac:(vm_compute; reflexivity)) as KEPT.
cbn [ms_regs restrict mkst] in KEPT.
assert (HRCn : sa_rconf (rdW W3 (ms_mem ms)) (x_c v) (cc_at v (i + 1))).
{ assert (Hstep : cc_at v (i + 1) = r_upd (SegModel.refuse (cc_at v i) 0 F_xmodel
      [AS (rs_name (cc2_sgi v i)); AS (rs_model (cc2_sgi v i))]) (Z.to_nat i) rs_drop_model).
  { unfold cc_at. rewrite cc_fold_S by lia.
    exact (r_cross_seg_model (cc_fold (x_rcs v) i) (Z.to_nat i) HMS HRS). }
  rewrite Hstep.
  apply (sa_rconf_drop_model (rdW W3 mem3) (rdW W3 (ms_mem ms)) (x_c v) _ (Z.to_nat i) HRC
    ltac:(rewrite Hseg; exact Hlt)).
  - intros k Hk. rewrite Z2Nat.id by lia. unfold seg_spec.RS_MODEL_SET.
    replace (x_c v + 356 * i + 60 + k) with ((x_c v + 356 * i + 60) + Z.of_nat (Z.to_nat k))
      by (rewrite Z2Nat.id by lia; lia).
    apply (cc2_zero_rd SEGS (w_H W3) (ms_mem ms) (x_c v + 356 * i + 60) 4%nat VMS). lia.
  - rewrite Z2Nat.id by lia. unfold seg_spec.RS_MODEL.
    replace (x_c v + 356 * i + 36) with ((x_c v + 356 * i + 36) + Z.of_nat 0%nat) by (cbn; lia).
    apply (cc2_zero_rd SEGS (w_H W3) (ms_mem ms) (x_c v + 356 * i + 36) 1%nat VMM). lia.
  - intros a Ha Hne Hnr. rewrite Z2Nat.id in Hne, Hnr by lia.
    unfold seg_spec.RS_MODEL in Hne. unfold seg_spec.RS_MODEL_SET in Hnr.
    apply HOUT; unfold seg_spec.SEG_C_SIZE in *; lia. }
apply (cc2_latch v i ly3 S3 W3 _ _ mdk HPRE HEPI HLOOP HFRM).
unfold cc2_INV_LATCH.
split; [exact (cc2_fi_stk v ly3 S3 W3 regs3 mem3 md3 _ _ mdk HFI HJ HSTK
                 (KEPT 2%bv ltac:(cbn; tauto)) (KEPT 3%bv ltac:(cbn; tauto))
                 (KEPT 4%bv ltac:(cbn; tauto)))|].
split; [exact (cc2_un_store v ly3 S3 W3 mem3 md3 _ mdk HAR (proj1 HJ) HUN HOUTB)|].
split; [exact Hi|].
split; [exact HRCn|].
split; [rewrite (KEPT 8%bv ltac:(cbn; tauto)); exact R8|].
split; [rewrite (KEPT 9%bv ltac:(cbn; tauto)); exact R9|].
split; [rewrite (KEPT 18%bv ltac:(cbn; tauto)); exact R18|].
split; [rewrite (KEPT 19%bv ltac:(cbn; tauto)); exact R19|].
split; [rewrite (KEPT 25%bv ltac:(cbn; tauto)); exact R25|].
split; [rewrite (KEPT 26%bv ltac:(cbn; tauto)); exact R26|].
split; [rewrite (KEPT 27%bv ltac:(cbn; tauto)); exact R27|].
split.
- exact (cc2_rdw_on (rdW W3 mem3) (rdW W3 (ms_mem ms)) (cc_sp0 v - 120) 3
    ltac:(intros x Hx; apply HSTK; lia) Hsp8).
- exact (cc2_rdw_on (rdW W3 mem3) (rdW W3 (ms_mem ms)) (cc_sp0 v - 112) (lit F_xbox)
    ltac:(intros x Hx; apply HSTK; lia) Hsp10).
Qed.

(* ===================== 9. the box arm, 0x893a0-0x893b4 ===================== *)
Definition cc2_INV_A2 (v : ccx) (i : Z)
  (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (regs3 : bvmap 5 word) (mem3 : word -> option byte)
  (md3 : Model) : Prop :=
  cc_fi B lit gotw guard STK_REF v ly3 S3 W3 regs3 mem3 md3 /\
  cc_un B lit gotw guard STK_REF v ly3 S3 W3 mem3 /\
  0 <= i < cc_n v /\
  rs_model_set (cc2_sgi v i) = false /\
  rs_role_set (cc2_sgi v i) && (rs_role (cc2_sgi v i) =? 4) = true /\
  sa_rconf (rdW W3 mem3) (x_c v)
    (SegModel.refuse (cc_at v i) 0 F_xbox [AS (rs_name (cc2_sgi v i))]) /\
  getr regs3 8 = w64 (x_c v) /\
  getr regs3 9 = w64 (x_c v + seg_spec.RC_N) /\
  getr regs3 18 = w64 (lit F_xmodel) /\
  getr regs3 19 = w64 SHADOW_OFF /\
  getr regs3 20 = w64 (x_c v + 356 * i) /\
  getr regs3 23 = w64 (SHADOW_OFF + (x_c v + 356 * i + seg_spec.RS_ROLE_SET) / 8) /\
  getr regs3 24 = w64 (SHADOW_OFF + (x_c v + 356 * i + seg_spec.RS_ROLE) / 8) /\
  getr regs3 25 = w64 (356 * i) /\
  getr regs3 26 = w64 i /\
  getr regs3 27 = w64 (SHADOW_OFF + (x_c v + seg_spec.RC_N) / 8) /\
  rdword (rdW W3 mem3) (cc_sp0 v - 120) = Some 3 /\
  rdword (rdW W3 mem3) (cc_sp0 v - 112) = Some (lit F_xbox).
Lemma cc2_arm2 : forall (v : ccx) (i : Z) ly3 S3 (W3 : world SEGS) regs3 mem3 md3,
  cc_pre B lit gotw guard STK_REF v ->
  (forall fx0 : YK11.FPState, from_EPI (fx := fx0) B lit gotw guard STK_REF v) ->
  (forall fx0 : YK11.FPState, frm0 fx0 -> from_LOOP (fx := fx0) B lit gotw guard STK_REF v (i + 1)) ->
  frm0 fx ->
  cc2_INV_A2 v i ly3 S3 W3 regs3 mem3 md3 ->
  SRr SEGS W3 (cfg_at SEGS (BASE + CC_RET2) regs3 mem3 md3) (cc_post B lit gotw guard STK_REF v).
Proof.
intros v i ly3 S3 W3 regs3 mem3 md3 HPRE HEPI HLOOP HFRM HINV.
pose proof HINV as (HFI & HUN & Hi & HMS & HRS & HRC & R8 & R9 & R18 & R19 & R20 & R23 & R24 & R25 & R26
                    & R27 & Hsp8 & Hsp10).
destruct (cc2_bounds v i ly3 S3 W3 regs3 mem3 md3 HPRE HFI HUN Hi)
  as (Hc4 & Hcc & Hc16 & Hi31 & Happ & HSA & Hpres & Hsp & Hsp47 & Hxb & Hl32).
pose proof asan_consts as (C1 & _).
pose proof (fi_j _ _ _ _ _ _ _ _ _ _ _ _ HFI) as HJ.
pose proof (proj1 HJ) as HAR.
pose proof (un_heap _ _ _ _ _ _ _ _ _ _ HUN) as HH.
assert (Hseg : rc_seg (SegModel.refuse (cc_at v i) 0 F_xbox [AS (rs_name (cc2_sgi v i))])
               = rc_seg (cc_at v i)) by apply refuse_seg.
assert (Hlf : length (rc_seg (cc_at v i)) = length (rc_seg (x_rcs v)))
  by (unfold cc_at; apply cc_fold_len; lia).
assert (Hlt : (Z.to_nat i < length (rc_seg (cc_at v i)))%nat) by (unfold cc_n in Hi; lia).
pose proof (cc2_ewT v i regs3) as EE.
pose proof (cc2_exT v i regs3 0%nat ltac:(lia)) as E32.
pose proof (cc2_exT v i regs3 2%nat ltac:(lia)) as E34.
pose proof (cc2_exT v i regs3 3%nat ltac:(lia)) as E35.
pose proof (cc2_exT v i regs3 4%nat ltac:(lia)) as E36.
pose proof (cc2_exT v i regs3 5%nat ltac:(lia)) as E37.
cbn [Nat.add nth] in E32, E34, E35, E36, E37.
assert (E8 : ew (cc2_Et lit v i regs3) 8%nat = Z_to_bv 64 (x_c v))
  by (rewrite (EE 8%nat 8%bv eq_refl); exact R8).
assert (E9 : ew (cc2_Et lit v i regs3) 9%nat = Z_to_bv 64 (x_c v + seg_spec.RC_N))
  by (rewrite (EE 9%nat 9%bv eq_refl); exact R9).
assert (E19 : ew (cc2_Et lit v i regs3) 19%nat = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (EE 19%nat 19%bv eq_refl); exact R19).
assert (E25 : ew (cc2_Et lit v i regs3) 25%nat = Z_to_bv 64 (356 * i))
  by (rewrite (EE 25%nat 25%bv eq_refl); exact R25).
assert (E26 : ew (cc2_Et lit v i regs3) 26%nat = Z_to_bv 64 i)
  by (rewrite (EE 26%nat 26%bv eq_refl); exact R26).
assert (U32 : base_val (cc2_Et lit v i regs3) (Some 32%nat) = x_c v + 356 * i)
  by (cbn [base_val]; rewrite E32; apply unsigned_lit_small;
      unfold seg_spec.SEG_C_SIZE in *; lia).
assert (HBx : U (cc2_Et lit v i regs3) cc2_Bx = SHADOW_OFF)
  by (unfold cc2_Bx; apply U_atom; [exact E19 | unfold SHADOW_OFF; lia]).
assert (HEI : img_env VAL A_LIM (cc2_Et lit v i regs3))
  by (unfold cc2_Et, cc2_EL; apply Eimg_env).
assert (SHOK : sh_ok SEGS cc2_Bx cc2_SH (cc2_Et lit v i regs3) (mrestrict (w_H W3) mem3))
  by exact (cc2_shok v i W3 mem3 _ Hc4 ltac:(unfold CC2_CEIL; lia) Hi31 Happ HSA HBx E32 E9).
assert (HAG : env_agree 32 (Ereg regs3
    [Z_to_bv 64 (x_c v + 356 * i); Z_to_bv 64 (lit F_xbox); Z_to_bv 64 0; Z_to_bv 64 0;
     Z_to_bv 64 0; Z_to_bv 64 (Z.of_nat (length (rc_seg (x_rcs v))))]) (cc2_Et lit v i regs3))
  by (unfold cc2_Et, cc2_EL; split;
      [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (HS : st_ok_pi SEGS VAL (cc2_Et lit v i regs3) ss_cc2A2
   (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 (BASE + CC_RET2)) mem3 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_cc2A2. apply pa_entry_st_ok_full.
  - apply regs_ok_rereg; [ | reflexivity | ].
    + apply regs_ok_rereg; [ | reflexivity | ].
      * apply regs_ok_rereg; [unfold cc2_Et, cc2_EL; apply regs_ok_Eimg_Ereg | reflexivity | ].
        rewrite R20.
        rewrite (cc2_den_off _ 32%nat 0 (x_c v + 356 * i) E32
          ltac:(unfold seg_spec.SEG_C_SIZE in *; lia) ltac:(unfold seg_spec.SEG_C_SIZE in *; lia)).
        rewrite Z.add_0_r. reflexivity.
      * rewrite R23. unfold cc2_shx.
        rewrite (cc2_shadow_denot_off _ 32%nat 19%nat (x_c v + 356 * i) 20 E32 E19
          ltac:(unfold seg_spec.SEG_C_SIZE in *; lia) ltac:(unfold seg_spec.SEG_C_SIZE in *; lia)).
        unfold seg_spec.RS_ROLE_SET. reflexivity.
    + rewrite R24. unfold cc2_shx.
      rewrite (cc2_shadow_denot_off _ 32%nat 19%nat (x_c v + 356 * i) 16 E32 E19
        ltac:(unfold seg_spec.SEG_C_SIZE in *; lia) ltac:(unfold seg_spec.SEG_C_SIZE in *; lia)).
      unfold seg_spec.RS_ROLE. reflexivity.
  - vm_compute. reflexivity.
  - unfold cc2_A2mem. apply Forall_cons; [|apply Forall_nil].
    unfold cc2_rR, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite U32. split; [lia|]. split; [unfold seg_spec.SEG_C_SIZE in *; lia|].
    split; [|apply Forall_nil].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. unfold seg_spec.SEG_C_SIZE; lia.
  - unfold cc2_A2mem. cbn [pairwise_disjoint all_disjoint]. tauto.
  - exact (cc2_factsok _ (x_c v) i 0 0 0 _ E8 E9 E19 E25 E26 E32 E34 E35 E36 E37 Hc4
             ltac:(unfold CC2_CEIL; lia) Hc16 Hi31 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). }
unfold cfg_at, w64.
paj_run_to_tok RUNTO HS HJ SHOK cc2_Bspan CC_LATCH.
{ unfold ss_cc2A2, cc2_A2mem. cbn [ss_mem].
  apply (YCbq.awr_ok_cons_gen SEGS B _ _ _ _ _ _ _ _ _ _ _ 32%nat (x_c v + 356 * i));
    [reflexivity | exact U32 | | apply awr_ok_nil].
  intros a Ha. unfold cc2_rR in Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
  apply (cc2_awr_blk v ly3 S3 W3 mem3 md3 _ _ _ _ _ a HAR HH).
  unfold seg_spec.RSEG_SIZE; lia. }
pmkst HS. cc2_mdv mdk.
assert (HOUT : forall a, 0 <= a < 2 ^ 64 ->
  ~ (x_c v + 356 * i + 16 <= a < x_c v + 356 * i + 24) ->
  rdW W3 (ms_mem ms) a = rdW W3 mem3 a).
{ intros a Ha H1. apply (cc2_rd_out (w_H W3) (ss_mem ss_cc2A2) _ _ _ HF a Ha).
  intros (r & Hr & Hw). unfold ss_cc2A2, cc2_A2mem in Hr. cbn [ss_mem] in Hr.
  destruct Hr as [<- | []]. unfold cc2_rR in Hw.
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hw. rewrite U32 in Hw. apply H1. lia. }
assert (HSTK : forall a, cc_sp0 v - 128 <= a < cc_sp0 v -> rdW W3 (ms_mem ms) a = rdW W3 mem3 a)
  by (intros a Ha; apply HOUT; unfold seg_spec.SEG_C_SIZE in *; lia).
assert (HOUTB : forall a, 0 <= a < 2 ^ 64 ->
  ~ (x_c v <= a < x_c v + seg_spec.SEG_C_SIZE) -> rdW W3 (ms_mem ms) a = rdW W3 mem3 a)
  by (intros a Ha Hb'; apply HOUT; unfold seg_spec.SEG_C_SIZE in *; lia).
cc2_rgn HS 0%nat RG0.
pose proof (field_of_region _ _ 32%nat (x_c v + 356 * i) _ _ _ _ _ 16 4%N (SLit 0) 0 RG0 U32
  ltac:(cc2_in) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as VMR1.
pose proof (field_of_region _ _ 32%nat (x_c v + 356 * i) _ _ _ _ _ 20 4%N (SLit 0) 0 RG0 U32
  ltac:(cc2_in) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as VMR2.
pose proof (regs_kept_of_st_ok_pi _ _ _ regs3 _
  [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 25%bv; 26%bv; 27%bv] HS HAG
  ltac:(vm_compute; reflexivity)) as KEPT.
cbn [ms_regs restrict mkst] in KEPT.
assert (HRCn : sa_rconf (rdW W3 (ms_mem ms)) (x_c v) (cc_at v (i + 1))).
{ assert (Hstep : cc_at v (i + 1) = r_upd (SegModel.refuse (cc_at v i) 0 F_xbox
      [AS (rs_name (cc2_sgi v i))]) (Z.to_nat i) rs_drop_role).
  { unfold cc_at. rewrite cc_fold_S by lia.
    exact (r_cross_seg_box (cc_fold (x_rcs v) i) (Z.to_nat i) HMS HRS). }
  rewrite Hstep.
  apply (sa_rconf_drop_role (rdW W3 mem3) (rdW W3 (ms_mem ms)) (x_c v) _ (Z.to_nat i) HRC
    ltac:(rewrite Hseg; exact Hlt)).
  - intros k Hk. rewrite Z2Nat.id by lia. unfold seg_spec.RS_ROLE.
    destruct (Z_lt_dec k 4) as [Hk4 | Hk4].
    + replace (x_c v + 356 * i + 16 + k) with ((x_c v + 356 * i + 16) + Z.of_nat (Z.to_nat k))
        by (rewrite Z2Nat.id by lia; lia).
      apply (cc2_zero_rd SEGS (w_H W3) (ms_mem ms) (x_c v + 356 * i + 16) 4%nat VMR1). lia.
    + replace (x_c v + 356 * i + 16 + k) with ((x_c v + 356 * i + 20) + Z.of_nat (Z.to_nat (k - 4)))
        by (rewrite Z2Nat.id by lia; lia).
      apply (cc2_zero_rd SEGS (w_H W3) (ms_mem ms) (x_c v + 356 * i + 20) 4%nat VMR2). lia.
  - intros a Ha Hnr. rewrite Z2Nat.id in Hnr by lia. unfold seg_spec.RS_ROLE in Hnr.
    apply HOUT; unfold seg_spec.SEG_C_SIZE in *; lia. }
apply (cc2_latch v i ly3 S3 W3 _ _ mdk HPRE HEPI HLOOP HFRM).
unfold cc2_INV_LATCH.
split; [exact (cc2_fi_stk v ly3 S3 W3 regs3 mem3 md3 _ _ mdk HFI HJ HSTK
                 (KEPT 2%bv ltac:(cbn; tauto)) (KEPT 3%bv ltac:(cbn; tauto))
                 (KEPT 4%bv ltac:(cbn; tauto)))|].
split; [exact (cc2_un_store v ly3 S3 W3 mem3 md3 _ mdk HAR (proj1 HJ) HUN HOUTB)|].
split; [exact Hi|].
split; [exact HRCn|].
split; [rewrite (KEPT 8%bv ltac:(cbn; tauto)); exact R8|].
split; [rewrite (KEPT 9%bv ltac:(cbn; tauto)); exact R9|].
split; [rewrite (KEPT 18%bv ltac:(cbn; tauto)); exact R18|].
split; [rewrite (KEPT 19%bv ltac:(cbn; tauto)); exact R19|].
split; [rewrite (KEPT 25%bv ltac:(cbn; tauto)); exact R25|].
split; [rewrite (KEPT 26%bv ltac:(cbn; tauto)); exact R26|].
split; [rewrite (KEPT 27%bv ltac:(cbn; tauto)); exact R27|].
split.
- exact (cc2_rdw_on (rdW W3 mem3) (rdW W3 (ms_mem ms)) (cc_sp0 v - 120) 3
    ltac:(intros x Hx; apply HSTK; lia) Hsp8).
- exact (cc2_rdw_on (rdW W3 mem3) (rdW W3 (ms_mem ms)) (cc_sp0 v - 112) (lit F_xbox)
    ltac:(intros x Hx; apply HSTK; lia) Hsp10).
Qed.

(* ===================== 10. a pass that takes neither arm ===================== *)
(* the three keep leaves of the head: the run from CC_LOOP to CC_LATCH writes nothing, so the state at the
   latch is the cut's but for the registers the run set *)
Lemma cc2_keep : forall (v : ccx) (i : Z) ly3 S3 (W3 : world SEGS) regs3 mem3 md3 regs4 md4,
  cc_pre B lit gotw guard STK_REF v ->
  (forall fx0 : YK11.FPState, from_EPI (fx := fx0) B lit gotw guard STK_REF v) ->
  (forall fx0 : YK11.FPState, frm0 fx0 -> from_LOOP (fx := fx0) B lit gotw guard STK_REF v (i + 1)) ->
  frm0 fx ->
  INV_LOOP B lit gotw guard STK_REF v i ly3 S3 W3 regs3 mem3 md3 ->
  (rs_model_set (cc2_sgi v i) = false /\
     rs_role_set (cc2_sgi v i) && (rs_role (cc2_sgi v i) =? 4) = false) \/
  (rs_model_set (cc2_sgi v i) = true /\
     rs_role_set (cc2_sgi v i) && (rs_role (cc2_sgi v i) =? 4) = true) ->
  ajournal SEGS B (cc_STK STK_REF) (cc_sp0 v) (cc_FP v) (x_ly v) (x_S v) (x_W v) (x_mem v) (x_md v) []
    ly3 S3 W3 mem3 md4 0 ->
  (forall r, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 25%bv; 26%bv] ->
     getr regs4 r = getr regs3 r) ->
  getr regs4 27 = getr regs3 27 ->
  SRr SEGS W3 (cfg_at SEGS (BASE + CC_LATCH) regs4 mem3 md4) (cc_post B lit gotw guard STK_REF v).
Proof.
intros v i ly3 S3 W3 regs3 mem3 md3 regs4 md4 HPRE HEPI HLOOP HFRM HINV HKEEPC HJ4 KEPT K27.
pose proof HINV as (HFI & HUN & Hi & HRC & R8 & R9 & R18 & R19 & R25 & R26 & R27 & Hsp8 & Hsp10).
assert (Hstep : cc_at v (i + 1) = cc_at v i).
{ unfold cc_at. rewrite cc_fold_S by lia.
  exact (r_cross_seg_keep (cc_fold (x_rcs v) i) (Z.to_nat i) HKEEPC). }
apply (cc2_latch v i ly3 S3 W3 regs4 mem3 md4 HPRE HEPI HLOOP HFRM).
unfold cc2_INV_LATCH.
split; [exact (cc2_fi_ext v ly3 S3 W3 regs3 mem3 md3 regs4 mem3 md4 HFI HJ4
                 (fun x => eq_refl) (KEPT 2%bv ltac:(cbn; tauto)) (KEPT 3%bv ltac:(cbn; tauto))
                 (KEPT 4%bv ltac:(cbn; tauto)))|].
split; [exact HUN|].
split; [exact Hi|].
split; [rewrite Hstep; exact HRC|].
split; [rewrite (KEPT 8%bv ltac:(cbn; tauto)); exact R8|].
split; [rewrite (KEPT 9%bv ltac:(cbn; tauto)); exact R9|].
split; [rewrite (KEPT 18%bv ltac:(cbn; tauto)); exact R18|].
split; [rewrite (KEPT 19%bv ltac:(cbn; tauto)); exact R19|].
split; [rewrite (KEPT 25%bv ltac:(cbn; tauto)); exact R25|].
split; [rewrite (KEPT 26%bv ltac:(cbn; tauto)); exact R26|].
split; [rewrite K27; exact R27|].
split; [exact Hsp8 | exact Hsp10].
Qed.
End a.

(* ===================== 11. the head of a pass, 0x892ac-0x8938c, and its two calls ===================== *)
Section c. Context {fx : YK11.FPState}.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
(* the frame part of a cut after a call of refuse: the entry journal is the call rule's, the 13 saved slots and
   the two spills lie above refuse's entry sp, and the allocator did nothing *)
Lemma cc2_fi_call : forall (v : ccx) ly3 S3 (W3 : world SEGS) regs3 mem3 md3
  ly4 S4 (W4 : world SEGS) regs4 mem4 md4,
  cc_fi B lit gotw guard STK_REF v ly3 S3 W3 regs3 mem3 md3 ->
  ajournal SEGS B (cc_STK STK_REF) (cc_sp0 v) (cc_FP v) (x_ly v) (x_S v) (x_W v) (x_mem v) (x_md v) []
    ly4 S4 W4 mem4 md4 0 ->
  sa_noalloc B ly3 S3 ly4 S4 ->
  (forall a, cc_sp0 v - 128 <= a < cc_sp0 v -> rdW W4 mem4 a = rdW W3 mem3 a) ->
  getr regs4 2 = getr regs3 2 -> getr regs4 3 = getr regs3 3 -> getr regs4 4 = getr regs3 4 ->
  cc_fi B lit gotw guard STK_REF v ly4 S4 W4 regs4 mem4 md4.
Proof.
intros v ly3 S3 W3 regs3 mem3 md3 ly4 S4 W4 regs4 mem4 md4
  [J1 G2 G3 G4 GSV GNO] HJ4 HNA HKEEP E2 E3 E4. constructor.
- exact HJ4.
- rewrite E2; exact G2.
- rewrite E3; exact G3.
- rewrite E4; exact G4.
- intros j r Hj.
  assert (Hj13 : (j < 13)%nat).
  { pose proof (proj1 (nth_error_Some cc_saved j) ltac:(rewrite Hj; discriminate)) as Hl.
    unfold cc_saved in Hl. cbn [length] in Hl. lia. }
  rewrite <- (GSV j r Hj). apply rdword_ext. intros k Hk. apply HKEEP. lia.
- exact (sa_noalloc_trans B (x_ly v) (x_S v) ly3 S3 ly4 S4 GNO HNA).
Qed.
(* the stack window of cross_check's own frame comes back from a call of refuse *)
Lemma cc2_keep_stk : forall (v : ccx) ly3 S3 (W3 : world SEGS) mem3 md3 ly4 S4 (W4 : world SEGS) mem4 md4
  (rcs : rconf) k,
  4096 <= x_c v -> x_c v + seg_spec.SEG_C_SIZE <= alloc_ceiling -> alloc_ceiling + 128 <= cc_sp0 v ->
  ajournal SEGS B STK_REF (cc_sp0 v - 128) (refuse_W (x_c v) rcs) ly3 S3 W3 mem3 md3 []
    ly4 S4 W4 mem4 md4 k ->
  forall a, cc_sp0 v - 128 <= a < cc_sp0 v -> rdW W4 mem4 a = rdW W3 mem3 a.
Proof.
intros v ly3 S3 W3 mem3 md3 ly4 S4 W4 mem4 md4 rcs k Hc4 Hcc Hsp HJc.
apply (cc_own_frame_kept B STK_REF v ly3 S3 W3 mem3 md3 ly4 S4 W4 mem4 md4 rcs k STKR HJc).
- intros a Ha. pose proof (refuse_W_in_block (x_c v) rcs a Ha).
  unfold seg_spec.RC_REFUSAL, seg_spec.RC_OVERFLOW, seg_spec.SEG_C_SIZE in *. lia.
- intros a Ha. unfold seg_spec.SEG_C_SIZE in *. lia.
Qed.
(* 0x89350: refuse(c, 0, F_xmodel, s->name, s->model), returning at CC_RET1 *)
Lemma cc2_call1 : forall (v : ccx) (i : Z) ly3 S3 (W3 : world SEGS) regs3 mem3 md3 regs4 md4,
  cc_pre B lit gotw guard STK_REF v ->
  (forall fx0 : YK11.FPState, from_EPI (fx := fx0) B lit gotw guard STK_REF v) ->
  (forall fx0 : YK11.FPState, frm0 fx0 -> from_LOOP (fx := fx0) B lit gotw guard STK_REF v (i + 1)) ->
  frm0 fx ->
  (forall fx0 : YK11.FPState,
     @refuse_contract fx0 rc SK SEGS B (BASE + AF_refuse) STK_REF SEG_RLO SEG_RHI lit gotw guard) ->
  INV_LOOP B lit gotw guard STK_REF v i ly3 S3 W3 regs3 mem3 md3 ->
  rs_model_set (cc2_sgi v i) = true ->
  rs_role_set (cc2_sgi v i) && (rs_role (cc2_sgi v i) =? 4) = false ->
  ajournal SEGS B (cc_STK STK_REF) (cc_sp0 v) (cc_FP v) (x_ly v) (x_S v) (x_W v) (x_mem v) (x_md v) []
    ly3 S3 W3 mem3 md4 0 ->
  getr regs4 1 = Z_to_bv 64 (BASE + CC_RET1) ->
  getr regs4 2 = w64 (cc_sp0 v - 128) ->
  getr regs4 3 = w64 (as_gp B) -> getr regs4 4 = w64 (as_tp B) ->
  getr regs4 8 = w64 (x_c v) -> getr regs4 9 = w64 (x_c v + seg_spec.RC_N) ->
  getr regs4 10 = w64 (x_c v) -> getr regs4 11 = w64 0 -> getr regs4 12 = w64 (lit F_xmodel) ->
  getr regs4 13 = w64 (x_c v + 356 * i) ->
  getr regs4 14 = w64 (x_c v + 356 * i + seg_spec.RS_MODEL) ->
  getr regs4 18 = w64 (lit F_xmodel) -> getr regs4 19 = w64 SHADOW_OFF ->
  getr regs4 21 = w64 (x_c v + 356 * i + seg_spec.RS_MODEL_SET) ->
  getr regs4 22 = w64 (x_c v + 356 * i + seg_spec.RS_MODEL) ->
  getr regs4 25 = w64 (356 * i) -> getr regs4 26 = w64 i ->
  getr regs4 27 = w64 (SHADOW_OFF + (x_c v + seg_spec.RC_N) / 8) ->
  SRr SEGS W3 (cfg_at SEGS (BASE + AF_refuse) regs4 mem3 md4)
    (cc_post B lit gotw guard STK_REF v).
Proof.
intros v i ly3 S3 W3 regs3 mem3 md3 regs4 md4 HPRE HEPI HLOOP HFRM REF HINV HMS HRS HJ4
  C1 C2 C3 C4 C8 C9 C10 C11 C12 C13 C14 C18 C19 C21 C22 C25 C26 C27.
pose proof HINV as (HFI & HUN & Hi & HRC & R8 & R9 & R18 & R19 & R25 & R26 & R27 & Hsp8 & Hsp10).
destruct (cc2_bounds v i ly3 S3 W3 regs3 mem3 md3 HPRE HFI HUN Hi)
  as (Hc4 & Hcc & Hc16 & Hi31 & Happ & HSA & Hpres & Hsp & Hsp47 & Hxb & Hl32).
pose proof pa_B_ok as (HB1 & HB2 & HB3). pose proof pa_base_lo as HBLO.
pose proof asan_consts as (CA & _).
pose proof (cp_c64 _ _ _ _ _ _ HPRE) as Hc64.
destruct (sa_rconf_n (rdW W3 mem3) (x_c v) (cc_at v i) HRC) as (_ & _ & Href8).
destruct (cc_call_room B lit gotw guard STK_REF v ly3 S3 W3 regs3 mem3 md3 HPRE HFI) as (_ & ROOM & EVB).
pose proof (cc_call_chain B lit gotw guard STK_REF v ly3 S3 W3 regs3 mem3 md3 regs4 HPRE HFI HUN C8 Hc64)
  as HCH.
pose proof (refuse_site_ok_89350 B lit gotw guard STK_REF v i ly3 S3 W3 regs3 mem3 md3 regs4
  HPRE HINV HFRM HMS HRS C10 C11 C12 C13 C14
  ltac:(unfold spZ; rewrite C2; apply cc_w64_u; lia)) as RPRE.
assert (HXM : 0 < lit F_xmodel < kLowMemEnd)
  by (apply (cc2_lit_lo v ly3 S3 W3 mem3); [exact HUN | unfold CROSS_CHECK_LITS; left; reflexivity]).
assert (HR1 : CC_RET1 = 17952) by (vm_compute; reflexivity).
unfold cfg_at, w64.
eapply SRr_bind.
{ eapply (cl_callSF B LAWS W3 regs4 mem3 (Z_to_bv 64 (BASE + AF_refuse))
    (cc_STK STK_REF) (cc_sp0 v) (cc_FP v) (x_ly v) (x_S v) (x_W v) (x_mem v) (x_md v) []
    ly3 S3 md4 0 STK_REF (refuse_W (x_c v) (cc_at v i)) EV_refuse (-128)
    (Z_to_bv 64 (BASE + CC_RET1)) []
    (fun ly2 S2 (W2 : world SEGS) regs2 mem2 md2 =>
       sa_rconf (rdW W2 mem2) (x_c v)
         (SegModel.refuse (cc_at v i) 0 F_xmodel
            [AS (rs_name (cc2_sgi v i)); AS (rs_model (cc2_sgi v i))]) /\ sa_noalloc B ly3 S3 ly2 S2)
    HJ4).
  - unfold spZ. rewrite C2. rewrite unsigned_lit_small by lia. lia.
  - reflexivity.
  - lia.
  - exact STKR.
  - unfold cc_STK. lia.
  - exact C3.
  - exact C4.
  - exact C1.
  - apply ret_ok_codeptr_v; [rewrite HR1; lia | rewrite HR1; reflexivity].
  - rewrite unsigned_lit_small; rewrite HR1; lia.
  - replace (cc_sp0 v + -128) with (cc_sp0 v - 128) by lia. exact HCH.
  - intros HPRE1. eapply SRr_mono.
    { exact (REF fx ly3 S3 W3 regs4 mem3 md4 [] (x_c v) 0 (lit F_xmodel) 0 (cc_at v i) F_xmodel
        [AS (rs_name (cc2_sgi v i)); AS (rs_model (cc2_sgi v i))] HPRE1
        (un_rod _ _ _ _ _ _ _ _ _ _ HUN) C10 Hc64 C11 ltac:(lia) C12
        ltac:(unfold kLowMemEnd in HXM; lia) RPRE ROOM EVB). }
    cbv beta. intros W' c' _ (fx' & ly' & S' & regs' & mem' & md' & -> & Hf1 & Hf2 & HJ' & HP' & HK').
    exists fx', ly', S', regs', mem', md'. split; [rewrite C1; reflexivity|].
    split; [exact Hf1|]. split; [exact Hf2|]. split; [exact HJ'|]. split; [exact HP' | exact HK'].
  - intros a Ha. left. split; [exact (cc_refuse_FP_sub v (cc_at v i) a Href8 Ha)|].
    pose proof (un_heap _ _ _ _ _ _ _ _ _ _ HUN) as (b & m & Hin & Hb & Hm).
    pose proof (refuse_W_in_block (x_c v) (cc_at v i) a Ha) as Hin2.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ (proj1 HJ4) Hin) as (_ & _ & _ & _ & _ & _ & Hn0).
    pose proof (req_size_pos0 m ltac:(lia)) as (Hrq1 & Hrq2).
    exists b, m. split; [exact Hin|].
    unfold seg_spec.RC_REFUSAL, seg_spec.RC_OVERFLOW, seg_spec.SEG_C_SIZE in *. lia. }
cbv beta.
intros W2 c2 _ (fx1 & ly2 & S2 & regs2 & mem2 & md2 & Hfx1 & -> & HJ2 & HJc2 & HP2 & (HRC2 & HNA2)).
replace (cc_sp0 v + -128) with (cc_sp0 v - 128) in HJc2 by lia.
replace (0 + EV_refuse) with 0 in HJ2 by (unfold EV_refuse; lia).
unfold cc_post.
eapply (srr_apost_baseF_lift SEGS fx1); [exact Hfx1|].
pose proof (cc2_keep_stk v ly3 S3 W3 mem3 md4 ly2 S2 W2 mem2 md2
  (cc_at v i) EV_refuse Hc4 Hcc Hsp HJc2) as HKEEP.
apply (cc2_arm1 (fx := fx1) v i ly2 S2 W2 regs2 mem2 md2 HPRE HEPI HLOOP
  (PaFx.fxrel_frm0 fx fx1 HFRM Hfx1)).
assert (V8 : getr regs2 8 = w64 (x_c v))
  by (transitivity (getr regs4 8); [exact (HP2 8 ltac:(unfold acallee_saved; lia)) | exact C8]).
assert (V9 : getr regs2 9 = w64 (x_c v + seg_spec.RC_N))
  by (transitivity (getr regs4 9); [exact (HP2 9 ltac:(unfold acallee_saved; lia)) | exact C9]).
assert (V18 : getr regs2 18 = w64 (lit F_xmodel))
  by (transitivity (getr regs4 18); [exact (HP2 18 ltac:(unfold acallee_saved; lia)) | exact C18]).
assert (V19 : getr regs2 19 = w64 SHADOW_OFF)
  by (transitivity (getr regs4 19); [exact (HP2 19 ltac:(unfold acallee_saved; lia)) | exact C19]).
assert (V21 : getr regs2 21 = w64 (x_c v + 356 * i + seg_spec.RS_MODEL_SET))
  by (transitivity (getr regs4 21); [exact (HP2 21 ltac:(unfold acallee_saved; lia)) | exact C21]).
assert (V22 : getr regs2 22 = w64 (x_c v + 356 * i + seg_spec.RS_MODEL))
  by (transitivity (getr regs4 22); [exact (HP2 22 ltac:(unfold acallee_saved; lia)) | exact C22]).
assert (V25 : getr regs2 25 = w64 (356 * i))
  by (transitivity (getr regs4 25); [exact (HP2 25 ltac:(unfold acallee_saved; lia)) | exact C25]).
assert (V26 : getr regs2 26 = w64 i)
  by (transitivity (getr regs4 26); [exact (HP2 26 ltac:(unfold acallee_saved; lia)) | exact C26]).
assert (V27 : getr regs2 27 = w64 (SHADOW_OFF + (x_c v + seg_spec.RC_N) / 8))
  by (transitivity (getr regs4 27); [exact (HP2 27 ltac:(unfold acallee_saved; lia)) | exact C27]).
unfold cc2_INV_A1.
split; [exact (cc2_fi_call v ly3 S3 W3 regs4 mem3 md4 ly2 S2 W2 regs2 mem2 md2
                 (cc2_fi_ext v ly3 S3 W3 regs3 mem3 md3 regs4 mem3 md4 HFI HJ4 (fun x => eq_refl)
                    ltac:(rewrite C2, (fi_sp _ _ _ _ _ _ _ _ _ _ _ _ HFI); reflexivity)
                    ltac:(rewrite C3, (fi_gp _ _ _ _ _ _ _ _ _ _ _ _ HFI); reflexivity)
                    ltac:(rewrite C4, (fi_tp _ _ _ _ _ _ _ _ _ _ _ _ HFI); reflexivity))
                 HJ2 HNA2 HKEEP
                 (HP2 2 ltac:(unfold acallee_saved; lia))
                 (HP2 3 ltac:(unfold acallee_saved; lia))
                 (HP2 4 ltac:(unfold acallee_saved; lia)))|].
split; [exact (cc_un_after B lit gotw guard STK_REF v ly3 S3 W3 mem3 md4 ly2 S2 W2 mem2 md2
                 (cc_at v i) EV_refuse ROIMG SSPAR HPRE HUN Href8 HJc2)|].
split; [exact Hi|].
split; [exact HMS|].
split; [exact HRS|].
split; [exact HRC2|].
split; [exact V8|]. split; [exact V9|]. split; [exact V18|]. split; [exact V19|].
split; [exact V21|]. split; [exact V22|]. split; [exact V25|]. split; [exact V26|].
split; [exact V27|].
split.
- exact (cc2_rdw_on (rdW W3 mem3) (rdW W2 mem2) (cc_sp0 v - 120) 3
    ltac:(intros x Hx; apply HKEEP; lia) Hsp8).
- exact (cc2_rdw_on (rdW W3 mem3) (rdW W2 mem2) (cc_sp0 v - 112) (lit F_xbox)
    ltac:(intros x Hx; apply HKEEP; lia) Hsp10).
Qed.
(* 0x8939c: refuse(c, 0, F_xbox, s->name), returning at CC_RET2 *)
Lemma cc2_call2 : forall (v : ccx) (i : Z) ly3 S3 (W3 : world SEGS) regs3 mem3 md3 regs4 md4,
  cc_pre B lit gotw guard STK_REF v ->
  (forall fx0 : YK11.FPState, from_EPI (fx := fx0) B lit gotw guard STK_REF v) ->
  (forall fx0 : YK11.FPState, frm0 fx0 -> from_LOOP (fx := fx0) B lit gotw guard STK_REF v (i + 1)) ->
  frm0 fx ->
  (forall fx0 : YK11.FPState,
     @refuse_contract fx0 rc SK SEGS B (BASE + AF_refuse) STK_REF SEG_RLO SEG_RHI lit gotw guard) ->
  INV_LOOP B lit gotw guard STK_REF v i ly3 S3 W3 regs3 mem3 md3 ->
  rs_model_set (cc2_sgi v i) = false ->
  rs_role_set (cc2_sgi v i) && (rs_role (cc2_sgi v i) =? 4) = true ->
  ajournal SEGS B (cc_STK STK_REF) (cc_sp0 v) (cc_FP v) (x_ly v) (x_S v) (x_W v) (x_mem v) (x_md v) []
    ly3 S3 W3 mem3 md4 0 ->
  getr regs4 1 = Z_to_bv 64 (BASE + CC_RET2) ->
  getr regs4 2 = w64 (cc_sp0 v - 128) ->
  getr regs4 3 = w64 (as_gp B) -> getr regs4 4 = w64 (as_tp B) ->
  getr regs4 8 = w64 (x_c v) -> getr regs4 9 = w64 (x_c v + seg_spec.RC_N) ->
  getr regs4 10 = w64 (x_c v) -> getr regs4 11 = w64 0 -> getr regs4 12 = w64 (lit F_xbox) ->
  getr regs4 13 = w64 (x_c v + 356 * i) ->
  getr regs4 18 = w64 (lit F_xmodel) -> getr regs4 19 = w64 SHADOW_OFF ->
  getr regs4 20 = w64 (x_c v + 356 * i) ->
  getr regs4 23 = w64 (SHADOW_OFF + (x_c v + 356 * i + seg_spec.RS_ROLE_SET) / 8) ->
  getr regs4 24 = w64 (SHADOW_OFF + (x_c v + 356 * i + seg_spec.RS_ROLE) / 8) ->
  getr regs4 25 = w64 (356 * i) -> getr regs4 26 = w64 i ->
  getr regs4 27 = w64 (SHADOW_OFF + (x_c v + seg_spec.RC_N) / 8) ->
  SRr SEGS W3 (cfg_at SEGS (BASE + AF_refuse) regs4 mem3 md4)
    (cc_post B lit gotw guard STK_REF v).
Proof.
intros v i ly3 S3 W3 regs3 mem3 md3 regs4 md4 HPRE HEPI HLOOP HFRM REF HINV HMS HRS HJ4
  C1 C2 C3 C4 C8 C9 C10 C11 C12 C13 C18 C19 C20 C23 C24 C25 C26 C27.
pose proof HINV as (HFI & HUN & Hi & HRC & R8 & R9 & R18 & R19 & R25 & R26 & R27 & Hsp8 & Hsp10).
destruct (cc2_bounds v i ly3 S3 W3 regs3 mem3 md3 HPRE HFI HUN Hi)
  as (Hc4 & Hcc & Hc16 & Hi31 & Happ & HSA & Hpres & Hsp & Hsp47 & Hxb & Hl32).
pose proof pa_B_ok as (HB1 & HB2 & HB3). pose proof pa_base_lo as HBLO.
pose proof asan_consts as (CA & _).
pose proof (cp_c64 _ _ _ _ _ _ HPRE) as Hc64.
destruct (sa_rconf_n (rdW W3 mem3) (x_c v) (cc_at v i) HRC) as (_ & _ & Href8).
destruct (cc_call_room B lit gotw guard STK_REF v ly3 S3 W3 regs3 mem3 md3 HPRE HFI) as (_ & ROOM & EVB).
pose proof (cc_call_chain B lit gotw guard STK_REF v ly3 S3 W3 regs3 mem3 md3 regs4 HPRE HFI HUN C8 Hc64)
  as HCH.
pose proof (refuse_site_ok_8939c B lit gotw guard STK_REF v i ly3 S3 W3 regs3 mem3 md3 regs4
  HPRE HINV HFRM HMS HRS C10 C11 C12 C13
  ltac:(unfold spZ; rewrite C2; apply cc_w64_u; lia)) as RPRE.
assert (HR2 : CC_RET2 = 18028) by (vm_compute; reflexivity).
unfold cfg_at, w64.
eapply SRr_bind.
{ eapply (cl_callSF B LAWS W3 regs4 mem3 (Z_to_bv 64 (BASE + AF_refuse))
    (cc_STK STK_REF) (cc_sp0 v) (cc_FP v) (x_ly v) (x_S v) (x_W v) (x_mem v) (x_md v) []
    ly3 S3 md4 0 STK_REF (refuse_W (x_c v) (cc_at v i)) EV_refuse (-128)
    (Z_to_bv 64 (BASE + CC_RET2)) []
    (fun ly2 S2 (W2 : world SEGS) regs2 mem2 md2 =>
       sa_rconf (rdW W2 mem2) (x_c v)
         (SegModel.refuse (cc_at v i) 0 F_xbox [AS (rs_name (cc2_sgi v i))]) /\
       sa_noalloc B ly3 S3 ly2 S2)
    HJ4).
  - unfold spZ. rewrite C2. rewrite unsigned_lit_small by lia. lia.
  - reflexivity.
  - lia.
  - exact STKR.
  - unfold cc_STK. lia.
  - exact C3.
  - exact C4.
  - exact C1.
  - apply ret_ok_codeptr_v; [rewrite HR2; lia | rewrite HR2; reflexivity].
  - rewrite unsigned_lit_small; rewrite HR2; lia.
  - replace (cc_sp0 v + -128) with (cc_sp0 v - 128) by lia. exact HCH.
  - intros HPRE1. eapply SRr_mono.
    { exact (REF fx ly3 S3 W3 regs4 mem3 md4 [] (x_c v) 0 (lit F_xbox) 0 (cc_at v i) F_xbox
        [AS (rs_name (cc2_sgi v i))] HPRE1
        (un_rod _ _ _ _ _ _ _ _ _ _ HUN) C10 Hc64 C11 ltac:(lia) C12
        ltac:(unfold kLowMemEnd in Hxb; lia) RPRE ROOM EVB). }
    cbv beta. intros W' c' _ (fx' & ly' & S' & regs' & mem' & md' & -> & Hf1 & Hf2 & HJ' & HP' & HK').
    exists fx', ly', S', regs', mem', md'. split; [rewrite C1; reflexivity|].
    split; [exact Hf1|]. split; [exact Hf2|]. split; [exact HJ'|]. split; [exact HP' | exact HK'].
  - intros a Ha. left. split; [exact (cc_refuse_FP_sub v (cc_at v i) a Href8 Ha)|].
    pose proof (un_heap _ _ _ _ _ _ _ _ _ _ HUN) as (b & m & Hin & Hb & Hm).
    pose proof (refuse_W_in_block (x_c v) (cc_at v i) a Ha) as Hin2.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ (proj1 HJ4) Hin) as (_ & _ & _ & _ & _ & _ & Hn0).
    pose proof (req_size_pos0 m ltac:(lia)) as (Hrq1 & Hrq2).
    exists b, m. split; [exact Hin|].
    unfold seg_spec.RC_REFUSAL, seg_spec.RC_OVERFLOW, seg_spec.SEG_C_SIZE in *. lia. }
cbv beta.
intros W2 c2 _ (fx1 & ly2 & S2 & regs2 & mem2 & md2 & Hfx1 & -> & HJ2 & HJc2 & HP2 & (HRC2 & HNA2)).
replace (cc_sp0 v + -128) with (cc_sp0 v - 128) in HJc2 by lia.
replace (0 + EV_refuse) with 0 in HJ2 by (unfold EV_refuse; lia).
unfold cc_post.
eapply (srr_apost_baseF_lift SEGS fx1); [exact Hfx1|].
pose proof (cc2_keep_stk v ly3 S3 W3 mem3 md4 ly2 S2 W2 mem2 md2
  (cc_at v i) EV_refuse Hc4 Hcc Hsp HJc2) as HKEEP.
apply (cc2_arm2 (fx := fx1) v i ly2 S2 W2 regs2 mem2 md2 HPRE HEPI HLOOP
  (PaFx.fxrel_frm0 fx fx1 HFRM Hfx1)).
assert (V8 : getr regs2 8 = w64 (x_c v))
  by (transitivity (getr regs4 8); [exact (HP2 8 ltac:(unfold acallee_saved; lia)) | exact C8]).
assert (V9 : getr regs2 9 = w64 (x_c v + seg_spec.RC_N))
  by (transitivity (getr regs4 9); [exact (HP2 9 ltac:(unfold acallee_saved; lia)) | exact C9]).
assert (V18 : getr regs2 18 = w64 (lit F_xmodel))
  by (transitivity (getr regs4 18); [exact (HP2 18 ltac:(unfold acallee_saved; lia)) | exact C18]).
assert (V19 : getr regs2 19 = w64 SHADOW_OFF)
  by (transitivity (getr regs4 19); [exact (HP2 19 ltac:(unfold acallee_saved; lia)) | exact C19]).
assert (V20 : getr regs2 20 = w64 (x_c v + 356 * i))
  by (transitivity (getr regs4 20); [exact (HP2 20 ltac:(unfold acallee_saved; lia)) | exact C20]).
assert (V23 : getr regs2 23 = w64 (SHADOW_OFF + (x_c v + 356 * i + seg_spec.RS_ROLE_SET) / 8))
  by (transitivity (getr regs4 23); [exact (HP2 23 ltac:(unfold acallee_saved; lia)) | exact C23]).
assert (V24 : getr regs2 24 = w64 (SHADOW_OFF + (x_c v + 356 * i + seg_spec.RS_ROLE) / 8))
  by (transitivity (getr regs4 24); [exact (HP2 24 ltac:(unfold acallee_saved; lia)) | exact C24]).
assert (V25 : getr regs2 25 = w64 (356 * i))
  by (transitivity (getr regs4 25); [exact (HP2 25 ltac:(unfold acallee_saved; lia)) | exact C25]).
assert (V26 : getr regs2 26 = w64 i)
  by (transitivity (getr regs4 26); [exact (HP2 26 ltac:(unfold acallee_saved; lia)) | exact C26]).
assert (V27 : getr regs2 27 = w64 (SHADOW_OFF + (x_c v + seg_spec.RC_N) / 8))
  by (transitivity (getr regs4 27); [exact (HP2 27 ltac:(unfold acallee_saved; lia)) | exact C27]).
unfold cc2_INV_A2.
split; [exact (cc2_fi_call v ly3 S3 W3 regs4 mem3 md4 ly2 S2 W2 regs2 mem2 md2
                 (cc2_fi_ext v ly3 S3 W3 regs3 mem3 md3 regs4 mem3 md4 HFI HJ4 (fun x => eq_refl)
                    ltac:(rewrite C2, (fi_sp _ _ _ _ _ _ _ _ _ _ _ _ HFI); reflexivity)
                    ltac:(rewrite C3, (fi_gp _ _ _ _ _ _ _ _ _ _ _ _ HFI); reflexivity)
                    ltac:(rewrite C4, (fi_tp _ _ _ _ _ _ _ _ _ _ _ _ HFI); reflexivity))
                 HJ2 HNA2 HKEEP
                 (HP2 2 ltac:(unfold acallee_saved; lia))
                 (HP2 3 ltac:(unfold acallee_saved; lia))
                 (HP2 4 ltac:(unfold acallee_saved; lia)))|].
split; [exact (cc_un_after B lit gotw guard STK_REF v ly3 S3 W3 mem3 md4 ly2 S2 W2 mem2 md2
                 (cc_at v i) EV_refuse ROIMG SSPAR HPRE HUN Href8 HJc2)|].
split; [exact Hi|].
split; [exact HMS|].
split; [exact HRS|].
split; [exact HRC2|].
split; [exact V8|]. split; [exact V9|]. split; [exact V18|]. split; [exact V19|].
split; [exact V20|]. split; [exact V23|]. split; [exact V24|]. split; [exact V25|].
split; [exact V26|]. split; [exact V27|].
split.
- exact (cc2_rdw_on (rdW W3 mem3) (rdW W2 mem2) (cc_sp0 v - 120) 3
    ltac:(intros x Hx; apply HKEEP; lia) Hsp8).
- exact (cc2_rdw_on (rdW W3 mem3) (rdW W2 mem2) (cc_sp0 v - 112) (lit F_xbox)
    ltac:(intros x Hx; apply HKEEP; lia) Hsp10).
Qed.

(* 0x892ac-0x8938c: the head of the pass. Three keep leaves reach CC_LATCH, two leaves reach the model-drop
   arm's call and one the box arm's; the branch tree is the one the executor builds (the conditions, in the
   order psrr_branch_tok splits them: role_set = 0, model_set = 0, role = BOX). *)
Lemma cc2_pass :
  (forall fx0 : YK11.FPState,
     @refuse_contract fx0 rc SK SEGS B (BASE + AF_refuse) STK_REF SEG_RLO SEG_RHI lit gotw guard) ->
  cc_S2P B lit gotw guard STK_REF.
Proof.
intros REF. unfold cc_S2P. intros v i HFRM HPRE HEPI HLOOP.
unfold from_LOOP, cc_from. intros ly3 S3 W3 regs3 mem3 md3 HINV.
pose proof HINV as (HFI & HUN & Hi & HRC & R8 & R9 & R18 & R19 & R25 & R26 & R27 & Hsp8 & Hsp10).
destruct (cc2_bounds v i ly3 S3 W3 regs3 mem3 md3 HPRE HFI HUN Hi)
  as (Hc4 & Hcc & Hc16 & Hi31 & Happ & HSA & Hpres & Hsp & Hsp47 & Hxb & Hl32).
pose proof asan_consts as (CA & _).
pose proof pa_B_ok as (HB1 & HB2 & HB3). pose proof pa_base_lo as HBLO.
destruct (cc2_seedL v i ly3 S3 W3 regs3 mem3 md3 HPRE HINV) as (HEI & HS & SHOK).
pose proof (fi_j _ _ _ _ _ _ _ _ _ _ _ _ HFI) as HJ.
pose proof (fi_sp _ _ _ _ _ _ _ _ _ _ _ _ HFI) as R2.
pose proof (fi_gp _ _ _ _ _ _ _ _ _ _ _ _ HFI) as R3.
pose proof (fi_tp _ _ _ _ _ _ _ _ _ _ _ _ HFI) as R4.
pose proof (cc2_ewL v i regs3) as EE.
pose proof (cc2_exL v i regs3 0%nat ltac:(lia)) as E32.
pose proof (cc2_exL v i regs3 1%nat ltac:(lia)) as E33.
pose proof (cc2_exL v i regs3 2%nat ltac:(lia)) as E34.
pose proof (cc2_exL v i regs3 3%nat ltac:(lia)) as E35.
pose proof (cc2_exL v i regs3 4%nat ltac:(lia)) as E36.
cbn [Nat.add nth] in E32, E33, E34, E35, E36.
assert (E2 : ew (cc2_El lit v i regs3) 2%nat = Z_to_bv 64 (cc_sp0 v - 128))
  by (rewrite (EE 2%nat 2%bv eq_refl); exact R2).
assert (E3 : ew (cc2_El lit v i regs3) 3%nat = Z_to_bv 64 (as_gp B))
  by (rewrite (EE 3%nat 3%bv eq_refl); exact R3).
assert (E4 : ew (cc2_El lit v i regs3) 4%nat = Z_to_bv 64 (as_tp B))
  by (rewrite (EE 4%nat 4%bv eq_refl); exact R4).
assert (E8 : ew (cc2_El lit v i regs3) 8%nat = Z_to_bv 64 (x_c v))
  by (rewrite (EE 8%nat 8%bv eq_refl); exact R8).
assert (E9 : ew (cc2_El lit v i regs3) 9%nat = Z_to_bv 64 (x_c v + seg_spec.RC_N))
  by (rewrite (EE 9%nat 9%bv eq_refl); exact R9).
assert (E18 : ew (cc2_El lit v i regs3) 18%nat = Z_to_bv 64 (lit F_xmodel))
  by (rewrite (EE 18%nat 18%bv eq_refl); exact R18).
assert (E19 : ew (cc2_El lit v i regs3) 19%nat = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (EE 19%nat 19%bv eq_refl); exact R19).
assert (E25 : ew (cc2_El lit v i regs3) 25%nat = Z_to_bv 64 (356 * i))
  by (rewrite (EE 25%nat 25%bv eq_refl); exact R25).
assert (E26 : ew (cc2_El lit v i regs3) 26%nat = Z_to_bv 64 i)
  by (rewrite (EE 26%nat 26%bv eq_refl); exact R26).
assert (EB : ew (cc2_El lit v i regs3) 240%nat = Z_to_bv 64 BASE)
  by (change 240%nat with A_TEXT; apply (img_env_atomP _ A_TEXT HEI); unfold A_TEXT, A_LIM; lia).
assert (HAG : env_agree 32 (Ereg regs3
    [Z_to_bv 64 (x_c v + 356 * i); Z_to_bv 64 (lit F_xbox); Z_to_bv 64 (rs_role (cc2_sgi v i));
     Z_to_bv 64 (cc2_bz (rs_role_set (cc2_sgi v i)));
     Z_to_bv 64 (cc2_bz (rs_model_set (cc2_sgi v i)));
     Z_to_bv 64 (Z.of_nat (length (rc_seg (cc_at v i))))]) (cc2_El lit v i regs3))
  by (unfold cc2_El, cc2_EL; split;
      [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (Hlt : (Z.to_nat i < length (rc_seg (cc_at v i)))%nat).
{ unfold cc_n in Hi.
  assert (Hlf : length (rc_seg (cc_at v i)) = length (rc_seg (x_rcs v)))
    by (unfold cc_at; apply cc_fold_len; lia).
  lia. }
assert (Hrole : 0 <= rs_role (cc2_sgi v i) < 2 ^ 31).
{ destruct (sa_rconf_fields (rdW W3 mem3) (x_c v) (cc_at v i) (Z.to_nat i) HRC Hlt)
    as (_ & _ & _ & _ & _ & HRr & _ & _).
  unfold cc2_sgi. exact HRr. }
assert (HR1 : CC_RET1 = 17952) by (vm_compute; reflexivity).
assert (HR2 : CC_RET2 = 18028) by (vm_compute; reflexivity).
unfold cfg_at, w64.
paj_run_tok RUN HS HJ SHOK cc2_Bspan.
{ cc2_ro_awr. }
cc2_mdv mdk.
cc2_frame HF HEQ1. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK cc2_Bspan.
- (* role_set = 0 *)
  pose proof (cc2_br_flag _ 35%nat _ _ E35 Hc) as Hf35. apply negb_true_iff in Hf35. clear Hc.
  paj_run_tok RUN HS HJ SHOK cc2_Bspan.
  { cc2_ro_awr. }
  cc2_mdv mdk1.
  cc2_frame HF HEQ2. pose proof (cc2_trans _ _ _ HEQ2 HEQ1) as HEQ. clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK cc2_Bspan.
  + (* model_set = 0: no arm, straight to the latch *)
    pose proof (cc2_br_flag _ 36%nat _ _ E36 Hc) as Hf36. apply negb_true_iff in Hf36. clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK cc2_Bspan CC_LATCH.
    { cc2_ro_awr. }
    pmkst HS. cc2_mdv mdk2.
    cc2_frame HF HEQ3. pose proof (cc2_trans _ _ _ HEQ3 HEQ) as HEQ'.
    apply functional_extensionality in HEQ'. rewrite HEQ' in HJ |- *.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs3 _
      [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 25%bv; 26%bv] HS HAG
      ltac:(vm_compute; reflexivity)) as KEPT.
    cbn [ms_regs restrict mkst] in KEPT.
    cc2_rg HS (27%bv : bv 5) T27.
    rewrite (cc2_shadow_denot _ 9%nat 19%nat (x_c v + seg_spec.RC_N) E9 E19
      ltac:(unfold seg_spec.RC_N, seg_spec.SEG_C_SIZE in *; lia)) in T27.
    apply (cc2_keep v i ly3 S3 W3 regs3 mem3 md3 _ _ HPRE HEPI HLOOP HFRM HINV
      ltac:(left; split; [exact Hf36 | rewrite Hf35; reflexivity]) HJ KEPT
      ltac:(rewrite T27, R27; reflexivity)).
  + (* model_set <> 0: the model-drop arm's call *)
    pose proof (cc2_br_flag _ 36%nat _ _ E36 Hc) as Hf36. apply negb_false_iff in Hf36. clear Hc.
    paj_run_tok RUN HS HJ SHOK cc2_Bspan.
    { cc2_ro_awr. }
    cc2_mdv mdc.
    cc2_frame HF HEQz. pose proof (cc2_trans _ _ _ HEQz HEQ) as HEQw.
    pmkst HS.
    apply functional_extensionality in HEQw. rewrite HEQw in HJ |- *.
    rewrite (SIGP SS_refuse ltac:(unfold seg_prog_syms; cbn [In]; tauto)).
    replace (seg_af SS_refuse) with AF_refuse by (vm_compute; reflexivity).
    cc2_rgS HS (1%bv : bv 5) Q1. cc2_rgS HS (2%bv : bv 5) Q2.
    cc2_rgS HS (3%bv : bv 5) Q3. cc2_rgS HS (4%bv : bv 5) Q4.
    cc2_rgS HS (8%bv : bv 5) Q8. cc2_rgS HS (9%bv : bv 5) Q9.
    cc2_rgS HS (10%bv : bv 5) Q10. cc2_rgS HS (11%bv : bv 5) Q11.
    cc2_rgS HS (12%bv : bv 5) Q12. cc2_rgS HS (13%bv : bv 5) Q13.
    cc2_rgS HS (14%bv : bv 5) Q14. cc2_rgS HS (18%bv : bv 5) Q18.
    cc2_rgS HS (19%bv : bv 5) Q19. cc2_rgS HS (21%bv : bv 5) Q21.
    cc2_rgS HS (22%bv : bv 5) Q22. cc2_rgS HS (25%bv : bv 5) Q25.
    cc2_rgS HS (26%bv : bv 5) Q26. cc2_rgS HS (27%bv : bv 5) Q27.
    rewrite (cc2_den_off _ 240%nat 17952 BASE EB ltac:(lia) ltac:(lia)) in Q1.
    rewrite cc2_den_atom, (EE 2%nat 2%bv eq_refl), R2 in Q2.
    rewrite cc2_den_atom, (EE 3%nat 3%bv eq_refl), R3 in Q3.
    rewrite cc2_den_atom, (EE 4%nat 4%bv eq_refl), R4 in Q4.
    rewrite cc2_den_atom, (EE 8%nat 8%bv eq_refl), R8 in Q8.
    rewrite cc2_den_atom, (EE 9%nat 9%bv eq_refl), R9 in Q9.
    rewrite cc2_den_atom, (EE 8%nat 8%bv eq_refl), R8 in Q10.
    rewrite (cc2_den_lit _ 0 ltac:(lia)) in Q11.
    rewrite cc2_den_atom, (EE 18%nat 18%bv eq_refl), R18 in Q12.
    rewrite (cc2_den_off _ 32%nat 0 (x_c v + 356 * i) E32
      ltac:(unfold seg_spec.SEG_C_SIZE in *; lia) ltac:(unfold seg_spec.SEG_C_SIZE in *; lia)),
      Z.add_0_r in Q13.
    rewrite (cc2_den_off _ 32%nat 36 (x_c v + 356 * i) E32
      ltac:(unfold seg_spec.SEG_C_SIZE in *; lia) ltac:(unfold seg_spec.SEG_C_SIZE in *; lia)) in Q14.
    rewrite cc2_den_atom, (EE 18%nat 18%bv eq_refl), R18 in Q18.
    rewrite cc2_den_atom, (EE 19%nat 19%bv eq_refl), R19 in Q19.
    rewrite (cc2_den_off _ 32%nat 60 (x_c v + 356 * i) E32
      ltac:(unfold seg_spec.SEG_C_SIZE in *; lia) ltac:(unfold seg_spec.SEG_C_SIZE in *; lia)) in Q21.
    rewrite (cc2_den_off _ 32%nat 36 (x_c v + 356 * i) E32
      ltac:(unfold seg_spec.SEG_C_SIZE in *; lia) ltac:(unfold seg_spec.SEG_C_SIZE in *; lia)) in Q22.
    rewrite cc2_den_atom, (EE 25%nat 25%bv eq_refl), R25 in Q25.
    rewrite cc2_den_atom, (EE 26%nat 26%bv eq_refl), R26 in Q26.
    rewrite (cc2_shadow_denot _ 9%nat 19%nat (x_c v + seg_spec.RC_N) E9 E19
      ltac:(unfold seg_spec.RC_N, seg_spec.SEG_C_SIZE in *; lia)) in Q27.
    apply (cc2_call1 v i ly3 S3 W3 regs3 mem3 md3 _ _ HPRE HEPI HLOOP HFRM REF HINV
      Hf36 ltac:(rewrite Hf35; reflexivity) HJ
      Q1 Q2 Q3 Q4 Q8 Q9 Q10 Q11 Q12 Q13 Q14 Q18 Q19 Q21 Q22 Q25 Q26 Q27).
- (* role_set <> 0 *)
  pose proof (cc2_br_flag _ 35%nat _ _ E35 Hc) as Hf35. apply negb_false_iff in Hf35. clear Hc.
  paj_run_tok RUN HS HJ SHOK cc2_Bspan.
  { cc2_ro_awr. }
  cc2_mdv mdk1.
  cc2_frame HF HEQ2. pose proof (cc2_trans _ _ _ HEQ2 HEQ1) as HEQ. clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK cc2_Bspan.
  + (* model_set = 0 *)
    pose proof (cc2_br_flag _ 36%nat _ _ E36 Hc) as Hf36. apply negb_true_iff in Hf36. clear Hc.
    paj_run_tok RUN HS HJ SHOK cc2_Bspan.
    { cc2_ro_awr. }
    cc2_mdv mdk2.
    cc2_frame HF HEQ3. pose proof (cc2_trans _ _ _ HEQ3 HEQ) as HEQa. clear HF HFr HG.
    psrr_branch_tok RUN BR HS SHOK cc2_Bspan.
    * (* role <> BOX: no arm *)
      pose proof (cc2_br_role_ne _ 34%nat _ _ E34 Hrole Hc) as Hf34.
      apply negb_true_iff in Hf34. clear Hc.
      paj_run_to_tok RUNTO HS HJ SHOK cc2_Bspan CC_LATCH.
      { cc2_ro_awr. }
      pmkst HS. cc2_mdv mdk3.
      cc2_frame HF HEQ4. pose proof (cc2_trans _ _ _ HEQ4 HEQa) as HEQ'.
      apply functional_extensionality in HEQ'. rewrite HEQ' in HJ |- *.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs3 _
        [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 25%bv; 26%bv] HS HAG
        ltac:(vm_compute; reflexivity)) as KEPT.
      cbn [ms_regs restrict mkst] in KEPT.
      cc2_rg HS (27%bv : bv 5) T27.
      rewrite (cc2_shadow_denot _ 9%nat 19%nat (x_c v + seg_spec.RC_N) E9 E19
        ltac:(unfold seg_spec.RC_N, seg_spec.SEG_C_SIZE in *; lia)) in T27.
      apply (cc2_keep v i ly3 S3 W3 regs3 mem3 md3 _ _ HPRE HEPI HLOOP HFRM HINV
        ltac:(left; split; [exact Hf36 | rewrite Hf34, andb_false_r; reflexivity]) HJ KEPT
        ltac:(rewrite T27, R27; reflexivity)).
    * (* role = BOX: the box arm's call *)
      pose proof (cc2_br_role_ne _ 34%nat _ _ E34 Hrole Hc) as Hf34.
      apply negb_false_iff in Hf34. clear Hc.
      paj_run_tok RUN HS HJ SHOK cc2_Bspan.
      { cc2_ro_awr. }
      cc2_mdv mdc.
      cc2_frame HF HEQz. pose proof (cc2_trans _ _ _ HEQz HEQa) as HEQw.
      pmkst HS.
      apply functional_extensionality in HEQw. rewrite HEQw in HJ |- *.
      rewrite (SIGP SS_refuse ltac:(unfold seg_prog_syms; cbn [In]; tauto)).
      replace (seg_af SS_refuse) with AF_refuse by (vm_compute; reflexivity).
      cc2_rgS HS (1%bv : bv 5) Q1. cc2_rgS HS (2%bv : bv 5) Q2.
      cc2_rgS HS (3%bv : bv 5) Q3. cc2_rgS HS (4%bv : bv 5) Q4.
      cc2_rgS HS (8%bv : bv 5) Q8. cc2_rgS HS (9%bv : bv 5) Q9.
      cc2_rgS HS (10%bv : bv 5) Q10. cc2_rgS HS (11%bv : bv 5) Q11.
      cc2_rgS HS (12%bv : bv 5) Q12. cc2_rgS HS (13%bv : bv 5) Q13.
      cc2_rgS HS (18%bv : bv 5) Q18. cc2_rgS HS (19%bv : bv 5) Q19.
      cc2_rgS HS (20%bv : bv 5) Q20. cc2_rgS HS (23%bv : bv 5) Q23.
      cc2_rgS HS (24%bv : bv 5) Q24. cc2_rgS HS (25%bv : bv 5) Q25.
      cc2_rgS HS (26%bv : bv 5) Q26. cc2_rgS HS (27%bv : bv 5) Q27.
      rewrite (cc2_den_off _ 240%nat 18028 BASE EB ltac:(lia) ltac:(lia)) in Q1.
      rewrite cc2_den_atom, (EE 2%nat 2%bv eq_refl), R2 in Q2.
      rewrite cc2_den_atom, (EE 3%nat 3%bv eq_refl), R3 in Q3.
      rewrite cc2_den_atom, (EE 4%nat 4%bv eq_refl), R4 in Q4.
      rewrite cc2_den_atom, (EE 8%nat 8%bv eq_refl), R8 in Q8.
      rewrite cc2_den_atom, (EE 9%nat 9%bv eq_refl), R9 in Q9.
      rewrite cc2_den_atom, (EE 8%nat 8%bv eq_refl), R8 in Q10.
      rewrite (cc2_den_lit _ 0 ltac:(lia)) in Q11.
      rewrite cc2_den_atom, E33 in Q12.
      rewrite (cc2_den_off _ 32%nat 0 (x_c v + 356 * i) E32
        ltac:(unfold seg_spec.SEG_C_SIZE in *; lia) ltac:(unfold seg_spec.SEG_C_SIZE in *; lia)),
        Z.add_0_r in Q13.
      rewrite cc2_den_atom, (EE 18%nat 18%bv eq_refl), R18 in Q18.
      rewrite cc2_den_atom, (EE 19%nat 19%bv eq_refl), R19 in Q19.
      rewrite (cc2_den_off _ 32%nat 0 (x_c v + 356 * i) E32
        ltac:(unfold seg_spec.SEG_C_SIZE in *; lia) ltac:(unfold seg_spec.SEG_C_SIZE in *; lia)),
        Z.add_0_r in Q20.
      rewrite (cc2_shadow_denot_off _ 32%nat 19%nat (x_c v + 356 * i) 20 E32 E19
        ltac:(unfold seg_spec.SEG_C_SIZE in *; lia)
        ltac:(unfold seg_spec.SEG_C_SIZE in *; lia)) in Q23.
      rewrite (cc2_shadow_denot_off _ 32%nat 19%nat (x_c v + 356 * i) 16 E32 E19
        ltac:(unfold seg_spec.SEG_C_SIZE in *; lia)
        ltac:(unfold seg_spec.SEG_C_SIZE in *; lia)) in Q24.
      rewrite cc2_den_atom, (EE 25%nat 25%bv eq_refl), R25 in Q25.
      rewrite cc2_den_atom, (EE 26%nat 26%bv eq_refl), R26 in Q26.
      rewrite (cc2_shadow_denot _ 9%nat 19%nat (x_c v + seg_spec.RC_N) E9 E19
        ltac:(unfold seg_spec.RC_N, seg_spec.SEG_C_SIZE in *; lia)) in Q27.
      apply (cc2_call2 v i ly3 S3 W3 regs3 mem3 md3 _ _ HPRE HEPI HLOOP HFRM REF HINV
        Hf36 ltac:(rewrite Hf35, Hf34; reflexivity) HJ
        Q1 Q2 Q3 Q4 Q8 Q9 Q10 Q11 Q12 Q13 Q18 Q19 Q20 Q23 Q24 Q25 Q26 Q27).
  + (* model_set <> 0 *)
    pose proof (cc2_br_flag _ 36%nat _ _ E36 Hc) as Hf36. apply negb_false_iff in Hf36. clear Hc.
    paj_run_tok RUN HS HJ SHOK cc2_Bspan.
    { cc2_ro_awr. }
    cc2_mdv mdk2.
    cc2_frame HF HEQ3. pose proof (cc2_trans _ _ _ HEQ3 HEQ) as HEQa. clear HF HFr HG.
    psrr_branch_tok RUN BR HS SHOK cc2_Bspan.
    * (* role = BOX: no arm *)
      pose proof (cc2_br_role _ 34%nat _ _ E34 Hrole Hc) as Hf34. clear Hc.
      paj_run_to_tok RUNTO HS HJ SHOK cc2_Bspan CC_LATCH.
      { cc2_ro_awr. }
      pmkst HS. cc2_mdv mdk3.
      cc2_frame HF HEQ4. pose proof (cc2_trans _ _ _ HEQ4 HEQa) as HEQ'.
      apply functional_extensionality in HEQ'. rewrite HEQ' in HJ |- *.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs3 _
        [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 25%bv; 26%bv] HS HAG
        ltac:(vm_compute; reflexivity)) as KEPT.
      cbn [ms_regs restrict mkst] in KEPT.
      cc2_rg HS (27%bv : bv 5) T27.
      rewrite (cc2_shadow_denot _ 9%nat 19%nat (x_c v + seg_spec.RC_N) E9 E19
        ltac:(unfold seg_spec.RC_N, seg_spec.SEG_C_SIZE in *; lia)) in T27.
      apply (cc2_keep v i ly3 S3 W3 regs3 mem3 md3 _ _ HPRE HEPI HLOOP HFRM HINV
        ltac:(right; split; [exact Hf36 | rewrite Hf35, Hf34; reflexivity]) HJ KEPT
        ltac:(rewrite T27, R27; reflexivity)).
    * (* role <> BOX: the model-drop arm's call *)
      pose proof (cc2_br_role _ 34%nat _ _ E34 Hrole Hc) as Hf34. clear Hc.
      paj_run_tok RUN HS HJ SHOK cc2_Bspan.
      { cc2_ro_awr. }
      cc2_mdv mdc.
      cc2_frame HF HEQz. pose proof (cc2_trans _ _ _ HEQz HEQa) as HEQw.
      pmkst HS.
      apply functional_extensionality in HEQw. rewrite HEQw in HJ |- *.
      rewrite (SIGP SS_refuse ltac:(unfold seg_prog_syms; cbn [In]; tauto)).
      replace (seg_af SS_refuse) with AF_refuse by (vm_compute; reflexivity).
      cc2_rgS HS (1%bv : bv 5) Q1. cc2_rgS HS (2%bv : bv 5) Q2.
      cc2_rgS HS (3%bv : bv 5) Q3. cc2_rgS HS (4%bv : bv 5) Q4.
      cc2_rgS HS (8%bv : bv 5) Q8. cc2_rgS HS (9%bv : bv 5) Q9.
      cc2_rgS HS (10%bv : bv 5) Q10. cc2_rgS HS (11%bv : bv 5) Q11.
      cc2_rgS HS (12%bv : bv 5) Q12. cc2_rgS HS (13%bv : bv 5) Q13.
      cc2_rgS HS (14%bv : bv 5) Q14. cc2_rgS HS (18%bv : bv 5) Q18.
      cc2_rgS HS (19%bv : bv 5) Q19. cc2_rgS HS (21%bv : bv 5) Q21.
      cc2_rgS HS (22%bv : bv 5) Q22. cc2_rgS HS (25%bv : bv 5) Q25.
      cc2_rgS HS (26%bv : bv 5) Q26. cc2_rgS HS (27%bv : bv 5) Q27.
      rewrite (cc2_den_off _ 240%nat 17952 BASE EB ltac:(lia) ltac:(lia)) in Q1.
      rewrite cc2_den_atom, (EE 2%nat 2%bv eq_refl), R2 in Q2.
      rewrite cc2_den_atom, (EE 3%nat 3%bv eq_refl), R3 in Q3.
      rewrite cc2_den_atom, (EE 4%nat 4%bv eq_refl), R4 in Q4.
      rewrite cc2_den_atom, (EE 8%nat 8%bv eq_refl), R8 in Q8.
      rewrite cc2_den_atom, (EE 9%nat 9%bv eq_refl), R9 in Q9.
      rewrite cc2_den_atom, (EE 8%nat 8%bv eq_refl), R8 in Q10.
      rewrite (cc2_den_lit _ 0 ltac:(lia)) in Q11.
      rewrite cc2_den_atom, (EE 18%nat 18%bv eq_refl), R18 in Q12.
      rewrite (cc2_den_off _ 32%nat 0 (x_c v + 356 * i) E32
        ltac:(unfold seg_spec.SEG_C_SIZE in *; lia) ltac:(unfold seg_spec.SEG_C_SIZE in *; lia)),
        Z.add_0_r in Q13.
      rewrite (cc2_den_off _ 32%nat 36 (x_c v + 356 * i) E32
        ltac:(unfold seg_spec.SEG_C_SIZE in *; lia)
        ltac:(unfold seg_spec.SEG_C_SIZE in *; lia)) in Q14.
      rewrite cc2_den_atom, (EE 18%nat 18%bv eq_refl), R18 in Q18.
      rewrite cc2_den_atom, (EE 19%nat 19%bv eq_refl), R19 in Q19.
      rewrite (cc2_den_off _ 32%nat 60 (x_c v + 356 * i) E32
        ltac:(unfold seg_spec.SEG_C_SIZE in *; lia)
        ltac:(unfold seg_spec.SEG_C_SIZE in *; lia)) in Q21.
      rewrite (cc2_den_off _ 32%nat 36 (x_c v + 356 * i) E32
        ltac:(unfold seg_spec.SEG_C_SIZE in *; lia)
        ltac:(unfold seg_spec.SEG_C_SIZE in *; lia)) in Q22.
      rewrite cc2_den_atom, (EE 25%nat 25%bv eq_refl), R25 in Q25.
      rewrite cc2_den_atom, (EE 26%nat 26%bv eq_refl), R26 in Q26.
      rewrite (cc2_shadow_denot _ 9%nat 19%nat (x_c v + seg_spec.RC_N) E9 E19
        ltac:(unfold seg_spec.RC_N, seg_spec.SEG_C_SIZE in *; lia)) in Q27.
      apply (cc2_call1 v i ly3 S3 W3 regs3 mem3 md3 _ _ HPRE HEPI HLOOP HFRM REF HINV
        Hf36 ltac:(rewrite Hf35, Hf34, andb_false_r; reflexivity) HJ
        Q1 Q2 Q3 Q4 Q8 Q9 Q10 Q11 Q12 Q13 Q14 Q18 Q19 Q21 Q22 Q25 Q26 Q27).
Qed.
End c.
End e.
End f.
End d.

(* ===================== 12. the segment ===================== *)
Section d2. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f2.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).

(* S2: one pass of the loop, from the head at i to the head at i + 1 or to the epilogue. *)
Theorem cc_s2 : forall (B : asyms) (lit : list Z -> Z) (gotw guard STK_REF : Z),
  PALib B -> PALibF B -> seg_val_objs -> seg_sig_prog ->
  (forall a, SEG_RLO <= a < SEG_RHI -> in_img SEGS a) ->
  (forall ly S (W : world SEGS) mem md,
     AR SEGS B ly S W mem md -> sa_ssp (aview SEGS (w_H W) mem) gotw guard) ->
  lit F_xmodel = VAL (A_OBJ 73) -> lit F_xbox = VAL (A_OBJ 74) -> 0 <= STK_REF ->
  (forall fx0 : YK11.FPState,
     @refuse_contract fx0 rc SK SEGS B (BASE + AF_refuse) STK_REF SEG_RLO SEG_RHI lit gotw guard) ->
  cc_S2P B lit gotw guard STK_REF.
Proof.
intros B lit gotw guard STK_REF TL TLF VOBJ SIGP RRO SSP L73 L74 HSR REF.
apply cc2_pass; assumption.
Qed.
End f2.
End d2.
