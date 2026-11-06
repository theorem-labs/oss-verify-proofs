(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntrySweepS1b), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v. *)
(* Modified by Theorem Labs, 2026-10: image-B twin of lib/A/Prog/GrantEntrySweepS1b.v. *)
(* Segment 1b of the sweep phase of fuzz_grant's entry function on IMAGE B:
   0x813dc .. 0x81450, and 0x813dc .. 0x81804 when the builder refused.

   The sweep buffer is allocated, and a0 and s11 hold it. This segment hands it to
   reac_grant_build_sweep (`jal` at 0x813e8, return address listing offset 0x9b0) with
   the row count (a1 = s4), the address of `a` (a2 = s8) and the head-amp table
   (a3 = s2). It recomputes `rows >= 8 + 3 * a.width ? 8 + 3 * a.width : -1` from the
   width byte at 1(s8) (0x813ec .. 0x81404) and compares it with the answer. At
   `blez a0` (0x8140c) it goes to the free at 0x81804 when the builder refused. Else it
   zeroes the row index a3 (0x81410), writes the one's complement of the buffer into
   spill slot 88 (0x81414 .. 0x81418), sets a4 and s5 to the buffer plus 2 and s8 to the
   buffer (0x8141c, 0x81448, 0x8144c), loads the ten constants a5 .. t6 the row loop
   keeps (0x81420 .. 0x81444), and reaches the loop head at 0x81450.

   The walk is three engine runs. The first (0x813dc .. 0x813e8) reads no memory. The
   other two run over the width byte of `a` in the entry function's frame on the side
   stack (read-only, over atom 24, the register the code reads it through) and over the
   realigned machine frame (atom 9) with the 8-byte window of slot 88 writable. The
   call writes only the rows of the sweep buffer, so every memory fact of the cut is
   carried by `gs_keep_*` (LLVMFEntrySweepS1c.v) across it, and outside the window of
   slot 88 across the runs. The branch at 0x81408 to the abort block (0x81d98,
   __asan_handle_no_return), which the proof shows is not taken, is not taken because
   the answer the builder gives is the value the harness recomputes: `bsw_ok` is
   `8 + 3 * w <=? rows` here (BuildSweepModel.v bsw_ok_go).

   Adapted from lib/A/Prog/GrantEntrySweepS1b.v (a working branch afd75724b5b, blob
   4748748bd, 793 lines), which carries no licence header of its own.
   Image B passes the row count, the address of `a`
   and the table from s4, s8 and s2 (image A: s3, s2 and s4), keeps the sweep buffer in
   the callee-saved register s11 where image A reloads it from spill slot 64, returns to
   listing offset 0x9b0, and before the row loop stores the one's complement of the
   buffer into spill slot 88 for its UBSan pointer-overflow guards. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YC5d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym PaShadow PaRun PaStep.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantTop GrantSyms GrantList GrantPa GrantPaLib GrantRo GrantBContracts
LLVMFEntryDefs LLVMFEntrySweepDefs.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import YC1g YC1h YC45 YC85 GrantFrame GrantACja GrantACjr.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import LLVMFEntrySeat.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require KindOfLink1.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import
HeadampModel GrantModel GrantSweepModel BuildSweepModel GrantSlotPlan.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require SlotNeeds_c SegSetModel BuildSweepLink HeadampLayout.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* Image A's text was written with this flag false; `Local` keeps the setting here. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import LLVMFEntrySweepS1c.

(* ---- the bits of Z this walk needs ---- *)

Lemma gse_bit_high : forall y i, 0 <= y < 2 ^ 64 -> 64 <= i -> Z.testbit y i = false.
Proof.
intros y i Hy Hi. destruct (Z.eq_dec y 0) as [->|Hne]; [apply Z.bits_0|].
apply Z.bits_above_log2; [lia|].
assert (Hl : Z.log2 y < 64) by (apply Z.log2_lt_pow2; lia). lia.
Qed.

(* `neg (sltu …)` is all ones, and all ones swallows the other operand. *)
Lemma gse_lor_ones : forall y, 0 <= y < 2 ^ 64 -> Z.lor (2 ^ 64 - 1) y = 2 ^ 64 - 1.
Proof.
intros y Hy. replace (2 ^ 64 - 1) with (Z.ones 64) by (vm_compute; reflexivity).
apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec, Z.testbit_ones by lia.
rewrite (proj2 (Z.leb_le 0 i) Hi). cbn [andb].
destruct (i <? 64) eqn:Hb; cbn [orb]; [reflexivity|].
apply Z.ltb_ge in Hb. rewrite (gse_bit_high y i Hy Hb). reflexivity.
Qed.

(* `not` (`xori -1`) of a word is all ones minus the word (0x81414). *)
Lemma gse_lxor_ones : forall y, 0 <= y < 2 ^ 64 -> Z.lxor y (2 ^ 64 - 1) = 2 ^ 64 - 1 - y.
Proof.
intros y Hy. replace (2 ^ 64 - 1) with (Z.ones 64) by (vm_compute; reflexivity).
assert (Hl : Z.land y (Z.lxor y (Z.ones 64)) = 0).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.lxor_spec, Z.bits_0.
  destruct (Z.testbit y i) eqn:Eb; cbn [andb]; [|reflexivity].
  rewrite Z.testbit_ones by lia. rewrite (proj2 (Z.leb_le 0 i) Hi). cbn [andb].
  destruct (i <? 64) eqn:Hb; [reflexivity|].
  apply Z.ltb_ge in Hb. rewrite (gse_bit_high y i Hy Hb) in Eb. discriminate. }
pose proof (Z.add_nocarry_lxor y (Z.lxor y (Z.ones 64)) Hl) as Hs.
rewrite <- Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_l in Hs. lia.
Qed.

(* The three bytes of the head-amp table the layout does not name are padding; the
   layout names no other byte outside [0, 460). *)
Lemma gse_tx_fbyte_pad : forall i, HeadampLayout.tx_fbyte i = true ->
  0 <= i < 460 /\ i <> 438 /\ i <> 439 /\ i <> 451.
Proof.
intros i Hi. unfold HeadampLayout.tx_fbyte, HeadampLayout.lay_byte in Hi.
apply existsb_exists in Hi as ([o w] & Hin & Hb).
cbn [fst snd] in Hb. apply andb_prop in Hb as [H1 H2].
apply Z.leb_le in H1. apply Z.ltb_lt in H2.
unfold HeadampLayout.LAY_TX in Hin. apply in_app_iff in Hin as [Hin | Hin].
- apply in_map_iff in Hin as (q & Hq & Hqs). injection Hq as E1 E2. subst o w.
  apply in_seq in Hqs. cbn [Z.of_N] in H2. lia.
- cbn [In] in Hin.
  repeat (destruct Hin as [Heq | Hin];
    [ injection Heq as E1 E2; subst o w; cbn [Z.of_N] in H2; lia |]).
  destruct Hin.
Qed.

(* The sweep the builder lays down: 8 + 3 w rows of 34 bytes. *)
Lemma gse_length_chans : forall base vals l,
  length (concat (map (ga_chan base vals) l)) = (102 * length l)%nat.
Proof.
intros base vals l. induction l as [|c l IH]; [reflexivity|].
cbn [map concat length]. rewrite length_app, IH.
unfold ga_chan, ga_row. rewrite !length_app, !length_GA. lia.
Qed.

Lemma gse_length_sweep : forall base w vals, (1 <= w)%nat ->
  Z.of_nat (length (SWEEP base w vals)) = 34 * (8 + 3 * Z.of_nat w).
Proof.
intros base w vals Hw. unfold SWEEP. rewrite !length_app, gse_length_chans, length_seq.
unfold ga_chan, ga_row. rewrite !length_app, !length_GA.
change (length HEAD_ACK34) with 34%nat. change (length HEAD_MARK34) with 34%nat.
change (length GBall) with 204%nat. lia.
Qed.

(* ---- the symbolic state of the runs ---- *)
(* After the call: atom 32 is a.width, the byte at 1(s8); the registers are their own
   atoms 0 .. 31, so the builder's answer is atom 10 and the buffer atom 27. The frame
   region over atom 9 lets the runs write slot 88 and nothing else. *)
Definition gse_regions : YP09.smem :=
  [ YP09.mkRegion (Some 24%nat) 0 2 0 0 [YP09.mkChunk 1 (CVal 1 (SOff 32 0))];
    YP09.mkRegion (Some 9%nat) 0 192 88 96 [] ].
Definition gse_extra (aw : Z) : list word := [w64 aw].

(* The value the code recomputes at 0x813ec .. 0x81404 from a.width (atom 32) and the
   row count (s4, x20) and compares the builder's answer with: 8 + 3 * a.width, or all
   ones when the rows do not fit. *)
Definition gse_want : sv :=
  SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_SLL (SExt false 8 (SOff 32 0)) (SLit 1))
                             (SExt false 8 (SOff 32 0))) (SLit 8).
Definition gse_ansv : sv :=
  SAlu ALU_OR (SAlu ALU_SUB (SLit 0) (SAlu ALU_SLTU (SOff 20 0) gse_want)) gse_want.

Lemma gse_want_U : forall (E : env) aw, ew E 32 = w64 aw -> 0 <= aw < 256 ->
  U E gse_want = 8 + 3 * aw.
Proof.
intros E aw H32 Haw. unfold gse_want.
rewrite !U_SAlu. cbn [zalu_raw].
rewrite U_SExt. rewrite (U_atom E 32 aw H32 ltac:(lia)).
cbn [Z.of_N]. rewrite (Z.mod_small aw (2 ^ 8)) by lia.
rewrite (zcanon_id aw) by (unfold M64; lia).
rewrite (U_lit E 1) by lia. rewrite (U_lit E 8) by lia.
change (Z.land 1 63) with 1. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
rewrite (zcanon_id (aw * 2)) by (unfold M64; lia).
rewrite (zcanon_id (aw * 2 + aw)) by (unfold M64; lia).
rewrite (zcanon_id (aw * 2 + aw + 8)) by (unfold M64; lia). lia.
Qed.

Lemma gse_ansv_U : forall (E : env) aw rows,
  ew E 32 = w64 aw -> ew E 20 = w64 rows -> 0 <= aw < 256 -> 0 <= rows < 256 ->
  U E gse_ansv = (if 8 + 3 * aw <=? rows then 8 + 3 * aw else 2 ^ 64 - 1).
Proof.
intros E aw rows H32 H20 Haw Hrows. unfold gse_ansv.
rewrite U_SAlu. cbn [zalu_raw].
rewrite (gse_want_U E aw H32 Haw).
rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_lit E 0) by lia.
rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E 20 rows H20 ltac:(lia)).
rewrite (gse_want_U E aw H32 Haw).
destruct (Z.ltb_spec rows (8 + 3 * aw)) as [Hlt | Hge].
- replace (8 + 3 * aw <=? rows) with false by (symmetry; apply Z.leb_gt; lia).
  rewrite (zcanon_id 1) by (unfold M64; lia).
  replace (zcanon (0 - 1)) with (2 ^ 64 - 1) by (unfold zcanon, M64; vm_compute; reflexivity).
  rewrite (gse_lor_ones (8 + 3 * aw)) by lia.
  apply zcanon_id. unfold M64. lia.
- replace (8 + 3 * aw <=? rows) with true by (symmetry; apply Z.leb_le; lia).
  rewrite (zcanon_id 0) by (unfold M64; lia).
  replace (zcanon (0 - 0)) with 0 by (unfold zcanon, M64; vm_compute; reflexivity).
  rewrite Z.lor_0_l. apply zcanon_id. unfold M64. lia.
Qed.

(* The word the store at 0x81418 writes: the engine keeps `not a1,s11` as `xori a1,s11,-1`. *)
Lemma gse_den_not : forall (E : env) n v, ew E n = w64 v -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SAlu ALU_XOR (SOff n 0) (SLit (-1))) = Z_to_bv 64 (2 ^ 64 - 1 - v).
Proof.
intros E n v Hn Hv. rewrite (denot_lit_U E _). f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E n v Hn Hv), U_SLit.
replace (zcanon (-1)) with (2 ^ 64 - 1) by (unfold zcanon, M64; vm_compute; reflexivity).
rewrite (gse_lxor_ones v Hv). apply zcanon_id. unfold M64. lia.
Qed.

(* ---- a run that writes at most the window [lo, lo + 8) ---- *)
Definition gse_kept (lo : Z) (m m' : word -> option byte) : Prop :=
  forall x : word, ~ (lo <= bv_unsigned x < lo + 8) -> m' x = m x.

Lemma gse_kept_of_frame : forall (E : env) rs (m m' : word -> option byte) lo,
  frame_of E rs m m' -> (forall a, in_wrange E rs a -> lo <= a < lo + 8) -> gse_kept lo m m'.
Proof. intros E rs m m' lo HF Hw x Hx. apply HF. intros Hin. apply Hx, Hw, Hin. Qed.

Lemma gse_kept_trans : forall lo (m1 m2 m3 : word -> option byte),
  gse_kept lo m1 m2 -> gse_kept lo m2 m3 -> gse_kept lo m1 m3.
Proof. intros lo m1 m2 m3 H12 H23 x Hx. rewrite (H23 x Hx). exact (H12 x Hx). Qed.

(* Every write window of a region list is the window [lo, lo + 8) of the frame. *)
Ltac gse_win U9 :=
  let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Ha := fresh "Ha" in
  intros a (r & Hin & Ha); cbn in Hin;
  repeat (destruct Hin as [<- | Hin];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Ha; rewrite ?U9 in Ha; lia |]);
  destruct Hin.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).

Lemma gse_kept_aview : forall (H : word -> bool) (m m' : word -> option byte) lo,
  gse_kept lo m m' -> forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < lo + 8) ->
  aview SEGS H m' a = aview SEGS H m a.
Proof.
intros H m m' lo HK a Ha Hn. apply (aview_eq_of SEGS H). unfold mrestrict. cbv beta.
rewrite (HK (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by lia. exact Hn.
Qed.

(* A byte of a region whose value the environment holds in an atom. *)
Lemma gse_atom_byte_chunk : forall (W : world SEGS) (E : env) (mem : word -> option byte) base off n v,
  ew E n = w64 v -> 0 <= v < 256 ->
  aview SEGS (w_H W) mem (base + off) = Some v ->
  YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) base (YP09.mkChunk off (CVal 1 (SOff n 0))).
Proof.
intros W E mem base off n v He Hv Hr.
apply (chunk_ok_val SEGS E (mrestrict (w_H W) mem) base off 1%N (SOff n 0) v).
- cbn [sv_denot]. rewrite He. unfold w64. rewrite unsigned_lit_small by lia.
  rewrite Z.add_0_r. reflexivity.
- change (8 * Z.of_N 1) with 8. change (2 ^ 8) with 256. exact Hv.
- cbn [Z.of_N]; lia.
- exact (gs_val_mem_of_byte (w_H W) mem _ v Hr).
Qed.

(* The two bytes of `a` in the frame on the side stack for frames, as a region over
   the register the code reads them through (x24). *)
Lemma gse_areg_ok : forall (W : world SEGS) (E : env) (mem : word -> option byte) base cs,
  bv_unsigned (ew E 24%nat) = base -> 0 <= base -> base + 2 <= 2 ^ 64 ->
  Forall (YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) base) cs ->
  YP09.region_ok SEGS E (mrestrict (w_H W) mem) (YP09.mkRegion (Some 24%nat) 0 2 0 0 cs).
Proof.
intros W E mem base cs Hb H0 H1 Hcs. unfold YP09.region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
rewrite Hb. split; [lia|]. split; [lia|]. split; [intros o Ho; lia | exact Hcs].
Qed.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.

(* The image's read-only bytes are what they were: this call takes no footprint of
   its own, so the journal keeps every byte of the image the walk may read. *)
Lemma gse_rod : forall STK sp0 ly S W mem md own ly' S' W' mem' md' k,
  ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W') mem').
Proof.
intros STK sp0 ly S W mem md own ly' S' W' mem' md' k HJ HR a Hro Ho He.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
rewrite (F3 a); [exact (HR a Hro Ho He) | | exact Ho | exact He |
  apply fp_spares_closed; exact sink_closed_nil].
destruct Hro as [(sg & Hs & _ & Hr) | Hgot]; [exists sg; split; [exact Hs | exact Hr]|].
exact (pa_relro_img a Hgot).
Qed.

Hypothesis LAWS : AR_laws SEGS B.
Hypothesis MTF : ameter_fs_laws MT.
Hypothesis TBSW : tb_reac_grant_build_sweep_spec B.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let BR := paj_branch (PI := PI).

(* An address the walk keeps across the call and outside the window of slot 88. *)
Local Ltac gse_pk :=
  split; [unfold gs_keep_at; try change (Z.of_nat GE_NSH) with 104;
          try change (fs_frame_bytes GE_CID) with 1024;
          first [ left; lia | right; left; lia | right; right; left; lia
                | right; right; right; left; lia | right; right; right; right; lia ]
         | split; lia ].

(* A constant the code loads with `addi rd,zero,imm`; the engine keeps it as a literal. *)
Local Ltac gse_const HS r :=
  let RR := fresh "RR" in prreg HS r RR; rewrite RR; apply bv_eq; vm_compute; reflexivity.

(* The write windows of the runs after the call. *)
Local Ltac gse_awr U9 :=
  lazymatch goal with |- awr_ok ?Ey ?rs ?stk ?sp0 ?fp ?b0 ?bc ?lyy ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok Ey rs' stk sp0 fp b0 bc lyy own) end;
  apply awr_ok_cons_ro; [cbn; lia|];
  lazymatch goal with |- awr_ok _ _ _ ?sp0 _ _ _ _ _ =>
    lazymatch goal with Hs1 : bv_unsigned (ew _ 9%nat) = ?sp1 |- _ =>
      eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (sp1 - sp0));
        [ reflexivity | rewrite U9; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia
        | apply awr_ok_nil ] end end.

Lemma gse_mal :
  ge_from B MT (ge_post B MT) (GIS_rowhd B MT) ->
  ge_from B MT (ge_post B MT) (GIS_free1 B MT) ->
  ge_from B MT (ge_post B MT) (GIS_mal B MT).
Proof.
intros HROW HFREE cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HGI.
destruct HGI as (t & s & HBODY & Hk & Hacc & HBLK & SL88 & R10 & R27 & R20 & R24 & R18 & R19).
destruct HBLK as (Eab & Hsin & HTAB & HWAS & HSET & HREL & HI1 & SLOTS & Hn26 & Ht0 & Hs0 & Hok & HA0 & HA1).
pose proof SLOTS as (SL8 & SL16 & SL40 & SL48 & SL56 & SL64 & SL72 & SL80 & SL96 & SL104 & SL112 & SL120
  & SL128 & SL136 & SL144 & SL152).
pose proof HBODY as (Hpc & Hresv & Hsvc & Hrom & Hfrg & Hfcsr & HREGS & HSAVED & HSH & HFL & HLEN & HINP).
pose proof HREGS as (R2 & R8 & R9 & R3 & R4).
pose proof HB as (HPRE & H10 & H11 & Hpn & HPL & Hfr0 & Hev & Hlive & HROD & Hsp1d & HE0 & HE02 & HE032
  & HMOK & HTR & HNEED).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hchain & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof pa_base_lo as HBLO. rewrite IMG_LO_B_val in HBLO.
pose proof HJ as HJ0.
pose proof HJ as (HAR3 & Hly3 & _ & _ & _ & Hfrs3 & Hnev3 & Hk0 & JK1 & _).
pose proof Hly3 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
assert (FFS : GE_STK = 32768) by reflexivity.
assert (Has : ASTACK = 16384) by reflexivity.
assert (Hfb : fs_frame_bytes GE_CID = 1024) by (vm_compute; reflexivity).
assert (Hsp288 : 0 <= spZ (c_regs cx) + -288) by lia.
assert (Hmod288 : (spZ (c_regs cx) + -288) mod 16 = 0)
  by (rewrite <- Zplus_mod_idemp_l, Hal16; reflexivity).
destruct (sp1_facts (spZ (c_regs cx) + -288) Hsp288 Hmod288) as (Hsp1r & Hsp1al32 & Hsp1al16).
rewrite <- Hsp1d in Hsp1r, Hsp1al32, Hsp1al16.
assert (Hsp1lo : alloc_ceiling <= c_sp1 cx) by lia.
assert (Hsp1hi : c_sp1 cx + 192 <= 2 ^ 64) by lia.
destruct (al_layout _ _ LAWS (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) ly3 HAR0 Hly3)
  as (Eabl & Efa & Eown).
assert (EFA : frame_addr ly3 GE_CID fp = gF cx fp) by (unfold gF; rewrite Efa; reflexivity).
assert (HtIn : In (t, 460) (ablocks B ly3 S3)) by (destruct HTAB as (HH & _); exact HH).
assert (HpIn : 0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly3 S3)).
{ intros Hn. rewrite Eab. apply in_or_app. left.
  destruct Hpn as [(Hz & _) | (_ & Hin)]; [lia | exact Hin]. }
assert (HfrIn : In (GE_CID, fp) (YG01.frames S3)) by (rewrite HFR; left; reflexivity).
pose proof (gs_mbytes_range (c_pl cx)) as Hswr.
pose proof (gs_rows_range (c_pl cx)) as Hrows.
assert (Hnotin : ~ In (s, sw_mbytes (c_pl cx)) (ablocks B (c_ly cx) (c_S cx) ++ [(t, 460)])).
{ apply (gs_blocks_tail B ly3 S3 W3 (ms_mem ms3) md3 (ablocks B (c_ly cx) (c_S cx)) (t, 460)
    (s, sw_mbytes (c_pl cx)) LAWS HAR3 ltac:(cbn [snd]; lia)).
  rewrite Eab. reflexivity. }
assert (Htne : (t, 460) <> (s, sw_mbytes (c_pl cx)))
  by (intros Heq; apply Hnotin; apply in_or_app; right; left; exact Heq).
assert (Hpne : 0 < c_n cx -> (c_p cx, c_n cx) <> (s, sw_mbytes (c_pl cx))).
{ intros Hn Heq. apply Hnotin. apply in_or_app. left. rewrite <- Heq.
  destruct Hpn as [(Hz & _) | (_ & Hin)]; [lia | exact Hin]. }
assert (GEO : gs_geo cx fp t s (sw_mbytes (c_pl cx))).
{ apply (gs_geo_of B cx fp t s (sw_mbytes (c_pl cx)) ly3 S3 W3 (ms_mem ms3) md3 LAWS HAR3 HtIn Htne
    ltac:(intros Hn; split; [exact (HpIn Hn) | exact (Hpne Hn)]) Hsin HfrIn EFA Hsp1lo Hsp1hi). }
assert (Hpn64 : c_p cx + c_n cx <= 2 ^ 64).
{ destruct Hpn as [(Hz & Hemp) | (Hn & Hin)].
  - rewrite Hz, Hemp. unfold GE_EMPTY, A_EMPTY_B. lia.
  - destruct (al_blocks _ _ LAWS (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) (c_p cx) (c_n cx) HAR0 Hin)
      as (_ & _ & Hce & _). pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hq]. lia. }
assert (Hpceil : 0 < c_n cx -> 0 <= c_p cx /\ c_p cx + c_n cx <= alloc_ceiling).
{ intros Hn. destruct Hpn as [(Hz & _) | (_ & Hin)]; [lia|].
  destruct (al_blocks _ _ LAWS (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) (c_p cx) (c_n cx) HAR0 Hin)
    as (_ & Hp4096 & Hce & _). pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hq]. lia. }
(* the frame on the side stack: where it is and how it is aligned *)
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 GE_CID fp HAR3 HfrIn) as (HF0 & HFc & HFia).
destruct (al_frames _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 GE_CID fp HAR3 HfrIn) as (Hf32 & _).
rewrite EFA in HF0, HFc, HFia, Hf32.
rewrite Hfb in HFc, HFia.
assert (HgF8 : gF cx fp mod 8 = 0).
{ apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hf32; [|lia].
  destruct Hf32 as [q Hq]. exists (4 * q). lia. }
destruct (proj1 (Z.mod_divide (gF cx fp) 8 ltac:(lia)) HgF8) as [q8 Hq8].
assert (Hshlo : 0 <= gSH cx fp /\ gSH cx fp + 128 <= alloc_ceiling).
{ unfold gSH, shadow_of_addr, SHADOW_OFF.
  assert (Hd0 : 0 <= gF cx fp / 8) by (apply Z.div_pos; lia).
  assert (Hd1 : gF cx fp / 8 <= 17592184995840) by (apply Z.div_le_upper_bound; lia). lia. }
destruct Hshlo as (Hsh0 & Hshc).
(* the table and the block the malloc gave *)
destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 t 460 HAR3 HtIn) as (_ & Ht4096 & Htceil & _).
change (req_size 460) with 460 in Htceil.
destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 s (sw_mbytes (c_pl cx)) HAR3 Hsin)
  as (Hs16 & Hs4096 & Hsceil & Hsapp & _).
pose proof (req_size_pos (sw_mbytes (c_pl cx)) ltac:(lia)) as [Hrq1 Hrq2].
(* the two bytes of `a` *)
assert (Habr : 0 <= sw_base (c_pl cx) < 256)
  by (exact (gs_byte_range (w_H W3) (ms_mem ms3) _ _ HA0)).
assert (Hawr : 0 <= sw_in (c_pl cx) < 256)
  by (exact (gs_byte_range (w_H W3) (ms_mem ms3) _ _ HA1)).
destruct (gs_ok_range (c_pl cx) Hok) as (Hb0 & Hw0 & Hbw).
destruct (SegSetModel.tables_end_inv (c_pl cx)) as (HTL & HwsL & HstL & _).
(* ---- run 1: 0x813dc -> the call of reac_grant_build_sweep at 0x813e8 ---- *)
assert (Ems3 : ms3 = mkst (ms_regs ms3) (Z_to_bv 64 (BASE + GPS_mal)) (ms_mem ms3) (seg_rom SEGS)).
{ clear - Hpc Hresv Hsvc Hrom Hfrg Hfcsr. destruct ms3; cbn in *; subst; reflexivity. }
pose proof (gs_seat W3 (ms_regs ms3) (ms_mem ms3) [] GPS_mal [] []
   ltac:(vm_compute; reflexivity) ltac:(apply Forall_nil) ltac:(cbn; tauto) I) as HS.
rewrite <- Ems3 in HS.
remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms3) r)
  by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
clear HE.
paj_run_shc RUNP RUNC HS HJ.
{ apply awr_ok_nil. }
lazymatch goal with HFx : frame_of _ ?rs ?m (ms_mem ?msn) |- _ =>
  pose proof (frame_of_read_only _ rs m (ms_mem msn) ltac:(vm_compute; reflexivity) HFx) as HM end.
clear HF HFr HG.
assert (QSP : getr (ms_regs ms) 2 = w64 (c_sp1 cx))
  by (prreg HS (2%bv : bv 5) RR; rewrite RR, (EE 2%nat 2%bv eq_refl); exact R2).
assert (QGP : getr (ms_regs ms) 3 = w64 (as_gp B))
  by (prreg HS (3%bv : bv 5) RR; rewrite RR, (EE 3%nat 3%bv eq_refl), R3; exact Hgp).
assert (QTP : getr (ms_regs ms) 4 = w64 (as_tp B))
  by (prreg HS (4%bv : bv 5) RR; rewrite RR, (EE 4%nat 4%bv eq_refl), R4; exact Htp).
assert (QS0 : getr (ms_regs ms) 8 = w64 (spZ (c_regs cx)))
  by (prreg HS (8%bv : bv 5) RR; rewrite RR, (EE 8%nat 8%bv eq_refl); exact R8).
assert (QS1 : getr (ms_regs ms) 9 = w64 (c_sp1 cx))
  by (prreg HS (9%bv : bv 5) RR; rewrite RR, (EE 9%nat 9%bv eq_refl); exact R9).
assert (QA0 : getr (ms_regs ms) 10 = w64 s)
  by (prreg HS (10%bv : bv 5) RR; rewrite RR, (EE 10%nat 10%bv eq_refl); exact R10).
(* 0x813dc .. 0x813e4: `mv a1,s4`, `mv a2,s8`, `mv a3,s2` *)
assert (QA1 : getr (ms_regs ms) 11 = w64 (sw_rows (c_pl cx)))
  by (prreg HS (11%bv : bv 5) RR; rewrite RR, (EE 20%nat 20%bv eq_refl); exact R20).
assert (QA2 : getr (ms_regs ms) 12 = w64 (gF cx fp + GO_A))
  by (prreg HS (12%bv : bv 5) RR; rewrite RR, (EE 24%nat 24%bv eq_refl); exact R24).
assert (QA3 : getr (ms_regs ms) 13 = w64 t)
  by (prreg HS (13%bv : bv 5) RR; rewrite RR, (EE 18%nat 18%bv eq_refl); exact R18).
assert (Q19 : getr (ms_regs ms) 19 = w64 (gSH cx fp))
  by (prreg HS (19%bv : bv 5) RR; rewrite RR, (EE 19%nat 19%bv eq_refl); exact R19).
assert (Q20 : getr (ms_regs ms) 20 = w64 (sw_rows (c_pl cx)))
  by (prreg HS (20%bv : bv 5) RR; rewrite RR, (EE 20%nat 20%bv eq_refl); exact R20).
assert (Q24 : getr (ms_regs ms) 24 = w64 (gF cx fp + GO_A))
  by (prreg HS (24%bv : bv 5) RR; rewrite RR, (EE 24%nat 24%bv eq_refl); exact R24).
assert (Q27 : getr (ms_regs ms) 27 = w64 s)
  by (prreg HS (27%bv : bv 5) RR; rewrite RR, (EE 27%nat 27%bv eq_refl); exact R27).
assert (QRA : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + 0x9b0))
  by (prreg HS (1%bv : bv 5) RR; exact RR).
(* the chain this call hands to the callee *)
assert (HCH : achain ly3 (aview SEGS (w_H W3) (ms_mem ms)) (c_sp1 cx) (s0Z (ms_regs ms)) (gch cx)).
{ assert (Hrd : forall a, spZ (c_regs cx) <= a < 2 ^ 64 ->
    aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H (c_W cx)) (c_mem cx) a).
  { intros a Ha. pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _). apply F1; lia. }
  assert (H8 : rdword (aview SEGS (w_H W3) (ms_mem ms)) (spZ (c_regs cx) - 8) = Some (raZ (c_regs cx)))
    by (rewrite HM; exact (proj1 HSAVED)).
  assert (H16 : rdword (aview SEGS (w_H W3) (ms_mem ms)) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx))).
  { rewrite HM. pose proof (proj2 HSAVED 0 ltac:(lia)) as Hj0.
    replace (spZ (c_regs cx) - 16 - 8 * 0) with (spZ (c_regs cx) - 16) in Hj0 by lia.
    cbn [Z.ltb Z.compare] in Hj0. exact Hj0. }
  assert (ES0 : s0Z (ms_regs ms) = spZ (c_regs cx))
    by (unfold s0Z; rewrite QS0; unfold w64; apply unsigned_lit_small; lia).
  rewrite ES0.
  exact (achain_ly_top (c_ly cx) ly3 _ _ _ _ Etop
    (ge_achain B MT cx HB (aview SEGS (w_H W3) (ms_mem ms)) (c_sp1 cx) Hrd H8 H16 ltac:(lia))). }
assert (HTBS : STK_reac_grant_build_sweep = 4832) by (vm_compute; reflexivity).
pmkst HS. rewrite pa_sigma_reac_grant_build_sweep.
eapply SRr_bind.
{ eapply (cl_callS B LAWS W3 (ms_regs ms) (ms_mem ms) _ GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx)
    (c_W cx) (c_mem cx) (c_md cx) [(GE_CID, fp)] ly3 S3 _ k STK_reac_grant_build_sweep _ 0
    (c_sp1 cx - spZ (c_regs cx)) (Z_to_bv 64 (BASE + 0x9b0)) (gch cx) _ HJ).
  - unfold spZ. rewrite QSP. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - pose proof (proj1 (Z.mod_divide (c_sp1 cx) 16 ltac:(lia)) Hsp1al16) as [q1 Hq1].
    pose proof (proj1 (Z.mod_divide (spZ (c_regs cx)) 16 ltac:(lia)) Hal16) as [q2 Hq2].
    rewrite Hq1, Hq2. replace (q1 * 16 - q2 * 16) with ((q1 - q2) * 16) by lia. apply Z_mod_mult.
  - lia.
  - lia.
  - lia.
  - exact QGP.
  - exact QTP.
  - exact QRA.
  - apply (ret_ok_codeptr_v 0x9b0 ltac:(lia) ltac:(reflexivity)).
  - rewrite unsigned_lit_small by lia. lia.
  - replace (spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx))) with (c_sp1 cx) by lia. exact HCH.
  - (* the callee's contract: every premise from the cut *)
    intros HPRE2.
    eapply SRr_mono.
    { apply (TBSW ly3 S3 W3 (ms_regs ms) (ms_mem ms) _ (gch cx) s (sw_rows (c_pl cx))
        (gF cx fp + GO_A) t (sw_base (c_pl cx)) (sw_in (c_pl cx)) (T_end (c_pl cx)) HPRE2).
      - (* the live-frame bound: one frame, the entry function's *)
        rewrite HFR. cbn [length]. lia.
      - (* the stack top: s1 is 288 bytes and more under the entry sp *)
        unfold spZ. rewrite QSP. unfold w64. rewrite unsigned_lit_small by lia. rewrite Etop. lia.
      - (* the read-only data, carried across the first call by the journal *)
        rewrite HM. exact (gse_rod _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0 HROD).
      - exact QA0.
      - exact QA1.
      - exact QA2.
      - exact QA3.
      - (* the buffer is a heap block under the ceiling *) lia.
      - (* the row count is a byte *) lia.
      - unfold GO_A. lia.
      - (* `a`: in the entry function's frame, 8-aligned, its granule marked 02, and its bytes *)
        intros _. rewrite HM. split.
        + split.
          * exists GE_CID, fp. split; [exact HfrIn|]. split; [unfold GE_CID; lia|].
            rewrite EFA, Hfb. split; [exact HgF8|]. split; [unfold GO_A; lia | unfold GO_A; lia].
          * split; [unfold GO_A; rewrite Hq8; rewrite Z.add_comm, Z_mod_plus_full; reflexivity|].
            intros x Hx. exists 2. unfold GO_A in Hx.
            assert (Hxd : x / 8 = q8 + 56).
            { replace x with (q8 * 8 + (x - q8 * 8)) by lia. rewrite Z.div_add_l by lia.
              assert (Hr2 : x - q8 * 8 = 448 \/ x - q8 * 8 = 449) by lia.
              destruct Hr2 as [-> | ->]; reflexivity. }
            assert (Hsa : shadow_of_addr SHADOW_OFF x = gSH cx fp + Z.of_nat 56).
            { unfold gSH, shadow_of_addr. rewrite Hxd, Hq8.
              rewrite (Z.div_mul q8 8) by lia. cbn [Z.of_nat]. lia. }
            rewrite Hsa. split.
            { assert (HL : (56 < length GSH_a)%nat) by (rewrite HLEN; unfold GE_NSH; lia).
              rewrite (HSH 56%nat HL). vm_compute. reflexivity. }
            { unfold saddr_ok. right. split; [|lia].
              replace x with ((x - q8 * 8) + q8 * 8) by lia. rewrite Z_mod_plus_full.
              assert (Hr2 : x - q8 * 8 = 448 \/ x - q8 * 8 = 449) by lia.
              destruct Hr2 as [-> | ->]; reflexivity. }
        + intros j Hj. cbn [length] in Hj. destruct j as [|[|j]]; [| |cbn in Hj; lia].
          * cbn [nth Z.of_nat]. rewrite Z.add_0_r.
            split; [exact (gs_val_mem_of_byte (w_H W3) (ms_mem ms3) _ _ HA0) | lia].
          * cbn [nth]. split; [|lia].
            replace (gF cx fp + GO_A + Z.of_nat 1) with (gF cx fp + (GO_A + 1)) by lia.
            exact (gs_val_mem_of_byte (w_H W3) (ms_mem ms3) _ _ HA1).
      - (* the table's block *) exact HtIn.
      - (* the table's length *) destruct HTAB as (_ & _ & HLT & _). exact HLT.
      - (* the table's fields, from the bytes the cut names *)
        rewrite HM.
        apply (proj2 (HeadampLayout.tx_obj_bytes SEGS (mrestrict (w_H W3) (ms_mem ms3)) t (T_end (c_pl cx)))).
        intros i Hi. destruct (gse_tx_fbyte_pad i Hi) as (Hir & H438 & H439 & H451).
        destruct HTAB as (_ & _ & _ & HB460).
        rewrite <- (HeadampLayout.tb_nth (T_end (c_pl cx)) i).
        exact (gs_mbyte_byte (w_H W3) (ms_mem ms3) (t + i) _ (HB460 i Hir H438 H439 H451)
          (HeadampLayout.tb_range (T_end (c_pl cx)) i)).
      - (* tx_set01, from SlotNeeds_c.I1 *) exact (BuildSweepLink.I1_set01 _ HI1).
      - (* tx_legal, from SlotNeeds_c.I1 *) exact (BuildSweepLink.I1_legal _ HI1).
      - (* the row buffer: the sweep block holds the 8 + 3 w rows *)
        intros Hbs. exists s, (sw_mbytes (c_pl cx)). split; [exact Hsin|].
        apply bsw_ok_spec in Hbs as (_ & _ & Hw & _ & _ & Hmx).
        assert (Hmb : sw_mbytes (c_pl cx) = 34 * sw_rows (c_pl cx))
          by (unfold sw_mbytes; rewrite (proj2 (Z.ltb_lt 0 _)) by lia; reflexivity).
        lia. }
    cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & Hc2 & HJc & HPc & HKc).
    exists ly2, S2, regs2, mem2, md2. rewrite QRA in Hc2.
    split; [exact Hc2|]. split; [exact HJc|]. split; [exact HPc | exact HKc].
  - (* the rows the call may write lie inside the sweep buffer *)
    intros a Ha. right. exists s, (sw_mbytes (c_pl cx)).
    split; [exact Hsin|]. split.
    { intros Hin. apply Hnotin. apply in_or_app. left. exact Hin. }
    unfold tb_reac_grant_build_sweep_FP in Ha.
    destruct (bsw_ok s (gF cx fp + GO_A) (sw_rows (c_pl cx)) (sw_base (c_pl cx)) (sw_in (c_pl cx)))
      eqn:HBS.
    + destruct Ha as (r & [<- | []] & Hr). cbn [fst snd] in Hr.
      apply bsw_ok_spec in HBS as (_ & _ & Hw & _ & _ & Hmx).
      assert (Hmb : sw_mbytes (c_pl cx) = 34 * sw_rows (c_pl cx))
        by (unfold sw_mbytes; rewrite (proj2 (Z.ltb_lt 0 _)) by lia; reflexivity).
      lia.
    + destruct Ha as (r & [] & _). }
(* ---- the call is done ---- *)
cbv beta. intros W2 c2 Hwle (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJ1 & HP2 & HKc).
destruct HKc as (Hfrs2 & Eab2 & (fset & ES2) & Ha0 & HSWP).
replace (spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx))) with (c_sp1 cx) in HJ1 by lia.
assert (KEEP : gs_keepW cx fp t W3 W2 (ms_mem ms) mem2).
{ apply (gs_keep_of_journal B cx fp t s (sw_mbytes (c_pl cx)) ly3 S3 W3 (ms_mem ms) _ ly2 S2 W2 mem2 md2
    STK_reac_grant_build_sweep _ 0 HJ1); [| exact Eab2 | exact HtIn | exact HpIn | exact HFR | exact EFA | exact GEO].
  intros a Ha. unfold tb_reac_grant_build_sweep_FP in Ha.
  destruct (bsw_ok s (gF cx fp + GO_A) (sw_rows (c_pl cx)) (sw_base (c_pl cx)) (sw_in (c_pl cx)))
    eqn:HBS.
  - destruct Ha as (r & [<- | []] & Hr). cbn [fst snd] in Hr.
    apply bsw_ok_spec in HBS as (_ & _ & Hw & _ & _ & Hmx).
    assert (Hmb : sw_mbytes (c_pl cx) = 34 * sw_rows (c_pl cx))
      by (unfold sw_mbytes; rewrite (proj2 (Z.ltb_lt 0 _)) by lia; reflexivity).
    lia.
  - destruct Ha as (r & [] & _). }
assert (KEEP3 : gs_keepW cx fp t W3 W2 (ms_mem ms3) mem2) by (rewrite <- HM; exact KEEP).
(* the answer, as a number the walk can read *)
assert (HBOK : bsw_ok s (gF cx fp + GO_A) (sw_rows (c_pl cx)) (sw_base (c_pl cx)) (sw_in (c_pl cx))
               = (8 + 3 * sw_in (c_pl cx) <=? sw_rows (c_pl cx)))
  by (apply bsw_ok_go; [lia | unfold GO_A; lia | lia | lia | lia]).
pose proof (fun H => HSWP H) as HSW2. rewrite HBOK in Ha0, HSW2.
assert (Qa0 : getr regs2 10
              = w64 (if 8 + 3 * sw_in (c_pl cx) <=? sw_rows (c_pl cx)
                     then 8 + 3 * sw_in (c_pl cx) else 2 ^ 64 - 1)).
{ rewrite Ha0. destruct (8 + 3 * sw_in (c_pl cx) <=? sw_rows (c_pl cx)); [reflexivity|].
  unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. vm_compute. reflexivity. }
(* the registers the call kept *)
assert (P2 : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs2 r = getr (ms_regs ms) r)
  by (intros r Hr; exact (gs_kept_reg (ms_regs ms) regs2 r HP2 Hr)).
assert (Q2sp : getr regs2 2 = w64 (c_sp1 cx)).
{ rewrite (P2 (2%bv : bv 5) ltac:(assert (HX : bv_unsigned (2%bv : bv 5) = 2) by (vm_compute; reflexivity);
    unfold acallee_saved; rewrite HX; lia)). exact QSP. }
assert (Q2gp : getr regs2 3 = getr (c_regs cx) 3).
{ rewrite (P2 (3%bv : bv 5) ltac:(assert (HX : bv_unsigned (3%bv : bv 5) = 3) by (vm_compute; reflexivity);
    unfold acallee_saved; rewrite HX; lia)). rewrite QGP. symmetry. exact Hgp. }
assert (Q2tp : getr regs2 4 = getr (c_regs cx) 4).
{ rewrite (P2 (4%bv : bv 5) ltac:(assert (HX : bv_unsigned (4%bv : bv 5) = 4) by (vm_compute; reflexivity);
    unfold acallee_saved; rewrite HX; lia)). rewrite QTP. symmetry. exact Htp. }
assert (Q2s0 : getr regs2 8 = w64 (spZ (c_regs cx))).
{ rewrite (P2 (8%bv : bv 5) ltac:(assert (HX : bv_unsigned (8%bv : bv 5) = 8) by (vm_compute; reflexivity);
    unfold acallee_saved; rewrite HX; lia)). exact QS0. }
assert (Q2s1 : getr regs2 9 = w64 (c_sp1 cx)).
{ rewrite (P2 (9%bv : bv 5) ltac:(assert (HX : bv_unsigned (9%bv : bv 5) = 9) by (vm_compute; reflexivity);
    unfold acallee_saved; rewrite HX; lia)). exact QS1. }
assert (Q2_19 : getr regs2 19 = w64 (gSH cx fp)).
{ rewrite (P2 (19%bv : bv 5) ltac:(assert (HX : bv_unsigned (19%bv : bv 5) = 19) by (vm_compute; reflexivity);
    unfold acallee_saved; rewrite HX; lia)). exact Q19. }
assert (Q2_20 : getr regs2 20 = w64 (sw_rows (c_pl cx))).
{ rewrite (P2 (20%bv : bv 5) ltac:(assert (HX : bv_unsigned (20%bv : bv 5) = 20) by (vm_compute; reflexivity);
    unfold acallee_saved; rewrite HX; lia)). exact Q20. }
assert (Q2_24 : getr regs2 24 = w64 (gF cx fp + GO_A)).
{ rewrite (P2 (24%bv : bv 5) ltac:(assert (HX : bv_unsigned (24%bv : bv 5) = 24) by (vm_compute; reflexivity);
    unfold acallee_saved; rewrite HX; lia)). exact Q24. }
assert (Q2_27 : getr regs2 27 = w64 s).
{ rewrite (P2 (27%bv : bv 5) ltac:(assert (HX : bv_unsigned (27%bv : bv 5) = 27) by (vm_compute; reflexivity);
    unfold acallee_saved; rewrite HX; lia)). exact Q27. }
(* the width byte of `a`, which the call kept *)
assert (HA1b : aview SEGS (w_H W2) mem2 (gF cx fp + (GO_A + 1)) = Some (sw_in (c_pl cx)))
  by (exact (gs_keep_fb cx fp t W3 W2 (ms_mem ms3) mem2 (GO_A + 1) _ KEEP3
               ltac:(rewrite Hfb; unfold GO_A; lia) HA1)).
(* ---- the memory of the next cuts, from what the call kept and the runs left ---- *)
assert (HKC : forall msF : machine_state, gse_kept (c_sp1 cx + 88) mem2 (ms_mem msF) ->
  forall x, gs_keep_at cx fp t x /\ 0 <= x < 2 ^ 64 /\ ~ (c_sp1 cx + 88 <= x < c_sp1 cx + 88 + 8) ->
  aview SEGS (w_H W2) (ms_mem msF) x = aview SEGS (w_H W3) (ms_mem ms3) x).
{ intros msF OUT x (Hk1 & Hk2 & Hk3).
  rewrite (gse_kept_aview (w_H W2) mem2 (ms_mem msF) _ OUT x Hk2 Hk3). exact (KEEP3 x Hk1). }
assert (BLK : forall msF : machine_state, gse_kept (c_sp1 cx + 88) mem2 (ms_mem msF) ->
  gsw_blk B cx fp ly2 S2 W2 msF t s).
{ intros msF OUT. pose proof (HKC msF OUT) as HK.
  assert (SLK : forall off v, 0 <= off -> off + 8 <= 88 \/ 96 <= off -> off + 8 <= 192 ->
    gslot cx W3 ms3 off v -> gslot cx W2 msF off v).
  { intros off v H0 H1 H2 Hv. unfold gslot in *.
    apply (gs_word_out W3 W2 (ms_mem ms3) (ms_mem msF) _ (c_sp1 cx + off) v HK); [|exact Hv].
    intros i Hi. gse_pk. }
  unfold gsw_blk.
  split; [rewrite Eab2; exact Eab|].
  split; [rewrite Eab2; exact Hsin|].
  split.
  { destruct HTAB as (_ & Ht0' & Hlen & Hbytes).
    split; [rewrite Eab2; exact HtIn|]. split; [exact Ht0'|]. split; [exact Hlen|].
    intros i Hi H1 H2 H3. rewrite (HK (t + i) ltac:(gse_pk)). exact (Hbytes i Hi H1 H2 H3). }
  split.
  { unfold gfarr in *. apply (gs_garr_out W3 W2 (ms_mem ms3) (ms_mem msF) _ _ _ HK); [|exact HWAS].
    intros j Hj. rewrite HwsL in Hj. unfold GO_WAS. gse_pk. }
  split.
  { unfold gfarr in *. apply (gs_garr_out W3 W2 (ms_mem ms3) (ms_mem msF) _ _ _ HK); [|exact HSET].
    intros j Hj. rewrite HstL in Hj. unfold GO_SET. gse_pk. }
  split; [exact HREL|]. split; [exact HI1|].
  split.
  { unfold gsw_slots.
    split; [apply (SLK 8); first [lia | assumption]|].
    split; [apply (SLK 16); first [lia | assumption]|].
    split; [apply (SLK 40); first [lia | assumption]|].
    split; [apply (SLK 48); first [lia | assumption]|].
    split; [apply (SLK 56); first [lia | assumption]|].
    split; [apply (SLK 64); first [lia | assumption]|].
    split; [apply (SLK 72); first [lia | assumption]|].
    split; [apply (SLK 80); first [lia | assumption]|].
    split; [apply (SLK 96); first [lia | assumption]|].
    split; [apply (SLK 104); first [lia | assumption]|].
    split; [apply (SLK 112); first [lia | assumption]|].
    split; [apply (SLK 120); first [lia | assumption]|].
    split; [apply (SLK 128); first [lia | assumption]|].
    split; [apply (SLK 136); first [lia | assumption]|].
    split; [apply (SLK 144); first [lia | assumption]|].
    apply (SLK 152); first [lia | assumption]. }
  split; [exact Hn26|]. split; [exact Ht0|]. split; [exact Hs0|].
  split; [exact Hok|].
  split.
  - unfold gfb in *. rewrite (HK (gF cx fp + GO_A) ltac:(unfold GO_A; gse_pk)). exact HA0.
  - unfold gfb in *. rewrite (HK (gF cx fp + (GO_A + 1)) ltac:(unfold GO_A; gse_pk)). exact HA1. }
assert (BODY : forall (msF : machine_state) (pc' : Z), gse_kept (c_sp1 cx + 88) mem2 (ms_mem msF) ->
  ms_pc_val msF = w64 (BASE + pc') -> ms_resv msF = None -> ms_svc_pending msF = None ->
  ms_rom msF = seg_rom SEGS -> ms_fregs msF = fp_regs -> ms_fcsr msF = fp_csr -> gregs cx msF ->
  ge_body cx fp pc' W2 msF GSH_a).
{ intros msF pc' OUT Hpcv Hrv Hsv Hrom' Hfr' Hfc' HR'.
  apply (gs_body_out cx fp GPS_mal pc' _ W3 W2 ms3 msF GSH_a (HKC msF OUT)).
  - intros a Ha. gse_pk.
  - intros i Hi. unfold GE_NSH in Hi. cbn [Z.of_nat] in Hi. gse_pk.
  - intros i Hi. rewrite Hfb in Hi. gse_pk.
  - intros i Hi. pose proof (Hpceil ltac:(lia)) as (Hp0 & Hpc'). gse_pk.
  - exact Hpcv.
  - exact Hrv.
  - exact Hsv.
  - exact Hrom'.
  - exact Hfr'.
  - exact Hfc'.
  - exact HR'.
  - exact HBODY. }
assert (HMO2 : mo_le MT (c_S cx) S2 acc)
  by (rewrite ES2; exact (mo_le_set_fs_r MT MTF (c_S cx) S3 fset acc HMO)).
assert (HFR2 : YG01.frames S2 = [(GE_CID, fp)]) by (rewrite Hfrs2; exact HFR).
(* ---- run 2: 0x813ec -> the answer test at 0x81408 ---- *)
remember (if 8 + 3 * sw_in (c_pl cx) <=? sw_rows (c_pl cx) then 8 + 3 * sw_in (c_pl cx) else 2 ^ 64 - 1)
  as ansZ eqn:HansZ.
assert (Hans : 0 <= ansZ < 2 ^ 64)
  by (rewrite HansZ; destruct (8 + 3 * sw_in (c_pl cx) <=? sw_rows (c_pl cx)); lia).
assert (U9b : bv_unsigned (ew (Eimg (Ereg regs2 (gse_extra (sw_in (c_pl cx))))) 9%nat) = c_sp1 cx).
{ rewrite (ew_Eimg_Ereg_nat regs2 _ 9%nat 9%bv eq_refl), Q2s1. apply unsigned_lit_small. lia. }
assert (U24b : bv_unsigned (ew (Eimg (Ereg regs2 (gse_extra (sw_in (c_pl cx))))) 24%nat) = gF cx fp + GO_A).
{ rewrite (ew_Eimg_Ereg_nat regs2 _ 24%nat 24%bv eq_refl), Q2_24. apply unsigned_lit_small. unfold GO_A. lia. }
assert (HEXb : ew (Eimg (Ereg regs2 (gse_extra (sw_in (c_pl cx))))) 32%nat = w64 (sw_in (c_pl cx))).
{ rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs2 (gse_extra (sw_in (c_pl cx))) 0). }
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
assert (Hrsb : Forall (YP09.region_ok SEGS (Eimg (Ereg regs2 (gse_extra (sw_in (c_pl cx)))))
                 (mrestrict (w_H W2) mem2)) gse_regions).
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - apply (gse_areg_ok W2 _ mem2 (gF cx fp + GO_A) _ U24b ltac:(unfold GO_A; lia) ltac:(unfold GO_A; lia)).
    apply Forall_cons; [|apply Forall_nil].
    apply (gse_atom_byte_chunk W2 _ mem2 (gF cx fp + GO_A) 1 32%nat (sw_in (c_pl cx)) HEXb ltac:(lia)
      ltac:(replace (gF cx fp + GO_A + 1) with (gF cx fp + (GO_A + 1)) by lia; exact HA1b)).
  - apply (gs_slotreg_ok W2 _ mem2 [] (c_sp1 cx) 88 96 U9b ltac:(lia) ltac:(lia)); [|apply Forall_nil].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres2. lia. }
assert (Hpdb : YP09.pairwise_disjoint (Eimg (Ereg regs2 (gse_extra (sw_in (c_pl cx))))) gse_regions).
{ apply pairwise_disjoint_of_extents. unfold gse_regions, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val]. rewrite U24b, U9b.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold GO_A. lia. }
pose proof (gs_seat W2 regs2 mem2 (gse_extra (sw_in (c_pl cx))) 0x9b0 gse_regions []
   ltac:(vm_compute; reflexivity) Hrsb Hpdb I) as HS2.
remember (Eimg (Ereg regs2 (gse_extra (sw_in (c_pl cx))))) as E2 eqn:HE2.
clear HS HEI EE.
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply Eimg_env).
assert (EE2 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E2 n = getr regs2 r)
  by (intros n r Hn; rewrite HE2; apply ew_Eimg_Ereg_nat; exact Hn).
clear HE2.
assert (F10 : ew E2 10 = w64 ansZ)
  by (rewrite (EE2 10%nat 10%bv eq_refl), Qa0, HansZ; reflexivity).
assert (F20 : ew E2 20 = w64 (sw_rows (c_pl cx))) by (rewrite (EE2 20%nat 20%bv eq_refl); exact Q2_20).
assert (F27 : ew E2 27 = w64 s) by (rewrite (EE2 27%nat 27%bv eq_refl); exact Q2_27).
paj_run_sh RUNP HS2 HJ2.
{ gse_awr U9b. }
pose proof (gse_kept_of_frame _ _ _ _ (c_sp1 cx + 88) HF ltac:(gse_win U9b)) as OUT.
cbn [ms_mem mkst] in OUT. clear HF HFr HG.
(* 0x81408: the answer is the value the code recomputes, so the abort block is not reached *)
psrr_branch_pi RUNP BR HS2.
{ exfalso. rewrite branch_ne_U in Hc. apply negb_true_iff, Z.eqb_neq in Hc. apply Hc.
  rewrite (U_atom E2 10 ansZ F10 Hans).
  assert (HU : U E2 gse_ansv = ansZ).
  { rewrite HansZ.
    exact (gse_ansv_U E2 (sw_in (c_pl cx)) (sw_rows (c_pl cx)) HEXb F20 ltac:(lia) ltac:(lia)). }
  unfold gse_ansv, gse_want in HU. symmetry. exact HU. }
clear Hc.
(* ---- run 3: on to `blez a0` at 0x8140c ---- *)
paj_run_sh RUNP HS2 HJ2.
{ gse_awr U9b. }
pose proof (gse_kept_trans _ _ _ _ OUT (gse_kept_of_frame _ _ _ _ (c_sp1 cx + 88) HF ltac:(gse_win U9b)))
  as OUT'.
clear OUT HF HFr HG. rename OUT' into OUT.
psrr_branch_pi RUNP BR HS2.
- (* a0 <= 0: the builder refused; on to the free at 0x81804 *)
  case_eq (8 + 3 * sw_in (c_pl cx) <=? sw_rows (c_pl cx)); intros Hcmp; rewrite Hcmp in HansZ;
    cbv iota in HansZ.
  + exfalso. rewrite KindOfLink1.bt_ge_Sg in Hc. apply negb_true_iff, Z.ltb_ge in Hc.
    rewrite (KindOfLink1.Sg_lit E2 0 ltac:(lia)) in Hc.
    rewrite (KindOfLink1.Sg_atom E2 10 ansZ F10 Hans) in Hc.
    unfold KindOfLink1.sx64 in Hc. rewrite HansZ in Hc.
    rewrite (proj2 (Z.ltb_lt (8 + 3 * sw_in (c_pl cx)) (2 ^ 63))) in Hc by lia. lia.
  + paj_run_to_sh RUNTOP HS2 HJ2 GPS_free1.
    { gse_awr U9b. }
    pose proof (gse_kept_trans _ _ _ _ OUT (gse_kept_of_frame _ _ _ _ (c_sp1 cx + 88) HF ltac:(gse_win U9b)))
      as OUT'.
    clear OUT HF HFr HG. rename OUT' into OUT.
    lazymatch goal with |- SRr _ _ (mkCfg ?m _) _ => rename m into msF end.
    assert (G2 : getr (ms_regs msF) 2 = w64 (c_sp1 cx))
      by (prreg HS2 (2%bv : bv 5) RR; rewrite RR, (EE2 2%nat 2%bv eq_refl); exact Q2sp).
    assert (G3 : getr (ms_regs msF) 3 = getr (c_regs cx) 3)
      by (prreg HS2 (3%bv : bv 5) RR; rewrite RR, (EE2 3%nat 3%bv eq_refl); exact Q2gp).
    assert (G4 : getr (ms_regs msF) 4 = getr (c_regs cx) 4)
      by (prreg HS2 (4%bv : bv 5) RR; rewrite RR, (EE2 4%nat 4%bv eq_refl); exact Q2tp).
    assert (G8 : getr (ms_regs msF) 8 = w64 (spZ (c_regs cx)))
      by (prreg HS2 (8%bv : bv 5) RR; rewrite RR, (EE2 8%nat 8%bv eq_refl); exact Q2s0).
    assert (G9 : getr (ms_regs msF) 9 = w64 (c_sp1 cx))
      by (prreg HS2 (9%bv : bv 5) RR; rewrite RR, (EE2 9%nat 9%bv eq_refl); exact Q2s1).
    assert (G19 : getr (ms_regs msF) 19 = w64 (gSH cx fp))
      by (prreg HS2 (19%bv : bv 5) RR; rewrite RR, (EE2 19%nat 19%bv eq_refl); exact Q2_19).
    assert (G27 : getr (ms_regs msF) 27 = w64 s)
      by (prreg HS2 (27%bv : bv 5) RR; rewrite RR; exact F27).
    pose proof HS2 as (Hfrg0 & Hpcv0 & Hpend0 & Hresv0 & Hfcsr0 & Hrom0 & _).
    cbn [abs_ss setpc ss_pc restrict ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom]
      in Hfrg0, Hpcv0, Hpend0, Hresv0, Hfcsr0, Hrom0.
    apply (HFREE cx fp (k + 0) acc ly2 S2 W2 msF _ HB HJ2 HFR2 HMO2).
    exists t, s.
    split.
    { apply (BODY msF GPS_free1 OUT Hpcv0 Hresv0 Hpend0 Hrom0 Hfrg0 Hfcsr0).
      unfold gregs. split; [exact G2|]. split; [exact G8|]. split; [exact G9|].
      split; [exact G3 | exact G4]. }
    split; [lia|]. split; [lia|].
    split; [exact (BLK msF OUT)|].
    split; [exact G27 | exact G19].
- (* a0 > 0: the rows are laid down; on to the row loop at 0x81450 *)
  case_eq (8 + 3 * sw_in (c_pl cx) <=? sw_rows (c_pl cx)); intros Hcmp; rewrite Hcmp in HansZ;
    cbv iota in HansZ.
  + (* 0x81410 .. 0x8144c: the row cursor, slot 88 := ~s11, and the loop's constants *)
    paj_run_to_sh RUNTOP HS2 HJ2 GPS_rowhd.
    { gse_awr U9b. }
    pose proof (gse_kept_trans _ _ _ _ OUT (gse_kept_of_frame _ _ _ _ (c_sp1 cx + 88) HF ltac:(gse_win U9b)))
      as OUT'.
    clear OUT HF HFr HG. rename OUT' into OUT.
    lazymatch goal with |- SRr _ _ (mkCfg ?m _) _ => rename m into msF end.
    (* the slot the store at 0x81418 wrote *)
    assert (SL88n : gslot cx W2 msF 88 (2 ^ 64 - 1 - s)).
    { unfold gslot. apply (rdword_of_val_mem SEGS (w_H W2) (ms_mem msF)); [|lia].
      eapply (field_of_region E2 (mrestrict (w_H W2) (ms_mem msF)) 9%nat (c_sp1 cx) _ 0 192 88 96 88 8%N
        _ (2 ^ 64 - 1 - s) (st_ok_pi_region_nth E2 _ _ 1%nat _ HS2 eq_refl) U9b).
      - cbn [In]. left. reflexivity.
      - exact (gse_den_not E2 27 s F27 ltac:(lia)).
      - cbn [Z.of_N]. change (8 * 8) with 64. lia.
      - cbn [Z.of_N]. lia. }
    assert (G2 : getr (ms_regs msF) 2 = w64 (c_sp1 cx))
      by (prreg HS2 (2%bv : bv 5) RR; rewrite RR, (EE2 2%nat 2%bv eq_refl); exact Q2sp).
    assert (G3 : getr (ms_regs msF) 3 = getr (c_regs cx) 3)
      by (prreg HS2 (3%bv : bv 5) RR; rewrite RR, (EE2 3%nat 3%bv eq_refl); exact Q2gp).
    assert (G4 : getr (ms_regs msF) 4 = getr (c_regs cx) 4)
      by (prreg HS2 (4%bv : bv 5) RR; rewrite RR, (EE2 4%nat 4%bv eq_refl); exact Q2tp).
    assert (G8 : getr (ms_regs msF) 8 = w64 (spZ (c_regs cx)))
      by (prreg HS2 (8%bv : bv 5) RR; rewrite RR, (EE2 8%nat 8%bv eq_refl); exact Q2s0).
    assert (G9 : getr (ms_regs msF) 9 = w64 (c_sp1 cx))
      by (prreg HS2 (9%bv : bv 5) RR; rewrite RR, (EE2 9%nat 9%bv eq_refl); exact Q2s1).
    assert (G19 : getr (ms_regs msF) 19 = w64 (gSH cx fp))
      by (prreg HS2 (19%bv : bv 5) RR; rewrite RR, (EE2 19%nat 19%bv eq_refl); exact Q2_19).
    assert (G27 : getr (ms_regs msF) 27 = w64 s)
      by (prreg HS2 (27%bv : bv 5) RR; rewrite RR; exact F27).
    pose proof HS2 as (Hfrg0 & Hpcv0 & Hpend0 & Hresv0 & Hfcsr0 & Hrom0 & _).
    cbn [abs_ss setpc ss_pc restrict ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom]
      in Hfrg0, Hpcv0, Hpend0, Hresv0, Hfcsr0, Hrom0.
    assert (Esn : sw_n (c_pl cx) = 8 + 3 * sw_in (c_pl cx)) by (unfold sw_n, sw_want; rewrite Hcmp; reflexivity).
    assert (Hmb : sw_mbytes (c_pl cx) = 34 * sw_rows (c_pl cx))
      by (unfold sw_mbytes; rewrite (proj2 (Z.ltb_lt 0 _)) by (apply Z.leb_le in Hcmp; lia); reflexivity).
    apply Z.leb_le in Hcmp.
    apply (HROW cx fp (k + 0) acc ly2 S2 W2 msF _ HB HJ2 HFR2 HMO2).
    exists t, s, 0%nat.
    split.
    { apply (BODY msF GPS_rowhd OUT Hpcv0 Hresv0 Hpend0 Hrom0 Hfrg0 Hfcsr0).
      unfold gregs. split; [exact G2|]. split; [exact G8|]. split; [exact G9|].
      split; [exact G3 | exact G4]. }
    split; [lia|]. split; [lia|].
    split; [exact (BLK msF OUT)|].
    split.
    { (* the rows the builder laid down, which the runs did not touch *)
      split; [unfold sw_want; exact Hcmp|].
      unfold sw_bytes, sw_vals.
      apply (gs_garr_out W2 W2 mem2 (ms_mem msF)
        (fun x => 0 <= x < 2 ^ 64 /\ ~ (c_sp1 cx + 88 <= x < c_sp1 cx + 88 + 8))).
      - intros x (Hx1 & Hx2). exact (gse_kept_aview (w_H W2) mem2 (ms_mem msF) _ OUT x Hx1 Hx2).
      - intros j Hj.
        pose proof (gse_length_sweep (sw_base (c_pl cx)) (Z.to_nat (sw_in (c_pl cx)))
          (sweep_vals (T_end (c_pl cx)) t (sw_base (c_pl cx)) (Z.to_nat (sw_in (c_pl cx)))) ltac:(lia)) as HL.
        rewrite Z2Nat.id in HL by lia. cbv beta. lia.
      - exact (HSW2 (proj2 (Z.leb_le _ _) Hcmp)). }
    split; [exact SL88n|].
    split; [rewrite Esn; cbn [Z.of_nat]; lia|].
    split; [gse_const HS2 (13%bv : bv 5)|].
    split; [prreg HS2 (10%bv : bv 5) RR; rewrite RR, F10, Esn, HansZ; reflexivity|].
    (* `addi a4,s11,2` and `mv s5,a4`: the engine keeps both as atom 27 plus 2 *)
    split.
    { prreg HS2 (14%bv : bv 5) RR. rewrite RR, F27. unfold w64. rewrite unsigned_lit_small by lia.
      f_equal. cbn [Z.of_nat]. lia. }
    split.
    { prreg HS2 (21%bv : bv 5) RR. rewrite RR, F27. unfold w64. rewrite unsigned_lit_small by lia.
      f_equal. cbn [Z.of_nat]. lia. }
    split; [prreg HS2 (24%bv : bv 5) RR; rewrite RR, F27; f_equal; cbn [Z.of_nat]; lia|].
    split; [exact G27|]. split; [exact G19|].
    split; [gse_const HS2 (15%bv : bv 5)|].
    split; [gse_const HS2 (16%bv : bv 5)|].
    split; [gse_const HS2 (17%bv : bv 5)|].
    split; [gse_const HS2 (5%bv : bv 5)|].
    split; [gse_const HS2 (6%bv : bv 5)|].
    split; [gse_const HS2 (7%bv : bv 5)|].
    split; [gse_const HS2 (28%bv : bv 5)|].
    split; [gse_const HS2 (29%bv : bv 5)|].
    split; [gse_const HS2 (30%bv : bv 5)|].
    gse_const HS2 (31%bv : bv 5).
  + exfalso. rewrite KindOfLink1.bt_ge_Sg in Hc. apply negb_false_iff, Z.ltb_lt in Hc.
    rewrite (KindOfLink1.Sg_lit E2 0 ltac:(lia)) in Hc.
    rewrite (KindOfLink1.Sg_atom E2 10 ansZ F10 Hans) in Hc.
    unfold KindOfLink1.sx64 in Hc. rewrite HansZ in Hc.
    rewrite (proj2 (Z.ltb_ge (2 ^ 64 - 1) (2 ^ 63))) in Hc by lia. lia.
Qed.

End c.
End b.
End a.

(* The segment, with reac_grant_build_sweep's contract (GrantBContracts.v) taken as it is. *)
Lemma gsw_seg_mal : forall {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}
  {PI : PAImg grant_listing} (B : asyms) (MT : ameter_ops),
  GrantBContracts.tb_reac_grant_build_sweep_spec B -> @SEG_mal fx rc SK PI B MT.
Proof.
intros fx rc SK PI B MT TBSW RT HROW HFREE.
destruct RT as (LAWS & TL & TLF & ML & MTL & MTF & AMALLOC4 & AFREE4 & ABCMP & HIMG & HGL & RO).
eapply gse_mal; eassumption.
Qed.
