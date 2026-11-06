(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntrySweepS1b), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v. *)
(* Segment 1b of the sweep phase: 0x80e98 -> 0x80ef4 / 0x81298.

   The sweep buffer is allocated and its address is in slot 64 and in a0; this
   segment hands it to reac_grant_build_sweep (0x80ea4) with the row count, the
   address of `a` and the head-amp table, checks the answer against
   `rows >= 8 + 3 * a.width ? 8 + 3 * a.width : -1` (0x80ea8 .. 0x80ec4) and goes
   on to the row loop at 0x80ef4 when the builder laid the rows down, or to the
   free at 0x81298 when it refused (0x80ec8).

   The walk is three engine runs, all over two read-only regions: the two bytes of
   `a` in the entry function's frame on the side stack for frames (over atom 18,
   the register the code reads them through) and the spill slots 64 and 152 of the
   realigned machine frame (over atom 9). Nothing in the range writes memory, so
   every memory fact of the cut is carried by `gs_keep_*` (GrantEntrySweepS1c.v)
   across the one call. The branch at 0x80ec4 to the error path (0x81a0c,
   __asan_handle_no_return then abort), which the proof shows is not reached, is not
   taken because the answer the builder gives is the value the harness recomputes:
   `bsw_ok` is `8 + 3 * w <=? rows` here (BuildSweepModel.v:113, bsw_ok_go). *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YC5d YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal GrantSyms GrantList GrantPa GrantPaLib GrantBase GrantRo
GrantEntryDefs GrantEntrySweepDefs.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import YC1g YC1h YC45 YC85 GrantFrame GrantACja.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import HeadampTxEffective GrantEntrySeat.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import GrantEntrySweepS1c GrantBuildSweep.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require KindOfLink1.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import
HeadampModel GrantModel GrantSweepModel BuildSweepModel SweepRowCheck GrantSlotPlan.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require SlotNeeds_c SegSetModel BuildSweepLink.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

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

(* The three bytes of the head-amp table the layout does not name are padding; the
   layout names no other byte outside [0, 460). *)
Lemma gse_tx_fbyte_pad : forall i, tx_fbyte i = true ->
  0 <= i < 460 /\ i <> 438 /\ i <> 439 /\ i <> 451.
Proof.
intros i Hi. unfold tx_fbyte, lay_byte in Hi.
apply existsb_exists in Hi as ([o w] & Hin & Hb).
cbn [fst snd] in Hb. apply andb_prop in Hb as [H1 H2].
apply Z.leb_le in H1. apply Z.ltb_lt in H2.
unfold LAY_TX in Hin. apply in_app_iff in Hin as [Hin | Hin].
- apply in_map_iff in Hin as (q & Hq & Hqs). injection Hq as E1 E2. subst o w.
  apply in_seq in Hqs. cbn [Z.of_N] in H2. lia.
- cbn [In] in Hin.
  repeat (destruct Hin as [Heq | Hin];
    [ injection Heq as E1 E2; subst o w; cbn [Z.of_N] in H2; lia |]).
  destruct Hin.
Qed.

(* ---- the symbolic state of the three runs ---- *)
(* atoms: 32 the sweep buffer (slot 64), 33 the shadow offset (slot 152), 34 a.base,
   35 a.width; the registers are their own atoms 0 .. 31, so the builder's answer
   is atom 10. *)
Definition gse_regions : YP09.smem :=
  [ YP09.mkRegion (Some 18%nat) 0 2 0 0
      [YP09.mkChunk 0 (CVal 1 (SOff 34 0)); YP09.mkChunk 1 (CVal 1 (SOff 35 0))];
    YP09.mkRegion (Some 9%nat) 0 192 0 0
      [YP09.mkChunk 64 (CVal 8 (SOff 32 0)); YP09.mkChunk 152 (CVal 8 (SOff 33 0))] ].
Definition gse_extra (s ab aw : Z) : list word := [w64 s; w64 SHADOW_OFF; w64 ab; w64 aw].

(* The value the code recomputes at 0x80ea8 .. 0x80ec0 from a.width (atom 35) and the
   row count (s3, x19) and compares the builder's answer with: 8 + 3 * a.width, or all
   ones when the rows do not fit. *)
Definition gse_want : sv :=
  SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_SLL (SExt false 8 (SOff 35 0)) (SLit 1))
                             (SExt false 8 (SOff 35 0))) (SLit 8).
Definition gse_ansv : sv :=
  SAlu ALU_OR (SAlu ALU_SUB (SLit 0) (SAlu ALU_SLTU (SOff 19 0) gse_want)) gse_want.

Lemma gse_want_U : forall (E : env) aw, ew E 35 = w64 aw -> 0 <= aw < 256 ->
  U E gse_want = 8 + 3 * aw.
Proof.
intros E aw H35 Haw. unfold gse_want.
rewrite !U_SAlu. cbn [zalu_raw].
rewrite U_SExt. rewrite (U_atom E 35 aw H35 ltac:(lia)).
cbn [Z.of_N]. rewrite (Z.mod_small aw (2 ^ 8)) by lia.
rewrite (zcanon_id aw) by (unfold M64; lia).
rewrite (U_lit E 1) by lia. rewrite (U_lit E 8) by lia.
change (Z.land 1 63) with 1. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
rewrite (zcanon_id (aw * 2)) by (unfold M64; lia).
rewrite (zcanon_id (aw * 2 + aw)) by (unfold M64; lia).
rewrite (zcanon_id (aw * 2 + aw + 8)) by (unfold M64; lia). lia.
Qed.

Lemma gse_ansv_U : forall (E : env) aw rows,
  ew E 35 = w64 aw -> ew E 19 = w64 rows -> 0 <= aw < 256 -> 0 <= rows < 256 ->
  U E gse_ansv = (if 8 + 3 * aw <=? rows then 8 + 3 * aw else 2 ^ 64 - 1).
Proof.
intros E aw rows H35 H19 Haw Hrows. unfold gse_ansv.
rewrite U_SAlu. cbn [zalu_raw].
rewrite (gse_want_U E aw H35 Haw).
rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_lit E 0) by lia.
rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E 19 rows H19 ltac:(lia)).
rewrite (gse_want_U E aw H35 Haw).
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

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).

(* A byte of the view, as the engine's byte of a region. *)
Lemma gse_mbyte_of_aview : forall (H : word -> bool) (mem : word -> option byte) a v,
  aview SEGS H mem a = Some v -> mbyte SEGS (mrestrict H mem) a = Some (Z_to_bv 8 v).
Proof.
intros H mem a v Hx. unfold aview in Hx.
destruct (mbyte SEGS (mrestrict H mem) a) as [b|] eqn:Hb; [|discriminate].
cbn in Hx. injection Hx as <-. rewrite Z_to_bv_bv_unsigned. reflexivity.
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
   the register the code reads them through (x18). *)
Lemma gse_areg_ok : forall (W : world SEGS) (E : env) (mem : word -> option byte) base cs,
  bv_unsigned (ew E 18%nat) = base -> 0 <= base -> base + 2 <= 2 ^ 64 ->
  Forall (YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) base) cs ->
  YP09.region_ok SEGS E (mrestrict (w_H W) mem) (YP09.mkRegion (Some 18%nat) 0 2 0 0 cs).
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
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTF : ameter_fs_laws MT.
Hypothesis TBSW : treac_grant_build_sweep_spec B.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let BR := paj_branch (PI := PI).

Lemma gse_mal :
  ge_from B MT (ge_post B MT) (GIS_rowhd B MT) ->
  ge_from B MT (ge_post B MT) (GIS_free1 B MT) ->
  ge_from B MT (ge_post B MT) (GIS_mal B MT).
Proof.
intros HROW HFREE cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HGI.
destruct HGI as (t & s & HBODY & Hk & Hacc & HBLK & HOK & R10 & R19 & R18 & R22).
destruct HBLK as (Eab & Hsin & HTAB & HWAS & HSET & HREL & HI1 & SLATE & SL88 & SL120 & SL96 & SL64
  & R20 & Hn26 & Ht0 & Hs0 & HAB).
rewrite HOK in HAB. destruct HAB as (HA0 & HA1).
pose proof SLATE as (SMID & SL8 & SL32 & SL40 & SL72 & SL80 & SL104 & SL112 & SL128).
pose proof SMID as (SL16 & SL24 & SL48 & SL56 & SL136 & SL144 & SL152 & SL176).
pose proof HBODY as (Hpc & Hresv & Hsvc & Hrom & Hfrg & Hfcsr & HREGS & HSAVED & HSH & HFL & HLEN & HINP).
pose proof HREGS as (R2 & R8 & R9 & R3 & R4).
pose proof HB as (HPRE & H10 & H11 & Hpn & HPL & Hfr0 & Hev & Hlive & HROD & Hsp1d & HE0 & HE02 & HE032
  & HMOK & HTR & HNEED).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hchain & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof pa_base_lo as HBLO.
pose proof HJ as HJ0.
pose proof HJ as (HAR3 & Hly3 & _ & _ & _ & Hfrs3 & Hnev3 & Hk0 & JK1 & _).
pose proof Hly3 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
assert (FFS : GE_STK = 32768) by reflexivity.
assert (Has : ASTACK = 16384) by reflexivity.
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
  - rewrite Hz, Hemp. unfold GE_EMPTY. lia.
  - destruct (al_blocks _ _ LAWS (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) (c_p cx) (c_n cx) HAR0 Hin)
      as (_ & _ & Hce & _). pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hq]. lia. }
(* the frame on the side stack: where it is and how it is aligned *)
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 GE_CID fp HAR3 HfrIn) as (HF0 & HFc & HFia).
destruct (al_frames _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 GE_CID fp HAR3 HfrIn) as (Hf32 & _).
rewrite EFA in HF0, HFc, HFia, Hf32.
assert (Hfb : fs_frame_bytes GE_CID = 1024) by (vm_compute; reflexivity).
rewrite Hfb in HFc, HFia.
assert (HgF8 : gF cx fp mod 8 = 0).
{ apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hf32; [|lia].
  destruct Hf32 as [q Hq]. exists (4 * q). lia. }
destruct (proj1 (Z.mod_divide (gF cx fp) 8 ltac:(lia)) HgF8) as [q8 Hq8].
(* the block the malloc gave *)
destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 s (sw_mbytes (c_pl cx)) HAR3 Hsin)
  as (Hs16 & Hs4096 & Hsceil & Hsapp & _).
pose proof (req_size_pos (sw_mbytes (c_pl cx))) as Hrq.
(* the two bytes of `a` *)
assert (Habr : 0 <= sw_base (c_pl cx) < 256)
  by (exact (gs_byte_range (w_H W3) (ms_mem ms3) _ _ HA0)).
assert (Hawr : 0 <= sw_in (c_pl cx) < 256)
  by (exact (gs_byte_range (w_H W3) (ms_mem ms3) _ _ HA1)).
assert (Hfits : 1 <= sw_in (c_pl cx) <= 40 /\ 0 <= sw_base (c_pl cx)
                /\ sw_base (c_pl cx) + sw_in (c_pl cx) <= 48).
{ unfold sw_base, sw_in. unfold ok, fits in HOK.
  repeat rewrite andb_true_iff in HOK. rewrite !Z.leb_le in HOK. lia. }
destruct (SegSetModel.tables_end_inv (c_pl cx)) as (HTL & HwsL & HstL & _ & _).
(* ---- run 1: 0x80e98 -> the call of reac_grant_build_sweep ---- *)
assert (Ems3 : ms3 = mkst (ms_regs ms3) (Z_to_bv 64 (BASE + GPS_mal)) (ms_mem ms3) (seg_rom SEGS)).
{ clear - Hpc Hresv Hsvc Hrom Hfrg Hfcsr. destruct ms3; cbn in *; subst; reflexivity. }
assert (U9 : bv_unsigned (ew (Eimg (Ereg (ms_regs ms3)
               (gse_extra s (sw_base (c_pl cx)) (sw_in (c_pl cx))))) 9%nat) = c_sp1 cx).
{ rewrite (ew_Eimg_Ereg_nat (ms_regs ms3) _ 9%nat 9%bv eq_refl), R9.
  apply unsigned_lit_small. lia. }
assert (U18 : bv_unsigned (ew (Eimg (Ereg (ms_regs ms3)
               (gse_extra s (sw_base (c_pl cx)) (sw_in (c_pl cx))))) 18%nat) = gF cx fp + GO_A).
{ rewrite (ew_Eimg_Ereg_nat (ms_regs ms3) _ 18%nat 18%bv eq_refl), R18.
  apply unsigned_lit_small. unfold GO_A. lia. }
assert (HEX : forall j, (j < 4)%nat ->
  ew (Eimg (Ereg (ms_regs ms3) (gse_extra s (sw_base (c_pl cx)) (sw_in (c_pl cx))))) (32 + j)
  = nth j (gse_extra s (sw_base (c_pl cx)) (sw_in (c_pl cx))) (Z_to_bv 64 0)).
{ intros j Hj. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (Hrs : Forall (YP09.region_ok SEGS (Eimg (Ereg (ms_regs ms3)
                 (gse_extra s (sw_base (c_pl cx)) (sw_in (c_pl cx)))))
                 (mrestrict (w_H W3) (ms_mem ms3))) gse_regions).
{ apply Forall_cons.
  - apply (gse_areg_ok W3 _ (ms_mem ms3) (gF cx fp + GO_A) _ U18 ltac:(unfold GO_A; lia)
      ltac:(unfold GO_A; lia)).
    repeat apply Forall_cons; try apply Forall_nil.
    + apply (gse_atom_byte_chunk W3 _ (ms_mem ms3) (gF cx fp + GO_A) 0 34%nat (sw_base (c_pl cx))
        (HEX 2%nat ltac:(lia)) ltac:(lia) ltac:(rewrite Z.add_0_r; exact HA0)).
    + apply (gse_atom_byte_chunk W3 _ (ms_mem ms3) (gF cx fp + GO_A) 1 35%nat (sw_in (c_pl cx))
        (HEX 3%nat ltac:(lia)) ltac:(lia)
        ltac:(replace (gF cx fp + GO_A + 1) with (gF cx fp + (GO_A + 1)) by lia; exact HA1)).
  - apply Forall_cons; [|apply Forall_nil].
    apply (gs_slotreg_ok W3 _ (ms_mem ms3) _ (c_sp1 cx) 0 0 U9 ltac:(lia) ltac:(lia)
      ltac:(intros o Ho; lia)).
    repeat apply Forall_cons; try apply Forall_nil.
    + apply (gs_slot_chunk W3 _ (ms_mem ms3) 64 32%nat s (c_sp1 cx) (HEX 0%nat ltac:(lia)) U9 SL64).
    + apply (gs_slot_chunk W3 _ (ms_mem ms3) 152 33%nat SHADOW_OFF (c_sp1 cx)
        (HEX 1%nat ltac:(lia)) U9 SL152). }
assert (Hpd : YP09.pairwise_disjoint (Eimg (Ereg (ms_regs ms3)
                (gse_extra s (sw_base (c_pl cx)) (sw_in (c_pl cx))))) gse_regions).
{ apply pairwise_disjoint_of_extents. unfold gse_regions, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val]. rewrite U18, U9.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold GO_A. lia. }
pose proof (gs_seat W3 (ms_regs ms3) (ms_mem ms3)
   (gse_extra s (sw_base (c_pl cx)) (sw_in (c_pl cx))) GPS_mal gse_regions []
   ltac:(vm_compute; reflexivity) Hrs Hpd I) as HS.
rewrite <- Ems3 in HS.
remember (Eimg (Ereg (ms_regs ms3) (gse_extra s (sw_base (c_pl cx)) (sw_in (c_pl cx))))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms3) r)
  by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
pose proof (HEX 0%nat ltac:(lia)) as E32. pose proof (HEX 1%nat ltac:(lia)) as E33.
pose proof (HEX 2%nat ltac:(lia)) as E34. pose proof (HEX 3%nat ltac:(lia)) as E35.
cbn [gse_extra nth Nat.add] in E32, E33, E34, E35.
paj_run_shc RUNP RUNC HS HJ.
{ apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]]. }
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
assert (QA1 : getr (ms_regs ms) 11 = w64 (sw_rows (c_pl cx)))
  by (prreg HS (11%bv : bv 5) RR; rewrite RR, (EE 19%nat 19%bv eq_refl); exact R19).
assert (QA2 : getr (ms_regs ms) 12 = w64 (gF cx fp + GO_A))
  by (prreg HS (12%bv : bv 5) RR; rewrite RR, (EE 18%nat 18%bv eq_refl); exact R18).
assert (QA3 : getr (ms_regs ms) 13 = w64 t)
  by (prreg HS (13%bv : bv 5) RR; rewrite RR, (EE 20%nat 20%bv eq_refl); exact R20).
assert (Q18 : getr (ms_regs ms) 18 = w64 (gF cx fp + GO_A))
  by (prreg HS (18%bv : bv 5) RR; rewrite RR, (EE 18%nat 18%bv eq_refl); exact R18).
assert (Q19 : getr (ms_regs ms) 19 = w64 (sw_rows (c_pl cx)))
  by (prreg HS (19%bv : bv 5) RR; rewrite RR, (EE 19%nat 19%bv eq_refl); exact R19).
assert (Q20 : getr (ms_regs ms) 20 = w64 t)
  by (prreg HS (20%bv : bv 5) RR; rewrite RR, (EE 20%nat 20%bv eq_refl); exact R20).
assert (Q22 : getr (ms_regs ms) 22 = w64 (gSH cx fp))
  by (prreg HS (22%bv : bv 5) RR; rewrite RR, (EE 22%nat 22%bv eq_refl); exact R22).
assert (QRA : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + 0x7f8))
  by (prreg HS (1%bv : bv 5) RR; exact RR).
assert (HEV : EV_MAX = 11776) by reflexivity.
assert (HGEV : GE_EV = 2000) by reflexivity.
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
assert (HTBS : TBSW_STK = 6224) by (vm_compute; reflexivity).
pmkst HS. rewrite pa_sigma_reac_grant_build_sweep.
eapply SRr_bind.
{ eapply (cl_callS B LAWS W3 (ms_regs ms) (ms_mem ms) _ GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx)
    (c_W cx) (c_mem cx) (c_md cx) [(GE_CID, fp)] ly3 S3 _ k TBSW_STK _ 0
    (c_sp1 cx - spZ (c_regs cx)) (Z_to_bv 64 (BASE + 0x7f8)) (gch cx) _ HJ).
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
  - apply (ret_ok_codeptr_v 0x7f8 ltac:(lia) ltac:(reflexivity)).
  - rewrite unsigned_lit_small by lia. lia.
  - replace (spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx))) with (c_sp1 cx) by lia. exact HCH.
  - (* the callee's contract *)
    intros HPRE2.
    eapply SRr_mono.
    { apply (TBSW ly3 S3 W3 (ms_regs ms) (ms_mem ms) _ (gch cx) s (sw_rows (c_pl cx))
        (gF cx fp + GO_A) t (sw_base (c_pl cx)) (sw_in (c_pl cx)) (T_end (c_pl cx)) HPRE2).
      - rewrite HFR. cbn [length]. lia.
      - unfold spZ. rewrite QSP. unfold w64. rewrite unsigned_lit_small by lia. rewrite Etop. lia.
      - rewrite HM. exact (gse_rod _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0 HROD).
      - exact QA0.
      - exact QA1.
      - exact QA2.
      - exact QA3.
      - lia.
      - lia.
      - unfold GO_A. lia.
      - intros _. rewrite HM. split.
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
      - change TX_SIZE with 460. exact HtIn.
      - destruct HTAB as (_ & _ & HLT & _). exact HLT.
      - rewrite HM. apply (proj2 (tx_obj_bytes SEGS (mrestrict (w_H W3) (ms_mem ms3)) t (T_end (c_pl cx)))).
        intros i Hi. destruct (gse_tx_fbyte_pad i Hi) as (Hir & H438 & H439 & H451).
        destruct HTAB as (_ & _ & _ & HB460).
        rewrite <- (tb_nth (T_end (c_pl cx)) i).
        exact (gse_mbyte_of_aview (w_H W3) (ms_mem ms3) (t + i) _ (HB460 i Hir H438 H439 H451)).
      - exact (BuildSweepLink.I1_set01 _ HI1).
      - exact (BuildSweepLink.I1_legal _ HI1).
      - intros Hbs. exists s, (sw_mbytes (c_pl cx)). split; [exact Hsin|].
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
    unfold bsw_FP in Ha.
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
    TBSW_STK _ 0 HJ1); [| exact Eab2 | exact HtIn | exact HpIn | exact HFR | exact EFA | exact GEO].
  intros a Ha. unfold bsw_FP in Ha.
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
assert (Q2gp : getr regs2 3 = w64 (as_gp B)).
{ rewrite (P2 (3%bv : bv 5) ltac:(assert (HX : bv_unsigned (3%bv : bv 5) = 3) by (vm_compute; reflexivity);
    unfold acallee_saved; rewrite HX; lia)). exact QGP. }
assert (Q2tp : getr regs2 4 = w64 (as_tp B)).
{ rewrite (P2 (4%bv : bv 5) ltac:(assert (HX : bv_unsigned (4%bv : bv 5) = 4) by (vm_compute; reflexivity);
    unfold acallee_saved; rewrite HX; lia)). exact QTP. }
assert (Q2s0 : getr regs2 8 = w64 (spZ (c_regs cx))).
{ rewrite (P2 (8%bv : bv 5) ltac:(assert (HX : bv_unsigned (8%bv : bv 5) = 8) by (vm_compute; reflexivity);
    unfold acallee_saved; rewrite HX; lia)). exact QS0. }
assert (Q2s1 : getr regs2 9 = w64 (c_sp1 cx)).
{ rewrite (P2 (9%bv : bv 5) ltac:(assert (HX : bv_unsigned (9%bv : bv 5) = 9) by (vm_compute; reflexivity);
    unfold acallee_saved; rewrite HX; lia)). exact QS1. }
assert (Q2gp' : getr regs2 3 = getr (c_regs cx) 3) by (rewrite Q2gp; symmetry; exact Hgp).
assert (Q2tp' : getr regs2 4 = getr (c_regs cx) 4) by (rewrite Q2tp; symmetry; exact Htp).
assert (Q2_18 : getr regs2 18 = w64 (gF cx fp + GO_A)).
{ rewrite (P2 (18%bv : bv 5) ltac:(assert (HX : bv_unsigned (18%bv : bv 5) = 18) by (vm_compute; reflexivity);
    unfold acallee_saved; rewrite HX; lia)). exact Q18. }
assert (Q2_19 : getr regs2 19 = w64 (sw_rows (c_pl cx))).
{ rewrite (P2 (19%bv : bv 5) ltac:(assert (HX : bv_unsigned (19%bv : bv 5) = 19) by (vm_compute; reflexivity);
    unfold acallee_saved; rewrite HX; lia)). exact Q19. }
assert (Q2_20 : getr regs2 20 = w64 t).
{ rewrite (P2 (20%bv : bv 5) ltac:(assert (HX : bv_unsigned (20%bv : bv 5) = 20) by (vm_compute; reflexivity);
    unfold acallee_saved; rewrite HX; lia)). exact Q20. }
assert (Q2_22 : getr regs2 22 = w64 (gSH cx fp)).
{ rewrite (P2 (22%bv : bv 5) ltac:(assert (HX : bv_unsigned (22%bv : bv 5) = 22) by (vm_compute; reflexivity);
    unfold acallee_saved; rewrite HX; lia)). exact Q22. }
(* ---- the memory of the next cut, from what the call kept ---- *)
assert (SL64b : rdword (aview SEGS (w_H W2) mem2) (c_sp1 cx + 64) = Some s)
  by (eapply gs_keep_word; [exact KEEP3 | intros i Hi; left; unfold gs_keep_at; lia | exact SL64]).
assert (SL152b : rdword (aview SEGS (w_H W2) mem2) (c_sp1 cx + 152) = Some SHADOW_OFF)
  by (eapply gs_keep_word; [exact KEEP3 | intros i Hi; left; unfold gs_keep_at; lia | exact SL152]).
assert (HA0b : aview SEGS (w_H W2) mem2 (gF cx fp + GO_A) = Some (sw_base (c_pl cx)))
  by (exact (gs_keep_fb cx fp t W3 W2 (ms_mem ms3) mem2 GO_A _ KEEP3
               ltac:(rewrite Hfb; unfold GO_A; lia) HA0)).
assert (HA1b : aview SEGS (w_H W2) mem2 (gF cx fp + (GO_A + 1)) = Some (sw_in (c_pl cx)))
  by (exact (gs_keep_fb cx fp t W3 W2 (ms_mem ms3) mem2 (GO_A + 1) _ KEEP3
               ltac:(rewrite Hfb; unfold GO_A; lia) HA1)).
assert (BLK : forall msF : machine_state, ms_mem msF = mem2 -> getr (ms_regs msF) 20 = w64 t ->
  gsw_blk B cx fp ly2 S2 W2 msF t s).
{ intros msF EmF G20.
  assert (KEEPF : gs_keepW cx fp t W3 W2 (ms_mem ms3) (ms_mem msF)) by (rewrite EmF; exact KEEP3).
  unfold gsw_blk.
  split; [rewrite Eab2; exact Eab|].
  split; [rewrite Eab2; exact Hsin|].
  split.
  { destruct (gs_keep_gtab B cx fp ly3 S3 W3 W2 ms3 msF t (T_end (c_pl cx)) KEEPF HTAB)
      as (_ & Ht0' & Hlen' & Hbytes').
    split; [rewrite Eab2; exact HtIn|]. split; [exact Ht0'|]. split; [exact Hlen' | exact Hbytes']. }
  split.
  { apply (gs_keep_gfarr cx fp t W3 W2 ms3 msF GO_WAS (ws_end (c_pl cx)) KEEPF ltac:(unfold GO_WAS; lia)
      ltac:(rewrite HwsL, Hfb; unfold GO_WAS; lia) HWAS). }
  split.
  { apply (gs_keep_gfarr cx fp t W3 W2 ms3 msF GO_SET (st_end (c_pl cx)) KEEPF ltac:(unfold GO_SET; lia)
      ltac:(rewrite HstL, Hfb; unfold GO_SET; lia) HSET). }
  split; [exact HREL|]. split; [exact HI1|].
  split; [exact (gs_keep_gslots_late cx fp t W3 W2 ms3 msF KEEPF ltac:(lia) SLATE)|].
  split; [exact (gs_keep_gslot cx fp t W3 W2 ms3 msF 88 _ KEEPF ltac:(lia) ltac:(lia) SL88)|].
  split; [exact (gs_keep_gslot cx fp t W3 W2 ms3 msF 120 _ KEEPF ltac:(lia) ltac:(lia) SL120)|].
  split; [exact (gs_keep_gslot cx fp t W3 W2 ms3 msF 96 _ KEEPF ltac:(lia) ltac:(lia) SL96)|].
  split; [exact (gs_keep_gslot cx fp t W3 W2 ms3 msF 64 _ KEEPF ltac:(lia) ltac:(lia) SL64)|].
  split; [exact G20|]. split; [exact Hn26|]. split; [exact Ht0|]. split; [exact Hs0|].
  rewrite HOK. split.
  - exact (gs_keep_fb cx fp t W3 W2 (ms_mem ms3) (ms_mem msF) GO_A _ KEEPF
      ltac:(rewrite Hfb; unfold GO_A; lia) HA0).
  - exact (gs_keep_fb cx fp t W3 W2 (ms_mem ms3) (ms_mem msF) (GO_A + 1) _ KEEPF
      ltac:(rewrite Hfb; unfold GO_A; lia) HA1). }
assert (BODY : forall (msF : machine_state) (pc' : Z), ms_mem msF = mem2 ->
  ms_pc_val msF = w64 (BASE + pc') -> ms_resv msF = None -> ms_svc_pending msF = None ->
  ms_rom msF = seg_rom SEGS -> ms_fregs msF = fp_regs -> ms_fcsr msF = fp_csr -> gregs cx msF ->
  ge_body cx fp pc' W2 msF GSH_a).
{ intros msF pc' EmF Hpcv Hrv Hsv Hrom' Hfr' Hfc' HR'.
  exact (gs_keep_body cx fp t GPS_mal pc' W3 W2 ms3 msF GSH_a ltac:(rewrite EmF; exact KEEP3)
    ltac:(lia) ltac:(lia) ltac:(lia) Hpn64 Hpcv Hrv Hsv Hrom' Hfr' Hfc' HR' HBODY). }
assert (HMO2 : mo_le MT (c_S cx) S2 acc)
  by (rewrite ES2; exact (mo_le_set_fs_r MT MTF (c_S cx) S3 fset acc HMO)).
assert (HFR2 : YG01.frames S2 = [(GE_CID, fp)]) by (rewrite Hfrs2; exact HFR).
(* ---- run 2: 0x80ea8 -> the answer test at 0x80ec4 ---- *)
remember (if 8 + 3 * sw_in (c_pl cx) <=? sw_rows (c_pl cx) then 8 + 3 * sw_in (c_pl cx) else 2 ^ 64 - 1)
  as ansZ eqn:HansZ.
assert (Hans : 0 <= ansZ < 2 ^ 64)
  by (rewrite HansZ; destruct (8 + 3 * sw_in (c_pl cx) <=? sw_rows (c_pl cx)); lia).
assert (U9b : bv_unsigned (ew (Eimg (Ereg regs2 (gse_extra s (sw_base (c_pl cx)) (sw_in (c_pl cx)))))
                9%nat) = c_sp1 cx).
{ rewrite (ew_Eimg_Ereg_nat regs2 _ 9%nat 9%bv eq_refl), Q2s1. apply unsigned_lit_small. lia. }
assert (U18b : bv_unsigned (ew (Eimg (Ereg regs2 (gse_extra s (sw_base (c_pl cx)) (sw_in (c_pl cx)))))
                18%nat) = gF cx fp + GO_A).
{ rewrite (ew_Eimg_Ereg_nat regs2 _ 18%nat 18%bv eq_refl), Q2_18. apply unsigned_lit_small. unfold GO_A. lia. }
assert (HEXb : forall j, (j < 4)%nat ->
  ew (Eimg (Ereg regs2 (gse_extra s (sw_base (c_pl cx)) (sw_in (c_pl cx))))) (32 + j)
  = nth j (gse_extra s (sw_base (c_pl cx)) (sw_in (c_pl cx))) (Z_to_bv 64 0)).
{ intros j Hj. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (Hrsb : Forall (YP09.region_ok SEGS (Eimg (Ereg regs2
                 (gse_extra s (sw_base (c_pl cx)) (sw_in (c_pl cx))))) (mrestrict (w_H W2) mem2))
                 gse_regions).
{ apply Forall_cons.
  - apply (gse_areg_ok W2 _ mem2 (gF cx fp + GO_A) _ U18b ltac:(unfold GO_A; lia)
      ltac:(unfold GO_A; lia)).
    repeat apply Forall_cons; try apply Forall_nil.
    + apply (gse_atom_byte_chunk W2 _ mem2 (gF cx fp + GO_A) 0 34%nat (sw_base (c_pl cx))
        (HEXb 2%nat ltac:(lia)) ltac:(lia) ltac:(rewrite Z.add_0_r; exact HA0b)).
    + apply (gse_atom_byte_chunk W2 _ mem2 (gF cx fp + GO_A) 1 35%nat (sw_in (c_pl cx))
        (HEXb 3%nat ltac:(lia)) ltac:(lia)
        ltac:(replace (gF cx fp + GO_A + 1) with (gF cx fp + (GO_A + 1)) by lia; exact HA1b)).
  - apply Forall_cons; [|apply Forall_nil].
    apply (gs_slotreg_ok W2 _ mem2 _ (c_sp1 cx) 0 0 U9b ltac:(lia) ltac:(lia) ltac:(intros o Ho; lia)).
    repeat apply Forall_cons; try apply Forall_nil.
    + apply (gs_slot_chunk W2 _ mem2 64 32%nat s (c_sp1 cx) (HEXb 0%nat ltac:(lia)) U9b SL64b).
    + apply (gs_slot_chunk W2 _ mem2 152 33%nat SHADOW_OFF (c_sp1 cx) (HEXb 1%nat ltac:(lia)) U9b SL152b). }
assert (Hpdb : YP09.pairwise_disjoint (Eimg (Ereg regs2
                 (gse_extra s (sw_base (c_pl cx)) (sw_in (c_pl cx))))) gse_regions).
{ apply pairwise_disjoint_of_extents. unfold gse_regions, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val]. rewrite U18b, U9b.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold GO_A. lia. }
pose proof (gs_seat W2 regs2 mem2 (gse_extra s (sw_base (c_pl cx)) (sw_in (c_pl cx))) 0x7f8
   gse_regions [] ltac:(vm_compute; reflexivity) Hrsb Hpdb I) as HS2.
remember (Eimg (Ereg regs2 (gse_extra s (sw_base (c_pl cx)) (sw_in (c_pl cx))))) as E2 eqn:HE2.
clear HS HEI EE E32 E33 E34 E35 HE.
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply Eimg_env).
assert (EE2 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E2 n = getr regs2 r)
  by (intros n r Hn; rewrite HE2; apply ew_Eimg_Ereg_nat; exact Hn).
pose proof (HEXb 0%nat ltac:(lia)) as F32. pose proof (HEXb 1%nat ltac:(lia)) as F33.
pose proof (HEXb 2%nat ltac:(lia)) as F34. pose proof (HEXb 3%nat ltac:(lia)) as F35.
cbn [gse_extra nth Nat.add] in F32, F33, F34, F35.
assert (F10 : ew E2 10 = w64 ansZ)
  by (rewrite (EE2 10%nat 10%bv eq_refl), Qa0, HansZ; reflexivity).
assert (F19 : ew E2 19 = w64 (sw_rows (c_pl cx))) by (rewrite (EE2 19%nat 19%bv eq_refl); exact Q2_19).
paj_run_sh RUNP HS2 HJ2.
{ apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]]. }
lazymatch goal with HFx : frame_of _ ?rs ?m (ms_mem ?msn) |- _ =>
  pose proof (frame_of_read_only _ rs m (ms_mem msn) ltac:(vm_compute; reflexivity) HFx) as HM2 end.
clear HF HFr HG. cbn [ms_mem mkst] in HM2.
(* 0x80ec4: the answer is the value the code recomputes, so the error path is not reached *)
psrr_branch_pi RUNP BR HS2.
{ exfalso. rewrite branch_ne_U in Hc. apply negb_true_iff, Z.eqb_neq in Hc. apply Hc.
  rewrite (U_atom E2 10 ansZ F10 Hans).
  assert (HU : U E2 gse_ansv = ansZ).
  { rewrite HansZ.
    exact (gse_ansv_U E2 (sw_in (c_pl cx)) (sw_rows (c_pl cx)) F35 F19 ltac:(lia) ltac:(lia)). }
  unfold gse_ansv, gse_want in HU. symmetry. exact HU. }
clear Hc.
(* ---- run 3: on to `blez a0` at 0x80ec8 ---- *)
paj_run_sh RUNP HS2 HJ2.
{ apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]]. }
lazymatch goal with HFx : frame_of _ ?rs ?m (ms_mem ?msn) |- _ =>
  pose proof (frame_of_read_only _ rs m (ms_mem msn) ltac:(vm_compute; reflexivity) HFx) as HM3 end.
clear HF HFr HG. cbn [ms_mem mkst] in HM3.
psrr_branch_pi RUNP BR HS2.
- (* a0 <= 0: the builder refused; on to the free at 0x81298 *)
  case_eq (8 + 3 * sw_in (c_pl cx) <=? sw_rows (c_pl cx)); intros Hcmp; rewrite Hcmp in HansZ;
    cbv iota in HansZ.
  + exfalso. rewrite KindOfLink1.bt_ge_Sg in Hc. apply negb_true_iff, Z.ltb_ge in Hc.
    rewrite (KindOfLink1.Sg_lit E2 0 ltac:(lia)) in Hc.
    rewrite (KindOfLink1.Sg_atom E2 10 ansZ F10 Hans) in Hc.
    unfold KindOfLink1.sx64 in Hc. rewrite HansZ in Hc.
    rewrite (proj2 (Z.ltb_lt (8 + 3 * sw_in (c_pl cx)) (2 ^ 63))) in Hc by lia. lia.
  + paj_run_to_sh RUNTOP HS2 HJ2 GPS_free1.
    { apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]]. }
    lazymatch goal with HFx : frame_of _ ?rs ?m (ms_mem ?msn) |- _ =>
      pose proof (frame_of_read_only _ rs m (ms_mem msn) ltac:(vm_compute; reflexivity) HFx) as HM4 end.
    clear HF HFr HG. cbn [ms_mem mkst] in HM4.
    lazymatch goal with |- SRr _ _ (mkCfg ?m _) _ => rename m into msF end.
    assert (EmF : ms_mem msF = mem2) by congruence.
    assert (G2 : getr (ms_regs msF) 2 = w64 (c_sp1 cx))
      by (prreg HS2 (2%bv : bv 5) RR; rewrite RR, (EE2 2%nat 2%bv eq_refl); exact Q2sp).
    assert (G3 : getr (ms_regs msF) 3 = getr (c_regs cx) 3)
      by (prreg HS2 (3%bv : bv 5) RR; rewrite RR, (EE2 3%nat 3%bv eq_refl); exact Q2gp').
    assert (G4 : getr (ms_regs msF) 4 = getr (c_regs cx) 4)
      by (prreg HS2 (4%bv : bv 5) RR; rewrite RR, (EE2 4%nat 4%bv eq_refl); exact Q2tp').
    assert (G8 : getr (ms_regs msF) 8 = w64 (spZ (c_regs cx)))
      by (prreg HS2 (8%bv : bv 5) RR; rewrite RR, (EE2 8%nat 8%bv eq_refl); exact Q2s0).
    assert (G9 : getr (ms_regs msF) 9 = w64 (c_sp1 cx))
      by (prreg HS2 (9%bv : bv 5) RR; rewrite RR, (EE2 9%nat 9%bv eq_refl); exact Q2s1).
    assert (G20 : getr (ms_regs msF) 20 = w64 t)
      by (prreg HS2 (20%bv : bv 5) RR; rewrite RR, (EE2 20%nat 20%bv eq_refl); exact Q2_20).
    assert (G22 : getr (ms_regs msF) 22 = w64 (gSH cx fp))
      by (prreg HS2 (22%bv : bv 5) RR; rewrite RR, (EE2 22%nat 22%bv eq_refl); exact Q2_22).
    pose proof HS2 as (Hfrg0 & Hpcv0 & Hpend0 & Hresv0 & Hfcsr0 & Hrom0 & _).
    cbn [abs_ss setpc ss_pc restrict ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom]
      in Hfrg0, Hpcv0, Hpend0, Hresv0, Hfcsr0, Hrom0.
    apply (HFREE cx fp (k + 0) acc ly2 S2 W2 msF _ HB HJ2 HFR2 HMO2).
    exists t, s.
    split.
    { apply (BODY msF GPS_free1 EmF Hpcv0 Hresv0 Hpend0 Hrom0 Hfrg0 Hfcsr0).
      unfold gregs. split; [exact G2|]. split; [exact G8|]. split; [exact G9|].
      split; [exact G3 | exact G4]. }
    split; [lia|]. split; [lia|].
    split; [exact (BLK msF EmF G20) | exact G22].
- (* a0 > 0: the rows are laid down; on to the row loop at 0x80ef4 *)
  case_eq (8 + 3 * sw_in (c_pl cx) <=? sw_rows (c_pl cx)); intros Hcmp; rewrite Hcmp in HansZ;
    cbv iota in HansZ.
  + paj_run_to_sh RUNTOP HS2 HJ2 GPS_rowhd.
    { apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]]. }
    lazymatch goal with HFx : frame_of _ ?rs ?m (ms_mem ?msn) |- _ =>
      pose proof (frame_of_read_only _ rs m (ms_mem msn) ltac:(vm_compute; reflexivity) HFx) as HM4 end.
    clear HF HFr HG. cbn [ms_mem mkst] in HM4.
    lazymatch goal with |- SRr _ _ (mkCfg ?m _) _ => rename m into msF end.
    assert (EmF : ms_mem msF = mem2) by congruence.
    assert (G2 : getr (ms_regs msF) 2 = w64 (c_sp1 cx))
      by (prreg HS2 (2%bv : bv 5) RR; rewrite RR, (EE2 2%nat 2%bv eq_refl); exact Q2sp).
    assert (G3 : getr (ms_regs msF) 3 = getr (c_regs cx) 3)
      by (prreg HS2 (3%bv : bv 5) RR; rewrite RR, (EE2 3%nat 3%bv eq_refl); exact Q2gp').
    assert (G4 : getr (ms_regs msF) 4 = getr (c_regs cx) 4)
      by (prreg HS2 (4%bv : bv 5) RR; rewrite RR, (EE2 4%nat 4%bv eq_refl); exact Q2tp').
    assert (G8 : getr (ms_regs msF) 8 = w64 (spZ (c_regs cx)))
      by (prreg HS2 (8%bv : bv 5) RR; rewrite RR, (EE2 8%nat 8%bv eq_refl); exact Q2s0).
    assert (G9 : getr (ms_regs msF) 9 = w64 (c_sp1 cx))
      by (prreg HS2 (9%bv : bv 5) RR; rewrite RR, (EE2 9%nat 9%bv eq_refl); exact Q2s1).
    assert (G20 : getr (ms_regs msF) 20 = w64 t)
      by (prreg HS2 (20%bv : bv 5) RR; rewrite RR, (EE2 20%nat 20%bv eq_refl); exact Q2_20).
    assert (G22 : getr (ms_regs msF) 22 = w64 (gSH cx fp))
      by (prreg HS2 (22%bv : bv 5) RR; rewrite RR, (EE2 22%nat 22%bv eq_refl); exact Q2_22).
    assert (G18 : getr (ms_regs msF) 18 = w64 (gF cx fp + GO_A))
      by (prreg HS2 (18%bv : bv 5) RR; rewrite RR, (EE2 18%nat 18%bv eq_refl); exact Q2_18).
    pose proof HS2 as (Hfrg0 & Hpcv0 & Hpend0 & Hresv0 & Hfcsr0 & Hrom0 & _).
    cbn [abs_ss setpc ss_pc restrict ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom]
      in Hfrg0, Hpcv0, Hpend0, Hresv0, Hfcsr0, Hrom0.
    assert (Esn : sw_n (c_pl cx) = 8 + 3 * sw_in (c_pl cx)) by (unfold sw_n, sw_want; rewrite Hcmp; reflexivity).
    apply (HROW cx fp (k + 0) acc ly2 S2 W2 msF _ HB HJ2 HFR2 HMO2).
    exists t, s, 0%nat.
    split.
    { apply (BODY msF GPS_rowhd EmF Hpcv0 Hresv0 Hpend0 Hrom0 Hfrg0 Hfcsr0).
      unfold gregs. split; [exact G2|]. split; [exact G8|]. split; [exact G9|].
      split; [exact G3 | exact G4]. }
    split; [lia|]. split; [lia|].
    split; [exact (BLK msF EmF G20)|].
    split.
    { split; [exact HOK|]. split; [unfold sw_want; apply Z.leb_le; exact Hcmp|].
      rewrite EmF. unfold sw_bytes, sw_vals. exact (HSW2 Hcmp). }
    split; [rewrite Esn; cbn [Z.of_nat]; lia|].
    split; [prreg HS2 (13%bv : bv 5) RR; rewrite RR; reflexivity|].
    split; [prreg HS2 (10%bv : bv 5) RR; rewrite RR, F10, Esn, HansZ; reflexivity|].
    split.
    { prreg HS2 (14%bv : bv 5) RR. rewrite RR, F32. unfold w64. rewrite unsigned_lit_small by lia.
      f_equal. cbn [Z.of_nat]. lia. }
    split.
    { prreg HS2 (7%bv : bv 5) RR. rewrite RR, F32. unfold w64. rewrite unsigned_lit_small by lia.
      f_equal. cbn [Z.of_nat]. lia. }
    split; [prreg HS2 (21%bv : bv 5) RR; rewrite RR; exact F32|].
    split; [prreg HS2 (23%bv : bv 5) RR; rewrite RR; exact F33|].
    split; [exact G22|]. split; [exact G18|].
    split; [prreg HS2 (15%bv : bv 5) RR; rewrite RR; reflexivity|].
    split; [prreg HS2 (16%bv : bv 5) RR; rewrite RR; reflexivity|].
    split; [prreg HS2 (17%bv : bv 5) RR; rewrite RR; reflexivity|].
    split; [prreg HS2 (5%bv : bv 5) RR; rewrite RR; reflexivity|].
    prreg HS2 (6%bv : bv 5) RR; rewrite RR; reflexivity.
  + exfalso. rewrite KindOfLink1.bt_ge_Sg in Hc. apply negb_false_iff, Z.ltb_lt in Hc.
    rewrite (KindOfLink1.Sg_lit E2 0 ltac:(lia)) in Hc.
    rewrite (KindOfLink1.Sg_atom E2 10 ansZ F10 Hans) in Hc.
    unfold KindOfLink1.sx64 in Hc. rewrite HansZ in Hc.
    rewrite (proj2 (Z.ltb_ge (2 ^ 64 - 1) (2 ^ 63))) in Hc by lia. lia.
Qed.

End c.
End b.
End a.

(* The segment, with reac_grant_build_sweep's stated contract (a Theorem Labs lane,
   GrantBuildSweep.v) taken as it is. *)
Lemma gsw_seg_mal : forall {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}
  {PI : PAImg grant_listing} (B : asyms) (MT : ameter_ops),
  treac_grant_build_sweep_spec B -> @SEG_mal fx rc SK PI B MT.
Proof.
intros fx rc SK PI B MT TBSW RT HROW HFREE.
destruct RT as (LAWS & TL & MTL & MTF & _).
eapply gse_mal; eassumption.
Qed.
