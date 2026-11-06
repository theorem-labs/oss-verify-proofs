(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8q.v:156-158;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACbk.v:76-79; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:200-203, 287-290,
   358-363, for libreac/fuzz_identity's ASan build (lib/A). The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8h.v:75-78, 95-98, 104-107. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_family_of.v, with its module paths and module names changed; 1114 of its 1204 lines of code are new or changed and 748 lines of the source are left out. *)
(* Segment E of LLVMFuzzerTestOneInput's ASan walk, 0x8157c..0x815f8 (31 slots): seg_E of
   lib/A/Prog/LLVMFuzzerTestOneInput_inv.v.

   0x8157c loads &id from mf+184 and calls reac_box_family_of on it (0x81580); its result r is kept in s6.
   0x81584..0x81588 load &hw from mf+48 and hw.have from it. If have = 0 the harness skips its own table walk
   (0x81590 beqz a1 -> 0x815cc). Otherwise 0x81594..0x815a8 set the inlined family_of_hw loop up (s8 = HW_TABLE,
   s4 = HW_TABLE + 4, s7 = 0, s9 = -36) and 0x815ac..0x815c8 walk the table's three rows: the bcmp of the eight
   bytes at hw.raw (SF+436) against the row's hw block, and on a mismatch s7 -= 12, s4 += 12 and the next row.
   On a match 0x815d8..0x815ec read the row's family field (through its shadow byte) and 0x815f4 checks that it
   is r; with no match and with have = 0 the run reaches 0x815cc, and 0x815d0 checks that r = 0.

   Both checks hold of the model: r = FAM id (reac_box_family_of's post at the image's HW_FAMILY) and
   FAM id = fam_hw have hw.raw (SlotModel.rec_P7), with HW_FAMILY and HW_TABLE the same 36 bytes. So the
   abort at 0x822f0 is never reached; the segment keeps every byte outside the two calls' stack windows and
   ends at 0x815f8 with a3 = SHADOW_OFF. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI08 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentSyms IdentList IdentPa IdentPaLib IdentBase IdentFrame IdentCJ IdentRo
IdentProgSig YC1g YC1h YC45 YC4b YC81 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require reac_box_family_of.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel reac_box_family_of_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* YC4b turns lia's division and modulo handling off for every file that loads it; this segment's address
   arithmetic (shadow_addr, the frame's alignment) needs it. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the image's two hardware tables ---------------------------------------------------------------------- *)
(* HW_TABLE (object 6, 0x20fe0) and HW_FAMILY (object 16, 0x210e0) hold the same 36 bytes (the contract's
   HW_ROWS): three rows of a 4-byte family number and an 8-byte hardware block
   (reac_box_family_of_c.FAMOF_HW1..3, which SlotModel.HWT names). *)
Lemma e_hwb_row : forall j i, (j < 3)%nat -> (i < 8)%nat ->
nth (4 + 12 * j + i) HW_ROWS 0 = nth i (SlotModel.HWT j) 0.
Proof.
intros j i Hj Hi. destruct j as [|[|[|j]]]; [| | | lia];
destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; try lia; reflexivity.
Qed.

Lemma e_hwt_len : forall j, (j < 3)%nat -> length (SlotModel.HWT j) = 8%nat.
Proof. intros j Hj. destruct j as [|[|[|j]]]; [reflexivity | reflexivity | reflexivity | lia]. Qed.

Lemma e_hwrows_len : length HW_ROWS = 36%nat.
Proof. reflexivity. Qed.

(* A hardware block equals a table row exactly when its eight bytes do. *)
Lemma e_rows_eq : forall (l : list byte) (r : list Z), length l = 8%nat -> length r = 8%nat ->
((forall j, (j < 8)%nat -> bv_unsigned (nth j l (Z_to_bv 8 0)) = nth j r 0) <-> map bv_unsigned l = r).
Proof.
intros l r Hl Hr.
destruct l as [|a0 [|a1 [|a2 [|a3 [|a4 [|a5 [|a6 [|a7 [|a8 l]]]]]]]]]; cbn [length] in Hl; try lia.
destruct r as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|b7 [|b8 r]]]]]]]]]; cbn [length] in Hr; try lia.
cbn [map nth]. split.
- intros H. rewrite (H 0%nat ltac:(lia)), (H 1%nat ltac:(lia)), (H 2%nat ltac:(lia)), (H 3%nat ltac:(lia)),
  (H 4%nat ltac:(lia)), (H 5%nat ltac:(lia)), (H 6%nat ltac:(lia)), (H 7%nat ltac:(lia)). reflexivity.
- intros H. injection H as <- <- <- <- <- <- <- <-.
  intros j Hj. destruct j as [|[|[|[|[|[|[|[|j]]]]]]]]; cbn [nth]; try reflexivity; lia.
Qed.

Lemma e_fam_cmp_hit : forall hw j, (j < 3)%nat -> map bv_unsigned hw = SlotModel.HWT j ->
SlotModel.fam_cmp hw = Z.of_nat j + 1.
Proof.
intros hw j Hj H. unfold SlotModel.fam_cmp. cbv zeta. rewrite H.
destruct j as [|[|[|j]]]; [| | | lia]; cbn [SlotModel.HWT nth];
repeat (destruct (list_eq_dec Z.eq_dec _ _) as [E|E]; [try reflexivity; exfalso; discriminate E |]);
first [reflexivity | exfalso; apply E; reflexivity].
Qed.

Lemma e_fam_cmp_miss : forall hw,
map bv_unsigned hw <> SlotModel.HWT 0 -> map bv_unsigned hw <> SlotModel.HWT 1 ->
map bv_unsigned hw <> SlotModel.HWT 2 -> SlotModel.fam_cmp hw = 0.
Proof.
intros hw H0 H1 H2. unfold SlotModel.fam_cmp. cbv zeta.
cbn [SlotModel.HWT nth] in H0, H1, H2.
destruct (list_eq_dec Z.eq_dec (map bv_unsigned hw) reac_box_family_of_c.FAMOF_HW1) as [E|_];
[exfalso; exact (H0 E)|].
destruct (list_eq_dec Z.eq_dec (map bv_unsigned hw) reac_box_family_of_c.FAMOF_HW2) as [E|_];
[exfalso; exact (H1 E)|].
destruct (list_eq_dec Z.eq_dec (map bv_unsigned hw) reac_box_family_of_c.FAMOF_HW3) as [E|_];
[exfalso; exact (H2 E) | reflexivity].
Qed.

Lemma e_hwb_len : forall inp i, length (SlotModel.rec_hwb inp i) = 8%nat.
Proof.
intros inp i. unfold SlotModel.rec_hwb.
assert (H : match SlotModel.rec_hw inp i with Some h => length h = 8%nat | None => True end).
{ induction i as [|i IH]; cbn [SlotModel.rec_hw]; [exact I|].
  destruct ((SlotModel.rec_addr inp i =? RcIdentModel.ADDR_REAC_VERSION) && (8 <=? SlotModel.rec_k inp i)) eqn:Hc;
  [|exact IH].
  apply andb_prop in Hc as [_ Hk]. apply Z.leb_le in Hk.
  rewrite length_firstn, SlotModel.rec_pl_length. lia. }
destruct (SlotModel.rec_hw inp i); [exact H | apply repeat_length].
Qed.

Lemma e_raw_len : forall l, length l = 38%nat -> length (RcIdentModel.raw l) = 8%nat.
Proof.
intros l Hl. unfold RcIdentModel.raw, RcIdentModel.get, RcIdentModel.REAC_VER_LEN, RcIdentModel.OFF_RAW.
rewrite length_firstn, length_skipn, Hl. reflexivity.
Qed.

Lemma e_nth_skipn : forall (l : list byte) m j d, nth j (skipn m l) d = nth (m + j) l d.
Proof.
induction l as [|x l IH]; intros [|m] j d; cbn; try reflexivity.
- destruct j; reflexivity.
- destruct m; [reflexivity | apply IH].
Qed.

Lemma e_raw_nth : forall (l : list byte) j d, (j < 8)%nat ->
nth j (RcIdentModel.raw l) d = nth (28 + j) l d.
Proof.
intros l j d Hj. unfold RcIdentModel.raw, RcIdentModel.get, RcIdentModel.REAC_VER_LEN, RcIdentModel.OFF_RAW.
rewrite (SlotModel.nth_first (skipn 28 l) 8 j d Hj). apply e_nth_skipn.
Qed.

(* ---- the symbolic state of the walk ------------------------------------------------------------------------ *)
(* Atoms: 0..31 the registers at 0x8157c; 32 SHADOW_OFF; 33 SF (the class-4 frame); 34 hw.have;
   A_OBJ 6 HW_TABLE. Regions: the three machine-frame words the segment loads, hw.have, and the table (its
   three family fields are the image's literals 1, 2, 3). All read-only. *)
Definition SB_E : Z := 0x7fff8000.
Definition Bx_E : sv := SOff 32 0.
Definition Bspan_E : Z * Z := (SB_E, SB_E + 2 ^ 44 - 1).
Definition e_mf : YP09.region :=
YP09.mkRegion (Some 9%nat) 48 192 48 48
[YP09.mkChunk 48 (CVal 8 (SOff 33 432)); YP09.mkChunk 176 (CVal 8 (SOff 32 0));
YP09.mkChunk 184 (CVal 8 (SOff 33 352))].
Definition e_hw : YP09.region := YP09.mkRegion (Some 33%nat) 432 436 432 432 [YP09.mkChunk 432 (CVal 4 (SOff 34 0))].
Definition e_tbl : YP09.region :=
YP09.mkRegion (Some (A_OBJ 6)) 0 36 0 0
[YP09.mkChunk 0 (CVal 4 (SLit 1)); YP09.mkChunk 12 (CVal 4 (SLit 2)); YP09.mkChunk 24 (CVal 4 (SLit 3))].
Definition e_atoms : list (nat * afact) :=
[(2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (32%nat, mkAF SB_E SB_E 0);
(33%nat, mkAF 4096 (2 ^ 47) 6); (34%nat, mkAF 0 1 0); (A_OBJ 6, mkAF IMG_LO IMG_TOP 0)].
Definition ss_E0 : sstate := mkSS 0xe70 sr_atoms [e_mf; e_hw; e_tbl] None (mkFacts e_atoms [] []).
Definition e_SHT : list shent := [mkSHE (A_OBJ 6) 0 36].

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
(* The Section of LLVMFuzzerTestOneInput.v / _inv.v, in the same order. *)
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.

(* ---- what the segment takes -------------------------------------------------------------------------------- *)
Hypothesis HSTK : STK_LLVMF <= LLVMF_STK.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis PSIG : ident_prog_sig_ok (PI := PI).
(* the read-only image of the contract, in the callees' shape (LLVMFuzzerTestOneInput.v:154) *)
Hypothesis HRO : forall rdr, arodata_okS SEGS B RLO RHI rdr -> arodata_okP SEGS pa_relro_lo pa_relro_hi B rdr.
(* the registered globals (LLVMFuzzerTestOneInput.v:156-162): HW_TABLE is one of them *)
Variable G : list (Z * Z).
Hypothesis GM : globs_marked SEGS B G.
Hypothesis IV : img_shadow_vis SEGS B.
Hypothesis G_HW : In (VAL (A_OBJ 6), 36) G.
(* the bcmp interceptor (CONVENTIONS section 4) *)
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA IS___interceptor_trampoline_bcmp).
(* cgif ACfh.v:162-164 *)
Hypothesis AJ_NIL_IO : forall STK sp0 ly S (W : world SEGS) mem md own ly' S' W' mem' md' k,
ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
m_fds md' = m_fds md /\ m_fs md' = m_fs md.
(* the program callee: reac_box_family_of (proved on the integration branch) *)
Hypothesis HFAM : reac_box_family_of.treac_box_family_of_spec B.
(* The image constants (contract, LLVMFuzzerTestOneInput.v:257-261): this segment uses HW_TABLE's 36 bytes
   and its room inside the image's read range (IdentRo.ro_hull needs that slack for the bcmp at 0x815b8). *)
Hypothesis HIMG : forall (W : world SEGS) mem,
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) -> llvmf_img B G W mem.

Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* ---- small memory facts ------------------------------------------------------------------------------------ *)
Lemma e_vm1 : forall (W : world SEGS) mem a v, aview SEGS (w_H W) mem a = Some v -> val_mem SEGS (rd W mem) a 1 v.
Proof.
intros W mem a v Hv k Hk. assert (k = 0%nat) by lia. subst k. rewrite Z.add_0_r.
unfold aview in Hv. destruct (mbyte SEGS (rd W mem) a) as [b|] eqn:Eb; [|discriminate].
cbn [option_map] in Hv. injection Hv as <-. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned. unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. pose proof (bv_unsigned_in_range 8 b) as Hr. unfold bv_wrap.
change (bv_modulus 8) with 256 in *. change (2 ^ 8) with 256.
repeat rewrite (Z.mod_small (bv_unsigned b) 256) by lia. reflexivity.
Qed.

Lemma e_vm4 : forall (W : world SEGS) mem a v, 0 <= v < 256 ->
aview SEGS (w_H W) mem a = Some v ->
aview SEGS (w_H W) mem (a + 1) = Some 0 -> aview SEGS (w_H W) mem (a + 2) = Some 0 ->
aview SEGS (w_H W) mem (a + 3) = Some 0 ->
val_mem SEGS (rd W mem) a 4 v.
Proof.
intros W mem a v Hv H0 H1 H2 H3 k Hk.
assert (Hb : forall x w, aview SEGS (w_H W) mem x = Some w -> mbyte SEGS (rd W mem) x = Some (Z_to_bv 8 w)).
{ intros x w Hx. unfold aview in Hx. destruct (mbyte SEGS (rd W mem) x) as [b|] eqn:Eb; [|discriminate].
  cbn [option_map] in Hx. injection Hx as <-. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned.
  pose proof (bv_unsigned_in_range 8 b) as Hr. unfold bv_wrap. change (bv_modulus 8) with 256 in *.
  symmetry; apply Z.mod_small; lia. }
assert (L : forall j, (j < 4)%nat -> YO0f.le_byte v 4 j = (if Nat.eqb j 0 then v else 0)).
{ intros j Hj. unfold YO0f.le_byte. change (8 * Z.of_nat 4) with 32.
  rewrite (Z.mod_small v (2 ^ 32)) by lia.
  destruct j as [|[|[|[|j]]]]; try lia; cbn [Nat.eqb].
  - change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. apply Z.mod_small. lia.
  - change (8 * Z.of_nat 1) with 8. rewrite Z.shiftr_div_pow2 by lia.
    rewrite (Z.div_small v (2 ^ 8)) by lia. reflexivity.
  - change (8 * Z.of_nat 2) with 16. rewrite Z.shiftr_div_pow2 by lia.
    rewrite (Z.div_small v (2 ^ 16)) by lia. reflexivity.
  - change (8 * Z.of_nat 3) with 24. rewrite Z.shiftr_div_pow2 by lia.
    rewrite (Z.div_small v (2 ^ 24)) by lia. reflexivity. }
destruct k as [|[|[|[|k]]]]; try lia.
- rewrite (L 0%nat ltac:(lia)). cbn [Nat.eqb]. rewrite Z.add_0_r. exact (Hb a v H0).
- rewrite (L 1%nat ltac:(lia)). cbn [Nat.eqb].
  replace (a + Z.of_nat 1) with (a + 1) by lia. exact (Hb (a + 1) 0 H1).
- rewrite (L 2%nat ltac:(lia)). cbn [Nat.eqb].
  replace (a + Z.of_nat 2) with (a + 2) by lia. exact (Hb (a + 2) 0 H2).
- rewrite (L 3%nat ltac:(lia)). cbn [Nat.eqb].
  replace (a + Z.of_nat 3) with (a + 3) by lia. exact (Hb (a + 3) 0 H3).
Qed.

(* a byte of an array, as the reader sees it *)
Lemma e_aview_garr8 : forall (W : world SEGS) mem a l i,
garr8 SEGS (rd W mem) a l -> 0 <= i < Z.of_nat (length l) ->
aview SEGS (w_H W) mem (a + i) = Some (nth (Z.to_nat i) l 0).
Proof.
intros W mem a l i Hg Hi.
assert (Hj : (Z.to_nat i < length l)%nat) by lia.
pose proof (garr8_mbyte SEGS (rd W mem) a l (Z.to_nat i) Hg Hj) as Hm.
rewrite Z2Nat.id in Hm by lia.
unfold aview. rewrite Hm. cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
apply Z.mod_small. exact (proj2 (Hg (Z.to_nat i) Hj)).
Qed.

(* ---- the symbolic state at 0x8157c -------------------------------------------------------------------------- *)
Definition EE (regs : bvmap 5 word) (F hv : Z) : env := Eimg (Ereg regs (map (Z_to_bv 64) [SB_E; F; hv])).

Lemma e_frame_addr_le : forall n ly ly' cid pos, layout_le n ly ly' -> frame_addr ly' cid pos = frame_addr ly cid pos.
Proof.
intros n ly ly' cid pos H. unfold frame_addr. destruct H as (_ & _ & _ & _ & _ & HF & _). rewrite HF. reflexivity.
Qed.

Lemma e_start : forall g pos mf ly2 S2 (W2 : world SEGS) regs2 mem2 md2 k,
ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
ly2 S2 W2 mem2 md2 k ->
frames S2 = [(4, pos)] ->
getr regs2 2 = w64 mf -> getr regs2 9 = w64 mf ->
e_sp0 g - 336 <= mf <= e_sp0 g - 320 -> mf mod 32 = 0 ->
STK_LLVMF <= LLVMF_STK ->
val_mem SEGS (rd W2 mem2) (mf + 48) 8 (SFa g pos + V_hw) ->
val_mem SEGS (rd W2 mem2) (mf + 176) 8 SHADOW_OFF ->
val_mem SEGS (rd W2 mem2) (mf + 184) 8 (SFa g pos + V_id) ->
val_mem SEGS (rd W2 mem2) (SFa g pos + V_hw) 4 (m_have g (m_nrec g)) ->
0 <= m_have g (m_nrec g) <= 1 ->
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W2) mem2) ->
st_ok_pi SEGS VAL (EE regs2 (SFa g pos) (m_have g (m_nrec g))) ss_E0
(restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0xe70)) mem2 (seg_rom SEGS))).
Proof.
intros g pos mf ly2 S2 W2 regs2 mem2 md2 k HJ HFR R2 R9 HMF HMF32 HSTK' M48 M176 M184 MHW Hhv HROD.
set (F := SFa g pos) in *. set (hv := m_have g (m_nrec g)) in *.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstatic & _).
pose proof Hstatic as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
unfold STK_LLVMF, ESTACK, ASTACK in HSTK'.
assert (Hfin : In (4, pos) (frames S2)) by (rewrite HFR; left; reflexivity).
pose proof (e_frame_addr_le _ _ _ 4 pos Hly) as HFeq. fold (SFa g pos) F in HFeq.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 4 pos HAR Hfin) as (HF4096 & HFceil & _).
destruct (frame_al64 SEGS B ly2 S2 W2 mem2 md2 4 pos HAR Hfin) as (HF64 & _ & _).
pose proof (frm_off_imgP B ly2 S2 W2 mem2 md2 4 pos HAR Hfin) as HFimg.
rewrite HFeq in HF4096, HFceil, HF64, HFimg. change (fs_frame_bytes 4) with 1024 in HFceil, HFimg.
pose proof (pa_obj_img 6 ltac:(lia)) as HO6. pose proof (pa_val_range (A_OBJ 6)) as HR6.
destruct (HIMG W2 mem2 HROD) as (_ & Hg6 & HI1 & HI2 & _).
assert (Rmf : alloc_ceiling <= mf /\ 2 ^ 46 <= mf /\ mf + 320 <= 2 ^ 47)
by (clear - HMF Hslo Hshi Hceil H47 C1 HSTK'; lia).
assert (Htblv : forall i, 0 <= i < 36 -> aview SEGS (w_H W2) mem2 (VAL (A_OBJ 6) + i) = Some (nth (Z.to_nat i) HW_ROWS 0))
by (intros i Hi; apply (e_aview_garr8 W2 mem2 _ HW_ROWS i Hg6); rewrite e_hwrows_len; lia).
rewrite restrict_mkst_fx.
set (E := EE regs2 F hv).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs2 (map (Z_to_bv 64) [SB_E; F; hv])) n)
by (intros n Hn; subst E; unfold EE; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = w64 mf) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl); exact R2).
assert (E9 : ew E 9 = w64 mf) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs2 _ 9 9%bv eq_refl); exact R9).
assert (E32 : ew E 32 = Z_to_bv 64 SB_E) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 F) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 hv) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 2)).
assert (E6 : ew E (A_OBJ 6) = Z_to_bv 64 (VAL (A_OBJ 6)))
by (subst E; unfold EE; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
unfold ss_E0. apply pa_entry_st_ok_full.
- subst E. unfold EE. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok, e_mf, e_hw, e_tbl;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + rewrite (VB 9%nat mf E9) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ mf 48 8 (SOff 33 432) (F + 432));
      [cbn [sv_denot]; rewrite E33, unsigned_lit_small by lia; reflexivity | zside | zside | exact M48].
    * apply (chunk_ok_val SEGS E _ mf 176 8 (SOff 32 0) SB_E);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB_E; zside | zside | exact M176].
    * apply (chunk_ok_val SEGS E _ mf 184 8 (SOff 33 352) (F + 352));
      [cbn [sv_denot]; rewrite E33, unsigned_lit_small by lia; reflexivity | zside | zside | exact M184].
  + rewrite (VB 33%nat F E33) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ F 432 4 (SOff 34 0) hv);
    [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact MHW].
  + rewrite (VB (A_OBJ 6) (VAL (A_OBJ 6)) E6) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 6)) 0 4 (SLit 1) 1); [reflexivity | zside | zside |].
      rewrite Z.add_0_r. apply (e_vm4 W2 mem2 (VAL (A_OBJ 6)) 1); try lia;
      [ rewrite <- (Z.add_0_r (VAL (A_OBJ 6))); apply (Htblv 0) | apply (Htblv 1) | apply (Htblv 2)
      | apply (Htblv 3)]; lia.
    * apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 6)) 12 4 (SLit 2) 2); [reflexivity | zside | zside |].
      apply (e_vm4 W2 mem2 (VAL (A_OBJ 6) + 12) 2); try lia;
      [ apply (Htblv 12) | replace (VAL (A_OBJ 6) + 12 + 1) with (VAL (A_OBJ 6) + 13) by lia; apply (Htblv 13)
      | replace (VAL (A_OBJ 6) + 12 + 2) with (VAL (A_OBJ 6) + 14) by lia; apply (Htblv 14)
      | replace (VAL (A_OBJ 6) + 12 + 3) with (VAL (A_OBJ 6) + 15) by lia; apply (Htblv 15)]; lia.
    * apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 6)) 24 4 (SLit 3) 3); [reflexivity | zside | zside |].
      apply (e_vm4 W2 mem2 (VAL (A_OBJ 6) + 24) 3); try lia;
      [ apply (Htblv 24) | replace (VAL (A_OBJ 6) + 24 + 1) with (VAL (A_OBJ 6) + 25) by lia; apply (Htblv 25)
      | replace (VAL (A_OBJ 6) + 24 + 2) with (VAL (A_OBJ 6) + 26) by lia; apply (Htblv 26)
      | replace (VAL (A_OBJ 6) + 24 + 3) with (VAL (A_OBJ 6) + 27) by lia; apply (Htblv 27)]; lia.
- apply pairwise_disjoint_of_extents.
  unfold e_mf, e_hw, e_tbl, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB 9%nat mf E9) by lia. rewrite (VB 33%nat F E33) by lia.
  rewrite (VB (A_OBJ 6) (VAL (A_OBJ 6)) E6) by lia.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  clear - Rmf HF4096 HFceil HFimg HI1 HI2 C1.
  repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [e_atoms f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E2, E9, E32, E33, E34, E6. unfold w64. rewrite !unsigned_lit_small by (unfold SB_E; lia).
  change (2 ^ 5) with 32. change (2 ^ 6) with 64. rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold SB_E. clear - Rmf HMF32 HF4096 HFceil HF64 Hhv HO6 HR6 C1.
  repeat match goal with |- _ /\ _ => split end; try lia.
Qed.

(* ---- what the segment keeps -------------------------------------------------------------------------------- *)
(* The two calls write only inside their own stack windows below mf; the deeper is reac_box_family_of's
   (64 + 2 * ESTACK = 8256, the bcmp interceptor's is 2 * ESTACK). The engine's runs write nothing (every
   region of ss_E0 is read-only). *)
Definition e_keep (W : world SEGS) (m m' : word -> option byte) (mf : Z) : Prop :=
forall a, 0 <= a < 2 ^ 64 -> ~ (mf - 8256 <= a < mf) -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a.

Lemma e_keep_refl : forall W m mf, e_keep W m m mf.
Proof. intros W m mf a _ _. reflexivity. Qed.
Lemma e_keep_trans : forall W m0 m1 m2 mf, e_keep W m0 m1 mf -> e_keep W m1 m2 mf -> e_keep W m0 m2 mf.
Proof. intros W m0 m1 m2 mf H1 H2 a Ha Hw. rewrite (H2 a Ha Hw). exact (H1 a Ha Hw). Qed.
(* A run of the engine over read-only regions keeps every byte. *)
Lemma e_keep_run : forall W E (rs : smem) m0 m1 m2 mf,
forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true ->
frame_of E rs (rd W m1) (rd W m2) -> e_keep W m0 m1 mf -> e_keep W m0 m2 mf.
Proof.
intros W E rs m0 m1 m2 mf Hro HF HK a Ha Hw. rewrite <- (HK a Ha Hw).
apply (aview_eq_of SEGS). apply HF. intros (rg & Hin & Hr).
rewrite forallb_forall in Hro. specialize (Hro rg Hin). apply Z.leb_le in Hro. lia.
Qed.

(* Below the allocation ceiling (the frame, the heap blocks, every shadow byte and the image) and at or above
   mf (the machine frame and the entry's saved words) a kept state agrees with the start state. *)
Lemma e_keep_lo : forall W m m' mf a, e_keep W m m' mf -> alloc_ceiling + 8256 <= mf -> 0 <= a < alloc_ceiling ->
aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a.
Proof.
intros W m m' mf a HK Hmf Ha. pose proof asan_consts as (C1 & _). apply HK; lia.
Qed.
Lemma e_keep_hi : forall W m m' mf a, e_keep W m m' mf -> 0 <= mf -> mf <= a < 2 ^ 64 ->
aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a.
Proof. intros W m m' mf a HK H0 Ha. apply HK; lia. Qed.

Lemma e_garr8_moved : forall (W : world SEGS) (m m' : word -> option byte) a l,
(forall k, 0 <= k < Z.of_nat (length l) -> aview SEGS (w_H W) m' (a + k) = aview SEGS (w_H W) m (a + k)) ->
garr8 SEGS (rd W m) a l -> garr8 SEGS (rd W m') a l.
Proof.
intros W m m' a l Hk Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
apply (val_mem_moved SEGS (w_H W) (w_H W) m m' (a + Z.of_nat j) (a + Z.of_nat j) 1 (nth j l 0)); [|exact Hv].
intros i Hi. replace (a + Z.of_nat j + i) with (a + (Z.of_nat j + i)) by lia. apply Hk. cbn in Hi. lia.
Qed.
Lemma e_zs_moved : forall (W : world SEGS) (m m' : word -> option byte) a n,
(forall i, 0 <= i < n / 8 -> aview SEGS (w_H W) m' (shadow_of_addr SHADOW_OFF a + i) =
aview SEGS (w_H W) m (shadow_of_addr SHADOW_OFF a + i)) ->
sh_zero W m a n -> sh_zero W m' a n.
Proof. intros W m m' a n Hk Hz i Hi. rewrite (Hk i Hi). exact (Hz i Hi). Qed.
Lemma e_blk_moved : forall (W : world SEGS) (m m' : word -> option byte) a n,
(forall i, 0 <= i < (n + 7) / 8 -> aview SEGS (w_H W) m' (shadow_of_addr SHADOW_OFF a + i) =
aview SEGS (w_H W) m (shadow_of_addr SHADOW_OFF a + i)) ->
sh_blk W m a n -> sh_blk W m' a n.
Proof.
intros W m m' a n Hk (H8 & Hn & Hc). split; [exact H8|]. split; [exact Hn|].
intros i Hi. rewrite (Hk i Hi). exact (Hc i Hi).
Qed.

(* ---- what reac_box_family_of returns ------------------------------------------------------------------------ *)
(* famof_res, read at the identity struct's bytes and the image's HW_FAMILY, is the plain model's FAM of the struct. *)
Lemma e_r_is_FAM : forall (rdr : reader) (p t r : Z) (idb : list byte),
(forall i, 0 <= i < 38 -> rdr (p + i) = Some (bv_unsigned (nth (Z.to_nat i) idb (Z_to_bv 8 0)))) ->
(forall i, 0 <= i < 36 -> rdr (t + i) = Some (nth (Z.to_nat i) HW_ROWS 0)) ->
length idb = 38%nat -> p <> 0 ->
reac_box_family_of.famof_res rdr p t 1 2 3 r ->
r = SlotModel.FAM idb.
Proof.
intros rdr p t r idb Hid Htb Hlen Hp Hres.
assert (Hrow : forall j, (j < 3)%nat ->
(reac_box_family_of.famof_row rdr p t (Z.of_nat j) <-> map bv_unsigned (RcIdentModel.raw idb) = SlotModel.HWT j)).
{ intros j Hj. rewrite <- (e_rows_eq (RcIdentModel.raw idb) (SlotModel.HWT j) (e_raw_len idb Hlen) (e_hwt_len j Hj)).
  unfold reac_box_family_of.famof_row. split.
  - intros H i Hi. rewrite (e_raw_nth idb i (Z_to_bv 8 0) Hi).
    pose proof (H (Z.of_nat i) ltac:(lia)) as Hq.
    replace (p + 28 + Z.of_nat i) with (p + (28 + Z.of_nat i)) in Hq by lia.
    replace (t + 12 * Z.of_nat j + 4 + Z.of_nat i) with (t + (12 * Z.of_nat j + 4 + Z.of_nat i)) in Hq by lia.
    rewrite (Hid (28 + Z.of_nat i) ltac:(lia)), (Htb (12 * Z.of_nat j + 4 + Z.of_nat i) ltac:(lia)) in Hq.
    injection Hq as Hq.
    replace (Z.to_nat (28 + Z.of_nat i)) with (28 + i)%nat in Hq by lia.
    replace (Z.to_nat (12 * Z.of_nat j + 4 + Z.of_nat i)) with (4 + 12 * j + i)%nat in Hq by lia.
    rewrite Hq. apply e_hwb_row; [exact Hj | exact Hi].
  - intros H i Hi.
    replace (p + 28 + i) with (p + (28 + i)) by lia.
    replace (t + 12 * Z.of_nat j + 4 + i) with (t + (12 * Z.of_nat j + 4 + i)) by lia.
    rewrite (Hid (28 + i) ltac:(lia)), (Htb (12 * Z.of_nat j + 4 + i) ltac:(lia)). f_equal.
    pose proof (H (Z.to_nat i) ltac:(lia)) as Hq. rewrite (e_raw_nth idb (Z.to_nat i) (Z_to_bv 8 0) ltac:(lia)) in Hq.
    replace (Z.to_nat (28 + i)) with (28 + Z.to_nat i)%nat by lia. rewrite Hq.
    replace (Z.to_nat (12 * Z.of_nat j + 4 + i)) with (4 + 12 * j + Z.to_nat i)%nat by lia.
    symmetry. apply e_hwb_row; [exact Hj | lia]. }
assert (Hb36 : rdr (p + 36) = Some (bv_unsigned (nth 36 idb (Z_to_bv 8 0))))
by (pose proof (Hid 36 ltac:(lia)) as Hq; exact Hq).
unfold SlotModel.FAM, reac_box_family_of_c.FAMOF_FAM. cbn [Z.eqb].
destruct Hres as [(H0 & ->) | [(_ & Hz & ->) | [(_ & Hnz & H0 & ->) | [(_ & Hnz & Hn0 & H1 & ->) |
[(_ & Hnz & Hn0 & Hn1 & H2 & ->) | (_ & Hnz & Hn0 & Hn1 & Hn2 & ->)]]]]].
- exfalso. exact (Hp H0).
- rewrite Hb36 in Hz. injection Hz as Hz. rewrite Hz. reflexivity.
- assert (Hne : bv_unsigned (nth 36 idb (Z_to_bv 8 0)) <> 0) by (intros Hq; apply Hnz; rewrite Hb36, Hq; reflexivity).
  destruct (Z.eqb_spec (bv_unsigned (nth 36 idb (Z_to_bv 8 0))) 0) as [Hq|_]; [exfalso; exact (Hne Hq)|].
  change (RcIdentModel.raw idb) with (firstn 8 (skipn 28 idb)) in Hrow.
  pose proof (proj1 (Hrow 0%nat ltac:(lia)) H0) as Hm. cbn [SlotModel.HWT nth] in Hm. rewrite Hm.
  destruct (list_eq_dec Z.eq_dec _ _) as [_|Hc]; [reflexivity | exfalso; apply Hc; reflexivity].
- assert (Hne : bv_unsigned (nth 36 idb (Z_to_bv 8 0)) <> 0) by (intros Hq; apply Hnz; rewrite Hb36, Hq; reflexivity).
  destruct (Z.eqb_spec (bv_unsigned (nth 36 idb (Z_to_bv 8 0))) 0) as [Hq|_]; [exfalso; exact (Hne Hq)|].
  change (RcIdentModel.raw idb) with (firstn 8 (skipn 28 idb)) in Hrow.
  pose proof (proj1 (Hrow 1%nat ltac:(lia)) H1) as Hm.
  assert (Hnm : map bv_unsigned (firstn 8 (skipn 28 idb)) <> SlotModel.HWT 0)
  by (intros Hq; exact (Hn0 (proj2 (Hrow 0%nat ltac:(lia)) Hq))).
  cbn [SlotModel.HWT nth] in Hm, Hnm. rewrite Hm.
  destruct (list_eq_dec Z.eq_dec _ _) as [Hc|_]; [exfalso; apply Hnm; rewrite Hm; exact Hc|].
  destruct (list_eq_dec Z.eq_dec _ _) as [_|Hc]; [reflexivity | exfalso; apply Hc; reflexivity].
- assert (Hne : bv_unsigned (nth 36 idb (Z_to_bv 8 0)) <> 0) by (intros Hq; apply Hnz; rewrite Hb36, Hq; reflexivity).
  destruct (Z.eqb_spec (bv_unsigned (nth 36 idb (Z_to_bv 8 0))) 0) as [Hq|_]; [exfalso; exact (Hne Hq)|].
  change (RcIdentModel.raw idb) with (firstn 8 (skipn 28 idb)) in Hrow.
  pose proof (proj1 (Hrow 2%nat ltac:(lia)) H2) as Hm.
  assert (Hnm0 : map bv_unsigned (firstn 8 (skipn 28 idb)) <> SlotModel.HWT 0)
  by (intros Hq; exact (Hn0 (proj2 (Hrow 0%nat ltac:(lia)) Hq))).
  assert (Hnm1 : map bv_unsigned (firstn 8 (skipn 28 idb)) <> SlotModel.HWT 1)
  by (intros Hq; exact (Hn1 (proj2 (Hrow 1%nat ltac:(lia)) Hq))).
  cbn [SlotModel.HWT nth] in Hm, Hnm0, Hnm1. rewrite Hm.
  destruct (list_eq_dec Z.eq_dec _ _) as [Hc|_]; [exfalso; apply Hnm0; rewrite Hm; exact Hc|].
  destruct (list_eq_dec Z.eq_dec _ _) as [Hc|_]; [exfalso; apply Hnm1; rewrite Hm; exact Hc|].
  destruct (list_eq_dec Z.eq_dec _ _) as [_|Hc]; [reflexivity | exfalso; apply Hc; reflexivity].
- assert (Hne : bv_unsigned (nth 36 idb (Z_to_bv 8 0)) <> 0) by (intros Hq; apply Hnz; rewrite Hb36, Hq; reflexivity).
  destruct (Z.eqb_spec (bv_unsigned (nth 36 idb (Z_to_bv 8 0))) 0) as [Hq|_]; [exfalso; exact (Hne Hq)|].
  change (RcIdentModel.raw idb) with (firstn 8 (skipn 28 idb)) in Hrow.
  assert (Hnm0 : map bv_unsigned (firstn 8 (skipn 28 idb)) <> SlotModel.HWT 0)
  by (intros Hq; exact (Hn0 (proj2 (Hrow 0%nat ltac:(lia)) Hq))).
  assert (Hnm1 : map bv_unsigned (firstn 8 (skipn 28 idb)) <> SlotModel.HWT 1)
  by (intros Hq; exact (Hn1 (proj2 (Hrow 1%nat ltac:(lia)) Hq))).
  assert (Hnm2 : map bv_unsigned (firstn 8 (skipn 28 idb)) <> SlotModel.HWT 2)
  by (intros Hq; exact (Hn2 (proj2 (Hrow 2%nat ltac:(lia)) Hq))).
  cbn [SlotModel.HWT nth] in Hnm0, Hnm1, Hnm2.
  destruct (list_eq_dec Z.eq_dec _ _) as [Hc|_]; [exfalso; exact (Hnm0 Hc)|].
  destruct (list_eq_dec Z.eq_dec _ _) as [Hc|_]; [exfalso; exact (Hnm1 Hc)|].
  destruct (list_eq_dec Z.eq_dec _ _) as [Hc|_]; [exfalso; exact (Hnm2 Hc) | reflexivity].
Qed.

(* ---- the call chain at the entry's own calls ---------------------------------------------------------------- *)
(* s0 = sp0 holds the entry's saved ra and s0 (ecommon), above them is the entry's own chain (its pre-condition's
   achain, with ch = []), and the journal keeps every byte at or above sp0. *)
Lemma e_mod32_16 : forall x, x mod 32 = 0 -> x mod 16 = 0.
Proof.
intros x H. apply Z.mod_divide in H; [|lia]. apply Z.mod_divide; [lia|].
apply (Z.divide_trans _ 32); [exists 2; reflexivity | exact H].
Qed.
Lemma e_nth_map_bv : forall (l : list byte) j,
nth j (map (fun b : byte => bv_unsigned b) l) 0 = bv_unsigned (nth j l (Z_to_bv 8 0)).
Proof. intros l j. revert l. induction j as [|j IH]; intros [|x l]; cbn; try reflexivity. apply IH. Qed.

Lemma e_chain : forall g pos ly2 S2 (W2 : world SEGS) memc mdc k mf,
ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
ly2 S2 W2 memc mdc k ->
e_pre B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv
arodata_okS g ->
e_sp0 g - 336 <= mf <= e_sp0 g - 320 ->
val_mem SEGS (rd W2 memc) (e_sp0 g - 8) 8 RA_LLVMF ->
val_mem SEGS (rd W2 memc) (e_sp0 g - 16) 8 (s0Z (e_regs g)) ->
exists ch, achain ly2 (aview SEGS (w_H W2) memc) mf (e_sp0 g) ch.
Proof.
intros g pos ly2 S2 W2 memc mdc k mf HJ HPRE HMF Vra Vs0.
pose proof HPRE as (HFN & Hraz & _).
pose proof HFN as (HAR0 & _ & Hra4 & _ & _ & Hstk0 & _ & Hch0 & _).
pose proof HJ as (HAR2 & Hly2 & _ & _ & _ & _ & _ & _ & F1 & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _ & Htop0 & Htop1).
pose proof Hly2 as (_ & _ & _ & _ & _ & _ & _ & _ & ETop & _).
pose proof asan_consts as (C1 & _).
pose proof HSTK as HSTK'. unfold STK_LLVMF, ASTACK in HSTK'.
set (sp0 := e_sp0 g) in *.
change (spZ (e_regs g)) with sp0 in Hch0.
assert (Hach : achain ly2 (aview SEGS (w_H (e_W g)) (e_mem g)) sp0 (s0Z (e_regs g)) []).
{ apply (achain_ly_top (e_ly g)); [exact ETop | exact Hch0]. }
destruct (Z_lt_le_dec sp0 (ly_top ly2 - 16)) as [Hlt | Hge].
- exists [(sp0, RA_LLVMF, s0Z (e_regs g))].
  pose proof (bv_unsigned_in_range 64 (getr (e_regs g) 1)) as Rra. change (bv_modulus 64) with (2 ^ 64) in Rra.
  pose proof (bv_unsigned_in_range 64 (getr (e_regs g) 8)) as Rs0r. change (bv_modulus 64) with (2 ^ 64) in Rs0r.
  apply (achain_push ly2 _ _ sp0 (s0Z (e_regs g)) RA_LLVMF [] mf Hach).
  + rewrite ETop. clear - Htop1 H47. lia.
  + intros a Ha. apply F1; clear - Ha Hceil Hslo HSTK'; lia.
  + apply rdword_of_val_mem; [exact Vra | unfold raZ in Hraz; clear - Hraz Rra; lia].
  + apply rdword_of_val_mem; [exact Vs0 | unfold s0Z; clear - Rs0r; lia].
  + rewrite <- Hraz. exact Hra4.
  + clear - Hceil Hslo HSTK'. lia.
  + clear - Hsp0al. lia.
  + exact Hlt.
  + clear - HMF. lia.
- exists []. left. split; [right; left; exact Hge | reflexivity].
Qed.

(* ---- carrying the boundary's facts across the segment ---------------------------------------------------- *)
Lemma e_tr_hi : forall (W : world SEGS) m m' mf a (n : nat) v, e_keep W m m' mf -> 0 <= mf -> mf <= a ->
a + Z.of_nat n <= 2 ^ 64 -> val_mem SEGS (rd W m) a n v -> val_mem SEGS (rd W m') a n v.
Proof.
intros W m m' mf a n v HK H0 H1 H2 Hv. apply (val_mem_moved SEGS (w_H W) (w_H W) m m' a a n v); [|exact Hv].
intros kk Hkk. apply (e_keep_hi W m m' mf); [exact HK | lia | lia].
Qed.
Lemma e_tr_lo : forall (W : world SEGS) m m' mf a (n : nat) v, e_keep W m m' mf -> alloc_ceiling + 8256 <= mf ->
0 <= a -> a + Z.of_nat n <= alloc_ceiling -> val_mem SEGS (rd W m) a n v -> val_mem SEGS (rd W m') a n v.
Proof.
intros W m m' mf a n v HK H0 H1 H2 Hv. apply (val_mem_moved SEGS (w_H W) (w_H W) m m' a a n v); [|exact Hv].
intros kk Hkk. apply (e_keep_lo W m m' mf); [exact HK | exact H0 | lia].
Qed.
Lemma e_tr_bytes : forall (W : world SEGS) m m' mf a bs, e_keep W m m' mf -> alloc_ceiling + 8256 <= mf ->
0 <= a -> a + Z.of_nat (length bs) <= alloc_ceiling -> bytes_at8 W m a bs -> bytes_at8 W m' a bs.
Proof.
intros W m m' mf a bs HK H0 H1 H2 Hb. unfold bytes_at8 in *. apply (e_garr8_moved W m m' a); [|exact Hb].
intros kk Hkk. rewrite length_map in Hkk. apply (e_keep_lo W m m' mf); [exact HK | exact H0 | lia].
Qed.
(* A frame object's shadow cells lie below the allocation ceiling. *)
Lemma e_tr_zs : forall (W : world SEGS) m m' mf a n, e_keep W m m' mf -> alloc_ceiling + 8256 <= mf ->
0 <= a -> 0 <= n -> a + n <= 2 ^ 47 -> sh_zero W m a n -> sh_zero W m' a n.
Proof.
intros W m m' mf a n HK H0 H1 H2 H3 Hz. apply (e_zs_moved W m m' a n); [|exact Hz].
intros i Hi. pose proof asan_consts as (C1 & _). apply (e_keep_lo W m m' mf); [exact HK | exact H0|].
unfold shadow_of_addr, SHADOW_OFF. clear - H1 H2 H3 Hi C1. Z.div_mod_to_equations. lia.
Qed.
Lemma e_tr_blk : forall (W : world SEGS) m m' mf a n, e_keep W m m' mf -> alloc_ceiling + 8256 <= mf ->
0 <= a -> 0 <= n -> a + n + 8 <= 2 ^ 47 -> sh_blk W m a n -> sh_blk W m' a n.
Proof.
intros W m m' mf a n HK H0 H1 H2 H3 Hz. apply (e_blk_moved W m m' a n); [|exact Hz].
intros i Hi. pose proof asan_consts as (C1 & _). apply (e_keep_lo W m m' mf); [exact HK | exact H0|].
unfold shadow_of_addr, SHADOW_OFF. clear - H1 H2 H3 Hi C1. Z.div_mod_to_equations. lia.
Qed.
Lemma e_tr_id : forall g pos (W : world SEGS) m m' mf i, e_keep W m m' mf -> alloc_ceiling + 8256 <= mf ->
4096 <= SFa g pos -> SFa g pos + 1024 <= alloc_ceiling ->
id_at g pos i W m -> id_at g pos i W m'.
Proof.
intros g pos W m m' mf i HK H0 H1 H2 Hid. pose proof asan_consts as (C1 & _).
unfold id_at, V_id, N_id in *. destruct Hid as (Hb & Hz & Hk).
split; [|split].
- apply (e_tr_bytes W m m' mf); [exact HK | exact H0 | lia | | exact Hb].
  unfold m_id. rewrite SlotModel.rec_id_length. unfold RcIdentModel.ID_SIZE. lia.
- apply (e_tr_zs W m m' mf); [exact HK | exact H0 | lia | lia | lia | exact Hz].
- apply (e_tr_blk W m m' mf); [exact HK | exact H0 | lia | lia | lia | exact Hk].
Qed.
Lemma e_tr_hw : forall g pos (W : world SEGS) m m' mf i, e_keep W m m' mf -> alloc_ceiling + 8256 <= mf ->
4096 <= SFa g pos -> SFa g pos + 1024 <= alloc_ceiling ->
hw_at g pos i W m -> hw_at g pos i W m'.
Proof.
intros g pos W m m' mf i HK H0 H1 H2 Hhw. pose proof asan_consts as (C1 & _).
unfold hw_at, V_hw, N_hw in *. destruct Hhw as (Hv & Hb & Hz & Hk).
split; [|split; [|split]].
- apply (e_tr_lo W m m' mf); [exact HK | exact H0 | lia | cbn; lia | exact Hv].
- apply (e_tr_bytes W m m' mf); [exact HK | exact H0 | lia | | exact Hb].
  unfold m_hwb. rewrite e_hwb_len. lia.
- apply (e_tr_zs W m m' mf); [exact HK | exact H0 | lia | lia | lia | exact Hz].
- apply (e_tr_blk W m m' mf); [exact HK | exact H0 | lia | lia | lia | exact Hk].
Qed.

(* The read-only image of any state the walk reaches. *)
Lemma e_rod : forall g pos ly2 S2 (W2 : world SEGS) m md k,
ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly2 S2 W2 m md k ->
e_pre B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv
arodata_okS g ->
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W2) m).
Proof.
intros g pos ly2 S2 W2 m md k HJ HPRE.
pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HROS & _).
eapply (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img); [exact HJ | apply HRO; exact HROS].
Qed.

(* A read-only region keeps its bytes. *)
Lemma e_region_kept_ro : forall E H (m m2 : word -> option byte) n b lo hi w cs,
bv_unsigned (ew E n) = b ->
(forall a, b + lo <= a < b + hi -> aview SEGS H m2 a = aview SEGS H m a) ->
region_kept SEGS E (mrestrict H m) (mrestrict H m2) (YP09.mkRegion (Some n) lo hi w w cs).
Proof.
intros E H m m2 n b lo hi w cs Hn Hav.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). apply Hav. exact Ha.
- lia.
Qed.

(* ---- 0x81580: reac_box_family_of(&id) ------------------------------------------------------------------------ *)
(* The call through cl_callS with the callee's contract HFAM: the box is the frame object id (afobj, its whole
   shadow from id_at's sh_blk), the table is HW_FAMILY (HIMG). Its result is the plain model's FAM of id (e_r_is_FAM). *)
Lemma e_fam_call : forall g pos mf ly2 S2 (W2 : world SEGS) memc mdc k (regsc : bvmap 5 word),
ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
ly2 S2 W2 memc mdc k ->
frames S2 = [(4, pos)] ->
e_pre B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv
arodata_okS g ->
e_sp0 g - 336 <= mf <= e_sp0 g - 320 -> mf mod 32 = 0 ->
val_mem SEGS (rd W2 memc) (e_sp0 g - 8) 8 RA_LLVMF ->
val_mem SEGS (rd W2 memc) (e_sp0 g - 16) 8 (s0Z (e_regs g)) ->
getr regsc 1 = Z_to_bv 64 (BASE + 0xe78) -> getr regsc 2 = w64 mf -> getr regsc 8 = w64 (e_sp0 g) ->
getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 10 = w64 (SFa g pos + V_id) ->
id_at g pos (m_nrec g) W2 memc ->
SRr SEGS W2 (mkCfg (mkst regsc (Z_to_bv 64 (SIGMA IS_reac_box_family_of)) memc (seg_rom SEGS)) mdc)
(fun W3 c3 => exists regs3 mem3 md3,
c3 = mkCfg (mkst regs3 (Z_to_bv 64 (BASE + 0xe78)) mem3 (seg_rom SEGS)) md3 /\ W3 = W2 /\
ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
ly2 S2 W2 mem3 md3 k /\
aregs_preserved regsc regs3 /\
getr regs3 10 = Z_to_bv 64 (reac_box_family_of.famof_sx32 (SlotModel.FAM (m_id g (m_nrec g)))) /\
e_keep W2 memc mem3 mf).
Proof.
intros g pos mf ly2 S2 W2 memc mdc k regsc HJ HFR HPRE HMF HMF32 Vra Vs0 R1 R2 R8 R3 R4 R10 Hid.
unfold id_at, bytes_at8 in Hid. destruct Hid as (Hidb & _ & Hidk).
pose proof pa_base_lo as HBLO. pose proof pa_B_ok as HBASE.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HSTK as HSTK'. unfold STK_LLVMF, ASTACK in HSTK'.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstatic & _).
pose proof Hstatic as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
assert (Hfin : In (4, pos) (frames S2)) by (rewrite HFR; left; reflexivity).
pose proof (e_frame_addr_le _ _ _ 4 pos Hly) as HFeq. fold (SFa g pos) in HFeq.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 4 pos HAR Hfin) as (HF4096 & HFceil & _).
destruct (frame_al64 SEGS B ly2 S2 W2 memc mdc 4 pos HAR Hfin) as (HF64 & _ & _).
rewrite HFeq in HF4096, HFceil, HF64. change (fs_frame_bytes 4) with 1024 in HFceil.
pose proof (e_rod g pos ly2 S2 W2 memc mdc k HJ HPRE) as HROD.
set (F := SFa g pos) in *.
assert (Rmf : alloc_ceiling <= mf /\ 2 ^ 46 <= mf /\ mf + 320 <= 2 ^ 47)
by (clear - HMF Hslo Hshi Hceil H47 C1 HSTK'; lia).
destruct (e_chain g pos ly2 S2 W2 memc mdc k mf HJ HPRE HMF Vra Vs0) as (ch & Hch).
assert (Usp : spZ regsc = mf) by (unfold spZ; rewrite R2; apply unsigned_lit_small; lia).
assert (Us0 : s0Z regsc = e_sp0 g) by (unfold s0Z; rewrite R8; apply unsigned_lit_small; lia).
assert (WS : reac_box_family_of.REAC_BOX_FAMILY_OF_STK = 8256) by reflexivity.
rewrite (PSIG IS_reac_box_family_of AF_reac_box_family_of eq_refl).
destruct (HIMG W2 memc HROD) as (_ & _ & _ & _ & Hg16 & _).
assert (Htb : forall i, 0 <= i < 36 ->
aview SEGS (w_H W2) memc (VAL (A_OBJ 16) + i) = Some (nth (Z.to_nat i) HW_ROWS 0))
by (intros i Hi; apply (e_aview_garr8 W2 memc _ HW_ROWS i Hg16); rewrite e_hwrows_len; lia).
(* id's bytes, read through the reader *)
assert (Hidv : forall i, 0 <= i < 38 -> aview SEGS (w_H W2) memc (F + V_id + i) =
Some (bv_unsigned (nth (Z.to_nat i) (m_id g (m_nrec g)) (Z_to_bv 8 0)))).
{ intros i Hi. rewrite (e_aview_garr8 W2 memc _ _ i Hidb).
  - rewrite e_nth_map_bv. reflexivity.
  - rewrite length_map. unfold m_id. rewrite SlotModel.rec_id_length. unfold RcIdentModel.ID_SIZE. lia. }
pose proof (pa_obj_img 16 ltac:(lia)) as HO16.
eapply SRr_mono.
{ eapply (cl_callS B LAWS W2 regsc memc (Z_to_bv 64 (BASE + AF_reac_box_family_of)) LLVMF_STK (e_sp0 g) []
  (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly2 S2 mdc k reac_box_family_of.REAC_BOX_FAMILY_OF_STK
  [] 0 (mf - e_sp0 g) (Z_to_bv 64 (BASE + 0xe78)) ch
  (fun ly3 S3 W3 regs3 mem3 md3 => ly3 = ly2 /\ S3 = S2 /\ W3 = W2 /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsc - reac_box_family_of.REAC_BOX_FAMILY_OF_STK <= a < spZ regsc) ->
  aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W2) memc a) /\
  exists r, reac_box_family_of.famof_res (aview SEGS (w_H W2) memc) (F + V_id) reac_box_family_of.FAMOF_HWF 1 2 3 r /\
  getr regs3 10 = Z_to_bv 64 (reac_box_family_of.famof_sx32 r)) HJ).
  - rewrite Usp. lia.
  - clear - HMF32 Hal16. rewrite Zminus_mod, (e_mod32_16 mf HMF32), Hal16. reflexivity.
  - lia.
  - rewrite WS. lia.
  - rewrite WS. lia.
  - exact R3.
  - exact R4.
  - exact R1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite unsigned_lit_small by lia. lia.
  - replace (e_sp0 g + (mf - e_sp0 g)) with mf by lia. rewrite Us0. exact Hch.
  - intros HPRE1. eapply SRr_mono.
    + apply (HFAM ly2 S2 W2 regsc memc mdc ch (F + V_id) 1 2 3 HPRE1 R10).
      * unfold V_id. lia.
      * intros _. right. split; [|split].
        -- exists 4, pos. rewrite HFeq. change (fs_frame_bytes 4) with 1024. unfold V_id.
           split; [exact Hfin|]. lia.
        -- unfold V_id. lia.
        -- apply (block_shadow_range (aview SEGS (w_H W2) memc) SHADOW_OFF (F + V_id) N_id);
           [exact Hidk | lia | unfold N_id; lia].
      * unfold reac_box_family_of.famof_tbl, reac_box_family_of.FAMOF_HWF.
        split; [intros a Ha; replace a with (VAL (A_OBJ 16) + (a - VAL (A_OBJ 16))) by lia;
        rewrite (Htb (a - VAL (A_OBJ 16))) by lia; discriminate|].
        split; [lia|]. split.
        { apply (e_vm4 W2 memc (VAL (A_OBJ 16)) 1); [lia | | | |].
          - rewrite <- (Z.add_0_r (VAL (A_OBJ 16))) at 1. apply (Htb 0). lia.
          - apply (Htb 1). lia.
          - apply (Htb 2). lia.
          - apply (Htb 3). lia. }
        split; [lia|]. split.
        { apply (e_vm4 W2 memc (VAL (A_OBJ 16) + 12) 2); [lia | | | |].
          - apply (Htb 12). lia.
          - replace (VAL (A_OBJ 16) + 12 + 1) with (VAL (A_OBJ 16) + 13) by lia. apply (Htb 13). lia.
          - replace (VAL (A_OBJ 16) + 12 + 2) with (VAL (A_OBJ 16) + 14) by lia. apply (Htb 14). lia.
          - replace (VAL (A_OBJ 16) + 12 + 3) with (VAL (A_OBJ 16) + 15) by lia. apply (Htb 15). lia. }
        split; [lia|].
        { apply (e_vm4 W2 memc (VAL (A_OBJ 16) + 24) 3); [lia | | | |].
          - apply (Htb 24). lia.
          - replace (VAL (A_OBJ 16) + 24 + 1) with (VAL (A_OBJ 16) + 25) by lia. apply (Htb 25). lia.
          - replace (VAL (A_OBJ 16) + 24 + 2) with (VAL (A_OBJ 16) + 26) by lia. apply (Htb 26). lia.
          - replace (VAL (A_OBJ 16) + 24 + 3) with (VAL (A_OBJ 16) + 27) by lia. apply (Htb 27). lia. }
    + cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & HQ).
      exists ly3, S3, regs3, mem3, md3. split; [rewrite R1; reflexivity|].
      split; [exact HJ3|]. split; [exact HP3 | exact HQ].
  - intros a (rr & Hr & _). destruct Hr. }
cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & _ & HP3 & (-> & -> & -> & HK3 & r & Hr & R10')).
exists regs3, mem3, md3. split; [reflexivity|]. split; [reflexivity|].
split; [rewrite Z.add_0_r in HJ3; exact HJ3|]. split; [exact HP3|]. split.
- rewrite R10'. do 2 f_equal.
  apply (e_r_is_FAM (aview SEGS (w_H W2) memc) (F + V_id) (VAL (A_OBJ 16)) r (m_id g (m_nrec g))).
  + exact Hidv.
  + exact Htb.
  + unfold m_id. apply SlotModel.rec_id_length.
  + unfold V_id. lia.
  + exact Hr.
- intros a Ha Hw. apply HK3; [exact Ha | rewrite Usp, WS; exact Hw].
Qed.

(* ---- 0x815b8: bcmp(hw.raw, HW_TABLE + 4 + 12 j, 8) ---------------------------------------------------------- *)
Lemma e_bcmp_call : forall g pos mf ly2 S2 (W2 : world SEGS) memc mdc k (regsT : bvmap 5 word) (j retk : Z),
ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
ly2 S2 W2 memc mdc k ->
frames S2 = [(4, pos)] ->
e_pre B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv
arodata_okS g ->
e_sp0 g - 336 <= mf <= e_sp0 g - 320 -> mf mod 32 = 0 ->
0 <= j < 3 -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
getr regsT 10 = w64 (SFa g pos + V_hw + 4) -> getr regsT 11 = w64 (VAL (A_OBJ 6) + 4 + 12 * j) ->
getr regsT 12 = w64 8 -> getr regsT 1 = Z_to_bv 64 (BASE + retk) -> getr regsT 2 = w64 mf ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
hw_at g pos (m_nrec g) W2 memc ->
SRr SEGS W2 (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA IS___interceptor_trampoline_bcmp)) memc (seg_rom SEGS)) mdc)
(fun W3 c3 => W3 = W2 /\ exists regs3 mem3 md3 (v : word),
c3 = mkCfg (mkst regs3 (Z_to_bv 64 (BASE + retk)) mem3 (seg_rom SEGS)) md3 /\
ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
ly2 S2 W2 mem3 md3 k /\
aregs_preserved regsT regs3 /\ getr regs3 10 = v /\
(v = w64 0 <-> map bv_unsigned (m_hwb g (m_nrec g)) = SlotModel.HWT (Z.to_nat j)) /\
e_keep W2 memc mem3 mf).
Proof.
intros g pos mf ly2 S2 W2 memc mdc k regsT j retk HJ HFR HPRE HMF HMF32 Hj Hrk Hrk2 R10 R11 R12 R1 R2 R3 R4 Hhw.
unfold hw_at, bytes_at8 in Hhw. destruct Hhw as (_ & Hhwb & _ & Hhwk).
pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HSTK as HSTK'. unfold STK_LLVMF, ASTACK in HSTK'.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstatic & _).
pose proof Hstatic as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
assert (Hfin : In (4, pos) (frames S2)) by (rewrite HFR; left; reflexivity).
pose proof (e_frame_addr_le _ _ _ 4 pos Hly) as HFeq. fold (SFa g pos) in HFeq.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 4 pos HAR Hfin) as (HF4096 & HFceil & HFapp).
rewrite HFeq in HF4096, HFceil, HFapp. change (fs_frame_bytes 4) with 1024 in HFceil, HFapp.
pose proof (e_rod g pos ly2 S2 W2 memc mdc k HJ HPRE) as HROD.
set (F := SFa g pos) in *.
assert (Rmf : alloc_ceiling <= mf /\ 2 ^ 46 <= mf /\ mf + 320 <= 2 ^ 47)
by (clear - HMF Hslo Hshi Hceil H47 C1 HSTK'; lia).
assert (Usp : spZ regsT = mf) by (unfold spZ; rewrite R2; apply unsigned_lit_small; lia).
destruct (HIMG W2 memc HROD) as (_ & Hg6 & HI1 & HI2 & _).
pose proof (pa_obj_img 6 ltac:(lia)) as HO6.
assert (Htb : forall i, 0 <= i < 36 ->
aview SEGS (w_H W2) memc (VAL (A_OBJ 6) + i) = Some (nth (Z.to_nat i) HW_ROWS 0))
by (intros i Hi; apply (e_aview_garr8 W2 memc _ HW_ROWS i Hg6); rewrite e_hwrows_len; lia).
(* hw's eight raw bytes, read through the reader *)
assert (Hhwv : forall i, 0 <= i < 8 -> aview SEGS (w_H W2) memc (F + V_hw + 4 + i) =
Some (bv_unsigned (nth (Z.to_nat i) (m_hwb g (m_nrec g)) (Z_to_bv 8 0)))).
{ intros i Hi. rewrite (e_aview_garr8 W2 memc _ _ i Hhwb).
  - rewrite e_nth_map_bv. reflexivity.
  - rewrite length_map. unfold m_hwb. rewrite e_hwb_len. lia. }
destruct (ro_read_ok_glob SEGS B G ly2 S2 W2 memc mdc (VAL (A_OBJ 6)) 36 (VAL (A_OBJ 6) + 4 + 12 * j) 8
GM G_HW IV HAR) as [HyRA HyH]; [lia | lia | lia | lia | unfold IMG_HI; lia |].
eapply SRr_mono.
{ eapply (aj_bcmp_at SEGS B LAWS Hsegs (SIGMA IS___interceptor_trampoline_bcmp) ABCMP W2 regsT memc
  LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly2 S2 mdc k
  (F + V_hw + 4) (VAL (A_OBJ 6) + 4 + 12 * j) 8 (mf - e_sp0 g) (Z_to_bv 64 (BASE + retk)) HJ R10 R11 R12).
  - lia.
  - unfold V_hw. lia.
  - unfold V_hw. lia.
  - lia.
  - lia.
  - rewrite Usp. lia.
  - clear - HMF32 Hal16. rewrite Zminus_mod, (e_mod32_16 mf HMF32), Hal16. reflexivity.
  - lia.
  - unfold ESTACK. lia.
  - exact R3.
  - exact R4.
  - exact R1.
  - apply ret_ok_codeptr_v; [lia | exact Hrk2].
  - intros a Ha. split.
    + replace a with (F + V_hw + 4 + (a - (F + V_hw + 4))) by lia.
      rewrite (Hhwv (a - (F + V_hw + 4))) by lia. discriminate.
    + rewrite Usp. unfold ESTACK, V_hw in *. lia.
  - intros a Ha. split.
    + replace a with (VAL (A_OBJ 6) + (a - VAL (A_OBJ 6))) by lia.
      rewrite (Htb (a - VAL (A_OBJ 6))) by lia. discriminate.
    + rewrite Usp. unfold ESTACK. lia.
  - intros a Ha. unfold ESTACK, V_hw in *. lia.
  - intros a Ha. unfold ESTACK. lia.
  - apply (amem_range_sub_app F 1024 (F + V_hw + 4) 8); [exact HFapp | exact HFceil | unfold V_hw; lia | unfold V_hw; lia | lia].
  - apply amem_range_high; lia.
  - apply (block_shadow_range (aview SEGS (w_H W2) memc) SHADOW_OFF (F + V_hw) N_hw);
    [exact Hhwk | lia | unfold N_hw; lia].
  - intros _. apply (shadow_hull_vis_of_frame SEGS B LAWS ly2 S2 W2 memc mdc 4 pos (F + V_hw + 4) 8 HAR Hfin);
    try rewrite HFeq; try change (fs_frame_bytes 4) with 1024; unfold V_hw; lia.
  - exact HyRA.
  - intros _. exact HyH. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & v & -> & HJ3 & HP3 & Hv & Hcmp & Hfr3 & Hpres3).
split; [reflexivity|]. exists regs3, mem3, md3, v.
split; [reflexivity|]. split; [exact HJ3|]. split; [exact HP3|]. split; [exact Hv|]. split.
- rewrite Hcmp. set (jn := Z.to_nat j).
  assert (Hjn : (jn < 3)%nat) by (subst jn; lia).
  rewrite <- (e_rows_eq (m_hwb g (m_nrec g)) (SlotModel.HWT jn) (e_hwb_len _ _) (e_hwt_len jn Hjn)).
  split.
  + intros H i Hi. pose proof (H (Z.of_nat i) ltac:(lia)) as Hq.
    rewrite (Hhwv (Z.of_nat i)) in Hq by lia.
    replace (VAL (A_OBJ 6) + 4 + 12 * j + Z.of_nat i) with (VAL (A_OBJ 6) + (4 + 12 * j + Z.of_nat i)) in Hq by lia.
    rewrite (Htb (4 + 12 * j + Z.of_nat i)) in Hq by lia. injection Hq as Hq.
    rewrite Nat2Z.id in Hq. rewrite Hq.
    replace (Z.to_nat (4 + 12 * j + Z.of_nat i)) with (4 + 12 * jn + i)%nat by (subst jn; lia).
    apply e_hwb_row; [exact Hjn | exact Hi].
  + intros H i Hi. rewrite (Hhwv i Hi).
    replace (VAL (A_OBJ 6) + 4 + 12 * j + i) with (VAL (A_OBJ 6) + (4 + 12 * j + i)) by lia.
    rewrite (Htb (4 + 12 * j + i)) by lia. f_equal.
    rewrite (H (Z.to_nat i) ltac:(lia)).
    replace (Z.to_nat (4 + 12 * j + i)) with (4 + 12 * jn + Z.to_nat i)%nat by (subst jn; lia).
    symmetry. apply e_hwb_row; [exact Hjn | lia].
- intros a Ha Hw. apply Hfr3; [exact Ha | unfold ESTACK; lia].
Qed.

(* ---- 0x815f8: the boundary inv_E_end -------------------------------------------------------------------------- *)
(* Every leaf of the walk ends here with the same facts: the journal from the entry at the same layout, state and
   world (no event, no allocation), every byte outside the calls' windows kept, the eight registers the
   boundary and ecommon name unchanged, and a3 = SHADOW_OFF (0x815cc or 0x815e0). The model equation is
   SlotModel.rec_P7. *)
Lemma e_leaf : forall g pos mf ly2 S2 (W2 : world SEGS) regs2 mem2 md2 regs3 mem3 md3,
ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
ly2 S2 W2 mem3 md3 (4 * Z.of_nat (m_nrec g)) ->
frames S2 = [(4, pos)] -> 0 <= 4 * Z.of_nat (m_nrec g) <= EV_LLVMF ->
mo_le MT (e_S g) S2 (4 * Z.of_nat (m_nrec g) * (mo_malloc MT 256 + mo_free MT)) ->
mo_ok MT S2 ((EV_LLVMF - 4 * Z.of_nat (m_nrec g)) * (mo_malloc MT 256 + mo_free MT)) ->
ecommon B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv
arodata_okS g pos mf ly2 S2 W2 regs2 mem2 md2 ->
cur_at g (m_nrec g) regs2 -> id_at g pos (m_nrec g) W2 mem2 -> hw_at g pos (m_nrec g) W2 mem2 ->
hblocks B g ly2 S2 [] -> mf_id3 g pos mf W2 mem2 -> mf_id g pos mf W2 mem2 ->
e_keep W2 mem2 mem3 mf ->
(forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 26]%bv -> getr regs3 r = getr regs2 r) ->
getr regs3 13 = w64 SHADOW_OFF ->
inv_E_end B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv
arodata_okS g pos mf W2 (mkCfg (mkst regs3 (Z_to_bv 64 (BASE + 0xeec)) mem3 (seg_rom SEGS)) md3).
Proof.
intros g pos mf ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 HJ3 HFR Hk MLE MOK HEC Hcur Hid Hhw Hbl Vid3 Vid HK HR R13.
destruct HEC as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & Rs3 & V80 & V192 & V176 & Vra & Vs0 &
V24 & V32 & V40 & V48 & V56 & V64 & V72 & V80b & V88 & V96 & V104 & Vmf24 & Vflag & HPRE & Hfds & Hfs & Hinb).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HSTK as HSTK'. unfold STK_LLVMF, ASTACK in HSTK'.
pose proof HJ3 as (HAR3 & Hly3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
assert (Hfin : In (4, pos) (frames S2)) by (rewrite HFR; left; reflexivity).
pose proof (e_frame_addr_le _ _ _ 4 pos Hly3) as HFeq. fold (SFa g pos) in HFeq.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 4 pos HAR3 Hfin) as (HF4096 & HFceil & _).
rewrite HFeq in HF4096, HFceil. change (fs_frame_bytes 4) with 1024 in HFceil.
assert (Hmf0 : alloc_ceiling + 8256 <= mf) by (clear - Hmfb Hceil Hslo HSTK'; lia).
assert (Hmfp : 0 <= mf) by lia.
assert (Hsp47 : e_sp0 g <= 2 ^ 47) by (clear - Hshi H47; lia).
destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as [Efd Efs].
unfold inv_E_end, acut.
exists ly2, S2, regs3, mem3, md3.
split; [reflexivity|]. split; [exact HJ3|]. split; [exact HFR|]. split; [exact Hk|].
split; [exact MLE|]. split; [exact MOK|]. split.
- unfold ecommon.
  split; [rewrite (HR 2%bv ltac:(cbn; tauto)); exact Rsp|].
  split; [rewrite (HR 9%bv ltac:(cbn; tauto)); exact Rs1|].
  split; [rewrite (HR 8%bv ltac:(cbn; tauto)); exact Rs0|].
  split; [exact Hmfb|]. split; [exact Hmf32|].
  split; [rewrite (HR 3%bv ltac:(cbn; tauto)); exact Rgp|].
  split; [rewrite (HR 4%bv ltac:(cbn; tauto)); exact Rtp|].
  split; [rewrite (HR 19%bv ltac:(cbn; tauto)); exact Rs3|].
  split; [apply (e_tr_hi W2 mem2 mem3 mf); [exact HK | exact Hmfp | lia | cbn; lia | exact V80]|].
  split; [apply (e_tr_hi W2 mem2 mem3 mf); [exact HK | exact Hmfp | lia | cbn; lia | exact V192]|].
  split; [apply (e_tr_hi W2 mem2 mem3 mf); [exact HK | exact Hmfp | lia | cbn; lia | exact V176]|].
  split; [apply (e_tr_hi W2 mem2 mem3 mf); [exact HK | exact Hmfp | lia | cbn; lia | exact Vra]|].
  split; [apply (e_tr_hi W2 mem2 mem3 mf); [exact HK | exact Hmfp | lia | cbn; lia | exact Vs0]|].
  split; [apply (e_tr_hi W2 mem2 mem3 mf); [exact HK | exact Hmfp | lia | cbn; lia | exact V24]|].
  split; [apply (e_tr_hi W2 mem2 mem3 mf); [exact HK | exact Hmfp | lia | cbn; lia | exact V32]|].
  split; [apply (e_tr_hi W2 mem2 mem3 mf); [exact HK | exact Hmfp | lia | cbn; lia | exact V40]|].
  split; [apply (e_tr_hi W2 mem2 mem3 mf); [exact HK | exact Hmfp | lia | cbn; lia | exact V48]|].
  split; [apply (e_tr_hi W2 mem2 mem3 mf); [exact HK | exact Hmfp | lia | cbn; lia | exact V56]|].
  split; [apply (e_tr_hi W2 mem2 mem3 mf); [exact HK | exact Hmfp | lia | cbn; lia | exact V64]|].
  split; [apply (e_tr_hi W2 mem2 mem3 mf); [exact HK | exact Hmfp | lia | cbn; lia | exact V72]|].
  split; [apply (e_tr_hi W2 mem2 mem3 mf); [exact HK | exact Hmfp | lia | cbn; lia | exact V80b]|].
  split; [apply (e_tr_hi W2 mem2 mem3 mf); [exact HK | exact Hmfp | lia | cbn; lia | exact V88]|].
  split; [apply (e_tr_hi W2 mem2 mem3 mf); [exact HK | exact Hmfp | lia | cbn; lia | exact V96]|].
  split; [apply (e_tr_hi W2 mem2 mem3 mf); [exact HK | exact Hmfp | lia | cbn; lia | exact V104]|].
  split; [apply (e_tr_hi W2 mem2 mem3 mf); [exact HK | exact Hmfp | lia | cbn; lia | exact Vmf24]|].
  split; [apply (e_tr_lo W2 mem2 mem3 mf); [exact HK | exact Hmf0 | lia | cbn; lia | exact Vflag]|].
  split; [exact HPRE|]. split; [intros fd; rewrite Efd; reflexivity|]. split; [exact Efs|].
  pose proof HPRE as (HFN & _ & _ & _ & Hinp & Hlen & _).
  destruct Hinp as [[Hn0 _] | [[Hn0 Hn26] Hine]].
  + destruct (e_pl g) as [|b0 l0] eqn:Epl; [|cbn in Hlen; lia].
    unfold bytes_at8. cbn [map]. apply garr8_nil.
  + pose proof HFN as (HAR0 & _).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ (e_p g) (e_n g) HAR0 Hine) as (_ & Hp4096 & Hpce & _).
    pose proof (req_size_pos (e_n g) ltac:(lia)) as [_ Hrq].
    apply (e_tr_bytes W2 mem2 mem3 mf); [exact HK | exact Hmf0 | lia | rewrite <- Hlen; lia | exact Hinb].
- split; [exact (e_tr_id g pos W2 mem2 mem3 mf (m_nrec g) HK Hmf0 HF4096 HFceil Hid)|].
  split; [exact (e_tr_hw g pos W2 mem2 mem3 mf (m_nrec g) HK Hmf0 HF4096 HFceil Hhw)|].
  split; [exact Hbl|].
  split; [apply (e_tr_hi W2 mem2 mem3 mf); [exact HK | exact Hmfp | lia | cbn; lia | exact Vid3]|].
  split; [apply (e_tr_hi W2 mem2 mem3 mf); [exact HK | exact Hmfp | lia | cbn; lia | exact Vid]|].
  split; [exact (SlotModel.rec_P7 (e_pl g) (m_nrec g))|].
  destruct Hcur as (C26 & C18 & _).
  split; [rewrite (HR 26%bv ltac:(cbn; tauto)); exact C26|].
  split; [rewrite (HR 18%bv ltac:(cbn; tauto)); exact C18|].
  exact R13.
Qed.

(* ---- the branches ------------------------------------------------------------------------------------------- *)
Lemma e_br_eq0 : forall E n (v : word), ew E n = v ->
branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = true -> v = w64 0.
Proof.
intros E n v Hn Hb. rewrite branch_eq_U in Hb. apply Z.eqb_eq in Hb.
unfold U in Hb. cbn [sv_denot] in Hb. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned in Hb.
apply bv_eq. exact Hb.
Qed.
Lemma e_br_ne0 : forall E n (v : word), ew E n = v ->
branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = false -> v <> w64 0.
Proof.
intros E n v Hn Hb Hv. rewrite branch_eq_U in Hb. apply Z.eqb_neq in Hb. apply Hb.
unfold U. cbn [sv_denot]. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned, Hv. reflexivity.
Qed.
Lemma e_br_val : forall E n z c, ew E n = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> 0 <= c < 2 ^ 64 ->
branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit c)) = (z =? c) /\
branch_taken BC_NE (sv_denot E (SOff n 0)) (sv_denot E (SLit c)) = negb (z =? c).
Proof.
intros E n z c Hn Hz Hc. rewrite branch_eq_U, branch_ne_U, (U_atom E n z Hn Hz), U_SLit, zcanon_id
by (unfold M64; lia). split; reflexivity.
Qed.

(* ---- the walk's tactics ---------------------------------------------------------------------------------- *)
(* Runs extend the environment (ewset) and calls havoc it at or above A_LIM; these take a goal about the
   environment in hand back to the entry environment E. *)
Ltac e_env_old := repeat first [ rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia ].
(* the atom a call's clobber gave a register (0x10 at index 4 of CLOB) *)
Ltac e_hv Hv :=
e_env_old;
lazymatch goal with |- ew (havoc _ ?K _) ?n = _ =>
let j := eval vm_compute in (n - K)%nat in
change n with (K + j)%nat; rewrite (ew_havoc_new _ K _ j (Z_to_bv 64 0)) by (cbn; lia);
cbn [nth map CLOB]; exact Hv end.
(* the kept-bytes fact after a run (every region read-only) *)
Ltac e_keep_step :=
lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict _ ?m1) (mrestrict _ ?m2), HKo : e_keep ?Wd ?m0 _ ?mfv |- _ =>
let HK2 := fresh "HKn" in
assert (HK2 : e_keep Wd m0 m2 mfv)
by (apply (e_keep_run Wd Ex rs m0 m1 m2 mfv); [vm_compute; reflexivity | exact HFr | exact HKo]);
clear HKo; rename HK2 into HK end;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
(* HW_TABLE's shadow entry, re-made from the current state's AR after a call *)
Ltac e_shok E32 :=
lazymatch goal with HS : st_ok_pi _ _ ?Ev _ (restrict (w_H ?Wd) _),
HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mx _ _ |- _ =>
let HEIa := fresh "HEIa" in
assert (HEIa : img_env VAL A_LIM Ev) by (apply img_env_havoc_hi; [assumption | cbv; lia]);
assert (SHOK : sh_ok SEGS Bx_E e_SHT Ev (mrestrict (w_H Wd) mx));
[ unfold sh_ok, e_SHT; apply Forall_cons; [ | apply Forall_nil ];
  apply (shent_ok_of_range SEGS (w_H Wd) mx Ev Bx_E (A_OBJ 6) (VAL (A_OBJ 6)) 36 (VAL (A_OBJ 6)) 0 36
  (ro_usable_glob SEGS B G _ _ Wd mx _ (VAL (A_OBJ 6)) 36 (VAL (A_OBJ 6)) 36 GM G_HW (proj1 HJx)
  ltac:(lia) ltac:(lia)));
  [ unfold U, Bx_E; cbn [sv_denot]; e_env_old; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned;
    rewrite unsigned_lit_small by (unfold SB_E; lia); reflexivity
  | exact (U_img_atom Ev HEIa (A_OBJ 6) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))
  | lia | lia
  | intros x Hx; cbn [Z.min Z.max] in Hx; pose proof (pa_obj_img 6 ltac:(lia)); unfold SHADOW_OFF; lia ]
| ] end.
(* after a call: the three regions are kept (every byte outside the call's window) *)
Ltac e_kept U9 U33 U6 HKc Hmfp Hmf0 :=
cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil;
[ apply (e_region_kept_ro _ _ _ _ 9%nat _ _ _ _ _ U9);
  intros a Ha; apply (e_keep_hi _ _ _ _ a HKc Hmfp); lia
| apply (e_region_kept_ro _ _ _ _ 33%nat _ _ _ _ _ U33);
  intros a Ha; apply (e_keep_lo _ _ _ _ a HKc Hmf0); lia
| apply (e_region_kept_ro _ _ _ _ (A_OBJ 6) _ _ _ _ _ U6);
  intros a Ha; apply (e_keep_lo _ _ _ _ a HKc Hmf0); lia ].
(* the boundary at 0x815f8 *)
Ltac e_fin g pos mf ly2 S2 W2 regs2 mem2 md2 HFR Hk MLE MOK HEC Hcur Hid Hhw Hbl Vid3 Vid184 HAE E32 :=
lazymatch goal with HS : st_ok_pi _ _ ?Ev ?ssx (restrict _ ?msc),
HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, HKx : e_keep _ _ _ _ |- _ =>
let R13 := fresh "R13" in let HRk := fresh "HRk" in
prreg HS (13%bv : bv 5) R13;
pose proof (regs_kept_of_st_ok_pi Ev ssx (restrict (w_H W2) msc) regs2
(map (Z_to_bv 64) [SB_E; SFa g pos; m_have g (m_nrec g)]) [2; 3; 4; 8; 9; 18; 19; 26]%bv HS
ltac:(split; [intros nn Hnn; e_env_old; exact (proj1 HAE nn Hnn) | cbn [ed havoc ewset]; exact (proj2 HAE)])
ltac:(vm_compute; reflexivity)) as HRk;
cbn [ms_regs restrict] in HRk;
pmkst HS; apply SRr_ret;
apply (e_leaf g pos mf ly2 S2 W2 regs2 mem2 md2 _ _ _ HJx HFR Hk MLE MOK HEC Hcur Hid Hhw Hbl Vid3 Vid184 HKx HRk);
rewrite R13, E32; reflexivity end.

(* ---- the walk ------------------------------------------------------------------------------------------------ *)
(* Run 1 (0x8157c) loads &id and stops at the call of reac_box_family_of; e_fam_call gives its result r = FAM id.
   Run 2 (0x81584) loads hw.have and stops at 0x81590. With have = 0 the run reaches 0x815d0 and r = 0 holds
   (fam_hw 0 _ = 0). Otherwise each of the three rows runs to the bcmp call (e_bcmp_call), rebuilds the symbolic
   state (the three regions are kept, the shadow entry of HW_TABLE is re-made) and branches on the result
   (0x815bc): 0 runs through the table's shadow test to 0x815f4, where r = j + 1 = fam_cmp hw.raw holds; not 0
   goes on to the next row, and after row 2 to 0x815d0, where r = 0 = fam_cmp hw.raw holds. *)
Theorem seg_E_holds : seg_E B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
asink_none ameta_inv arodata_okS.
Proof.
intros g pos mf W2 c2 Hstart.
destruct Hstart as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & HFR & Hk & MLE & MOK & HEC & HP).
pose proof HEC as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & Rs3 & V80 & V192 & V176 & Vra & Vs0 &
_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRE & _ & _ & _).
pose proof HP as (Hcur & Hid & Hhw & Hbl & Vhw48 & Vid3 & Vid184). clear HP.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_base_lo as HBLO. pose proof pa_B_ok as HBASE.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HSTK as HSTK'. unfold STK_LLVMF, ASTACK in HSTK'.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
assert (Hfin : In (4, pos) (frames S2)) by (rewrite HFR; left; reflexivity).
pose proof (e_frame_addr_le _ _ _ 4 pos Hly) as HFeq. fold (SFa g pos) in HFeq.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 4 pos HAR Hfin) as (HF4096 & HFceil & _).
rewrite HFeq in HF4096, HFceil. change (fs_frame_bytes 4) with 1024 in HFceil.
clear HAR Hly Hstatic HFeq Hfin.
assert (Hmf0 : alloc_ceiling + 8256 <= mf) by (clear - Hmfb Hceil Hslo HSTK'; lia).
assert (Hmfp : 0 <= mf) by lia.
pose proof (pa_obj_img 6 ltac:(lia)) as HO6. pose proof (pa_val_range (A_OBJ 6)) as HR6.
(* the model: reac_box_family_of's result is FAM id = fam_hw have hw.raw *)
assert (Hhv : 0 <= m_have g (m_nrec g) <= 1)
by (unfold m_have, SlotModel.rec_have; destruct (SlotModel.rec_hw _ _); lia).
assert (HFV : SlotModel.FAM (m_id g (m_nrec g)) = SlotModel.fam_hw (m_have g (m_nrec g)) (m_hwb g (m_nrec g)))
by exact (SlotModel.rec_P7 (e_pl g) (m_nrec g)).
assert (HFVr : 0 <= SlotModel.FAM (m_id g (m_nrec g)) <= 3).
{ rewrite HFV. unfold SlotModel.fam_hw, SlotModel.fam_cmp. cbv zeta.
  destruct (m_have g (m_nrec g) =? 0); [lia|].
  repeat (destruct (list_eq_dec Z.eq_dec _ _); [lia|]). lia. }
assert (Hsx : reac_box_family_of.famof_sx32 (SlotModel.FAM (m_id g (m_nrec g))) = SlotModel.FAM (m_id g (m_nrec g)))
by (unfold reac_box_family_of.famof_sx32; destruct (Z.ltb_spec (SlotModel.FAM (m_id g (m_nrec g))) (2 ^ 31)); lia).
(* the symbolic state at 0x8157c *)
pose proof (e_rod g pos ly2 S2 W2 mem2 md2 _ HJ HPRE) as HROD.
pose proof (e_start g pos mf ly2 S2 W2 regs2 mem2 md2 _ HJ HFR Rsp Rs1 Hmfb Hmf32 HSTK Vhw48 V176 Vid184
(proj1 Hhw) Hhv HROD) as HS.
clear HROD.
remember (EE regs2 (SFa g pos) (m_have g (m_nrec g))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold EE; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat ->
ew E n = ew (Ereg regs2 (map (Z_to_bv 64) [SB_E; SFa g pos; m_have g (m_nrec g)])) n)
by (intros n Hn; subst E; unfold EE; apply Eimg_low; exact Hn).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs2 rr)
by (intros n rr Hn; subst E; unfold EE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 SB_E) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (SFa g pos)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (m_have g (m_nrec g)))
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 2)).
assert (E6 : ew E (A_OBJ 6) = Z_to_bv 64 (VAL (A_OBJ 6)))
by (apply (img_env_atomP E (A_OBJ 6) HEI); unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (U9 : bv_unsigned (ew E 9) = mf) by (rewrite (EEo 9%nat 9%bv eq_refl), Rs1; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = SFa g pos) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U6 : bv_unsigned (ew E (A_OBJ 6)) = VAL (A_OBJ 6)) by (rewrite E6; apply unsigned_lit_small; lia).
assert (HAE : env_agree 32 (Ereg regs2 (map (Z_to_bv 64) [SB_E; SFa g pos; m_have g (m_nrec g)])) E)
by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
clear HE EL.
assert (SHOK : sh_ok SEGS Bx_E [] E (mrestrict (w_H W2) mem2)) by constructor.
assert (HK : e_keep W2 mem2 mem2 mf) by apply e_keep_refl.
unfold cfg_at. change (w64 (BASE + 0xe70)) with (Z_to_bv 64 (BASE + 0xe70)).
(* ---- run 1: 0x8157c ld a0,184(s1); 0x81580 jal reac_box_family_of ---- *)
paj_run_tok RUN HS HJ SHOK Bspan_E; [awr_ok_tac |].
e_keep_step.
prreg HS (10%bv : bv 5) Q10. prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2.
prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
eapply SRr_bind;
[ apply (e_fam_call g pos mf ly2 S2 W2 mm mdq _ rg HJ HFR HPRE Hmfb Hmf32);
  [ apply (e_tr_hi W2 mem2 mm mf); [exact HK | exact Hmfp | lia | cbn; lia | exact Vra]
  | apply (e_tr_hi W2 mem2 mm mf); [exact HK | exact Hmfp | lia | cbn; lia | exact Vs0]
  | exact Q1
  | rewrite Q2, (EEo 2%nat 2%bv eq_refl); exact Rsp
  | rewrite Q8, (EEo 8%nat 8%bv eq_refl); exact Rs0
  | rewrite Q3, (EEo 3%nat 3%bv eq_refl); exact Rgp
  | rewrite Q4, (EEo 4%nat 4%bv eq_refl); exact Rtp
  | rewrite Q10, E33, (unsigned_lit_small (SFa g pos)) by lia; reflexivity
  | exact (e_tr_id g pos W2 mem2 mm mf (m_nrec g) HK Hmf0 HF4096 HFceil Hid) ]
| ] end.
clear Q10 Q1 Q2 Q3 Q4 Q8.
cbv beta. intros W3 c3 _ (regs3 & mem3 & md3 & -> & -> & HJ3 & HP3 & R10f & HK3).
rewrite Hsx in R10f.
jafter_call_keep_hi HS 512%nat regs3 (mrestrict (w_H W2) mem3) HP3 [0;1;2]%nat HS3.
match type of HS3 with ?Q -> _ => assert (HQ : Q); [ | specialize (HS3 HQ); clear HQ ] end.
{ e_kept U9 U33 U6 HK3 Hmfp Hmf0. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
pose proof (e_keep_trans _ _ _ _ _ HK HK3) as HKn. clear HK HK3. rename HKn into HK.
clear HJ SHOK. rename HJ3 into HJ.
e_shok E32.
(* ---- run 2: 0x81584 .. 0x81590 beqz a1 (hw.have) ---- *)
paj_run_tok RUN HS HJ SHOK Bspan_E; [awr_ok_tac |].
e_keep_step.
psrr_branch_tok RUN BR HS SHOK Bspan_E.
{ (* have = 0: 0x815cc, and 0x815d0 beqz s6 needs r = 0 *)
  assert (Hh0 : m_have g (m_nrec g) = 0).
  { lazymatch type of Hc with branch_taken BC_EQ (sv_denot ?Ev (SOff 34 0)) (sv_denot _ (SLit 0)) = true =>
    destruct (e_br_val Ev 34 (m_have g (m_nrec g)) 0 ltac:(e_env_old; exact E34) ltac:(lia) ltac:(lia)) as [Hb _] end.
    rewrite Hb in Hc. apply Z.eqb_eq in Hc. exact Hc. }
  clear Hc.
  assert (HF0 : SlotModel.FAM (m_id g (m_nrec g)) = 0) by (rewrite HFV; unfold SlotModel.fam_hw; rewrite Hh0; reflexivity).
  paj_run_to_tok RUNTO HS HJ SHOK Bspan_E 0xeec; [awr_ok_tac |].
  e_keep_step.
  psrr_branch_tok RUN BR HS SHOK Bspan_E.
  - clear Hc. paj_run_to_tok RUNTO HS HJ SHOK Bspan_E 0xeec; [awr_ok_tac |]. e_keep_step.
    e_fin g pos mf ly2 S2 W2 regs2 mem2 md2 HFR Hk MLE MOK HEC Hcur Hid Hhw Hbl Vid3 Vid184 HAE E32.
  - exfalso.
    lazymatch type of Hc with branch_taken BC_EQ (sv_denot ?Ev (SOff ?n 0)) (sv_denot _ (SLit 0)) = false =>
    destruct (e_br_val Ev n (SlotModel.FAM (m_id g (m_nrec g))) 0 ltac:(e_hv R10f) ltac:(lia) ltac:(lia)) as [Hb _] end.
    rewrite Hb, HF0 in Hc. discriminate Hc. }
(* have = 1: the table walk *)
assert (Hh1 : m_have g (m_nrec g) = 1).
{ lazymatch type of Hc with branch_taken BC_EQ (sv_denot ?Ev (SOff 34 0)) (sv_denot _ (SLit 0)) = false =>
  destruct (e_br_val Ev 34 (m_have g (m_nrec g)) 0 ltac:(e_env_old; exact E34) ltac:(lia) ltac:(lia)) as [Hb _] end.
  rewrite Hb in Hc. apply Z.eqb_neq in Hc. lia. }
clear Hc.
assert (HFc : SlotModel.FAM (m_id g (m_nrec g)) = SlotModel.fam_cmp (m_hwb g (m_nrec g)))
by (rewrite HFV; unfold SlotModel.fam_hw; rewrite Hh1; reflexivity).
(* ---- row 0: 0x81594 .. the bcmp call at 0x815b8 ---- *)
paj_run_tok RUN HS HJ SHOK Bspan_E; [awr_ok_tac |].
e_keep_step.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
eapply SRr_bind;
[ apply (e_bcmp_call g pos mf ly2 S2 W2 mm mdq _ rg 0 0xeb0 HJ HFR HPRE Hmfb Hmf32);
  [ lia | lia | reflexivity
  | rewrite Q10, E33, (unsigned_lit_small (SFa g pos)) by lia; unfold w64, V_hw; f_equal; lia
  | rewrite Q11; change 247%nat with (A_OBJ 6); rewrite E6, (unsigned_lit_small (VAL (A_OBJ 6))) by lia;
    unfold w64; f_equal; lia
  | exact Q12 | exact Q1
  | rewrite Q2, (EEo 2%nat 2%bv eq_refl); exact Rsp
  | rewrite Q3, (EEo 3%nat 3%bv eq_refl); exact Rgp
  | rewrite Q4, (EEo 4%nat 4%bv eq_refl); exact Rtp
  | exact (e_tr_hw g pos W2 mem2 mm mf (m_nrec g) HK Hmf0 HF4096 HFceil Hhw) ]
| ] end.
clear Q10 Q11 Q12 Q1 Q2 Q3 Q4.
cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & v0 & -> & HJ4 & HP4 & Hv0 & Hc0 & HK4).
change (Z.to_nat 0) with 0%nat in Hc0.
lazymatch goal with HS : st_ok _ _ ?ssx _ |- _ =>
let K := eval vm_compute in (run_K A_LIM Bx_E e_SHT ssx) in
jafter_call_keep_hi HS K regs4 (mrestrict (w_H W2) mem4) HP4 [0;1;2]%nat HS4 end.
match type of HS4 with ?Q -> _ => assert (HQ : Q); [ | specialize (HS4 HQ); clear HQ ] end.
{ e_kept U9 U33 U6 HK4 Hmfp Hmf0. }
clear HS. rewrite <- restrict_mkst_fx in HS4. rename HS4 into HS.
pose proof (e_keep_trans _ _ _ _ _ HK HK4) as HKn. clear HK HK4. rename HKn into HK.
clear HJ SHOK. rename HJ4 into HJ.
e_shok E32.
psrr_branch_tok RUN BR HS SHOK Bspan_E.
{ (* row 0 matches: r = 1 *)
  assert (Hm : map bv_unsigned (m_hwb g (m_nrec g)) = SlotModel.HWT 0).
  { apply Hc0. lazymatch type of Hc with branch_taken BC_EQ (sv_denot ?Ev (SOff ?n 0)) _ = true =>
    apply (e_br_eq0 Ev n v0); [e_hv Hv0 | exact Hc] end. }
  clear Hc.
  assert (HF1 : SlotModel.FAM (m_id g (m_nrec g)) = 1)
  by (rewrite HFc, (e_fam_cmp_hit _ 0%nat ltac:(lia) Hm); reflexivity).
  paj_run_to_tok RUNTO HS HJ SHOK Bspan_E 0xeec; [awr_ok_tac |].
  e_keep_step.
  psrr_branch_tok RUN BR HS SHOK Bspan_E.
  - exfalso.
    lazymatch type of Hc with branch_taken BC_NE (sv_denot ?Ev (SOff ?n 0)) (sv_denot _ (SLit ?c)) = true =>
    destruct (e_br_val Ev n (SlotModel.FAM (m_id g (m_nrec g))) c ltac:(e_hv R10f) ltac:(lia) ltac:(lia)) as [_ Hb] end.
    rewrite Hb, HF1 in Hc. discriminate Hc.
  - clear Hc. paj_run_to_tok RUNTO HS HJ SHOK Bspan_E 0xeec; [awr_ok_tac |]. e_keep_step.
    e_fin g pos mf ly2 S2 W2 regs2 mem2 md2 HFR Hk MLE MOK HEC Hcur Hid Hhw Hbl Vid3 Vid184 HAE E32. }
(* row 0 misses *)
assert (Hn0 : map bv_unsigned (m_hwb g (m_nrec g)) <> SlotModel.HWT 0).
{ intros Hrow. lazymatch type of Hc with branch_taken BC_EQ (sv_denot ?Ev (SOff ?n 0)) _ = false =>
  apply (e_br_ne0 Ev n v0); [e_hv Hv0 | exact Hc | apply Hc0; exact Hrow] end. }
clear Hc Hc0 Hv0.
(* ---- row 1 ---- *)
paj_run_tok RUN HS HJ SHOK Bspan_E; [awr_ok_tac |].
e_keep_step.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
eapply SRr_bind;
[ apply (e_bcmp_call g pos mf ly2 S2 W2 mm mdq _ rg 1 0xeb0 HJ HFR HPRE Hmfb Hmf32);
  [ lia | lia | reflexivity
  | rewrite Q10, E33, (unsigned_lit_small (SFa g pos)) by lia; unfold w64, V_hw; f_equal; lia
  | rewrite Q11; change 247%nat with (A_OBJ 6); rewrite E6, (unsigned_lit_small (VAL (A_OBJ 6))) by lia;
    unfold w64; f_equal; lia
  | exact Q12 | exact Q1
  | rewrite Q2, (EEo 2%nat 2%bv eq_refl); exact Rsp
  | rewrite Q3, (EEo 3%nat 3%bv eq_refl); exact Rgp
  | rewrite Q4, (EEo 4%nat 4%bv eq_refl); exact Rtp
  | exact (e_tr_hw g pos W2 mem2 mm mf (m_nrec g) HK Hmf0 HF4096 HFceil Hhw) ]
| ] end.
clear Q10 Q11 Q12 Q1 Q2 Q3 Q4.
cbv beta. intros W5 c5 _ (-> & regs5 & mem5 & md5 & v1 & -> & HJ5 & HP5 & Hv1 & Hc1 & HK5).
change (Z.to_nat 1) with 1%nat in Hc1.
lazymatch goal with HS : st_ok _ _ ?ssx _ |- _ =>
let K := eval vm_compute in (run_K A_LIM Bx_E e_SHT ssx) in
jafter_call_keep_hi HS K regs5 (mrestrict (w_H W2) mem5) HP5 [0;1;2]%nat HS5 end.
match type of HS5 with ?Q -> _ => assert (HQ : Q); [ | specialize (HS5 HQ); clear HQ ] end.
{ e_kept U9 U33 U6 HK5 Hmfp Hmf0. }
clear HS. rewrite <- restrict_mkst_fx in HS5. rename HS5 into HS.
pose proof (e_keep_trans _ _ _ _ _ HK HK5) as HKn. clear HK HK5. rename HKn into HK.
clear HJ SHOK. rename HJ5 into HJ.
e_shok E32.
psrr_branch_tok RUN BR HS SHOK Bspan_E.
{ (* row 1 matches: r = 2 *)
  assert (Hm : map bv_unsigned (m_hwb g (m_nrec g)) = SlotModel.HWT 1).
  { apply Hc1. lazymatch type of Hc with branch_taken BC_EQ (sv_denot ?Ev (SOff ?n 0)) _ = true =>
    apply (e_br_eq0 Ev n v1); [e_hv Hv1 | exact Hc] end. }
  clear Hc.
  assert (HF2 : SlotModel.FAM (m_id g (m_nrec g)) = 2)
  by (rewrite HFc, (e_fam_cmp_hit _ 1%nat ltac:(lia) Hm); reflexivity).
  paj_run_to_tok RUNTO HS HJ SHOK Bspan_E 0xeec; [awr_ok_tac |].
  e_keep_step.
  psrr_branch_tok RUN BR HS SHOK Bspan_E.
  - exfalso.
    lazymatch type of Hc with branch_taken BC_NE (sv_denot ?Ev (SOff ?n 0)) (sv_denot _ (SLit ?c)) = true =>
    destruct (e_br_val Ev n (SlotModel.FAM (m_id g (m_nrec g))) c ltac:(e_hv R10f) ltac:(lia) ltac:(lia)) as [_ Hb] end.
    rewrite Hb, HF2 in Hc. discriminate Hc.
  - clear Hc. paj_run_to_tok RUNTO HS HJ SHOK Bspan_E 0xeec; [awr_ok_tac |]. e_keep_step.
    e_fin g pos mf ly2 S2 W2 regs2 mem2 md2 HFR Hk MLE MOK HEC Hcur Hid Hhw Hbl Vid3 Vid184 HAE E32. }
(* row 1 misses *)
assert (Hn1 : map bv_unsigned (m_hwb g (m_nrec g)) <> SlotModel.HWT 1).
{ intros Hrow. lazymatch type of Hc with branch_taken BC_EQ (sv_denot ?Ev (SOff ?n 0)) _ = false =>
  apply (e_br_ne0 Ev n v1); [e_hv Hv1 | exact Hc | apply Hc1; exact Hrow] end. }
clear Hc Hc1 Hv1.
(* ---- row 2 ---- *)
paj_run_tok RUN HS HJ SHOK Bspan_E; [awr_ok_tac |].
e_keep_step.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
eapply SRr_bind;
[ apply (e_bcmp_call g pos mf ly2 S2 W2 mm mdq _ rg 2 0xeb0 HJ HFR HPRE Hmfb Hmf32);
  [ lia | lia | reflexivity
  | rewrite Q10, E33, (unsigned_lit_small (SFa g pos)) by lia; unfold w64, V_hw; f_equal; lia
  | rewrite Q11; change 247%nat with (A_OBJ 6); rewrite E6, (unsigned_lit_small (VAL (A_OBJ 6))) by lia;
    unfold w64; f_equal; lia
  | exact Q12 | exact Q1
  | rewrite Q2, (EEo 2%nat 2%bv eq_refl); exact Rsp
  | rewrite Q3, (EEo 3%nat 3%bv eq_refl); exact Rgp
  | rewrite Q4, (EEo 4%nat 4%bv eq_refl); exact Rtp
  | exact (e_tr_hw g pos W2 mem2 mm mf (m_nrec g) HK Hmf0 HF4096 HFceil Hhw) ]
| ] end.
clear Q10 Q11 Q12 Q1 Q2 Q3 Q4.
cbv beta. intros W6 c6 _ (-> & regs6 & mem6 & md6 & v2 & -> & HJ6 & HP6 & Hv2 & Hc2 & HK6).
change (Z.to_nat 2) with 2%nat in Hc2.
lazymatch goal with HS : st_ok _ _ ?ssx _ |- _ =>
let K := eval vm_compute in (run_K A_LIM Bx_E e_SHT ssx) in
jafter_call_keep_hi HS K regs6 (mrestrict (w_H W2) mem6) HP6 [0;1;2]%nat HS6 end.
match type of HS6 with ?Q -> _ => assert (HQ : Q); [ | specialize (HS6 HQ); clear HQ ] end.
{ e_kept U9 U33 U6 HK6 Hmfp Hmf0. }
clear HS. rewrite <- restrict_mkst_fx in HS6. rename HS6 into HS.
pose proof (e_keep_trans _ _ _ _ _ HK HK6) as HKn. clear HK HK6. rename HKn into HK.
clear HJ SHOK. rename HJ6 into HJ.
e_shok E32.
psrr_branch_tok RUN BR HS SHOK Bspan_E.
{ (* row 2 matches: r = 3 *)
  assert (Hm : map bv_unsigned (m_hwb g (m_nrec g)) = SlotModel.HWT 2).
  { apply Hc2. lazymatch type of Hc with branch_taken BC_EQ (sv_denot ?Ev (SOff ?n 0)) _ = true =>
    apply (e_br_eq0 Ev n v2); [e_hv Hv2 | exact Hc] end. }
  clear Hc.
  assert (HF3 : SlotModel.FAM (m_id g (m_nrec g)) = 3)
  by (rewrite HFc, (e_fam_cmp_hit _ 2%nat ltac:(lia) Hm); reflexivity).
  paj_run_to_tok RUNTO HS HJ SHOK Bspan_E 0xeec; [awr_ok_tac |].
  e_keep_step.
  psrr_branch_tok RUN BR HS SHOK Bspan_E.
  - exfalso.
    lazymatch type of Hc with branch_taken BC_NE (sv_denot ?Ev (SOff ?n 0)) (sv_denot _ (SLit ?c)) = true =>
    destruct (e_br_val Ev n (SlotModel.FAM (m_id g (m_nrec g))) c ltac:(e_hv R10f) ltac:(lia) ltac:(lia)) as [_ Hb] end.
    rewrite Hb, HF3 in Hc. discriminate Hc.
  - clear Hc. paj_run_to_tok RUNTO HS HJ SHOK Bspan_E 0xeec; [awr_ok_tac |]. e_keep_step.
    e_fin g pos mf ly2 S2 W2 regs2 mem2 md2 HFR Hk MLE MOK HEC Hcur Hid Hhw Hbl Vid3 Vid184 HAE E32. }
(* no row matches: 0x815cc, and 0x815d0 beqz s6 needs r = 0 = fam_cmp hw.raw *)
assert (Hn2 : map bv_unsigned (m_hwb g (m_nrec g)) <> SlotModel.HWT 2).
{ intros Hrow. lazymatch type of Hc with branch_taken BC_EQ (sv_denot ?Ev (SOff ?n 0)) _ = false =>
  apply (e_br_ne0 Ev n v2); [e_hv Hv2 | exact Hc | apply Hc2; exact Hrow] end. }
clear Hc Hc2 Hv2.
assert (HF0 : SlotModel.FAM (m_id g (m_nrec g)) = 0) by (rewrite HFc; exact (e_fam_cmp_miss _ Hn0 Hn1 Hn2)).
paj_run_to_tok RUNTO HS HJ SHOK Bspan_E 0xeec; [awr_ok_tac |].
e_keep_step.
psrr_branch_tok RUN BR HS SHOK Bspan_E.
- clear Hc. paj_run_to_tok RUNTO HS HJ SHOK Bspan_E 0xeec; [awr_ok_tac |]. e_keep_step.
  e_fin g pos mf ly2 S2 W2 regs2 mem2 md2 HFR Hk MLE MOK HEC Hcur Hid Hhw Hbl Vid3 Vid184 HAE E32.
- exfalso.
  lazymatch type of Hc with branch_taken BC_EQ (sv_denot ?Ev (SOff ?n 0)) (sv_denot _ (SLit 0)) = false =>
  destruct (e_br_val Ev n (SlotModel.FAM (m_id g (m_nrec g))) 0 ltac:(e_hv R10f) ltac:(lia) ltac:(lia)) as [Hb _] end.
  rewrite Hb, HF0 in Hc. discriminate Hc.
Qed.

End c.
End b.
End a.
