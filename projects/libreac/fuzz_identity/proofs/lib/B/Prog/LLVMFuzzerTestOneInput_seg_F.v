(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-366, for
   libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_H.v, with its module paths and module names changed; 670 of its 748 lines of code are new or changed and 1065 lines of the source are left out. *)
(* Segment F of LLVMFuzzerTestOneInput's ASan+UBSan walk (fuzz_identity.asan-ubsan), seg_F of
   lib/B/Prog/LLVMFuzzerTestOneInput_inv.v: +0x1080 .. +0x1128 (0x817f4 .. 0x8189c) and the out-of-line block
   +0x1cd4 .. +0x1e98 (0x82448 .. 0x8260c), from inv_E_end to inv_F_end, the slot of the first buf_of call.

   The code reads the ten tail bytes of the input at x25 = p + c while x24 = n - c bytes are left: byte 0 into
   x27, byte 1 into mf+176, byte 2 into mf+160, byte 3 mod 16 into x18 and x10, byte 4 mod 32 into x22, bytes
   5 and 6 mod 40 into x26 and x21 (through (b * 205) >> 13), byte 7 mod 64 into mf+120, byte 8 into mf+112,
   and bytes 9 and 10 into x24 = b9 | b10 << 8. Once the input is exhausted every later value is 0 (the
   branches on x24 at 0x817f4, 0x8181c, 0x81860, 0x81c24 and in the block 0x82448 .. 0x8260c). Each read is
   preceded by the UBSan pointer-overflow check of its address (the trap at 0x82610) and the ASan shadow check
   (the partial-granule re-checks at 0x82634 .. 0x82710). x25 ends as &ef (0x8188c).

   The walk splits on the bytes left, r = n - c: r = 0 .. 10 (x24 pinned to r) and r >= 11. In each case one
   run of the token engine (IdentBPaLib.paj_run_to_tok) covers the segment: the branches on x24 are decided by
   the pinned value or its range, the overflow checks by the range of x25 (inside a heap block), and the
   shadow checks by one shadow entry for the first min r 11 bytes of the input block (the block's shadow,
   YCbq.range_addressable_of_block), so the run leaves no shadow obligation. f_entry builds the symbolic
   state, f_keep / f_slot read the final one, and f_post turns it into inv_F_end. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentBase IdentRo YC4b YC81.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBFrame IdentBCJ IdentBProgSig YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel IdentSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* ---- the symbolic state at +0x1080 ---- *)
Definition f_mA : YP09.region := YP09.mkRegion (Some 9%nat) 64 72 64 64 [YP09.mkChunk 64 (CVal 8 (SOff 32 0))].
Definition f_mB : YP09.region := YP09.mkRegion (Some 9%nat) 112 128 112 128 [].
Definition f_mC : YP09.region := YP09.mkRegion (Some 9%nat) 160 168 160 168 [].
Definition f_mD : YP09.region := YP09.mkRegion (Some 9%nat) 176 184 176 184 [].
Definition f_in (m : nat) : YP09.region :=
  YP09.mkRegion (Some 25%nat) 0 (Z.of_nat m) 0 0
    (map (fun j => YP09.mkChunk (Z.of_nat j) (CVal 1 (SOff (33 + j) 0))) (seq 0 m)).
Definition f_mem (m : nat) : smem :=
  [f_mA; f_mB; f_mC; f_mD] ++ match m with O => [] | S _ => [f_in m] end.
Definition f_fix : list (nat * afact) := [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (14%nat, mkAF SB SB 0)].
Definition f_f24 (pin : bool) (r : Z) : list (nat * afact) :=
  [(24%nat, if pin then mkAF r r 0 else mkAF 11 (2 ^ 26) 0)].
Definition f_f25 (m : nat) : list (nat * afact) :=
  match m with O => [] | S _ => [(25%nat, mkAF 4096 0x7fffff800000 0)] end.
Definition f_fby : list (nat * afact) := map (fun j => ((33 + j)%nat, mkAF 0 255 0)) (seq 0 11).
Definition f_facts (m : nat) (pin : bool) (r : Z) : facts := mkFacts (f_fix ++ f_f24 pin r ++ f_f25 m ++ f_fby) [] [].
Definition f_Bx : sv := SOff 14 0.
Definition f_SH (m : nat) : list shent := match m with O => [] | S _ => [mkSHE 25 0 (Z.of_nat m)] end.
Definition f_ss0 (m : nat) (pin : bool) (r : Z) : sstate := mkSS 0x1080 sr_atoms (f_mem m) None (f_facts m pin r).
Definition f_ss (m : nat) (pin : bool) (r : Z) : sstate :=
  mkSS 0x1080 (if pin then sr_set sr_atoms 24 (SLit r) else sr_atoms) (f_mem m) None (f_facts m pin r).
Definition f_extra (SF : Z) (inp : list byte) : list word :=
  Z_to_bv 64 SF :: map (fun j => Z_to_bv 64 (SlotModel.tb inp (Z.of_nat j))) (seq 0 11).
Definition f_win (mf a : Z) : Prop := mf + 112 <= a < mf + 128 \/ mf + 160 <= a < mf + 168 \/ mf + 176 <= a < mf + 184.

(* ---- the model ---- *)
Lemma f_tb_past : forall inp j, SlotModel.nlen inp <= SlotModel.cT inp + j -> SlotModel.tb inp j = 0.
Proof.
intros inp j H. unfold SlotModel.tb, SlotModel.inb, RcIdentModel.nthb. unfold SlotModel.nlen in H.
rewrite nth_overflow by lia. reflexivity.
Qed.
Lemma f_tb_range : forall inp j, 0 <= SlotModel.tb inp j < 256.
Proof. intros. unfold SlotModel.tb. apply SlotModel.inb_range. Qed.
Lemma f_mod40 : forall b, 0 <= b < 256 -> b - Z.shiftr (b * 205) 13 * 40 = b mod 40.
Proof.
intros b Hb.
pose proof (IdentSpec.z_all_spec (fun x => (x - Z.shiftr (x * 205) 13 * 40) =? x mod 40) 256 0
  ltac:(vm_compute; reflexivity) b ltac:(lia)) as H.
cbv beta in H. apply Z.eqb_eq in H. exact H.
Qed.
Lemma f_lor_shl8 : forall x y, 0 <= x -> 0 <= y < 256 -> Z.lor (Z.shiftl x 8) y = x * 256 + y.
Proof.
intros x y Hx Hy.
assert (Lg : Z.log2 y < 8).
{ destruct (Z.eq_dec y 0) as [->|Hy0]; [cbn; lia|]. apply Z.log2_lt_pow2; lia. }
assert (L : Z.land (Z.shiftl x 8) y = 0).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i 8).
  - rewrite Z.shiftl_spec_low by lia. reflexivity.
  - rewrite (Z.bits_above_log2 y i) by lia. apply andb_false_r. }
rewrite <- Z.lxor_lor by exact L. rewrite <- Z.add_nocarry_lxor by exact L.
rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.

(* ---- the values the run leaves in registers and slots ---- *)
Lemma f_dn_lit0 : forall E v, v = 0 -> sv_denot E (SLit 0) = w64 v.
Proof. intros E v ->. reflexivity. Qed.
Lemma f_dn_atom : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = w64 v.
Proof. intros E n v H Hv. rewrite denot_lit_U, (U_atom E n v H Hv). reflexivity. Qed.
Lemma f_dn_and : forall E n b m, ew E n = Z_to_bv 64 b -> 0 <= b < 256 -> 0 <= m < 2 ^ 64 ->
  sv_denot E (SAlu ALU_AND (SOff n 0) (SLit m)) = w64 (Z.land b m).
Proof. intros E n b m H Hb Hm. rewrite denot_lit_U, (U_and_lit E _ m Hm), (U_atom E n b H) by lia. reflexivity. Qed.
Lemma f_dn_and0 : forall E n b, ew E n = Z_to_bv 64 b -> 0 <= b < 256 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_AND (SOff n 0) (SLit 15)) (SLit 0)) = w64 (Z.land b 15).
Proof.
intros E n b H Hb. rewrite denot_lit_U, U_SAlu, (U_and_lit E _ 15) by lia. rewrite (U_atom E n b H) by lia.
rewrite U_SLit. cbn [zalu_raw]. pose proof (Z.land_nonneg b 15). pose proof (Z_land_upper b 15 ltac:(lia)).
rewrite (zcanon_id 0), Z.add_0_r, zcanon_id by (unfold M64; lia). reflexivity.
Qed.
Lemma f_dn_mod40 : forall E n b, ew E n = Z_to_bv 64 b -> 0 <= b < 256 ->
  sv_denot E (SAlu ALU_SUB (SOff n 0)
    (SMd M_MUL (SAlu ALU_SRL (SMd M_MUL (SOff n 0) (SLit 205)) (SLit 13)) (SLit 40))) = w64 (b mod 40).
Proof.
intros E n b H Hb. rewrite denot_lit_U. unfold w64. f_equal.
rewrite U_SAlu, !U_SMd, U_SAlu, U_SMd, !U_SLit, (U_atom E n b H) by lia. cbn [zalu_raw zmd_raw].
rewrite (zcanon_id 205), (zcanon_id 13), (zcanon_id 40) by (unfold M64; lia).
change (Z.land 13 63) with 13.
rewrite (zcanon_id (b * 205)) by (unfold M64; lia).
assert (Q : 0 <= Z.shiftr (b * 205) 13 < 7).
{ rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 13) with 8192. split; [apply Z.div_pos; lia|].
  apply Z.div_lt_upper_bound; lia. }
rewrite (zcanon_id (Z.shiftr (b * 205) 13)) by (unfold M64; lia).
rewrite (zcanon_id (Z.shiftr (b * 205) 13 * 40)) by (unfold M64; lia).
rewrite f_mod40 by exact Hb. apply zcanon_id. pose proof (Z.mod_pos_bound b 40). unfold M64. lia.
Qed.
Lemma f_dn_or : forall E n9 n10 b9 b10, ew E n9 = Z_to_bv 64 b9 -> ew E n10 = Z_to_bv 64 b10 ->
  0 <= b9 < 256 -> 0 <= b10 < 256 ->
  sv_denot E (SAlu ALU_OR (SAlu ALU_SLL (SOff n10 0) (SLit 8)) (SOff n9 0)) = w64 (b9 + 256 * b10).
Proof.
intros E n9 n10 b9 b10 H9 H10 R9 R10. rewrite denot_lit_U. unfold w64. f_equal.
rewrite !U_SAlu, U_SLit, (U_atom E n9 b9 H9), (U_atom E n10 b10 H10) by lia. cbn [zalu_raw].
rewrite (zcanon_id 8) by (unfold M64; lia). change (Z.land 8 63) with 8.
rewrite (zcanon_id (Z.shiftl b10 8)) by (rewrite Z.shiftl_mul_pow2 by lia; unfold M64; lia).
rewrite f_lor_shl8 by lia. rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma f_dn_or0 : forall E n9 b9 c, ew E n9 = Z_to_bv 64 b9 -> 0 <= b9 < 256 -> c = 0 ->
  sv_denot E (SAlu ALU_OR (SLit 0) (SOff n9 0)) = w64 (b9 + 256 * c).
Proof.
intros E n9 b9 c H9 R9 ->. rewrite denot_lit_U. unfold w64. f_equal.
rewrite U_SAlu, U_SLit, (U_atom E n9 b9 H9) by lia. cbn [zalu_raw]. rewrite Z.lor_0_l.
rewrite !zcanon_id by (unfold M64; lia). lia.
Qed.

(* ---- the symbolic state's shape ---- *)
Lemma f_in_wf : forall m, region_wf (f_in m) = true.
Proof.
intros m. unfold region_wf, f_in. cbn [YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
apply andb_true_intro; split; [apply andb_true_intro; split; [apply Z.leb_le; lia | reflexivity]|].
apply forallb_forall. intros c Hc. apply in_map_iff in Hc as (j & <- & Hj). apply in_seq in Hj.
unfold chunk_inside, c_len, cv_len. cbn [YP09.r_lo YP09.r_hi YP09.c_off YP09.c_val].
apply andb_true_intro; split; [apply andb_true_intro; split|]; apply Z.leb_le; lia.
Qed.
Lemma f_mem_wf : forall m, regions_wf (f_mem m) = true.
Proof. intros [|m]; [vm_compute; reflexivity|]. unfold f_mem. cbn [app regions_wf]. rewrite f_in_wf. reflexivity. Qed.
Lemma f_atoms_app : forall E l1 l2, atoms_ok E l1 -> atoms_ok E l2 -> atoms_ok E (l1 ++ l2).
Proof.
intros E l1 l2 H1 H2. induction l1 as [|[n f] l IH]; cbn [app atoms_ok] in *; [exact H2|].
destruct H1 as [Ha Hl]. split; [exact Ha | exact (IH Hl)].
Qed.
Lemma f_atoms_fby : forall E, (forall j, (j < 11)%nat -> 0 <= bv_unsigned (ew E (33 + j)) <= 255) -> atoms_ok E f_fby.
Proof.
intros E H. unfold f_fby.
assert (G : forall l, (forall j, In j l -> (j < 11)%nat) ->
  atoms_ok E (map (fun j => ((33 + j)%nat, mkAF 0 255 0)) l)).
{ induction l as [|j l IH]; intros Hl; cbn [map atoms_ok]; [exact I|]. split.
  - unfold afact_ok; cbn [af_lo af_hi af_al2]. rewrite Z.pow_0_r, Z.mod_1_r.
    pose proof (H j (Hl j (or_introl eq_refl))). lia.
  - apply IH. intros j' Hj'. apply Hl. right. exact Hj'. }
apply G. intros j Hj. apply in_seq in Hj. lia.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation VAL := (@pa_val _ identb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).

Lemma f_E_tb : forall regs SF inp j, (j < 11)%nat ->
  ew (Eimg (Ereg regs (f_extra SF inp))) (33 + j) = Z_to_bv 64 (SlotModel.tb inp (Z.of_nat j)).
Proof.
intros regs SF inp j Hj. rewrite Eimg_low by (unfold A_TEXT; lia).
replace (33 + j)%nat with (32 + S j)%nat by lia. rewrite ew_Ereg_extra. unfold f_extra.
do 11 (destruct j as [|j]; [reflexivity|]). lia.
Qed.
Lemma f_E_SF : forall regs SF inp, ew (Eimg (Ereg regs (f_extra SF inp))) 32 = Z_to_bv 64 SF.
Proof. intros regs SF inp. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). Qed.
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
(* What this segment needs, each as the contract's Section states it. *)
Hypothesis HSTK : STK_LLVMF <= LLVMF_STK.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis AJ_NIL_IO : forall STK sp0 ly S (W : world SEGS) mem md own ly' S' W' mem' md' k,
  ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
  m_fds md' = m_fds md /\ m_fs md' = m_fs md.
#[local] Notation ECOM := (ecommon B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation INV_E := (inv_E_end B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation INV_F := (inv_F_end B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation JE g pos := (ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g)
  [(4, pos)]).

(* The cursor and the bytes left, from the model: 0 <= cT <= n. *)
Lemma f_cT_range : forall (g : ectx), e_n g = Z.of_nat (length (e_pl g)) ->
  0 <= SlotModel.cT (e_pl g) <= e_n g.
Proof.
intros g Hn. pose proof (SlotModel.rec_c_range (e_pl g) (SlotModel.nrecn (e_pl g))) as H.
unfold SlotModel.cT, SlotModel.nlen in *. lia.
Qed.

(* The entry of the run at +0x1080: the symbolic state and its shadow entry. *)
Lemma f_entry : forall (g : ectx) pos mf (W2 : world SEGS) ly2 S2 regs2 mem2 md2 k (m : nat) (pin : bool) (r : Z),
  JE g pos ly2 S2 W2 mem2 md2 k ->
  ECOM g pos mf ly2 S2 W2 regs2 mem2 md2 -> hblocks B g ly2 S2 [] ->
  getr regs2 25 = w64 (e_p g + SlotModel.cT (e_pl g)) ->
  getr regs2 24 = w64 (e_n g - SlotModel.cT (e_pl g)) ->
  getr regs2 14 = w64 SHADOW_OFF ->
  Z.of_nat m = Z.min (e_n g - SlotModel.cT (e_pl g)) 11 ->
  (if pin then e_n g - SlotModel.cT (e_pl g) = r else 11 <= e_n g - SlotModel.cT (e_pl g)) ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs2 (f_extra (SFa g pos) (e_pl g)))) (f_ss m pin r)
    (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x1080)) mem2 (seg_rom SEGS))) /\
  sh_ok SEGS f_Bx (f_SH m) (Eimg (Ereg regs2 (f_extra (SFa g pos) (e_pl g)))) (mrestrict (w_H W2) mem2).
Proof.
intros g pos mf W2 ly2 S2 regs2 mem2 md2 k m pin r HJ HC Hbl R25 R24 R14 Hm Hpin.
destruct HC as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & V16 & V64 & V192 & V168 & Vra & Vs0 &
  V24 & V32 & V40 & V48 & V56 & V64b & V72 & V80 & V88 & V96 & V104 & Vflag & HPRE & Hfds & Hfs & Hinb).
pose proof HPRE as (_ & _ & _ & _ & Hinp & Hlen & _).
pose proof HJ as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstatic & _).
pose proof Hstatic as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
assert (Has : ASTACK = 16384) by reflexivity.
pose proof HSTK as HSTK'. unfold STK_LLVMF in HSTK'.
set (sp0 := e_sp0 g) in *.
assert (Hmf0 : alloc_ceiling + 16384 <= mf /\ mf + 320 <= sp0 /\ sp0 <= 2 ^ 47)
  by (clear - Hmfb Hceil Hslo Hshi H47 HSTK' Has; lia).
set (inp := e_pl g) in *. set (p := e_p g) in *. set (n := e_n g) in *.
set (cT := SlotModel.cT inp) in *.
assert (HcT : 0 <= cT <= n) by (exact (f_cT_range g Hlen)).
assert (Hn26 : 0 <= n < 2 ^ 26) by (clear - Hinp; destruct Hinp as [[H0 _] | [H0 _]]; lia).
set (E := Eimg (Ereg regs2 (f_extra (SFa g pos) inp))).
assert (EE : forall nn (rr : bv 5), Z.of_nat nn = bv_unsigned rr -> ew E nn = getr regs2 rr)
  by (intros nn rr Hn; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U9 : bv_unsigned (ew E 9) = mf).
{ rewrite (EE 9%nat 9%bv eq_refl), Rs1. apply unsigned_lit_small. clear - Hmf0 C1. lia. }
assert (U14 : ew E 14 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 14%nat 14%bv eq_refl), R14; reflexivity).
assert (U24 : ew E 24 = Z_to_bv 64 (n - cT)) by (rewrite (EE 24%nat 24%bv eq_refl), R24; reflexivity).
assert (U25 : ew E 25 = Z_to_bv 64 (p + cT)) by (rewrite (EE 25%nat 25%bv eq_refl), R25; reflexivity).
assert (U32 : ew E 32 = Z_to_bv 64 (SFa g pos)) by exact (f_E_SF regs2 (SFa g pos) inp).
assert (UB : forall j, (j < 11)%nat -> ew E (33 + j) = Z_to_bv 64 (SlotModel.tb inp (Z.of_nat j)))
  by (intros j Hj; exact (f_E_tb regs2 (SFa g pos) inp j Hj)).
(* the input block, when the run reads it *)
assert (Hblk : (0 < m)%nat -> In (p, n) (ablocks B ly2 S2) /\ 0 < n < 2 ^ 26).
{ intros Hm0. destruct Hinp as [[Hn0 _] | [Hn Hin]]; [exfalso; clear - Hm Hm0 Hn0 HcT; lia|].
  split; [|exact Hn]. destruct Hbl as [Hperm _]. apply (Permutation_in _ (Permutation_sym Hperm)). exact Hin. }
assert (HS0 : st_ok_pi SEGS VAL E (f_ss0 m pin r)
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x1080)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold f_ss0. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - apply f_mem_wf.
  - assert (RW : forall lo hi, 112 <= lo -> hi <= 184 ->
      region_ok SEGS E (mrestrict (w_H W2) mem2) (YP09.mkRegion (Some 9%nat) lo hi lo hi [])).
    { intros lo hi Hlo Hhi. unfold region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
      split; [clear - Hmf0 C1 Hlo; lia|]. split; [clear - Hmf0 Hhi; lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. clear - Hmf0 Ho Hlo Hhi HSTK' Has Hmfb.
      unfold sp0 in *. lia. }
    unfold f_mem. apply Forall_app. split.
    + constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
      * unfold f_mA, region_ok.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
        split; [clear - Hmf0 C1; lia|]. split; [clear - Hmf0; lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val SEGS E _ mf 64 8 (SOff 32 0) (SFa g pos)).
        -- cbn [sv_denot]. rewrite U32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
        -- pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 (SFa g pos))) as Hr.
           assert (HSF : exists ly S W mm md, AR SEGS B ly S W mm md /\ In (4, pos) (frames S) /\
             frame_addr ly 4 pos = SFa g pos).
           { exists ly2, S2, W2, mem2, md2. split; [exact HAR2|].
             pose proof HJ as (_ & Hly2 & _ & _ & _ & Hfrs2 & _). split; [rewrite Hfrs2; left; reflexivity|].
             pose proof Hly2 as (_ & _ & _ & _ & _ & EF & _). unfold SFa, frame_addr. rewrite EF. reflexivity. }
           destruct HSF as (ly & S & W & mm & md & HAR & Hin & EFa).
           destruct (frames_bounds SEGS B LAWS ly S W mm md 4 pos HAR Hin) as (HF0 & HF1 & _).
           rewrite EFa in HF0, HF1. change (fs_frame_bytes 4) with 1024 in HF1. clear - HF0 HF1 C1. lia.
        -- lia.
        -- exact V64.
      * apply RW; lia.
      * apply RW; lia.
      * apply RW; lia.
    + destruct m as [|m']; [constructor|]. constructor; [|constructor].
      destruct (Hblk ltac:(lia)) as [Hin Hn].
      destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 p n HAR2 Hin) as (_ & Hp4096 & Hpce & _).
      pose proof (req_size_pos n ltac:(lia)) as Hrq.
      assert (Up : base_val E (Some 25%nat) = p + cT).
      { cbn [base_val]. rewrite U25. apply unsigned_lit_small. clear - Hp4096 Hpce Hrq HcT C1. lia. }
      unfold f_in, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite Up. split; [clear - Hp4096 HcT; lia|]. split; [clear - Hp4096 Hpce Hrq HcT Hm C1; lia|].
      split; [intros o Ho; lia|].
      apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (j & <- & Hj). apply in_seq in Hj.
      apply (chunk_ok_val SEGS E _ (p + cT) (Z.of_nat j) 1 (SOff (33 + j) 0) (SlotModel.tb inp (Z.of_nat j))).
      * cbn [sv_denot]. rewrite UB by lia. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      * pose proof (f_tb_range inp (Z.of_nat j)). change (2 ^ (8 * Z.of_N 1)) with 256. lia.
      * lia.
      * assert (Hj' : (Z.to_nat (cT + Z.of_nat j) < length (map (fun b : byte => bv_unsigned b) inp))%nat)
          by (rewrite length_map; clear - Hm Hj HcT Hlen; unfold n in *; lia).
        destruct (Hinb _ Hj') as [Hv _].
        replace (p + Z.of_nat (Z.to_nat (cT + Z.of_nat j))) with (p + cT + Z.of_nat j) in Hv
          by (clear - HcT; lia).
        replace (SlotModel.tb inp (Z.of_nat j)) with (nth (Z.to_nat (cT + Z.of_nat j)) (map (fun b : byte => bv_unsigned b) inp) 0).
        { exact Hv. }
        unfold SlotModel.tb, SlotModel.inb, RcIdentModel.nthb, RcIdentModel.bz.
        rewrite (nth_indep _ 0 (bv_unsigned (RcIdentModel.zb 0))) by exact Hj'.
        rewrite map_nth. reflexivity.
  - unfold f_mem. destruct m as [|m'].
    + cbn [app pairwise_disjoint all_disjoint]. unfold extent_disjoint, f_mA, f_mB, f_mC, f_mD.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9. clear.
      repeat split; first [left; lia | right; lia].
    + destruct (Hblk ltac:(lia)) as [Hin Hn].
      destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 p n HAR2 Hin) as (_ & Hp4096 & Hpce & _).
      pose proof (req_size_pos n ltac:(lia)) as Hrq.
      assert (Up : bv_unsigned (ew E 25) = p + cT).
      { rewrite U25. apply unsigned_lit_small. clear - Hp4096 Hpce Hrq HcT C1. lia. }
      assert (Hlow : p + cT + Z.of_nat (S m') <= mf + 64) by (clear - Hm Hpce Hrq HcT Hmf0; lia).
      cbn [app pairwise_disjoint all_disjoint]. unfold extent_disjoint, f_mA, f_mB, f_mC, f_mD, f_in.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, Up. clear - Hlow.
      repeat split; first [left; lia | right; lia].
  - unfold facts_ok, f_facts. cbn [f_atoms f_conds f_alias conds_ok alias_ok]. split; [|split; exact I].
    apply f_atoms_app; [|apply f_atoms_app; [|apply f_atoms_app]].
    + unfold f_fix. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U9, U14, unsigned_lit_small by (unfold SHADOW_OFF; lia).
      change (2 ^ 5) with 32. change (2 ^ 0) with 1. rewrite Z.mod_1_r. unfold SB, SHADOW_OFF.
      clear - Hmf0 Hmf32 C1. repeat split; lia.
    + unfold f_f24. cbn [atoms_ok]. split; [|exact I]. unfold afact_ok. rewrite U24.
      rewrite unsigned_lit_small by (clear - HcT Hn26; lia).
      destruct pin; cbn [af_lo af_hi af_al2]; change (2 ^ 0) with 1; rewrite Z.mod_1_r;
      clear - Hpin HcT Hn26; repeat split; lia.
    + unfold f_f25. destruct m as [|m']; cbn [atoms_ok]; [exact I|]. split; [|exact I].
      destruct (Hblk ltac:(lia)) as [Hin Hn].
      destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 p n HAR2 Hin) as (_ & Hp4096 & Hpce & _).
      pose proof (req_size_pos n ltac:(lia)) as Hrq.
      unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U25, unsigned_lit_small by (clear - Hp4096 Hpce Hrq HcT C1; lia).
      change (2 ^ 0) with 1. rewrite Z.mod_1_r. clear - Hp4096 Hpce Hrq HcT C1 Hm. repeat split; lia.
    + apply f_atoms_fby. intros j Hj. rewrite UB by exact Hj.
      pose proof (f_tb_range inp (Z.of_nat j)). rewrite unsigned_lit_small by lia. lia. }
split.
- destruct pin.
  + refine (st_ok_pi_pin_reg' E (f_ss0 m true r) _ 24%bv r HS0 _ eq_refl).
    cbn [restrict ms_regs mkst]. rewrite R24, Hpin. reflexivity.
  + exact HS0.
- destruct m as [|m']; [apply Forall_nil|]. apply Forall_cons; [|apply Forall_nil].
  destruct (Hblk ltac:(lia)) as [Hin Hn].
  destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 p n HAR2 Hin) as (_ & Hp4096 & Hpce & Happ & _).
  pose proof (req_size_pos n ltac:(lia)) as Hrq.
  apply (shent_ok_of_range SEGS (w_H W2) mem2 E f_Bx 25 (p + cT) (Z.of_nat (S m')) (p + cT) 0 (Z.of_nat (S m'))).
  + apply (range_addressable_of_block SEGS B LAWS ly2 S2 W2 mem2 md2 p n); [exact HAR2 | exact Hin | lia |].
    clear - Hm Hrq HcT. lia.
  + unfold f_Bx. apply U_atom; [exact U14 | unfold SHADOW_OFF; lia].
  + apply U_atom; [exact U25 | clear - Hp4096 Hpce Hrq HcT C1; lia].
  + lia.
  + lia.
  + intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *.
    clear - Hx Happ Hm Hrq HcT. lia.
Qed.

(* The run writes only its three machine-frame windows, all inside the stack window. *)
Lemma f_awr : forall E m STK sp0 FP bl0 blc ly own mf,
  bv_unsigned (ew E 9) = mf -> sp0 - STK <= mf + 112 -> mf + 184 <= sp0 ->
  awr_ok E (f_mem m) STK sp0 FP bl0 blc ly own.
Proof.
intros E m STK sp0 FP bl0 blc ly own mf U9 H1 H2.
assert (HW : forall lo hi rs, 112 <= lo -> hi <= 184 -> awr_ok E rs STK sp0 FP bl0 blc ly own ->
  awr_ok E (YP09.mkRegion (Some 9%nat) lo hi lo hi [] :: rs) STK sp0 FP bl0 blc ly own).
{ intros lo hi rs Hlo Hhi Hrs.
  apply (awr_ok_cons_stack_off E (YP09.mkRegion (Some 9%nat) lo hi lo hi []) rs STK sp0 FP bl0 blc ly own 9 (mf - sp0));
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi]; [reflexivity | lia | lia | lia | exact Hrs]. }
unfold f_mem, f_mA, f_mB, f_mC, f_mD. cbn [app].
apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|].
apply HW; [lia|lia|]. apply HW; [lia|lia|]. apply HW; [lia|lia|].
destruct m; [apply awr_ok_nil|]. apply awr_ok_cons_ro; [unfold f_in; cbn [YP09.r_wlo YP09.r_whi]; lia|].
apply awr_ok_nil.
Qed.

(* What the run kept: every byte outside the three windows. *)
Lemma f_keep : forall E m (H : word -> bool) (mem mem' : word -> option byte) mf,
  bv_unsigned (ew E 9) = mf ->
  frame_of E (f_mem m) (mrestrict H mem) (mrestrict H mem') ->
  forall a, 0 <= a < 2 ^ 64 -> ~ f_win mf a -> aview SEGS H mem' a = aview SEGS H mem a.
Proof.
intros E m H mem mem' mf U9 HF a Ha Hw.
apply (kept_of_frame E (f_mem m) H mem mem' (f_win mf) HF); [|exact Ha|exact Hw].
intros b wlo whi x Hin Hx. unfold windows in Hin. apply in_map_iff in Hin as (rg & Eq & Hrg).
injection Eq as <- <- <-. unfold f_mem in Hrg. apply in_app_or in Hrg as [Hrg|Hrg].
- cbn [In] in Hrg. destruct Hrg as [<-|[<-|[<-|[<-|[]]]]]; unfold f_mA, f_mB, f_mC, f_mD in Hx;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx; rewrite U9 in Hx; unfold f_win; lia.
- destruct m; cbn [In] in Hrg; [contradiction|]. destruct Hrg as [<-|[]]. unfold f_in in Hx.
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx. lia.
Qed.

(* A machine-frame slot the run stored: its chunk in the final symbolic state. *)
Lemma f_slot : forall E ss ms (H : word -> bool) i rg off e v mf,
  st_ok_pi SEGS VAL E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some rg ->
  YP09.r_base rg = Some 9%nat -> bv_unsigned (ew E 9) = mf ->
  In (YP09.mkChunk off (CVal 8 e)) (YP09.r_chunks rg) ->
  sv_denot E e = w64 v -> 0 <= v < 2 ^ 64 ->
  val_mem SEGS (mrestrict H (ms_mem ms)) (mf + off) 8 v.
Proof.
intros E ss ms H i rg off e v mf HS Hi Hb U9 Hin He Hv.
pose proof (st_ok_pi_region_nth E ss (restrict H ms) i rg HS Hi) as HR.
unfold region_ok in HR. destruct HR as (_ & _ & _ & Hc). rewrite Hb in Hc. cbn [base_val] in Hc. rewrite U9 in Hc.
rewrite Forall_forall in Hc. specialize (Hc _ Hin).
exact (val_of_chunk_ok SEGS E _ mf off 8 e v Hc He ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(lia)).
Qed.

Lemma f_hwb_length : forall inp i, length (SlotModel.rec_hwb inp i) = 8%nat.
Proof.
intros inp i. unfold SlotModel.rec_hwb.
assert (H : match SlotModel.rec_hw inp i with Some h => length h = 8%nat | None => True end).
{ induction i as [|i IH]; cbn [SlotModel.rec_hw]; [exact I|].
  destruct ((SlotModel.rec_addr inp i =? RcIdentModel.ADDR_REAC_VERSION) && (8 <=? SlotModel.rec_k inp i)) eqn:Hc;
  [|exact IH].
  apply andb_prop in Hc as [_ Hk]. apply Z.leb_le in Hk.
  rewrite length_firstn, SlotModel.rec_pl_length. lia. }
destruct (SlotModel.rec_hw inp i); [exact H | reflexivity].
Qed.

(* The boundary inv_F_end, from what the run did. *)
Lemma f_post : forall (g : ectx) pos mf (W2 : world SEGS) ly2 S2 regs2 mem2 md2 regs3 mem3 md3,
  JE g pos ly2 S2 W2 mem3 md3 (4 * Z.of_nat (m_nrec g)) ->
  frames S2 = [(4, pos)] -> 0 <= 4 * Z.of_nat (m_nrec g) <= EV_LLVMF ->
  mo_le MT (e_S g) S2 (4 * Z.of_nat (m_nrec g) * MEV MT) ->
  mo_ok MT S2 ((EV_LLVMF - 4 * Z.of_nat (m_nrec g)) * MEV MT) ->
  ECOM g pos mf ly2 S2 W2 regs2 mem2 md2 ->
  id_at g pos (m_nrec g) W2 mem2 -> hw_at g pos (m_nrec g) W2 mem2 -> hblocks B g ly2 S2 [] ->
  mf_id3 g pos mf W2 mem2 -> mf_id g pos mf W2 mem2 -> sh_reg g pos regs2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ f_win mf a -> aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) mem2 a) ->
  getr regs3 2 = getr regs2 2 -> getr regs3 9 = getr regs2 9 -> getr regs3 8 = getr regs2 8 ->
  getr regs3 3 = getr regs2 3 -> getr regs3 4 = getr regs2 4 -> getr regs3 23 = getr regs2 23 ->
  getr regs3 25 = w64 (SFa g pos + V_ef) ->
  getr regs3 10 = w64 (Z.land (SlotModel.tb (e_pl g) 3) 15) ->
  getr regs3 18 = w64 (Z.land (SlotModel.tb (e_pl g) 3) 15) ->
  getr regs3 22 = w64 (Z.land (SlotModel.tb (e_pl g) 4) 31) ->
  getr regs3 26 = w64 (SlotModel.tb (e_pl g) 5 mod 40) ->
  getr regs3 21 = w64 (SlotModel.tb (e_pl g) 6 mod 40) ->
  getr regs3 27 = w64 (SlotModel.tb (e_pl g) 0) ->
  getr regs3 24 = w64 (SlotModel.tb (e_pl g) 9 + 256 * SlotModel.tb (e_pl g) 10) ->
  val_mem SEGS (rd W2 mem3) (mf + 176) 8 (SlotModel.tb (e_pl g) 1) ->
  val_mem SEGS (rd W2 mem3) (mf + 160) 8 (SlotModel.tb (e_pl g) 2) ->
  val_mem SEGS (rd W2 mem3) (mf + 120) 8 (Z.land (SlotModel.tb (e_pl g) 7) 63) ->
  val_mem SEGS (rd W2 mem3) (mf + 112) 8 (SlotModel.tb (e_pl g) 8) ->
  INV_F g pos mf W2 (cfg_at SEGS (BASE + 0x1128) regs3 mem3 md3).
Proof.
intros g pos mf W2 ly2 S2 regs2 mem2 md2 regs3 mem3 md3 HJ3 Hfrs Hk MLE MOK HC Hid Hhw Hbl Hid3 Hmid Hsh KEEP
  K2 K9 K8 K3 K4 K23 Q25 Q10 Q18 Q22 Q26 Q21 Q27 Q24 V176 V160 V120 V112.
destruct HC as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & V16 & V64 & V192 & V168 & Vra & Vs0 &
  V24 & V32 & V40 & V48 & V56 & V64b & V72 & V80 & V88 & V96 & V104 & Vflag & HPRE & Hfds & Hfs & Hinb).
pose proof HPRE as (_ & _ & _ & _ & Hinp & Hlen & _).
pose proof HJ3 as (HAR3 & Hly3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
assert (Has : ASTACK = 16384) by reflexivity.
pose proof HSTK as HSTK'. unfold STK_LLVMF in HSTK'.
assert (Hmf0 : alloc_ceiling + 16384 <= mf /\ mf + 320 <= e_sp0 g /\ e_sp0 g <= 2 ^ 47)
  by (clear - Hmfb Hceil Hslo Hshi H47 HSTK' Has; lia).
pose proof Hly3 as (_ & _ & _ & _ & _ & EF & _).
assert (EFa : frame_addr ly2 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF; reflexivity).
assert (Hin4 : In (4, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly2 S2 W2 mem3 md3 4 pos HAR3 Hin4) as (HSF0 & HSF1 & _).
rewrite EFa in HSF0, HSF1. change (fs_frame_bytes 4) with 1024 in HSF1.
destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as [Efd Efs].
assert (VM : forall a (nn : nat) v, 0 <= a -> a + Z.of_nat nn <= 2 ^ 64 ->
  (forall x, a <= x < a + Z.of_nat nn -> ~ f_win mf x) ->
  val_mem SEGS (rd W2 mem2) a nn v -> val_mem SEGS (rd W2 mem3) a nn v).
{ intros a nn v H0 H1 Hw Hv. apply (val_mem_moved SEGS (w_H W2) (w_H W2) mem2 mem3 a a nn v); [|exact Hv].
  intros kk Hkk. apply KEEP; [clear - H0 H1 Hkk; lia | apply Hw; clear - Hkk; lia]. }
assert (GM : forall a l, 0 <= a -> a + Z.of_nat (length l) <= mf + 112 ->
  garr8 SEGS (rd W2 mem2) a l -> garr8 SEGS (rd W2 mem3) a l).
{ intros a l H0 H1 Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
  apply VM; [clear - H0; lia | clear - H1 Hj Hmf0 C1; lia | intros x Hx; unfold f_win; clear - H1 Hj Hx; lia | exact Hv]. }
assert (ZM : forall a nn, 0 <= a -> SHADOW_OFF + a / 8 + nn / 8 <= mf + 112 ->
  sh_zero W2 mem2 a nn -> sh_zero W2 mem3 a nn).
{ intros a nn H0 H1 Hz i Hi. unfold sh_zero, zero_shadow, shadow_of_addr in *.
  rewrite KEEP; [apply Hz; exact Hi | |].
  - assert (0 <= a / 8) by (apply Z.div_pos; lia). unfold SHADOW_OFF in *. clear - H0 H1 Hi Hmf0 C1. lia.
  - unfold f_win. clear - H1 Hi. lia. }
assert (BM : forall a nn, 0 <= a -> SHADOW_OFF + a / 8 + (nn + 7) / 8 <= mf + 112 ->
  sh_blk W2 mem2 a nn -> sh_blk W2 mem3 a nn).
{ intros a nn H0 H1 (Ha8 & Hn0 & Hz). unfold sh_blk, block_shadow in *. split; [exact Ha8|]. split; [exact Hn0|].
  intros i Hi. unfold shadow_of_addr in *. rewrite KEEP; [apply Hz; exact Hi | |].
  - assert (0 <= a / 8) by (apply Z.div_pos; lia). unfold SHADOW_OFF in *. clear - H0 H1 Hi Hmf0 C1. lia.
  - unfold f_win. clear - H1 Hi. lia. }
assert (LO : forall a nn, a + Z.of_nat nn <= mf + 112 -> forall x, a <= x < a + Z.of_nat nn -> ~ f_win mf x)
  by (intros a nn H x Hx; unfold f_win; clear - H Hx; lia).
assert (HI : forall a nn, mf + 184 <= a -> forall x, a <= x < a + Z.of_nat nn -> ~ f_win mf x)
  by (intros a nn H x Hx; unfold f_win; clear - H Hx; lia).
set (SF := SFa g pos) in *.
unfold inv_F_end, acut.
exists ly2, S2, regs3, mem3, md3.
split; [reflexivity|]. split; [exact HJ3|]. split; [exact Hfrs|]. split; [exact Hk|].
split; [exact MLE|]. split; [exact MOK|].
split.
{ unfold ecommon. fold SF.
  split; [rewrite K2; exact Rsp|]. split; [rewrite K9; exact Rs1|]. split; [rewrite K8; exact Rs0|].
  split; [exact Hmfb|]. split; [exact Hmf32|]. split; [rewrite K3; exact Rgp|]. split; [rewrite K4; exact Rtp|].
  split; [apply VM; [clear - Hmf0 C1; lia | clear - Hmf0; lia | apply LO; clear; lia | exact V16]|].
  split; [apply VM; [clear - Hmf0 C1; lia | clear - Hmf0; lia | apply LO; clear; lia | exact V64]|].
  split; [apply VM; [clear - Hmf0 C1; lia | clear - Hmf0; lia | apply HI; clear; lia | exact V192]|].
  split; [apply VM; [clear - Hmf0 C1; lia | clear - Hmf0; lia | intros x Hx; unfold f_win; clear - Hx; lia
    | exact V168]|].
  do 13 (split; [apply VM; [clear - Hmf0 C1; lia | clear - Hmf0; lia | apply HI; clear - Hmf0; lia | assumption]|]).
  split; [apply VM; [clear - HSF0; lia | clear - HSF1 Hmf0 C1; lia | apply LO; clear - HSF1 Hmf0 C1; lia
    | exact Vflag]|].
  split; [exact HPRE|]. split; [intros fd; rewrite Efd; reflexivity|]. split; [exact Efs|].
  unfold bytes_at8 in *. destruct Hinp as [[Hn0 _] | [[Hn0 Hn1] Hin]].
  - assert (Hpl : e_pl g = []) by (destruct (e_pl g); [reflexivity | cbn [length] in Hlen; lia]).
    rewrite Hpl. apply garr8_nil.
  - assert (Hin2 : In (e_p g, e_n g) (ablocks B ly2 S2)).
    { destruct Hbl as [Hperm _]. apply (Permutation_in _ (Permutation_sym Hperm)). exact Hin. }
    destruct (al_blocks _ _ LAWS ly2 S2 W2 mem3 md3 (e_p g) (e_n g) HAR3 Hin2) as (_ & Hp4096 & Hpce & _).
    pose proof (req_size_pos (e_n g) ltac:(lia)) as Hrq.
    apply GM; [clear - Hp4096; lia | rewrite length_map, <- Hlen; clear - Hpce Hrq Hmf0; lia | exact Hinb]. }
unfold id_at, hw_at, hw_mem, mf_id3, mf_id, sh_reg, bytes_at8 in Hid, Hhw, Hid3, Hmid, Hsh |- *.
fold SF in Hid, Hhw, Hid3, Hmid, Hsh |- *.
destruct Hid as (Hidb & Hidz & Hidk). destruct Hhw as ((Hhwb & Hhwz & Hhwk) & Hhv).
assert (HSF8 : SF mod 8 = 0).
{ destruct (frame_al64 SEGS B ly2 S2 W2 mem3 md3 4 pos HAR3 Hin4) as (H64 & _).
  rewrite EFa in H64. fold SF in H64. clear - H64. lia. }
split.
{ split.
  - apply GM; [clear - HSF0; unfold V_id; lia | |exact Hidb].
    rewrite length_map. unfold m_id. rewrite SlotModel.rec_id_length. unfold V_id, RcIdentModel.ID_SIZE.
    clear - HSF1 Hmf0 C1. lia.
  - split.
    + apply ZM; [clear - HSF0; unfold V_id; lia | |exact Hidz].
      unfold V_id, N_id, SHADOW_OFF. clear - HSF0 HSF1 Hmf0 C1. lia.
    + apply BM; [clear - HSF0; unfold V_id; lia | |exact Hidk].
      unfold V_id, N_id, SHADOW_OFF. clear - HSF0 HSF1 Hmf0 C1. lia. }
split.
{ split; [split|].
  - apply GM; [clear - HSF0; unfold V_hw; lia | |exact Hhwb].
    rewrite length_map. unfold m_hwb. rewrite f_hwb_length. unfold V_hw. clear - HSF1 Hmf0 C1. lia.
  - split.
    + apply ZM; [clear - HSF0; unfold V_hw; lia | |exact Hhwz].
      unfold V_hw, N_hw, SHADOW_OFF. clear - HSF0 HSF1 Hmf0 C1. lia.
    + apply BM; [clear - HSF0; unfold V_hw; lia | |exact Hhwk].
      unfold V_hw, N_hw, SHADOW_OFF. clear - HSF0 HSF1 Hmf0 C1. lia.
  - apply VM; [clear - HSF0; unfold V_hw; lia | clear - HSF1 Hmf0 C1; unfold V_hw; lia
    | apply LO; unfold V_hw; clear - HSF1 Hmf0 C1; lia | exact Hhv]. }
split; [exact Hbl|].
split; [apply VM; [clear - Hmf0 C1; lia | clear - Hmf0; lia | intros x Hx; unfold f_win; clear - Hx; lia | exact Hid3]|].
split; [apply VM; [clear - Hmf0 C1; lia | clear - Hmf0; lia | apply HI; clear; lia | exact Hmid]|].
split; [rewrite K23; exact Hsh|].
split; [exact Q25|].
assert (L4 : forall b, Z.land b 15 = b mod 16) by (intros b; change 15 with (Z.ones 4); apply Z.land_ones; lia).
assert (L5 : forall b, Z.land b 31 = b mod 32) by (intros b; change 31 with (Z.ones 5); apply Z.land_ones; lia).
assert (L6 : forall b, Z.land b 63 = b mod 64) by (intros b; change 63 with (Z.ones 6); apply Z.land_ones; lia).
unfold SlotModel.t_cap_fw, SlotModel.t_cap_ver, SlotModel.t_cap_name, SlotModel.t_cap_tok, SlotModel.t_fam_raw,
  SlotModel.t_any_fw, SlotModel.t_in, SlotModel.t_out, SlotModel.t_cap_disp, SlotModel.t_row.
rewrite L4 in Q10, Q18. rewrite L5 in Q22. rewrite L6 in V120.
split; [exact Q10|]. split; [exact Q18|]. split; [exact Q22|]. split; [exact Q26|]. split; [exact Q21|].
split; [exact Q27|]. split; [exact Q24|]. split; [exact V176|]. split; [exact V160|]. split; [exact V120|].
exact V112.
Qed.

Lemma f_reg_kept : forall E n (v : word), ew E n = v -> sv_denot E (SOff n 0) = v.
Proof. intros E n v H. cbn [sv_denot]. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.

Lemma f_nlen : forall (g : ectx) pos mf ly2 S2 (W2 : world SEGS) regs2 mem2 md2,
  ECOM g pos mf ly2 S2 W2 regs2 mem2 md2 -> SlotModel.nlen (e_pl g) = e_n g.
Proof.
intros g pos mf ly2 S2 W2 regs2 mem2 md2 HC.
destruct HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRE & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hlen & _). unfold SlotModel.nlen. lia.
Qed.

Lemma f_frame : forall (g : ectx) pos mf ly2 S2 (W2 : world SEGS) regs2 mem2 md2 k,
  JE g pos ly2 S2 W2 mem2 md2 k -> ECOM g pos mf ly2 S2 W2 regs2 mem2 md2 ->
  getr regs2 9 = w64 mf /\ e_sp0 g - LLVMF_STK <= mf + 112 /\ mf + 184 <= e_sp0 g /\ 0 <= mf < 2 ^ 64.
Proof.
intros g pos mf ly2 S2 W2 regs2 mem2 md2 k HJ HC.
destruct HC as (_ & Rs1 & _ & Hmfb & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
assert (Has : ASTACK = 16384) by reflexivity.
pose proof HSTK as HSTK'. unfold STK_LLVMF in HSTK'.
split; [exact Rs1|]. clear - Hmfb Hceil Hslo Hshi H47 HSTK' Has C1. lia.
Qed.

Lemma f_dn_atom_off : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v /\ v + c < 2 ^ 64 /\ 0 <= c ->
  sv_denot E (SOff n c) = w64 (v + c).
Proof.
intros E n v c H Hv. rewrite denot_lit_U, (U_atom_off E n v c H) by lia. reflexivity.
Qed.

Lemma f_sf : forall (g : ectx) pos ly2 S2 (W2 : world SEGS) mem2 md2 k,
  JE g pos ly2 S2 W2 mem2 md2 k -> frames S2 = [(4, pos)] ->
  0 <= SFa g pos /\ SFa g pos + V_ef < 2 ^ 64 /\ 0 <= V_ef.
Proof.
intros g pos ly2 S2 W2 mem2 md2 k HJ Hfrs.
pose proof HJ as (HAR2 & Hly2 & _).
pose proof Hly2 as (_ & _ & _ & _ & _ & EF & _).
assert (EFa : frame_addr ly2 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF; reflexivity).
assert (Hin4 : In (4, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly2 S2 W2 mem2 md2 4 pos HAR2 Hin4) as (HSF0 & HSF1 & _).
rewrite EFa in HSF0, HSF1. change (fs_frame_bytes 4) with 1024 in HSF1.
pose proof asan_consts as (C1 & _). unfold V_ef. clear - HSF0 HSF1 C1. lia.
Qed.

Definition f_case_stmt (m : nat) (pin : bool) (r : Z) : Prop :=
  forall (g : ectx) pos mf (W2 : world SEGS) ly2 S2 regs2 mem2 md2,
  JE g pos ly2 S2 W2 mem2 md2 (4 * Z.of_nat (m_nrec g)) ->
  frames S2 = [(4, pos)] -> 0 <= 4 * Z.of_nat (m_nrec g) <= EV_LLVMF ->
  mo_le MT (e_S g) S2 (4 * Z.of_nat (m_nrec g) * MEV MT) ->
  mo_ok MT S2 ((EV_LLVMF - 4 * Z.of_nat (m_nrec g)) * MEV MT) ->
  ECOM g pos mf ly2 S2 W2 regs2 mem2 md2 ->
  id_at g pos (m_nrec g) W2 mem2 -> hw_at g pos (m_nrec g) W2 mem2 -> hblocks B g ly2 S2 [] ->
  mf_id3 g pos mf W2 mem2 -> mf_id g pos mf W2 mem2 -> sh_reg g pos regs2 ->
  getr regs2 25 = w64 (e_p g + SlotModel.cT (e_pl g)) ->
  getr regs2 24 = w64 (e_n g - SlotModel.cT (e_pl g)) ->
  getr regs2 14 = w64 SHADOW_OFF ->
  Z.of_nat m = Z.min (e_n g - SlotModel.cT (e_pl g)) 11 ->
  (if pin then e_n g - SlotModel.cT (e_pl g) = r else 11 <= e_n g - SlotModel.cT (e_pl g)) ->
  SRr SEGS W2 (cfg_at SEGS (BASE + 0x1080) regs2 mem2 md2) (INV_F g pos mf).

Let RUNTO := paj_run_to B LAWS.

Ltac f_regnorm Q :=
  lazymatch type of Q with getr _ ?r = sv_denot _ (sr_get (ss_regs ?ss) ?r) =>
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Q
  end; cbn [ms_regs restrict] in Q.
Ltac f_brange := lazymatch goal with |- 0 <= SlotModel.tb ?i ?j < _ => pose proof (f_tb_range i j); lia end.
Ltac f_val :=
  first
  [ apply f_dn_lit0; repeat match goal with Z : SlotModel.tb _ _ = 0 |- _ => rewrite Z end; reflexivity
  | apply f_dn_atom; [assumption | f_brange]
  | apply f_dn_and0; [assumption | f_brange]
  | apply f_dn_and; [assumption | f_brange | lia]
  | apply f_dn_mod40; [assumption | f_brange]
  | apply f_dn_or; [assumption | assumption | f_brange | f_brange]
  | apply f_dn_or0; [assumption | f_brange | assumption] ].
Ltac f_chunk := cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right]).

Ltac f_case_tac :=
  lazymatch goal with |- f_case_stmt ?m ?pin ?r =>
  unfold f_case_stmt;
  intros g pos mf W2 ly2 S2 regs2 mem2 md2 HJ Hfrs Hk MLE MOK HC Hid Hhw Hbl Hid3 Hmid Hsh R25 R24 R14 Hm Hpin;
  destruct (f_entry g pos mf W2 ly2 S2 regs2 mem2 md2 _ m pin r HJ HC Hbl R25 R24 R14 Hm Hpin) as [HS SHOK];
  destruct (f_frame g pos mf ly2 S2 W2 regs2 mem2 md2 _ HJ HC) as (Rs1 & Hw1 & Hw2 & Hmf);
  pose proof (f_nlen g pos mf ly2 S2 W2 regs2 mem2 md2 HC) as Hnl;
  remember (Eimg (Ereg regs2 (f_extra (SFa g pos) (e_pl g)))) as E eqn:HE;
  assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env);
  assert (EE : forall nn (rr : bv 5), Z.of_nat nn = bv_unsigned rr -> ew E nn = getr regs2 rr)
    by (intros nn rr Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn);
  assert (U9 : bv_unsigned (ew E 9) = mf) by (rewrite (EE 9%nat 9%bv eq_refl), Rs1; apply unsigned_lit_small; exact Hmf);
  assert (U32 : ew E 32 = Z_to_bv 64 (SFa g pos)) by (rewrite HE; exact (f_E_SF regs2 (SFa g pos) (e_pl g)));
  pose proof (f_sf g pos ly2 S2 W2 mem2 md2 _ HJ Hfrs) as HSFr;
  assert (UB : forall j, (j < 11)%nat -> ew E (33 + j) = Z_to_bv 64 (SlotModel.tb (e_pl g) (Z.of_nat j)))
    by (intros j Hj; rewrite HE; exact (f_E_tb regs2 (SFa g pos) (e_pl g) j Hj));
  clear HE;
  unfold cfg_at; change (w64 (BASE + 0x1080)) with (Z_to_bv 64 (BASE + 0x1080));
  paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x1128;
  [ exact (f_awr E m LLVMF_STK (e_sp0 g) [] _ _ ly2 [(4, pos)] mf U9 Hw1 Hw2) |];
  lazymatch goal with HS : st_ok_pi _ _ ?E' ?ss' (restrict _ ?ms), HFr : frame_of _ _ _ _ |- _ =>
  assert (AG : forall nn, (nn < 512)%nat -> ew E' nn = ew E nn)
    by (intros nn Hn; repeat rewrite ew_ewset_other by lia; reflexivity);
  pose proof (f_keep E m (w_H W2) mem2 (ms_mem ms) mf U9 HFr) as KEEP;
  assert (U9' : bv_unsigned (ew E' 9) = mf) by (try (rewrite AG by lia); exact U9);
  assert (T0 : ew E' 33 = Z_to_bv 64 (SlotModel.tb (e_pl g) 0)) by (try (rewrite AG by lia); exact (UB 0%nat ltac:(lia)));
  assert (T1 : ew E' 34 = Z_to_bv 64 (SlotModel.tb (e_pl g) 1)) by (try (rewrite AG by lia); exact (UB 1%nat ltac:(lia)));
  assert (T2 : ew E' 35 = Z_to_bv 64 (SlotModel.tb (e_pl g) 2)) by (try (rewrite AG by lia); exact (UB 2%nat ltac:(lia)));
  assert (T3 : ew E' 36 = Z_to_bv 64 (SlotModel.tb (e_pl g) 3)) by (try (rewrite AG by lia); exact (UB 3%nat ltac:(lia)));
  assert (T4 : ew E' 37 = Z_to_bv 64 (SlotModel.tb (e_pl g) 4)) by (try (rewrite AG by lia); exact (UB 4%nat ltac:(lia)));
  assert (T5 : ew E' 38 = Z_to_bv 64 (SlotModel.tb (e_pl g) 5)) by (try (rewrite AG by lia); exact (UB 5%nat ltac:(lia)));
  assert (T6 : ew E' 39 = Z_to_bv 64 (SlotModel.tb (e_pl g) 6)) by (try (rewrite AG by lia); exact (UB 6%nat ltac:(lia)));
  assert (T7 : ew E' 40 = Z_to_bv 64 (SlotModel.tb (e_pl g) 7)) by (try (rewrite AG by lia); exact (UB 7%nat ltac:(lia)));
  assert (T8 : ew E' 41 = Z_to_bv 64 (SlotModel.tb (e_pl g) 8)) by (try (rewrite AG by lia); exact (UB 8%nat ltac:(lia)));
  assert (T9 : ew E' 42 = Z_to_bv 64 (SlotModel.tb (e_pl g) 9)) by (try (rewrite AG by lia); exact (UB 9%nat ltac:(lia)));
  assert (T10 : ew E' 43 = Z_to_bv 64 (SlotModel.tb (e_pl g) 10)) by (try (rewrite AG by lia); exact (UB 10%nat ltac:(lia)));
  (lazymatch pin with
   | true =>
     assert (HNC : SlotModel.nlen (e_pl g) = SlotModel.cT (e_pl g) + r) by (rewrite Hnl; clear - Hpin; cbv iota in Hpin; lia);
     try (assert (Z0 : SlotModel.tb (e_pl g) 0 = 0) by (apply f_tb_past; clear - HNC; lia));
     try (assert (Z1 : SlotModel.tb (e_pl g) 1 = 0) by (apply f_tb_past; clear - HNC; lia));
     try (assert (Z2 : SlotModel.tb (e_pl g) 2 = 0) by (apply f_tb_past; clear - HNC; lia));
     try (assert (Z3 : SlotModel.tb (e_pl g) 3 = 0) by (apply f_tb_past; clear - HNC; lia));
     try (assert (Z4 : SlotModel.tb (e_pl g) 4 = 0) by (apply f_tb_past; clear - HNC; lia));
     try (assert (Z5 : SlotModel.tb (e_pl g) 5 = 0) by (apply f_tb_past; clear - HNC; lia));
     try (assert (Z6 : SlotModel.tb (e_pl g) 6 = 0) by (apply f_tb_past; clear - HNC; lia));
     try (assert (Z7 : SlotModel.tb (e_pl g) 7 = 0) by (apply f_tb_past; clear - HNC; lia));
     try (assert (Z8 : SlotModel.tb (e_pl g) 8 = 0) by (apply f_tb_past; clear - HNC; lia));
     try (assert (Z9 : SlotModel.tb (e_pl g) 9 = 0) by (apply f_tb_past; clear - HNC; lia));
     try (assert (Z10 : SlotModel.tb (e_pl g) 10 = 0) by (apply f_tb_past; clear - HNC; lia))
   | false => idtac
   end);
  pose proof (st_ok_pi_restrict_reg (w_H W2) E' ss' ms 2%bv HS) as Q2; f_regnorm Q2; pose proof (st_ok_pi_restrict_reg (w_H W2) E' ss' ms 9%bv HS) as Q9; f_regnorm Q9; pose proof (st_ok_pi_restrict_reg (w_H W2) E' ss' ms 8%bv HS) as Q8; f_regnorm Q8; pose proof (st_ok_pi_restrict_reg (w_H W2) E' ss' ms 3%bv HS) as Q3; f_regnorm Q3; pose proof (st_ok_pi_restrict_reg (w_H W2) E' ss' ms 4%bv HS) as Q4; f_regnorm Q4;
  pose proof (st_ok_pi_restrict_reg (w_H W2) E' ss' ms 23%bv HS) as Q23; f_regnorm Q23; pose proof (st_ok_pi_restrict_reg (w_H W2) E' ss' ms 25%bv HS) as Q25; f_regnorm Q25; pose proof (st_ok_pi_restrict_reg (w_H W2) E' ss' ms 10%bv HS) as Q10; f_regnorm Q10; pose proof (st_ok_pi_restrict_reg (w_H W2) E' ss' ms 18%bv HS) as Q18; f_regnorm Q18; pose proof (st_ok_pi_restrict_reg (w_H W2) E' ss' ms 22%bv HS) as Q22; f_regnorm Q22;
  pose proof (st_ok_pi_restrict_reg (w_H W2) E' ss' ms 26%bv HS) as Q26; f_regnorm Q26; pose proof (st_ok_pi_restrict_reg (w_H W2) E' ss' ms 21%bv HS) as Q21; f_regnorm Q21; pose proof (st_ok_pi_restrict_reg (w_H W2) E' ss' ms 27%bv HS) as Q27; f_regnorm Q27; pose proof (st_ok_pi_restrict_reg (w_H W2) E' ss' ms 24%bv HS) as Q24; f_regnorm Q24;
  pmkst HS; apply SRr_ret;
  apply (f_post g pos mf W2 ly2 S2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms) _ HJ Hfrs Hk MLE MOK HC Hid Hhw Hbl
    Hid3 Hmid Hsh KEEP);
  [ rewrite Q2; apply f_reg_kept; try (rewrite AG by lia); apply EE; reflexivity
  | rewrite Q9; apply f_reg_kept; try (rewrite AG by lia); apply EE; reflexivity
  | rewrite Q8; apply f_reg_kept; try (rewrite AG by lia); apply EE; reflexivity
  | rewrite Q3; apply f_reg_kept; try (rewrite AG by lia); apply EE; reflexivity
  | rewrite Q4; apply f_reg_kept; try (rewrite AG by lia); apply EE; reflexivity
  | rewrite Q23; apply f_reg_kept; try (rewrite AG by lia); apply EE; reflexivity
  | rewrite Q25; apply f_dn_atom_off; [try (rewrite AG by lia); exact U32 | exact HSFr]
  | rewrite Q10; f_val | rewrite Q18; f_val | rewrite Q22; f_val | rewrite Q26; f_val | rewrite Q21; f_val
  | rewrite Q27; f_val | rewrite Q24; f_val
  | eapply (f_slot E' ss' ms (w_H W2) 3%nat _ 176 _ _ mf HS); [reflexivity | reflexivity | exact U9' | f_chunk | f_val | f_brange]
  | eapply (f_slot E' ss' ms (w_H W2) 2%nat _ 160 _ _ mf HS); [reflexivity | reflexivity | exact U9' | f_chunk | f_val | f_brange]
  | eapply (f_slot E' ss' ms (w_H W2) 1%nat _ 120 _ _ mf HS); [reflexivity | reflexivity | exact U9' | f_chunk | f_val
    | pose proof (Z.land_nonneg (SlotModel.tb (e_pl g) 7) 63); pose proof (Z_land_upper (SlotModel.tb (e_pl g) 7) 63 ltac:(lia)); lia]
  | eapply (f_slot E' ss' ms (w_H W2) 1%nat _ 112 _ _ mf HS); [reflexivity | reflexivity | exact U9' | f_chunk | f_val | f_brange] ]
  end end.

Lemma f_case0 : f_case_stmt 0 true 0.
Proof. f_case_tac. Qed.
Lemma f_case1 : f_case_stmt 1 true 1.
Proof. f_case_tac. Qed.
Lemma f_case2 : f_case_stmt 2 true 2.
Proof. f_case_tac. Qed.
Lemma f_case3 : f_case_stmt 3 true 3.
Proof. f_case_tac. Qed.
Lemma f_case4 : f_case_stmt 4 true 4.
Proof. f_case_tac. Qed.
Lemma f_case5 : f_case_stmt 5 true 5.
Proof. f_case_tac. Qed.
Lemma f_case6 : f_case_stmt 6 true 6.
Proof. f_case_tac. Qed.
Lemma f_case7 : f_case_stmt 7 true 7.
Proof. f_case_tac. Qed.
Lemma f_case8 : f_case_stmt 8 true 8.
Proof. f_case_tac. Qed.
Lemma f_case9 : f_case_stmt 9 true 9.
Proof. f_case_tac. Qed.
Lemma f_case10 : f_case_stmt 10 true 10.
Proof. f_case_tac. Qed.
Lemma f_case11 : f_case_stmt 11 false 0.
Proof. f_case_tac. Qed.

Lemma seg_F : seg_F_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none
  ameta_inv arodata_okS.
Proof.
intros g pos mf W2 c2 Hstart.
destruct Hstart as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfrs & Hk & MLE & MOK & HC & HP).
destruct HP as (Hid & Hhw & Hbl & Hid3 & Hmid & Hsh & _ & R25 & R24 & R14).
pose proof (f_nlen g pos mf ly2 S2 W2 regs2 mem2 md2 HC) as Hnl.
pose proof (SlotModel.rec_c_range (e_pl g) (SlotModel.nrecn (e_pl g))) as HcT.
fold (SlotModel.cT (e_pl g)) in HcT. rewrite Hnl in HcT.
destruct (Z_lt_le_dec (e_n g - SlotModel.cT (e_pl g)) 11) as [Hlt | Hge].
- assert (Hc : e_n g - SlotModel.cT (e_pl g) = 0 \/ e_n g - SlotModel.cT (e_pl g) = 1 \/
    e_n g - SlotModel.cT (e_pl g) = 2 \/ e_n g - SlotModel.cT (e_pl g) = 3 \/
    e_n g - SlotModel.cT (e_pl g) = 4 \/ e_n g - SlotModel.cT (e_pl g) = 5 \/
    e_n g - SlotModel.cT (e_pl g) = 6 \/ e_n g - SlotModel.cT (e_pl g) = 7 \/
    e_n g - SlotModel.cT (e_pl g) = 8 \/ e_n g - SlotModel.cT (e_pl g) = 9 \/
    e_n g - SlotModel.cT (e_pl g) = 10) by (clear - HcT Hlt; lia).
  destruct Hc as [Hr|[Hr|[Hr|[Hr|[Hr|[Hr|[Hr|[Hr|[Hr|[Hr|Hr]]]]]]]]]];
  [ apply (f_case0 g pos mf W2 ly2 S2 regs2 mem2 md2)
  | apply (f_case1 g pos mf W2 ly2 S2 regs2 mem2 md2)
  | apply (f_case2 g pos mf W2 ly2 S2 regs2 mem2 md2)
  | apply (f_case3 g pos mf W2 ly2 S2 regs2 mem2 md2)
  | apply (f_case4 g pos mf W2 ly2 S2 regs2 mem2 md2)
  | apply (f_case5 g pos mf W2 ly2 S2 regs2 mem2 md2)
  | apply (f_case6 g pos mf W2 ly2 S2 regs2 mem2 md2)
  | apply (f_case7 g pos mf W2 ly2 S2 regs2 mem2 md2)
  | apply (f_case8 g pos mf W2 ly2 S2 regs2 mem2 md2)
  | apply (f_case9 g pos mf W2 ly2 S2 regs2 mem2 md2)
  | apply (f_case10 g pos mf W2 ly2 S2 regs2 mem2 md2) ];
  first [ assumption | rewrite Hr; reflexivity ].
- apply (f_case11 g pos mf W2 ly2 S2 regs2 mem2 md2); first [ assumption | clear - Hge; lia ].
Qed.
Check (seg_F : seg_F_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
  asink_none ameta_inv arodata_okS).

End c.
End b.
End a.

Print Assumptions seg_F.
