(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACbk.v:76-79;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACer.v:148-161; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:200-203;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACja.v:107-118, for libreac/fuzz_identity's ASan build (lib/A). The same text
   also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACa2.v:141-143. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_A.v; 667 of its 722 lines of code are new or changed and 525 lines of the source are left out. *)
(* Segment F of LLVMFuzzerTestOneInput's ASan walk (fuzz_identity.asan): 0x815f8 .. 0x816e4, with the
   out-of-line block 0x82178 .. 0x822ec that the segment jumps through. The code reads the eleven tail bytes
   of the input block through the cursor x26, each behind a shadow test, and reduces them: the family byte
   (x23), the two widths (mf+160, mf+168), the five capacities (x20 = b3 mod 16, x25 = b4 mod 32,
   x26 = b5 mod 40, x24 = b6 mod 40, mf+144 = b7 mod 64), the catalogue row (mf+136) and the two bytes of the
   16-bit firmware value (x21, x18); x10 is max(cap_fw, 1), the argument of the malloc at 0x816e4, which is
   the segment's last slot. When fewer than eleven bytes are left the code jumps out of the chain early and
   zeroes the rest, which is what the model's reader gives for an index past the end.

   The walk is one run of the position-abstract engine per possible number of remaining bytes (0 .. 10, and
   11 or more), with the input bytes in a region of one chunk per byte. No call is made, so this file takes
   no callee contract; the only Section hypothesis is AR_laws. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentSyms IdentList IdentPa IdentPaLib IdentBase YC81.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require IdentSpec SlotModel RcIdentModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
(* LLVMFuzzerTestOneInput_inv imports YC4b, which turns lia's euclidean division handling off; the shadow
   lemmas below need it on. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* ---- the symbolic state the segment is walked from ------------------------------------------------------ *)
Definition F_pc0 : Z := 0xeec.
Definition F_pc1 : Z := 0xfd8.
Definition F_Bx : sv := SOff 13 0.
Definition F_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
(* the callee-saved registers and the fixed ones the segment never writes *)
Definition F_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 13; 19; 22; 27]%bv.
(* the four machine-frame slots the segment writes (mf + 136 .. mf + 176) *)
Definition mf_region : YP09.region := YP09.mkRegion (Some 9%nat) 136 176 136 176 [].
(* the tail of the input block: one chunk per byte, atom 32 + j for byte j *)
Definition in_chunks (m : nat) : list YP09.chunk :=
map (fun j => YP09.mkChunk (Z.of_nat j) (CVal 1 (SOff (32 + j) 0))) (seq 0 m).
Definition in_region (m : nat) : YP09.region := YP09.mkRegion (Some 26%nat) 0 (Z.of_nat m) 0 0 (in_chunks m).
Definition F_regions (m : nat) : smem := match m with O => [mf_region] | _ => [mf_region; in_region m] end.
Definition F_byte_facts (m : nat) : list (nat * afact) := map (fun j => ((32 + j)%nat, mkAF 0 255 0)) (seq 0 m).
Definition F_facts (m : nat) (big : bool) : facts :=
mkFacts ([(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (13%nat, mkAF SB SB 0)]
++ (match m with O => [] | _ => [(26%nat, mkAF 4096 (2 ^ 47 - 16) 0)] end)
++ (if big then [(18%nat, mkAF 11 (2 ^ 26) 0)] else []) ++ F_byte_facts m) [] [].
Definition ss_F (m : nat) (big : bool) : sstate := mkSS F_pc0 sr_atoms (F_regions m) None (F_facts m big).
Definition F_extra (tv : nat -> Z) : list word := map (fun j => Z_to_bv 64 (tv j)) (seq 0 11).

(* ---- the arithmetic the reductions need ----------------------------------------------------------------- *)
Lemma land15 : forall b, 0 <= b < 256 -> Z.land b 15 = b mod 16.
Proof. intros b Hb. change 15 with (Z.ones 4). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land31 : forall b, 0 <= b < 256 -> Z.land b 31 = b mod 32.
Proof. intros b Hb. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land63 : forall b, 0 <= b < 256 -> Z.land b 63 = b mod 64.
Proof. intros b Hb. change 63 with (Z.ones 6). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma div205 : forall b, 0 <= b < 256 -> b * 205 / 8192 = b / 40.
Proof.
intros b Hb.
assert (HB : 0 <= b < 0 + Z.of_nat 256) by (replace (Z.of_nat 256) with 256 by (vm_compute; reflexivity); lia).
pose proof (IdentSpec.z_all_spec (fun y => y * 205 / 8192 =? y / 40) 256%nat 0
ltac:(vm_compute; reflexivity) b HB) as H.
apply Z.eqb_eq in H. exact H.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* ---- the shapes the final state's registers have -------------------------------------------------------- *)
Lemma U_atomv : forall E x b, ew E x = Z_to_bv 64 b -> 0 <= b < 256 -> U E (SOff x 0) = b.
Proof. intros E x b H Hb. rewrite U_SOff, H, unsigned_lit_small by lia. rewrite Z.add_0_r. unfold zcanon, M64. apply Z.mod_small. lia. Qed.
Lemma U_and_gen : forall E x b k mk, ew E x = Z_to_bv 64 b -> 0 <= b < 256 -> Z.land b k = b mod mk ->
0 <= k < 2 ^ 64 -> 0 < mk < 2 ^ 64 -> U E (SAlu ALU_AND (SOff x 0) (SLit k)) = b mod mk.
Proof.
intros E x b k mk H Hb Hl Hk Hmk. pose proof (Z.mod_pos_bound b mk (proj1 Hmk)) as Hr.
rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atomv E x b H Hb), U_SLit. unfold zcanon, M64. rewrite (Z.mod_small k (2 ^ 64)) by lia.
rewrite Hl. apply Z.mod_small. lia.
Qed.
Lemma U_and15 : forall E x b, ew E x = Z_to_bv 64 b -> 0 <= b < 256 ->
U E (SAlu ALU_AND (SOff x 0) (SLit 15)) = b mod 16.
Proof. intros E x b H Hb. apply (U_and_gen E x b 15 16 H Hb (land15 b Hb)); lia. Qed.
Lemma U_and31 : forall E x b, ew E x = Z_to_bv 64 b -> 0 <= b < 256 ->
U E (SAlu ALU_AND (SOff x 0) (SLit 31)) = b mod 32.
Proof. intros E x b H Hb. apply (U_and_gen E x b 31 32 H Hb (land31 b Hb)); lia. Qed.
Lemma U_and63 : forall E x b, ew E x = Z_to_bv 64 b -> 0 <= b < 256 ->
U E (SAlu ALU_AND (SOff x 0) (SLit 63)) = b mod 64.
Proof. intros E x b H Hb. apply (U_and_gen E x b 63 64 H Hb (land63 b Hb)); lia. Qed.
Lemma U_mod40 : forall E x b, ew E x = Z_to_bv 64 b -> 0 <= b < 256 ->
U E (SAlu ALU_SUB (SOff x 0)
(SMd M_MUL (SAlu ALU_SRL (SMd M_MUL (SOff x 0) (SLit 205)) (SLit 13)) (SLit 40))) = b mod 40.
Proof.
intros E x b H Hb. pose proof (U_atomv E x b H Hb) as Hx.
assert (Hdiv : 0 <= b / 40 <= 6) by (Z.div_mod_to_equations; lia).
rewrite U_SAlu. cbn [zalu_raw]. rewrite Hx.
rewrite U_SMd. cbn [zmd_raw].
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw]. rewrite Hx, !U_SLit.
unfold zcanon, M64. rewrite (Z.mod_small 205 (2 ^ 64)) by lia. rewrite (Z.mod_small 13 (2 ^ 64)) by lia.
rewrite (Z.mod_small 40 (2 ^ 64)) by lia.
rewrite (Z.mod_small (b * 205) (2 ^ 64)) by lia.
change (Z.land 13 63) with 13. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 13) with 8192.
rewrite (div205 b Hb). rewrite (Z.mod_small (b / 40) (2 ^ 64)) by lia.
rewrite (Z.mod_small (b / 40 * 40) (2 ^ 64)) by lia.
rewrite (Z.mod_small (b - b / 40 * 40) (2 ^ 64)) by (pose proof (Z.mod_pos_bound b 40 ltac:(lia)); pose proof (Z.div_mod b 40 ltac:(lia)); lia).
pose proof (Z.div_mod b 40 ltac:(lia)). lia.
Qed.
Lemma U_max15 : forall E x b, ew E x = Z_to_bv 64 b -> 0 <= b < 256 ->
U E (SAlu ALU_ADD (SAlu ALU_AND (SOff x 0) (SLit 15))
(SAlu ALU_SLTU (SAlu ALU_AND (SOff x 0) (SLit 15)) (SLit 1))) = Z.max (b mod 16) 1.
Proof.
intros E x b H Hb. pose proof (U_and15 E x b H Hb) as Ha.
pose proof (Z.mod_pos_bound b 16 ltac:(lia)) as Hr.
rewrite U_SAlu. cbn [zalu_raw]. rewrite Ha.
rewrite U_SAlu. cbn [zalu_raw]. rewrite Ha, U_SLit.
unfold zcanon, M64. rewrite (Z.mod_small 1 (2 ^ 64)) by lia.
destruct (Z.ltb_spec (b mod 16) 1) as [Hlt | Hge].
- assert (Hz : b mod 16 = 0) by lia. rewrite Hz. reflexivity.
- change (0 mod 2 ^ 64) with 0. rewrite Z.add_0_r, (Z.mod_small (b mod 16) (2 ^ 64)) by lia. lia.
Qed.

Section b.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
Definition EF (regs : bvmap 5 word) (tv : nat -> Z) : env := Eimg (Ereg regs (F_extra tv)).

Lemma F_kept_fr : forall (W : world SEGS) Ex rs (m m' : word -> option byte) a,
frame_of Ex rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') -> 0 <= a < 2 ^ 64 -> ~ in_wrange Ex rs a ->
aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a.
Proof. intros W Ex rs m m' a HF Ha Hn. apply aview_eq_of. apply HF. rewrite unsigned_lit_small by lia. exact Hn. Qed.

Lemma atoms_ok_app : forall E l1 l2, atoms_ok E l1 -> atoms_ok E l2 -> atoms_ok E (l1 ++ l2).
Proof.
intros E l1. induction l1 as [|[n f] l1 IH]; intros l2 H1 H2; cbn in *; [exact H2|].
destruct H1 as [Ha Hr]. split; [exact Ha | exact (IH l2 Hr H2)].
Qed.
Lemma atoms_ok_bytes : forall E m (tv : nat -> Z),
(forall j, (j < 11)%nat -> ew E (32 + j)%nat = Z_to_bv 64 (tv j)) ->
(forall j, 0 <= tv j < 256) -> (m <= 11)%nat -> atoms_ok E (F_byte_facts m).
Proof.
intros E m tv HX Htv Hm. unfold F_byte_facts.
assert (HG : forall k, (k <= m)%nat -> atoms_ok E (map (fun j => ((32 + j)%nat, mkAF 0 255 0)) (seq (m - k) k))).
{ intros k. induction k as [|k IH]; intros Hk; [cbn; exact I|].
  replace (m - S k)%nat with (m - S k)%nat by reflexivity.
  cbn [seq map atoms_ok].
  split.
  - unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite (HX (m - S k)%nat ltac:(lia)), unsigned_lit_small by (pose proof (Htv (m - S k)%nat); lia).
    pose proof (Htv (m - S k)%nat). split; [lia|]. split; [apply Z.mod_1_r | lia].
  - replace (S (m - S k))%nat with (m - k)%nat by lia. apply IH. lia. }
pose proof (HG m ltac:(lia)) as H. replace (m - m)%nat with 0%nat in H by lia. exact H.
Qed.

Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Let RUNTO := paj_run_to B LAWS.

(* ---- the entry state ------------------------------------------------------------------------------------ *)
Lemma F_entry : forall (regs : bvmap 5 word) (W : world SEGS) (mem : word -> option byte)
(mf q rem : Z) (m : nat) (big : bool) (tv : nat -> Z),
(m <= 11)%nat ->
getr regs 9 = w64 mf -> getr regs 13 = w64 SHADOW_OFF ->
getr regs 26 = w64 q -> getr regs 18 = w64 rem ->
ASAN_CEIL <= mf -> mf + 176 <= 2 ^ 47 -> mf mod 32 = 0 ->
(forall a, mf + 136 <= a < mf + 176 -> apresent (w_H W) mem a) ->
((m = 0)%nat \/ (4096 <= q /\ q + Z.of_nat m <= ASAN_CEIL)) ->
(big = true -> 11 <= rem <= 2 ^ 26) ->
(forall j, (j < m)%nat -> val_mem SEGS (mrestrict (w_H W) mem) (q + Z.of_nat j) 1 (tv j)) ->
(forall j, 0 <= tv j < 256) ->
st_ok_pi SEGS VAL (EF regs tv) (ss_F m big)
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + F_pc0)) mem (seg_rom SEGS))).
Proof.
intros regs W mem mf q rem m big tv Hm E9 E13 E26 E18 Hmfc Hmfhi Hmf32 Hpres Hq Hbig Hbytes Htvr.
pose proof asan_consts as (AC & _ & _ & _ & _). unfold ASAN_CEIL in *.
rewrite restrict_mkst_fx.
set (E := EF regs tv).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (F_extra tv)) n)
by (intros n Hn; unfold E, EF; apply Eimg_low; exact Hn).
assert (W9 : ew E 9%nat = Z_to_bv 64 mf)
by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact E9).
assert (W13 : ew E 13%nat = Z_to_bv 64 SHADOW_OFF)
by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl); exact E13).
assert (W26 : ew E 26%nat = Z_to_bv 64 q)
by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact E26).
assert (W18 : ew E 18%nat = Z_to_bv 64 rem)
by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact E18).
assert (WX : forall j, (j < 11)%nat -> ew E (32 + j)%nat = Z_to_bv 64 (tv j)).
{ intros j Hj. rewrite EL by (unfold A_TEXT; lia). rewrite ew_Ereg_extra. unfold F_extra.
  rewrite (nth_indep _ (Z_to_bv 64 0) (Z_to_bv 64 (tv 0%nat))) by (rewrite length_map, length_seq; lia).
  rewrite (map_nth (fun j0 : nat => Z_to_bv 64 (tv j0)) (seq 0 11) 0%nat j).
  rewrite seq_nth by lia. reflexivity. }
assert (HMF : 0 <= mf < 2 ^ 64) by lia.
assert (B9 : base_val E (Some 9%nat) = mf) by (cbn [base_val]; rewrite W9; apply unsigned_lit_small; lia).
assert (HQ64 : 0 <= q < 2 ^ 64 \/ (m = 0)%nat) by (destruct Hq as [H|[H1 H2]]; [right; exact H | left; lia]).
unfold ss_F. apply pa_entry_st_ok_full.
- unfold E, EF. apply regs_ok_Eimg_Ereg.
- clear - Hm. do 12 (destruct m as [|m]; [vm_compute; reflexivity|]). lia.
- assert (HMFR : region_ok SEGS E (mrestrict (w_H W) mem) mf_region).
  { unfold mf_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B9.
    split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia. }
  destruct m as [|m0]; unfold F_regions.
  + apply Forall_cons; [exact HMFR | apply Forall_nil].
  + destruct Hq as [Hq0 | [Hql Hqh]]; [discriminate Hq0|].
    assert (B26 : base_val E (Some 26%nat) = q) by (cbn [base_val]; rewrite W26; apply unsigned_lit_small; lia).
    apply Forall_cons; [exact HMFR|]. apply Forall_cons; [|apply Forall_nil].
    unfold in_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B26.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    unfold in_chunks. apply Forall_forall. intros ch Hch.
    apply in_map_iff in Hch as (j & <- & Hj). apply in_seq in Hj.
    apply (chunk_ok_val SEGS E _ q (Z.of_nat j) 1 (SOff (32 + j) 0) (tv j)).
    * cbn [sv_denot]. rewrite (WX j ltac:(lia)), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    * cbn. pose proof (Htvr j). lia.
    * cbn. lia.
    * cbn [N.to_nat]. apply Hbytes. lia.
- destruct m as [|m0]; unfold F_regions.
  + cbn [pairwise_disjoint all_disjoint]. repeat split.
  + destruct Hq as [Hq0 | [Hql Hqh]]; [discriminate Hq0|].
    assert (B26 : base_val E (Some 26%nat) = q) by (cbn [base_val]; rewrite W26; apply unsigned_lit_small; lia).
    cbn [pairwise_disjoint all_disjoint].
    split; [split; [|exact I] | repeat split].
    unfold extent_disjoint, mf_region, in_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite B9, B26. right. lia.
- split; [|split; [exact I | exact I]].
  unfold F_facts. cbn [f_atoms].
  apply atoms_ok_app.
  + cbn [atoms_ok]. split; [|split; [|exact I]].
    * unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite W9, unsigned_lit_small by lia.
      split; [lia|]. split; [change (2 ^ 5) with 32; exact Hmf32 | lia].
    * unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite W13, unsigned_lit_small by (unfold SHADOW_OFF; lia).
      unfold SB, SHADOW_OFF. split; [lia|]. split; [apply Z.mod_1_r | lia].
  + apply atoms_ok_app.
    * destruct m as [|m0]; cbn [atoms_ok]; [exact I|].
      destruct Hq as [Hq0 | [Hql Hqh]]; [discriminate Hq0|].
      split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite W26, unsigned_lit_small by lia. split; [lia|]. split; [apply Z.mod_1_r | lia].
    * apply atoms_ok_app.
      -- destruct big; cbn [atoms_ok]; [|exact I].
         split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
         rewrite W18, unsigned_lit_small by (pose proof (Hbig eq_refl); lia).
         pose proof (Hbig eq_refl). split; [lia|]. split; [apply Z.mod_1_r | lia].
      -- exact (atoms_ok_bytes E m tv WX Htvr Hm).
Qed.

(* ---- what the segment leaves ---------------------------------------------------------------------------- *)
Definition F_end_at (STK sp0 : Z) (FP : list (Z * Z)) (ly0 : alayout) (S0 : astate) (W0 : world SEGS)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (ly : alayout) (S : astate) (W : world SEGS)
(regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k mf : Z) (tv : nat -> Z)
: world SEGS -> config -> Prop :=
fun W3 c3 => exists (regs3 : bvmap 5 word) mem3 md3,
c3 = cfg_at SEGS (BASE + F_pc1) regs3 mem3 md3 /\ W3 = W /\
m_fds md3 = m_fds md /\ m_fs md3 = m_fs md /\
ajournal SEGS B STK sp0 FP ly0 S0 W0 mem0 md0 own ly S W mem3 md3 k /\
(forall r : bv 5, In r F_KEPT -> getr regs3 r = getr regs r) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (mf + 136 <= a < mf + 176) ->
aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) mem a) /\
getr regs3 10 = w64 (Z.max (tv 3%nat mod 16) 1) /\
getr regs3 20 = w64 (tv 3%nat mod 16) /\
getr regs3 25 = w64 (tv 4%nat mod 32) /\
getr regs3 26 = w64 (tv 5%nat mod 40) /\
getr regs3 24 = w64 (tv 6%nat mod 40) /\
getr regs3 23 = w64 (tv 0%nat) /\
getr regs3 21 = w64 (tv 9%nat) /\
getr regs3 18 = w64 (tv 10%nat) /\
val_mem SEGS (mrestrict (w_H W) mem3) (mf + 160) 8 (tv 1%nat) /\
val_mem SEGS (mrestrict (w_H W) mem3) (mf + 168) 8 (tv 2%nat) /\
val_mem SEGS (mrestrict (w_H W) mem3) (mf + 144) 8 (tv 7%nat mod 64) /\
val_mem SEGS (mrestrict (w_H W) mem3) (mf + 136) 8 (tv 8%nat).

(* ---- the walk ------------------------------------------------------------------------------------------- *)
Lemma blk_bounds : forall ly S (W : world SEGS) mem md p n,
AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) -> 4096 <= p /\ p + req_size n <= ASAN_CEIL.
Proof.
intros ly S W mem md p n HAR Hin.
destruct HAR as (M & _).
apply In_ablocks in Hin as (ck & Hck & Hst & Hu & Hnn).
destruct (chunk_facts B ly S _ ck M Hck) as (G1 & G2 & _ & G4 & G5 & _ & G7 & G8 & _).
destruct G1 as (G1a & _).
rewrite <- Hnn, <- Hu, G4. lia.
Qed.
Lemma F_ew : forall (regs : bvmap 5 word) tv (r : bv 5) (x : nat) v,
(x < 32)%nat -> Z.of_nat x = bv_unsigned r -> getr regs r = w64 v -> ew (EF regs tv) x = Z_to_bv 64 v.
Proof.
intros regs tv r x v Hx Hr H. unfold EF. rewrite Eimg_low by (unfold A_TEXT; lia).
rewrite (ew_Ereg_nat regs _ x r Hr). exact H.
Qed.
Lemma F_ewx : forall (regs : bvmap 5 word) tv j, (j < 11)%nat -> ew (EF regs tv) (32 + j)%nat = Z_to_bv 64 (tv j).
Proof.
intros regs tv j Hj. unfold EF. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite ew_Ereg_extra. unfold F_extra.
rewrite (nth_indep _ (Z_to_bv 64 0) (Z_to_bv 64 (tv 0%nat))) by (rewrite length_map, length_seq; lia).
rewrite (map_nth (fun j0 : nat => Z_to_bv 64 (tv j0)) (seq 0 11) 0%nat j).
rewrite seq_nth by lia. reflexivity.
Qed.

Ltac Fx_ew := repeat (rewrite ew_ewset_other by (let HH := fresh in intros HH; discriminate HH)); eassumption.
Ltac Fx_v Htvr ZT :=
lazymatch goal with
| |- U _ (SAlu ALU_ADD (SAlu ALU_AND _ _) (SAlu ALU_SLTU _ _)) = _ => eapply U_max15; [Fx_ew | apply Htvr]
| |- U _ (SAlu ALU_AND _ (SLit 15)) = _ => eapply U_and15; [Fx_ew | apply Htvr]
| |- U _ (SAlu ALU_AND _ (SLit 31)) = _ => eapply U_and31; [Fx_ew | apply Htvr]
| |- U _ (SAlu ALU_AND _ (SLit 63)) = _ => eapply U_and63; [Fx_ew | apply Htvr]
| |- U _ (SAlu ALU_SUB _ _) = _ => eapply U_mod40; [Fx_ew | apply Htvr]
| |- U _ (SOff _ _) = _ => eapply U_atomv; [Fx_ew | apply Htvr]
| |- _ => rewrite U_SLit; symmetry;
  solve [ reflexivity
        | rewrite ZT by (split; [apply Nat.leb_le | apply Nat.ltb_lt]; reflexivity); reflexivity ]
end.
Ltac Fx_valr r Htvr ZT :=
lazymatch goal with
| HS : st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) |- _ =>
let R := fresh "R" in
pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as R;
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
change (sr_get (ss_regs ss) r) with e in R;
cbn [ms_regs restrict mkst] in R;
rewrite R; clear R; rewrite denot_lit_U; unfold w64; f_equal; Fx_v Htvr ZT
end.
Ltac Fx_valm Htvr ZT VB :=
lazymatch goal with
| |- val_mem _ _ (?base + ?off) _ ?v =>
eapply (val_of_chunk_ok SEGS _ _ base off 8%N _ v);
[ eassumption | rewrite denot_lit_U; unfold w64; f_equal; Fx_v Htvr ZT
| apply VB; first [apply Htvr | assumption] | apply Z.leb_le; reflexivity ]
end.
Ltac Fx_obl U26 HAR Hin HBx Hn0 OB1 OBR :=
cbn [ms_mem mkst];
rewrite (U26 Hn0) by (split; apply Z.leb_le; reflexivity);
eapply (obl_of_block SEGS B LAWS);
[ exact HAR | exact (Hin Hn0) | exact HBx
| apply OB1; apply Z.leb_le; reflexivity
| apply OBR; split; [apply Z.leb_le | apply Z.ltb_lt]; reflexivity ].
Ltac Fx_awr EW9 HMF64 AW1 AW2 mf sp0 :=
lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0' ?fp ?b0 ?bc ?ly' ?own' =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0' fp b0 bc ly' own') end;
repeat first
[ apply awr_ok_nil
| apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; apply Z.le_refl|]
| eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (mf - sp0));
[ reflexivity
| cbn [ew]; rewrite EW9, (unsigned_lit_small mf HMF64); ring
| cbn [YP09.r_wlo YP09.r_whi]; clear - AW1; lia
| cbn [YP09.r_wlo YP09.r_whi]; clear - AW2; lia | ] ].
Ltac Fx_nwr EW9 HMF64 mf Hna :=
let rg := fresh "rg" in let Hin2 := fresh "Hin2" in let Hrg := fresh "Hrg" in
intros (rg & Hin2 & Hrg); cbn [ss_mem In] in Hin2;
repeat (destruct Hin2 as [<- | Hin2]); try contradiction;
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg;
first [ rewrite EW9, (unsigned_lit_small mf HMF64) in Hrg; exact (Hna Hrg)
| clear - Hrg; lia ].
Ltac Fx_post EW9 HMF64 mf regs tv HAE Htvr ZT VB :=
lazymatch goal with
| HS : st_ok_pi _ _ ?Ef _ (restrict (w_H ?Wf) _),
  HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
let HMO := fresh "HMO" in let HRok := fresh "HRok" in let HCH := fresh "HCH" in let E9f := fresh "E9f" in
pose proof (st_ok_mem_ok SEGS _ _ _ HS) as HMO;
destruct HMO as (_ & HRok & _);
cbn [ss_mem abs_ss] in HRok;
apply Forall_inv in HRok;
destruct HRok as (_ & _ & _ & HCH);
cbn [YP09.r_chunks YP09.r_base base_val] in HCH;
assert (E9f : bv_unsigned (ew Ef 9%nat) = mf)
by (repeat (rewrite ew_ewset_other by (let HH := fresh in intros HH; discriminate HH));
rewrite EW9; exact (unsigned_lit_small mf HMF64));
rewrite E9f in HCH;
repeat (let HC := fresh "HC" in apply Forall_cons_iff in HCH as [HC HCH]);
rewrite (st_ok_pi_restrict_mkst _ _ _ _ HS eq_refl); cbn [ss_pc];
apply SRr_ret; unfold F_end_at;
eexists; eexists; eexists;
split; [unfold cfg_at, w64, F_pc1; reflexivity|];
split; [reflexivity|];
split; [reflexivity|];
split; [reflexivity|];
split; [exact HJ|];
split; [ let rr := fresh "rr" in let Hrr := fresh "Hrr" in let HAE2 := fresh "HAE2" in intros rr Hrr;
assert (HAE2 : env_agree 32 (Ereg regs (F_extra tv)) Ef) by (clear - HAE; env_agree_chain HAE);
exact (regs_kept_of_st_ok_pi _ _ _ regs (F_extra tv) F_KEPT HS
HAE2 ltac:(vm_compute; reflexivity) rr Hrr) |];
split; [ let aa := fresh "aa" in let Haa := fresh "Haa" in let Hna := fresh "Hna" in
intros aa Haa Hna; eapply (F_kept_fr Wf); [exact HFr | exact Haa | Fx_nwr EW9 HMF64 mf Hna] |];
split; [Fx_valr (10%bv : bv 5) Htvr ZT|]; split; [Fx_valr (20%bv : bv 5) Htvr ZT|];
split; [Fx_valr (25%bv : bv 5) Htvr ZT|]; split; [Fx_valr (26%bv : bv 5) Htvr ZT|];
split; [Fx_valr (24%bv : bv 5) Htvr ZT|]; split; [Fx_valr (23%bv : bv 5) Htvr ZT|];
split; [Fx_valr (21%bv : bv 5) Htvr ZT|]; split; [Fx_valr (18%bv : bv 5) Htvr ZT|];
split; [Fx_valm Htvr ZT VB|]; split; [Fx_valm Htvr ZT VB|];
split; [Fx_valm Htvr ZT VB|]; Fx_valm Htvr ZT VB
end.
Ltac Fx_run U26 HAR Hin HBx Hn0 OB1 OBR EW9 HMF64 AW1 AW2 mf sp0 regs tv HAE Htvr ZT VB :=
lazymatch goal with
| HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
paj_run_to_tok RUNTO HS HJ SHOK F_Bspan F_pc1;
[ Fx_obl U26 HAR Hin HBx Hn0 OB1 OBR .. | Fx_awr EW9 HMF64 AW1 AW2 mf sp0
| Fx_post EW9 HMF64 mf regs tv HAE Htvr ZT VB ]
end.
Ltac Fx_entry ENTRY HPC Hbytes E18 rr mm bg :=
let HS := fresh "HS" in
pose proof (ENTRY mm bg rr ltac:(lia) E18
ltac:(first [ left; reflexivity
| right; let HB1 := fresh in let HB2 := fresh in
destruct (HPC ltac:(lia)) as [HB1 HB2]; split; lia ])
ltac:(first [ let HH := fresh in intros HH; discriminate HH | intros _; lia ])
ltac:(let jj := fresh "jj" in let Hjj := fresh "Hjj" in intros jj Hjj; apply Hbytes; lia)) as HS.
Ltac Fx_norm :=
lazymatch goal with HS : st_ok_pi _ _ _ ?ss1 _ |- _ =>
let ss2 := eval vm_compute in ss1 in change ss1 with ss2 in HS end.
Ltac Fx_pin E18 rr :=
lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ss0 ?ms0 |- _ =>
let HP := fresh "HP" in
pose proof (st_ok_pi_pin_reg' Ex ss0 ms0 (18%bv : bv 5) rr HS
ltac:(cbn [ms_regs restrict mkst]; exact E18) eq_refl) as HP;
clear HS; rename HP into HS
end; Fx_norm.

Lemma F_core : forall (STK sp0 : Z) (FP : list (Z * Z)) (ly0 : alayout) (S0 : astate) (W0 : world SEGS)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (ly : alayout) (S : astate) (W : world SEGS)
(regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k mf p n c : Z) (tv : nat -> Z),
ajournal SEGS B STK sp0 FP ly0 S0 W0 mem0 md0 own ly S W mem md k ->
336 <= STK ->
getr regs 9 = w64 mf -> getr regs 13 = w64 SHADOW_OFF ->
getr regs 26 = w64 (p + c) -> getr regs 18 = w64 (n - c) ->
sp0 - 336 <= mf <= sp0 - 320 -> mf mod 32 = 0 ->
0 <= c <= n -> n < 2 ^ 26 ->
(0 < n -> In (p, n) (ablocks B ly S)) ->
(forall j, (j < 11)%nat -> c + Z.of_nat j < n ->
val_mem SEGS (mrestrict (w_H W) mem) (p + c + Z.of_nat j) 1 (tv j)) ->
(forall j, (j < 11)%nat -> n <= c + Z.of_nat j -> tv j = 0) ->
(forall j, 0 <= tv j < 256) ->
SRr SEGS W (cfg_at SEGS (BASE + F_pc0) regs mem md)
(F_end_at STK sp0 FP ly0 S0 W0 mem0 md0 own ly S W regs mem md k mf tv).
Proof.
intros STK sp0 FP ly0 S0 W0 mem0 md0 own ly S W regs mem md k mf p n c tv
HJ HSTK E9 E13 E26 E18 Hmf Hmf32 Hc Hn Hin Hbytes Hzero Htvr.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _ & _).
pose proof asan_consts as (AC & _ & _ & _ & _).
destruct Hstk as (Hsp16 & HSTK0 & Hceil & Hlo & Hhi & H47 & _).
assert (Hmfc : ASAN_CEIL <= mf) by (unfold ASAN_CEIL in *; lia).
assert (Hmfhi : mf + 176 <= 2 ^ 47) by lia.
assert (Hpresw : forall a, mf + 136 <= a < mf + 176 -> apresent (w_H W) mem a)
by (intros a Ha; apply Hpres; lia).
assert (HPC : 0 < n -> 4096 <= p /\ p + n <= ASAN_CEIL).
{ intros Hn0. pose proof (blk_bounds ly S W mem md p n HAR (Hin Hn0)) as [HB1 HB2].
  pose proof (req_size_pos n ltac:(lia)). lia. }
assert (EW9 : ew (EF regs tv) 9%nat = Z_to_bv 64 mf)
by (apply (F_ew regs tv 9%bv 9%nat mf); [lia | reflexivity | exact E9]).
pose proof (req_size_pos n ltac:(lia)) as HRS.
assert (HBx : U (EF regs tv) F_Bx = SHADOW_OFF).
{ unfold F_Bx. rewrite U_SOff, (F_ew regs tv 13%bv 13%nat SHADOW_OFF ltac:(lia) eq_refl E13).
  rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). rewrite Z.add_0_r. unfold zcanon, M64.
  apply Z.mod_small. unfold SHADOW_OFF; lia. }
assert (U26 : 0 < n -> forall j, 0 <= j <= 10 -> U (EF regs tv) (SOff 26%nat j) = p + c + j).
{ intros Hn0 jj Hjj. destruct (HPC Hn0) as [HB1 HB2].
  rewrite U_SOff, (F_ew regs tv 26%bv 26%nat (p + c) ltac:(lia) eq_refl E26).
  rewrite unsigned_lit_small by (unfold ASAN_CEIL in *; lia). unfold zcanon, M64.
  apply Z.mod_small. unfold ASAN_CEIL in *; lia. }
assert (HEI : img_env VAL A_LIM (EF regs tv)) by (unfold EF; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs (F_extra tv)) (EF regs tv))
by (split; [intros nn Hnn; unfold EF;
first [ apply Eimg_low; unfold A_TEXT; lia
| symmetry; apply Eimg_low; unfold A_TEXT; lia ] | reflexivity]).
pose proof (F_ewx regs tv 0%nat ltac:(lia)) as EX0; cbn in EX0.
pose proof (F_ewx regs tv 1%nat ltac:(lia)) as EX1; cbn in EX1.
pose proof (F_ewx regs tv 2%nat ltac:(lia)) as EX2; cbn in EX2.
pose proof (F_ewx regs tv 3%nat ltac:(lia)) as EX3; cbn in EX3.
pose proof (F_ewx regs tv 4%nat ltac:(lia)) as EX4; cbn in EX4.
pose proof (F_ewx regs tv 5%nat ltac:(lia)) as EX5; cbn in EX5.
pose proof (F_ewx regs tv 6%nat ltac:(lia)) as EX6; cbn in EX6.
pose proof (F_ewx regs tv 7%nat ltac:(lia)) as EX7; cbn in EX7.
pose proof (F_ewx regs tv 8%nat ltac:(lia)) as EX8; cbn in EX8.
pose proof (F_ewx regs tv 9%nat ltac:(lia)) as EX9; cbn in EX9.
pose proof (F_ewx regs tv 10%nat ltac:(lia)) as EX10; cbn in EX10.
pose proof (Htvr 0%nat). pose proof (Htvr 1%nat). pose proof (Htvr 2%nat). pose proof (Htvr 3%nat).
pose proof (Htvr 4%nat). pose proof (Htvr 5%nat). pose proof (Htvr 6%nat). pose proof (Htvr 7%nat).
pose proof (Htvr 8%nat). pose proof (Htvr 9%nat). pose proof (Htvr 10%nat).
pose proof (Z.mod_pos_bound (tv 3%nat) 16 ltac:(lia)).
pose proof (Z.mod_pos_bound (tv 4%nat) 32 ltac:(lia)).
pose proof (Z.mod_pos_bound (tv 5%nat) 40 ltac:(lia)).
pose proof (Z.mod_pos_bound (tv 6%nat) 40 ltac:(lia)).
pose proof (Z.mod_pos_bound (tv 7%nat) 64 ltac:(lia)) as M7.
assert (M7' : 0 <= tv 7%nat mod 64 < 256) by lia.
assert (HMF64 : 0 <= mf < 2 ^ 64) by lia.
assert (AW1 : - STK <= mf - sp0 + 136) by lia.
assert (AW2 : mf - sp0 + 176 <= 0) by lia.
assert (OB1 : forall j, 0 <= j -> p <= p + c + j) by (intros; lia).
assert (VB : forall v, 0 <= v < 256 -> 0 <= v < 2 ^ (8 * Z.of_N 8)) by (intros; cbn; lia).
assert (SHOK : sh_ok SEGS F_Bx (@nil shent) (EF regs tv) (mrestrict (w_H W) mem)) by apply Forall_nil.
assert (ENTRY : forall (mm : nat) (bg : bool) (rr : Z),
(mm <= 11)%nat -> getr regs 18 = w64 rr ->
((mm = 0)%nat \/ (4096 <= p + c /\ p + c + Z.of_nat mm <= ASAN_CEIL)) ->
(bg = true -> 11 <= rr <= 2 ^ 26) ->
(forall j, (j < mm)%nat -> val_mem SEGS (mrestrict (w_H W) mem) (p + c + Z.of_nat j) 1 (tv j)) ->
st_ok_pi SEGS VAL (EF regs tv) (ss_F mm bg)
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + F_pc0)) mem (seg_rom SEGS)))).
{ intros mm bg rr Hmm H18 Hq Hbg Hby.
  exact (F_entry regs W mem mf (p + c) rr mm bg tv Hmm E9 E13 E26 H18 Hmfc Hmfhi Hmf32 Hpresw Hq Hbg Hby Htvr). }
unfold cfg_at. change (w64 (BASE + F_pc0)) with (Z_to_bv 64 (BASE + F_pc0)).
assert (CASE : n - c = 0 \/ n - c = 1 \/ n - c = 2 \/ n - c = 3 \/ n - c = 4 \/ n - c = 5 \/
n - c = 6 \/ n - c = 7 \/ n - c = 8 \/ n - c = 9 \/ n - c = 10 \/ 11 <= n - c) by lia.
destruct CASE as [Hr|[Hr|[Hr|[Hr|[Hr|[Hr|[Hr|[Hr|[Hr|[Hr|[Hr|Hr]]]]]]]]]]].
- rewrite Hr in E18.
  assert (OBR : forall j, 0 <= j < 0 -> p + c + j + 1 <= p + req_size n) by (intros; lia).
  assert (ZT : forall j, (0 <= j < 11)%nat -> tv j = 0) by (intros jj Hjj; apply Hzero; lia).
  Fx_entry ENTRY HPC Hbytes E18 0 0%nat false. Fx_pin E18 0.
  Fx_run U26 HAR Hin HBx Hin OB1 OBR EW9 HMF64 AW1 AW2 mf sp0 regs tv HAE Htvr ZT VB.
- rewrite Hr in E18. assert (Hn0 : 0 < n) by lia.
  assert (OBR : forall j, 0 <= j < 1 -> p + c + j + 1 <= p + req_size n) by (intros; lia).
  assert (ZT : forall j, (1 <= j < 11)%nat -> tv j = 0) by (intros jj Hjj; apply Hzero; lia).
  Fx_entry ENTRY HPC Hbytes E18 1 1%nat false. Fx_pin E18 1.
  Fx_run U26 HAR Hin HBx Hn0 OB1 OBR EW9 HMF64 AW1 AW2 mf sp0 regs tv HAE Htvr ZT VB.
- rewrite Hr in E18. assert (Hn0 : 0 < n) by lia.
  assert (OBR : forall j, 0 <= j < 2 -> p + c + j + 1 <= p + req_size n) by (intros; lia).
  assert (ZT : forall j, (2 <= j < 11)%nat -> tv j = 0) by (intros jj Hjj; apply Hzero; lia).
  Fx_entry ENTRY HPC Hbytes E18 2 2%nat false. Fx_pin E18 2.
  Fx_run U26 HAR Hin HBx Hn0 OB1 OBR EW9 HMF64 AW1 AW2 mf sp0 regs tv HAE Htvr ZT VB.
- rewrite Hr in E18. assert (Hn0 : 0 < n) by lia.
  assert (OBR : forall j, 0 <= j < 3 -> p + c + j + 1 <= p + req_size n) by (intros; lia).
  assert (ZT : forall j, (3 <= j < 11)%nat -> tv j = 0) by (intros jj Hjj; apply Hzero; lia).
  Fx_entry ENTRY HPC Hbytes E18 3 3%nat false. Fx_pin E18 3.
  Fx_run U26 HAR Hin HBx Hn0 OB1 OBR EW9 HMF64 AW1 AW2 mf sp0 regs tv HAE Htvr ZT VB.
- rewrite Hr in E18. assert (Hn0 : 0 < n) by lia.
  assert (OBR : forall j, 0 <= j < 4 -> p + c + j + 1 <= p + req_size n) by (intros; lia).
  assert (ZT : forall j, (4 <= j < 11)%nat -> tv j = 0) by (intros jj Hjj; apply Hzero; lia).
  Fx_entry ENTRY HPC Hbytes E18 4 4%nat false. Fx_pin E18 4.
  Fx_run U26 HAR Hin HBx Hn0 OB1 OBR EW9 HMF64 AW1 AW2 mf sp0 regs tv HAE Htvr ZT VB.
- rewrite Hr in E18. assert (Hn0 : 0 < n) by lia.
  assert (OBR : forall j, 0 <= j < 5 -> p + c + j + 1 <= p + req_size n) by (intros; lia).
  assert (ZT : forall j, (5 <= j < 11)%nat -> tv j = 0) by (intros jj Hjj; apply Hzero; lia).
  Fx_entry ENTRY HPC Hbytes E18 5 5%nat false. Fx_pin E18 5.
  Fx_run U26 HAR Hin HBx Hn0 OB1 OBR EW9 HMF64 AW1 AW2 mf sp0 regs tv HAE Htvr ZT VB.
- rewrite Hr in E18. assert (Hn0 : 0 < n) by lia.
  assert (OBR : forall j, 0 <= j < 6 -> p + c + j + 1 <= p + req_size n) by (intros; lia).
  assert (ZT : forall j, (6 <= j < 11)%nat -> tv j = 0) by (intros jj Hjj; apply Hzero; lia).
  Fx_entry ENTRY HPC Hbytes E18 6 6%nat false. Fx_pin E18 6.
  Fx_run U26 HAR Hin HBx Hn0 OB1 OBR EW9 HMF64 AW1 AW2 mf sp0 regs tv HAE Htvr ZT VB.
- rewrite Hr in E18. assert (Hn0 : 0 < n) by lia.
  assert (OBR : forall j, 0 <= j < 7 -> p + c + j + 1 <= p + req_size n) by (intros; lia).
  assert (ZT : forall j, (7 <= j < 11)%nat -> tv j = 0) by (intros jj Hjj; apply Hzero; lia).
  Fx_entry ENTRY HPC Hbytes E18 7 7%nat false. Fx_pin E18 7.
  Fx_run U26 HAR Hin HBx Hn0 OB1 OBR EW9 HMF64 AW1 AW2 mf sp0 regs tv HAE Htvr ZT VB.
- rewrite Hr in E18. assert (Hn0 : 0 < n) by lia.
  assert (OBR : forall j, 0 <= j < 8 -> p + c + j + 1 <= p + req_size n) by (intros; lia).
  assert (ZT : forall j, (8 <= j < 11)%nat -> tv j = 0) by (intros jj Hjj; apply Hzero; lia).
  Fx_entry ENTRY HPC Hbytes E18 8 8%nat false. Fx_pin E18 8.
  Fx_run U26 HAR Hin HBx Hn0 OB1 OBR EW9 HMF64 AW1 AW2 mf sp0 regs tv HAE Htvr ZT VB.
- rewrite Hr in E18. assert (Hn0 : 0 < n) by lia.
  assert (OBR : forall j, 0 <= j < 9 -> p + c + j + 1 <= p + req_size n) by (intros; lia).
  assert (ZT : forall j, (9 <= j < 11)%nat -> tv j = 0) by (intros jj Hjj; apply Hzero; lia).
  Fx_entry ENTRY HPC Hbytes E18 9 9%nat false. Fx_pin E18 9.
  Fx_run U26 HAR Hin HBx Hn0 OB1 OBR EW9 HMF64 AW1 AW2 mf sp0 regs tv HAE Htvr ZT VB.
- rewrite Hr in E18. assert (Hn0 : 0 < n) by lia.
  assert (OBR : forall j, 0 <= j < 10 -> p + c + j + 1 <= p + req_size n) by (intros; lia).
  assert (ZT : forall j, (10 <= j < 11)%nat -> tv j = 0) by (intros jj Hjj; apply Hzero; lia).
  Fx_entry ENTRY HPC Hbytes E18 10 10%nat false. Fx_pin E18 10.
  Fx_run U26 HAR Hin HBx Hn0 OB1 OBR EW9 HMF64 AW1 AW2 mf sp0 regs tv HAE Htvr ZT VB.
- assert (Hn0 : 0 < n) by lia.
  assert (OBR : forall j, 0 <= j < 11 -> p + c + j + 1 <= p + req_size n) by (intros; lia).
  Fx_entry ENTRY HPC Hbytes E18 (n - c) 11%nat true. Fx_norm.
  Fx_run U26 HAR Hin HBx Hn0 OB1 OBR EW9 HMF64 AW1 AW2 mf sp0 regs tv HAE Htvr Hzero VB.
Qed.

End h.

(* ---- the boundary: inv_E_end -> inv_F_end ---------------------------------------------------------------- *)
(* What the segment keeps: every byte outside the four machine-frame slots it writes. *)
Lemma kept_val_mem : forall (W : world SEGS) (m m' : word -> option byte) lo hi a (n : nat) v,
(forall x, 0 <= x < 2 ^ 64 -> ~ (lo <= x < hi) -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> (a + Z.of_nat n <= lo \/ hi <= a) ->
val_mem SEGS (mrestrict (w_H W) m) a n v -> val_mem SEGS (mrestrict (w_H W) m') a n v.
Proof.
intros W m m' lo hi a n v HK Ha Hn Hd Hv.
eapply val_mem_kept; [|exact Hv].
intros k Hk. apply HK; lia.
Qed.
Lemma kept_garr8 : forall (W : world SEGS) (m m' : word -> option byte) lo hi a (l : list Z),
(forall x, 0 <= x < 2 ^ 64 -> ~ (lo <= x < hi) -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
0 <= a -> a + Z.of_nat (length l) <= 2 ^ 64 -> (a + Z.of_nat (length l) <= lo \/ hi <= a) ->
garr8 SEGS (mrestrict (w_H W) m) a l -> garr8 SEGS (mrestrict (w_H W) m') a l.
Proof.
intros W m m' lo hi a l HK Ha Hn Hd Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
apply (kept_val_mem W m m' lo hi (a + Z.of_nat j) 1 _ HK); [lia | lia | lia | exact Hv].
Qed.
Lemma kept_zero_shadow : forall (W : world SEGS) (m m' : word -> option byte) lo hi a len,
(forall x, 0 <= x < 2 ^ 64 -> ~ (lo <= x < hi) -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
0 <= a / 8 -> SHADOW_OFF + a / 8 + len / 8 <= lo -> lo <= 2 ^ 64 ->
zero_shadow (aview SEGS (w_H W) m) SHADOW_OFF a len -> zero_shadow (aview SEGS (w_H W) m') SHADOW_OFF a len.
Proof.
intros W m m' lo hi a len HK Ha Hlo Hlo64 Hz i Hi. unfold shadow_of_addr in *.
rewrite HK; [apply Hz; exact Hi | unfold SHADOW_OFF in *; lia | lia].
Qed.
Lemma kept_block_shadow : forall (W : world SEGS) (m m' : word -> option byte) lo hi a len,
(forall x, 0 <= x < 2 ^ 64 -> ~ (lo <= x < hi) -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
0 <= a / 8 -> SHADOW_OFF + a / 8 + (len + 7) / 8 <= lo -> lo <= 2 ^ 64 ->
block_shadow (aview SEGS (w_H W) m) SHADOW_OFF a len -> block_shadow (aview SEGS (w_H W) m') SHADOW_OFF a len.
Proof.
intros W m m' lo hi a len HK Ha Hlo Hlo64 (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
intros i Hi. unfold shadow_of_addr in *.
rewrite HK; [apply H3; exact Hi | unfold SHADOW_OFF in *; lia | lia].
Qed.
(* The model's tail byte j is the input byte at the cursor plus j, or 0 past the end. *)
Lemma tb_mem : forall (pl : list byte) k, (k < length pl)%nat ->
nth k (map (fun b : byte => bv_unsigned b) pl) 0 = RcIdentModel.bz (RcIdentModel.nthb pl k).
Proof.
intros pl k Hk. unfold RcIdentModel.bz, RcIdentModel.nthb.
rewrite (nth_indep _ 0 (bv_unsigned (RcIdentModel.zb 0))) by (rewrite length_map; lia).
rewrite (map_nth (fun b : byte => bv_unsigned b)). reflexivity.
Qed.
Lemma tb_past : forall (pl : list byte) k, (length pl <= k)%nat -> RcIdentModel.bz (RcIdentModel.nthb pl k) = 0.
Proof. intros pl k Hk. unfold RcIdentModel.bz, RcIdentModel.nthb. rewrite nth_overflow by exact Hk. reflexivity. Qed.

Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
(* The Section of LLVMFuzzerTestOneInput_inv.v, in the same order. *)
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable LS : lib_shape.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
(* The two contract hypotheses the segment uses (LLVMFuzzerTestOneInput.v): the allocator's laws and the
   machine-stack window. The segment makes no call. *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HSTK : STK_LLVMF <= LLVMF_STK.

Theorem seg_F_holds : seg_F B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
asink_none ameta_inv arodata_okS.
Proof.
unfold seg_F. intros g pos mf W2 c2 HE.
unfold inv_E_end, acut in HE.
destruct HE as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfr & Hk & Hmo & Hmo2 & HC & HP).
pose proof HC as (R2 & R9 & R8 & Hmf & Hmf32 & R3 & R4 & R19 & V80 & V192 & V176 & Vra & Vs0 &
W9 & W18 & W19 & W20 & W21 & W22 & W23 & W24 & W25 & W26 & W27 & V24 & Vflag & Hpre & Hfds & Hfs & Hinp).
destruct HP as (Hid & Hhw & Hbl & Hid3 & Hidp & HFAM & R26 & R18 & R13).
pose proof Hpre as (_ & _ & _ & _ & Hinpd & Hlen & _).
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _ & _).
destruct Hstk as (_ & _ & Hceil & Hlo & Hhi & H47 & _).
pose proof asan_consts as (AC & _ & _ & _ & _).
assert (HSTK' : 336 <= LLVMF_STK) by (unfold STK_LLVMF, ASTACK in HSTK; lia).
assert (HmfA : alloc_ceiling <= mf) by lia.
assert (Hmf47 : mf + 320 <= 2 ^ 47) by lia.
(* the side-stack frame lies below the allocator ceiling *)
assert (HSF : 4096 <= SFa g pos /\ SFa g pos + 1024 <= alloc_ceiling).
{ assert (Hin4 : In (4, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
  pose proof (frames_bounds SEGS B LAWS ly2 S2 W2 mem2 md2 4 pos HAR Hin4) as (F1 & F2 & _).
  destruct Hly as (_ & _ & _ & _ & _ & HF & _).
  unfold SFa. replace (frame_addr (e_ly g) 4 pos) with (frame_addr ly2 4 pos) by (unfold frame_addr; rewrite HF; reflexivity).
  change (fs_frame_bytes 4) with 1024 in F2. split; lia. }
(* the input, the model's tail *)
assert (HcT : 0 <= SlotModel.cT (e_pl g) <= e_n g).
{ pose proof (SlotModel.rec_c_range (e_pl g) (SlotModel.nrecn (e_pl g))) as H. unfold SlotModel.nlen in H.
  unfold SlotModel.cT. lia. }
assert (Hn26 : e_n g < 2 ^ 26) by (destruct Hinpd as [[H0 _] | [H0 _]]; lia).
assert (HinB : 0 < e_n g -> In (e_p g, e_n g) (ablocks B ly2 S2)).
{ intros Hn0. destruct Hinpd as [[H0 _] | [_ Hin0]]; [lia|].
  destruct Hbl as [Hperm _]. cbn [app] in Hperm. exact (Permutation_in _ (Permutation_sym Hperm) Hin0). }
eapply SRr_mono.
{ change (BASE + 0xeec) with (BASE + F_pc0).
  apply (F_core B LAWS LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
  ly2 S2 W2 regs2 mem2 md2 (4 * Z.of_nat (m_nrec g)) mf (e_p g) (e_n g) (SlotModel.cT (e_pl g))
  (fun j => SlotModel.tb (e_pl g) (Z.of_nat j)) HJ HSTK' R9 R13 R26 R18 Hmf Hmf32 HcT Hn26 HinB).
  - intros j Hj Hlt. unfold SlotModel.tb, SlotModel.inb.
    destruct (garr8_nthZ SEGS (rd W2 mem2) (e_p g) (map (fun b : byte => bv_unsigned b) (e_pl g))
    (SlotModel.cT (e_pl g) + Z.of_nat j) Hinp ltac:(lia) ltac:(rewrite length_map; lia)) as [Hv _].
    rewrite tb_mem in Hv by lia. rewrite Z.add_assoc in Hv. exact Hv.
  - intros j Hj Hge. unfold SlotModel.tb, SlotModel.inb. apply tb_past. lia.
  - intros j. unfold SlotModel.tb. apply SlotModel.inb_range. }
cbv beta. intros W3 c3 _ HF.
destruct HF as (regs3 & mem3 & md3 & -> & -> & Hfds3 & Hfs3 & HJ3 & Hkr & Hkm &
V10 & V20 & V25 & V26' & V24' & V23' & V21' & V18' & M160 & M168 & M144 & M136).
assert (KR : forall r : bv 5, In r F_KEPT -> getr regs3 r = getr regs2 r) by exact Hkr.
assert (HKV : forall a (n : nat) v, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> (a + Z.of_nat n <= mf + 136 \/ mf + 176 <= a) ->
val_mem SEGS (rd W2 mem2) a n v -> val_mem SEGS (rd W2 mem3) a n v)
by (intros a n v H1 H2 H3; exact (kept_val_mem W2 mem2 mem3 (mf + 136) (mf + 176) a n v Hkm H1 H2 H3)).
assert (HKB : forall a (bs : list byte), 0 <= a -> a + Z.of_nat (length bs) <= mf + 136 ->
bytes_at8 W2 mem2 a bs -> bytes_at8 W2 mem3 a bs).
{ intros a bs H1 H2. unfold bytes_at8. apply (kept_garr8 W2 mem2 mem3 (mf + 136) (mf + 176) a _ Hkm H1);
  rewrite length_map; lia. }
assert (HKZ : forall a len, 0 <= a -> a + len <= 2 ^ 47 -> 0 <= len ->
sh_zero W2 mem2 a len -> sh_zero W2 mem3 a len).
{ intros a len H1 H2 H3. unfold sh_zero. apply (kept_zero_shadow W2 mem2 mem3 (mf + 136) (mf + 176) a len Hkm);
  [apply Z.div_pos; lia | unfold SHADOW_OFF; Z.div_mod_to_equations; lia | lia]. }
assert (HKS : forall a len, 0 <= a -> a + len <= 2 ^ 47 -> 0 <= len ->
sh_blk W2 mem2 a len -> sh_blk W2 mem3 a len).
{ intros a len H1 H2 H3. unfold sh_blk. apply (kept_block_shadow W2 mem2 mem3 (mf + 136) (mf + 176) a len Hkm);
  [apply Z.div_pos; lia | unfold SHADOW_OFF; Z.div_mod_to_equations; lia | lia]. }
assert (KIN : forall r : bv 5, In r F_KEPT -> getr regs3 r = getr regs2 r) by exact Hkr.
unfold inv_F_end, acut.
exists ly2, S2, regs3, mem3, md3.
split; [unfold F_pc1; reflexivity|].
split; [exact HJ3|]. split; [exact Hfr|]. split; [exact Hk|]. split; [exact Hmo|]. split; [exact Hmo2|].
destruct HSF as [HSF1 HSF2].
split.
- unfold ecommon.
  rewrite (KR 2%bv ltac:(cbn; tauto)), (KR 9%bv ltac:(cbn; tauto)), (KR 8%bv ltac:(cbn; tauto)),
  (KR 3%bv ltac:(cbn; tauto)), (KR 4%bv ltac:(cbn; tauto)), (KR 19%bv ltac:(cbn; tauto)).
  split; [exact R2|]. split; [exact R9|]. split; [exact R8|]. split; [exact Hmf|]. split; [exact Hmf32|].
  split; [exact R3|]. split; [exact R4|]. split; [exact R19|].
  split; [apply HKV; [lia | lia | lia | exact V80]|].
  split; [apply HKV; [lia | lia | lia | exact V192]|].
  split; [apply HKV; [lia | lia | lia | exact V176]|].
  split; [apply HKV; [lia | lia | lia | exact Vra]|].
  split; [apply HKV; [lia | lia | lia | exact Vs0]|].
  split; [apply HKV; [lia | lia | lia | exact W9]|].
  split; [apply HKV; [lia | lia | lia | exact W18]|].
  split; [apply HKV; [lia | lia | lia | exact W19]|].
  split; [apply HKV; [lia | lia | lia | exact W20]|].
  split; [apply HKV; [lia | lia | lia | exact W21]|].
  split; [apply HKV; [lia | lia | lia | exact W22]|].
  split; [apply HKV; [lia | lia | lia | exact W23]|].
  split; [apply HKV; [lia | lia | lia | exact W24]|].
  split; [apply HKV; [lia | lia | lia | exact W25]|].
  split; [apply HKV; [lia | lia | lia | exact W26]|].
  split; [apply HKV; [lia | lia | lia | exact W27]|].
  split; [apply HKV; [lia | lia | lia | exact V24]|].
  split; [apply HKV; [lia | lia | lia | exact Vflag]|].
  split; [exact Hpre|].
  split; [intros fd; rewrite Hfds3; apply Hfds|].
  split; [rewrite Hfs3; exact Hfs|].
  destruct Hinpd as [[Hn0 _] | [Hn0 Hin0]].
  + unfold bytes_at8. assert (Hl0 : e_pl g = []) by (destruct (e_pl g); [reflexivity | cbn in Hlen; lia]).
    rewrite Hl0. cbn [map]. apply garr8_nil.
  + pose proof (blk_bounds B ly2 S2 W2 mem2 md2 (e_p g) (e_n g) HAR (HinB ltac:(lia))) as [HB1 HB2].
    pose proof (req_size_pos (e_n g) ltac:(lia)). unfold ASAN_CEIL in HB2.
    apply HKB; [lia | lia | exact Hinp].
- destruct Hid as (Hid1 & Hid2 & Hid4). destruct Hhw as (Hhw1 & Hhw2 & Hhw3 & Hhw4).
  assert (Hidl : length (m_id g (m_nrec g)) = 38%nat) by (unfold m_id; apply SlotModel.rec_id_length).
  assert (Hhwl : (length (m_hwb g (m_nrec g)) <= 8)%nat).
  { unfold m_hwb, SlotModel.rec_hwb. destruct (SlotModel.rec_hw (e_pl g) (m_nrec g)) as [h|] eqn:Ehw.
    - pose proof (SlotModel.rec_hw_inv (e_pl g) (m_nrec g)) as Hi. rewrite Ehw in Hi. destruct Hi as [_ ->].
      unfold RcIdentModel.raw, RcIdentModel.get. rewrite length_firstn. unfold RcIdentModel.REAC_VER_LEN. lia.
    - rewrite repeat_length. lia. }
  assert (HVid : V_id = 352) by reflexivity. assert (HNid : N_id = 38) by reflexivity.
  assert (HVhw : V_hw = 432) by reflexivity. assert (HNhw : N_hw = 12) by reflexivity.
  split; [split; [apply HKB; [lia | rewrite Hidl; lia | exact Hid1]|];
    split; [apply HKZ; [lia | lia | lia | exact Hid2] | apply HKS; [lia | lia | lia | exact Hid4]]|].
  split; [split; [apply HKV; [lia | lia | lia | exact Hhw1]|];
    split; [apply HKB; [lia | lia | exact Hhw2]|];
    split; [apply HKZ; [lia | lia | lia | exact Hhw3] | apply HKS; [lia | lia | lia | exact Hhw4]]|].
  split; [exact Hbl|].
  split; [apply HKV; [lia | lia | lia | exact Hid3]|].
  split; [apply HKV; [lia | lia | lia | exact Hidp]|].
  split; [exact V10|]. split; [exact V20|]. split; [exact V25|]. split; [exact V26'|].
  split; [exact V24'|]. split; [exact V23'|]. split; [exact V21'|]. split; [exact V18'|].
  split; [exact M160|]. split; [exact M168|]. split; [exact M144|]. exact M136.
Qed.
End c.
End b.
End a.
