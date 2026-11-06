(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACes.v:275-278
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACfk.v:194-195 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACh9.v:115-118 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:1570-1572, 1593-1598, 1605-1613 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* The tools and the proved pieces of segment K of LLVMFuzzerTestOneInput's ASan walk (fuzz_identity.asan 0x81e60 .. 0x82090, listing offsets
   0x1754 .. 0x1984, 140 slots). seg_K_holds itself is in LLVMFuzzerTestOneInput_K.v, which composes the pieces of
   this file (k_rne, k_pairA, k_pairC; seg_K_of_pieces) with the helper lanes' k_pairB, k_cmp, k_token_loop and
   k_cat_tail; those lanes Require this file for its tools (k_heap_str, aj_strlen_at, k_call_afn, k_ok_mf,
   k_garr8_moved, k_bytes_aview, k_pres, k_sextw).

   The code is the harness's `if (r == 0) { ... }` block (projects/libreac/fuzz_identity/source/fuzz_identity.c:479):
     0x81e60 the use-after-scope unpoisoning of `w4`, then `bnez s11` (r <> 0: straight to K's end 0x82090);
     0x81e6c .. 0x81eb4 three strlen / check_str pairs, on nm (mf+184, cap mf+152), tk (x21, cap x20) and
                        dp (x22, cap mf+144);
     0x81eb8 .. 0x81ed8 strcmp (nm, exp_nm = SF+V_nm) and strcmp (dp, exp_dp = SF+V_dp), each must return 0;
     0x81edc .. 0x81f9c the token loop: tk is nm lower-cased with its first '-' dropped;
     0x81fa0 .. 0x81fac the scope byte of `count` and reac_box_catalogue (&count);
     0x81fb0 .. 0x82084 the catalogue row (row mod count), reac_box_catalogue_defect, and the entry's own
                        expected mask (the row's widths at +16 / +20 and, when its display pointer is not null,
                        strcmp (e->display, dp)); the two masks must agree;
     0x82088 the re-poisoning of `count`, 0x82090 K's end.
   Every error branch (__asan_report_*, abort at 0x822f0) is refuted: the frame's shadow is zero where the walk
   reads it (inv_J_end's sh_zero of nm / dp), the heap buffers' shadow is the allocator's (AR_shadow_law), and
   the model (lib/Prog/SlotModel.v, box_name's n_TK and n_EXP_NM / n_EXP_DP) decides every compare. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String Ascii.
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
PaRun PaShadow PaJournal IdentSyms IdentList IdentPa IdentPaLib IdentBase IdentFrame IdentCJ IdentRo
IdentProgSig IdentBlkTail YC1g YC1h YC45 YC4b YC81 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Rt Require Import StrlenDef WrapRo.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import AStrcmpDef.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YK1g.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv LLVMFuzzerTestOneInput_Kcut.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel IdentSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* YC4b turns lia's division and modulo handling off; this segment's addresses need it (shadow_addr, the
   8-byte word of a string's NUL). *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
Import RcIdentModel.
(* a register number is callee-saved (YG0d.v:20), for aregs_preserved *)
Ltac kcs := unfold acallee_saved; vm_compute; repeat (first [left; reflexivity | right]); try (split; discriminate).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.

(* A byte of a `bytes_at8` run, as the reader sees it. *)
Lemma k_bytes_aview : forall (W : world SEGS) mem a (bs : list byte) j,
bytes_at8 W mem a bs -> (j < length bs)%nat ->
aview SEGS (w_H W) mem (a + Z.of_nat j) = Some (bz (nthb bs j)).
Proof.
intros W mem a bs j Hb Hj. unfold bytes_at8, garr8 in Hb.
destruct (Hb j ltac:(rewrite length_map; exact Hj)) as [Hv Hr].
rewrite (aview_of_val_mem1 SEGS (w_H W) mem _ _ Hv Hr). f_equal.
unfold bz, nthb, zb.
rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; exact Hj).
rewrite map_nth. reflexivity.
Qed.

(* Everything the strlen / strcmp / check_str contracts ask of a NUL-terminated string that lies in a heap
   block of the run: its first zero byte is at its length, its bytes and their shadow are readable, and the
   bytes to the end of the NUL's word are present (IdentBlkTail.v). *)
Lemma k_heap_str : forall ly2 S2 (W2 : world SEGS) mem2 md2 p cap (s : list byte),
AR SEGS B ly2 S2 W2 mem2 md2 ->
In (p, cap) (ablocks B ly2 S2) ->
bytes_at8 W2 mem2 p (s ++ [zb 0]) -> nzl s ->
Z.of_nat (length s) + 1 <= req_size cap ->
first_byte SEGS W2 mem2 p (Z.of_nat (length s) + 1) 0 (Z.of_nat (length s)) /\
amem_range p (Z.of_nat (length s) + 1) /\
range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF p (Z.of_nat (length s) + 1) /\
shadow_hull_vis (aview SEGS (w_H W2) mem2) p (Z.of_nat (length s) + 1) /\
(forall a, p + Z.of_nat (length s) < a < p + Z.of_nat (length s) - (p + Z.of_nat (length s)) mod 8 + 8 ->
 aview SEGS (w_H W2) mem2 a <> None) /\
4096 <= p /\ p + Z.of_nat (length s) + 1 <= alloc_ceiling /\ in_app p (req_size cap).
Proof.
intros ly2 S2 W2 mem2 md2 p cap s HAR Hin Hb Hnz Hcap.
set (L := Z.of_nat (length s)) in *.
assert (EL : L = Z.of_nat (length s)) by reflexivity.
assert (HL : 0 <= L) by lia.
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 p cap HAR Hin) as (H16 & H4096 & Hceil & Happ & Hpres & _ & Hn).
destruct (al_shadow _ _ LAWS ly2 S2 W2 mem2 md2 p cap HAR Hin) as [Hbs Hhull].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hlen : length (s ++ [zb 0]) = S (length s)) by (rewrite length_app; cbn [length]; lia).
(* the bytes before the NUL are nonzero, the byte at L is the NUL *)
assert (Hlt : forall i, 0 <= i < L -> exists b, aview SEGS (w_H W2) mem2 (p + i) = Some b /\ b <> 0).
{ intros i Hi. exists (bz (nthb (s ++ [zb 0]) (Z.to_nat i))).
  split.
  - replace (p + i) with (p + Z.of_nat (Z.to_nat i)) by lia.
    apply (k_bytes_aview W2 mem2 p (s ++ [zb 0]) (Z.to_nat i) Hb). rewrite Hlen. unfold L in Hi. lia.
  - unfold nthb. rewrite app_nth1 by (unfold L in Hi; lia).
    revert Hi. unfold L. intros Hi.
    apply (proj1 (Forall_forall _ _) Hnz). apply nth_In. lia. }
assert (Hat : aview SEGS (w_H W2) mem2 (p + L) = Some 0).
{ replace (p + L) with (p + Z.of_nat (length s)) by (lia).
  rewrite (k_bytes_aview W2 mem2 p (s ++ [zb 0]) (length s) Hb ltac:(rewrite Hlen; lia)).
  f_equal. unfold nthb. rewrite nth_middle. reflexivity. }
assert (Hreq : req_size cap <= cap \/ cap = 0) by (unfold req_size; destruct (Z.eqb_spec cap 0); lia).
split; [split; [lia | split; [exact Hlt | intros _; exact Hat]]|].
split; [apply (amem_range_sub_app p (req_size cap) p (L + 1) Happ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))|].
split; [exact (block_shadow_range _ SHADOW_OFF p (req_size cap) p (L + 1) Hbs ltac:(lia) ltac:(lia))|].
split; [intros x Hx; apply Hhull; revert Hx;
  pose proof (YCbq.shadow_mono p p ltac:(lia)) as M0;
  pose proof (YCbq.shadow_mono (p + L + 1 - 1) (p + req_size cap - 1) ltac:(lia)) as M1;
  unfold shadow_addr in *;
  assert (R8 : forall u v, u <= v -> u / 8 * 8 <= v / 8 * 8)
    by (intros u v Huv; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia);
  pose proof (R8 _ _ M1); lia|].
split.
{ intros a Ha. apply (blk_tail_present SEGS B LAWS ly2 S2 W2 mem2 md2 p cap L a HAR Hin ltac:(lia)).
  exact Ha. }
split; [exact H4096|]. split; [lia | exact Happ].
Qed.

(* The strlen wrapper in the journal form (as reac_box_catalogue_defect.v's aj_strcmp_at for strcmp). *)
Lemma aj_strlen_at : forall pc, astrlen_realizes SEGS B pc ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc kj x k (o : Z) raw,
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc kj ->
getr regsT 10 = w64 x -> 0 < x -> 0 <= k -> k + 1 < 2 ^ 32 -> x + k + 1 <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
first_byte SEGS W memT x (k + 1) 0 k ->
src_ok SEGS W regsT memT x (k + 1) ->
(forall a, x <= a <= x + k -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
amem_range x (k + 1) ->
range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF x (k + 1) ->
shadow_hull_vis (aview SEGS (w_H W) memT) x (k + 1) ->
(forall a, x + k < a < x + k - (x + k) mod 8 + 8 -> aview SEGS (w_H W) memT a <> None) ->
aro_unowned SEGS B (aview SEGS (w_H W) memT) ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 kj /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 k /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros pc AM W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc kj x k o raw
HJ Ha0 Hx0 Hk0 Hk1 Hxk Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hfb Hsx Hbx Hmx Hrx Hhx Htl Hro.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (ESTACK = 4096) as Hes by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
assert (HPRE : ecall_pre SEGS B lyc Sc W regsT memT mdc).
{ eapply ecall_pre_at with (o := o); try eassumption; try zlia. rewrite Hra. exact Hraw. }
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (Hlo2 : ly_stk_lo lyc + 2 * ESTACK <= spZ regsT) by (rewrite Eslo, Hsp'; zlia).
assert (Hpres2E : forall a, spZ regsT - 2 * ESTACK <= a < spZ regsT -> apresent (w_H W) memT a)
  by (intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia).
eapply SRr_mono.
{ exact (AM lyc Sc W regsT memT mdc x k HPRE Hlo2 Hpres2E Ha0 Hx0 Hk0 Hk1 Hxk Hfb Hsx
    ltac:(rewrite Hsp'; exact Hbx) Hmx Hrx Hhx Htl Hro). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hfr & Hpres2).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write SEGS B LAWS pa_segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc kj mem2 md2
    (fun a => sp0 + o - 2 * ESTACK <= a < sp0 + o) Sc own HJ).
  - intros a Ha Hna. apply (Hfr a Ha). exact Hna.
  - exact Hpres2.
  - exact Hsame.
  - intros a Ha; left; left; zlia.
  - exact HAR2.
  - reflexivity. - reflexivity. - zlia. - exact Hfrs. - exact HQT. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hfr | exact Hpres2].
Qed.

(* ---- the walk's symbolic state at 0x81e60 ------------------------------------------------------------------
   Region 0: the machine-frame words the segment reads, on s1 (atom 9), read-only: mf+80 = SF (atom 39),
   mf+136 = row (32), mf+144 = cap_disp (33), mf+152 = cap_name (34), mf+160 = in (35), mf+168 = out (36),
   mf+176 = the shadow base (37), mf+184 = nm (38). Region 1: the frame's shadow on s3 (atom 19), writable at
   byte 86, which is `w4`'s scope byte (SF + 688 = SF + 8 * 86). *)
Definition k_mfr : YP09.region := YP09.mkRegion (Some 9%nat) 80 192 80 80
  [YP09.mkChunk 80 (CVal 8 (SOff 39 0)); YP09.mkChunk 136 (CVal 8 (SOff 32 0));
   YP09.mkChunk 144 (CVal 8 (SOff 33 0)); YP09.mkChunk 152 (CVal 8 (SOff 34 0));
   YP09.mkChunk 160 (CVal 8 (SOff 35 0)); YP09.mkChunk 168 (CVal 8 (SOff 36 0));
   YP09.mkChunk 176 (CVal 8 (SOff 37 0)); YP09.mkChunk 184 (CVal 8 (SOff 38 0))].
Definition k_shr : YP09.region := YP09.mkRegion (Some 19%nat) 0 128 86 87 [].
Definition k_ss0 : sstate := mkSS 0x1754 sr_atoms [k_mfr; k_shr] None (mkFacts [] [] []).
Definition k_extra (row cap_disp cap_name tin tout nm SF : Z) : list word :=
  map (Z_to_bv 64) [row; cap_disp; cap_name; tin; tout; SHADOW_OFF; nm; SF].

(* A byte run and a value move with the memory when the bytes they name did not change. *)
Lemma k_garr8_moved : forall (W : world SEGS) (m m' : word -> option byte) a l,
(forall k, 0 <= k < Z.of_nat (length l) -> aview SEGS (w_H W) m' (a + k) = aview SEGS (w_H W) m (a + k)) ->
garr8 SEGS (rd W m) a l -> garr8 SEGS (rd W m') a l.
Proof.
intros W m m' a l Hk Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
apply (val_mem_moved SEGS (w_H W) (w_H W) m m' (a + Z.of_nat j) (a + Z.of_nat j) 1 (nth j l 0)); [|exact Hv].
intros kk Hkk. replace (a + Z.of_nat j + kk) with (a + (Z.of_nat j + kk)) by lia. apply Hk. lia.
Qed.

(* n_r is the result of reac_box_name: 0 or -1 (SlotModel.v:139). *)
Lemma k_r_cases : forall inp, SlotModel.n_r inp = 0 \/ SlotModel.n_r inp = -1.
Proof. intro inp. unfold SlotModel.n_r. destruct (SlotModel.n_wok inp && SlotModel.n_fits inp); auto. Qed.

(* A call of a program function in the afn_pre form, inside the walk's journal: YCbq.aj_call with the call's sp
   given as sp0 + o directly (the walk's environment has atom 2 = the segment's sp, not the journal's sp0). *)
Lemma k_call_afn : forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k STK1 FP1 EV1 (o : Z) raw ch1 pc
(K : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
achain lyc (aview SEGS (w_H W) memT) (spZ regsT) (s0Z regsT) ch1 ->
(afn_pre SEGS B STK1 lyc Sc W regsT memT mdc ch1 ->
 SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom SEGS)) mdc)
 (fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
   c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
   ajournal SEGS B STK1 (spZ regsT) FP1 lyc Sc W memT mdc [] ly2 S2 W2 mem2 md2 EV1 /\
   aregs_preserved regsT regs2 /\ K ly2 S2 W2 regs2 mem2 md2)) ->
(forall a, inFP FP1 a -> (inFP FP a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
 in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
 c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
 ajournal SEGS B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + EV1) /\
 ajournal SEGS B STK1 (sp0 + o) FP1 lyc Sc W memT mdc [] ly2 S2 W2 mem2 md2 EV1 /\
 aregs_preserved regsT regs2 /\ K ly2 S2 W2 regs2 mem2 md2).
Proof.
intros W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k STK1 FP1 EV1 o raw ch1 pc K
HJ Hsp Hal Hneg Hstk1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hceil & Hslo & Hshi & H47 & _) & _ & HQT).
eapply SRr_mono.
{ apply Hcallee. eapply (afn_pre_at SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT STK1 o ch1);
  try eassumption. - rewrite Hra. exact Hraw. - unfold raZ. rewrite Hra. exact Hra4. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ1 & HP & HK).
exists ly2, S2, regs2, mem2, md2. split; [reflexivity|]. rewrite Hsp in HJ1.
split; [| split; [exact HJ1 | split; [exact HP | exact HK]]].
change own with ([] ++ own). eapply (ajournal_sub SEGS B LAWS pa_segs_low); [exact HJ | exact HJ1 | zlia | zlia | exact HF].
Qed.

(* A callee-saved register after a call. *)
Lemma k_pres : forall (regs regs' : bvmap 5 word) (r : bv 5), aregs_preserved regs regs' ->
acallee_saved (bv_unsigned r) -> getr regs' r = getr regs r.
Proof. intros regs regs' r H Hr. pose proof (H (bv_unsigned r) Hr) as E. rewrite !Z_to_bv_bv_unsigned in E. exact E. Qed.

(* sext.w of a small non-negative value is the value (the strlen result before check_str, 0x81e78). *)
Lemma k_sextw : forall L, 0 <= L < 2 ^ 31 ->
sext 64 (alu32 ALU_ADD (low32 (Z_to_bv 64 L)) (low32 (Z_to_bv 64 0))) = Z_to_bv 64 L.
Proof.
intros L HL. rewrite YK1g.aluw_addi_lit. apply bv_eq. rewrite v_addiw_small; rewrite ?unsigned_lit_small by lia; lia.
Qed.

(* The symbolic state at any slot between two calls of the segment: only the machine-frame words. *)
Definition k_ssm (off : Z) : sstate := mkSS off sr_atoms [k_mfr] None (mkFacts [] [] []).
Lemma k_ok_mf : forall (W : world SEGS) (regs : bvmap 5 word) mem off mf row cd cn tin tout nm SF,
getr regs 9 = w64 mf -> 0 <= mf -> mf + 192 <= 2 ^ 64 ->
val_mem SEGS (rd W mem) (mf + 80) 8 SF -> val_mem SEGS (rd W mem) (mf + 136) 8 row ->
val_mem SEGS (rd W mem) (mf + 144) 8 cd -> val_mem SEGS (rd W mem) (mf + 152) 8 cn ->
val_mem SEGS (rd W mem) (mf + 160) 8 tin -> val_mem SEGS (rd W mem) (mf + 168) 8 tout ->
val_mem SEGS (rd W mem) (mf + 176) 8 SHADOW_OFF -> val_mem SEGS (rd W mem) (mf + 184) 8 nm ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (k_extra row cd cn tin tout nm SF))) (k_ssm off)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + off)) mem (seg_rom SEGS))).
Proof.
intros W regs mem off mf row cd cn tin tout nm SF H9 Hm0 Hm1 V80 V136 V144 V152 V160 V168 V176 V184.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (k_extra row cd cn tin tout nm SF))).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (k_extra row cd cn tin tout nm SF)) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E9 : ew E 9 = getr regs 9) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 9 9%bv eq_refl)).
assert (CH : forall o a X j, (j < 8)%nat -> a = (32 + j)%nat ->
  nth j (k_extra row cd cn tin tout nm SF) (Z_to_bv 64 0) = Z_to_bv 64 X ->
  val_mem SEGS (rd W mem) (mf + o) 8 X ->
  YP09.chunk_ok SEGS E (rd W mem) mf {| c_off := o; YP09.c_val := CVal 8 (SOff a 0) |}).
{ intros o a X j Hj Ha HX HV. subst a.
  assert (Ea : ew E (32 + j)%nat = Z_to_bv 64 X)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_extra regs _ j); exact HX).
  apply (chunk_ok_val SEGS E _ mf o 8 (SOff (32 + j) 0) (X mod 2 ^ 64)).
  - cbn [sv_denot]. rewrite Ea, Z.add_0_r, Z_to_bv_bv_unsigned. symmetry. apply bv_eq.
    rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. lia.
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). apply Z.mod_pos_bound. lia.
  - cbn. lia.
  - intros kk Hkk. rewrite (HV kk Hkk). unfold YO0f.le_byte.
    assert (P : 2 ^ (8 * Z.of_nat 8) = 2 ^ 64) by reflexivity. rewrite !P, Z.mod_mod by lia. reflexivity. }
unfold k_ssm. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor].
  unfold k_mfr, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E9, H9. unfold w64. rewrite unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  repeat apply Forall_cons; try apply Forall_nil.
  + exact (CH 80 39%nat SF 7%nat ltac:(lia) eq_refl eq_refl V80).
  + exact (CH 136 32%nat row 0%nat ltac:(lia) eq_refl eq_refl V136).
  + exact (CH 144 33%nat cd 1%nat ltac:(lia) eq_refl eq_refl V144).
  + exact (CH 152 34%nat cn 2%nat ltac:(lia) eq_refl eq_refl V152).
  + exact (CH 160 35%nat tin 3%nat ltac:(lia) eq_refl eq_refl V160).
  + exact (CH 168 36%nat tout 4%nat ltac:(lia) eq_refl eq_refl V168).
  + exact (CH 176 37%nat SHADOW_OFF 5%nat ltac:(lia) eq_refl eq_refl V176).
  + exact (CH 184 38%nat nm 6%nat ltac:(lia) eq_refl eq_refl V184).
- cbn [pairwise_disjoint all_disjoint]. split; exact I.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. split; [exact I | split; exact I].
Qed.

Section d.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
#[local] Notation ECOMMON := (@ecommon rc PI B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation INV_J := (@inv_J_end fx rc SK PI B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation INV_K := (@inv_K_end fx rc SK PI B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
Hypothesis HSTK : STK_LLVMF <= LLVMF_STK.
Hypothesis TL : PALib B.
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Hypothesis HRO : forall rdr, arodata_okS SEGS B RLO RHI rdr -> arodata_okP SEGS pa_relro_lo pa_relro_hi B rdr.
Hypothesis PSIG : ident_prog_sig_ok (PI := PI).
Hypothesis ASTRLEN : astrlen_realizes SEGS B (SIGMA IS___interceptor_trampoline_strlen).
Hypothesis HCHK : check_str.tcheck_str_spec B.
Hypothesis AJ_NIL_IO : forall STK sp0 ly S (W : world SEGS) mem md own ly' S' W' mem' md' k,
ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
m_fds md' = m_fds md /\ m_fs md' = m_fs md.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let BR := paj_branch (PI := PI).

(* 0x81e60 .. 0x81e68 on the r <> 0 path: the scope byte of `w4` is unpoisoned and `bnez s11` jumps to K's end.
   Nothing else of the state moves, so inv_K_end holds with the journal of inv_J_end. *)
Theorem k_rne : forall g pos mf nm tk dp W2 c2,
INV_J g pos mf nm tk dp W2 c2 -> SlotModel.n_r (e_pl g) <> 0 ->
SRr SEGS W2 c2 (INV_K g pos mf nm tk dp).
Proof.
intros g pos mf nm tk dp W2 c2 HJend Hr.
destruct HJend as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfrs & Hk & MLE & MOK & HC & HP).
destruct HP as (HBL & Hwok & R27 & R26 & R24 & R20 & R21 & R22 & Vnm & Vcn & Vcd & Vin & Vout & Vrow &
  Bnm & Bdp & Znm & Zdp & Hr0).
destruct HC as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & Rs3 & V80 & V192 & V176 & Vra & Vs0 &
  W9 & W18 & W19 & W20 & W21 & W22 & W23 & W24 & W25 & W26 & W27 & Vmf24 & Vflag & HPRE & Hfds & Hfs & Hinb).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof pa_base_lo as HBLO. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity.
pose proof HSTK as HSTK'. unfold STK_LLVMF in HSTK'. assert (Has : ASTACK = 16384) by reflexivity.
pose proof HJ as (HAR2 & Hly2 & _ & _ & _ & Hfrs2 & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _ & Htop0 & Htop1).
pose proof Hly2 as (_ & _ & _ & _ & _ & EF & _).
set (sp0 := e_sp0 g) in *.
assert (EFa : frame_addr ly2 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF; reflexivity).
set (SF := SFa g pos) in *.
assert (Hin4 : In (4, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly2 S2 W2 mem2 md2 4 pos HAR2 Hin4) as (HSF0 & HSF1 & HSFapp).
destruct (frame_al64 SEGS B ly2 S2 W2 mem2 md2 4 pos HAR2 Hin4) as (HSF64 & _ & _).
rewrite EFa in HSF0, HSF1, HSFapp, HSF64. rewrite HFB in HSF1, HSFapp.
set (sh := shadow_addr SF) in *.
assert (Esh : sh = SHADOW_OFF + SF / 8) by reflexivity.
assert (Hmf0 : alloc_ceiling + 16384 <= mf) by (clear - Hmfb Hceil Hslo HSTK' Has; lia).
assert (Hsh1 : 0 <= sh /\ sh + 128 <= alloc_ceiling).
{ clear - Esh HSF0 HSF1 C1. clearbody sh SF. unfold SHADOW_OFF in Esh. lia. }
(* the environment: the eight machine-frame words the segment reads *)
remember (Eimg (Ereg regs2 (k_extra (SlotModel.t_row (e_pl g)) (SlotModel.t_cap_disp (e_pl g))
  (SlotModel.t_cap_name (e_pl g)) (SlotModel.t_in (e_pl g)) (SlotModel.t_out (e_pl g)) nm SF))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
  by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs2 (k_extra (SlotModel.t_row (e_pl g))
  (SlotModel.t_cap_disp (e_pl g)) (SlotModel.t_cap_name (e_pl g)) (SlotModel.t_in (e_pl g))
  (SlotModel.t_out (e_pl g)) nm SF)) n)
  by (intros n Hn; rewrite HE; apply Eimg_low; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 (SlotModel.t_row (e_pl g)))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (SlotModel.t_cap_disp (e_pl g)))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (SlotModel.t_cap_name (e_pl g)))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (SlotModel.t_in (e_pl g)))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 (SlotModel.t_out (e_pl g)))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 5)).
assert (E38 : ew E 38 = Z_to_bv 64 nm)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 6)).
assert (E39 : ew E 39 = Z_to_bv 64 SF)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 7)).
assert (ER : regs_ok E sr_atoms regs2) by (rewrite HE; apply regs_ok_Eimg_Ereg).
clear HE.
assert (U9 : bv_unsigned (ew E 9) = mf).
{ rewrite (EE 9%nat 9%bv eq_refl), Rs1. apply unsigned_lit_small. clear - Hmf0 H47 Hmfb Hshi C1. lia. }
assert (U19 : bv_unsigned (ew E 19) = sh).
{ rewrite (EE 19%nat 19%bv eq_refl), Rs3. apply unsigned_lit_small. clear - Hsh1 C1. lia. }
assert (CH : forall off a X, ew E a = Z_to_bv 64 X -> val_mem SEGS (rd W2 mem2) (mf + off) 8 X ->
  YP09.chunk_ok SEGS E (rd W2 mem2) mf {| c_off := off; YP09.c_val := CVal 8 (SOff a 0) |}).
{ intros off a X Ha HX. apply (chunk_ok_val SEGS E _ mf off 8 (SOff a 0) (X mod 2 ^ 64)).
  - cbn [sv_denot]. rewrite Ha, Z.add_0_r, Z_to_bv_bv_unsigned. symmetry. apply bv_eq.
    rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. lia.
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). apply Z.mod_pos_bound. lia.
  - cbn. lia.
  - intros kk Hkk. rewrite (HX kk Hkk). unfold YO0f.le_byte.
    assert (P : 2 ^ (8 * Z.of_nat 8) = 2 ^ 64) by reflexivity. rewrite !P, Z.mod_mod by lia. reflexivity. }
(* the symbolic state at 0x81e60 *)
assert (HS : st_ok_pi SEGS VAL E k_ss0
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x1754)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold k_ss0. apply pa_entry_st_ok_full.
  - exact ER.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + unfold k_mfr, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [clear - Hmf0 C1; lia|]. split; [clear - Hmf0 H47 Hmfb Hshi; unfold sp0 in *; lia|].
      split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * exact (CH 80 39%nat SF E39 V80).
      * exact (CH 136 32%nat _ E32 Vrow).
      * exact (CH 144 33%nat _ E33 Vcd).
      * exact (CH 152 34%nat _ E34 Vcn).
      * exact (CH 160 35%nat _ E35 Vin).
      * exact (CH 168 36%nat _ E36 Vout).
      * exact (CH 176 37%nat _ E37 V176).
      * exact (CH 184 38%nat _ E38 Vnm).
    + unfold k_shr, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U19. split; [clear - Hsh1; lia|]. split; [clear - Hsh1 C1; lia|].
      split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS).
      apply (proj1 (awr_byte_present SEGS B LAWS LLVMF_STK sp0 [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g)
        [(4, pos)] ly2 S2 W2 mem2 md2 (4 * Z.of_nat (m_nrec g) + 7) (sh + o) HJ ltac:(
        right; right; right; exists 4, pos; split; [left; reflexivity|]; right;
        unfold in_zr; cbn [fst snd]; rewrite EFa, HFB; fold sh; clear - Ho; lia))).
  - cbn [pairwise_disjoint all_disjoint]. split; [split; [|exact I] | split; exact I].
    unfold extent_disjoint, k_mfr, k_shr. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U19.
    right. clear - Hsh1 Hmf0. lia.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. split; [exact I | split; exact I]. }
unfold cfg_at. change (w64 (BASE + 0x1754)) with (Z_to_bv 64 (BASE + 0x1754)).
(* 0x81e60 .. 0x81e68: the scope store, then the branch on r *)
paj_run_sh RUNP HS HJ.
{ intros a (r & Hr' & Ha). unfold k_ss0 in Hr'. cbn [ss_mem In] in Hr'.
  destruct Hr' as [<- | [<- | []]]; unfold k_mfr, k_shr in Ha;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; [lia|].
  rewrite U19 in Ha. right; right; right. exists 4, pos. split; [left; reflexivity|]. right.
  unfold in_zr; cbn [fst snd]. rewrite EFa, HFB. fold sh. clear - Ha. lia. }
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sh + 86 <= a < sh + 87) ->
  aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hw.
  apply (kept_of_frame E _ (w_H W2) mem2 (ms_mem ms) (fun x => sh + 86 <= x < sh + 87) HFr); [|exact Ha|exact Hw].
  intros bb wlo whi aa Hin Hr'. unfold k_ss0, windows in Hin. cbn in Hin.
  destruct Hin as [Eq | [Eq | []]]; injection Eq as <- <- <-; cbn [base_val] in Hr';
  [rewrite U9 in Hr'; clear - Hr'; lia | rewrite U19 in Hr'; clear - Hr'; lia]. }
clear HF HFr HG.
(* the branch on r at 0x81e68 *)
prreg HS (27%bv : bv 5) Q27.
rewrite (EE 27%nat 27%bv eq_refl), R27 in Q27.
psrr_branch_pi RUNP BR HS.
- (* r <> 0: on to K's end at 0x82090 *)
  paj_run_to_sh RUNTOP HS HJ 0x1984.
  { intros a (r & Hr' & Ha). unfold k_ss0 in Hr'. cbn [ss_mem In] in Hr'.
    destruct Hr' as [<- | [<- | []]]; unfold k_mfr, k_shr in Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; [lia|].
    rewrite U19 in Ha. right; right; right. exists 4, pos. split; [left; reflexivity|]. right.
    unfold in_zr; cbn [fst snd]. rewrite EFa, HFB. fold sh. clear - Ha. lia. }
  assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sh + 86 <= a < sh + 87) ->
    aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W2) mem2 a).
  { intros a Ha Hw. rewrite <- (KEEP1 a Ha Hw).
    apply (kept_of_frame E _ (w_H W2) (ms_mem ms) (ms_mem ms0) (fun x => sh + 86 <= x < sh + 87) HFr);
    [|exact Ha|exact Hw].
    intros bb wlo whi aa Hin Hr'. unfold k_ss0, windows in Hin. cbn in Hin.
    destruct Hin as [Eq | [Eq | []]]; injection Eq as <- <- <-; cbn [base_val] in Hr';
    [rewrite U9 in Hr'; clear - Hr'; lia | rewrite U19 in Hr'; clear - Hr'; lia]. }
  (* the only byte the two runs wrote is the scope byte of `w4` in the frame's shadow *)
  assert (NSHm : forall a, mf - 2 * ESTACK <= a < sp0 -> ~ (sh + 86 <= a < sh + 87))
    by (intros a Ha [X Y]; clear - Ha X Y Hmf0 Hsh1 Hmfb; unfold ESTACK in *; lia).
  assert (NSH : forall a, SF <= a < SF + 1024 -> ~ (sh + 86 <= a < sh + 87)).
  { intros a Ha [X Y]. apply (fshadow_not_app SF 128 SF 1024 a);
    [exact HSF0 | clear - HSF1 C1; lia | exact HSFapp | rewrite Esh in X, Y; unfold SHADOW_OFF in X, Y;
     clear - X Y; lia | exact Ha]. }
  assert (VK : forall a (n : nat) v, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
    (forall kk, 0 <= kk < Z.of_nat n -> ~ (sh + 86 <= a + kk < sh + 87)) ->
    val_mem SEGS (rd W2 mem2) a n v -> val_mem SEGS (rd W2 (ms_mem ms0)) a n v).
  { intros a n v H0 H1 Hns Hv. eapply (val_mem_kept SEGS); [|exact Hv]. intros kk Hkk.
    apply KEEP2; [clear - H0 H1 Hkk; lia | apply Hns; lia]. }
  prreg HS (2%bv : bv 5) Q2. prreg HS (9%bv : bv 5) Q9. prreg HS (8%bv : bv 5) Q8.
  prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (19%bv : bv 5) Q19.
  prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22.
  rewrite (EE 2%nat 2%bv eq_refl), Rsp in Q2. rewrite (EE 9%nat 9%bv eq_refl), Rs1 in Q9.
  rewrite (EE 8%nat 8%bv eq_refl), Rs0 in Q8. rewrite (EE 3%nat 3%bv eq_refl), Rgp in Q3.
  rewrite (EE 4%nat 4%bv eq_refl), Rtp in Q4. rewrite (EE 19%nat 19%bv eq_refl), Rs3 in Q19.
  rewrite (EE 21%nat 21%bv eq_refl), R21 in Q21. rewrite (EE 22%nat 22%bv eq_refl), R22 in Q22.
  destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as [Efd Efs].
  (* the input block's bytes are kept: it is a heap block, the written byte is in the frame's shadow *)
  assert (HINP : forall kk, 0 <= kk < Z.of_nat (length (map (fun b : byte => bv_unsigned b) (e_pl g))) ->
    aview SEGS (w_H W2) (ms_mem ms0) (e_p g + kk) = aview SEGS (w_H W2) mem2 (e_p g + kk)).
  { intros kk Hkk. rewrite length_map in Hkk.
    unfold e_pre, tLLVMFuzzerTestOneInput_pre in HPRE.
    destruct HPRE as ((HAR0 & _) & _ & _ & _ & Hinp & Hlen & _).
    destruct Hinp as [[Hn0 _] | [[Hn0 Hn26] Hine]]; [rewrite <- Hlen in Hkk; lia|].
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hine) as (_ & Q4096 & Qceil & Qapp & _).
    pose proof (req_size_pos (e_n g) ltac:(lia)) as Hrq.
    apply KEEP2; [clear - Hkk Hlen Q4096 Qceil C1 Hrq; lia|].
    intros [X Y]. apply (fshadow_not_app SF 128 (e_p g) (req_size (e_n g)) (e_p g + kk));
    [exact HSF0 | clear - HSF1 C1; lia | exact Qapp
    | rewrite Esh in X, Y; unfold SHADOW_OFF in X, Y; clear - X Y; lia
    | clear - Hkk Hlen Hrq; lia]. }
  apply SRr_ret. unfold inv_K_end, acut. pmkst HS.
  exists ly2, S2, (ms_regs ms0), (ms_mem ms0),
    (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy md2) mat md2)) mat0
       (with_vm_backing (m_vm_lazy md2) mat md2)).
  split; [reflexivity|].
  split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|].
  split; [exact MLE|]. split; [exact MOK|].
  split.
  { unfold ecommon. change (e_sp0 g) with sp0. change (SFa g pos) with SF.
    split; [exact Q2|]. split; [exact Q9|]. split; [exact Q8|].
    split; [exact Hmfb|]. split; [exact Hmf32|]. split; [exact Q3|]. split; [exact Q4|].
    split; [exact Q19|].
    repeat match goal with
    | |- _ /\ _ => split
    | |- e_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => exact HPRE
    | |- forall fd, _ => intros fd; rewrite Efd; reflexivity
    | |- m_fs _ = _ => rewrite Efs; exact Hfs
    | |- m_fs _ = m_fs (e_md g) => exact Efs
    | |- bytes_at8 _ _ (e_p g) _ => unfold bytes_at8 in *;
        apply (k_garr8_moved W2 mem2 (ms_mem ms0) _ _ HINP Hinb)
    | |- val_mem _ _ (SF + 1016) _ _ => apply VK;
         [clear - HSF0; lia | clear - HSF1 C1; cbn; lia
         | intros kk Hkk; apply NSH; cbn in Hkk; clear - Hkk HSF0 HSF1; lia | exact Vflag]
    | |- val_mem _ _ ?a _ _ => apply VK;
         [clear - Hmf0 Hmfb C1; cbn; lia | clear - Hmf0 Hmfb Hceil Hshi H47 C1; cbn; lia
         | intros kk Hkk; apply NSHm; cbn in Hkk; clear - Hkk Hmf0 Hmfb; unfold ESTACK; lia | assumption]
    end. }
  split; [exact HBL|]. split; [exact Q22|]. split; [exact Q21|].
  apply VK; [clear - Hmf0 Hmfb C1; lia | clear - Hmf0 Hmfb Hceil Hshi H47 C1; cbn; lia
  | intros kk Hkk; apply NSHm; cbn in Hkk; clear - Hkk Hmf0 Hmfb; unfold ESTACK; lia | exact Vnm].
- (* r = 0: this lemma's hypothesis excludes it *)
  exfalso.
  assert (E27 : ew E 27 = w64 (SlotModel.n_r (e_pl g)))
    by (rewrite (EE 27%nat 27%bv eq_refl); exact R27).
  destruct (k_r_cases (e_pl g)) as [E0 | E0]; [exact (Hr E0)|].
  rewrite E0 in E27.
  rewrite branch_ne_U in Hc. apply negb_false_iff, Z.eqb_eq in Hc.
  rewrite U_SLit, U_SOff, E27 in Hc.
  unfold zcanon, M64, w64 in Hc. rewrite Z_to_bv_unsigned in Hc. unfold bv_wrap in Hc.
  change (bv_modulus 64) with (2 ^ 64) in Hc.
  rewrite Z.add_0_r, Z.mod_mod in Hc by lia.
  assert (HM : (-1) mod 2 ^ 64 = 2 ^ 64 - 1)
    by (rewrite <- (Z.mod_add (-1) 1 (2 ^ 64)) by lia; rewrite Z.mod_small by lia; lia).
  rewrite HM in Hc. change (0 mod 2 ^ 64) with 0 in Hc. lia.
Qed.

Theorem k_pairA : k_pairA_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS.
Proof.
intros g pos mf nm tk dp W2 regs2' mem2' md2' HJend Hr.
destruct HJend as (ly2 & S2 & regs2 & mem2 & md2 & Ecfg & HJ & Hfrs & Hk & MLE & MOK & HC & HP).
unfold cfg_at in Ecfg. injection Ecfg as -> -> ->.
destruct HP as (HBL & Hwok & R27 & R26 & R24 & R20 & R21 & R22 & Vnm & Vcn & Vcd & Vin & Vout & Vrow &
  Bnm & Bdp & Znm & Zdp & Hr0).
destruct HC as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & Rs3 & V80 & V192 & V176 & Vra & Vs0 &
  W9 & W18 & W19 & W20 & W21 & W22 & W23 & W24 & W25 & W26 & W27 & Vmf24 & Vflag & HPRE & Hfds & Hfs & Hinb).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof pa_base_lo as HBLO. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity.
pose proof HSTK as HSTK'. unfold STK_LLVMF in HSTK'. assert (Has : ASTACK = 16384) by reflexivity.
pose proof HJ as (HAR2 & Hly2 & _ & _ & _ & Hfrs2 & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _ & Htop0 & Htop1).
pose proof Hly2 as (_ & _ & _ & _ & _ & EF & _).
set (sp0 := e_sp0 g) in *.
assert (EFa : frame_addr ly2 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF; reflexivity).
set (SF := SFa g pos) in *.
assert (Hin4 : In (4, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly2 S2 W2 mem2 md2 4 pos HAR2 Hin4) as (HSF0 & HSF1 & HSFapp).
destruct (frame_al64 SEGS B ly2 S2 W2 mem2 md2 4 pos HAR2 Hin4) as (HSF64 & _ & _).
rewrite EFa in HSF0, HSF1, HSFapp, HSF64. rewrite HFB in HSF1, HSFapp.
set (sh := shadow_addr SF) in *.
assert (Esh : sh = SHADOW_OFF + SF / 8) by reflexivity.
assert (Hmf0 : alloc_ceiling + 16384 <= mf) by (clear - Hmfb Hceil Hslo HSTK' Has; lia).
assert (Hsh1 : 0 <= sh /\ sh + 128 <= alloc_ceiling).
{ clear - Esh HSF0 HSF1 C1. clearbody sh SF. unfold SHADOW_OFF in Esh. lia. }
(* the environment: the eight machine-frame words the segment reads *)
remember (Eimg (Ereg regs2 (k_extra (SlotModel.t_row (e_pl g)) (SlotModel.t_cap_disp (e_pl g))
  (SlotModel.t_cap_name (e_pl g)) (SlotModel.t_in (e_pl g)) (SlotModel.t_out (e_pl g)) nm SF))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
  by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs2 (k_extra (SlotModel.t_row (e_pl g))
  (SlotModel.t_cap_disp (e_pl g)) (SlotModel.t_cap_name (e_pl g)) (SlotModel.t_in (e_pl g))
  (SlotModel.t_out (e_pl g)) nm SF)) n)
  by (intros n Hn; rewrite HE; apply Eimg_low; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 (SlotModel.t_row (e_pl g)))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (SlotModel.t_cap_disp (e_pl g)))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (SlotModel.t_cap_name (e_pl g)))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (SlotModel.t_in (e_pl g)))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 (SlotModel.t_out (e_pl g)))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 5)).
assert (E38 : ew E 38 = Z_to_bv 64 nm)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 6)).
assert (E39 : ew E 39 = Z_to_bv 64 SF)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 7)).
assert (ER : regs_ok E sr_atoms regs2) by (rewrite HE; apply regs_ok_Eimg_Ereg).
clear HE.
assert (U9 : bv_unsigned (ew E 9) = mf).
{ rewrite (EE 9%nat 9%bv eq_refl), Rs1. apply unsigned_lit_small. clear - Hmf0 H47 Hmfb Hshi C1. lia. }
assert (U19 : bv_unsigned (ew E 19) = sh).
{ rewrite (EE 19%nat 19%bv eq_refl), Rs3. apply unsigned_lit_small. clear - Hsh1 C1. lia. }
assert (CH : forall off a X, ew E a = Z_to_bv 64 X -> val_mem SEGS (rd W2 mem2) (mf + off) 8 X ->
  YP09.chunk_ok SEGS E (rd W2 mem2) mf {| c_off := off; YP09.c_val := CVal 8 (SOff a 0) |}).
{ intros off a X Ha HX. apply (chunk_ok_val SEGS E _ mf off 8 (SOff a 0) (X mod 2 ^ 64)).
  - cbn [sv_denot]. rewrite Ha, Z.add_0_r, Z_to_bv_bv_unsigned. symmetry. apply bv_eq.
    rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. lia.
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). apply Z.mod_pos_bound. lia.
  - cbn. lia.
  - intros kk Hkk. rewrite (HX kk Hkk). unfold YO0f.le_byte.
    assert (P : 2 ^ (8 * Z.of_nat 8) = 2 ^ 64) by reflexivity. rewrite !P, Z.mod_mod by lia. reflexivity. }
(* the symbolic state at 0x81e60 *)
assert (HS : st_ok_pi SEGS VAL E k_ss0
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x1754)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold k_ss0. apply pa_entry_st_ok_full.
  - exact ER.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + unfold k_mfr, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [clear - Hmf0 C1; lia|]. split; [clear - Hmf0 H47 Hmfb Hshi; unfold sp0 in *; lia|].
      split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * exact (CH 80 39%nat SF E39 V80).
      * exact (CH 136 32%nat _ E32 Vrow).
      * exact (CH 144 33%nat _ E33 Vcd).
      * exact (CH 152 34%nat _ E34 Vcn).
      * exact (CH 160 35%nat _ E35 Vin).
      * exact (CH 168 36%nat _ E36 Vout).
      * exact (CH 176 37%nat _ E37 V176).
      * exact (CH 184 38%nat _ E38 Vnm).
    + unfold k_shr, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U19. split; [clear - Hsh1; lia|]. split; [clear - Hsh1 C1; lia|].
      split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS).
      apply (proj1 (awr_byte_present SEGS B LAWS LLVMF_STK sp0 [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g)
        [(4, pos)] ly2 S2 W2 mem2 md2 (4 * Z.of_nat (m_nrec g) + 7) (sh + o) HJ ltac:(
        right; right; right; exists 4, pos; split; [left; reflexivity|]; right;
        unfold in_zr; cbn [fst snd]; rewrite EFa, HFB; fold sh; clear - Ho; lia))).
  - cbn [pairwise_disjoint all_disjoint]. split; [split; [|exact I] | split; exact I].
    unfold extent_disjoint, k_mfr, k_shr. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U19.
    right. clear - Hsh1 Hmf0. lia.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. split; [exact I | split; exact I]. }
unfold cfg_at. change (w64 (BASE + 0x1754)) with (Z_to_bv 64 (BASE + 0x1754)).
(* 0x81e60 .. 0x81e68: the scope store, then the branch on r *)
paj_run_sh RUNP HS HJ.
{ intros a (r & Hr' & Ha). unfold k_ss0 in Hr'. cbn [ss_mem In] in Hr'.
  destruct Hr' as [<- | [<- | []]]; unfold k_mfr, k_shr in Ha;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; [lia|].
  rewrite U19 in Ha. right; right; right. exists 4, pos. split; [left; reflexivity|]. right.
  unfold in_zr; cbn [fst snd]. rewrite EFa, HFB. fold sh. clear - Ha. lia. }
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sh + 86 <= a < sh + 87) ->
  aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hw.
  apply (kept_of_frame E _ (w_H W2) mem2 (ms_mem ms) (fun x => sh + 86 <= x < sh + 87) HFr); [|exact Ha|exact Hw].
  intros bb wlo whi aa Hin Hr'. unfold k_ss0, windows in Hin. cbn in Hin.
  destruct Hin as [Eq | [Eq | []]]; injection Eq as <- <- <-; cbn [base_val] in Hr';
  [rewrite U9 in Hr'; clear - Hr'; lia | rewrite U19 in Hr'; clear - Hr'; lia]. }
clear HF HFr HG.
(* the branch on r at 0x81e68: r = 0 falls through *)
prreg HS (27%bv : bv 5) Q27.
assert (E27 : ew E 27 = w64 (SlotModel.n_r (e_pl g))) by (rewrite (EE 27%nat 27%bv eq_refl); exact R27).
psrr_branch_pi RUNP BR HS.
{ exfalso. rewrite branch_ne_U in Hc. apply negb_true_iff, Z.eqb_neq in Hc. apply Hc.
  rewrite U_SLit, U_SOff, E27, Hr. reflexivity. }
(* 0x81e6c .. 0x81e74: s2 := nm, a0 := s2, the strlen call *)
paj_run_shc RUNP RUNC HS HJ.
{ intros a (r & Hr' & Ha). cbn [ss_mem add_cond k_ss0 In] in Hr'.
  destruct Hr' as [<- | [<- | []]]; unfold k_mfr, k_shr in Ha;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; [lia|].
  rewrite U19 in Ha. right; right; right. exists 4, pos. split; [left; reflexivity|]. right.
  unfold in_zr; cbn [fst snd]. rewrite EFa, HFB. fold sh. clear - Ha. lia. }
assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sh + 86 <= a < sh + 87) ->
  aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hw. rewrite <- (KEEP1 a Ha Hw).
  apply (kept_of_frame E _ (w_H W2) (ms_mem ms) (ms_mem ms0) (fun x => sh + 86 <= x < sh + 87) HFr);
  [|exact Ha|exact Hw].
  intros bb wlo whi aa Hin Hr'. unfold windows in Hin. cbn in Hin.
  destruct Hin as [Eq | [Eq | []]]; injection Eq as <- <- <-; cbn [base_val] in Hr';
  [rewrite U9 in Hr'; clear - Hr'; lia | rewrite U19 in Hr'; clear - Hr'; lia]. }
clear HF HFr HG.
(* the heap blocks are apart from the frame's shadow *)
assert (HBM : forall p n, In (p, n) (ablocks B ly2 S2) -> forall a, p <= a < p + req_size n ->
  ~ (sh + 86 <= a < sh + 87)).
{ intros p n Hin a Ha [X Y].
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR2 Hin) as (_ & _ & _ & Happ & _).
  apply (fshadow_not_app SF 128 p (req_size n) a);
  [exact HSF0 | clear - HSF1 C1; lia | exact Happ | rewrite Esh in X, Y; unfold SHADOW_OFF in X, Y; clear - X Y; lia
  | exact Ha]. }
(* the model at r = 0 *)
destruct (k_r0 (e_pl g) Hr) as [Hwok' Hfits].
destruct (k_fits (e_pl g) Hfits) as (Fnm & Ftk & Fdp).
destruct (Hr0 Hr) as (Bnm0 & Btk0 & Bdp0).
assert (Hblk : forall x, In x (k_blocks g nm tk dp) -> In x (ablocks B ly2 S2)).
{ intros x Hx. destruct HBL as [Hperm _]. apply (Permutation_in _ (Permutation_sym Hperm)).
  apply in_or_app. left. exact Hx. }
assert (Inm : In (nm, Z.max (SlotModel.t_cap_name (e_pl g)) 1) (ablocks B ly2 S2))
  by (apply Hblk; unfold k_blocks; left; reflexivity).
(* the registers at the call *)
prreg HS (10%bv : bv 5) R10. prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2.
prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
prreg HS (8%bv : bv 5) C8. prreg HS (9%bv : bv 5) C9. prreg HS (18%bv : bv 5) C18.
prreg HS (19%bv : bv 5) C19. prreg HS (20%bv : bv 5) C20. prreg HS (21%bv : bv 5) C21.
prreg HS (22%bv : bv 5) C22. prreg HS (24%bv : bv 5) C24. prreg HS (26%bv : bv 5) C26.
prreg HS (27%bv : bv 5) C27.
rewrite E38 in R10. rewrite E38 in C18.
rewrite (EE 8%nat 8%bv eq_refl), Rs0 in C8. rewrite (EE 9%nat 9%bv eq_refl), Rs1 in C9.
rewrite (EE 19%nat 19%bv eq_refl), Rs3 in C19. rewrite (EE 20%nat 20%bv eq_refl), R20 in C20.
rewrite (EE 21%nat 21%bv eq_refl), R21 in C21. rewrite (EE 22%nat 22%bv eq_refl), R22 in C22.
rewrite (EE 24%nat 24%bv eq_refl), R24 in C24. rewrite (EE 26%nat 26%bv eq_refl), R26 in C26.
rewrite (EE 27%nat 27%bv eq_refl), R27, Hr in C27.
rewrite (EE 2%nat 2%bv eq_refl), Rsp in R2. rewrite (EE 3%nat 3%bv eq_refl), Rgp in R3.
rewrite (EE 4%nat 4%bv eq_refl), Rtp in R4.
pmkst HS.
pose proof HJ as (HARc & _).
set (L := length (SlotModel.n_EXP_NM (e_pl g))) in *.
assert (HLn : Z.of_nat L = SlotModel.n_ln (e_pl g)) by reflexivity.
pose proof (SlotModel.n_ln_le (e_pl g) Hwok') as HL21.
assert (Hcap1 : Z.of_nat L + 1 <= req_size (Z.max (SlotModel.t_cap_name (e_pl g)) 1))
  by (unfold req_size; destruct (Z.eqb_spec (Z.max (SlotModel.t_cap_name (e_pl g)) 1) 0); lia).
assert (HBnm : bytes_at8 W2 (ms_mem ms0) nm (SlotModel.n_EXP_NM (e_pl g) ++ [zb 0])).
{ unfold bytes_at8 in *. apply (k_garr8_moved W2 mem2 (ms_mem ms0) _ _); [|exact Bnm0].
  intros kk Hkk. rewrite length_map, length_app in Hkk. cbn [length] in Hkk. fold L in Hkk.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR2 Inm) as (_ & Q4096 & Qceil & _).
  apply KEEP2; [clear - Hkk Q4096 Qceil C1 Hcap1; lia|]. apply (HBM _ _ Inm). clear - Hkk Hcap1. lia. }
destruct (k_heap_str ly2 S2 W2 (ms_mem ms0) _ nm _ (SlotModel.n_EXP_NM (e_pl g)) HARc Inm HBnm
  (k_exp_nm_nz (e_pl g) Hwok') Hcap1) as (Hfb & Hmr & Hrx & Hhx & Htl & Hp0 & Hp1 & Happ).
fold L in Hfb, Hmr, Hrx, Hhx, Htl, Hp1.
assert (HROc : aro_unowned SEGS B (aview SEGS (w_H W2) (ms_mem ms0))).
{ pose proof HPRE as HPRE'. unfold e_pre, tLLVMFuzzerTestOneInput_pre in HPRE'.
  destruct HPRE' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAROS & _).
  exact (aro_unowned_of_arodata SEGS _ _ B _
    (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ (HRO _ HAROS))). }
assert (Usp : spZ (ms_regs ms0) = sp0 + (mf - sp0)).
{ unfold spZ. rewrite R2. unfold w64. rewrite unsigned_lit_small; [lia|]. clear - Hmf0 H47 Hmfb Hshi C1. lia. }
eapply SRr_bind.
{ refine (aj_strlen_at _ ASTRLEN W2 (ms_regs ms0) (ms_mem ms0) _ _ _ _ _ _ _ _ _ _ _ _ _ nm (Z.of_nat L)
    (mf - sp0) _ HJ R10 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(clear - Hp1 C1; lia) Usp
    ltac:(clear - Hmf32 Hsp0al; lia) ltac:(lia) ltac:(clear - Hmfb HSTK' Has; unfold ESTACK; lia) R3 R4 eq_refl _ Hfb _ _
    Hmr Hrx Hhx Htl HROc).
  - rewrite R1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. split.
    + destruct Hfb as (_ & Hlt & Hat). destruct (Z.lt_ge_cases a (nm + Z.of_nat L)) as [Hl | Hg].
      * destruct (Hlt (a - nm) ltac:(lia)) as (b & Hb & _). replace a with (nm + (a - nm)) by lia. rewrite Hb. discriminate.
      * replace a with (nm + Z.of_nat L) by lia. rewrite (Hat ltac:(lia)). discriminate.
    + rewrite Usp. clear - Ha Hp1 Hmf0. unfold ESTACK. lia.
  - intros a Ha. clear - Ha Hp1 Hmf0. unfold ESTACK. lia. }
cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & R10' & KEEPs & GROWs).
(* back at 0x81e78: the callee-saved registers and the memory outside strlen's window are those of the call *)
pose proof (k_pres _ _ 9%bv HP3 ltac:(kcs)) as P9. rewrite C9 in P9.
assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> ~ (mf - 2 * ESTACK <= a < mf) -> ~ (sh + 86 <= a < sh + 87) ->
  aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hw Hs. rewrite (KEEPs a Ha ltac:(replace (sp0 + (mf - sp0)) with mf by lia; exact Hw)).
  exact (KEEP2 a Ha Hs). }
assert (VM3 : forall o v, 0 <= o -> o + 8 <= 192 -> val_mem SEGS (rd W2 mem2) (mf + o) 8 v ->
  val_mem SEGS (rd W2 mem3) (mf + o) 8 v).
{ intros o v H0 H1 Hv. eapply (val_mem_kept SEGS); [|exact Hv]. intros kk Hkk. apply KEEP3.
  - clear - H0 H1 Hkk Hmf0 Hmfb Hshi H47 C1. lia.
  - clear - H0 Hkk. unfold ESTACK. lia.
  - clear - H0 Hkk Hmf0 Hsh1. lia. }
pose proof (k_ok_mf W2 regs3 mem3 0x176c mf _ _ _ _ _ nm SF P9 ltac:(clear - Hmf0 C1; lia)
  ltac:(clear - Hmf0 Hmfb Hshi H47 C1; lia)
  (VM3 80 _ ltac:(lia) ltac:(lia) V80) (VM3 136 _ ltac:(lia) ltac:(lia) Vrow)
  (VM3 144 _ ltac:(lia) ltac:(lia) Vcd) (VM3 152 _ ltac:(lia) ltac:(lia) Vcn)
  (VM3 160 _ ltac:(lia) ltac:(lia) Vin) (VM3 168 _ ltac:(lia) ltac:(lia) Vout)
  (VM3 176 _ ltac:(lia) ltac:(lia) V176) (VM3 184 _ ltac:(lia) ltac:(lia) Vnm)) as HS3.
rewrite R1.
remember (Eimg (Ereg regs3 (k_extra (SlotModel.t_row (e_pl g)) (SlotModel.t_cap_disp (e_pl g))
  (SlotModel.t_cap_name (e_pl g)) (SlotModel.t_in (e_pl g)) (SlotModel.t_out (e_pl g)) nm SF))) as E3 eqn:HE3.
assert (HEI3 : img_env VAL A_LIM E3) by (rewrite HE3; apply Eimg_env).
assert (EE3 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E3 n = getr regs3 r)
  by (intros n r Hn; rewrite HE3; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E3_34 : ew E3 34 = Z_to_bv 64 (SlotModel.t_cap_name (e_pl g)))
  by (rewrite HE3, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 2)).
clear HE3.
clear HS HEI. rename HS3 into HS. rename HEI3 into HEI.
(* 0x81e78 .. 0x81e84: a0 := sext.w len, a1 := nm, a2 := cap_name, the check_str call *)
paj_run_shc RUNP RUNC HS HJ3.
{ cbn [ss_mem k_ssm]. apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo k_mfr]; lia | apply awr_ok_nil]. }
prreg HS (10%bv : bv 5) X10. prreg HS (11%bv : bv 5) X11. prreg HS (12%bv : bv 5) X12. prreg HS (1%bv : bv 5) X1.
prreg HS (2%bv : bv 5) X2. prreg HS (3%bv : bv 5) X3. prreg HS (4%bv : bv 5) X4. prreg HS (8%bv : bv 5) X8.
rewrite (EE3 10%nat 10%bv eq_refl), R10' in X10. unfold w64 in X10. rewrite k_sextw in X10 by (clear - HL21 HLn; lia).
rewrite (EE3 18%nat 18%bv eq_refl), (k_pres _ _ 18%bv HP3 ltac:(kcs)), C18 in X11.
rewrite E3_34 in X12.
rewrite (EE3 2%nat 2%bv eq_refl), (k_pres _ _ 2%bv HP3 ltac:(kcs)), R2 in X2.
rewrite (EE3 3%nat 3%bv eq_refl), (k_pres _ _ 3%bv HP3 ltac:(kcs)), R3 in X3.
rewrite (EE3 4%nat 4%bv eq_refl), (k_pres _ _ 4%bv HP3 ltac:(kcs)), R4 in X4.
rewrite (EE3 8%nat 8%bv eq_refl), (k_pres _ _ 8%bv HP3 ltac:(kcs)), C8 in X8.
prreg HS (9%bv : bv 5) Y9. prreg HS (18%bv : bv 5) Y18. prreg HS (19%bv : bv 5) Y19. prreg HS (20%bv : bv 5) Y20.
prreg HS (21%bv : bv 5) Y21. prreg HS (22%bv : bv 5) Y22. prreg HS (24%bv : bv 5) Y24. prreg HS (26%bv : bv 5) Y26.
prreg HS (27%bv : bv 5) Y27.
rewrite (EE3 9%nat 9%bv eq_refl), (k_pres _ _ 9%bv HP3 ltac:(kcs)), C9 in Y9.
rewrite (EE3 18%nat 18%bv eq_refl), (k_pres _ _ 18%bv HP3 ltac:(kcs)), C18 in Y18.
rewrite (EE3 19%nat 19%bv eq_refl), (k_pres _ _ 19%bv HP3 ltac:(kcs)), C19 in Y19.
rewrite (EE3 20%nat 20%bv eq_refl), (k_pres _ _ 20%bv HP3 ltac:(kcs)), C20 in Y20.
rewrite (EE3 21%nat 21%bv eq_refl), (k_pres _ _ 21%bv HP3 ltac:(kcs)), C21 in Y21.
rewrite (EE3 22%nat 22%bv eq_refl), (k_pres _ _ 22%bv HP3 ltac:(kcs)), C22 in Y22.
rewrite (EE3 24%nat 24%bv eq_refl), (k_pres _ _ 24%bv HP3 ltac:(kcs)), C24 in Y24.
rewrite (EE3 26%nat 26%bv eq_refl), (k_pres _ _ 26%bv HP3 ltac:(kcs)), C26 in Y26.
rewrite (EE3 27%nat 27%bv eq_refl), (k_pres _ _ 27%bv HP3 ltac:(kcs)), C27 in Y27.
(* what the run to the call kept: everything (its one region is read-only) *)
assert (KEEP4 : forall a, 0 <= a < 2 ^ 64 -> ~ (mf - 2 * ESTACK <= a < mf) -> ~ (sh + 86 <= a < sh + 87) ->
  aview SEGS (w_H W2) (ms_mem ms1) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hw Hs. rewrite <- (KEEP3 a Ha Hw Hs).
  apply (kept_of_frame E3 _ (w_H W2) mem3 (ms_mem ms1) (fun _ => False) HFr); [|exact Ha|intros []].
  intros bb wlo whi aa Hin Hr'. unfold windows in Hin. cbn in Hin.
  destruct Hin as [Eq | []]. injection Eq as <- <- <-. clear - Hr'. lia. }
clear HF HFr HG.
pmkst HS.
rewrite (PSIG IS_check_str AF_check_str eq_refl).
(* the string facts again, at the call's memory *)
pose proof HJ3 as (HARc1 & _).
assert (HBnm1 : bytes_at8 W2 (ms_mem ms1) nm (SlotModel.n_EXP_NM (e_pl g) ++ [zb 0])).
{ unfold bytes_at8 in *. apply (k_garr8_moved W2 mem2 (ms_mem ms1) _ _); [|exact Bnm0].
  intros kk Hkk. rewrite length_map, length_app in Hkk. cbn [length] in Hkk. fold L in Hkk.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR2 Inm) as (_ & Q4096 & Qceil & _).
  apply KEEP4; [clear - Hkk Q4096 Qceil C1 Hcap1; lia | clear - Hkk Q4096 Qceil Hcap1 Hmf0; unfold ESTACK; lia |].
  apply (HBM _ _ Inm). clear - Hkk Hcap1. lia. }
destruct (k_heap_str ly2 S2 W2 (ms_mem ms1) _ nm _ (SlotModel.n_EXP_NM (e_pl g)) HARc1 Inm HBnm1
  (k_exp_nm_nz (e_pl g) Hwok') Hcap1) as (Gfb & Gmr & Grx & Ghx & Gtl & _ & _ & _).
fold L in Gfb, Gmr, Grx, Ghx, Gtl.
pose proof (blk_off_imgP B ly2 S2 W2 mem2 md2 nm _ HAR2 Inm) as Hoff.
assert (HROc1 : aro_unowned SEGS B (aview SEGS (w_H W2) (ms_mem ms1))).
{ pose proof HPRE as HPRE'. unfold e_pre, tLLVMFuzzerTestOneInput_pre in HPRE'.
  destruct HPRE' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAROS & _).
  exact (aro_unowned_of_arodata SEGS _ _ B _
    (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3 (HRO _ HAROS))). }
(* the call chain at the call: the entry's frame record on top of the entry's own chain (as D6) *)
pose proof HPRE as (HFN & Hraz & _).
pose proof HFN as (HAR0 & _ & Hra4 & _ & _ & Hstk0' & _ & Hch0 & _).
pose proof Hly2 as (_ & _ & _ & _ & _ & _ & _ & _ & ETop & _).
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & F1c & _).
assert (VK4 : forall a (n : nat) v, mf <= a -> a + Z.of_nat n <= sp0 ->
  val_mem SEGS (rd W2 mem2) a n v -> val_mem SEGS (rd W2 (ms_mem ms1)) a n v).
{ intros a n v H0 H1 Hv. eapply (val_mem_kept SEGS); [|exact Hv]. intros kk Hkk. apply KEEP4.
  - clear - H0 H1 Hkk Hmf0 Hshi H47 C1. lia.
  - clear - H0 Hkk. unfold ESTACK. lia.
  - clear - H0 Hkk Hmf0 Hsh1. lia. }
assert (HCH : exists ch, achain ly2 (aview SEGS (w_H W2) (ms_mem ms1)) mf sp0 ch).
{ change (spZ (e_regs g)) with sp0 in Hch0.
  assert (Hach : achain ly2 (aview SEGS (w_H (e_W g)) (e_mem g)) sp0 (s0Z (e_regs g)) []).
  { apply (achain_ly_top (e_ly g)); [exact ETop | exact Hch0]. }
  destruct (Z_lt_le_dec sp0 (ly_top ly2 - 16)) as [Hlt | Hge].
  - exists [(sp0, RA_LLVMF, s0Z (e_regs g))].
    pose proof (bv_unsigned_in_range 64 (getr (e_regs g) 1)) as Rra. change (bv_modulus 64) with (2 ^ 64) in Rra.
    pose proof (bv_unsigned_in_range 64 (getr (e_regs g) 8)) as Rs0r. change (bv_modulus 64) with (2 ^ 64) in Rs0r.
    apply (achain_push ly2 _ _ sp0 (s0Z (e_regs g)) RA_LLVMF [] mf Hach).
    + rewrite ETop. clear - Htop1 H47. lia.
    + intros a Ha. apply F1c; clear - Ha Hceil Hslo HSTK' Has; lia.
    + apply rdword_of_val_mem; [|unfold raZ in Hraz; clear - Hraz Rra; lia].
      apply VK4; [clear - Hmfb; lia | clear; cbn; lia | exact Vra].
    + apply rdword_of_val_mem; [|unfold s0Z; clear - Rs0r; lia].
      apply VK4; [clear - Hmfb; lia | clear; cbn; lia | exact Vs0].
    + rewrite <- Hraz. exact Hra4.
    + clear - Hceil Hslo HSTK' Has. lia.
    + clear - Hsp0al. lia.
    + exact Hlt.
    + clear - Hmfb. lia.
  - exists []. left. split; [right; left; exact Hge | reflexivity]. }
destruct HCH as (ch1 & Hchain).
assert (Usp1 : spZ (ms_regs ms1) = sp0 + (mf - sp0)).
{ unfold spZ. rewrite X2. unfold w64. rewrite unsigned_lit_small; [lia|]. clear - Hmf0 H47 Hmfb Hshi C1. lia. }
assert (Us01 : s0Z (ms_regs ms1) = sp0).
{ unfold s0Z. rewrite X8. unfold w64. apply unsigned_lit_small. clear - Hmf0 H47 Hmfb Hshi C1. lia. }
assert (HCSS : check_str.CHECK_STR_STK = 8208) by reflexivity.
eapply SRr_bind.
{ apply (k_call_afn W2 (ms_regs ms1) (ms_mem ms1) LLVMF_STK sp0 [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g)
    [(4, pos)] ly2 S2 _ _ check_str.CHECK_STR_STK [] 0 (mf - sp0) (getr (ms_regs ms1) 1) ch1 (BASE + AF_check_str)
    (fun ly' S' W' _ _ _ => ly' = ly2 /\ S' = S2 /\ W' = W2) HJ3 Usp1
    ltac:(clear - Hmf32 Hsp0al; lia) ltac:(lia) ltac:(rewrite HCSS; lia)
    ltac:(rewrite HCSS; clear - Hmfb HSTK' Has; lia) X3 X4 eq_refl).
  - rewrite X1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite X1. rewrite unsigned_lit_small by (clear - HBASE; lia). clear - HBLO. lia.
  - rewrite Usp1, Us01. replace (sp0 + (mf - sp0)) with mf by lia. exact Hchain.
  - intros HAFN.
    refine (HCHK ly2 S2 W2 (ms_regs ms1) (ms_mem ms1) _ ch1 (Z.of_nat L) nm (SlotModel.t_cap_name (e_pl g))
      HAFN HROc1 X10 X11 X12 ltac:(clear - HL21 HLn; lia) ltac:(pose proof (SlotModel.inb_range (e_pl g) (SlotModel.cT (e_pl g) + 5)); unfold SlotModel.t_cap_name, SlotModel.tb in *; pose proof (Z.mod_pos_bound (SlotModel.inb (e_pl g) (SlotModel.cT (e_pl g) + 5)) 40 ltac:(lia)); lia) _).
    intros _. unfold check_str.tcheck_str_ok.
    split; [clear - Fnm HLn; lia|]. split; [clear - Hp0; lia|].
    split; [clear - Hoff Hcap1; destruct Hoff; [left | right]; lia|].
    split; [exact Gfb|].
    split; [intros a Ha; rewrite Usp1; rewrite HCSS; clear - Ha Hp1 Hmf0; lia|].
    split; [exact Gmr|]. split; [exact Grx|]. split; [exact Ghx | exact Gtl].
  - intros a (r & Hr' & _). destruct Hr'. }
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HJc4 & HP4 & (-> & -> & ->)).
(* 0x81e88: kpre *)
apply SRr_ret. unfold kpre. split; [reflexivity|].
exists ly2, S2, regs4, mem4, md4.
split; [unfold cfg_at; rewrite X1; reflexivity|].
split; [replace (4 * Z.of_nat (m_nrec g) + 7) with (4 * Z.of_nat (m_nrec g) + 7 + 0) by lia; exact HJ4|].
split; [exact Hfrs|]. split; [exact MLE|]. split; [exact MOK|]. split; [exact HBL|].
pose proof HJc4 as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & G2 & _ & G4 & _).
split.
{ intros a Ha Hw. rewrite (G1 a Ha ltac:(rewrite HCSS in Hw |- *; clear - Hw; lia)).
  apply KEEP4; [clear - Ha C1; lia | rewrite HCSS in Hw; clear - Hw; unfold ESTACK; lia | clear - Ha Hsh1; lia]. }
split.
{ intros b n i Hin Hi. rewrite (G2 b n i Hin Hin Hi ltac:(intros (r & Hr' & _); destruct Hr')).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR2 Hin) as (_ & Q4096 & Qceil & _).
  apply KEEP4; [clear - Hi Q4096 Qceil C1; lia | clear - Hi Q4096 Qceil Hmf0; unfold ESTACK; lia
  | apply (HBM _ _ Hin); clear - Hi; lia]. }
split.
{ intros a Ha Hs. rewrite (G4 4 pos a ltac:(rewrite Hfrs; left; reflexivity) Ha ltac:(intros (r & Hr' & _); destruct Hr')).
  unfold in_zr, frame_rng in Ha. cbn [fst snd] in Ha. rewrite EFa, HFB in Ha. fold sh in Ha.
  apply KEEP4; [clear - Ha HSF0 HSF1 Hsh1 C1; lia | clear - Ha HSF1 Hsh1 Hmf0; unfold ESTACK; lia | exact Hs]. }
rewrite !(k_pres _ _ _ HP4) by kcs.
split; [exact X2|]. split; [exact Y9|]. split; [exact X8|]. split; [exact X3|]. split; [exact X4|].
split; [exact Y19|]. split; [exact Y18|]. split; [exact Y20|]. split; [exact Y21|]. split; [exact Y22|].
split; [exact Y24|]. split; [exact Y26 | exact Y27].
Qed.


(* 0x81ea0 .. 0x81eb8, from kpre: strlen (dp = x22), check_str (dp, its length, cap_disp = mf+144), kpre at
   BASE + 0x17ac. The same walk as k_pairA from its strlen on; the start state is kpre's (Fix A), so the start
   memory facts of inv_J_end reach the current memory through kpre's three keep clauses. *)
Theorem k_pairC : k_pairC_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS.
Proof.
intros g pos mf nm tk dp W2 regs2' mem2' md2' W c HJend Hr HK.
destruct HJend as (ly2 & S2 & regs2 & mem2 & md2 & Ecfg & HJ & Hfrs & Hk & MLE & MOK & HC & HP).
unfold cfg_at in Ecfg. injection Ecfg as -> -> ->.
destruct HP as (HBL & Hwok & R27 & R26 & R24 & R20 & R21 & R22 & Vnm & Vcn & Vcd & Vin & Vout & Vrow &
  Bnm & Bdp & Znm & Zdp & Hr0).
destruct HC as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & Rs3 & V80 & V192 & V176 & Vra & Vs0 &
  W9 & W18 & W19 & W20 & W21 & W22 & W23 & W24 & W25 & W26 & W27 & Vmf24 & Vflag & HPRE & Hfds & Hfs & Hinb).
destruct HK as (-> & lyk & Sk & regsk & memk & mdk & -> & HJk & Hfrsk & MLEk & MOKk & HBLk & K1 & K2 & K3 &
  Qk2 & Qk9 & Qk8 & Qk3 & Qk4 & Qk19 & Qk18 & Qk20 & Qk21 & Qk22 & Qk24 & Qk26 & Qk27).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof pa_base_lo as HBLO. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity.
pose proof HSTK as HSTK'. unfold STK_LLVMF in HSTK'. assert (Has : ASTACK = 16384) by reflexivity.
pose proof HJ as (HAR2 & Hly2 & _ & _ & _ & Hfrs2 & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _ & Htop0 & Htop1).
pose proof Hly2 as (_ & _ & _ & _ & _ & EF & _).
set (sp0 := e_sp0 g) in *.
assert (EFa : frame_addr ly2 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF; reflexivity).
set (SF := SFa g pos) in *.
assert (Hin4 : In (4, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly2 S2 W2 mem2 md2 4 pos HAR2 Hin4) as (HSF0 & HSF1 & HSFapp).
destruct (frame_al64 SEGS B ly2 S2 W2 mem2 md2 4 pos HAR2 Hin4) as (HSF64 & _ & _).
rewrite EFa in HSF0, HSF1, HSFapp, HSF64. rewrite HFB in HSF1, HSFapp.
set (sh := shadow_addr SF) in *.
assert (Esh : sh = SHADOW_OFF + SF / 8) by reflexivity.
assert (Hmf0 : alloc_ceiling + 16384 <= mf) by (clear - Hmfb Hceil Hslo HSTK' Has; lia).
assert (Hsh1 : 0 <= sh /\ sh + 128 <= alloc_ceiling).
{ clear - Esh HSF0 HSF1 C1. clearbody sh SF. unfold SHADOW_OFF in Esh. lia. }
(* the model at r = 0, and the display buffer *)
destruct (k_r0 (e_pl g) Hr) as [Hwok' Hfits].
destruct (k_fits (e_pl g) Hfits) as (Fnm & Ftk & Fdp).
destruct (Hr0 Hr) as (Bnm0 & Btk0 & Bdp0).
assert (Idp : In (dp, Z.max (SlotModel.t_cap_disp (e_pl g)) 1) (ablocks B lyk Sk)).
{ destruct HBLk as [Hperm _]. apply (Permutation_in _ (Permutation_sym Hperm)).
  apply in_or_app. left. unfold k_blocks. right; right; left; reflexivity. }
pose proof HJk as (HARk & Hlyk & _).
pose proof Hlyk as (_ & _ & _ & _ & _ & EFk & _).
assert (EFak : frame_addr lyk 4 pos = SF) by (unfold SF, SFa, frame_addr; rewrite EFk; reflexivity).
assert (HCSS : check_str.CHECK_STR_STK = 8208) by reflexivity.
(* the machine-frame words at the current memory (kpre's first clause) *)
assert (VMk : forall o v, 0 <= o -> o + 8 <= 192 -> val_mem SEGS (rd W2 mem2) (mf + o) 8 v ->
  val_mem SEGS (rd W2 memk) (mf + o) 8 v).
{ intros o v H0 H1 Hv. eapply (val_mem_kept SEGS); [|exact Hv]. intros kk Hkk. apply K1.
  - clear - H0 H1 Hkk Hmf0 Hmfb Hshi H47 C1. lia.
  - rewrite HCSS. clear - H0 Hkk. lia. }
(* the symbolic state at 0x81ea0 *)
pose proof (k_ok_mf W2 regsk memk 0x1794 mf _ _ _ _ _ nm SF Qk9 ltac:(clear - Hmf0 C1; lia)
  ltac:(clear - Hmf0 Hmfb Hshi H47 C1; lia)
  (VMk 80 _ ltac:(lia) ltac:(lia) V80) (VMk 136 _ ltac:(lia) ltac:(lia) Vrow)
  (VMk 144 _ ltac:(lia) ltac:(lia) Vcd) (VMk 152 _ ltac:(lia) ltac:(lia) Vcn)
  (VMk 160 _ ltac:(lia) ltac:(lia) Vin) (VMk 168 _ ltac:(lia) ltac:(lia) Vout)
  (VMk 176 _ ltac:(lia) ltac:(lia) V176) (VMk 184 _ ltac:(lia) ltac:(lia) Vnm)) as HS.
remember (Eimg (Ereg regsk (k_extra (SlotModel.t_row (e_pl g)) (SlotModel.t_cap_disp (e_pl g))
  (SlotModel.t_cap_name (e_pl g)) (SlotModel.t_in (e_pl g)) (SlotModel.t_out (e_pl g)) nm SF))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsk r)
  by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
clear HE.
unfold cfg_at. change (w64 (BASE + 0x1794)) with (Z_to_bv 64 (BASE + 0x1794)).
(* 0x81ea0 .. 0x81ea4: a0 := dp, the strlen call *)
paj_run_shc RUNP RUNC HS HJk.
{ cbn [ss_mem k_ssm]. apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo k_mfr]; lia | apply awr_ok_nil]. }
assert (KEEPr : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) memk a).
{ intros a Ha. apply (kept_of_frame E _ (w_H W2) memk (ms_mem ms) (fun _ => False) HFr); [|exact Ha|intros []].
  intros bb wlo whi aa Hin Hr'. unfold windows in Hin. cbn in Hin.
  destruct Hin as [Eq | []]. injection Eq as <- <- <-. clear - Hr'. lia. }
clear HF HFr HG.
prreg HS (10%bv : bv 5) R10. prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2.
prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
prreg HS (8%bv : bv 5) C8. prreg HS (9%bv : bv 5) C9. prreg HS (18%bv : bv 5) C18.
prreg HS (19%bv : bv 5) C19. prreg HS (20%bv : bv 5) C20. prreg HS (21%bv : bv 5) C21.
prreg HS (22%bv : bv 5) C22. prreg HS (24%bv : bv 5) C24. prreg HS (26%bv : bv 5) C26.
prreg HS (27%bv : bv 5) C27.
rewrite (EE 22%nat 22%bv eq_refl), Qk22 in R10.
rewrite (EE 8%nat 8%bv eq_refl), Qk8 in C8. rewrite (EE 9%nat 9%bv eq_refl), Qk9 in C9.
rewrite (EE 18%nat 18%bv eq_refl), Qk18 in C18.
rewrite (EE 19%nat 19%bv eq_refl), Qk19 in C19. rewrite (EE 20%nat 20%bv eq_refl), Qk20 in C20.
rewrite (EE 21%nat 21%bv eq_refl), Qk21 in C21. rewrite (EE 22%nat 22%bv eq_refl), Qk22 in C22.
rewrite (EE 24%nat 24%bv eq_refl), Qk24 in C24. rewrite (EE 26%nat 26%bv eq_refl), Qk26 in C26.
rewrite (EE 27%nat 27%bv eq_refl), Qk27 in C27.
rewrite (EE 2%nat 2%bv eq_refl), Qk2 in R2. rewrite (EE 3%nat 3%bv eq_refl), Qk3 in R3.
rewrite (EE 4%nat 4%bv eq_refl), Qk4 in R4.
pmkst HS.
pose proof HJk as (HARc & _).
set (L := length (SlotModel.n_EXP_DP (e_pl g))) in *.
assert (HLn : Z.of_nat L = SlotModel.n_ld (e_pl g)) by reflexivity.
pose proof (SlotModel.n_ld_le (e_pl g) Hwok') as HL38.
assert (HL0 : 0 <= Z.of_nat L) by lia.
assert (Hcap1 : Z.of_nat L + 1 <= req_size (Z.max (SlotModel.t_cap_disp (e_pl g)) 1))
  by (unfold req_size; destruct (Z.eqb_spec (Z.max (SlotModel.t_cap_disp (e_pl g)) 1) 0); lia).
(* dp's bytes at the call: kpre's second clause, then the run (which wrote nothing) *)
assert (HBdp : bytes_at8 W2 (ms_mem ms) dp (SlotModel.n_EXP_DP (e_pl g) ++ [zb 0])).
{ unfold bytes_at8 in *. apply (k_garr8_moved W2 mem2 (ms_mem ms) _ _); [|exact Bdp0].
  intros kk Hkk. rewrite length_map, length_app in Hkk. cbn [length] in Hkk. fold L in Hkk.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARk Idp) as (_ & Q4096 & Qceil & _).
  rewrite KEEPr by (clear - Hkk Q4096 Qceil C1 Hcap1; lia).
  apply (K2 dp _ kk Idp). clear - Hkk Hcap1. lia. }
destruct (k_heap_str lyk Sk W2 (ms_mem ms) _ dp _ (SlotModel.n_EXP_DP (e_pl g)) HARc Idp HBdp
  (k_exp_dp_nz (e_pl g) Hwok') Hcap1) as (Hfb & Hmr & Hrx & Hhx & Htl & Hp0 & Hp1 & Happ).
fold L in Hfb, Hmr, Hrx, Hhx, Htl, Hp1.
assert (HROc : aro_unowned SEGS B (aview SEGS (w_H W2) (ms_mem ms))).
{ pose proof HPRE as HPRE'. unfold e_pre, tLLVMFuzzerTestOneInput_pre in HPRE'.
  destruct HPRE' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAROS & _).
  exact (aro_unowned_of_arodata SEGS _ _ B _
    (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJk (HRO _ HAROS))). }
assert (Usp : spZ (ms_regs ms) = sp0 + (mf - sp0)).
{ unfold spZ. rewrite R2. unfold w64. rewrite unsigned_lit_small; [lia|]. clear - Hmf0 H47 Hmfb Hshi C1. lia. }
eapply SRr_bind.
{ refine (aj_strlen_at _ ASTRLEN W2 (ms_regs ms) (ms_mem ms) _ _ _ _ _ _ _ _ _ _ _ _ _ dp (Z.of_nat L)
    (mf - sp0) _ HJk R10 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(clear - Hp1 C1; lia) Usp
    ltac:(clear - Hmf32 Hsp0al; lia) ltac:(lia) ltac:(clear - Hmfb HSTK' Has; unfold ESTACK; lia) R3 R4 eq_refl _ Hfb _ _
    Hmr Hrx Hhx Htl HROc).
  - rewrite R1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. split.
    + destruct Hfb as (_ & Hlt & Hat). destruct (Z.lt_ge_cases a (dp + Z.of_nat L)) as [Hl | Hg].
      * destruct (Hlt (a - dp) ltac:(lia)) as (b & Hb & _). replace a with (dp + (a - dp)) by lia. rewrite Hb. discriminate.
      * replace a with (dp + Z.of_nat L) by lia. rewrite (Hat ltac:(lia)). discriminate.
    + rewrite Usp. clear - Ha Hp1 Hmf0. unfold ESTACK. lia.
  - intros a Ha. clear - Ha Hp1 Hmf0. unfold ESTACK. lia. }
cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & R10' & KEEPs & GROWs).
(* back at 0x81ea8: the callee-saved registers and the memory outside strlen's window are those of the call *)
pose proof (k_pres _ _ 9%bv HP3 ltac:(kcs)) as P9. rewrite C9 in P9.
assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> ~ (mf - 2 * ESTACK <= a < mf) ->
  aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) memk a).
{ intros a Ha Hw. rewrite (KEEPs a Ha ltac:(replace (sp0 + (mf - sp0)) with mf by lia; exact Hw)).
  exact (KEEPr a Ha). }
assert (VM3 : forall o v, 0 <= o -> o + 8 <= 192 -> val_mem SEGS (rd W2 mem2) (mf + o) 8 v ->
  val_mem SEGS (rd W2 mem3) (mf + o) 8 v).
{ intros o v H0 H1 Hv. pose proof (VMk o v H0 H1 Hv) as Hv'.
  eapply (val_mem_kept SEGS); [|exact Hv']. intros kk Hkk. apply KEEP3.
  - clear - H0 H1 Hkk Hmf0 Hmfb Hshi H47 C1. lia.
  - clear - H0 Hkk. unfold ESTACK. lia. }
pose proof (k_ok_mf W2 regs3 mem3 0x179c mf _ _ _ _ _ nm SF P9 ltac:(clear - Hmf0 C1; lia)
  ltac:(clear - Hmf0 Hmfb Hshi H47 C1; lia)
  (VM3 80 _ ltac:(lia) ltac:(lia) V80) (VM3 136 _ ltac:(lia) ltac:(lia) Vrow)
  (VM3 144 _ ltac:(lia) ltac:(lia) Vcd) (VM3 152 _ ltac:(lia) ltac:(lia) Vcn)
  (VM3 160 _ ltac:(lia) ltac:(lia) Vin) (VM3 168 _ ltac:(lia) ltac:(lia) Vout)
  (VM3 176 _ ltac:(lia) ltac:(lia) V176) (VM3 184 _ ltac:(lia) ltac:(lia) Vnm)) as HS3.
rewrite R1.
remember (Eimg (Ereg regs3 (k_extra (SlotModel.t_row (e_pl g)) (SlotModel.t_cap_disp (e_pl g))
  (SlotModel.t_cap_name (e_pl g)) (SlotModel.t_in (e_pl g)) (SlotModel.t_out (e_pl g)) nm SF))) as E3 eqn:HE3.
assert (HEI3 : img_env VAL A_LIM E3) by (rewrite HE3; apply Eimg_env).
assert (EE3 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E3 n = getr regs3 r)
  by (intros n r Hn; rewrite HE3; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E3_33 : ew E3 33 = Z_to_bv 64 (SlotModel.t_cap_disp (e_pl g)))
  by (rewrite HE3, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 1)).
clear HE3.
clear HS HEI. rename HS3 into HS. rename HEI3 into HEI.
(* 0x81ea8 .. 0x81eb4: a0 := sext.w len, a1 := dp, a2 := cap_disp (mf+144), the check_str call *)
paj_run_shc RUNP RUNC HS HJ3.
{ cbn [ss_mem k_ssm]. apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo k_mfr]; lia | apply awr_ok_nil]. }
prreg HS (10%bv : bv 5) X10. prreg HS (11%bv : bv 5) X11. prreg HS (12%bv : bv 5) X12. prreg HS (1%bv : bv 5) X1.
prreg HS (2%bv : bv 5) X2. prreg HS (3%bv : bv 5) X3. prreg HS (4%bv : bv 5) X4. prreg HS (8%bv : bv 5) X8.
rewrite (EE3 10%nat 10%bv eq_refl), R10' in X10. unfold w64 in X10. rewrite k_sextw in X10 by (clear - HL38 HLn HL0; lia).
rewrite (EE3 22%nat 22%bv eq_refl), (k_pres _ _ 22%bv HP3 ltac:(kcs)), C22 in X11.
rewrite E3_33 in X12.
rewrite (EE3 2%nat 2%bv eq_refl), (k_pres _ _ 2%bv HP3 ltac:(kcs)), R2 in X2.
rewrite (EE3 3%nat 3%bv eq_refl), (k_pres _ _ 3%bv HP3 ltac:(kcs)), R3 in X3.
rewrite (EE3 4%nat 4%bv eq_refl), (k_pres _ _ 4%bv HP3 ltac:(kcs)), R4 in X4.
rewrite (EE3 8%nat 8%bv eq_refl), (k_pres _ _ 8%bv HP3 ltac:(kcs)), C8 in X8.
prreg HS (9%bv : bv 5) Y9. prreg HS (18%bv : bv 5) Y18. prreg HS (19%bv : bv 5) Y19. prreg HS (20%bv : bv 5) Y20.
prreg HS (21%bv : bv 5) Y21. prreg HS (22%bv : bv 5) Y22. prreg HS (24%bv : bv 5) Y24. prreg HS (26%bv : bv 5) Y26.
prreg HS (27%bv : bv 5) Y27.
rewrite (EE3 9%nat 9%bv eq_refl), (k_pres _ _ 9%bv HP3 ltac:(kcs)), C9 in Y9.
rewrite (EE3 18%nat 18%bv eq_refl), (k_pres _ _ 18%bv HP3 ltac:(kcs)), C18 in Y18.
rewrite (EE3 19%nat 19%bv eq_refl), (k_pres _ _ 19%bv HP3 ltac:(kcs)), C19 in Y19.
rewrite (EE3 20%nat 20%bv eq_refl), (k_pres _ _ 20%bv HP3 ltac:(kcs)), C20 in Y20.
rewrite (EE3 21%nat 21%bv eq_refl), (k_pres _ _ 21%bv HP3 ltac:(kcs)), C21 in Y21.
rewrite (EE3 22%nat 22%bv eq_refl), (k_pres _ _ 22%bv HP3 ltac:(kcs)), C22 in Y22.
rewrite (EE3 24%nat 24%bv eq_refl), (k_pres _ _ 24%bv HP3 ltac:(kcs)), C24 in Y24.
rewrite (EE3 26%nat 26%bv eq_refl), (k_pres _ _ 26%bv HP3 ltac:(kcs)), C26 in Y26.
rewrite (EE3 27%nat 27%bv eq_refl), (k_pres _ _ 27%bv HP3 ltac:(kcs)), C27 in Y27.
(* what the run to the call kept: everything (its one region is read-only) *)
assert (KEEP4 : forall a, 0 <= a < 2 ^ 64 -> ~ (mf - 2 * ESTACK <= a < mf) ->
  aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W2) memk a).
{ intros a Ha Hw. rewrite <- (KEEP3 a Ha Hw).
  apply (kept_of_frame E3 _ (w_H W2) mem3 (ms_mem ms0) (fun _ => False) HFr); [|exact Ha|intros []].
  intros bb wlo whi aa Hin Hr'. unfold windows in Hin. cbn in Hin.
  destruct Hin as [Eq | []]. injection Eq as <- <- <-. clear - Hr'. lia. }
clear HF HFr HG.
pmkst HS.
rewrite (PSIG IS_check_str AF_check_str eq_refl).
(* the string facts again, at the call's memory *)
pose proof HJ3 as (HARc1 & _).
assert (HBdp1 : bytes_at8 W2 (ms_mem ms0) dp (SlotModel.n_EXP_DP (e_pl g) ++ [zb 0])).
{ unfold bytes_at8 in *. apply (k_garr8_moved W2 mem2 (ms_mem ms0) _ _); [|exact Bdp0].
  intros kk Hkk. rewrite length_map, length_app in Hkk. cbn [length] in Hkk. fold L in Hkk.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARk Idp) as (_ & Q4096 & Qceil & _).
  rewrite KEEP4 by (first [clear - Hkk Q4096 Qceil C1 Hcap1; lia | clear - Hkk Q4096 Qceil Hcap1 Hmf0; unfold ESTACK; lia]).
  apply (K2 dp _ kk Idp). clear - Hkk Hcap1. lia. }
destruct (k_heap_str lyk Sk W2 (ms_mem ms0) _ dp _ (SlotModel.n_EXP_DP (e_pl g)) HARc1 Idp HBdp1
  (k_exp_dp_nz (e_pl g) Hwok') Hcap1) as (Gfb & Gmr & Grx & Ghx & Gtl & _ & _ & _).
fold L in Gfb, Gmr, Grx, Ghx, Gtl.
pose proof (blk_off_imgP B lyk Sk W2 memk mdk dp _ HARk Idp) as Hoff.
assert (HROc1 : aro_unowned SEGS B (aview SEGS (w_H W2) (ms_mem ms0))).
{ pose proof HPRE as HPRE'. unfold e_pre, tLLVMFuzzerTestOneInput_pre in HPRE'.
  destruct HPRE' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAROS & _).
  exact (aro_unowned_of_arodata SEGS _ _ B _
    (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3 (HRO _ HAROS))). }
(* the call chain at the call: the entry's frame record on top of the entry's own chain (as D6) *)
pose proof HPRE as (HFN & Hraz & _).
pose proof HFN as (HAR0 & _ & Hra4 & _ & _ & Hstk0' & _ & Hch0 & _).
pose proof Hlyk as (_ & _ & _ & _ & _ & _ & _ & _ & ETop & _).
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & F1c & _).
assert (VK4 : forall a (n : nat) v, mf <= a -> a + Z.of_nat n <= sp0 ->
  val_mem SEGS (rd W2 mem2) a n v -> val_mem SEGS (rd W2 (ms_mem ms0)) a n v).
{ intros a n v H0 H1 Hv. eapply (val_mem_kept SEGS); [|exact Hv]. intros kk Hkk.
  rewrite KEEP4 by (first [clear - H0 H1 Hkk Hmf0 Hshi H47 C1; lia | clear - H0 Hkk; unfold ESTACK; lia]).
  apply K1; [clear - H0 H1 Hkk Hmf0 Hshi H47 C1; lia | rewrite HCSS; clear - H0 Hkk; lia]. }
assert (HCH : exists ch, achain lyk (aview SEGS (w_H W2) (ms_mem ms0)) mf sp0 ch).
{ change (spZ (e_regs g)) with sp0 in Hch0.
  assert (Hach : achain lyk (aview SEGS (w_H (e_W g)) (e_mem g)) sp0 (s0Z (e_regs g)) []).
  { apply (achain_ly_top (e_ly g)); [exact ETop | exact Hch0]. }
  destruct (Z_lt_le_dec sp0 (ly_top lyk - 16)) as [Hlt | Hge].
  - exists [(sp0, RA_LLVMF, s0Z (e_regs g))].
    pose proof (bv_unsigned_in_range 64 (getr (e_regs g) 1)) as Rra. change (bv_modulus 64) with (2 ^ 64) in Rra.
    pose proof (bv_unsigned_in_range 64 (getr (e_regs g) 8)) as Rs0r. change (bv_modulus 64) with (2 ^ 64) in Rs0r.
    apply (achain_push lyk _ _ sp0 (s0Z (e_regs g)) RA_LLVMF [] mf Hach).
    + rewrite ETop. clear - Htop1 H47. lia.
    + intros a Ha. apply F1c; clear - Ha Hceil Hslo HSTK' Has; lia.
    + apply rdword_of_val_mem; [|unfold raZ in Hraz; clear - Hraz Rra; lia].
      apply VK4; [clear - Hmfb; lia | clear; cbn; lia | exact Vra].
    + apply rdword_of_val_mem; [|unfold s0Z; clear - Rs0r; lia].
      apply VK4; [clear - Hmfb; lia | clear; cbn; lia | exact Vs0].
    + rewrite <- Hraz. exact Hra4.
    + clear - Hceil Hslo HSTK' Has. lia.
    + clear - Hsp0al. lia.
    + exact Hlt.
    + clear - Hmfb. lia.
  - exists []. left. split; [right; left; exact Hge | reflexivity]. }
destruct HCH as (ch1 & Hchain).
assert (Usp1 : spZ (ms_regs ms0) = sp0 + (mf - sp0)).
{ unfold spZ. rewrite X2. unfold w64. rewrite unsigned_lit_small; [lia|]. clear - Hmf0 H47 Hmfb Hshi C1. lia. }
assert (Us01 : s0Z (ms_regs ms0) = sp0).
{ unfold s0Z. rewrite X8. unfold w64. apply unsigned_lit_small. clear - Hmf0 H47 Hmfb Hshi C1. lia. }
eapply SRr_bind.
{ apply (k_call_afn W2 (ms_regs ms0) (ms_mem ms0) LLVMF_STK sp0 [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g)
    [(4, pos)] lyk Sk _ _ check_str.CHECK_STR_STK [] 0 (mf - sp0) (getr (ms_regs ms0) 1) ch1 (BASE + AF_check_str)
    (fun ly' S' W' _ _ _ => ly' = lyk /\ S' = Sk /\ W' = W2) HJ3 Usp1
    ltac:(clear - Hmf32 Hsp0al; lia) ltac:(lia) ltac:(rewrite HCSS; lia)
    ltac:(rewrite HCSS; clear - Hmfb HSTK' Has; lia) X3 X4 eq_refl).
  - rewrite X1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite X1. rewrite unsigned_lit_small by (clear - HBASE; lia). clear - HBLO. lia.
  - rewrite Usp1, Us01. replace (sp0 + (mf - sp0)) with mf by lia. exact Hchain.
  - intros HAFN.
    refine (HCHK lyk Sk W2 (ms_regs ms0) (ms_mem ms0) _ ch1 (Z.of_nat L) dp (SlotModel.t_cap_disp (e_pl g))
      HAFN HROc1 X10 X11 X12 ltac:(clear - HL38 HLn HL0; lia)
      ltac:(unfold SlotModel.t_cap_disp; pose proof (Z.mod_pos_bound (SlotModel.tb (e_pl g) 7) 64 ltac:(lia)); lia) _).
    intros _. unfold check_str.tcheck_str_ok.
    split; [clear - Fdp HLn; lia|]. split; [clear - Hp0; lia|].
    split; [clear - Hoff Hcap1; destruct Hoff; [left | right]; lia|].
    split; [exact Gfb|].
    split; [intros a Ha; rewrite Usp1; rewrite HCSS; clear - Ha Hp1 Hmf0; lia|].
    split; [exact Gmr|]. split; [exact Grx|]. split; [exact Ghx | exact Gtl].
  - intros a (r & Hr' & _). destruct Hr'. }
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HJc4 & HP4 & (-> & -> & ->)).
(* 0x81eb8: kpre *)
apply SRr_ret. unfold kpre. split; [reflexivity|].
exists lyk, Sk, regs4, mem4, md4.
split; [unfold cfg_at; rewrite X1; reflexivity|].
split; [replace (4 * Z.of_nat (m_nrec g) + 7) with (4 * Z.of_nat (m_nrec g) + 7 + 0) by lia; exact HJ4|].
split; [exact Hfrsk|]. split; [exact MLEk|]. split; [exact MOKk|]. split; [exact HBLk|].
pose proof HJc4 as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & G2 & _ & G4 & _).
split.
{ intros a Ha Hw. rewrite (G1 a Ha ltac:(rewrite HCSS in Hw |- *; clear - Hw; lia)).
  rewrite KEEP4 by (first [clear - Ha C1; lia | rewrite HCSS in Hw; clear - Hw; unfold ESTACK; lia]).
  exact (K1 a Ha Hw). }
split.
{ intros b n i Hin Hi. rewrite (G2 b n i Hin Hin Hi ltac:(intros (r & Hr' & _); destruct Hr')).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARk Hin) as (_ & Q4096 & Qceil & _).
  rewrite KEEP4 by (first [clear - Hi Q4096 Qceil C1; lia | clear - Hi Q4096 Qceil Hmf0; unfold ESTACK; lia]).
  exact (K2 b n i Hin Hi). }
split.
{ intros a Ha Hs. rewrite (G4 4 pos a ltac:(rewrite Hfrsk; left; reflexivity) Ha ltac:(intros (r & Hr' & _); destruct Hr')).
  assert (Ha' := Ha). unfold in_zr, frame_rng in Ha'. cbn [fst snd] in Ha'. rewrite EFak, HFB in Ha'. fold sh in Ha'.
  rewrite KEEP4 by (first [clear - Ha' HSF0 HSF1 Hsh1 C1; lia | clear - Ha' HSF1 Hsh1 Hmf0; unfold ESTACK; lia]).
  exact (K3 a Ha Hs). }
rewrite !(k_pres _ _ _ HP4) by kcs.
split; [exact X2|]. split; [exact Y9|]. split; [exact X8|]. split; [exact X3|]. split; [exact X4|].
split; [exact Y19|]. split; [exact Y18|]. split; [exact Y20|]. split; [exact Y21|]. split; [exact Y22|].
split; [exact Y24|]. split; [exact Y26 | exact Y27].
Qed.

(* seg_K from its pieces: the r <> 0 path (k_rne) and, for r = 0, k_pairA, the helper's k_pairB, k_pairC and the
   helper's k_cmp up to the loop head, the token loop and the catalogue tail. LLVMFuzzerTestOneInput_K.v applies this to
   the helpers' theorems. *)
Theorem seg_K_of_pieces :
  k_pairB_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv
    arodata_okS ->
  k_cmp_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv
    arodata_okS ->
  k_token_loop_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv
    arodata_okS ->
  k_cat_tail_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv
    arodata_okS ->
  seg_K B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv arodata_okS.
Proof.
intros HKB HKCMP HKTOK HKCAT g pos mf nm tk dp W2 c2 HJ.
destruct (k_r_cases (e_pl g)) as [Hr0 | Hr1].
2: { apply (k_rne g pos mf nm tk dp W2 c2 HJ). rewrite Hr1. discriminate. }
pose proof HJ as (ly2 & S2 & regs2 & mem2 & md2 & -> & _).
eapply SRr_bind; [exact (k_pairA g pos mf nm tk dp W2 regs2 mem2 md2 HJ Hr0)|].
intros W3 c3 _ HA. pose proof HA as (-> & _).
eapply SRr_bind; [exact (HKB g pos mf nm tk dp W2 regs2 mem2 md2 W2 c3 HJ Hr0 HA)|].
intros W4 c4 _ HB. pose proof HB as (-> & _).
eapply SRr_bind; [exact (k_pairC g pos mf nm tk dp W2 regs2 mem2 md2 W2 c4 HJ Hr0 HB)|].
intros W5 c5 _ HC. pose proof HC as (-> & _).
eapply SRr_bind; [exact (HKCMP g pos mf nm tk dp W2 regs2 mem2 md2 W2 c5 HJ Hr0 HC)|].
intros W6 c6 _ HL.
eapply SRr_bind; [exact (HKTOK g pos mf nm tk dp 0%nat 0%nat false W6 c6 HL)|].
intros W7 c7 _ HM.
exact (HKCAT g pos mf nm tk dp W7 c7 HM).
Qed.

End d.
End c.
End b.
End a.
