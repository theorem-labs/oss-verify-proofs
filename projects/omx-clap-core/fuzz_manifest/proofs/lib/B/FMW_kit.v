(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 848 of its 931 lines of code are new or changed and 1841 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_manifest/lib/A/FMW_hp_kit.v; 109 of its 144 lines of code are new or changed and 896 lines of the source are left out. *)
(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/FMW_kit.v at a working branch 0d38fb8ac64, relocated A->B by
   Theorem Labs tools over the unstripped twins, every image numeral re-derived by symbol / section / string
   content and checked by revcheck (reports in (internal path)). Imports: lib.Reusable kernel kept;
   the per-image root files from lib.ReusableB; fm's own per-image files from lib.B; FMupoison shared from lib.A. *)
(* fm program part, walk kit shared by the FMW_* walks: fm.asan image facts, the shadow-base cells, the code tables of
   the walked functions, and lemmas that re-derive a callee's premises (stack shadow, C strings) from AR at a call site. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YC20.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMH_Base.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- fm.asan-ubsan image ---- *)
Definition FMW_GOT_shadow : Z := 0x99c98.   (* .got slot holding &__asan_shadow_memory_dynamic_address *)
Definition FMW_shadow_cell : Z := 0xa2078.  (* __asan_shadow_memory_dynamic_address *)
Definition FMW_SB : Z := 0x7fff8000.
Lemma FMW_SB_eq : FMW_SB = SHADOW_OFF. Proof. reflexivity. Qed.
Definition FMW_IMG_LO : Z := 0x10000.
Definition FMW_IMG_END : Z := 0x5f7000.

Lemma fmw_wx : wx_segs_nowrap tfibsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.

Lemma fmw_img_range : forall a, in_img tfibsegs a -> FMW_IMG_LO <= a < FMW_IMG_END.
Proof.
intros a (sg & Hin & Hr).
assert (H : In (Z.of_N (seg_base sg), Z.of_N (seg_size sg))
(map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) tfibsegs)).
{ exact (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) tfibsegs sg Hin). }
remember (Z.of_N (seg_base sg)) as b eqn:Eb. remember (Z.of_N (seg_size sg)) as z eqn:Ez. clear Eb Ez.
vm_compute in H. unfold FMW_IMG_LO, FMW_IMG_END.
destruct H as [H|[H|[H|[H|[]]]]]; injection H as <- <-; lia.
Qed.

Lemma fmw_segs_low : forall a, in_img tfibsegs a -> 0 <= a < kLowMemEnd.
Proof. intros a Ha. pose proof (fmw_img_range a Ha) as R. unfold FMW_IMG_LO, FMW_IMG_END, kLowMemEnd in *. lia. Qed.

(* ---- code tables of the walked functions (instruction words read from tfibsegs) ---- *)
Definition fmw_tbl_crt : ctable := Eval vm_compute in build_table tfibsegs 0x80ff8 159 TEmpty.
Lemma fmw_tbl_crt_eq : fmw_tbl_crt = build_table tfibsegs 0x80ff8 159 TEmpty.
Proof. vm_cast_no_check (eq_refl fmw_tbl_crt). Qed.
Lemma fmw_tbl_crt_ok : table_ok tfibsegs fmw_tbl_crt.
Proof. rewrite fmw_tbl_crt_eq. apply build_table_ok0. lia. Qed.
Lemma fmw_tbl_crt_probe :
clookup fmw_tbl_crt 0x80ff8 = Some 0xf9010113 /\ clookup fmw_tbl_crt 0x81270 = Some 0xc0001073 /\
clookup fmw_tbl_crt 0x81274 = None.
Proof. vm_compute. repeat split; reflexivity. Qed.

Definition fmw_tbl_llvmf : ctable := Eval vm_compute in build_table tfibsegs 0x8097c 150 TEmpty.
Lemma fmw_tbl_llvmf_eq : fmw_tbl_llvmf = build_table tfibsegs 0x8097c 150 TEmpty.
Proof. vm_cast_no_check (eq_refl fmw_tbl_llvmf). Qed.
Lemma fmw_tbl_llvmf_ok : table_ok tfibsegs fmw_tbl_llvmf.
Proof. rewrite fmw_tbl_llvmf_eq. apply build_table_ok0. lia. Qed.

(* ---- symbolic regions: the stack frame, the shadow-base .got slot and cell ---- *)
Definition fmw_stack_region (frame : Z) (cs : list YP09.chunk) : YP09.region :=
YP09.mkRegion (Some 2%nat) (- frame) 0 (- frame) 0 cs.
Definition fmw_got_region : YP09.region :=
YP09.mkRegion None FMW_GOT_shadow (FMW_GOT_shadow + 8) 0 0 [YP09.mkChunk FMW_GOT_shadow (CVal 8 (SLit FMW_shadow_cell))].
Definition fmw_bcell_region (bx : nat) : YP09.region :=
YP09.mkRegion None FMW_shadow_cell (FMW_shadow_cell + 8) 0 0 [YP09.mkChunk FMW_shadow_cell (CVal 8 (SOff bx 0))].
Definition fmw_Bspan : Z * Z := (FMW_SB, FMW_SB + 2 ^ 44 - 1).

Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.

(* the zero shadow of the stack, from AR alone (ARm am_zshadow over zero_shadow_ranges, YG0n.v:188-191) *)
Lemma stk_sh0_of_AR : forall ly S (W : world tfibsegs) mem md lo hi,
AR tfibsegs B ly S W mem md -> ly_stk_lo ly <= lo -> hi <= ly_stk_hi ly ->
stk_sh0 tfibsegs W mem lo hi.
Proof.
intros ly S W mem md lo hi (M & _) Hlo Hhi a Ha.
pose proof (am_layout B ly S _ M) as HLY. pose proof (lo_top ly HLY) as (_ & _ & _ & _ & Hpl & Hph & _).
pose proof (am_zshadow B ly S _ M) as HZ. unfold zshadow_ok, zero_shadow_ranges in HZ.
apply Forall_inv in HZ. cbn [fst snd] in HZ. unfold zero_shadow in HZ.
unfold page_aligned in Hpl, Hph.
set (l0 := ly_stk_lo ly) in *. set (h0 := ly_stk_hi ly) in *.
assert (E : shadow_addr a = shadow_of_addr SHADOW_OFF l0 + (a / 8 - l0 / 8)).
{ unfold shadow_addr, shadow_of_addr. lia. }
rewrite E. apply HZ.
pose proof (Z.div_mod l0 4096 ltac:(lia)) as D0. pose proof (Z.div_mod h0 4096 ltac:(lia)) as D1.
rewrite Hpl, Z.add_0_r in D0. rewrite Hph, Z.add_0_r in D1.
assert (Q0 : l0 / 8 = 512 * (l0 / 4096)) by (rewrite D0 at 1; replace (4096 * (l0 / 4096)) with ((512 * (l0 / 4096)) * 8) by lia; apply Z.div_mul; lia).
assert (Q1 : (h0 - l0) / 8 = 512 * (h0 / 4096) - 512 * (l0 / 4096)).
{ rewrite D0 at 1. rewrite D1 at 1. replace (4096 * (h0 / 4096) - 4096 * (l0 / 4096)) with ((512 * (h0 / 4096) - 512 * (l0 / 4096)) * 8) by lia.
apply Z.div_mul. lia. }
rewrite Q1. split.
- apply Zle_minus_le_0. apply Z.div_le_mono; lia.
- assert (a / 8 < 512 * (h0 / 4096)).
{ apply Z.div_lt_upper_bound; lia. }
lia.
Qed.
End k.

(* a live heap block is visible from its start to the end of the 8-byte word holding its last byte (re-derives
   cstr_ok's last clause, FMH_Base.v, for heap strings) *)
Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.

(* the 8-byte word end of a byte below an 8-aligned end stays at or below that end *)
Lemma fmw_word_end_le : forall x base ext, base mod 16 = 0 -> ext mod 8 = 0 -> x < base + ext ->
x - x mod 8 + 8 <= base + ext.
Proof.
intros x base ext H1 H2 H3.
pose proof (Z.div_mod base 16 ltac:(lia)) as D1. pose proof (Z.div_mod ext 8 ltac:(lia)) as D2.
pose proof (Z.div_mod x 8 ltac:(lia)) as D3. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as D4.
lia.
Qed.

(* a chunk's extent is whole 8-byte words: primary class_size mod 32 = 0, secondary a page multiple less a page (YG0a.v) *)
Lemma fmw_extent_mod8 : forall k, 0 <= ck_req k -> ck_extent k mod 8 = 0.
Proof.
intros k Hq. unfold ck_extent. destruct (from_primary (ck_req k)) eqn:Ep.
- pose proof (primary_geometry (ck_req k) Hq Ep) as (_ & _ & _ & H32 & _).
set (c := class_size (chunk_class (ck_req k))) in *.
pose proof (Z.div_mod c 32 ltac:(lia)) as D. pose proof (Z.div_mod c 8 ltac:(lia)) as D8.
pose proof (Z.mod_pos_bound c 8 ltac:(lia)) as R8. lia.
- pose proof (secondary_geometry (ck_req k) Hq Ep) as (_ & _ & _ & _ & HP & _).
set (s := sec_map_size (ck_req k)) in *. unfold kPage in *.
pose proof (Z.div_mod s 4096 ltac:(lia)) as D. pose proof (Z.div_mod (s - 4096) 8 ltac:(lia)) as D8.
pose proof (Z.mod_pos_bound (s - 4096) 8 ltac:(lia)) as R8. lia.
Qed.

(* a live heap block is visible from its start to the end of the 8-byte word holding its last byte: the block bytes
   by al_blocks (apresent), the bytes after it by ARm am_junk over the chunk's tail junk range (YG0n.v chunk_junk) *)
Lemma block_word_tail_vis : forall ly S (W : world tfibsegs) mem md b m,
  AR tfibsegs B ly S W mem md -> In (b, m) (ablocks B ly S) -> 0 < m ->
  forall a, b <= a < (b + m - 1) - (b + m - 1) mod 8 + 8 -> aview tfibsegs (w_H W) mem a <> None.
Proof.
intros ly S W mem md b m HAR Hin Hm a Ha.
assert (Hrq : req_size m = m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
destruct (Z_lt_le_dec a (b + m)) as [Hlt | Hge].
- destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & _ & _ & _ & Hpres & _).
apply (aview_some_of_apresent tfibsegs). exact (proj1 (Hpres a ltac:(lia))).
- destruct HAR as (M & _).
apply In_ablocks in Hin as (k & Hk & Hst & Hu & Hn).
pose proof (chunk_facts B ly S _ k M Hk) as (_ & _ & Hb16 & Huser & _ & _ & Hreq & Hext & _).
rewrite Hn, Hrq in Hext.
assert (Hcn : ck_n k = m) by (unfold ck_n; rewrite Hn; exact Hrq).
pose proof (fmw_extent_mod8 k ltac:(lia)) as Hx8.
pose proof (fmw_word_end_le (b + m - 1) (ck_base B ly k) (ck_extent k) Hb16 Hx8 ltac:(lia)) as Hend.
pose proof (am_junk B ly S _ M) as HJ. rewrite Forall_forall in HJ.
specialize (HJ (aoff (sptr_exp (ck_beg k)) (ck_rz k + ck_n k), ck_extent k - ck_rz k - ck_n k)).
unfold range_vis in HJ. cbn [fst snd] in HJ.
assert (NSH : forall e', sptr_exp (ck_beg k) <> ASh e') by (intros e'; destruct (ck_beg k); cbn; discriminate).
rewrite (aeval_aoff B ly (sptr_exp (ck_beg k)) (ck_rz k + ck_n k) NSH) in HJ.
assert (Eb : aeval B ly (sptr_exp (ck_beg k)) = ck_base B ly k) by reflexivity.
replace a with (aeval B ly (sptr_exp (ck_beg k)) + (ck_rz k + ck_n k) + (a - (b + m))) by lia.
apply HJ; [|lia].
unfold ajunk. apply in_cons. apply in_cons.
apply in_or_app; right. apply in_or_app; right. apply in_or_app; left.
apply in_flat_map. exists k. split; [exact Hk|].
unfold chunk_junk. cbv zeta.
apply in_or_app; right. apply in_or_app; right. apply in_or_app; right. apply in_eq.
Qed.
End w.
