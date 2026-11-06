(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/A/ACja.v for libreac/fuzz_grant's program walk, over fuzz_grant's listing. Image objects follow fuzz_grant.asan: the GOT word of the shadow-base cell is object 1 (atom 242), the GOT word of the side-stack flag is object 0 (atom 241), the shadow-base cell is object 32 (atom 273) and the side-stack flag cell is object 33 (atom 274), so img_factsF and img_hull_factsF give E240 E241 E242 E273 E274 and Hob241 Hob242 Hob273 Hob274, keptFL keeps those four regions, and aconstsF rewrites with PALib's pal_got_shadow, pal_cell and GrantFrame's palf_got_uar. awrFL, keptFL, fs_roF and fs_rwF keep the walks' atoms for the own side-stack frame (516), its shadow (529), the realigned stack (60) and the stack (2), for any frame class; stack bounds compute the walk's own STK constant; cgif's case for its 40-byte FRAME block (atom 11) is left out, and awrFL_with/keptFL_with take a tactic for a walk's own head regions. Module paths changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v of a working branch ca2ec2ecd18 and re-keyed to fuzz_ctrl.asan, whose shadow-base cell is object 30 (atom 271) and whose side-stack flag cell is object 31 (atom 272): img_factsF and img_hull_factsF now give E240 E241 E242 E271 E272 and Hob241 Hob242 Hob271 Hob272, and keptFL keeps the regions of atoms 241, 242, 271 and 272. The two GOT words (objects 0 and 1, atoms 241 and 242) are unchanged. Module paths and module names re-keyed to fuzz_ctrl. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/CtrlACja.v, with its module paths and module names changed; 566 of its 624 lines of code are new or changed and 273 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/TjUnk.v; 83 of its 150 lines of code are new or changed and 557 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0b YP0a.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YCkd.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0d YP0c YP07 YI0w YI0z YI12 YC4a YC8i.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC45 YC85 YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC8g YC1i.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YCjr YCj1 YCja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SnShared SnprintfDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Rt Require Import SnprintfConsts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YRo YXcalls YCbj.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import ReacDiscoTableJson TjBase TjCuts TjLoopCuts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import TjEntry TjExit TjClose TjUnk TjTokB TjTail TjPre.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import PfFacts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_json_text.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require disco_table_c reac_disco_table_json_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import ReacBoxName SbCh SbDec TjMac TjRole TjBox TjImg.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require ReacBoxNameTop SbDecWalk.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require SetShadowDef StrlenDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require SnprintfDefR.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
#[local] Notation PI := PB_tfib.
Context {RO : ro_below_ofl (@pa_segs _ lib_both3_0_listing PI) (@pa_relro_lo _ lib_both3_0_listing PI) (@pa_relro_hi _ lib_both3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
Definition tj_nmax : Z := 8.
Section h.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASM2 : forall fq : YK11.FPState, astack_malloc_realizes (fx := fq) SEGS B 2.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis ASF : astack_free_law SEGS B.
Variables SNPC GC GV IMGLO IMGHI : Z.
Variable CR : list (Z * Z).
Hypothesis HSNPC : SIGMA AS___interceptor_trampoline_snprintf = SNPC.
Hypothesis ASNP : forall fq : YK11.FPState,
SnprintfDefR.sh_asnprintf_realizesR (fx := fq) SEGS B pa_relro_lo pa_relro_hi (SnFF.FF_disco disco_fmt_lo disco_fmt_hi) SNPRINTF_STK GC GV IMGLO IMGHI CR SNPC.
Hypothesis tj_snp_consts : forall (W : world SEGS) mem, arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) -> consts_view SEGS W mem CR.
Hypothesis tj_snp_cr : Forall (fun r => IMG_LO <= fst r /\ 0 <= snd r /\ fst r + snd r <= IMG_TOP) CR.
Hypothesis tj_snp_canary : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
exists cval, rdword (aview SEGS (w_H W) mem) GC = Some GV /\ rdword (aview SEGS (w_H W) mem) GV = Some cval.
Hypothesis tj_snp_gcgv : IMG_LO <= GC /\ GC + 8 <= IMG_TOP /\ IMG_LO <= GV /\ GV + 8 <= IMG_TOP.
Hypothesis tj_snp_img : IMG_LO <= IMGLO /\ IMGHI <= IMG_TOP.
Hypothesis DRO : tfib_ro_unowned B.
Hypothesis GM : globs_marked SEGS B tfib_globs.
Hypothesis HV : img_shadow_vis SEGS B.
Hypothesis AMEMSET : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OSet (SIGMA AS___asan_memset).
Hypothesis AMEMCPY : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OCpy (SIGMA AS___asan_memcpy).
Hypothesis ABCMP : forall fq : YK11.FPState, abcmp_realizes (fx := fq) SEGS B (SIGMA AS___interceptor_trampoline_bcmp).
Hypothesis ASTRLEN : forall fq : YK11.FPState,
StrlenDef.astrlen_realizesM (fx := fq) SEGS B MC_CONSTS_LO MC_CONSTS_HI (SIGMA AS___interceptor_trampoline_strlen).
Hypothesis ASSF5 : forall fq : YK11.FPState,
SetShadowDef.aset_shadow_realizes (fx := fq) SEGS B (SIGMA AS___asan_set_shadow_f5) 0xf5.
Hypothesis ASM3 : forall fq : YK11.FPState, astack_malloc_realizes (fx := fq) SEGS B 3.
Hypothesis ASM0 : forall fq : YK11.FPState, astack_malloc_realizes (fx := fq) SEGS B 0.
Let TJS : tj_strs := tj_strs_tfib.
Let RBR : tj_rbn_rom := tj_rbn_rom_tfib.
Lemma tj_mc_unowned : forall a, MC_CONSTS_LO <= a < MC_CONSTS_HI ->
~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros a Ha.
assert (HIN : In (0x10368, 32) tfib_ro_ranges).
{ apply in_or_app. right. cbn. right. right. right. right. right. right. right. left. reflexivity. }
apply (tfib_ro_unowned_at B 0x10368 32 DRO HIN a).
unfold MC_CONSTS_LO, MC_CONSTS_HI in Ha. lia.
Qed.
Lemma tj_mc_img : forall a, MC_CONSTS_LO <= a < MC_CONSTS_HI -> in_img SEGS a.
Proof. intros a Ha. exact (tj_ro_img _ _ a (proj1 RBR) ltac:(lia)). Qed.
Lemma tj_sb_ch : tsb_ch_spec B.
Proof. eapply pb_sb_ch; eassumption. Qed.
Lemma tj_sb_dec : tsb_dec_spec B.
Proof. eapply SbDecWalk.pb_sb_dec; first [exact tj_sb_ch | eassumption]. Qed.
Lemma tj_rbn : treac_box_name_spec B.
Proof.
eapply ReacBoxNameTop.pb_reac_box_name;
first [exact tj_mc_unowned | exact tj_mc_img | exact tj_sb_dec | exact tj_sb_ch | eassumption].
Qed.
Variable IMG : world SEGS -> (word -> option byte) -> Prop.
Lemma tj_walk_X : tj_fromX B IMG.
Proof. eapply pb_tj_exit; eassumption. Qed.
Lemma tj_walk_C : tj_fromC B IMG.
Proof. eapply pb_tj_close; first [exact tj_walk_X | eassumption]. Qed.
Lemma tj_walk_U : tj_seg_unk B IMG.
Proof. eapply pb_tj_unk; eassumption. Qed.
Lemma tj_walk_K : tj_seg_tok B IMG.
Proof. eapply pb_tj_tok_b; eassumption. Qed.
Lemma tj_walk_T : tj_seg_tail B IMG.
Proof. eapply pb_tj_tail; first [exact PRP_tfib | eassumption]. Qed.
Lemma tj_walk_R : tj_seg_box B IMG.
Proof. eapply pb_tj_box; first [exact tj_mc_unowned | exact tj_rbn | exact PX_tfib | eassumption]. Qed.
Lemma tj_walk_M : tj_seg_role B IMG.
Proof. eapply pb_tj_seg_role; first [exact PRP_tfib | eassumption]. Qed.
Lemma tj_walk_L : tj_seg_mac B IMG.
Proof. eapply pb_tj_mac; first [exact PRP_tfib | eassumption]. Qed.
Lemma tj_fromL_past : forall i, tj_nmax <= i -> tj_fromL B IMG i.
Proof.
intros i Hi. unfold tj_fromL, tj_from0.
intros cx E k ly3 S3 W3 ms3 md3 HB _ _ _ HINV _.
destruct HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hok & _).
unfold disco_table_c.table_ok, disco_table_c.tbl_T1 in Hok. destruct Hok as (Hn & _).
destruct HINV as (_ & _ & _ & _ & Hi' & _).
unfold tj_nmax in Hi. lia.
Qed.
Lemma tj_walk_body : forall i, tj_fromL B IMG (i + 1) -> tj_fromL B IMG i.
Proof.
intros i FL1.
pose proof (tj_walk_T i tj_walk_X tj_walk_C FL1) as FT.
exact (tj_walk_L i tj_walk_X (tj_walk_M i tj_walk_X (tj_walk_R i (tj_walk_U i tj_walk_X FT) (tj_walk_K i tj_walk_X FT)))).
Qed.
Lemma tj_walk_loop_m : forall m : nat, forall i, tj_nmax - i <= Z.of_nat m -> tj_fromL B IMG i.
Proof.
induction m as [|m IH]; intros i Hm.
- apply tj_fromL_past. lia.
- apply tj_walk_body. apply IH. lia.
Qed.
Lemma tj_walk_loop : forall i, tj_fromL B IMG i.
Proof. intros i. apply (tj_walk_loop_m (Z.to_nat (tj_nmax - i))). lia. Qed.
Lemma tj_pre_to_from0 : tj_from0 B IMG ss_tj0 (INV_tj0 B 0).
Proof. eapply pb_tj_pre; first [exact tj_walk_X | exact tj_walk_C | exact (tj_walk_loop 0) | eassumption]. Qed.
Theorem reac_disco_table_json_ok : treac_disco_table_json_spec B IMG.
Proof. eapply pb_tj_entry; first [exact tj_pre_to_from0 | eassumption]. Qed.
End h.
End f.
End d.
