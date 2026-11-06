(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YP0n.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/Reusable/YP0n.v, with its module paths and module names changed; 967 of its 1043 lines of code are new or changed and 1914 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/Cno102B_Base.v, with its module names changed; 472 of its 536 lines of code are new or changed and 979 lines of the source are left out. *)
(* fuzz_preset, image A' (#102 pins: asan sha256 1be0f53d96cb9d6c): segments CA6 / CA7 / CA8 (Read1-3, the GUARD parts)
   of the re-walk of check_no_overread (cno) against the text tcheck_no_overread_specX, by a Theorem Labs lane (sub-lane
   of another lane, under a Theorem Labs session; plan, the internal file PLAN-cno-caw-102.md 5.1 rows CA6-CA8). Each segment ends at the parse_noting
   call state (cn_ex_pn1 / pn2 / pn3) or at the next cut; the parse_noting step itself closes after the kit's Batch 2.
   rule 24: no function proved. rule 24: proves no function (kind: segment lemma).
   INPUTS (by path, at the kit cut 7cdbb61b5fa0, a working branch): the contract lib/A/Prog/Cno102A_Base.v
   blob ba76a7bc31c9 (the cuts carry cn_prog D E S over the events since entry, the grants o1 / o2 / o0 last, ran =
   cn_ranz (read2 / read3 / cmp) or cn_ro .. = false (pn2 / pn3), the structs against the model, cn_rd / cn_rds2 /
   cn_rds3, their free-order ties cn_fo, the spent wild budget as cn_base's last argument, cn_cdead in the refused-copy
   arms; cn_mid's ledger `.. ran (ci_most D) own`); the texts at the cut: lib/A/PRH_Base.v ef7c8ca98529 (prh_ledger
   with most / own, prh_own, the projections prh_ledger_own / prh_ledger_bounds), lib/A/PRH_FnAlloc.v 4d8aeba047e5
   (tfuzz_alloc_ran_out_specX: S' = S), lib/A/PRH_FnCheck.v c40cf3fdcd2a (ck_cno_ranout), lib/A/PRH_PjOrder.v
   e5917626b82b (pj_foR); lib/Spec/PresetRun.v 5ac818ab1fe6 (ranout _ _ None = false); the step kit
   lib/A/Prog/Cno102A_Ro.v re-fit to the cut (cn_ro_call keeps S, wk and carries cn_mid at own and the three cn_fo
   across fuzz_alloc_ran_out; cn_hs_* / cn_base_mat); listing lib/A/Listing_prog.v 7ed1529926bd.
   Re-fit of f193cb34d038 (Base f1b6bdaed87b) to f97c: the ran-out call keeps S, so each exit carries the cut's cn_prog;
   g_ran_out after the call decides the model's ranout of the readings made (r6_ranz1 / r6_ranz2: a skipped reading's
   grant None never runs out); a reading skipped after a ran-out one adds no event (r6_revs2_skip / r6_revs3_skip) and
   leaves its struct zero (r6_rds2_skip / r6_rds3_skip); these helpers are the B' twin's (Cno102B_R4.v cac511967efd,
   r4_ for r6_). The statements of cn_read2_seg / cn_read3_seg take the cuts' new grants o1 / o1 o2; no other change.
   Base 1ffd0a7bddd: read2's skip arm (own0 <> 0) states st1 = None (CA6 chooses it), and CN_FREE's refused-copy arm
   (ownl <> 0) carries cn_prog over the copies' events and three zero structs (CA7's free exit: read2's skip arm).
   RE-FIT TO THE KIT CUT 7cdbb61b5fa0 (contract lib/A/Prog/Cno102A_Base.v blob ba76a7bc31c9; the step kit
   Cno102A_Ro.v re-fit to the cut): cn_pre has no run-word list DW and is read by name (cn_pre_ran); cn_base takes the
   spent wild budget wk last, kept by every hand step and by fuzz_alloc_ran_out (cn_ro_call), and raised by
   cn_base_mono where a reading is skipped (read1 0 -> read2 2, read2 2 -> read3 4 / free 6, read3 4 -> cmp 6); the
   refused copy's dead arm (own0 <> 0 -> cn_cdead D) rides read1 -> read2's skip arm -> free's ownl <> 0 arm; the
   readings' free-order ties cn_fo ride the register steps unchanged and cross fuzz_alloc_ran_out by cn_ro_call's
   keep (pj_foR_frame over the tree bytes the call keeps); a skipped reading's struct is None, whose cn_fo is True.
   The statements of cn_read1_seg / cn_read2_seg / cn_read3_seg drop DW; no other change.
   THE FREE / REALLOC MOVE: the cut's journal spans parse_noting (the restated tparse_noting_specX concludes SRr'
   SEGS RZ_cf, its post at wle'), so a cut after the first reading carries cn_J at wle' SEGS RZ_cf. cn_read1_seg runs
   before it (CN_READ1 -> the pn1 call state / CN_READ2's skip arm): unchanged, at SRr. cn_read2_seg starts at
   cn_at_read2R at wle' (CN_READ2 holds on both sides; its before-side arrivals lift by the base's mono lemma) and
   cn_read3_seg at cn_at_read3 (after only, at wle'); both conclude SRr' SEGS RZ_cf. Their hand steps stay the kit's
   SRr steps, run inside the kit's cn_srrG_lift; fuzz_alloc_ran_out (a plain, non-crossing text) goes through the
   kit's cn_ro_callR at wle', and the exits leave by SRr_ret, SRrG_ret. THE HULL: each cut carries the base's plain
   conjunct `PresetHullBudget.hull_budget S (cn_hrest_<stage> (ci_x D))` (copies at CN_READ1 / pn1, rd1 at CN_READ2 /
   pn2, rd2 at CN_READ3 / pn3, rd0 at CN_CMP / CN_FREE). No allocator call runs here and fuzz_alloc_ran_out keeps S,
   so the conjunct rides to the exit at its stage unchanged; a skipped reading pays nothing, so a skip arm drops that
   reading's events from the budget (r6_hull_rd1 / r6_hull_rd2 / r6_hull_rd0: hull_budget_app with nothing used, over
   the base's split equations).
   THE CODE (DERIVED offsets inside cno; listing: the A' disassembly of check_no_overread):
     CA6  748 li s7,-1 | 752 bnez s10,+188 (-> 940 ld s10,24(s1); 944 = CN_READ2) | 756 jal fuzz_alloc_ran_out |
          760 ld s10,24(s1) | 764 bnez a0,+180 (-> 944) | 768 mv a0,s10 | 772 mv a1,s4 | 776 ld a2,56(s1) |
          780 jal parse_noting (ra = 784 = CN_RET1)
     CA7  944 lbu a0,-1368(s8) | 948 beqz a0,+16 (-> 964) | 952 ld s9,56(s1) | 956 li s5,1 | 960 j +100 (1060 =
          CN_FREE) | 964 jal fuzz_alloc_ran_out | 968 beqz a0,+12 (-> 980) | 972 li s9,-1 | 976 j +24 (1000 =
          CN_READ3) | 980 ld a0,40(s1) | 984 mv a1,s4 | 988 mv a2,s5 | 992 jal parse_noting (ra = 996 = CN_RET2)
     CA8  1000 li s5,1 | 1004 lbu a0,-1368(s8) | 1008 bnez a0,+48 (-> 1056 ld s9,56(s1); 1060 = CN_FREE) |
          1012 jal fuzz_alloc_ran_out | 1016 beqz a0,+12 (-> 1028) | 1020 li s4,-1 | 1024 j +24 (1048 = CN_CMP) |
          1028 mv a0,s6 | 1032 mv a1,s4 | 1036 mv a2,s3 | 1040 jal parse_noting (ra = 1044 = CN_RET3)
   THE g_own_ran_out BYTE: each lbu reads it afresh (cn_img's cni_hi9 / cni_own give the address, cni_pst_seg makes the
   load read a value) and the byte read is the own of the cut's ledger (PRH_Base.prh_ledger_own, then r6_own_read).
   The ledger rides the hand steps unchanged (no step of CA6-CA8 stores) and crosses fuzz_alloc_ran_out at the same
   own inside cn_mid (cn_ro_call). In CA7 the byte 0 says own0 = 0, so every copy is non-NULL, and the free exit
   carries ownl = own0; in CA8 own = 0, so `bnez` never goes to free.
   No abort edge and no ASan report site lies in these stretches.
   Numerals: offsets as above (DERIVED); 24 / 40 / 56 (LENGTH: the real-stack slots); register numbers (WORD);
   2 ^ 64 (word range). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YI16 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Img PRH_Reader PRH_FnAlloc
  PRH_FnReader PRH_FnPj PRH_FnEx PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_StepKit Cno102A_Base Cno102A_Ro.
(* the PLAIN build's sink instance is loaded transitively; it must never fill an ASan sink argument *)
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.
(* PRW_StepKit loads YF0v.v, which turns zify's division rewriting off globally (S4_PsU.v's reset) *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* a register of a cut's snapshot *)
Ltac cn_get HR := apply (cn_regsat_get _ _ _ _ HR); unfold cn_core, cn_s8; ro_in.
(* one register of an exit's snapshot, through the steps' updates *)
Lemma r6_li : forall regs i, v_addi (getr regs 0%bv) i = w64 i.
Proof. intros regs i. rewrite ro_getr0. unfold v_addi, w64. rewrite unsigned_lit_small by lia. f_equal. Qed.
Lemma r6_mv : forall (x : word), v_addi x 0 = x.
Proof. intros x. unfold v_addi. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Ltac cn_rs_one HR := cbn [fst snd]; ro_getr;
  first [ reflexivity | rewrite r6_li; reflexivity | rewrite r6_mv; ro_getr; first [reflexivity | cn_get HR] | cn_get HR ].
Ltac cn_rs HR := unfold cn_regsat, cn_core, cn_s8; cbn [app];
  repeat (apply Forall_cons; [cn_rs_one HR |]); apply Forall_nil.
Ltac cn_acs := lazymatch goal with |- acallee_saved (bv_unsigned ?r) =>
  let v := eval vm_compute in (bv_unsigned r) in change (bv_unsigned r) with v; unfold acallee_saved; lia end.
Ltac r6_sig := repeat (match goal with |- context [bv_signed ?i] =>
  let v := eval vm_compute in (bv_signed i) in change (bv_signed i) with v end).
Ltac r6_bnd := r6_sig; lia.
Ltac cn_acsl := unfold cn_core, cn_s8; cbn [app]; repeat (apply Forall_cons; [cbn [fst]; cn_acs |]); apply Forall_nil.

Section r6. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Existing Instance prh_img_A.
Context {PA : PAImg A_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation VAL := (@pa_val _ A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
(* the world relation of a cut after a free *)
#[local] Notation RZ := YGcfRehidePost.RZ_cf.
#[local] Notation RCF := (wle' SEGS YGcfRehidePost.RZ_cf).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable CTX0 : list (list Z).
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
Hypothesis IMG : cn_img B.
(* The kit's text (PRH_FnAlloc.v 4d8aeba047e5 :175-183, the cut 7cdbb61b5fa0), for any float state *)
Hypothesis HRO : forall fz : YK11.FPState,
  @tfuzz_alloc_ran_out_specX fz rc cp prh_img_A RL A_prog_listing PA B ARx SK.

(* ---- helpers ---- *)
Lemma r6_live_nonneg : forall x, 0 <= PRH_FnPj.LIVE_pj_parse x.
Proof.
intros x. unfold PRH_FnPj.LIVE_pj_parse. pose proof (@cf_head_nonneg cp) as H0.
assert (H1 : 0 <= hpeakR (PRH_FnPj.prhPj_ptrace x))
  by (destruct (PRH_FnPj.prhPj_ptrace x) as [|e r]; cbn [hpeakR]; lia).
nia.
Qed.

Lemma r6_mid_nr : forall D ly S Hp W mem Lam peak cnt ran own (nr nr' : nat) r1 r2 r3 st1 st2 st3,
  cn_mid B D ly S Hp W mem Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3 -> (nr <= nr' <= 3)%nat ->
  cn_mid B D ly S Hp W mem Lam peak cnt ran own nr' r1 r2 r3 st1 st2 st3.
Proof.
intros D ly S Hp W mem Lam peak cnt ran own nr nr' r1 r2 r3 st1 st2 st3
  (C1 & C2 & C3 & HL & Hpk & Hcnt & Hroom & Hbb & HRest) Hn.
pose proof (r6_live_nonneg (ci_x D)) as HLV.
assert (Hnc : 0 <= ck_ncalls (ci_x D)) by (unfold ck_ncalls; lia).
split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [exact HL|]. split; [exact Hpk|].
split; [nia|]. split; [exact Hroom|].
split; [rewrite !Nat2Z.inj_sub in * by lia; nia | exact HRest].
Qed.

(* the g_own_ran_out byte: every load of it reads a value *)
Lemma r6_own_byte : forall (W : world SEGS) mem, exists b, mbyte SEGS (rdW W mem) (VAL (A_OBJ 13)) = Some b.
Proof.
intros W mem. unfold mbyte.
destruct (mrestrict (w_H W) mem (Z_to_bv 64 (VAL (A_OBJ 13)))) as [b|] eqn:E; [exists b; reflexivity|].
destruct (YK11.seg_rom SEGS (Z_to_bv 64 (VAL (A_OBJ 13)))) as [b|] eqn:E2; [exists b; reflexivity|].
exfalso. apply (cni_pst_seg B IMG (VAL (A_OBJ 13))); [|exact E2].
rewrite (cni_own B IMG). unfold prh_pst. apply Exists_exists.
exists (pi_g_own_ran_out, Z.of_nat pi_gz_own_ran_out). split; [ro_in|].
unfold in_zr. cbn [fst snd]. assert (Hz : pi_gz_own_ran_out = 1%nat) by (vm_compute; reflexivity). rewrite Hz. lia.
Qed.

(* the address of `lbu a0, -0x558(s8)` *)
Lemma r6_own_addr : forall regs, getr regs 24%bv = w64 (VAL (A_HI 9)) ->
  bv_unsigned (getr regs 24%bv) + (-1368) = VAL (A_OBJ 13).
Proof.
intros regs H. rewrite H. unfold w64. rewrite unsigned_lit_small by (apply pa_val_range).
rewrite <- (cni_hi9 B IMG). lia.
Qed.

(* the byte read, against a byte the memory is known to hold *)
Lemma r6_byte_val : forall (m : word -> option byte) a b v, mbyte SEGS m a = Some b -> val_mem SEGS m a 1 v ->
  0 <= v < 256 -> bv_unsigned b = v.
Proof.
intros m a b v Hb Hv Hr. specialize (Hv 0%nat ltac:(lia)). cbn [Z.of_nat] in Hv. rewrite Z.add_0_r, Hb in Hv.
injection Hv as ->. rewrite Z_to_bv_unsigned. unfold YO0f.le_byte, bv_wrap.
change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
change (bv_modulus 8) with 256. change (2 ^ 8) with 256. rewrite !Z.mod_small by lia. reflexivity.
Qed.

Lemma r6_byte_w64 : forall (b : byte), Z_to_bv 64 (bv_unsigned b) = w64 (bv_unsigned b).
Proof. reflexivity. Qed.

(* the byte `lbu a0, -0x558(s8)` reads is the own of prh_own (pi_gz_own_ran_out = 1), the ledger's own cell *)
Lemma r6_own_read : forall (W : world SEGS) mem b own, mbyte SEGS (rdW W mem) (VAL (A_OBJ 13)) = Some b ->
  prh_own W mem own -> bv_unsigned b = own.
Proof.
intros W mem b own Hb (Hv & Ho). rewrite <- (cni_own B IMG) in Hv.
assert (Hz : pi_gz_own_ran_out = 1%nat) by (vm_compute; reflexivity). rewrite Hz in Hv.
apply (r6_byte_val _ _ b own Hb Hv). lia.
Qed.

(* the entry's numbers the steps use: the real stack slots lie in the word range, ci_ran D = 0 (cn_pre by name) *)
Lemma r6_entry : forall D, cn_pre (fx := fx) B ARx CTX0 D ->
  4096 <= cn_S1 D /\ cn_S1 D + 88 <= 2 ^ 47 /\ ci_ran D = 0.
Proof.
intros D HPRE.
destruct (cn_entry_facts B ARx CTX0 D HPRE) as (Hal16 & Hceil & Hslo & Htop1 & Htop2 & H47 & Hhi64 & _).
destruct (cn_S1_facts D Hal16) as (HS1a & _). pose proof cn_stk_val as HS. pose proof asan_consts as (C1 & _).
split; [lia|]. split; [lia | exact (cn_pre_ran (fx := fx) B ARx CTX0 D HPRE)].
Qed.

(* the cut's base under another register file that keeps gp / tp, and at a materialised model, over any world
   relation R (a cut after a free: R := wle' SEGS RZ_cf); r6_base / r6_mat are their forms at wle *)
Lemma r6_baseR : forall (R : world SEGS -> world SEGS -> Prop) D fxk ly S Hp W regs regs' mem md k wk,
  cn_baseR (fx := fx) B ARx R D fxk ly S Hp W regs mem md k wk ->
  getr regs' 3%bv = getr regs 3%bv -> getr regs' 4%bv = getr regs 4%bv ->
  cn_baseR (fx := fx) B ARx R D fxk ly S Hp W regs' mem md k wk.
Proof.
intros R D fxk ly S Hp W regs regs' mem md k wk (Hz & Hk & HJ & HF & HSV & R3 & R4 & HRO') E3 E4.
repeat (split; [eassumption|]). split; [rewrite E3; exact R3|]. split; [rewrite E4; exact R4|]. exact HRO'.
Qed.
Lemma r6_base : forall D fxk ly S Hp W regs regs' mem md k wk,
  cn_base (fx := fx) B ARx D fxk ly S Hp W regs mem md k wk ->
  getr regs' 3%bv = getr regs 3%bv -> getr regs' 4%bv = getr regs 4%bv ->
  cn_base (fx := fx) B ARx D fxk ly S Hp W regs' mem md k wk.
Proof. exact (r6_baseR (@wle SEGS)). Qed.
Lemma r6_matR : forall (R : world SEGS -> world SEGS -> Prop) D fxk ly S Hp W regs mem md k wk X,
  cn_baseR (fx := fx) B ARx R D fxk ly S Hp W regs mem md k wk ->
  cn_baseR (fx := fx) B ARx R D fxk ly S Hp W regs mem (with_vm_backing (m_vm_lazy md) X md) k wk.
Proof.
intros R D fxk ly S Hp W regs mem md k wk X HB.
exact (cn_base_matR B ARx LAWS R D fxk ly S Hp W regs regs mem md k wk X HB eq_refl eq_refl).
Qed.
Lemma r6_mat : forall D fxk ly S Hp W regs mem md k wk X,
  cn_base (fx := fx) B ARx D fxk ly S Hp W regs mem md k wk ->
  cn_base (fx := fx) B ARx D fxk ly S Hp W regs mem (with_vm_backing (m_vm_lazy md) X md) k wk.
Proof. exact (r6_matR (@wle SEGS)). Qed.

(* cn_base at an exit: the materialised models, then a register file that keeps gp / tp *)
Ltac r6_base HB := eapply r6_base; [repeat apply r6_mat; exact HB | ro_getr; reflexivity | ro_getr; reflexivity].
(* the same at a cut whose spent wild budget is larger (a skipped reading spends none of its 2) *)
Ltac r6_base_up HB := eapply cn_base_mono; [|r6_base HB]; lia.
(* the two at a cut after a free (cn_baseR at the cut's relation) *)
Ltac r6_baseR HB := eapply r6_baseR; [repeat apply r6_matR; exact HB | ro_getr; reflexivity | ro_getr; reflexivity].
Ltac r6_base_upR HB := eapply cn_baseR_mono_wk; [|r6_baseR HB]; lia.

(* ---- THE HULL STAGE of a skipped reading: it runs no allocator call, so the cut's budget for the rest of the
   all-granted list is one for the rest after that reading (hull_budget_app with nothing used, hull_used_refl), over
   the base's split equations cn_hrest_<stage>_split ---- *)
Lemma r6_hull_drop : forall S (A Rl : list PresetReqAt.hev),
  PresetHullBudget.hull_budget S (A ++ Rl) -> PresetHullBudget.hull_budget S Rl.
Proof. intros S A Rl H. exact (PresetHullBudget.hull_budget_app S S A Rl H (PresetHullBudget.hull_used_refl S A)). Qed.
(* reading 1 skipped (CN_READ1 -> CN_READ2 at own0 <> 0) *)
Lemma r6_hull_rd1 : forall S x,
  PresetHullBudget.hull_budget S (cn_hrest_copies x) -> PresetHullBudget.hull_budget S (cn_hrest_rd1 x).
Proof. intros S x H. rewrite (cn_hrest_rd1_split x) in H. exact (r6_hull_drop S _ _ H). Qed.
(* reading 2 skipped (CN_READ2 -> CN_READ3 / CN_FREE) *)
Lemma r6_hull_rd2 : forall S x,
  PresetHullBudget.hull_budget S (cn_hrest_rd1 x) -> PresetHullBudget.hull_budget S (cn_hrest_rd2 x).
Proof. intros S x H. rewrite (cn_hrest_rd2_split x) in H. exact (r6_hull_drop S _ _ H). Qed.
(* reading 3 skipped (CN_READ3 -> CN_CMP, CN_READ2 -> CN_FREE) *)
Lemma r6_hull_rd0 : forall S x,
  PresetHullBudget.hull_budget S (cn_hrest_rd2 x) -> PresetHullBudget.hull_budget S (cn_hrest_rd0 x).
Proof. intros S x H. rewrite (cn_hrest_rd0_split x) in H. exact (r6_hull_drop S _ _ H). Qed.

(* ---- THE READINGS' EVENTS, g_ran_out AND THE STRUCTS (f97c's exact-position form): the model's ranout of a skipped
   reading (grant None) is false, so g_ran_out after the readings is 1 exactly when a reading made ran out; a reading
   skipped after a ran-out reading adds no event (cn_revs2 / cn_revs3's skip) and leaves its struct zero (cn_rds2 /
   cn_rds3). The B' twin's helpers (Cno102B_R4.v cac511967efd), r4_ for r6_. ---- *)
Lemma r6_ranz1 : forall D o1, cn_ranz D o1 None None = if cn_ro D o1 then 1 else 0.
Proof. intros D o1. unfold cn_ranz, ck_cno_ranout, cn_ro. destruct (PresetRun.ranout _ (ci_x D) o1); reflexivity. Qed.
Lemma r6_ranz2 : forall D o1 o2, cn_ranz D o1 o2 None = if cn_ro D o1 || cn_ro D o2 then 1 else 0.
Proof.
intros D o1 o2. unfold cn_ranz, ck_cno_ranout, cn_ro.
destruct (PresetRun.ranout _ (ci_x D) o1), (PresetRun.ranout _ (ci_x D) o2); reflexivity.
Qed.
(* CA7: g_ran_out = 1 after reading 1 says reading 1 ran out, 0 says it did not *)
Lemma r6_ro1_true : forall D o1, 1 = cn_ranz D o1 None None -> cn_ro D o1 = true.
Proof. intros D o1. rewrite r6_ranz1. destruct (cn_ro D o1); [reflexivity | discriminate]. Qed.
Lemma r6_ro1_false : forall D o1, 0 = cn_ranz D o1 None None -> cn_ro D o1 = false.
Proof. intros D o1. rewrite r6_ranz1. destruct (cn_ro D o1); [discriminate | reflexivity]. Qed.
(* CA8: the same after readings 1 and 2 *)
Lemma r6_ro2_false : forall D o1 o2, 0 = cn_ranz D o1 o2 None -> cn_ro D o1 = false /\ cn_ro D o2 = false.
Proof.
intros D o1 o2. rewrite r6_ranz2. destruct (cn_ro D o1), (cn_ro D o2); intros H; cbv iota beta in H;
  first [discriminate H | split; reflexivity].
Qed.
(* the skip: reading 2 (CA7, grant None) or reading 3 (CA8, grant None) after a ran-out reading adds no event *)
Lemma r6_revs2_skip : forall D o1, cn_ro D o1 = true -> cn_revs2 D o1 None = cn_pe D o1.
Proof. intros D o1 H. unfold cn_revs2. rewrite H. apply app_nil_r. Qed.
Lemma r6_revs3_skip : forall D o1 o2, 1 = cn_ranz D o1 o2 None -> cn_revs3 D o1 o2 None = cn_revs2 D o1 o2.
Proof.
intros D o1 o2. rewrite r6_ranz2. unfold cn_revs3, cn_revs2.
destruct (cn_ro D o1), (cn_ro D o2); intros H; cbv iota beta in H |- *;
  first [discriminate H | rewrite ?app_nil_r; reflexivity].
Qed.
(* the structs at the skip: reading 2 (CA7) / reading 3 (CA8) skipped, its struct stays zero (None) *)
Lemma r6_rds2_skip : forall D o1 st1, cn_ro D o1 = true -> cn_rd D o1 st1 -> cn_rds2 D o1 None st1 None.
Proof. intros D o1 st1 Hro H. unfold cn_rds2. rewrite Hro. split; [exact H | exact eq_refl]. Qed.
Lemma r6_rds3_skip : forall D o1 o2 st1 st2, 1 = cn_ranz D o1 o2 None -> cn_rds2 D o1 o2 st1 st2 ->
  cn_rds3 D o1 o2 None st1 st2 None.
Proof.
intros D o1 o2 st1 st2. rewrite r6_ranz2. unfold cn_rds3, cn_rds2.
destruct (cn_ro D o1), (cn_ro D o2); intros H (H1 & H2); cbv iota beta in H, H2 |- *;
  first [discriminate H | split; [exact H1 | split; [exact H2 | exact eq_refl]]].
Qed.
(* the reading-2 struct of a pn3 call state: reading 1 did not run out *)
Lemma r6_rds2_rd : forall D o1 o2 st1 st2, cn_ro D o1 = false -> cn_rds2 D o1 o2 st1 st2 ->
  cn_rd D o1 st1 /\ cn_rd D o2 st2.
Proof. intros D o1 o2 st1 st2 Hro (H1 & H2). rewrite Hro in H2. exact (conj H1 H2). Qed.

(* ---- CA6, CN_READ1 -> CN_READ2 (own0 <> 0, or the ran-out flag set) or the parse_noting call (pn1) ---- *)
Theorem cn_read1_seg : forall P, srr_inv_laws SEGS P -> srr_inv_call SEGS P ->
  forall D fxk ly S Hp W regs mem md k r1 r2 r3 own0,
  cn_pre (fx := fx) B ARx CTX0 D ->
  cn_at_read1 (fx := fx) B ARx D fxk ly S Hp W regs mem md k r1 r2 r3 own0 -> P mem ->
  SRr SEGS W (@cn_cfg SEGS fxk (cn_pc CN_READ1) regs mem md)
    (fun W' c' => (cn_ex_read2 (fx := fx) B ARx D W' c' \/ cn_ex_pn1 (fx := fx) B ARx D W' c') /\
                  P (ms_mem (cfg_ms c'))).
Proof.
intros P PLAW PCALL D fxk ly S Hp W regs mem md k r1 r2 r3 own0 HPRE HAT HPM.
destruct HAT as (HB & HR & HSL & HFL & EHp & HCD & HPG & HM & HH).
pose proof HFL as (Hown & Hf0 & Hf1).
destruct (r6_entry D HPRE) as (HS1a & HS1b & HRAN).
assert (G26 : getr regs 26%bv = w64 own0) by cn_get HR.
assert (G9 : getr regs 9%bv = w64 (cn_S1 D)) by cn_get HR.
unfold CN_READ1.
(* 748 li s7, -1 *)
eapply (cn_hs_addi W fxk regs mem md _ 748 752 23%bv 0%bv (-1));
  [vm_compute; reflexivity | reflexivity | lia | reflexivity |].
intros X1.
destruct (Z.eqb_spec own0 0) as [E0 | N0].
- (* own0 = 0: every copy is non-NULL; the guard calls fuzz_alloc_ran_out *)
  subst own0. destruct (Hf0 eq_refl) as (Nr1 & Nr2 & Nr3).
  (* 752 bnez s10: falls through *)
  eapply (cn_hs_bnez W fxk _ mem _ _ 752 26%bv 188 940 756 true);
    [vm_compute; reflexivity | lia | lia | reflexivity | reflexivity
    | ro_getr; rewrite G26, ro_getr0; reflexivity |].
  intros X2. cbv iota.
  (* 756 jal fuzz_alloc_ran_out *)
  eapply (cn_hs_call W fxk _ mem _ _ 756 760 AS_fuzz_alloc_ran_out); [vm_compute; reflexivity | lia | reflexivity |].
  intros X3.
  eapply SRr_bind.
  { apply (cn_ro_call (fx := fx) B ARx LAWS IMG HRO P PCALL CTX0 D fxk ly S Hp W _ mem _ k 0%nat
      (ci_Lam D) (ci_peak D) (ci_cnt D) (ci_ran D) 0 0 r1 r2 r3 None None None 760 HPRE).
    - unfold cn_ro_rets. ro_in.
    - r6_base HB.
    - cn_rs HR.
    - ro_getr. reflexivity.
    - exact HSL.
    - exact HM.
    - exact HPM. }
  cbv beta.
  intros W2 c2 _ (ly2 & regs2 & mem2 & md2 & k2 & -> & HB2 & HP2 & R10 & HAB2 & HSL2 & HM2 & _ & _ & _ & HPM2).
  assert (HR2 : cn_regsat regs2 (cn_core D ++ [cn_s8; (19%bv, cn_d3 D); (20%bv, cn_size D); (21%bv, cn_d2 D);
    (22%bv, r3); (23%bv, -1); (25%bv, cn_d1 D)])).
  { apply (cn_regsat_pres (regupd (regupd regs 23%bv (v_addi (getr regs 0%bv) (bv_signed (4095%bv : bv 12)))) 1%bv
      (w64 (cn_pc 760))) regs2); [cn_rs HR | exact HP2 | cn_acsl]. }
  assert (G9' : getr regs2 9%bv = w64 (cn_S1 D)) by cn_get HR2.
  pose proof HSL2 as HSLv. unfold cn_slots in HSLv.
  (* 760 ld s10, 24(s1) *)
  eapply (cn_hs_ld W2 fxk regs2 mem2 md2 _ 760 764 26%bv 9%bv 24 (cn_S1 D + 24) r1);
    [vm_compute; reflexivity | reflexivity | lia | reflexivity
    | rewrite G9'; unfold w64; rewrite unsigned_lit_small by lia; reflexivity | lia | lia
    | exact (proj1 (Forall_forall _ _) HSLv (24, r1) ltac:(ro_in)) |].
  intros X4.
  (* 764 bnez a0: g_ran_out = 0 at entry and the ledger is kept, so it falls through *)
  eapply (cn_hs_bnez W2 fxk _ mem2 _ _ 764 10%bv 180 944 768 true);
    [vm_compute; reflexivity | lia | lia | reflexivity | reflexivity
    | ro_getr; rewrite R10, HRAN, ro_getr0; reflexivity |].
  intros X5. cbv iota.
  (* 768 mv a0, s10 *)
  eapply (cn_hs_addi W2 fxk _ mem2 _ _ 768 772 10%bv 26%bv 0);
    [vm_compute; reflexivity | reflexivity | lia | reflexivity |].
  intros X6.
  (* 772 mv a1, s4 *)
  eapply (cn_hs_addi W2 fxk _ mem2 _ _ 772 776 11%bv 20%bv 0);
    [vm_compute; reflexivity | reflexivity | lia | reflexivity |].
  intros X7.
  (* 776 ld a2, 56(s1) *)
  eapply (cn_hs_ld W2 fxk _ mem2 _ _ 776 780 12%bv 9%bv 56 (cn_S1 D + 56) (cn_d1 D));
    [vm_compute; reflexivity | reflexivity | lia | reflexivity
    | ro_getr; rewrite G9'; unfold w64; rewrite unsigned_lit_small by lia; reflexivity | lia | lia
    | exact (proj1 (Forall_forall _ _) HSLv (56, cn_d1 D) ltac:(ro_in)) |].
  intros X8.
  (* 780 jal parse_noting *)
  eapply (cn_hs_call W2 fxk _ mem2 _ _ 780 784 AS_parse_noting); [vm_compute; reflexivity | lia | reflexivity |].
  intros X9.
  apply SRr_ret. split; [right|exact HPM2].
  exists fxk, ly2, S, Hp. do 3 eexists. exists k2, r1, r2, r3. split; [reflexivity|].
  split; [r6_base HB2|].
  split; [cn_rs HR2|].
  split; [exact HSL2|]. split; [exact Nr1|]. split; [exact Nr2|]. split; [exact Nr3|]. split; [exact EHp|].
  (* the events: S is kept across the ran-out call *)
  split; [exact HPG|].
  (* the hull stage is still the copies' (S kept, no reading made yet) *)
  split; [rewrite HRAN in HM2; exact HM2 | exact HH].
- (* own0 <> 0: the copy test jumps straight to the read2 cut *)
  (* 752 bnez s10: taken *)
  eapply (cn_hs_bnez W fxk _ mem _ _ 752 26%bv 188 940 756 false);
    [vm_compute; reflexivity | lia | lia | reflexivity | reflexivity
    | ro_getr; rewrite G26, ro_getr0, ro_c_eq0 by lia; apply Z.eqb_neq; exact N0 |].
  intros X2. cbv iota.
  (* 940 ld s10, 24(s1) *)
  pose proof HSL as HSLv. unfold cn_slots in HSLv.
  eapply (cn_hs_ld W fxk _ mem _ _ 940 944 26%bv 9%bv 24 (cn_S1 D + 24) r1);
    [vm_compute; reflexivity | reflexivity | lia | reflexivity
    | ro_getr; rewrite G9; unfold w64; rewrite unsigned_lit_small by lia; reflexivity | lia | lia
    | exact (proj1 (Forall_forall _ _) HSLv (24, r1) ltac:(ro_in)) |].
  intros X3.
  apply SRr_ret. split; [left|exact HPM].
  (* reading 1 skipped (a copy NULL): no event; the grant parameter o1 is free (None) *)
  exists fxk, ly, S, Hp. do 4 eexists.
  exists (ci_Lam D), (ci_peak D), (ci_cnt D), (ci_ran D), r1, r2, r3, own0, (-1), None, None.
  split; [reflexivity|].
  (* reading 1 skipped: it spent none of its wild budget (0 -> 2) *)
  split; [r6_base_up HB|].
  split; [cn_rs HR|].
  split; [exact HSL|]. split; [exact HFL|].
  split; [exact (r6_mid_nr D ly S Hp W mem _ _ _ _ _ 0 1 r1 r2 r3 None None None HM ltac:(lia))|].
  (* the skip arm: no reading event, reading 1's struct stays zero (st1 = None), and the refused copy is dead at a
     consumer run (read1's own0 <> 0 arm) *)
  split; [intros E; exfalso; exact (N0 E)|].
  split; [intros _; split; [exact HPG|]; split; [reflexivity | exact (HCD N0)]|].
  (* reading 1 skipped: it pays nothing (copies -> rd1) *)
  exact (r6_hull_rd1 S (ci_x D) HH).
Qed.

(* ---- CA7, CN_READ2 -> CN_FREE (the byte set), CN_READ3 (the ran-out flag set) or the parse_noting call (pn2); the
   cut holds after the first parse_noting, so its journal is at wle' SEGS RZ_cf and the segment concludes SRr' ---- *)
Theorem cn_read2_seg : forall P, srr_inv_laws SEGS P -> srr_inv_call SEGS P ->
  forall D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 own0 rc1 st1 o1,
  cn_pre (fx := fx) B ARx CTX0 D ->
  cn_at_read2R (fx := fx) B ARx RCF D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 own0 rc1 st1 o1 -> P mem ->
  SRr' SEGS RZ W (@cn_cfg SEGS fxk (cn_pc CN_READ2) regs mem md)
    (fun W' c' => (cn_ex_freeR (fx := fx) B ARx RCF D W' c' \/ cn_ex_read3R (fx := fx) B ARx RCF D W' c' \/
                   cn_ex_pn2R (fx := fx) B ARx RCF D W' c') /\ P (ms_mem (cfg_ms c'))).
Proof.
intros P PLAW PCALL D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 own0 rc1 st1 o1 HPRE HAT HPM.
destruct HAT as (HB & HR & HSL & HFL & HM & HRES & HNZ & HH).
pose proof HFL as (Hown & Hf0 & _).
destruct (r6_entry D HPRE) as (HS1a & HS1b & HRAN).
assert (G24 : getr regs 24%bv = w64 (VAL (A_HI 9))) by cn_get HR.
assert (G9 : getr regs 9%bv = w64 (cn_S1 D)) by cn_get HR.
pose proof HSL as HSLv. unfold cn_slots in HSLv.
destruct (r6_own_byte W mem) as (b & Hb).
pose proof (u8_range b) as Hb8.
(* the byte the lbu reads is own0, the own cell of the cut's ledger *)
pose proof HM as (_ & _ & _ & HL & _).
pose proof (r6_own_read W mem b own0 Hb
  (PRH_Base.prh_ledger_own B ly S Hp W mem Lam peak cnt SIZE_MAXZ ran (ci_most D) own0 HL)) as Hv.
unfold CN_READ2.
(* the hand steps run at SRr inside the stretch over wle' (the kit's cn_srrG_lift) *)
unfold SRr'. apply (cn_srrG_lift RCF (wle'_trans SEGS RZ) (wle_wle' SEGS RZ)).
(* 944 lbu a0, -1368(s8): the g_own_ran_out byte, read afresh *)
eapply (cn_hs_lbu W fxk regs mem md _ 944 948 10%bv 24%bv (-1368) (VAL (A_OBJ 13)) b);
  [vm_compute; reflexivity | reflexivity | lia | reflexivity | exact (r6_own_addr regs G24) | exact Hb |].
intros X1.
destruct (Z.eqb_spec (bv_unsigned b) 0) as [Ev | Nv].
- (* the byte is 0: so own0 = 0, every copy non-NULL; the guard calls fuzz_alloc_ran_out *)
  assert (E0 : own0 = 0) by lia. clear Hv.
  subst own0. destruct (Hf0 eq_refl) as (Nr1 & Nr2 & Nr3). clear HNZ.
  destruct (HRES eq_refl) as (HPG & HRZ & HRD & HRES1 & HFO1). clear HRES. rename HRES1 into HRES.
  (* 948 beqz a0: taken *)
  eapply (cn_hs_beqz W fxk _ mem _ _ 948 10%bv 16 964 952 true);
    [vm_compute; reflexivity | lia | lia | reflexivity | reflexivity | ro_getr; rewrite ro_getr0, Ev; reflexivity |].
  intros X2. cbv iota.
  (* 964 jal fuzz_alloc_ran_out *)
  eapply (cn_hs_call W fxk _ mem _ _ 964 968 AS_fuzz_alloc_ran_out); [vm_compute; reflexivity | lia | reflexivity |].
  intros X3.
  (* the call, over the cut's relation: out of the stretch, cn_ro_callR at wle', back into a stretch after it *)
  apply SRr_ret. cbv beta.
  eapply (SRrG_bind SEGS RCF (wle'_trans SEGS RZ)).
  { apply (cn_ro_callR (fx := fx) B ARx LAWS IMG HRO RCF (wle'_refl SEGS RZ) (wle'_trans SEGS RZ) (wle_wle' SEGS RZ)
      P PCALL CTX0 D fxk ly S Hp W _ mem _ k 2%nat Lam peak cnt ran 0 1 r1 r2 r3 st1 None None 968 HPRE).
    - unfold cn_ro_rets. ro_in.
    - r6_baseR HB.
    - cn_rs HR.
    - ro_getr. reflexivity.
    - exact HSL.
    - exact HM.
    - exact HPM. }
  cbv beta.
  intros W2 c2 _ (ly2 & regs2 & mem2 & md2 & k2 & -> & HB2 & HP2 & R10 & HAB2 & HSL2 & HM2 & HK1 & _ & _ & HPM2).
  apply (cn_srrG_lift RCF (wle'_trans SEGS RZ) (wle_wle' SEGS RZ)).
  (* reading 1's free-order tie across the ran-out call (the tree bytes kept) *)
  pose proof (HK1 o1 HFO1) as HFO1'. clear HK1 HFO1.
  assert (HR2 : cn_regsat regs2 (cn_core D ++ [cn_s8; (19%bv, cn_d3 D); (20%bv, cn_size D); (21%bv, cn_d2 D);
    (22%bv, r3); (23%bv, rc1); (25%bv, cn_d1 D); (26%bv, r1)])).
  { apply (cn_regsat_pres (regupd (regupd regs 10%bv (Z_to_bv 64 (bv_unsigned b))) 1%bv (w64 (cn_pc 968))) regs2);
      [cn_rs HR | exact HP2 | cn_acsl]. }
  pose proof HM2 as (_ & _ & _ & HL2 & _).
  destruct (prh_ledger_bounds _ _ _ _ _ _ _ _ _ _ _ _ _ HL2) as (_ & _ & _ & _ & Hran).
  pose proof HSL2 as HSLv2. unfold cn_slots in HSLv2.
  assert (G9' : getr regs2 9%bv = w64 (cn_S1 D)) by cn_get HR2.
  revert HRZ. destruct Hran as [Er | Er]; subst ran; intros HRZ.
  + (* g_ran_out = 0: 968 beqz a0 taken, the reading *)
    eapply (cn_hs_beqz W2 fxk regs2 mem2 md2 _ 968 10%bv 12 980 972 true);
      [vm_compute; reflexivity | lia | lia | reflexivity | reflexivity | rewrite R10, ro_getr0; reflexivity |].
    intros X4. cbv iota.
    (* 980 ld a0, 40(s1) *)
    eapply (cn_hs_ld W2 fxk _ mem2 _ _ 980 984 10%bv 9%bv 40 (cn_S1 D + 40) r2);
      [vm_compute; reflexivity | reflexivity | lia | reflexivity
      | rewrite G9'; unfold w64; rewrite unsigned_lit_small by lia; reflexivity | lia | lia
      | exact (proj1 (Forall_forall _ _) HSLv2 (40, r2) ltac:(ro_in)) |].
    intros X5.
    (* 984 mv a1, s4 *)
    eapply (cn_hs_addi W2 fxk _ mem2 _ _ 984 988 11%bv 20%bv 0); [vm_compute; reflexivity | reflexivity | lia | reflexivity |].
    intros X6.
    (* 988 mv a2, s5 *)
    eapply (cn_hs_addi W2 fxk _ mem2 _ _ 988 992 12%bv 21%bv 0); [vm_compute; reflexivity | reflexivity | lia | reflexivity |].
    intros X7.
    (* 992 jal parse_noting *)
    eapply (cn_hs_call W2 fxk _ mem2 _ _ 992 996 AS_parse_noting); [vm_compute; reflexivity | lia | reflexivity |].
    intros X8.
    apply SRr_ret. cbv beta. apply (SRrG_ret SEGS RCF (wle'_refl SEGS RZ)). split; [right; right | exact HPM2].
    exists fxk, ly2, S, Hp. do 3 eexists. exists k2, Lam, peak, cnt, r1, r2, r3, rc1, st1, o1.
    split; [reflexivity|].
    split; [r6_baseR HB2|].
    split; [cn_rs HR2|].
    split; [exact HSL2|]. split; [exact Nr1|]. split; [exact Nr2|]. split; [exact Nr3|].
    (* the events: S is kept across the ran-out call; reading 1 did not run out (g_ran_out = 0) *)
    split; [exact HPG|]. split; [exact (r6_ro1_false D o1 HRZ)|]. split; [exact HRD|].
    split; [exact HFO1'|].
    split; [exact HM2|].
    (* the hull stage is still rd1 (S kept, reading 2 not made yet) *)
    split; [exact HRES | exact HH].
  + (* g_ran_out = 1: 968 beqz a0 falls through, the reading is skipped (rc2 = -1) *)
    eapply (cn_hs_beqz W2 fxk regs2 mem2 md2 _ 968 10%bv 12 980 972 false);
      [vm_compute; reflexivity | lia | lia | reflexivity | reflexivity | rewrite R10, ro_getr0; reflexivity |].
    intros X4. cbv iota.
    (* 972 li s9, -1 *)
    eapply (cn_hs_addi W2 fxk _ mem2 _ _ 972 976 25%bv 0%bv (-1)); [vm_compute; reflexivity | reflexivity | lia | reflexivity |].
    intros X5.
    (* 976 j +24 *)
    eapply (cn_hs_j W2 fxk _ mem2 _ _ 976 1000 24); [vm_compute; reflexivity | lia | reflexivity | lia |].
    intros X6.
    apply SRr_ret. cbv beta. apply (SRrG_ret SEGS RCF (wle'_refl SEGS RZ)). split; [right; left | exact HPM2].
    exists fxk, ly2, S, Hp. do 3 eexists. exists k2, Lam, peak, cnt, 1, r1, r2, r3, rc1, (-1), st1, None, o1, None.
    split; [reflexivity|].
    (* reading 2 skipped: it spent none of its wild budget (2 -> 4) *)
    split; [r6_base_upR HB2|].
    split; [cn_rs HR2|].
    split; [exact HSL2|]. split; [exact Nr1|]. split; [exact Nr2|]. split; [exact Nr3|].
    (* reading 1 ran out (g_ran_out = 1): reading 2 skipped, no event (r6_revs2_skip), its struct zero *)
    split; [rewrite (r6_revs2_skip D o1 (r6_ro1_true D o1 HRZ)); exact HPG|]. split; [exact HRZ|].
    split; [exact (r6_rds2_skip D o1 st1 (r6_ro1_true D o1 HRZ) HRD)|].
    (* the ties: reading 1's across the call, reading 2's struct None (cn_fo True) *)
    split; [exact HFO1'|]. split; [exact I|].
    split; [exact (r6_mid_nr D ly2 S Hp W2 mem2 _ _ _ _ _ 1 2 r1 r2 r3 st1 None None HM2 ltac:(lia))|].
    split; [exact HRES|]. split; [unfold cn_res; intros E; discriminate E|].
    (* reading 2 skipped: it pays nothing (rd1 -> rd2) *)
    exact (r6_hull_rd2 S (ci_x D) HH).
- (* the byte is non-zero: 948 beqz falls through, r = 1, the free exit's ownl = own0 *)
  eapply (cn_hs_beqz W fxk _ mem _ _ 948 10%bv 16 964 952 false);
    [vm_compute; reflexivity | lia | lia | reflexivity | reflexivity
    | ro_getr; rewrite ro_getr0, r6_byte_w64, ro_c_eq0 by lia; apply Z.eqb_neq; exact Nv |].
  intros X2. cbv iota.
  (* 952 ld s9, 56(s1) *)
  eapply (cn_hs_ld W fxk _ mem _ _ 952 956 25%bv 9%bv 56 (cn_S1 D + 56) (cn_d1 D));
    [vm_compute; reflexivity | reflexivity | lia | reflexivity
    | ro_getr; rewrite G9; unfold w64; rewrite unsigned_lit_small by lia; reflexivity | lia | lia
    | exact (proj1 (Forall_forall _ _) HSLv (56, cn_d1 D) ltac:(ro_in)) |].
  intros X3.
  (* 956 li s5, 1 *)
  eapply (cn_hs_addi W fxk _ mem _ _ 956 960 21%bv 0%bv 1); [vm_compute; reflexivity | reflexivity | lia | reflexivity |].
  intros X4.
  (* 960 j +100 *)
  eapply (cn_hs_j W fxk _ mem _ _ 960 1060 100); [vm_compute; reflexivity | lia | reflexivity | lia |].
  intros X5.
  apply SRr_ret. cbv beta. apply (SRrG_ret SEGS RCF (wle'_refl SEGS RZ)). split; [left | exact HPM].
  exists fxk, ly, S, Hp. do 4 eexists.
  exists Lam, peak, cnt, ran, r1, r2, r3, 1, own0, st1, None, None, None, None, None.
  split; [reflexivity|].
  (* readings 2 and 3 never run on this path: none of their wild budget is spent (2 -> 6) *)
  split; [r6_base_upR HB|].
  split; [cn_rs HR|].
  split; [exact HSL|].
  split; [exact (r6_mid_nr D ly S Hp W mem _ _ _ _ _ 1 3 r1 r2 r3 st1 None None HM ltac:(lia))|].
  (* r = 1 by ownl = own0 <> 0; the events clause speaks only at ownl = 0; the refused-copy clause is read2's skip
     arm (st1 = None, the refusal dead at a consumer run) with structs 2 and 3 still zero *)
  split; [lia|]. split; [left; split; [reflexivity | left; lia]|].
  split; [intros E; exfalso; clear - Hv Nv E; lia|].
  split.
  { intros Hne. destruct (HNZ Hne) as (HPG0 & Hst1 & HCD).
    split; [exact HPG0|]. split; [exact Hst1|]. split; [reflexivity|]. split; [reflexivity | exact HCD]. }
  (* readings 2 and 3 skipped: they pay nothing (rd1 -> rd2 -> rd0) *)
  exact (r6_hull_rd0 S (ci_x D) (r6_hull_rd2 S (ci_x D) HH)).
Qed.

(* ---- CA8, CN_READ3 -> CN_CMP (the ran-out flag set) or the parse_noting call (pn3); the cut's own is 0, so the byte
   read is 0 and the CN_FREE disjunct of the contract's exit is never taken. The cut holds only after a reading
   position (cn_at_read3 at wle' SEGS RZ_cf), so the segment concludes SRr' ---- *)
Theorem cn_read3_seg : forall P, srr_inv_laws SEGS P -> srr_inv_call SEGS P ->
  forall D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 rc1 rc2 st1 st2 o1 o2,
  cn_pre (fx := fx) B ARx CTX0 D ->
  cn_at_read3R (fx := fx) B ARx RCF D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 rc1 rc2 st1 st2 o1 o2 ->
  P mem ->
  SRr' SEGS RZ W (@cn_cfg SEGS fxk (cn_pc CN_READ3) regs mem md)
    (fun W' c' => (cn_ex_freeR (fx := fx) B ARx RCF D W' c' \/ cn_ex_cmpR (fx := fx) B ARx RCF D W' c' \/
                   cn_ex_pn3R (fx := fx) B ARx RCF D W' c') /\ P (ms_mem (cfg_ms c'))).
Proof.
intros P PLAW PCALL D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 rc1 rc2 st1 st2 o1 o2 HPRE HAT HPM.
destruct HAT as (HB & HR & HSL & Nr1 & Nr2 & Nr3 & HPG & HRZ & HRDS & HFO1 & HFO2 & HM & HRES1 & HRES2 & HH).
destruct (r6_entry D HPRE) as (HS1a & HS1b & HRAN).
assert (G24 : getr regs 24%bv = w64 (VAL (A_HI 9))) by cn_get HR.
destruct (r6_own_byte W mem) as (b & Hb).
(* the byte the lbu reads is the own of the cut's ledger, 0: `bnez a0` never jumps to the free cut *)
pose proof HM as (_ & _ & _ & HL & _).
pose proof (r6_own_read W mem b 0 Hb
  (PRH_Base.prh_ledger_own B ly S Hp W mem Lam peak cnt SIZE_MAXZ ran (ci_most D) 0 HL)) as Ev.
unfold CN_READ3.
(* the hand steps run at SRr inside the stretch over wle' (the kit's cn_srrG_lift) *)
unfold SRr'. apply (cn_srrG_lift RCF (wle'_trans SEGS RZ) (wle_wle' SEGS RZ)).
(* 1000 li s5, 1 *)
eapply (cn_hs_addi W fxk regs mem md _ 1000 1004 21%bv 0%bv 1); [vm_compute; reflexivity | reflexivity | lia | reflexivity |].
intros X1.
(* 1004 lbu a0, -1368(s8): the g_own_ran_out byte, read afresh *)
eapply (cn_hs_lbu W fxk _ mem _ _ 1004 1008 10%bv 24%bv (-1368) (VAL (A_OBJ 13)) b);
  [vm_compute; reflexivity | reflexivity | lia | reflexivity
  | apply r6_own_addr; ro_getr; exact G24 | exact Hb |].
intros X2.
(* 1008 bnez a0: falls through, the guard calls fuzz_alloc_ran_out *)
eapply (cn_hs_bnez W fxk _ mem _ _ 1008 10%bv 48 1056 1012 true);
  [vm_compute; reflexivity | lia | lia | reflexivity | reflexivity | ro_getr; rewrite ro_getr0, Ev; reflexivity |].
intros X3. cbv iota.
(* 1012 jal fuzz_alloc_ran_out *)
eapply (cn_hs_call W fxk _ mem _ _ 1012 1016 AS_fuzz_alloc_ran_out); [vm_compute; reflexivity | lia | reflexivity |].
intros X4.
(* the call, over the cut's relation: out of the stretch, cn_ro_callR at wle', back into a stretch after it *)
apply SRr_ret. cbv beta.
eapply (SRrG_bind SEGS RCF (wle'_trans SEGS RZ)).
{ apply (cn_ro_callR (fx := fx) B ARx LAWS IMG HRO RCF (wle'_refl SEGS RZ) (wle'_trans SEGS RZ) (wle_wle' SEGS RZ)
    P PCALL CTX0 D fxk ly S Hp W _ mem _ k 4%nat Lam peak cnt ran 0 2 r1 r2 r3 st1 st2 None 1016 HPRE).
  - unfold cn_ro_rets. ro_in.
  - r6_baseR HB.
  - cn_rs HR.
  - ro_getr. reflexivity.
  - exact HSL.
  - exact HM.
  - exact HPM. }
cbv beta.
intros W2 c2 _ (ly2 & regs2 & mem2 & md2 & k2 & -> & HB2 & HP2 & R10 & HAB2 & HSL2 & HM2 & HK1 & HK2 & _ & HPM2).
apply (cn_srrG_lift RCF (wle'_trans SEGS RZ) (wle_wle' SEGS RZ)).
(* readings 1 and 2's free-order ties across the ran-out call (the tree bytes kept) *)
pose proof (HK1 o1 HFO1) as HFO1'. pose proof (HK2 o2 HFO2) as HFO2'. clear HK1 HK2 HFO1 HFO2.
assert (HR2 : cn_regsat regs2 (cn_core D ++ [cn_s8; (19%bv, cn_d3 D); (20%bv, cn_size D); (21%bv, 1);
  (22%bv, r3); (23%bv, rc1); (25%bv, rc2); (26%bv, r1)])).
{ apply (cn_regsat_pres (regupd (regupd (regupd regs 21%bv (v_addi (getr regs 0%bv) 1)) 10%bv
    (Z_to_bv 64 (bv_unsigned b))) 1%bv (w64 (cn_pc 1016))) regs2); [cn_rs HR | exact HP2 | cn_acsl]. }
pose proof HM2 as (_ & _ & _ & HL2 & _).
destruct (prh_ledger_bounds _ _ _ _ _ _ _ _ _ _ _ _ _ HL2) as (_ & _ & _ & _ & Hran).
revert HRZ. destruct Hran as [Er | Er]; subst ran; intros HRZ.
- (* g_ran_out = 0: 1016 beqz a0 taken, the reading *)
  eapply (cn_hs_beqz W2 fxk regs2 mem2 md2 _ 1016 10%bv 12 1028 1020 true);
    [vm_compute; reflexivity | lia | lia | reflexivity | reflexivity | rewrite R10, ro_getr0; reflexivity |].
  intros X5. cbv iota.
  (* 1028 mv a0, s6 *)
  eapply (cn_hs_addi W2 fxk _ mem2 _ _ 1028 1032 10%bv 22%bv 0); [vm_compute; reflexivity | reflexivity | lia | reflexivity |].
  intros X6.
  (* 1032 mv a1, s4 *)
  eapply (cn_hs_addi W2 fxk _ mem2 _ _ 1032 1036 11%bv 20%bv 0); [vm_compute; reflexivity | reflexivity | lia | reflexivity |].
  intros X7.
  (* 1036 mv a2, s3 *)
  eapply (cn_hs_addi W2 fxk _ mem2 _ _ 1036 1040 12%bv 19%bv 0); [vm_compute; reflexivity | reflexivity | lia | reflexivity |].
  intros X8.
  (* 1040 jal parse_noting *)
  eapply (cn_hs_call W2 fxk _ mem2 _ _ 1040 1044 AS_parse_noting); [vm_compute; reflexivity | lia | reflexivity |].
  intros X9.
  apply SRr_ret. cbv beta. apply (SRrG_ret SEGS RCF (wle'_refl SEGS RZ)). split; [right; right | exact HPM2].
  exists fxk, ly2, S, Hp. do 3 eexists. exists k2, Lam, peak, cnt, r1, r2, r3, rc1, rc2, st1, st2, o1, o2.
  split; [reflexivity|].
  split; [r6_baseR HB2|].
  split; [cn_rs HR2|].
  split; [exact HSL2|]. split; [exact Nr1|]. split; [exact Nr2|]. split; [exact Nr3|].
  (* the events: S is kept across the ran-out call; neither reading ran out (g_ran_out = 0) *)
  destruct (r6_ro2_false D o1 o2 HRZ) as (Hro1 & Hro2).
  destruct (r6_rds2_rd D o1 o2 st1 st2 Hro1 HRDS) as (Hrd1 & Hrd2).
  split; [exact HPG|]. split; [exact Hro1|]. split; [exact Hro2|]. split; [exact Hrd1|]. split; [exact Hrd2|].
  split; [exact HFO1'|]. split; [exact HFO2'|].
  split; [exact HM2|]. split; [exact HRES1|].
  (* the hull stage is still rd2 (S kept, reading 3 not made yet) *)
  split; [exact HRES2 | exact HH].
- (* g_ran_out = 1: 1016 beqz a0 falls through, the reading is skipped (rc3 = -1) *)
  eapply (cn_hs_beqz W2 fxk regs2 mem2 md2 _ 1016 10%bv 12 1028 1020 false);
    [vm_compute; reflexivity | lia | lia | reflexivity | reflexivity | rewrite R10, ro_getr0; reflexivity |].
  intros X5. cbv iota.
  (* 1020 li s4, -1 *)
  eapply (cn_hs_addi W2 fxk _ mem2 _ _ 1020 1024 20%bv 0%bv (-1)); [vm_compute; reflexivity | reflexivity | lia | reflexivity |].
  intros X6.
  (* 1024 j +24 *)
  eapply (cn_hs_j W2 fxk _ mem2 _ _ 1024 1048 24); [vm_compute; reflexivity | lia | reflexivity | lia |].
  intros X7.
  apply SRr_ret. cbv beta. apply (SRrG_ret SEGS RCF (wle'_refl SEGS RZ)). split; [right; left | exact HPM2].
  exists fxk, ly2, S, Hp. do 3 eexists.
  exists k2, Lam, peak, cnt, 1, r1, r2, r3, rc1, rc2, (-1), st1, st2, None, o1, o2, None.
  split; [reflexivity|].
  (* reading 3 skipped: it spent none of its wild budget (4 -> 6) *)
  split; [r6_base_upR HB2|].
  split; [cn_rs HR2|].
  split; [exact HSL2|]. split; [exact Nr1|]. split; [exact Nr2|]. split; [exact Nr3|].
  (* a reading ran out (g_ran_out = 1): reading 3 skipped, no event (r6_revs3_skip), its struct zero *)
  split; [rewrite (r6_revs3_skip D o1 o2 HRZ); exact HPG|]. split; [exact HRZ|].
  split; [exact (r6_rds3_skip D o1 o2 st1 st2 HRZ HRDS)|].
  (* the ties: readings 1 and 2's across the call, reading 3's struct None (cn_fo True) *)
  split; [exact HFO1'|]. split; [exact HFO2'|]. split; [exact I|].
  split; [exact (r6_mid_nr D ly2 S Hp W2 mem2 _ _ _ _ _ 2 3 r1 r2 r3 st1 st2 None HM2 ltac:(lia))|].
  split; [exact HRES1|]. split; [exact HRES2|].
  split; [unfold cn_res; intros E; discriminate E|].
  (* reading 3 skipped: it pays nothing (rd2 -> rd0) *)
  exact (r6_hull_rd0 S (ci_x D) HH).
Qed.

End r6.

(* the audit: each lemma closed under the Section hypotheses (LAWS, IMG, HRO), discharged as premises here *)
Print Assumptions cn_read1_seg.
Print Assumptions cn_read2_seg.
Print Assumptions cn_read3_seg.
