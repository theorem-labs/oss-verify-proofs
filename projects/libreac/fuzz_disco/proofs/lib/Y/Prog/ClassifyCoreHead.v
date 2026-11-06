(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths, module names and numbers changed; 681 of its 854 lines of code are new or changed and 1105 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC44 YC8g YC8i YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YC1g YC1h YC81 YC4b YC45 YC85 YCkd YC1i YCbf YCj1 YCjr YCja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import ClassifyCore ClassifyCoreSeg.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require CtrlParsed RcParse RcLeaf disco_classify_c.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition ch_extra (uc : Z) : list word := Z_to_bv 64 SB :: repeat (Z_to_bv 64 0) 26 ++ [Z_to_bv 64 uc].
Definition ch_regions : smem :=
[ stack_region 176; got_regionP; bcell_regionP 32; uar_got_regionP 59; uar_cell_regionP 59 ].
Definition ch_facts : facts :=
mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SB SB 0); (59%nat, mkAF IMG_LO IMG_TOP 2) ] [] [].
Definition ss_ch : sstate := mkSS AF_both3_classify_core sr_atoms ch_regions None ch_facts.
Definition trim_lo (r : YP09.region) (lo : Z) : YP09.region :=
YP09.mkRegion (YP09.r_base r) lo (YP09.r_hi r) (Z.max lo (YP09.r_wlo r)) (YP09.r_whi r)
(filter (fun c => lo <=? YP09.c_off c) (YP09.r_chunks r)).
Definition trim_stack (rs : smem) (lo : Z) : smem :=
match rs with [] => [] | r :: t => trim_lo r lo :: t end.
(* SPEED (a Theorem Labs lane, from the A twin lib/A/Prog/ClassifyCoreHead.v:41-57, verbatim): the shadow byte pattern is
   checked by computation (ch_pat_ok0 below) instead of 32 rewrites, each a lia over the walk's whole context *)
Definition ch_cb (c : YP09.chunk) (i : Z) : option Z :=
match YP09.c_val c with
| CVal w (SLit z) => if (YP09.c_off c <=? i) && (i <? YP09.c_off c + Z.of_N w)
  then Some (bv_unsigned (byte_of_word (Z_to_bv 64 z) (i - YP09.c_off c))) else None
| CZero len => if (YP09.c_off c <=? i) && (i <? YP09.c_off c + len) then Some 0 else None
| _ => None
end.
Fixpoint ch_look (cs : list YP09.chunk) (i : Z) : option Z :=
match cs with [] => None | c :: t => match ch_cb c i with Some v => Some v | None => ch_look t i end end.
Fixpoint ch_pat (cs : list YP09.chunk) (j : Z) (l : list Z) : bool :=
match l with
| [] => true
| v :: t => match ch_look cs j with
  | Some v' => (v' =? v) && (0 <=? v) && (v <? 256) && ch_pat cs (j + 1) t
  | None => false
  end
end.
Lemma denot_and_m32_add0 : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v + c -> v + c < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_AND (SOff n c) (SLit (-32))) (SLit 0)) = Z_to_bv 64 (32 * ((v + c) / 32)).
Proof.
intros E n v c Hn H0 H1 Hv.
assert (Hq : 0 <= 32 * ((v + c) / 32) < 2 ^ 64).
{ split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
  pose proof (Z.mul_div_le (v + c) 32 ltac:(lia)). lia. }
rewrite denot_lit_U. f_equal.
rewrite !U_SAlu. cbn [zalu_raw]. rewrite !U_SLit, (U_atom_off E n v c Hn) by lia.
change (zcanon (-32)) with (2 ^ 64 - 32). rewrite land_m32 by lia.
rewrite (zcanon_id (32 * ((v + c) / 32))) by (unfold M64; lia).
rewrite (zcanon_id 0) by (unfold M64; lia). rewrite Z.add_0_r.
apply zcanon_id. unfold M64. lia.
Qed.
Ltac ro_win := apply (proj1 (Z.leb_le _ _)); vm_compute; reflexivity.
Ltac awr_ch_rec hd := first [ apply awr_ok_nil | apply awr_ok_cons_ro; [first [ro_win | cbn; lia]|]; awr_ch_rec hd | hd; awr_ch_rec hd ].
Ltac awr_ch hd := lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0q fp b0 bc lyq ownq) end; awr_ch_rec hd.
Ltac awr_hd2 U2 U60 sp0v spv sp1v :=
lazymatch goal with
| |- awr_ok _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spv - sp0v));
  [reflexivity | rewrite U2; lia | cbn; lia | cbn; lia |]
| |- awr_ok _ (YP09.mkRegion (Some 60%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 60%nat (sp1v - sp0v));
  [reflexivity | rewrite U60; lia | cbn; lia | cbn; lia |]
end.
Ltac ch_fsb_lits := repeat match goal with
| |- context [fs_frame_bytes ?c / 8] => let v := eval vm_compute in (fs_frame_bytes c / 8) in
lazymatch v with Zpos _ => change (fs_frame_bytes c / 8) with v end
| |- context [fs_frame_bytes ?c] => let v := eval vm_compute in (fs_frame_bytes c) in
lazymatch v with Zpos _ => change (fs_frame_bytes c) with v end
end.
Ltac ch_awrF_rec hd AG fpos F EFA :=
lazymatch goal with
| |- awr_ok _ [] _ _ _ _ _ _ _ => apply awr_ok_nil
| |- awr_ok _ (YP09.mkRegion _ _ _ ?wlo ?whi _ :: _) _ _ _ _ _ _ _ =>
first
[ lazymatch (eval vm_compute in (Z.leb whi wlo)) with true => apply awr_ok_cons_ro; [clear; cbn; lia|] end
| hd
| lazymatch goal with
| |- awr_ok _ (YP09.mkRegion (Some 529%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ ((?c, _) :: _) =>
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 529%nat); [reflexivity | evalE AG | | ];
[ cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right; exists c, fpos; split; [left; reflexivity|]; right;
unfold in_zr, shadow_addr; cbn [fst snd]; rewrite <- SB_SHADOW_OFF; ch_fsb_lits; rewrite ?EFA; fold F; unfold SB; clear - Ha; lia
| ]
| |- awr_ok _ (YP09.mkRegion (Some 516%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ ((?c, _) :: _) =>
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 516%nat); [reflexivity | evalE AG | | ];
[ cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right; exists c, fpos; split; [left; reflexivity|]; left;
unfold in_zr; cbn [fst snd]; ch_fsb_lits; rewrite ?EFA; fold F; clear - Ha; lia
| ]
end ];
ch_awrF_rec hd AG fpos F EFA
end.
Ltac ch_awrFL hd AG fpos F EFA :=
lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
ch_awrF_rec hd AG fpos F EFA.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
Context {PX : PAXcalls lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ASM2 : forall fq, astack_malloc_realizes (fx := fq) SEGS B 2.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis KS : cls_kept_step_ok B.

Definition ECH (regs : bvmap 5 word) : env := Eimg (Ereg regs (ch_extra (as_uar_cell B))).

Lemma ch_entry : forall (fq : YK11.FPState) lyc Sc (W : world SEGS) (regs : bvmap 5 word) memc mdc,
AR SEGS B lyc Sc W memc mdc ->
(forall a, spZ regs - 176 <= a < spZ regs -> apresent (w_H W) memc a) ->
2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
st_ok_pi (fx := fq) SEGS VAL (ECH regs) ss_ch
(restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + AF_both3_classify_core)) memc (seg_rom SEGS))).
Proof.
intros fq lyc Sc W regs memc mdc HAR Hpres Hsp Hsp16.
pose proof pa_B_ok as HBASE.
destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
rewrite (palf_got_uar B TLF) in Kguar.
pose proof (pa_obj_img 0 ltac:(lia)) as Hob0. pose proof (pa_obj_img 1 ltac:(lia)) as Hob1.
pose proof (pa_obj_img 12 ltac:(lia)) as Hob12.
pose proof (palf_uar_img B TLF) as Huar. pose proof (palf_uar_al B TLF) as Huar4.
pose proof (pal_got_cell B TL) as Hgc.
rewrite restrict_mkst_fx. unfold ss_ch.
set (E := ECH regs).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (ch_extra (as_uar_cell B))) n)
by (intros n Hn; unfold E, ECH; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E59 : ew E 59 = Z_to_bv 64 (as_uar_cell B))
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 27)).
assert (EO : forall i, (i < 68)%nat -> ew E (A_OBJ i) = Z_to_bv 64 (VAL (A_OBJ i)))
by (intros i Hi; unfold E, ECH; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (EO 0%nat ltac:(lia)) as E241. pose proof (EO 1%nat ltac:(lia)) as E242.
pose proof (EO 12%nat ltac:(lia)) as E253.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v0, ew E n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 -> base_val E (Some n) = v0)
by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
pose proof (pa_val_range (A_OBJ 0)) as R241. pose proof (pa_val_range (A_OBJ 1)) as R242.
pose proof (pa_val_range (A_OBJ 12)) as R253.
unfold IMG_LO, IMG_TOP in *.
apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold ch_regions, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
    [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kgot).
  + rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SB);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kcell).
  + rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff 59 0) (as_uar_cell B));
    [cbn [sv_denot]; rewrite E59, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kguar).
  + rewrite (VB 59%nat (as_uar_cell B) E59) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (as_uar_cell B) 0 4 (SLit 1) 1);
    [reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H W) memc _ _ Kuar).
- apply pairwise_disjoint_of_extents.
  unfold ch_regions, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241), (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242),
  (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253), (VB 59%nat (as_uar_cell B) E59) by lia.
  cbn [base_val]. rewrite Usp.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  pose proof (palf_sep B TLF) as Hsep4.
  cbn [zseps zseps_from fst snd] in Hsep4.
  revert Hgc Hsep4 Hob0 Hob1 Hob12 Huar Huar4 R241 R242 R253 Hsp. clear.
  unfold A_OBJ, Nat.add. intros. repeat split; first [exact I | lia].
- split; [|split; [exact I | exact I]].
  cbn [ch_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, E32, E59, !unsigned_lit_small by (unfold SB; lia).
  change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
  revert Hsp Hsp16 Huar Huar4. clear.
  unfold SB, IMG_LO, IMG_TOP. intros.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.

Lemma ch_shadow_lt : forall x n a, 0 <= x -> 0 <= n -> x + n <= alloc_ceiling ->
in_zr a (shadow_addr x, n / 8) -> 0 <= a < alloc_ceiling.
Proof.
intros x n a Hx Hn Hxn Ha. unfold in_zr, shadow_addr, SHADOW_OFF in Ha. cbn [fst snd] in Ha.
pose proof asan_consts as (C1 & _).
assert (D1 : x / 8 + n / 8 <= (x + n) / 8).
{ apply Z.div_le_lower_bound; [lia|].
  pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
  pose proof (Z.div_mod n 8 ltac:(lia)). pose proof (Z.mod_pos_bound n 8 ltac:(lia)). lia. }
assert (D2 : (x + n) / 8 <= alloc_ceiling / 8) by (apply Z.div_le_mono; lia).
assert (D3 : 8 * (alloc_ceiling / 8) <= alloc_ceiling) by (apply Z.mul_div_le; lia).
assert (D4 : 0 <= x / 8) by (apply Z.div_pos; lia).
lia.
Qed.

Lemma ch_kept_sm : forall lyc Sc (W : world SEGS) memc mdc (memA mem2 : word -> option byte) SP slo shi lk o L,
AR SEGS B lyc Sc W memc mdc ->
alloc_ceiling <= SP - CLS_STK -> SP - CLS_STK <= slo -> shi <= SP ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (SP - 176 <= a < SP) -> aview SEGS (w_H W) memA a = aview SEGS (w_H W) memc a) ->
(forall a, apresent (w_H W) memc a -> apresent (w_H W) memA a) ->
acall_kept SEGS B lyc Sc W memA W mem2 slo shi (fun _ => False) ->
(forall a, SP - CLS_STK <= a < SP -> apresent (w_H W) mem2 a) ->
tcls_kept B lyc Sc W memc W mem2 SP lk o L.
Proof.
intros lyc Sc W memc mdc memA mem2 SP slo shi lk o L HAR Hce Hslo Hshi KA PA (K1 & K2 & K3 & K4 & K5 & K6) Hwin.
pose proof pa_segs_low as Hsegs. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HCS : CLS_STK = ltac:(let v := eval vm_compute in CLS_STK in exact v)) by reflexivity.
split; [|split; [|split; [|split; [|split]]]].
- intros a Ha Hw _. rewrite (K1 a Ha ltac:(lia)). apply KA; lia.
- intros b m i Hb Hi _. rewrite (K2 b m i Hb Hi (fun x => x)).
  destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & Hb4096 & Hbceil & _).
  apply KA; lia.
- intros a Himg Hown Herr. rewrite (K3 a Himg Hown Herr). pose proof (Hsegs a Himg). apply KA; lia.
- intros cid pos a Hf Hr _. rewrite (K4 cid pos a Hf Hr (fun x => x)).
  destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hf) as (Hf4096 & Hfceil & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hfb.
  assert (Hab : 0 <= a < alloc_ceiling).
  { destruct Hr as [Hr | Hr]; [unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; lia|].
    exact (ch_shadow_lt (frame_addr lyc cid pos) (fs_frame_bytes cid) a ltac:(lia) Hfb ltac:(lia) Hr). }
  apply KA; lia.
- intros a Ha Hw Hp. apply (K5 a Ha ltac:(lia)). apply PA. exact Hp.
- exact Hwin.
Qed.

Lemma ch_obj_kept : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k
(memA mem2 : word -> option byte) SP slo shi a,
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a ->
alloc_ceiling <= SP - CLS_STK -> ~ (SP - CLS_STK <= a < SP) -> SP - CLS_STK <= slo -> shi <= SP ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (SP - 176 <= a < SP) -> aview SEGS (w_H W) memA a = aview SEGS (w_H W) memc a) ->
acall_kept SEGS B lyc Sc W memA W mem2 slo shi (fun _ => False) ->
aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memc a.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k memA mem2 SP slo shi a HJ Hw Hce Hna Hslo Hshi KA (K1 & K2 & K3 & K4 & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hceil & Hslo0 & Hshi0 & H47 & _) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HCS : CLS_STK = ltac:(let v := eval vm_compute in CLS_STK in exact v)) by reflexivity.
destruct (awr_byte_cases SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw) as
(_ & [(Hce' & Hwin) | [(Happ & b & n & Hin & Hr & _) | (cid & pos & Hin & [(Happ & Hr) | (Hsh & Hr)])]]).
- rewrite (K1 a ltac:(lia) ltac:(lia)). apply KA; lia.
- destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b n HAR Hin) as (_ & Hb4096 & Hbceil & _).
  replace a with (b + (a - b)) by lia. rewrite (K2 b n (a - b) Hin ltac:(lia) (fun x => x)).
  apply KA; lia.
- assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hin).
  destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hin') as (Hf4096 & Hfceil & _).
  rewrite (K4 cid pos a Hin' (or_introl Hr) (fun x => x)).
  unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr. apply KA; lia.
- assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hin).
  destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hin') as (Hf4096 & Hfceil & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hfb.
  pose proof (ch_shadow_lt (frame_addr lyc cid pos) (fs_frame_bytes cid) a ltac:(lia) Hfb ltac:(lia) Hr) as Ha.
  rewrite (K4 cid pos a Hin' (or_intror Hr) (fun x => x)). apply KA; lia.
Qed.

Lemma ch_obj_sep : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k S2 (W2 : world SEGS) mem2 md2 fpos a,
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a ->
AR SEGS B lyc S2 W2 mem2 md2 -> frames S2 = (2, fpos) :: frames Sc ->
ablocks B lyc S2 = ablocks B lyc Sc ->
(a < kLowMemEnd - 1 \/ kHighMemBeg <= a) ->
~ (frame_addr lyc 2 fpos <= a < frame_addr lyc 2 fpos + 256) /\
~ (SHADOW_OFF + frame_addr lyc 2 fpos / 8 <= a < SHADOW_OFF + frame_addr lyc 2 fpos / 8 + 32).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k S2 W2 mem2 md2 fpos a HJ Hw HAR2 Hfrs2 Eab Hap.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hceil & Hslo0 & Hshi0 & H47 & _) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hfin2 : In (2, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 2 fpos HAR2 Hfin2) as (HF4096 & HFceil & _).
change (fs_frame_bytes 2) with 256 in HFceil.
assert (HF8 : frame_addr lyc 2 fpos / 8 <= alloc_ceiling / 8) by (apply Z.div_le_mono; lia).
assert (HF8' : 8 * (alloc_ceiling / 8) <= alloc_ceiling) by (apply Z.mul_div_le; lia).
assert (HF0 : 0 <= frame_addr lyc 2 fpos / 8) by (apply Z.div_pos; lia).
split; [| unfold SHADOW_OFF; lia].
destruct (awr_byte_cases SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw) as
(_ & [(Hce & Hwin) | [(Happ & b & n & Hin & Hr & _) | (cid & pos & Hin & [(Happ & Hr) | (Hsh & Hr)])]]).
- lia.
- pose proof (sep_block_frame SEGS B LAWS lyc S2 W2 mem2 md2 b n 2 fpos HAR2 ltac:(rewrite Eab; exact Hin) Hfin2) as Hd.
  unfold zdisjoint in Hd; cbn [fst snd] in Hd. change (fs_frame_bytes 2) with 256 in Hd. lia.
- assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hin).
  destruct (in_split _ _ Hin') as (l1 & l2 & El).
  pose proof (sep_frames_pos SEGS B LAWS lyc S2 W2 mem2 md2 (2, fpos) (cid, pos) [] l1 l2 HAR2
    ltac:(rewrite Hfrs2, El; reflexivity)) as Hd.
  unfold zdisjoint, frame_rng in Hd; cbn [fst snd] in Hd. change (fs_frame_bytes 2) with 256 in Hd.
  unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr. lia.
- lia.
Qed.

(* SPEED (a Theorem Labs lane, from the A twin lib/A/Prog/ClassifyCoreHead.v:292-316, verbatim): HXk as a lemma, so its
   lia calls see only their own premises, not the walk's whole context *)
Lemma ch_xk : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k S2 mem2 md2 fpos
(memA mem3 : word -> option byte) SP slo shi p n a,
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
AR SEGS B lyc S2 W mem2 md2 -> frames S2 = (2, fpos) :: frames Sc -> ablocks B lyc S2 = ablocks B lyc Sc ->
alloc_ceiling <= SP - CLS_STK -> SP - CLS_STK <= slo -> shi <= SP ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (SP - 176 <= a < SP) -> aview SEGS (w_H W) memA a = aview SEGS (w_H W) memc a) ->
acall_kept SEGS B lyc Sc W memA W mem2 slo shi (fun _ => False) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (SP - CLS_STK <= a < SP) -> ~ (frame_addr lyc 2 fpos <= a < frame_addr lyc 2 fpos + 256) ->
  ~ (SB + frame_addr lyc 2 fpos / 8 <= a < SB + frame_addr lyc 2 fpos / 8 + 32) ->
  aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) mem2 a) ->
cls_read W memc SP p n -> cls_write B STK sp0 FP ly S lyc Sc own p n -> p <= a < p + n ->
aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) memc a.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k S2 mem2 md2 fpos memA mem3 SP slo shi p n a
  HJ HAR2 Hfrs2 Eab Hce Hslo Hshi KA HK HKH HOr HOw Ha.
pose proof HOr as (HO0 & HO63 & HOam & HOsp & _).
pose proof (HOw a Ha) as Hwa.
assert (Hap : a < kLowMemEnd - 1 \/ kHighMemBeg <= a) by (clear - HOam Ha; unfold amem_range in HOam; lia).
assert (Ha64 : 0 <= a < 2 ^ 64) by (clear - HO0 HO63 Ha; lia).
assert (Hasp : ~ (SP - CLS_STK <= a < SP)) by (clear - HOsp Ha; lia).
destruct (ch_obj_sep STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k S2 W mem2 md2 fpos a HJ Hwa HAR2 Hfrs2 Eab Hap)
  as [Hs1 Hs2].
rewrite (HKH a Ha64 Hasp Hs1 ltac:(rewrite SB_SHADOW_OFF; exact Hs2)).
exact (ch_obj_kept STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k memA mem2 SP slo shi a HJ Hwa Hce Hasp Hslo Hshi KA HK).
Qed.

Lemma ch_garr8_kept : forall H H' (m m' : word -> option byte) base l,
(forall i, 0 <= i < Z.of_nat (length l) -> aview SEGS H' m' (base + i) = aview SEGS H m (base + i)) ->
garr8 SEGS (mrestrict H m) base l -> garr8 SEGS (mrestrict H' m') base l.
Proof.
intros H H' m m' base l Hv Hg j Hj. destruct (Hg j Hj) as [Hm Hr]. split; [|exact Hr].
apply (val_mem_moved SEGS H H' m m' (base + Z.of_nat j) (base + Z.of_nat j) 1 _); [|exact Hm].
intros kk Hk. replace (base + Z.of_nat j + kk) with (base + (Z.of_nat j + kk)) by lia. apply Hv. lia.
Qed.

Lemma ch_chunk_byte : forall E (m : word -> option byte) base off (w : N) e i,
YP09.chunk_ok SEGS E m base (YP09.mkChunk off (CVal w e)) -> off <= i < off + Z.of_N w ->
mbyte SEGS m (base + i) = Some (byte_of_word (sv_denot E e) (i - off)).
Proof.
intros E m base off w e i Hc Hi. destruct (Hc (i - off) ltac:(cbn; lia)) as (b & Hb & Hm).
cbn [cbyte YP09.c_off YP09.c_val] in Hb, Hm. injection Hb as <-.
replace (base + off + (i - off)) with (base + i) in Hm by lia. exact Hm.
Qed.

Lemma ch_val_mem1 : forall (m : word -> option byte) a v, 0 <= v < 256 ->
mbyte SEGS m a = Some (Z_to_bv 8 v) -> val_mem SEGS m a 1 v.
Proof.
intros m a v Hv Hm k Hk. assert (k = 0%nat) by lia. subst k. rewrite Z.add_0_r, Hm.
assert (Hl : YO0f.le_byte v 1 0 = v).
{ unfold YO0f.le_byte. replace (2 ^ (8 * Z.of_nat 1)) with 256 by reflexivity. replace (8 * Z.of_nat 0) with 0 by reflexivity.
  rewrite Z.shiftr_0_r. rewrite (Z.mod_small v 256) by lia. rewrite (Z.mod_small v 256) by lia. reflexivity. }
rewrite Hl. reflexivity.
Qed.

Lemma ch_val_mem0_sub : forall (m : word -> option byte) a n k n',
val_mem SEGS m a n 0 -> (k + n' <= n)%nat -> val_mem SEGS m (a + Z.of_nat k) n' 0.
Proof.
intros m a n k n' H Hk j Hj.
assert (Z0 : forall w kk, YO0f.le_byte 0 w kk = 0)
by (intros; unfold YO0f.le_byte; rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia); rewrite Z.shiftr_0_l; reflexivity).
pose proof (H (k + j)%nat ltac:(lia)) as Hb. rewrite Z0 in Hb. rewrite Z0.
replace (a + Z.of_nat k + Z.of_nat j) with (a + Z.of_nat (k + j)) by lia. exact Hb.
Qed.

Lemma ch_val_mem_mod64 : forall (m : word -> option byte) a v, val_mem SEGS m a 8 (v mod 2 ^ 64) -> val_mem SEGS m a 8 v.
Proof.
intros m a v H j Hj. rewrite (H j Hj). unfold YO0f.le_byte. change (8 * Z.of_nat 8) with 64. rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* SPEED (a Theorem Labs lane, from the A twin lib/A/Prog/ClassifyCoreHead.v:352-396, verbatim) *)
Lemma ch_cb_ok : forall E (m : word -> option byte) base c i v,
YP09.chunk_ok SEGS E m base c -> ch_cb c i = Some v -> mbyte SEGS m (base + i) = Some (Z_to_bv 8 v).
Proof.
intros E m base [off cv] i v Hc Hv. unfold ch_cb in Hv. cbn [YP09.c_val YP09.c_off] in Hv.
destruct cv as [w sv0 | len | len | d s len]; try discriminate.
- destruct sv0; try discriminate.
  destruct ((off <=? i) && (i <? off + Z.of_N w)) eqn:Hb; [|discriminate].
  injection Hv as <-. apply andb_prop in Hb. destruct Hb as [Hb1 Hb2]. apply Z.leb_le in Hb1. apply Z.ltb_lt in Hb2.
  destruct (Hc (i - off) ltac:(cbn; lia)) as (b & Hb & Hm).
  cbn [cbyte YP09.c_off YP09.c_val sv_denot] in Hb, Hm. injection Hb as <-.
  replace (base + off + (i - off)) with (base + i) in Hm by lia. rewrite Hm, Z_to_bv_bv_unsigned. reflexivity.
- destruct ((off <=? i) && (i <? off + len)) eqn:Hb; [|discriminate].
  injection Hv as <-. apply andb_prop in Hb. destruct Hb as [Hb1 Hb2]. apply Z.leb_le in Hb1. apply Z.ltb_lt in Hb2.
  destruct (Hc (i - off) ltac:(cbn; lia)) as (b & Hb & Hm).
  cbn [cbyte YP09.c_off YP09.c_val] in Hb, Hm. injection Hb as <-.
  replace (base + off + (i - off)) with (base + i) in Hm by lia. exact Hm.
Qed.

Lemma ch_look_ok : forall E (m : word -> option byte) base cs i v,
Forall (YP09.chunk_ok SEGS E m base) cs -> ch_look cs i = Some v -> mbyte SEGS m (base + i) = Some (Z_to_bv 8 v).
Proof.
intros E m base cs i v Hcs. induction Hcs as [|c t Hc Ht IH]; cbn [ch_look]; [discriminate|].
destruct (ch_cb c i) as [v'|] eqn:Hv'; [|exact IH].
intros Hv. injection Hv as Hv. subst. eapply ch_cb_ok; eassumption.
Qed.

Lemma ch_pat_ok : forall E (m : word -> option byte) base cs l j,
Forall (YP09.chunk_ok SEGS E m base) cs -> ch_pat cs j l = true -> garr8 SEGS m (base + j) l.
Proof.
intros E m base cs l. induction l as [|v t IH]; intros j Hcs Hp jj Hjj; cbn [length] in Hjj; [lia|].
cbn [ch_pat] in Hp. destruct (ch_look cs j) as [v'|] eqn:Hl; [|discriminate].
apply andb_prop in Hp. destruct Hp as [Hp Hrest]. apply andb_prop in Hp. destruct Hp as [Hp Hv2].
apply andb_prop in Hp. destruct Hp as [Hv Hv1].
apply Z.eqb_eq in Hv. apply Z.leb_le in Hv1. apply Z.ltb_lt in Hv2. subst v'.
destruct jj as [|jj].
- cbn [nth]. split; [|lia]. apply ch_val_mem1; [lia|]. rewrite Z.add_0_r. exact (ch_look_ok E m base cs j v Hcs Hl).
- cbn [nth]. destruct (IH (j + 1) Hcs Hrest jj ltac:(lia)) as [Hm Hr]. split; [|exact Hr].
  replace (base + j + Z.of_nat (S jj)) with (base + (j + 1) + Z.of_nat jj) by lia. exact Hm.
Qed.

Lemma ch_pat_ok0 : forall E (m : word -> option byte) base cs l,
Forall (YP09.chunk_ok SEGS E m base) cs -> ch_pat cs 0 l = true -> garr8 SEGS m base l.
Proof.
intros E m base cs l Hcs Hp. rewrite <- (Z.add_0_r base). exact (ch_pat_ok E m base cs l 0 Hcs Hp).
Qed.

Ltac awr_ro_rec := first [ apply awr_ok_nil | apply awr_ok_cons_ro; [first [ro_win | cbn; lia]|]; awr_ro_rec ].

Theorem cls_head : cls_from_P B -> forall cx, cls_pre B cx ->
SRr SEGS (x_W cx) (cfg_at (fx := x_fq cx) SEGS (BASE + AF_both3_classify_core) (x_regs cx) (x_memc cx) (x_mdc cx)) (cls_Q B cx).
Proof.
intros FPc cx HPRE.
pose proof HPRE as HPRE0.
destruct cx as [fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch lk f len u o FB U OB L].
unfold cls_pre in HPRE.
cbn [x_fq x_STK x_sp0 x_FP x_ly x_S x_W0 x_mem0 x_md0 x_own x_lyc x_Sc x_W x_memc x_mdc x_k x_regs x_ch
x_lk x_f x_len x_u x_o x_FB x_U x_OB x_L] in HPRE |- *.
destruct HPRE as (HJ & HROD & Hra & Hra4 & Hgp & Htp & H10 & H11 & H12 & H13 & H14 & Hch & Hsp16 & Hbud & Hsple & Htop &
Hdep & Hlen & LFB & LU & LOB & Hfpre & HUr & HUs & HUg & Ho0 & Ho4 & HOr & HOg & HOw & HOst & HLk & HOU & HOF & HLd).
pose proof HJ as HJc.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = ltac:(let v := eval vm_compute in ESTACK in exact v)) by reflexivity. assert (HCS : CLS_STK = ltac:(let v := eval vm_compute in CLS_STK in exact v)) by reflexivity.
pose proof HJ as (HARc & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hsp016 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop1 & Htop2).
assert (Hsprng : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
pose proof (ch_entry fq lyc Sc W regs memc mdc HARc ltac:(intros a Ha; apply Hpres; lia) Hsprng Hsp16) as HS.
assert (HEI : img_env VAL A_LIM (ECH regs)) by apply Eimg_env.
assert (EL : forall n, (n < A_TEXT)%nat -> ew (ECH regs) n = ew (Ereg regs (ch_extra (as_uar_cell B))) n)
by (intros n Hn; unfold ECH; apply Eimg_low; exact Hn).
assert (E2 : ew (ECH regs) 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew (ECH regs) 2) = spZ regs) by (rewrite E2; reflexivity).
assert (E32 : ew (ECH regs) 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E59 : ew (ECH regs) 59 = Z_to_bv 64 (as_uar_cell B))
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 27)).
assert (HAE : env_agree 32 (Ereg regs (ch_extra (as_uar_cell B))) (ECH regs))
by (split; [intros n Hn; unfold ECH; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (ECH regs) n = getr regs r)
by (intros n r Hn; unfold ECH; apply ew_Eimg_Ereg_nat; exact Hn).
pose (RUNP := SRr_run_pi_AJ (fx := fq) B LAWS).
pose (RUNTOP := SRr_run_to_pi_AJ (fx := fq) B LAWS).
pose (RUNC := SRr_run_pi_AJ_call (fx := fq) B LAWS).
pose (BR := paj_branch (fx := fq) (PI := PI)).
unfold cfg_at. change (w64 (BASE + AF_both3_classify_core)) with (Z_to_bv 64 (BASE + AF_both3_classify_core)).
paj_run_to_sh RUNTOP HS HJ (AF_both3_classify_core + 0x48).
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
  let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0q fp b0 bc lyq ownq) end.
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spZ regs - sp0));
  [reflexivity | rewrite Usp; lia | cbn; lia | cbn; lia |].
  awr_ro_rec. }
rename ms into ms1. rename HF into HF1. rename HFr into HFr1. rename HG into HG1.
cbn [ms_mem mkst] in HF1, HFr1, HG1.
assert (KA1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 176 <= a < spZ regs) ->
  aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) memc a).
{ intros a Ha Hna. apply aview_eq_of. apply HFr1. rewrite unsigned_lit_small by (clear - Ha; lia).
  intros (rg & Hin & Hrg).
  lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
  clear - Hin Hrg Ha Hna Usp;
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg; rewrite ?Usp in Hrg; lia|]); destruct Hin. }
assert (PA1 : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem ms1) a)
by (intros a Ha; eapply apresent_grows; [exact HG1 | exact Ha]).
clear HF1 HFr1 HG1.
set (sp1 := cls_S1 (spZ regs)).
destruct (sp1_facts (spZ regs + -160) ltac:(lia) ltac:(rewrite <- Zplus_mod_idemp_l, Hsp16; reflexivity))
as (Hsp1r & Hsp1al & Hsp1al16).
assert (Esp1 : 32 * ((spZ regs + -160) / 32) = sp1) by reflexivity.
rewrite Esp1 in Hsp1r, Hsp1al, Hsp1al16.
assert (Hsp1 : spZ regs - 176 <= sp1 <= spZ regs - 160) by lia. clear Hsp1r.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
  let e2 := eval vm_compute in (sr_get (ss_regs ssx) (2%bv : bv 5)) in
  assert (R2 : getr (ms_regs msx) (2%bv : bv 5) = Z_to_bv 64 sp1) by
    (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx (2%bv : bv 5) HS) _);
     change (sv_denot Ex e2 = Z_to_bv 64 sp1); rewrite <- Esp1;
     exact (denot_and_m32 Ex 2 (spZ regs) (-160) ltac:(rewrite E2; symmetry; apply Z_to_bv_bv_unsigned) ltac:(lia) ltac:(lia) ltac:(lia)));
  let e9 := eval vm_compute in (sr_get (ss_regs ssx) (9%bv : bv 5)) in
  assert (R9 : getr (ms_regs msx) (9%bv : bv 5) = Z_to_bv 64 sp1) by
    (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx (9%bv : bv 5) HS) _);
     change (sv_denot Ex e9 = Z_to_bv 64 sp1); rewrite <- Esp1;
     exact (denot_and_m32_add0 Ex 2 (spZ regs) (-160) ltac:(rewrite E2; symmetry; apply Z_to_bv_bv_unsigned) ltac:(lia) ltac:(lia) ltac:(lia)))
end.
cbn [ms_regs restrict mkst] in R2, R9.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
  let rs := eval vm_compute in (trim_stack (ss_mem ssx) (-104)) in
  pose proof (st_ok_pi_submem Ex ssx msx rs HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
  clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
  pose proof (st_ok_pi_havoc_hi 60 Ev ssv msv [Z_to_bv 64 sp1] HS ltac:(vm_compute; reflexivity)) as HS3;
  hei_pose Ev 60%nat [Z_to_bv 64 sp1] end.
clear HS. rename HS3 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Enew _ _ =>
  remember Enew as E1v eqn:HEv in HS;
  repeat match goal with Hh : img_env _ _ Enew |- _ => rewrite <- HEv in Hh end end.
assert (AG : forall n, (n < 33)%nat -> ew E1v n = ew (ECH regs) n)
by (intros nn Hnn; rewrite HEv; rewrite !ew_havoc_old by lia; reflexivity).
assert (E60 : ew E1v 60 = Z_to_bv 64 sp1)
by (rewrite HEv; exact (ew_havoc_new _ 60 [Z_to_bv 64 sp1] 0 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (E32v : ew E1v 32 = Z_to_bv 64 SB) by (rewrite (AG 32%nat) by lia; exact E32).
assert (E59v : ew E1v 59 = Z_to_bv 64 (as_uar_cell B)) by (rewrite HEv; rewrite ew_havoc_old by lia; exact E59).
clear HEv E59.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (2%bv : bv 5) (SOff 60 0) HS ltac:(vm_compute; reflexivity)
  ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E60, Z.add_0_r, R2;
        rewrite unsigned_lit_small by lia; reflexivity)) as HS3;
  clear HS; rename HS3 into HS end.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (9%bv : bv 5) (SOff 60 0) HS ltac:(vm_compute; reflexivity)
  ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E60, Z.add_0_r, R9;
        rewrite unsigned_lit_small by lia; reflexivity)) as HS3;
  clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
  pose proof (st_ok_pi_add_fact Ex ssx msx 60%nat (mkAF (2 ^ 46 - 256) (2 ^ 47) 5) HS
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E60, unsigned_lit_small by lia;
        change (2 ^ 5) with 32; lia)) as HS3;
  clear HS; rename HS3 into HS end.
lazymatch goal with Himg : img_env _ _ E1v |- _ => pose proof Himg as HEIv end.
pose proof (pa_val_range (A_OBJ 0)) as Rv241. pose proof (pa_val_range (A_OBJ 1)) as Rv242.
pose proof (pa_val_range (A_OBJ 12)) as Rv253.
pose proof (pa_obj_img 0 ltac:(lia)) as Io241. pose proof (pa_obj_img 1 ltac:(lia)) as Io242.
pose proof (pa_obj_img 12 ltac:(lia)) as Io253. pose proof (palf_uar_img B TLF) as Iouc.
unfold IMG_LO, IMG_TOP in Io241, Io242, Io253, Iouc.
assert (Bv60 : base_val E1v (Some 60%nat) = sp1) by (cbn [base_val]; rewrite E60; apply unsigned_lit_small; lia).
assert (Bv2 : base_val E1v (Some 2%nat) = spZ regs) by (cbn [base_val]; rewrite (AG 2%nat) by lia; exact Usp).
assert (Bv241 : base_val E1v (Some 241%nat) = VAL (A_OBJ 0))
by (cbn [base_val]; rewrite (img_env_atomP E1v 241%nat HEIv ltac:(unfold A_TEXT, A_LIM; lia)); apply unsigned_lit_small; lia).
assert (Bv242 : base_val E1v (Some 242%nat) = VAL (A_OBJ 1))
by (cbn [base_val]; rewrite (img_env_atomP E1v 242%nat HEIv ltac:(unfold A_TEXT, A_LIM; lia)); apply unsigned_lit_small; lia).
assert (Bv253 : base_val E1v (Some 253%nat) = VAL (A_OBJ 12))
by (cbn [base_val]; rewrite (img_env_atomP E1v 253%nat HEIv ltac:(unfold A_TEXT, A_LIM; lia)); apply unsigned_lit_small; lia).
assert (Bv59 : base_val E1v (Some 59%nat) = as_uar_cell B)
by (cbn [base_val]; rewrite E59v; apply unsigned_lit_small; lia).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres1 & _).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 60%nat) 0 56 0 56 []) HS eq_refl
  ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem restrict mkst];
        rewrite Bv60; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
        intros oo Hoo; apply (apresent_writable SEGS); apply Hpres1; lia)
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
        cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi];
        rewrite Bv60, Bv2, Bv241, Bv242, Bv253, Bv59;
        repeat split; lia)) as HS3;
  clear HS; rename HS3 into HS end.
norm_ss HS.
assert (U2v : bv_unsigned (ew E1v 2) = spZ regs) by exact Bv2.
assert (U60v : bv_unsigned (ew E1v 60) = sp1) by exact Bv60.
paj_run_shc RUNP RUNC HS HJ.
{ awr_ch ltac:(idtac; awr_hd2 U2v U60v sp0 (spZ regs) sp1). }
rename ms into ms2. rename HF into HF2. rename HFr into HFr2. rename HG into HG2.
assert (KA2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 176 <= a < spZ regs) ->
  aview SEGS (w_H W) (ms_mem ms2) a = aview SEGS (w_H W) memc a).
{ intros a Ha Hna. rewrite <- (KA1 a Ha Hna). apply aview_eq_of. apply HFr2. rewrite unsigned_lit_small by (clear - Ha; lia).
  intros (rg & Hin & Hrg).
  lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
  clear - Hin Hrg Ha Hna U2v U60v Hsp1;
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg; rewrite ?U2v, ?U60v in Hrg; lia|]); destruct Hin. }
assert (PA2 : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem ms2) a)
by (intros a Ha; eapply apresent_grows; [exact HG2 | exact (PA1 a Ha)]).
clear HF2 HFr2 HG2.
lazymatch type of HS with st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
  let e2 := eval vm_compute in (sr_get (ss_regs ssx) (2%bv : bv 5)) in
  assert (R2c : getr (ms_regs msx) (2%bv : bv 5) = Z_to_bv 64 sp1) by
    (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx (2%bv : bv 5) HS) _);
     change (sv_denot Ex e2 = Z_to_bv 64 sp1); cbn [sv_denot]; rewrite E60, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity);
  let e3 := eval vm_compute in (sr_get (ss_regs ssx) (3%bv : bv 5)) in
  assert (R3c : getr (ms_regs msx) (3%bv : bv 5) = w64 (as_gp B)) by
    (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx (3%bv : bv 5) HS) _);
     change (sv_denot Ex e3 = w64 (as_gp B)); cbn [sv_denot]; rewrite (AG 3%nat) by lia;
     rewrite (EE 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Hgp);
  let e4 := eval vm_compute in (sr_get (ss_regs ssx) (4%bv : bv 5)) in
  assert (R4c : getr (ms_regs msx) (4%bv : bv 5) = w64 (as_tp B)) by
    (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx (4%bv : bv 5) HS) _);
     change (sv_denot Ex e4 = w64 (as_tp B)); cbn [sv_denot]; rewrite (AG 4%nat) by lia;
     rewrite (EE 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Htp);
  let e1 := eval vm_compute in (sr_get (ss_regs ssx) (1%bv : bv 5)) in
  assert (R1c : getr (ms_regs msx) (1%bv : bv 5) = Z_to_bv 64 (BASE + (AF_both3_classify_core + 0x80))) by
    (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx (1%bv : bv 5) HS) _);
     change (sv_denot Ex e1 = Z_to_bv 64 (BASE + (AF_both3_classify_core + 0x80))); apply codeptr_val; exact HEIv)
end.
cbn [ms_regs restrict mkst] in R1c, R2c, R3c, R4c.
pose proof (count_cid_le_length 2 (frames Sc)) as Hcnt.
aconstsF HJ Kgot1 Kcell1 Kguar1 Kuar1.
pmkst HS. rewrite (palf_sm2 B TLF).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
  eapply (aj_stack_malloc_atS (fx := fq) SEGS B LAWS Hsegs (pal_env B TL) ML SMP 2 (ASM2 fq) ltac:(lia) W (ms_regs msX) (ms_mem msX)
  STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k (sp1 - sp0) _ HJ) end.
  - unfold spZ at 1. rewrite R2c. rewrite unsigned_lit_small by lia. lia.
  - rewrite Zminus_mod, Hsp1al16, Hsp016. reflexivity.
  - lia.
  - lia.
  - exact R3c. - exact R4c. - exact R1c.
  - apply ret_ok_codeptr_v; [unfold AF_both3_classify_core; lia | reflexivity].
  - let vv := eval vm_compute in (fs_frames 2) in change (fs_frames 2) with vv.
    unfold CLS_DEPTH in Hdep. lia. }
cbv beta.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin &
Hnev2 & Hbb2 & Hz & Hflag & HK & HJM & (fS2 & ES2)).
aconstsF HJ2 Kgot2 Kcell2 Kguar2 Kuar2.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
reseat HS HJ2 HP2 [0; 1; 2; 3; 4; 5]%nat AG
ltac:(idtac; keptFL HK HJ2 AG Kgot1 Kgot2 Kcell1 Kcell2 Kguar1 Kguar2 Kuar1 Kuar2 ltac:(idtac; fail) ltac:(idtac; fail)).
pose proof (proj1 HJ2) as HAR2.
assert (Hfin2 : In (2, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR2 Hfin2) as (HFal & [HFhi _] & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 2 fpos HAR2 Hfin2) as (HF4096 & HFceil & HFapp).
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR2 Hfin2) as HFimg. unfold off_img, IMG_LO, IMG_TOP in HFimg.
change (fs_frame_bytes 2) with 256 in *.
set (F := frame_addr lyc 2 fpos) in *. set (FL := flag_addr lyc 2 fpos) in *.
destruct (al_flag _ _ LAWS _ _ _ _ _ 2 fpos HAR2 Hfin2) as (HFLpres & HFLown & [HFL4096 _] & HFLceil). fold FL in HFLpres, HFLown, HFL4096, HFLceil.
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8hi : F / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
  pose proof (st_ok_pi_havoc_hi 528 Ev ssv msv [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] HS ltac:(vm_compute; reflexivity)) as HS3;
  hei_pose Ev 528%nat [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] end.
clear HS. rename HS3 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Enew _ _ =>
  remember Enew as E3v eqn:HEv in HS;
  repeat match goal with Hh : img_env _ _ Enew |- _ => rewrite <- HEv in Hh end end.
lazymatch type of AG with forall n, _ -> ew ?Eo n = _ =>
  assert (AG3 : forall n, (n < 33)%nat -> ew E3v n = ew (ECH regs) n)
  by (intros nn Hnn; rewrite HEv; rewrite ew_havoc_old by lia; rewrite (AG nn Hnn); reflexivity);
  assert (E60' : ew E3v 60 = Z_to_bv 64 sp1) by (rewrite HEv; rewrite ew_havoc_old by lia; exact E60);
  assert (E59' : ew E3v 59 = Z_to_bv 64 (as_uar_cell B)) by (rewrite HEv; rewrite ew_havoc_old by lia; exact E59v);
  assert (E32' : ew E3v 32 = Z_to_bv 64 SB) by (rewrite (AG3 32%nat) by lia; exact E32) end.
assert (E528 : ew E3v 528 = Z_to_bv 64 FL)
by (rewrite HEv; exact (ew_havoc_new _ 528 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (E529 : ew E3v 529 = Z_to_bv 64 (SB + F / 8))
by (rewrite HEv; exact (ew_havoc_new _ 528 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia))).
clear HEv AG E60 E59v E32v. rename AG3 into AG. rename E60' into E60. rename E59' into E59v. rename E32' into E32v.
prreg HS (10%bv : bv 5) RF. cbn [ms_regs] in RF. rewrite Ha0 in RF. symmetry in RF. unfold w64 in RF. fold F in RF.
lazymatch goal with Himg : img_env _ _ E3v |- _ => pose proof Himg as HEI3 end.
assert (Bv60' : base_val E3v (Some 60%nat) = sp1) by (cbn [base_val]; rewrite E60; apply unsigned_lit_small; lia).
assert (Bv2' : base_val E3v (Some 2%nat) = spZ regs) by (cbn [base_val]; rewrite (AG 2%nat) by lia; exact Usp).
assert (Bv241' : base_val E3v (Some 241%nat) = VAL (A_OBJ 0))
by (cbn [base_val]; rewrite (img_env_atomP E3v 241%nat HEI3 ltac:(unfold A_TEXT, A_LIM; lia)); apply unsigned_lit_small; lia).
assert (Bv242' : base_val E3v (Some 242%nat) = VAL (A_OBJ 1))
by (cbn [base_val]; rewrite (img_env_atomP E3v 242%nat HEI3 ltac:(unfold A_TEXT, A_LIM; lia)); apply unsigned_lit_small; lia).
assert (Bv253' : base_val E3v (Some 253%nat) = VAL (A_OBJ 12))
by (cbn [base_val]; rewrite (img_env_atomP E3v 253%nat HEI3 ltac:(unfold A_TEXT, A_LIM; lia)); apply unsigned_lit_small; lia).
assert (Bv59' : base_val E3v (Some 59%nat) = as_uar_cell B) by (cbn [base_val]; rewrite E59v; apply unsigned_lit_small; lia).
assert (Bv516 : base_val E3v (Some 516%nat) = F) by (cbn [base_val]; rewrite RF; apply unsigned_lit_small; lia).
assert (Bv529 : base_val E3v (Some 529%nat) = SB + F / 8) by (cbn [base_val]; rewrite E529; apply unsigned_lit_small; unfold SB; lia).
clear Bv60 Bv2 Bv241 Bv242 Bv253 Bv59 U2v U60v.
assert (ZS : forall j, 0 <= j < 4 -> val_mem SEGS (mrestrict (w_H W) mem2) (SB + F / 8 + 8 * j) 8 0).
{ intros j Hj. apply val_mem_zero8. intros ii Hii. unfold zero_shadow, shadow_of_addr in Hz. rewrite <- SB_SHADOW_OFF in Hz.
  replace (SB + F / 8 + 8 * j + ii) with (SB + F / 8 + (8 * j + ii)) by lia. apply Hz. change (256 / 8) with 32. lia. }
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (st_ok_pi_add_fact Ev ssx msx 516%nat (HPTR 5) HS
  ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite RF, unsigned_lit_small by lia;
        change (2 ^ 5) with 32; lia)) as HS3; clear HS; rename HS3 into HS end.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (st_ok_pi_add_fact Ev ssx msx 528%nat (HPTR 0) HS
  ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E528, unsigned_lit_small by lia;
        rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3; clear HS; rename HS3 into HS end.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (st_ok_pi_add_fact Ev ssx msx 529%nat (mkAF (SB + 512) (SB + 2 ^ 44) 2) HS
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E529, unsigned_lit_small by (unfold SB; lia);
        change (2 ^ 2) with 4; split; [unfold SB; lia|]; split;
        [rewrite HF8; unfold SB; rewrite Z.add_mod, Z.mul_comm, Z_mod_mult by lia; reflexivity | unfold SB; lia]))
  as HS3; clear HS; rename HS3 into HS end.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (st_ok_pi_add_alias Ev ssx msx _ _ HS (shadow_decl_ok Ev 516 32 529 F SB RF ltac:(lia) E32v E529)) as HS3;
  clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  pose proof (st_ok_pi_add_region Ev _ _ (fframe_region 516 528 2 []) HS eq_refl
  ltac:(unfold region_ok, fframe_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem restrict mkst app];
        change (fs_frame_bytes 2) with 256; rewrite Bv516; split; [lia|]; split; [lia|]; split;
        [ intros oo Hoo; apply (apresent_writable SEGS); apply (proj1 (HFpres (F + oo) ltac:(lia)))
        | apply Forall_cons; [|apply Forall_nil]; apply (chunk_ok_val SEGS Ev _ F 248 8 _ FL);
          [cbn [sv_denot]; rewrite E528, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside
          | replace (F + 248) with (F + 256 - 8) by lia; exact (val_mem_of_rdword SEGS _ _ _ _ Hflag)] ])
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
        cbn [all_disjoint]; unfold extent_disjoint, fframe_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi];
        change (fs_frame_bytes 2) with 256;
        rewrite Bv516, Bv60', Bv2', Bv241', Bv242', Bv253', Bv59';
        clear - HFceil HF4096 HFimg Hceil Hslo Hshi Hbud HCS Hsp1 Io241 Io242 Io253 Iouc Rv241 Rv242 Rv253;
        repeat split; zone_lia)) as HS3;
  clear HS; rename HS3 into HS end.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  pose proof (st_ok_pi_add_region Ev _ _
  (fshadow_region 529 2 0 32 [YP09.mkChunk 0 (CVal 8 (SLit 0)); YP09.mkChunk 8 (CVal 8 (SLit 0));
                              YP09.mkChunk 16 (CVal 4 (SLit 0)); YP09.mkChunk 20 (CVal 4 (SLit 0));
                              YP09.mkChunk 24 (CVal 8 (SLit 0))]) HS eq_refl
  ltac:(unfold region_ok, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem restrict mkst app];
        change (fs_frame_bytes 2 / 8) with 32; rewrite Bv529; split; [unfold SB; lia|]; split; [unfold SB; lia|]; split;
        [ intros oo Hoo; apply (apresent_writable SEGS); unfold shadow_addr in HFSpres; rewrite <- SB_SHADOW_OFF in HFSpres;
          apply (proj1 (HFSpres oo ltac:(change (256 / 8) with 32; lia)))
        | apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ (SB + F / 8) 0 8 _ 0); [reflexivity | zside | zside | replace (SB + F / 8 + 0) with (SB + F / 8 + 8 * 0) by lia; apply ZS; lia]|];
          apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ (SB + F / 8) 8 8 _ 0); [reflexivity | zside | zside | replace (SB + F / 8 + 8) with (SB + F / 8 + 8 * 1) by lia; apply ZS; lia]|];
          apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ (SB + F / 8) 16 4 _ 0); [reflexivity | zside | zside |
            replace (SB + F / 8 + 16) with (SB + F / 8 + 8 * 2 + Z.of_nat 0) by lia; apply ch_val_mem0_sub with (n := 8%nat); [apply ZS; lia | lia]]|];
          apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ (SB + F / 8) 20 4 _ 0); [reflexivity | zside | zside |
            replace (SB + F / 8 + 20) with (SB + F / 8 + 8 * 2 + Z.of_nat 4) by lia; apply ch_val_mem0_sub with (n := 8%nat); [apply ZS; lia | lia]]|];
          apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ (SB + F / 8) 24 8 _ 0); [reflexivity | zside | zside | replace (SB + F / 8 + 24) with (SB + F / 8 + 8 * 3) by lia; apply ZS; lia]|];
          apply Forall_nil ])
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
        cbn [all_disjoint]; unfold extent_disjoint, fshadow_region, fframe_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi];
        change (fs_frame_bytes 2 / 8) with 32; change (fs_frame_bytes 2) with 256;
        rewrite Bv529, Bv516, Bv60', Bv2', Bv241', Bv242', Bv253', Bv59';
        clear - HFceil HF4096 HFimg Hceil Hslo Hshi Hbud HCS Hsp1 Io241 Io242 Io253 Iouc Rv241 Rv242 Rv253
          HFapp HF8lo HF8hi C1 C2 C3 C4 C5;
        unfold SB; repeat split; zone_lia)) as HS3;
  clear HS; rename HS3 into HS end.
norm_ss HS.
assert (U2' : bv_unsigned (ew E3v 2) = spZ regs) by exact Bv2'.
assert (U60' : bv_unsigned (ew E3v 60) = sp1) by exact Bv60'.
assert (EFA0 : forall c p0, frame_addr lyc c p0 = frame_addr lyc c p0) by reflexivity.
paj_run_shc RUNP RUNC HS HJ2.
{ ch_awrFL ltac:(idtac; awr_hd2 U2' U60' sp0 (spZ regs) sp1) AG fpos F EFA0. }
rename ms into ms3.
assert (U516 : bv_unsigned (ew E3v 516) = F) by exact Bv516.
assert (U529 : bv_unsigned (ew E3v 529) = SB + F / 8) by exact Bv529.
assert (HKH : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - CLS_STK <= a < spZ regs) -> ~ (F <= a < F + 256) ->
  ~ (SB + F / 8 <= a < SB + F / 8 + 32) -> aview SEGS (w_H W) (ms_mem ms3) a = aview SEGS (w_H W) mem2 a).
{ intros a Ha Hn1 Hn2 Hn3. apply aview_eq_of. apply HFr. rewrite unsigned_lit_small by (clear - Ha; lia).
  intros (rg & Hin & Hrg).
  lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
  clear - Hin Hrg Ha Hn1 Hn2 Hn3 HCS Hsp1 U2' U60' U516 U529;
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg; rewrite ?U2', ?U60', ?U516, ?U529 in Hrg; lia|]);
  destruct Hin. }
assert (PG3 : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) (ms_mem ms3) a)
by (intros a Ha; eapply apresent_grows; [exact HG | exact Ha]).
assert (Hce : alloc_ceiling <= spZ regs - CLS_STK) by lia.
assert (HK2 : tcls_kept B lyc Sc W memc W mem2 (spZ regs) lk o L).
{ apply (ch_kept_sm lyc Sc W memc mdc (ms_mem ms2) mem2 (spZ regs) (sp0 + (sp1 - sp0) - ESTACK) (sp0 + (sp1 - sp0)) lk o L HARc Hce ltac:(lia) ltac:(lia) KA2 PA2 HK).
  intros a Ha. apply Hpres2. lia. }
assert (HK3 : tcls_kept B lyc Sc W memc W (ms_mem ms3) (spZ regs) lk o L).
{ refine (KS (mkCCX fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch lk f len u o FB U OB L) fpos W lyc S2 mem2 md2
    (ms_mem ms3) (fun a => (spZ regs - CLS_STK <= a < spZ regs) \/ (F <= a < F + 256) \/ (SB + F / 8 <= a < SB + F / 8 + 32))
    HPRE0 HAR2 Hfrs2 Hnin ltac:(rewrite Eab; apply Permutation_refl) eq_refl eq_refl HK2 _ PG3 _).
  - intros a Ha HWr. apply HKH; [exact Ha | intro; apply HWr; tauto | intro; apply HWr; tauto | intro; apply HWr; tauto].
  - intros a [Hw | [Hw | Hw]]; unfold cSP, cF, cFL; cbn [x_regs x_lyc]; fold F FL;
    [left; exact Hw | right; right; left; exact Hw | right; right; right; left; rewrite <- SB_SHADOW_OFF; exact Hw]. }
assert (Hlo1 : spZ regs - CLS_STK <= sp0 + (sp1 - sp0) - ESTACK) by (clear - Hsp1 HCS Hes; lia).
assert (Hhi1 : sp0 + (sp1 - sp0) <= spZ regs) by (clear - Hsp1; lia).
assert (HXk : forall p n a, cls_read W memc (spZ regs) p n -> cls_write B STK sp0 FP ly S lyc Sc own p n -> p <= a < p + n ->
  aview SEGS (w_H W) (ms_mem ms3) a = aview SEGS (w_H W) memc a)
by (intros p n a; exact (ch_xk STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k S2 mem2 md2 fpos (ms_mem ms2) (ms_mem ms3)
  (spZ regs) _ _ p n a HJc HAR2 Hfrs2 Eab Hce Hlo1 Hhi1 KA2 HK HKH)).
assert (HOk : forall a, o <= a < o + 24 -> aview SEGS (w_H W) (ms_mem ms3) a = aview SEGS (w_H W) memc a)
by (intros a Ha; exact (HXk o 24 a HOr HOw Ha)).
assert (Hsig : SIGMA AS_reac_ctrl_parse = BASE + AF_both3_reac_ctrl_parse)
by (apply pa_xcalls; cbn [In both3_xcalls]; repeat (first [left; reflexivity | right])).
pmkst HS. rewrite Hsig.
unfold cls_from_P, cls_from in FPc.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdd) _ =>
  apply (FPc (mkCCX fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch lk f len u o FB U OB L) fpos W lyc S2 rg mm mdd HPRE0) end.
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
  let rs := eval vm_compute in (ss_mem ssx) in
  let r0 := eval vm_compute in (nth 0 rs got_regionP) in
  let r1 := eval vm_compute in (nth 1 rs got_regionP) in
  let r2 := eval vm_compute in (nth 2 rs got_regionP) in
  let r3 := eval vm_compute in (nth 3 rs got_regionP) in
  pose proof (st_ok_region_nth Ex ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as RG0;
  pose proof (st_ok_region_nth Ex ssx msx 1 r1 HS ltac:(vm_compute; reflexivity)) as RG1;
  pose proof (st_ok_region_nth Ex ssx msx 2 r2 HS ltac:(vm_compute; reflexivity)) as RG2;
  pose proof (st_ok_region_nth Ex ssx msx 3 r3 HS ltac:(vm_compute; reflexivity)) as RG3 end.
cbn [ms_mem restrict] in RG0, RG1, RG2, RG3.
prreg HS (Z_to_bv 5 1) G1. prreg HS (2%bv : bv 5) G2. prreg HS (3%bv : bv 5) G3. prreg HS (4%bv : bv 5) G4.
prreg HS (8%bv : bv 5) G8. prreg HS (9%bv : bv 5) G9. prreg HS (Z_to_bv 5 10) G10. prreg HS (Z_to_bv 5 11) G11.
prreg HS (Z_to_bv 5 12) G12. prreg HS (18%bv : bv 5) G18. prreg HS (19%bv : bv 5) G19. prreg HS (20%bv : bv 5) G20.
prreg HS (Z_to_bv 5 21) G21. prreg HS (Z_to_bv 5 22) G22. prreg HS (Z_to_bv 5 23) G23. prreg HS (Z_to_bv 5 24) G24.
prreg HS (Z_to_bv 5 25) G25. prreg HS (Z_to_bv 5 26) G26. prreg HS (27%bv : bv 5) G27.
rewrite E60 in G2, G9. rewrite RF in G18, G19. rewrite U516 in G12, G22. rewrite E529 in G27. rewrite E32v in G21.
rewrite (AG 3%nat), (EE 3%nat 3%bv eq_refl) in G3 by lia. rewrite (AG 4%nat), (EE 4%nat 4%bv eq_refl) in G4 by lia.
rewrite (AG 2%nat), E2 in G8 by lia.
rewrite (AG 11%nat), (EE 11%nat 11%bv eq_refl), H11 in G10, G24 by lia.
rewrite (AG 12%nat), (EE 12%nat 12%bv eq_refl), H12 in G11, G25 by lia.
rewrite (AG 10%nat), (EE 10%nat 10%bv eq_refl), H10 in G23 by lia.
rewrite (AG 13%nat), (EE 13%nat 13%bv eq_refl), H13 in G26 by lia.
unfold cls_at_P, cls_cut. cbv zeta.
unfold cS1, cF, cFL, cSP, PC_R1.
cbn [x_fq x_STK x_sp0 x_FP x_ly x_S x_W0 x_mem0 x_md0 x_own x_lyc x_Sc x_W x_memc x_mdc x_k x_regs x_ch
x_lk x_f x_len x_u x_o x_FB x_U x_OB x_L].
fold F FL. change (cls_S1 (spZ regs)) with sp1.
split; [exact HJ2|]. split; [exact Hfrs2|]. split; [exact Hnin|]. split; [rewrite Eab; apply Permutation_refl|].
split; [reflexivity|]. split; [reflexivity|]. split; [exact HK3|].
split; [rewrite G2; reflexivity|]. split; [exact G3|]. split; [exact G4|].
split; [rewrite G8; unfold w64, spZ; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split; [rewrite G9; reflexivity|]. split; [rewrite G18; reflexivity|]. split; [rewrite G19; reflexivity|].
split; [rewrite G20; apply bv_eq; reflexivity|]. split; [rewrite G27; reflexivity|].
split.
{ repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
  - rewrite G1. reflexivity. - exact G10. - exact G11. - rewrite G12; reflexivity. - rewrite G21; reflexivity.
  - rewrite G22; reflexivity. - exact G23. - exact G24. - exact G25. - exact G26. }
pose proof HOr as (HO0 & HO63 & _).
split.
{ unfold cls_spills. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
  (eapply (slot_of_region E3v _ (spZ regs) _ _ _ _ _ _ _ _ RG3 U2');
   [ cbn [In]; repeat (first [left; reflexivity | right])
   | cbn [sv_denot]; rewrite Z.add_0_r, !Z_to_bv_bv_unsigned; rewrite (AG _) by lia; apply EE; reflexivity
   | match goal with |- 0 <= bv_unsigned ?x < _ =>
       pose proof (bv_unsigned_in_range 64 x) as Hu; change (bv_modulus 64) with (2 ^ 64) in Hu; exact Hu end ]). }
split.
{ eapply (field_of_region E3v _ 60 sp1 _ _ _ _ _ 16 8 _ o RG2 U60');
  [ cbn [In]; repeat (first [left; reflexivity | right])
  | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (AG 14%nat), (EE 14%nat 14%bv eq_refl), H14 by lia; reflexivity
  | change (8 * Z.of_N 8) with 64; lia | cbn; lia ]. }
split.
{ apply ch_val_mem_mod64.
  assert (Hfm : f mod 2 ^ 64 = bv_unsigned (getr regs 11)) by (rewrite H11; unfold w64; rewrite Z_to_bv_unsigned; reflexivity).
  rewrite Hfm.
  eapply (field_of_region E3v _ 60 sp1 _ _ _ _ _ 24 8 _ _ RG2 U60');
  [ cbn [In]; repeat (first [left; reflexivity | right])
  | cbn [sv_denot]; rewrite Z.add_0_r, !Z_to_bv_bv_unsigned, (AG 11%nat), (EE 11%nat 11%bv eq_refl) by lia; reflexivity
  | change (8 * Z.of_N 8) with 64; pose proof (bv_unsigned_in_range 64 (getr regs 11)) as Hu;
    change (bv_modulus 64) with (2 ^ 64) in Hu; exact Hu
  | cbn; lia ]. }
split.
{ eapply (field_of_region E3v _ 60 sp1 _ _ _ _ _ 48 8 _ F RG2 U60');
  [ cbn [In]; repeat (first [left; reflexivity | right])
  | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, RF; reflexivity
  | change (8 * Z.of_N 8) with 64; lia | cbn; lia ]. }
split; [intros Hc; discriminate|].
split; [reflexivity|].
split.
{ destruct RG0 as (_ & _ & _ & Hcs0). cbn [YP09.r_base YP09.r_chunks base_val] in Hcs0. rewrite U529 in Hcs0.
  rewrite <- SB_SHADOW_OFF. apply (ch_pat_ok0 _ _ _ _ PAT_A Hcs0). vm_compute. reflexivity. }
split.
{ eapply (field_of_region E3v _ 516 F _ _ _ _ _ 248 8 _ FL RG1 U516);
  [ cbn [In]; repeat (first [left; reflexivity | right])
  | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E528; reflexivity
  | change (8 * Z.of_N 8) with 64; lia | cbn; lia ]. }
split; [exact I|].
split; [exact LOB|].
split.
{ apply (ch_garr8_kept (w_H W) (w_H W) memc (ms_mem ms3) o (cls_bytes OB)); [|exact HOg].
  intros i Hi. unfold cls_bytes in Hi. rewrite length_map, LOB in Hi. apply HOk. lia. }
destruct L as [Lb|]; [|exact I].
destruct HLk as (Hlk0 & Hlk4 & HLb & HLr & HLg & HLw & HLst).
split; [exact HLb|].
apply (ch_garr8_kept (w_H W) (w_H W) memc (ms_mem ms3) lk (cls_bytes Lb)); [|exact HLg].
intros i Hi. unfold cls_bytes in Hi. rewrite length_map, HLb in Hi. apply (HXk lk 12); [exact HLr | exact HLw | lia].
Qed.

End h.
End f.
End d.
