(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YP0n.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/Reusable/YP0n.v, with its module paths and module names changed; 967 of its 1043 lines of code are new or changed and 1914 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/Cno102B_Base.v, with its module paths and module names changed; 702 of its 797 lines of code are new or changed and 948 lines of the source are left out. *)
(* fuzz_preset, image A' (#102 pins: asan sha256 1be0f53d96cb9d6c): the SHARED STEP KIT of the re-walk of
   check_no_overread (cno) against the text tcheck_no_overread_specX, by a Theorem Labs lane (a sub-lane of another lane, under a Theorem Labs session;
   plan, the internal file PLAN-cno-caw-102.md 5.1, segments CA6-CA8 use it, CA9 (walked by a Theorem Labs lane) cites it at
   its fuzz_alloc_ran_out call 0x81ec4 and its two `same` calls).
   rule 24: no function proved. rule 24: proves no function (kind: segment lemma).
   Qed on the f97c kit before this re-fit (by a Theorem Labs lane); re-fit to the cut below.
   INPUTS AT THE CUT 7cdbb61b5fa0 (by path, the cut's blobs): the contract lib/A/Prog/Cno102A_Base.v ba76a7bc31c9;
   the texts lib/A/PRH_FnAlloc.v 4d8aeba047e5 (tfuzz_alloc_ran_out_specX :175-183: most / own in the ledger, S' = S),
   lib/A/PRH_Base.v ef7c8ca98529 (fpre :988-1010), lib/A/PRH_FnCheck.v c40cf3fdcd2a, lib/A/PRH_Reader.v 4266e709561a
   (pj_nodeR_frame, pj_zeroR_frame), lib/A/PRH_PjOrder.v e5917626b82b (pj_foR_frame); listing lib/A/Listing_prog.v
   7ed1529926bd (PCall AS_fuzz_alloc_ran_out 1 at offsets 756 / 964 / 1012 / 1472, PCall AS_parse_noting 1 at 780 /
   992 / 1040); engine lib/Reusable/YCbqGcallW.v fb6aa11676a2 (aj_call_xW), YCbqG.v 219748197d6b (ajournal_xw, the
   ajx_* projections, ajournal_x_materialize), YCbqGwild.v 0c63874858e4 (ajournal_xw_rebase, ajournal_xw_unbase0),
   YA0n.v 71b29196fd22 (SRr_step); kit lib/A/Prog/PRW_StepKit.v 0df3991c13f4 (pa_slot_lt_ceil_b).
   WHAT IS HERE (all generic in {PA : PAImg A_prog_listing}, B, ARx, SK; P abstract):
   - hand steps over cn_cfg configurations (no engine): cn_hs_addi / cn_hs_ld / cn_hs_lbu / cn_hs_beqz /
     cn_hs_bnez / cn_hs_j / cn_hs_call (the PCall jal: pc = SIGMA s, ra = the next offset); each step reads memory
     only, so the memory (and P of it) is unchanged and the model moves to a materialised copy; cn_srrG_lift runs
     them inside a segment over a world relation R;
   - cn_base_mat: cn_base at the materialised model and a register file that keeps gp / tp;
   - cn_chain: the frame chain at any cno call state (s0 = the entry sp: the record (sp0, entry ra, entry s0) from
     cn_saved :184 / :176, then the entry's chain, kept above sp0 by the journal; [] when sp0 is within 16 bytes of
     the stack top);
   - cn_call_keep: across a call whose post is fpostm with FP = [] and S' = S, Hp' = Hp, ablocks kept, the ledger
     restated: cn_base / cn_slots / cn_mid and the structs' cn_fo at the post state (frame and stack bytes by the
     callee journal's frame and stack clauses, live block bytes by its block clause, block shadow by AR_laws_x field
     alx_shadow at the post state, tree blocks through PRH_Reader's and PRH_PjOrder's frame lemmas, arodata_okP by the
     image clause with cn_img's cni_pst_rw);
   - cn_ro_call: the call to fuzz_alloc_ran_out at the callee entry (aj_call_xW, the text HRO for any float state,
     fpre's raZ bound from pa_slot_lt_ceil_b, P across by srr_inv_call at the text's memnorm keep).
   RE-FIT TO THE KIT CUT 7cdbb61b5fa0 (by a Theorem Labs lane; contract lib/A/Prog/Cno102A_Base.v blob ba76a7bc31c9 at
   a working branch 4b59cadb07a1): cn_pre has no run-word list DW and is read by its projections
   (cn_pre_fpre); cn_base takes the wild budget wk LAST and cn_J is the journal at that budget (exists WS,
   ajournal_xw .. WS /\ wbudget [] wk WS), read by the ajx_* projections. fuzz_alloc_ran_out (PRH_FnAlloc.v
   4d8aeba047e5, tfuzz_alloc_ran_out_specX unchanged from f97c: a plain fpostm, no wild site) adds no wild trace, so
   every lemma here keeps wk from premise to conclusion: the call runs aj_call_xW on the journal rebased to the empty
   budget (YCbqGwild.ajournal_xw_rebase, entry set_depot (st_depot S) (ci_S D)) and comes back with
   YCbqGwild.ajournal_xw_unbase0 at the same WS (its inclusion is ajx_wild of the call state's journal; the callee
   keeps S). cn_call_keep takes that rebased journal as HJ2; cn_call_keep / cn_ro_call also carry the three structs'
   free-order ties cn_fo across the call (PRH_PjOrder.pj_foR_frame over the tree footprints the call keeps).
   THE FREE / REALLOC MOVE (the cuts after the first parse_noting carry cn_J at wle' SEGS RZ_cf, the base's cn_baseR):
   the lemmas that read cn_base are used at cuts on BOTH sides of a free, so each has its R form beside it, generic in
   the world relation R, and the old name is that form at wle: cn_base_matR, cn_chainR, cn_call_keepR (journals at
   ajournal_xR .. R, read by the ajxR_* projections; YCbqGwild.ajournal_xw_rebaseR / _unbase0R,
   ajournal_x_materializeR) and cn_ro_callR (R reflexive, transitive and containing wle: aj_call_xWR at R; the text
   tfuzz_alloc_ran_out_specX is not a crossing text and stays plain, so its SRr is lifted by YA0nH.SRr_SRrG and its
   post by YCbqG.apost_base_x_R_lift, then fpostW_x_of_apostR). The hand steps read memory only and keep the world,
   so they stay at SRr, unchanged: a segment over R runs them inside `SRr W c (fun W' c' => SRrG SEGS R W' c' Q)`
   (cn_srrG_lift) and leaves the stretch at its next call or exit by SRr_ret. fuzz_alloc_ran_out keeps S, so the
   cut's allocator hull conjunct (a budget over st_secs at the cut's S, outside cn_base) rides any call here unchanged.
   Numerals: 748.. 1476 (DERIVED: byte offsets inside cno, the cuts of Cno102A_Base.v and the listing's slots);
   192 / 208 / 223 / 32 / 16 / 8 / 56 / 64 / 512 / 24 / 80 / 88 / 184 (LENGTH: frame, alignment, slot and struct
   sizes, the class-3 frame and its shadow); register numbers (WORD); 2 ^ 29 / 2 ^ 40 / 2 ^ 64 (LENGTH: offset, code
   span and word bounds). No ADDRESS. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqGcallW YN01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Img PRH_Reader PRH_FnAlloc
  PRH_FnReader PRH_FnPj PRH_FnEx PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_StepKit Cno102A_Base.
(* the PLAIN build's sink instance is loaded transitively; it must never fill an ASan sink argument *)
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.
(* PRW_StepKit loads YF0v.v, which turns zify's division rewriting off globally; this file's arithmetic on the
   frame, struct and shadow offsets needs it on (S4_PsU.v's reset) *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* ---- pure helpers ---- *)
Lemma ro_land32 : forall x, Z.land x (-32) = x - x mod 32.
Proof.
intros x. replace (-32) with (Z.lnot (Z.ones 5)) by reflexivity.
assert (Hl : Z.land x (Z.lnot (Z.ones 5)) = Z.ldiff x (Z.ones 5)).
{ apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.lnot_spec, Z.ldiff_spec by lia. reflexivity. }
rewrite Hl, Z.ldiff_ones_r, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2 ^ 5) with 32.
rewrite Z.mod_eq by lia. lia.
Qed.

(* two distinct-base members of a pairwise-disjoint mapped list are disjoint *)
Lemma ro_pairwise_map : forall (f : Z * Z -> Z * Z) (l : list (Z * Z)) x y,
  pairwise zdisjoint (map f l) -> In x l -> In y l -> fst x <> fst y -> zdisjoint (f x) (f y).
Proof.
intros f l. induction l as [|z t IH]; intros x y H Hx Hy Hne; [destruct Hx|].
cbn [map pairwise] in H. destruct H as [Hz Ht].
destruct Hx as [<- | Hx]; destruct Hy as [<- | Hy].
- exfalso. apply Hne. reflexivity.
- exact (proj1 (Forall_forall _ _) Hz (f y) (in_map f t y Hy)).
- pose proof (proj1 (Forall_forall _ _) Hz (f x) (in_map f t x Hx)) as Hd. unfold zdisjoint in *. lia.
- exact (IH x y Ht Hx Hy Hne).
Qed.

Lemma ro_hull_mono : forall (rd : reader) x n n', 0 < n' <= n -> shadow_hull_vis rd x n -> shadow_hull_vis rd x n'.
Proof.
intros rd x n n' Hn H s Hs. apply H.
assert (E1 : shadow_addr (x + n' - 1) <= shadow_addr (x + n - 1))
  by (unfold shadow_addr; apply Z.add_le_mono_l; apply Z.div_le_mono; lia).
assert (E2 : shadow_addr (x + n' - 1) / 8 <= shadow_addr (x + n - 1) / 8) by (apply Z.div_le_mono; lia).
lia.
Qed.

Lemma ro_div8 : forall a, 8 * (a / 8) <= a < 8 * (a / 8) + 8.
Proof.
intros a. pose proof (Z.div_mod a 8 ltac:(lia)) as H1. pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as H2.
revert H1 H2. generalize (a / 8) (a mod 8). intros q r H1 H2. lia.
Qed.

Lemma ro_rdword_kept : forall (rd rd' : reader) lo hi x,
  (forall a, lo <= a < hi -> rd' a = rd a) -> lo <= x -> x + 8 <= hi -> rdword rd' x = rdword rd x.
Proof. intros rd rd' lo hi x Hk H1 H2. apply rdword_ext. intros kk Hkk. apply Hk. lia. Qed.

Lemma ro_getr_same : forall regs (r : bv 5) v, bv_eqb r 0%bv = false -> getr (regupd regs r v) r = v.
Proof. intros regs r v H. apply getr_same. intros E. subst r. discriminate H. Qed.
Lemma ro_getr_other : forall regs (r r' : bv 5) v, bv_eqb r' r = false -> getr (regupd regs r v) r' = getr regs r'.
Proof. intros regs r r' v H. apply getr_other. intros E. subst r'. rewrite bv_eqb_refl in H. discriminate H. Qed.
Ltac ro_getr := repeat first [rewrite ro_getr_same by reflexivity | rewrite ro_getr_other by reflexivity].

Lemma ro_getr0 : forall regs, getr regs 0%bv = Z_to_bv 64 0.
Proof. intros regs. reflexivity. Qed.
Lemma ro_li : forall regs (imm : bv 12), v_addi (getr regs 0%bv) (bv_signed imm) = w64 (bv_signed imm).
Proof. intros regs imm. rewrite ro_getr0. unfold v_addi, w64. rewrite unsigned_lit_small by lia. f_equal. Qed.
Lemma ro_mv : forall (x : word), v_addi x (bv_signed (0%bv : bv 12)) = x.
Proof. intros x. unfold v_addi. change (bv_signed (0%bv : bv 12)) with 0. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

Lemma ro_c_eq0 : forall v, 0 <= v < 2 ^ 64 -> c_eq (w64 v) (Z_to_bv 64 0) = (v =? 0).
Proof. intros v Hv. unfold c_eq, bv_eqb, w64. rewrite !unsigned_lit_small by lia. reflexivity. Qed.

Lemma ro_bv_eqb_eq : forall {n} (a b : bv n), bv_eqb a b = true -> a = b.
Proof. intros n a b H. unfold bv_eqb in H. apply Z.eqb_eq in H. apply bv_eq. exact H. Qed.

Lemma ro_rdn1 : forall segs (m : word -> option byte) a b, mbyte segs m a = Some b -> rdn segs m (Z_to_bv 64 a) 1 = Some [b].
Proof. intros segs m a b H. cbn [rdn]. unfold mbyte in H. rewrite H. reflexivity. Qed.

(* the register snapshot *)
Lemma cn_regsat_get : forall regs l (r : bv 5) v, cn_regsat regs l -> In (r, v) l -> getr regs r = w64 v.
Proof. intros regs l r v H Hin. exact (proj1 (Forall_forall _ _) H (r, v) Hin). Qed.
Lemma cn_regsat_kept : forall regs regs' l, cn_regsat regs l ->
  Forall (fun p : bv 5 * Z => getr regs' (fst p) = getr regs (fst p)) l -> cn_regsat regs' l.
Proof.
intros regs regs' l H K. unfold cn_regsat in *. rewrite Forall_forall in *. intros p Hp.
rewrite (K p Hp). exact (H p Hp).
Qed.
Lemma cn_regsat_pres : forall regs regs' l, cn_regsat regs l -> aregs_preserved regs regs' ->
  Forall (fun p : bv 5 * Z => acallee_saved (bv_unsigned (fst p))) l -> cn_regsat regs' l.
Proof.
intros regs regs' l H HP HF. apply (cn_regsat_kept regs regs' l H). rewrite Forall_forall in *.
intros [r v] Hin. cbn [fst]. specialize (HF (r, v) Hin). cbn [fst] in HF.
pose proof (HP (bv_unsigned r) HF) as E. rewrite Z_to_bv_bv_unsigned in E. exact E.
Qed.
Ltac ro_in := cbn [app In]; repeat (first [left; reflexivity | right]).

Section ro. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Existing Instance prh_img_A.
Context {PA : PAImg A_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation VAL := (@pa_val _ A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Lemma cn_off_val : CN_OFF = 804.
Proof. reflexivity. Qed.

(* ---- the hand steps: one instruction, memory read only ---- *)
Lemma cn_step : forall (W : world SEGS) fxk regs mem md regs' off off' Q,
  0 <= off < 2 ^ 29 -> 0 <= off' < 2 ^ 29 ->
  RiscvSemantics.step SEGS (@YK11.mkst fxk regs (Z_to_bv 64 (BASE + (CN_OFF + off))) (mrestrict (w_H W) mem)
      (YK11.seg_rom SEGS)) =
    MachineOk (@YK11.mkst fxk regs' (Z_to_bv 64 (BASE + (CN_OFF + off'))) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)) ->
  (forall X, SRr SEGS W (@cn_cfg SEGS fxk (cn_pc off') regs' mem (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (@cn_cfg SEGS fxk (cn_pc off) regs mem md) Q.
Proof.
intros W fxk regs mem md regs' off off' Q Ho Ho' Hst HK.
unfold cn_cfg, cn_pc, w64. replace (BASE + CN_OFF + off) with (BASE + (CN_OFF + off)) by lia.
eapply (SRr_step SEGS pa_wx W); [reflexivity | rewrite (@restrict_mkst_fx fxk); exact Hst |].
intros md' Hs. rewrite (same_but_materialized_wvb md md' Hs).
cbn [ms_mem YK11.mkst]. rewrite (@unrestrict_mkst_mrestrict fxk).
specialize (HK (m_vm_materialized md')). unfold cn_cfg, cn_pc, w64 in HK.
replace (BASE + CN_OFF + off') with (BASE + (CN_OFF + off')) in HK by lia. exact HK.
Qed.

Lemma cn_pc4 : forall off, 0 <= off < 2 ^ 29 ->
  v_addi (Z_to_bv 64 (BASE + (CN_OFF + off))) 4 = Z_to_bv 64 (BASE + (CN_OFF + (off + 4))).
Proof.
intros off Ho. pose proof (@pa_B_ok _ _ PA) as (HB0 & HB1 & _). pose proof cn_off_val as HO.
unfold v_addi. rewrite unsigned_lit_small by lia. f_equal. lia.
Qed.
Lemma cn_pcj : forall off (j : Z), 0 <= off < 2 ^ 29 -> 0 <= off + j < 2 ^ 29 ->
  v_addi (Z_to_bv 64 (BASE + (CN_OFF + off))) j = Z_to_bv 64 (BASE + (CN_OFF + (off + j))).
Proof.
intros off j Ho Hj. pose proof (@pa_B_ok _ _ PA) as (HB0 & HB1 & _). pose proof cn_off_val as HO.
unfold v_addi. rewrite unsigned_lit_small by lia. f_equal. lia.
Qed.

Lemma cn_hs_addi0 : forall (W : world SEGS) fxk regs mem md Q off off' w rd rs imm,
  plookup A_prog_tpi_cno (CN_OFF + off) = Some (PW w) ->
  decode_any (Z_to_bv 32 w) = Some (OpImm ALU_ADD rd rs imm, 4%Z) -> bv_eqb rd 0%bv = false ->
  0 <= off < 2 ^ 28 -> off' = off + 4 ->
  (forall X, SRr SEGS W (@cn_cfg SEGS fxk (cn_pc off') (regupd regs rd (v_addi (getr regs rs) (bv_signed imm))) mem
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (@cn_cfg SEGS fxk (cn_pc off) regs mem md) Q.
Proof.
intros W fxk regs mem md Q off off' w rd rs imm Hpl Hdec Hrd Ho -> HK.
apply (cn_step W fxk regs mem md (regupd regs rd (v_addi (getr regs rs) (bv_signed imm))) off (off + 4) Q ltac:(lia) ltac:(lia)); [|exact HK].
rewrite (@step_addi fxk SEGS regs _ (mrestrict (w_H W) mem) (YK11.seg_rom SEGS) _ rd rs imm
  (@pa_fetch_pw _ _ PL_cno_A PA _ _ Hpl) (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec).
rewrite Hrd, (cn_pc4 off ltac:(lia)). reflexivity.
Qed.

Lemma cn_hs_ld0 : forall (W : world SEGS) fxk regs mem md Q off off' w rd rs imm a v,
  plookup A_prog_tpi_cno (CN_OFF + off) = Some (PW w) ->
  decode_any (Z_to_bv 32 w) = Some (Load SZ8 true rd rs imm, 4%Z) -> bv_eqb rd 0%bv = false ->
  0 <= off < 2 ^ 28 -> off' = off + 4 ->
  bv_unsigned (getr regs rs) + bv_signed imm = a -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  rdword (aview SEGS (w_H W) mem) a = Some v ->
  (forall X, SRr SEGS W (@cn_cfg SEGS fxk (cn_pc off') (regupd regs rd (w64 v)) mem (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (@cn_cfg SEGS fxk (cn_pc off) regs mem md) Q.
Proof.
intros W fxk regs mem md Q off off' w rd rs imm a v Hpl Hdec Hrd Ho -> Ha Ha0 Ha8 Hv HK.
apply (cn_step W fxk regs mem md (regupd regs rd (w64 v)) off (off + 4) Q ltac:(lia) ltac:(lia)); [|exact HK].
pose proof (val_mem_of_rdword SEGS (w_H W) mem a v Hv) as Hvm.
destruct (word_mem_ld SEGS (mrestrict (w_H W) mem) a v Hvm Ha0 Ha8) as (bs & Hbs & Hbv).
assert (Eaddr : v_addi (getr regs rs) (bv_signed imm) = Z_to_bv 64 a) by (unfold v_addi; rewrite Ha; reflexivity).
rewrite (@step_ld fxk SEGS regs _ (mrestrict (w_H W) mem) (YK11.seg_rom SEGS) _ rd rs imm bs (Z_to_bv 64 v)
  (@pa_fetch_pw _ _ PL_cno_A PA _ _ Hpl) (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec
  ltac:(rewrite Eaddr; exact Hbs) Hbv).
rewrite Hrd, (cn_pc4 off ltac:(lia)). reflexivity.
Qed.

Lemma cn_hs_lbu0 : forall (W : world SEGS) fxk regs mem md Q off off' w rd rs imm a b,
  plookup A_prog_tpi_cno (CN_OFF + off) = Some (PW w) ->
  decode_any (Z_to_bv 32 w) = Some (Load SZ1 false rd rs imm, 4%Z) -> bv_eqb rd 0%bv = false ->
  0 <= off < 2 ^ 28 -> off' = off + 4 ->
  bv_unsigned (getr regs rs) + bv_signed imm = a ->
  mbyte SEGS (mrestrict (w_H W) mem) a = Some b ->
  (forall X, SRr SEGS W (@cn_cfg SEGS fxk (cn_pc off') (regupd regs rd (Z_to_bv 64 (bv_unsigned b))) mem
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (@cn_cfg SEGS fxk (cn_pc off) regs mem md) Q.
Proof.
intros W fxk regs mem md Q off off' w rd rs imm a b Hpl Hdec Hrd Ho -> Ha Hb HK.
apply (cn_step W fxk regs mem md (regupd regs rd (Z_to_bv 64 (bv_unsigned b))) off (off + 4) Q ltac:(lia) ltac:(lia)); [|exact HK].
assert (Eaddr : v_addi (getr regs rs) (bv_signed imm) = Z_to_bv 64 a) by (unfold v_addi; rewrite Ha; reflexivity).
rewrite (@step_lbu fxk SEGS regs _ (mrestrict (w_H W) mem) (YK11.seg_rom SEGS) _ rd rs imm b
  (@pa_fetch_pw _ _ PL_cno_A PA _ _ Hpl) (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec
  ltac:(rewrite Eaddr; exact (ro_rdn1 SEGS _ a b Hb))).
rewrite Hrd, (cn_pc4 off ltac:(lia)). reflexivity.
Qed.

(* `beqz rs, imm`: taken when the register is zero *)
Lemma cn_hs_beqz0 : forall (W : world SEGS) fxk regs mem md Q off w rs imm (z : bool),
  plookup A_prog_tpi_cno (CN_OFF + off) = Some (PW w) ->
  decode_any (Z_to_bv 32 w) = Some (Branch BC_EQ rs 0%bv imm, 4%Z) ->
  0 <= off < 2 ^ 28 -> 0 <= off + bv_signed imm < 2 ^ 28 ->
  c_eq (getr regs rs) (getr regs 0%bv) = z ->
  (forall X, SRr SEGS W (@cn_cfg SEGS fxk (cn_pc (if z then off + bv_signed imm else off + 4)) regs mem
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (@cn_cfg SEGS fxk (cn_pc off) regs mem md) Q.
Proof.
intros W fxk regs mem md Q off w rs imm z Hpl Hdec Ho Hj Hc HK.
pose proof (@pa_fetch_pw _ _ PL_cno_A PA _ _ Hpl) as Hf.
pose proof (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) as He.
destruct z.
- apply (cn_step W fxk regs mem md regs off (off + bv_signed imm) Q ltac:(lia) ltac:(lia)); [|exact HK].
  rewrite (@step_beq_tk fxk SEGS regs _ (mrestrict (w_H W) mem) (YK11.seg_rom SEGS) _ rs 0%bv imm Hf He Hdec Hc).
  unfold btgt. rewrite (cn_pcj off (bv_signed imm) ltac:(lia) ltac:(lia)). reflexivity.
- apply (cn_step W fxk regs mem md regs off (off + 4) Q ltac:(lia) ltac:(lia)); [|exact HK].
  rewrite (@step_beq_ft fxk SEGS regs _ (mrestrict (w_H W) mem) (YK11.seg_rom SEGS) _ rs 0%bv imm Hf He Hdec Hc).
  rewrite (cn_pc4 off ltac:(lia)). reflexivity.
Qed.

(* `bnez rs, imm`: taken when the register is non-zero *)
Lemma cn_hs_bnez0 : forall (W : world SEGS) fxk regs mem md Q off w rs imm (z : bool),
  plookup A_prog_tpi_cno (CN_OFF + off) = Some (PW w) ->
  decode_any (Z_to_bv 32 w) = Some (Branch BC_NE rs 0%bv imm, 4%Z) ->
  0 <= off < 2 ^ 28 -> 0 <= off + bv_signed imm < 2 ^ 28 ->
  c_eq (getr regs rs) (getr regs 0%bv) = z ->
  (forall X, SRr SEGS W (@cn_cfg SEGS fxk (cn_pc (if z then off + 4 else off + bv_signed imm)) regs mem
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (@cn_cfg SEGS fxk (cn_pc off) regs mem md) Q.
Proof.
intros W fxk regs mem md Q off w rs imm z Hpl Hdec Ho Hj Hc HK.
pose proof (@pa_fetch_pw _ _ PL_cno_A PA _ _ Hpl) as Hf.
pose proof (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) as He.
destruct z.
- apply (cn_step W fxk regs mem md regs off (off + 4) Q ltac:(lia) ltac:(lia)); [|exact HK].
  rewrite (@step_bne_ft fxk SEGS regs _ (mrestrict (w_H W) mem) (YK11.seg_rom SEGS) _ rs 0%bv imm Hf He Hdec Hc).
  rewrite (cn_pc4 off ltac:(lia)). reflexivity.
- apply (cn_step W fxk regs mem md regs off (off + bv_signed imm) Q ltac:(lia) ltac:(lia)); [|exact HK].
  rewrite (@step_bne_tk fxk SEGS regs _ (mrestrict (w_H W) mem) (YK11.seg_rom SEGS) _ rs 0%bv imm Hf He Hdec Hc).
  unfold btgt. rewrite (cn_pcj off (bv_signed imm) ltac:(lia) ltac:(lia)). reflexivity.
Qed.

(* `j imm` *)
Lemma cn_hs_j0 : forall (W : world SEGS) fxk regs mem md Q off off' w imm,
  plookup A_prog_tpi_cno (CN_OFF + off) = Some (PW w) ->
  decode_any (Z_to_bv 32 w) = Some (Jal 0%bv imm, 4%Z) ->
  0 <= off < 2 ^ 28 -> off' = off + bv_signed imm -> 0 <= off' < 2 ^ 28 ->
  (forall X, SRr SEGS W (@cn_cfg SEGS fxk (cn_pc off') regs mem (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (@cn_cfg SEGS fxk (cn_pc off) regs mem md) Q.
Proof.
intros W fxk regs mem md Q off off' w imm Hpl Hdec Ho -> Hj HK.
apply (cn_step W fxk regs mem md regs off (off + bv_signed imm) Q ltac:(lia) ltac:(lia)); [|exact HK].
rewrite (@step_jal_link fxk SEGS regs _ (mrestrict (w_H W) mem) (YK11.seg_rom SEGS) _ 0%bv imm
  (@pa_fetch_pw _ _ PL_cno_A PA _ _ Hpl) (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec).
unfold btgt. rewrite (cn_pcj off (bv_signed imm) ltac:(lia) ltac:(lia)). reflexivity.
Qed.

(* the PCall jal of a listing slot: pc = SIGMA s, ra = the next offset *)
Lemma cn_hs_call : forall (W : world SEGS) fxk regs mem md Q off off' s,
  plookup A_prog_tpi_cno (CN_OFF + off) = Some (PCall s 1%bv) -> 0 <= off < 2 ^ 28 -> off' = off + 4 ->
  (forall X, SRr SEGS W (@cn_cfg SEGS fxk (SIGMA s) (regupd regs 1%bv (w64 (cn_pc off'))) mem
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (@cn_cfg SEGS fxk (cn_pc off) regs mem md) Q.
Proof.
intros W fxk regs mem md Q off off' s Hpl Ho -> HK.
pose proof (@pa_B_ok _ _ PA) as (HB0 & HB1 & _). pose proof cn_off_val as HO.
pose proof (cert_slot asym (clookup pa_tbl) VAL SIGMA A_prog_listing pa_cert (CN_OFF + off) (PCall s 1%bv) Hpl)
  as (Hck & _ & _).
unfold pi_slot_check in Hck. cbv zeta in Hck.
destruct (clookup pa_tbl (VAL A_TEXT + (CN_OFF + off))) as [wz|] eqn:Hf; [|discriminate Hck].
destruct (decode_any (Z_to_bv 32 wz)) as [[i isz]|] eqn:Hdec; [|discriminate Hck].
apply andb_prop in Hck as (Hsz & Hck). apply Z.eqb_eq in Hsz. subst isz.
destruct i; try (cbn in Hck; discriminate Hck).
apply andb_prop in Hck as (Hck & Hsig). apply andb_prop in Hck as (Hrd & _). apply Z.eqb_eq in Hsig.
assert (Erd : rd = 1%bv).
{ unfold bv_eqb in Hrd. apply Z.eqb_eq in Hrd. apply bv_eq. symmetry. exact Hrd. }
subst rd.
pose proof (pa_fetch_ok _ _ Hf) as Hfw.
unfold cn_cfg, cn_pc, w64. replace (BASE + CN_OFF + off) with (BASE + (CN_OFF + off)) by lia.
eapply (SRr_step SEGS pa_wx W); [reflexivity | rewrite (@restrict_mkst_fx fxk);
  exact (@step_jal_link fxk SEGS regs _ (mrestrict (w_H W) mem) (YK11.seg_rom SEGS) _ 1%bv imm Hfw
           (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec) |].
intros md' Hs. rewrite (same_but_materialized_wvb md md' Hs).
cbn [ms_mem YK11.mkst]. rewrite (@unrestrict_mkst_mrestrict fxk).
specialize (HK (m_vm_materialized md')). unfold cn_cfg, cn_pc, w64 in HK.
replace (BASE + CN_OFF + (off + 4)) with (BASE + (CN_OFF + (off + 4))) in HK by lia.
change (bv_eqb (1%bv : bv 5) 0%bv) with false. cbv iota.
rewrite (cn_pc4 off ltac:(lia)).
replace (btgt (Z_to_bv 64 (BASE + (CN_OFF + off))) (bv_signed imm)) with (Z_to_bv 64 (SIGMA s)); [exact HK|].
unfold btgt, v_addi. rewrite unsigned_lit_small by lia. rewrite <- Hsig.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, zcanon, M64. change (bv_modulus 64) with (2 ^ 64).
rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* the decoded word of an offset, and the closed boolean checks a walk discharges by vm_compute (a decoded bv is
   convertible to a literal only up to its well-formedness proof, so the checks compare bv_unsigned, never the bv) *)
Definition cn_dec (off : Z) : option (instr * Z) :=
  match plookup A_prog_tpi_cno (CN_OFF + off) with Some (PW w) => decode_any (Z_to_bv 32 w) | _ => None end.
Definition cn_is_addi (off : Z) (rd rs : bv 5) (i : Z) : bool :=
  match cn_dec off with
  | Some (OpImm ALU_ADD rd' rs' imm, sz) => (sz =? 4) && bv_eqb rd' rd && bv_eqb rs' rs && (bv_signed imm =? i)
  | _ => false end.
Definition cn_is_ld (off : Z) (rd rs : bv 5) (i : Z) : bool :=
  match cn_dec off with
  | Some (Load SZ8 true rd' rs' imm, sz) => (sz =? 4) && bv_eqb rd' rd && bv_eqb rs' rs && (bv_signed imm =? i)
  | _ => false end.
Definition cn_is_lbu (off : Z) (rd rs : bv 5) (i : Z) : bool :=
  match cn_dec off with
  | Some (Load SZ1 false rd' rs' imm, sz) => (sz =? 4) && bv_eqb rd' rd && bv_eqb rs' rs && (bv_signed imm =? i)
  | _ => false end.
Definition cn_is_beqz (off : Z) (rs : bv 5) (i : Z) : bool :=
  match cn_dec off with
  | Some (Branch BC_EQ rs' r0 imm, sz) => (sz =? 4) && bv_eqb rs' rs && bv_eqb r0 0%bv && (bv_signed imm =? i)
  | _ => false end.
Definition cn_is_bnez (off : Z) (rs : bv 5) (i : Z) : bool :=
  match cn_dec off with
  | Some (Branch BC_NE rs' r0 imm, sz) => (sz =? 4) && bv_eqb rs' rs && bv_eqb r0 0%bv && (bv_signed imm =? i)
  | _ => false end.
Definition cn_is_j (off : Z) (i : Z) : bool :=
  match cn_dec off with
  | Some (Jal rd' imm, sz) => (sz =? 4) && bv_eqb rd' 0%bv && (bv_signed imm =? i)
  | _ => false end.

Ltac cn_bools := repeat match goal with
  | H : _ && _ = true |- _ => apply andb_prop in H as [? ?]
  | H : bv_eqb _ _ = true |- _ => apply ro_bv_eqb_eq in H
  | H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
  end; subst.
Ltac cn_open H := unfold cn_is_addi, cn_is_ld, cn_is_lbu, cn_is_beqz, cn_is_bnez, cn_is_j, cn_dec in H;
  let Hpl := fresh "Hpl" in let Hdec := fresh "Hdec" in
  let e := fresh "e" in let ii := fresh "ii" in let sz := fresh "sz" in
  match type of H with context [plookup A_prog_tpi_cno ?k] =>
    destruct (plookup A_prog_tpi_cno k) as [e|] eqn:Hpl; [|discriminate H] end;
  destruct e; try (cbv beta iota in H; discriminate H);
  match type of H with context [decode_any ?x] => destruct (decode_any x) as [[ii sz]|] eqn:Hdec; [|discriminate H] end;
  destruct ii; try (cbv beta iota in H; discriminate H);
  repeat match goal with
  | Hd : decode_any _ = Some (OpImm ?o _ _ _, _) |- _ => is_var o; destruct o; try (cbv beta iota in H; discriminate H)
  | Hd : decode_any _ = Some (Load ?z _ _ _ _, _) |- _ => is_var z; destruct z; try (cbv beta iota in H; discriminate H)
  | Hd : decode_any _ = Some (Load _ ?g _ _ _, _) |- _ => is_var g; destruct g; try (cbv beta iota in H; discriminate H)
  | Hd : decode_any _ = Some (Branch ?c _ _ _, _) |- _ => is_var c; destruct c; try (cbv beta iota in H; discriminate H)
  end;
  cbv beta iota in H; cn_bools.

Lemma cn_hs_addi : forall (W : world SEGS) fxk regs mem md Q off off' rd rs i,
  cn_is_addi off rd rs i = true -> bv_eqb rd 0%bv = false -> 0 <= off < 2 ^ 28 -> off' = off + 4 ->
  (forall X, SRr SEGS W (@cn_cfg SEGS fxk (cn_pc off') (regupd regs rd (v_addi (getr regs rs) i)) mem
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (@cn_cfg SEGS fxk (cn_pc off) regs mem md) Q.
Proof.
intros W fxk regs mem md Q off off' rd rs i H. cn_open H. intros Hrd Ho -> HK.
eapply cn_hs_addi0; [exact Hpl | exact Hdec | exact Hrd | exact Ho | reflexivity | exact HK].
Qed.
Lemma cn_hs_ld : forall (W : world SEGS) fxk regs mem md Q off off' rd rs i a v,
  cn_is_ld off rd rs i = true -> bv_eqb rd 0%bv = false -> 0 <= off < 2 ^ 28 -> off' = off + 4 ->
  bv_unsigned (getr regs rs) + i = a -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  rdword (aview SEGS (w_H W) mem) a = Some v ->
  (forall X, SRr SEGS W (@cn_cfg SEGS fxk (cn_pc off') (regupd regs rd (w64 v)) mem (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (@cn_cfg SEGS fxk (cn_pc off) regs mem md) Q.
Proof.
intros W fxk regs mem md Q off off' rd rs i a v H. cn_open H. intros Hrd Ho -> Ha Ha0 Ha8 Hv HK.
eapply cn_hs_ld0; [exact Hpl | exact Hdec | exact Hrd | exact Ho | reflexivity | exact Ha | exact Ha0 | exact Ha8
  | exact Hv | exact HK].
Qed.
Lemma cn_hs_lbu : forall (W : world SEGS) fxk regs mem md Q off off' rd rs i a b,
  cn_is_lbu off rd rs i = true -> bv_eqb rd 0%bv = false -> 0 <= off < 2 ^ 28 -> off' = off + 4 ->
  bv_unsigned (getr regs rs) + i = a ->
  mbyte SEGS (mrestrict (w_H W) mem) a = Some b ->
  (forall X, SRr SEGS W (@cn_cfg SEGS fxk (cn_pc off') (regupd regs rd (Z_to_bv 64 (bv_unsigned b))) mem
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (@cn_cfg SEGS fxk (cn_pc off) regs mem md) Q.
Proof.
intros W fxk regs mem md Q off off' rd rs i a b H. cn_open H. intros Hrd Ho -> Ha Hb HK.
eapply cn_hs_lbu0; [exact Hpl | exact Hdec | exact Hrd | exact Ho | reflexivity | exact Ha | exact Hb | exact HK].
Qed.
(* `beqz rs`: z the register's zero test, tk / ft the taken / fall-through offsets *)
Lemma cn_hs_beqz : forall (W : world SEGS) fxk regs mem md Q off rs i tk ft (z : bool),
  cn_is_beqz off rs i = true -> 0 <= off < 2 ^ 28 -> 0 <= off + i < 2 ^ 28 -> tk = off + i -> ft = off + 4 ->
  c_eq (getr regs rs) (getr regs 0%bv) = z ->
  (forall X, SRr SEGS W (@cn_cfg SEGS fxk (cn_pc (if z then tk else ft)) regs mem
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (@cn_cfg SEGS fxk (cn_pc off) regs mem md) Q.
Proof.
intros W fxk regs mem md Q off rs i tk ft z H. cn_open H. intros Ho Hj -> -> Hc HK.
eapply cn_hs_beqz0; [exact Hpl | exact Hdec | exact Ho | exact Hj | exact Hc | exact HK].
Qed.
(* `bnez rs`: taken when the register is non-zero (z = false) *)
Lemma cn_hs_bnez : forall (W : world SEGS) fxk regs mem md Q off rs i tk ft (z : bool),
  cn_is_bnez off rs i = true -> 0 <= off < 2 ^ 28 -> 0 <= off + i < 2 ^ 28 -> tk = off + i -> ft = off + 4 ->
  c_eq (getr regs rs) (getr regs 0%bv) = z ->
  (forall X, SRr SEGS W (@cn_cfg SEGS fxk (cn_pc (if z then ft else tk)) regs mem
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (@cn_cfg SEGS fxk (cn_pc off) regs mem md) Q.
Proof.
intros W fxk regs mem md Q off rs i tk ft z H. cn_open H. intros Ho Hj -> -> Hc HK.
eapply cn_hs_bnez0; [exact Hpl | exact Hdec | exact Ho | exact Hj | exact Hc | exact HK].
Qed.
Lemma cn_hs_j : forall (W : world SEGS) fxk regs mem md Q off off' i,
  cn_is_j off i = true -> 0 <= off < 2 ^ 28 -> off' = off + i -> 0 <= off' < 2 ^ 28 ->
  (forall X, SRr SEGS W (@cn_cfg SEGS fxk (cn_pc off') regs mem (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (@cn_cfg SEGS fxk (cn_pc off) regs mem md) Q.
Proof.
intros W fxk regs mem md Q off off' i H. cn_open H. intros Ho -> Hj HK.
eapply cn_hs_j0; [exact Hpl | exact Hdec | exact Ho | reflexivity | exact Hj | exact HK].
Qed.

(* ---- A HAND-STEP STRETCH IN A SEGMENT OVER A WORLD RELATION R (a cut after a free: R := wle' SEGS RZ_cf). The steps
   above keep the world, so they stay at SRr; a segment over R runs them inside `SRr W c (fun W' c' => SRrG SEGS R W'
   c' Q)` (SRr_SRrG, then SRrG_bind) and leaves the stretch at its next call or exit by SRr_ret ---- *)
Lemma cn_srrG_lift : forall (R : world SEGS -> world SEGS -> Prop),
  (forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) -> (forall W W', wle W W' -> R W W') ->
  forall W c Q, SRr SEGS W c (fun W' c' => SRrG SEGS R W' c' Q) -> SRrG SEGS R W c Q.
Proof.
intros R Rt Rs W c Q H.
apply (SRrG_bind SEGS R Rt W c (fun W' c' => SRrG SEGS R W' c' Q) Q (SRr_SRrG SEGS R Rs W c _ H)).
intros W' c' _ HK. exact HK.
Qed.

Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
#[local] Notation AJ := (ajournal_x (SK := SK) SEGS B prh_pst ARx).
#[local] Notation AJR R := (ajournal_xR (SK := SK) SEGS B prh_pst ARx R).
#[local] Notation STK := STK_check_no_overread.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
Hypothesis IMG : cn_img B.

Lemma cn_stk_val : STK = 27424.
Proof. vm_compute. reflexivity. Qed.
Lemma cn_stk_ro_val : STK_fuzz_alloc_ran_out = 0.
Proof. vm_compute. reflexivity. Qed.

(* cn_base at the materialised model, at a register file that keeps gp / tp (the journal at its budget WS: rebased
   to the empty budget, materialised, and back at the same WS), over any world relation R; cn_base_mat is its form at
   wle *)
Lemma cn_base_matR : forall (R : world SEGS -> world SEGS -> Prop) D fxk ly S Hp W regs regs' mem md k wk X,
  cn_baseR (fx := fx) B ARx R D fxk ly S Hp W regs mem md k wk ->
  getr regs' 3%bv = getr regs 3%bv -> getr regs' 4%bv = getr regs 4%bv ->
  cn_baseR (fx := fx) B ARx R D fxk ly S Hp W regs' mem (with_vm_backing (m_vm_lazy md) X md) k wk.
Proof.
intros R D fxk ly S Hp W regs regs' mem md k wk X (Hz & Hk & HJ & HF & HSV & R3 & R4 & HRO) E3 E4.
split; [exact Hz|]. split; [exact Hk|].
split.
{ unfold cn_JR in *. destruct HJ as (WS & HJ & HBd). exists WS. split; [|exact HBd].
  pose proof (ajxR_wild HJ) as Hw.
  apply (YCbqGwild.ajournal_xw_unbase0R (SK := SK) SEGS B prh_pst ARx R) with (d := st_depot S); [|exact Hw].
  apply (ajournal_x_materializeR SEGS B prh_pst ARx LAWS pa_segs_low R).
  exact (YCbqGwild.ajournal_xw_rebaseR (SK := SK) SEGS B prh_pst ARx R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). }
split; [exact HF|]. split; [exact HSV|]. split; [rewrite E3; exact R3|]. split; [rewrite E4; exact R4|]. exact HRO.
Qed.
Lemma cn_base_mat : forall D fxk ly S Hp W regs regs' mem md k wk X,
  cn_base (fx := fx) B ARx D fxk ly S Hp W regs mem md k wk ->
  getr regs' 3%bv = getr regs 3%bv -> getr regs' 4%bv = getr regs 4%bv ->
  cn_base (fx := fx) B ARx D fxk ly S Hp W regs' mem (with_vm_backing (m_vm_lazy md) X md) k wk.
Proof. exact (cn_base_matR (@wle SEGS)). Qed.

(* the facts of the entry the steps use *)
Lemma cn_S1_facts : forall D, cn_sp0 D mod 16 = 0 ->
  cn_sp0 D - 208 <= cn_S1 D <= cn_sp0 D - 192 /\ cn_S1 D mod 32 = 0.
Proof. intros D H. unfold cn_S1. rewrite ro_land32. lia. Qed.

Lemma cn_entry_facts : forall CTX0 D, cn_pre (fx := fx) B ARx CTX0 D ->
  cn_sp0 D mod 16 = 0 /\ alloc_ceiling <= ly_stk_lo (ci_ly D) /\ ly_stk_lo (ci_ly D) + STK <= cn_sp0 D /\
  cn_sp0 D <= ly_top (ci_ly D) /\ ly_top (ci_ly D) <= ly_stk_hi (ci_ly D) /\ ly_stk_hi (ci_ly D) <= 2 ^ 47 /\
  cn_sp0 D + 64 <= ly_stk_hi (ci_ly D) /\
  getr (ci_regs D) 3%bv = w64 (as_gp B) /\ getr (ci_regs D) 4%bv = w64 (as_tp B) /\ 4096 <= raZ (ci_regs D) /\
  achain (ci_ly D) (aview SEGS (w_H (ci_W D)) (ci_mem D)) (cn_sp0 D) (s0Z (ci_regs D)) (ci_ch D) /\
  ARx (ci_ly D) (ci_S D) (ci_Hp D) (ci_W D) (ci_mem D) (ci_md D).
Proof.
intros CTX0 D HPRE. pose proof (cn_pre_fpre (fx := fx) B ARx CTX0 D HPRE) as HFP.
destruct HFP as ((HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0) & HROD0 & HSTKHI & HRAC).
destruct Hstk0 as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop1 & Htop2).
unfold cn_sp0. repeat split; try assumption; lia.
Qed.

(* ---- THE FRAME CHAIN at a cno call state: s0 = the entry sp (over any world relation R; cn_chain at wle) ---- *)
Lemma cn_chainR : forall (R : world SEGS -> world SEGS -> Prop) CTX0 D fxk ly S Hp W regs mem md k wk,
  cn_pre (fx := fx) B ARx CTX0 D -> cn_baseR (fx := fx) B ARx R D fxk ly S Hp W regs mem md k wk ->
  exists ch1, achain ly (aview SEGS (w_H W) mem) (cn_S1 D) (cn_sp0 D) ch1.
Proof.
intros R CTX0 D fxk ly S Hp W regs mem md k wk HPRE HB.
destruct (cn_entry_facts CTX0 D HPRE) as (Hal16 & Hceil & Hslo & Htop1 & Htop2 & H47 & Hhi64 & _ & _ & Hra40 & Hch0 & _).
pose proof cn_stk_val as HSTKv.
destruct (cn_S1_facts D Hal16) as (HS1a & HS1b).
destruct HB as (_ & _ & HJ & _ & HSV & _).
unfold cn_JR in HJ. destruct HJ as (WS & HJ & _).
pose proof (ajxR_ly HJ) as Hly. pose proof (ajxR_hi HJ) as F1.
assert (Etop : ly_top ly = ly_top (ci_ly D)) by (destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & E & _); exact E).
destruct (Z_lt_le_dec (cn_sp0 D) (ly_top (ci_ly D) - 16)) as [Hlt|Hge].
- exists ((cn_sp0 D, raZ (ci_regs D), s0Z (ci_regs D)) :: ci_ch D).
  apply (achain_ly_top (ci_ly D) ly); [exact Etop|].
  pose proof (proj1 (Forall_forall _ _) HSV (184, 1%bv) ltac:(ro_in)) as V1.
  pose proof (proj1 (Forall_forall _ _) HSV (176, 8%bv) ltac:(ro_in)) as V8.
  cbn [fst snd] in V1, V8.
  apply (achain_push (ci_ly D) (aview SEGS (w_H (ci_W D)) (ci_mem D)) (aview SEGS (w_H W) mem) (cn_sp0 D)
    (s0Z (ci_regs D)) (raZ (ci_regs D)) (ci_ch D) (cn_S1 D) Hch0).
  + lia.
  + intros a Ha. apply F1; lia.
  + replace (cn_sp0 D - 8) with (cn_sp0 D - 192 + 184) by lia. exact V1.
  + replace (cn_sp0 D - 16) with (cn_sp0 D - 192 + 176) by lia. exact V8.
  + exact Hra40.
  + lia.
  + lia.
  + exact Hlt.
  + lia.
- exists []. left. split; [right; left; rewrite Etop; lia | reflexivity].
Qed.
Lemma cn_chain : forall CTX0 D fxk ly S Hp W regs mem md k wk,
  cn_pre (fx := fx) B ARx CTX0 D -> cn_base (fx := fx) B ARx D fxk ly S Hp W regs mem md k wk ->
  exists ch1, achain ly (aview SEGS (w_H W) mem) (cn_S1 D) (cn_sp0 D) ch1.
Proof. exact (cn_chainR (@wle SEGS)). Qed.

(* ---- THE TRANSFER across a call with an empty footprint that keeps S, Hp and the blocks ---- *)
Lemma cn_open_keep : forall (rd rd' : reader) F c, F mod 32 = 0 -> 0 <= F -> 32 <= c <= 224 ->
  c mod 8 = 0 ->
  (forall a, shadow_addr F <= a < shadow_addr F + 64 -> rd' a = rd a) ->
  range_addressable rd SHADOW_OFF (F + c) 56 /\ shadow_hull_vis rd (F + c) 56 ->
  range_addressable rd' SHADOW_OFF (F + c) 56 /\ shadow_hull_vis rd' (F + c) 56.
Proof.
intros rd rd' F c HF HF0 Hc Hc8 Hk (Hra & Hhv).
assert (Ef : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
set (f := F / 32) in *. clearbody f. subst F.
split.
- apply (range_addressable_agree rd rd' SHADOW_OFF (32 * f + c) 56); [|exact Hra].
  intros x Hx. apply Hk. unfold shadow_of_addr, shadow_addr, SHADOW_OFF. lia.
- intros s Hs. rewrite Hk; [apply Hhv; exact Hs|].
  assert (Ec : c = 8 * (c / 8)) by (pose proof (Z.div_mod c 8 ltac:(lia)); lia).
  set (c' := c / 8) in *. clearbody c'. subst c.
  assert (E0 : 32 * f / 8 = 4 * f) by (replace (32 * f) with ((4 * f) * 8) by lia; apply Z.div_mul; lia).
  assert (E1 : (32 * f + 8 * c') / 8 = 4 * f + c')
    by (replace (32 * f + 8 * c') with ((4 * f + c') * 8) by lia; apply Z.div_mul; lia).
  assert (E2 : (32 * f + 8 * c' + 56 - 1) / 8 = 4 * f + c' + 6).
  { replace (32 * f + 8 * c' + 56 - 1) with (7 + (4 * f + c' + 6) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
  unfold shadow_addr, SHADOW_OFF in *. rewrite E1, E2 in Hs. rewrite E0.
  pose proof (ro_div8 (2147450880 + (4 * f + c'))) as D1. pose proof (ro_div8 (2147450880 + (4 * f + c' + 6))) as D2.
  revert Hs D1 D2. generalize ((2147450880 + (4 * f + c')) / 8) ((2147450880 + (4 * f + c' + 6)) / 8).
  intros q1 q2 Hs D1 D2. clear - Hs D1 D2 Hc. lia.
Qed.

(* HJ2 is the caller's journal REBASED to the empty budget (YCbqGwild.ajournal_xw_rebase: entry set_depot (st_depot S)
   (ci_S D)), what aj_call_xW returns from it; the callee keeps S, so the unbase back to cn_J's WS needs only ajx_wild
   of the call state's journal. Over any world relation R (both journals and cn_baseR at R, read by the ajxR_*
   projections; no law of R is used); cn_call_keep is its form at wle *)
Lemma cn_call_keepR : forall (R : world SEGS -> world SEGS -> Prop)
    CTX0 D fxk ly S Hp W regs mem md k wk Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3 STK1 ly2 W2 regs2 mem2 md2 k1,
  cn_pre (fx := fx) B ARx CTX0 D -> cn_baseR (fx := fx) B ARx R D fxk ly S Hp W regs mem md k wk ->
  cn_regsat regs (cn_core D) -> cn_slots D W mem r1 r2 ->
  cn_mid B D ly S Hp W mem Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3 ->
  0 <= STK1 -> STK1 + (cn_sp0 D - cn_S1 D) <= STK ->
  AJR R STK (cn_sp0 D) [] (ci_ly D) (set_depot (st_depot S) (ci_S D)) (ci_Hp D) (ci_W D) (ci_mem D) (ci_md D)
    [(CN_CID, ci_fpos D)] ly2 S Hp W2 mem2 md2 (k + k1) ->
  AJR R STK1 (cn_S1 D) [] ly S Hp W mem md [] ly2 S Hp W2 mem2 md2 k1 ->
  aregs_preserved regs regs2 -> ablocks B ly2 S = ablocks B ly S ->
  prh_ledger B ly2 S Hp W2 mem2 Lam peak cnt SIZE_MAXZ ran (ci_most D) own ->
  cn_baseR (fx := fx) B ARx R D fxk ly2 S Hp W2 regs2 mem2 md2 (k + k1) wk /\ cn_slots D W2 mem2 r1 r2 /\
  cn_mid B D ly2 S Hp W2 mem2 Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3 /\
  (forall o, cn_fo D W mem Lam o (cn_d1 D) st1 -> cn_fo D W2 mem2 Lam o (cn_d1 D) st1) /\
  (forall o, cn_fo D W mem Lam o (cn_d2 D) st2 -> cn_fo D W2 mem2 Lam o (cn_d2 D) st2) /\
  (forall o, cn_fo D W mem Lam o (cn_d3 D) st3 -> cn_fo D W2 mem2 Lam o (cn_d3 D) st3).
Proof.
intros R CTX0 D fxk ly S Hp W regs mem md k wk Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3 STK1 ly2 W2 regs2 mem2
  md2 k1 HPRE HB HC HSL HM HSTK1 HSTKb HJ2 HJ1 HP HAB HL2.
destruct (cn_entry_facts CTX0 D HPRE) as (Hal16 & Hceil & Hslo & Htop1 & Htop2 & H47 & Hhi64 & _ & _ & _ & _ & HAR0).
pose proof cn_stk_val as HSTKv. pose proof (@cf_head_nonneg cp) as Hh0. pose proof asan_consts as (C1 & _).
destruct (cn_S1_facts D Hal16) as (HS1a & HS1b).
destruct HB as (Hz & Hk & HJ & HF & HSV & R3 & R4 & HROD).
unfold cn_JR in HJ. destruct HJ as (WS & HJ & HBd).
(* the caller's journal back at its budget WS *)
pose proof (YCbqGwild.ajournal_xw_unbase0R (SK := SK) SEGS B prh_pst ARx R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  (st_depot S) WS HJ2 (ajxR_wild HJ)) as HJ2w.
pose proof (ajxR_ar HJ) as HAR. pose proof (ajxR_ly HJ) as Hly.
pose proof (ajxR_ar HJ2w) as HAR2. pose proof (ajxR_ly HJ2w) as Hly2.
pose proof (ajxR_hi HJ1) as G1. pose proof (ajxR_blk HJ1) as G2. pose proof (ajxR_img HJ1) as G3.
pose proof (ajxR_frm HJ1) as G4.
assert (EF1 : ly_F ly = ly_F (ci_ly D)) by (destruct Hly as (_ & _ & _ & _ & _ & E & _); exact E).
assert (EF2 : ly_F ly2 = ly_F (ci_ly D)) by (destruct Hly2 as (_ & _ & _ & _ & _ & E & _); exact E).
assert (EFa1 : frame_addr ly CN_CID (ci_fpos D) = cn_F D) by (unfold cn_F, frame_addr; rewrite EF1; reflexivity).
assert (EFa2 : frame_addr ly2 CN_CID (ci_fpos D) = cn_F D) by (unfold cn_F, frame_addr; rewrite EF2; reflexivity).
assert (EFl : flag_addr ly2 CN_CID (ci_fpos D) = flag_addr ly CN_CID (ci_fpos D))
  by (unfold flag_addr; rewrite EF1, EF2; reflexivity).
assert (EFB : fs_frame_bytes CN_CID = 512) by reflexivity.
destruct HF as (Hfrs & Hnin & Hflag & Hfpres & Hspres).
assert (Hin3 : In (CN_CID, ci_fpos D) (frames S)) by (rewrite Hfrs; left; reflexivity).
destruct (alx_frames SEGS B ARx LAWS ly S Hp W mem md CN_CID (ci_fpos D) HAR Hin3) as (Hal32 & _ & _ & _).
destruct (alx_frames SEGS B ARx LAWS ly2 S Hp W2 mem2 md2 CN_CID (ci_fpos D) HAR2 Hin3)
  as (_ & _ & Hfb2 & Hsh2).
rewrite EFa1 in Hal32. rewrite EFa2, EFB in Hfb2, Hsh2.
destruct (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md CN_CID (ci_fpos D) HAR Hin3) as (HF4096 & HFceil & _).
rewrite EFa1 in HF4096, HFceil. rewrite EFB in HFceil.
(* the kept byte ranges *)
assert (KF : forall a, cn_F D <= a < cn_F D + 512 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha. apply (G4 CN_CID (ci_fpos D) a Hin3); [left; unfold frame_rng, in_zr; cbn [fst snd]; rewrite EFa1, EFB; lia |].
  exact (inFP_nil a). }
assert (KS : forall a, shadow_addr (cn_F D) <= a < shadow_addr (cn_F D) + 64 ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha. apply (G4 CN_CID (ci_fpos D) a Hin3); [right; unfold in_zr; cbn [fst snd]; rewrite EFa1, EFB; lia |].
  exact (inFP_nil a). }
assert (KT : forall a, cn_S1 D <= a < cn_sp0 D -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha. apply G1; lia. }
assert (KB : forall p n i, In (p, n) (ablocks B ly S) -> 0 <= i < req_size n ->
  aview SEGS (w_H W2) mem2 (p + i) = aview SEGS (w_H W) mem (p + i)).
{ intros p n i Hin Hi. apply (G2 p n i Hin); [rewrite HAB; exact Hin | exact Hi | exact (inFP_nil _)]. }
destruct HM as (HC1 & HC2 & HC3 & HLED & Hpk & Hcnt & Hroom & Hbb & HO1 & HO2 & HO3 & HD1 & HD2 & HD3 & HPL & HPA & HNO).
(* a struct's footprint (its 56 bytes in the frame, the blocks of its tree, all in Lam) agrees across the call *)
assert (KA : forall c Dd, 0 <= c -> c + 56 <= 512 -> (forall b, In b Dd -> In b Lam) ->
  pj_agreeR SEGS (rdW W mem) (rdW W2 mem2) (pj_footR (cn_F D + c) Dd)).
{ intros c Dd Hc0 Hc HDL x Hx. destruct Hx as [Hx | ((a & kk) & Hb & Hhold)].
  - split.
    + apply (mbyte_of_aview SEGS). apply KF. lia.
    + intros _. apply (apresent_writable SEGS). exact (proj1 (Hfb2 x ltac:(lia))).
  - unfold pj_holdsR in Hhold. cbn [fst snd] in Hhold.
    pose proof (proj1 (Forall_forall _ _) (prh_ledger_blocks B ly S Hp W mem Lam peak cnt SIZE_MAXZ ran (ci_most D) own HLED)
      (a, kk) (HDL _ Hb)) as (Hkk0 & Hab & _). cbn [fst snd] in Hkk0, Hab.
    pose proof (req_size_pos (kk + @cf_head cp) ltac:(lia)) as (_ & Hq2).
    split.
    + apply (mbyte_of_aview SEGS). replace x with ((a - cf_head) + (x - a + cf_head)) by lia.
      apply (KB _ _ _ Hab). lia.
    + intros _. apply (apresent_writable SEGS).
      assert (Hab2 : In (a - cf_head, kk + cf_head) (ablocks B ly2 S)) by (rewrite HAB; exact Hab).
      destruct (alx_blocks SEGS B ARx LAWS ly2 S Hp W2 mem2 md2 _ _ HAR2 Hab2) as (_ & _ & _ & _ & Hpr & _).
      exact (proj1 (Hpr x ltac:(lia))). }
assert (HL1 : forall b, In b (cn_Dof st1) -> In b Lam)
  by (intros b Hb; apply (Permutation_in _ (Permutation_sym HPL)); apply in_or_app; left; exact Hb).
assert (HL2' : forall b, In b (cn_Dof st2) -> In b Lam)
  by (intros b Hb; apply (Permutation_in _ (Permutation_sym HPL)); apply in_or_app; right; apply in_or_app; left; exact Hb).
assert (HL3 : forall b, In b (cn_Dof st3) -> In b Lam)
  by (intros b Hb; apply (Permutation_in _ (Permutation_sym HPL)); apply in_or_app; right; apply in_or_app; right;
      apply in_or_app; left; exact Hb).
(* the free-order tie of a struct across the call (PRH_PjOrder.pj_foR_frame over the agreeing footprint) *)
assert (KFo : forall st c o, 0 <= c -> c + 56 <= 512 -> (forall b, In b (cn_Dof st) -> In b Lam) ->
  cn_fo D W mem Lam o (cn_F D + c) st -> cn_fo D W2 mem2 Lam o (cn_F D + c) st).
{ intros st c o Hc0 Hc HDL Hf. destruct st as [(t & Dd)|]; unfold cn_fo, cn_Dof in Hf, HDL |- *; [|exact I].
  intros Hh n Hn. destruct (Hf Hh n Hn) as (F & HF' & HMF). exists F. split; [|exact HMF].
  apply (PRH_PjOrder.pj_foR_frame SEGS n (rdW W mem) (rdW W2 mem2) (prh_lin Lam) (prh_lin Lam) (cn_F D + c) Dd F HF').
  - intros a kk Hak. exact (HDL _ Hak).
  - exact (KA c Dd Hc0 Hc HDL). }
split; [|split; [|split; [|split; [|split]]]].
- (* cn_base *)
  split; [exact Hz|]. split; [exact Hk|]. split; [exists WS; split; [exact HJ2w | exact HBd]|].
  split.
  { split; [exact Hfrs|]. split; [exact Hnin|]. split.
    - rewrite EFl, <- Hflag. apply (ro_rdword_kept _ _ (cn_F D) (cn_F D + 512)); [exact KF| rewrite EFB; lia | rewrite EFB; lia].
    - split.
      + intros a Ha. rewrite EFB in Ha. exact (proj1 (Hfb2 a Ha)).
      + intros a Ha. rewrite EFB in Ha. replace a with (shadow_addr (cn_F D) + (a - shadow_addr (cn_F D))) by lia.
        apply (proj1 (Hsh2 (a - shadow_addr (cn_F D)) ltac:(change (512 / 8) with 64 in *; lia))). }
  split.
  { unfold cn_saved in *. apply Forall_forall. intros [o r] Hin.
    pose proof (proj1 (Forall_forall _ _) HSV (o, r) Hin) as Hv. cbn [fst snd] in Hv |- *.
    assert (Ho : 88 <= o <= 184) by (cbn in Hin; repeat destruct Hin as [Hin|Hin]; try (injection Hin as <- _; lia); destruct Hin).
    rewrite <- Hv. apply (ro_rdword_kept _ _ (cn_S1 D) (cn_sp0 D)); [exact KT | lia | lia]. }
  split; [exact (eq_trans (HP 3 ltac:(unfold acallee_saved; lia)) R3)|].
  split; [exact (eq_trans (HP 4 ltac:(unfold acallee_saved; lia)) R4)|].
  intros a Hro Hown Herr. rewrite <- (HROD a Hro Hown Herr). apply G3.
  + destruct Hro as [(sg & Hsg & _ & Hb) | Hrel]; [exists sg; split; [exact Hsg | exact Hb] | exact (pa_relro_img a Hrel)].
  + exact Hown.
  + exact Herr.
  + intros Hpst. exact (cni_pst_rw B IMG a Hpst Hro).
  + intros (r & Hr & _). destruct Hr.
- (* cn_slots *)
  unfold cn_slots in *. apply Forall_forall. intros [o v] Hin.
  pose proof (proj1 (Forall_forall _ _) HSL (o, v) Hin) as Hv. cbn [fst snd] in Hv |- *.
  assert (Ho : 24 <= o <= 80) by (cbn in Hin; repeat destruct Hin as [Hin|Hin]; try (injection Hin as <- _; lia); destruct Hin).
  rewrite <- Hv. apply (ro_rdword_kept _ _ (cn_S1 D) (cn_sp0 D)); [exact KT | lia | lia].
- (* cn_mid *)
  (* the copies *)
  assert (KC : forall r, cn_copy B D ly S Hp W mem r -> cn_copy B D ly2 S Hp W2 mem2 r).
  { intros r [Hr0 | (Hin & Hnh & Hsrc)]; [left; exact Hr0|]. right.
    assert (Hin2 : In (r, cn_size D + 16) (ablocks B ly2 S)) by (rewrite HAB; exact Hin).
    split; [exact Hin2|]. split; [exact Hnh|].
    destruct Hsrc as (Hby & H4096 & Hceil' & Hamr & Hra & Hhv).
    pose proof (req_size_pos (cn_size D + 16) ltac:(unfold cn_size; lia)) as (Hreq1 & Hreq2).
    assert (HnoH : forall h, In h Hp -> ~ (r <= h < r + req_size (cn_size D + 16))).
    { intros h Hh Hhr.
      pose proof (prh_ledger_heads B ly2 S Hp W2 mem2 Lam peak cnt SIZE_MAXZ ran (ci_most D) own HL2) as HPm.
      apply (Permutation_in _ HPm) in Hh. apply in_map_iff in Hh as ((a & kk) & Ea & Hak). cbn [fst] in Ea.
      pose proof (proj1 (Forall_forall _ _) (prh_ledger_blocks B ly2 S Hp W2 mem2 Lam peak cnt SIZE_MAXZ ran (ci_most D) own HL2)
        (a, kk) Hak) as (Hkk0 & Hab & Hahp & _). cbn [fst snd] in Hkk0, Hab, Hahp.
      destruct (alx_blocks SEGS B ARx LAWS ly2 S Hp W2 mem2 md2 _ _ HAR2 Hab) as (_ & _ & _ & _ & _ & Hpw).
      assert (Hne : fst (a - cf_head, kk + cf_head) <> fst (r, cn_size D + 16)).
      { cbn [fst]. intros E. apply Hnh. rewrite <- E. exact Hahp. }
      pose proof (ro_pairwise_map (fun b => (fst b, req_size (snd b))) _ _ _ Hpw Hab Hin2 Hne) as Hdj.
      unfold zdisjoint in Hdj. cbn [fst snd] in Hdj.
      pose proof (req_size_pos (kk + @cf_head cp) ltac:(lia)) as (Hq1 & _). lia. }
    destruct (alx_shadow SEGS B ARx LAWS ly2 S Hp W2 mem2 md2 r (cn_size D + 16) HAR2 Hin2 HnoH) as (Hbs & Hhull).
    unfold cn_size in *.
    split; [|split; [exact H4096|]; split; [exact Hceil'|]; split; [exact Hamr|]; split].
    - unfold bytes_at in *. apply (garr8R_frame SEGS (rdW W mem) (rdW W2 mem2) r (ci_x D) Hby).
      intros x Hx. apply (mbyte_of_aview SEGS). replace x with (r + (x - r)) by lia. apply (KB r _ (x - r) Hin). lia.
    - apply (block_shadow_range _ SHADOW_OFF r (req_size (Z.of_nat (length (ci_x D)) + 16))); [exact Hbs | lia | lia].
    - intros Hl. apply (ro_hull_mono _ r (req_size (Z.of_nat (length (ci_x D)) + 16))); [lia | exact Hhull]. }
  (* the struct opening *)
  assert (KO : forall c, 32 <= c <= 224 -> c mod 8 = 0 ->
    cn_open W mem (cn_F D + c) -> cn_open W2 mem2 (cn_F D + c)).
  { intros c Hc Hc8 Ho. apply (cn_open_keep _ _ (cn_F D) c Hal32 ltac:(lia) Hc Hc8 KS Ho). }
  (* the structs' contents *)
  assert (KD : forall st c, 0 <= c -> c + 56 <= 512 -> (forall b, In b (cn_Dof st) -> In b Lam) ->
    cn_doc W mem Lam (cn_F D + c) st -> cn_doc W2 mem2 Lam (cn_F D + c) st).
  { intros st c Hc0 Hc HDL Hd. destruct st as [(t & Dd)|]; cbn [cn_doc cn_Dof] in Hd, HDL |- *.
    - destruct Hd as (Hn & Hdep). split; [|exact Hdep].
      exact (pj_nodeR_frame SEGS t (rdW W mem) (rdW W2 mem2) (prh_lin Lam) (cn_F D + c) Dd Hn (KA c Dd Hc0 Hc HDL)).
    - apply (pj_zeroR_frame SEGS (rdW W mem) (rdW W2 mem2) (cn_F D + c) Hd).
      intros x Hx. apply (mbyte_of_aview SEGS). apply KF. lia. }
  split; [exact (KC _ HC1)|]. split; [exact (KC _ HC2)|]. split; [exact (KC _ HC3)|].
  split; [exact HL2|]. split; [exact Hpk|]. split; [exact Hcnt|]. split; [exact Hroom|].
  split; [exact Hbb|].
  split; [exact (KO 32 ltac:(lia) ltac:(reflexivity) HO1)|].
  split; [exact (KO 128 ltac:(lia) ltac:(reflexivity) HO2)|].
  split; [exact (KO 224 ltac:(lia) ltac:(reflexivity) HO3)|].
  split; [exact (KD st1 32 ltac:(lia) ltac:(lia) HL1 HD1)|].
  split; [exact (KD st2 128 ltac:(lia) ltac:(lia) HL2' HD2)|].
  split; [exact (KD st3 224 ltac:(lia) ltac:(lia) HL3 HD3)|].
  split; [exact HPL|]. split; [rewrite HAB; exact HPA|]. exact HNO.
- intros o Hf. exact (KFo st1 32 o ltac:(lia) ltac:(lia) HL1 Hf).
- intros o Hf. exact (KFo st2 128 o ltac:(lia) ltac:(lia) HL2' Hf).
- intros o Hf. exact (KFo st3 224 o ltac:(lia) ltac:(lia) HL3 Hf).
Qed.
Lemma cn_call_keep : forall CTX0 D fxk ly S Hp W regs mem md k wk Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3
    STK1 ly2 W2 regs2 mem2 md2 k1,
  cn_pre (fx := fx) B ARx CTX0 D -> cn_base (fx := fx) B ARx D fxk ly S Hp W regs mem md k wk ->
  cn_regsat regs (cn_core D) -> cn_slots D W mem r1 r2 ->
  cn_mid B D ly S Hp W mem Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3 ->
  0 <= STK1 -> STK1 + (cn_sp0 D - cn_S1 D) <= STK ->
  AJ STK (cn_sp0 D) [] (ci_ly D) (set_depot (st_depot S) (ci_S D)) (ci_Hp D) (ci_W D) (ci_mem D) (ci_md D)
    [(CN_CID, ci_fpos D)] ly2 S Hp W2 mem2 md2 (k + k1) ->
  AJ STK1 (cn_S1 D) [] ly S Hp W mem md [] ly2 S Hp W2 mem2 md2 k1 ->
  aregs_preserved regs regs2 -> ablocks B ly2 S = ablocks B ly S ->
  prh_ledger B ly2 S Hp W2 mem2 Lam peak cnt SIZE_MAXZ ran (ci_most D) own ->
  cn_base (fx := fx) B ARx D fxk ly2 S Hp W2 regs2 mem2 md2 (k + k1) wk /\ cn_slots D W2 mem2 r1 r2 /\
  cn_mid B D ly2 S Hp W2 mem2 Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3 /\
  (forall o, cn_fo D W mem Lam o (cn_d1 D) st1 -> cn_fo D W2 mem2 Lam o (cn_d1 D) st1) /\
  (forall o, cn_fo D W mem Lam o (cn_d2 D) st2 -> cn_fo D W2 mem2 Lam o (cn_d2 D) st2) /\
  (forall o, cn_fo D W mem Lam o (cn_d3 D) st3 -> cn_fo D W2 mem2 Lam o (cn_d3 D) st3).
Proof. exact (cn_call_keepR (@wle SEGS)). Qed.

(* ---- THE CALL to fuzz_alloc_ran_out from cno (return sites 0x81bfc / 0x81ccc / 0x81cfc / 0x81ec8) ---- *)
Definition cn_ro_rets : list Z := [760; 968; 1016; 1476].
Hypothesis HRO : forall fz : YK11.FPState,
  @tfuzz_alloc_ran_out_specX fz rc cp prh_img_A RL A_prog_listing PA B ARx SK.

Lemma cn_ro_ret_ok : forall ret, In ret cn_ro_rets ->
  4096 <= cn_pc ret < YM05.alloc_ceiling /\ YK0s.ret_ok (w64 (cn_pc ret)) /\ 0 <= ret < 2 ^ 28.
Proof.
intros ret Hin. pose proof (cni_base B IMG) as HB. pose proof cn_off_val as HO.
assert (H : forall k, 0 <= k < 2 ^ 40 -> match plookup A_prog_tpi_cno k with Some _ => true | None => false end = true ->
  BASE + k < YM05.alloc_ceiling) by (intros kk Hk Hl; exact (@pa_slot_lt_ceil_b _ _ PL_cno_A PA kk Hk Hl)).
unfold cn_pc, w64. replace (BASE + CN_OFF + ret) with (BASE + (CN_OFF + ret)) by lia.
cbn [cn_ro_rets In] in Hin.
destruct Hin as [<- | [<- | [<- | [<- | []]]]]; (split; [split; [rewrite HB; vm_compute; discriminate | apply H;
  [rewrite HO; lia | vm_compute; reflexivity]] | split; [apply ret_ok_codeptr_v; [rewrite HO; lia | vm_compute; reflexivity] | lia]]).
Qed.

(* the call runs aj_call_xW on cn_J's journal rebased to the empty budget (the callee has no wild site); cn_call_keep
   brings it back at the same WS. Over a world relation R that is reflexive, transitive and contains wle (the call
   rule aj_call_xWR at R; the plain text HRO lifted into R by SRr_SRrG and apost_base_x_R_lift); cn_ro_call is its
   form at wle *)
Lemma cn_ro_callR : forall (R : world SEGS -> world SEGS -> Prop), (forall W, R W W) ->
  (forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) -> (forall W W', wle W W' -> R W W') ->
  forall P, srr_inv_call SEGS P ->
  forall CTX0 D fxk ly S Hp W regs mem md k wk Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3 ret,
  cn_pre (fx := fx) B ARx CTX0 D -> In ret cn_ro_rets ->
  cn_baseR (fx := fx) B ARx R D fxk ly S Hp W regs mem md k wk ->
  cn_regsat regs (cn_core D) -> getr regs 1%bv = w64 (cn_pc ret) -> cn_slots D W mem r1 r2 ->
  cn_mid B D ly S Hp W mem Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3 -> P mem ->
  SRrG SEGS R W (@cn_cfg SEGS fxk (SIGMA AS_fuzz_alloc_ran_out) regs mem md) (fun W' c' => exists ly' regs' mem' md' k',
    c' = @cn_cfg SEGS fxk (cn_pc ret) regs' mem' md' /\
    cn_baseR (fx := fx) B ARx R D fxk ly' S Hp W' regs' mem' md' k' wk /\
    aregs_preserved regs regs' /\ getr regs' 10%bv = w64 ran /\ ablocks B ly' S = ablocks B ly S /\
    cn_slots D W' mem' r1 r2 /\ cn_mid B D ly' S Hp W' mem' Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3 /\
    (forall o, cn_fo D W mem Lam o (cn_d1 D) st1 -> cn_fo D W' mem' Lam o (cn_d1 D) st1) /\
    (forall o, cn_fo D W mem Lam o (cn_d2 D) st2 -> cn_fo D W' mem' Lam o (cn_d2 D) st2) /\
    (forall o, cn_fo D W mem Lam o (cn_d3 D) st3 -> cn_fo D W' mem' Lam o (cn_d3 D) st3) /\ P mem').
Proof.
intros R Rr Rt Rs P PCALL CTX0 D fxk ly S Hp W regs mem md k wk Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3 ret
  HPRE Hret HB HC R1 HSL HM HPM.
destruct (cn_entry_facts CTX0 D HPRE) as (Hal16 & Hceil & Hslo & Htop1 & Htop2 & H47 & Hhi64 & Hgp0 & Htp0 & _ & _ & _).
pose proof cn_stk_val as HSTKv. pose proof cn_stk_ro_val as HSTKr. pose proof asan_consts as (C1 & _).
destruct (cn_S1_facts D Hal16) as (HS1a & HS1b).
destruct (cn_ro_ret_ok ret Hret) as ((Hr0 & Hrc) & Hrok & Hr28).
destruct (cn_chainR R CTX0 D fxk ly S Hp W regs mem md k wk HPRE HB) as (ch1 & Hch1).
pose proof HB as (Hz & Hk & HJ & HF & HSV & R3 & R4 & HROD).
unfold cn_JR in HJ. destruct HJ as (WS & HJ & _).
pose proof (ajxR_ly HJ) as Hly.
assert (Eshi : ly_stk_hi ly = ly_stk_hi (ci_ly D))
  by (destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E & _); exact E).
assert (G2 : getr regs 2%bv = w64 (cn_S1 D)) by (apply (cn_regsat_get regs (cn_core D)); [exact HC | ro_in]).
assert (G8 : getr regs 8%bv = w64 (cn_sp0 D)) by (apply (cn_regsat_get regs (cn_core D)); [exact HC | ro_in]).
assert (Hsp : spZ regs = cn_S1 D) by (unfold spZ; rewrite G2; unfold w64; apply unsigned_lit_small; lia).
assert (Hs0 : s0Z regs = cn_sp0 D) by (unfold s0Z; rewrite G8; unfold w64; apply unsigned_lit_small; lia).
assert (Hraz : raZ regs = cn_pc ret) by (unfold raZ; rewrite R1; unfold w64; apply unsigned_lit_small; lia).
pose proof HM as (_ & _ & _ & HLED & _).
unfold cn_cfg, w64.
eapply (SRrG_bind SEGS R Rt).
{ apply (@aj_call_xWR fxk rc SK SEGS B prh_pst ARx cf_head LAWS pa_segs_low R Rr Rt W regs mem
    (SIGMA AS_fuzz_alloc_ran_out)
    STK (cn_sp0 D) [] (ci_ly D) (set_depot (st_depot S) (ci_S D)) (ci_Hp D) (ci_W D) (ci_mem D) (ci_md D)
    [(CN_CID, ci_fpos D)] ly S Hp md k
    STK_fuzz_alloc_ran_out 0 [] (cn_S1 D - cn_sp0 D) (w64 (cn_pc ret)) ch1
    (fQmn mem (fun ly' S' Hp' W' regs' mem' md' =>
       (room_live_cf S -> room_live_cf S') /\
       getr regs' 10 = w64 ran /\ Hp' = Hp /\ S' = S /\ ablocks B ly' S' = ablocks B ly S /\
       prh_ledger B ly' S' Hp' W' mem' Lam peak cnt SIZE_MAXZ ran (ci_most D) own))).
  - exact (YCbqGwild.ajournal_xw_rebaseR (SK := SK) SEGS B prh_pst ARx R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ).
  - rewrite Hsp. lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - reflexivity.
  - lia.
  - rewrite R3. exact Hgp0.
  - rewrite R4. exact Htp0.
  - exact R1.
  - exact Hrok.
  - unfold w64. rewrite unsigned_lit_small by lia. exact Hr0.
  - replace (cn_sp0 D + (cn_S1 D - cn_sp0 D)) with (cn_S1 D) by lia. rewrite Hs0. exact Hch1.
  - intros HAFN _.
    assert (HFP : fpre (fx := fxk) B ARx STK_fuzz_alloc_ran_out ly S Hp W regs mem md ch1).
    { split; [exact HAFN|]. split; [exact HROD|]. split; [rewrite Hsp, Eshi; lia|].
      split; [rewrite Hraz; exact Hrc | exact Hz]. }
    (* the text is not a crossing text: its plain SRr and its post at wle lift into R *)
    eapply (SRrG_mono SEGS R);
      [exact (SRr_SRrG SEGS R Rs _ _ _
                (HRO fxk ly S Hp W regs mem md ch1 Lam peak cnt SIZE_MAXZ ran (ci_most D) own HFP HLED))|].
    intros W' c' _ HPOST. apply fpostW_x_of_apostR. apply apost_base_x_R_lift; [exact Rs | exact HPOST].
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & HJ1 & _ & HP2 & (HQ & HMN)).
destruct HQ as (_ & R10 & -> & -> & HAB & HL2).
rewrite Z.add_0_r in HJ1. replace (cn_sp0 D + (cn_S1 D - cn_sp0 D)) with (cn_S1 D) in HJ1 by lia.
rewrite HSTKr, !Z.add_0_r in HJ1.
destruct (cn_call_keepR R CTX0 D fxk ly S Hp W regs mem md k wk Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3
  0 ly2 W2 regs2 mem2 md2 k1 HPRE HB HC HSL HM ltac:(lia) ltac:(lia) HJ2 HJ1 HP2 HAB HL2)
  as (HB2 & HSL2 & HM2 & HF1 & HF2 & HF3).
apply (SRrG_ret SEGS R Rr). exists ly2, regs2, mem2, md2, (k + k1).
split; [reflexivity|]. split; [exact HB2|]. split; [exact HP2|]. split; [exact R10|]. split; [exact HAB|].
split; [exact HSL2|]. split; [exact HM2|]. split; [exact HF1|]. split; [exact HF2|]. split; [exact HF3|].
exact (PCALL mem mem2 HMN HPM).
Qed.
Lemma cn_ro_call : forall P, srr_inv_call SEGS P ->
  forall CTX0 D fxk ly S Hp W regs mem md k wk Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3 ret,
  cn_pre (fx := fx) B ARx CTX0 D -> In ret cn_ro_rets ->
  cn_base (fx := fx) B ARx D fxk ly S Hp W regs mem md k wk ->
  cn_regsat regs (cn_core D) -> getr regs 1%bv = w64 (cn_pc ret) -> cn_slots D W mem r1 r2 ->
  cn_mid B D ly S Hp W mem Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3 -> P mem ->
  SRr SEGS W (@cn_cfg SEGS fxk (SIGMA AS_fuzz_alloc_ran_out) regs mem md) (fun W' c' => exists ly' regs' mem' md' k',
    c' = @cn_cfg SEGS fxk (cn_pc ret) regs' mem' md' /\ cn_base (fx := fx) B ARx D fxk ly' S Hp W' regs' mem' md' k' wk /\
    aregs_preserved regs regs' /\ getr regs' 10%bv = w64 ran /\ ablocks B ly' S = ablocks B ly S /\
    cn_slots D W' mem' r1 r2 /\ cn_mid B D ly' S Hp W' mem' Lam peak cnt ran own nr r1 r2 r3 st1 st2 st3 /\
    (forall o, cn_fo D W mem Lam o (cn_d1 D) st1 -> cn_fo D W' mem' Lam o (cn_d1 D) st1) /\
    (forall o, cn_fo D W mem Lam o (cn_d2 D) st2 -> cn_fo D W' mem' Lam o (cn_d2 D) st2) /\
    (forall o, cn_fo D W mem Lam o (cn_d3 D) st3 -> cn_fo D W' mem' Lam o (cn_d3 D) st3) /\ P mem').
Proof. exact (cn_ro_callR (@wle SEGS) (wle_refl SEGS) (wle_trans SEGS) (fun W W' H => H)). Qed.

End ro.
