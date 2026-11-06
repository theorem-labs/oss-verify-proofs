(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module paths and module names changed; 1243 of its 1273 lines of code are new or changed and 39 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI04 YI09 YI08 YI00 YN3v YG0v YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09 YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
YC1g YC1h YC81 YC4b YC45 YC85 YCkd YC1i ACbf ACj1 DiscoACjr DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoEntryInv DiscoEntSeatStmt DiscoEntSeat DiscoEntBodyStmt DiscoEntBody
ClassifyCore ReacDiscoClassify ReacDiscoClassifyOnSegment CheckSighting ReacDiscoGateShouldPush.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_table_c disco_classify_c hunt_c SightModel slot_inv slot_frame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require GateModel CtrlParsed slot_classify.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoEntClsCuts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require AE2k.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoSites.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoEntClsL6 DiscoEntClsLoop DiscoEntClsLoop10.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis MT_TRIV : MT = ameter_triv.
Hypothesis DCAN : asink_img_laws SEGS B tfib_K /\ ak_canary tfib_K = AE2k.FF_canary.
Hypothesis TCLS : treac_disco_classify_spec B.
Hypothesis TCLSS : treac_disco_classify_on_segment_spec B.
Hypothesis TCHKS : tcheck_sighting_spec B.
Hypothesis TGP : treac_disco_gate_should_push_spec B.
Hypothesis ABCMP : forall fq : YK11.FPState, abcmp_realizes (fx := fq) SEGS B (SIGMA DS___interceptor_trampoline_bcmp).
#[local] Notation DAT := (d_at B MT XM_LIB RLO RHI tfib_K).
#[local] Notation DCTX := (d_ctx B MT XM_LIB RLO RHI tfib_K).
#[local] Notation cl_base := (cl_base B).
#[local] Notation cl_R := (cl_R B MT XM_LIB RLO RHI tfib_K).
#[local] Notation cl_CSR := (cl_CSR B MT XM_LIB RLO RHI tfib_K).
#[local] Notation cl_GR := (cl_GR B MT XM_LIB RLO RHI tfib_K).
#[local] Notation cl_LI := (cl_LI B MT XM_LIB RLO RHI tfib_K).
#[local] Notation cl_X := (cl_X B MT XM_LIB RLO RHI tfib_K).
#[local] Notation cl_amax := (cl_amax MT).
#[local] Notation cl_kept := (cl_kept B).
#[local] Notation cl_frame_keep := (cl_frame_keep B MT XM_LIB RLO RHI tfib_K LAWS).
#[local] Notation cl_achain := (cl_achain B MT XM_LIB XN_LIB RLO RHI tfib_K).
#[local] Notation cl_cread_obj := (cl_cread_obj B MT XM_LIB RLO RHI tfib_K LAWS).
#[local] Notation cl_view_A := (cl_view_A B MT XM_LIB RLO RHI tfib_K LAWS).
#[local] Notation cl_body_call := (cl_body_call B MT XM_LIB RLO RHI tfib_K LAWS DCAN).
#[local] Notation cl_frm_keep := (cl_frm_keep B MT XM_LIB RLO RHI tfib_K LAWS).
#[local] Notation cl_regs_ok := (cl_regs_ok B).
#[local] Notation cl_body_n := (cl_body_n B).
#[local] Notation cl_s_not_rdset := (cl_s_not_rdset B tfib_K DCAN).

Lemma cl_lock_ok : forall F len U Lb Lb', length F = 50%nat -> lock_ok Lb ->
  cm_lock F len U (Some Lb) = Some Lb' -> lock_ok Lb'.
Proof.
intros F len U Lb Lb' LF HL E. unfold cm_lock, classify_model in E. cbv zeta in E.
repeat (match type of E with context [if ?c then _ else _] => destruct c end); cbn [snd fst] in E;
  injection E as <-; try exact HL.
pose proof HL as (HL12 & _).
assert (Ls : length (src F) = 6%nat) by (unfold src, CtrlParsed.fld; rewrite length_firstn, length_skipn, LF; reflexivity).
assert (Lf : length (firstn 2 (skipn 6 Lb)) = 2%nat) by (rewrite length_firstn, length_skipn, HL12; reflexivity).
unfold lock_ok, latch. split.
- unfold CtrlParsed.fld. rewrite !length_app, Ls, Lf, slot_classify.sc_le4_len. reflexivity.
- right. unfold CtrlParsed.fu, CtrlParsed.fld. rewrite app_assoc, skipn_app, length_app, Ls, Lf.
  rewrite skipn_all2 by (rewrite length_app, Ls, Lf; lia). replace (8 - (6 + 2))%nat with 0%nat by reflexivity.
  rewrite skipn_O.
  vm_compute. reflexivity.
Qed.

Lemma cl_cls_ret : forall cx h i n now op nb fr len (fq : YK11.FPState) ly3 S3 (W : world SEGS) (regs4 : bvmap 5 word) m4 md4
  k acc pc lk (L : option (list byte)) (OB : list byte) (W2 : world SEGS) c2,
  lib.Lib.FP.frm0 (@YK11.fp_csr fq) -> d_base B MT XM_LIB RLO RHI tfib_K cx ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W m4 md4 k ->
  frames S3 = [(DFRAME_CLASS, c_fpos cx)] ->
  0 <= k <= cl_kmax i -> acc <= cl_amax i ->
  cl_base cx h i n now op nb fr len regs4 ly3 S3 W m4 -> dR_cls cx nb fr len regs4 ->
  getr regs4 1 = w64 (BASE + pc) -> spZ regs4 = d_A cx ->
  ((L = None /\ lk = 0) \/ (exists Lb, L = Some Lb /\ lk = d_obj cx OLOCK /\ lock_ok Lb)) ->
  tcls_post B fq LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(DFRAME_CLASS, c_fpos cx)]
    ly3 S3 W m4 k regs4 lk (d_obj cx OS) len (slot_classify.fb50 (firstn (Z.to_nat len) (rest_of (c_pl cx) nb)))
    (our_of (c_pl cx)) OB L W2 c2 ->
  cl_R cx h i n now op nb fr len pc W2 c2.
Proof.
intros cx h i n now op nb fr len fq ly3 S3 W regs4 m4 md4 k acc pc lk L OB W2 c2
  Hfq Hb HJ3 Hfrs Hk Hacc HB3 HR3 R1 Hsp4 HL Hpost.
set (FB := slot_classify.fb50 (firstn (Z.to_nat len) (rest_of (c_pl cx) nb))) in *.
destruct Hpost as (fx2 & ly2 & S2 & regs2 & mem2 & md2 & Hc & _ & Hcsr2 & HJ2 & HPR & Hfr2 & Hperm2 & Hret & Hout & Hlock & HK).
assert (Hfx2 : lib.Lib.FP.frm0 (@YK11.fp_csr fx2)).
{ destruct Hcsr2 as [Ecsr | Ecsr]; [rewrite Ecsr; exact Hfq | exact Ecsr]. }
change (k + EV_CLS) with (k + 0) in HJ2. rewrite Z.add_0_r in HJ2.
assert (HC3 : DCTX cx ly3 S3 W m4 md4 k) by (split; [exact Hb | split; assumption]).
assert (HC2 : DCTX cx ly2 S2 W2 mem2 md2 k) by (split; [exact Hb | split; [exact HJ2 | rewrite Hfr2; exact Hfrs]]).
pose proof HB3 as (Hi & Hn & Hnow & Hop & Hop2 & HrL & Hsp0 & Hfrm & H248 & H408 & H392 & Hlen & Hnb & Hnbn & Hbody).
pose proof HrL as (Hsp & Hgp & Htp & H8 & H9 & H18 & H20 & H25).
pose proof HR3 as (R27 & R24 & R23 & R26 & R22).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & Hshadow & Hobjs & Hblocks & Hinput & Himg & Hoff & Hgeo & _ & Hstk & Hawr).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W m4 md4 k HC3)
  as (Hal16 & Hlo & Hhi & HF0 & HFc & HFia & HFo & HFal & HFpres & HSpres & HWpres & HAR & Hfin & Efa & Efl).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
pose proof Hgeo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
set (wr := cls_wr lk (d_obj cx OS) L).
assert (HK' : cl_kept ly3 S3 W m4 W2 mem2 (d_A cx - CLS_STK) (d_A cx) wr) by (unfold tcls_kept in HK; rewrite Hsp4 in HK; exact HK).
assert (Hwr : forall a, wr a -> d_FB cx + 24 <= a < d_FB cx + DFRAME_SIZE).
{ intros a Ha. unfold wr, cls_wr in Ha. unfold DFRAME_SIZE.
  destruct HL as [(-> & ->) | (Lb & -> & -> & _)]; unfold d_obj in Ha; cbn [dobj_off] in Ha; destruct Ha as [Ha | Ha];
    [lia | destruct Ha | lia | cbn [dobj_off] in Ha; lia]. }
assert (Hwrc : forall a, wr a -> a < alloc_ceiling) by (intros a Ha; pose proof (Hwr a Ha); rewrite fs6 in G2; unfold DFRAME_SIZE in *; lia).
assert (KA : forall a, d_A cx <= a < d_S cx -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) m4 a)
  by exact (cl_view_A cx ly3 S3 W m4 md4 k W2 mem2 _ _ wr HC3 HK' ltac:(lia) Hwrc).
assert (VA : forall o v, 0 <= o -> o + 8 <= 472 -> val_mem SEGS (rd W m4) (d_A cx + o) 8 v ->
  val_mem SEGS (rd W2 mem2) (d_A cx + o) 8 v).
{ intros o v Ho1 Ho2 Hv. eapply YC88.val_mem_aview_kept_x; [|exact Hv]. intros x Hx. apply KA.
  change (Z.of_nat 8) with 8 in Hx. unfold MFRAME in HA1. lia. }
set (os := match L with None => [] | Some _ => [OLOCK] end).
assert (Hos : forall a, wr a -> d_rdset B cx h a -> Exists (fun o => d_objr cx o a) os).
{ intros a Ha Hrd. unfold wr, cls_wr in Ha. destruct (cl_objr_dec cx OLOCK a) as [Hlk | Hnlk].
  - destruct HL as [(EL & Elk) | (Lb & EL & Elk & _)].
    + exfalso. subst L lk. destruct Ha as [Ha | Ha]; [|destruct Ha].
      unfold d_obj in Ha. cbn [dobj_off] in Ha. unfold d_objr, d_obj in Hlk. cbn [dobj_off dobj_size] in Hlk. lia.
    + unfold os. rewrite EL. apply Exists_cons_hd. exact Hlk.
  - exfalso. apply (cl_s_not_rdset cx h a Hgeo Hoff); [|exact Hnlk|exact Hrd].
    destruct HL as [(-> & ->) | (Lb & -> & -> & _)]; unfold d_obj in Ha; cbn [dobj_off] in Ha; destruct Ha as [Ha | Ha];
      [lia | destruct Ha | lia | cbn [dobj_off] in Ha; lia]. }
assert (Hnew : Forall (fun o => d_obj_new cx o W2 mem2) os).
{ unfold os. destruct HL as [(-> & ->) | (Lb & -> & -> & HLok)]; [apply Forall_nil|].
  apply Forall_cons; [|apply Forall_nil].
  destruct (slot_classify.sc_cm_lock FB len (our_of (c_pl cx)) Lb (slot_classify.fb50_len _) (proj1 HLok)) as (Lb' & ELb & LLb).
  exists Lb'. split; [exact LLb|]. split; [exact (Hlock Lb' ELb)|].
  exact (cl_lock_ok FB len (our_of (c_pl cx)) Lb Lb' (slot_classify.fb50_len _) HLok ELb). }
unfold cl_R, d_at. exists fx2, ly2, S2, regs2, mem2, md2, k, acc.
split; [rewrite Hc, R1; reflexivity|]. split; [exact Hfx2|].
split; [exact Hb|]. split; [exact HJ2|]. split; [rewrite Hfr2; exact Hfrs|]. split; [exact Hk|].
split; [pose proof HJ2 as (_ & _ & _ & _ & _ & _ & Hnev2 & _); unfold cl_kmax in *; lia|].
split; [rewrite MT_TRIV; exact I|]. split; [exact Hacc|].
exists (cm_ret FB len (our_of (c_pl cx)) L).
split; [|split; [|split]].
- unfold cl_base. split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|]. split; [exact Hop|]. split; [exact Hop2|].
  split.
  { unfold d_rL. unfold spZ in Hsp |- *.
    assert (E2 : getr regs2 2 = getr regs4 2) by exact (cl_cs regs4 regs2 2 _ HPR ltac:(unfold acallee_saved; lia) eq_refl).
    rewrite E2. split; [exact Hsp|].
    split; [exact (cl_cs regs4 regs2 3 _ HPR ltac:(unfold acallee_saved; lia) Hgp)|].
    split; [exact (cl_cs regs4 regs2 4 _ HPR ltac:(unfold acallee_saved; lia) Htp)|].
    split; [exact (cl_cs regs4 regs2 8 _ HPR ltac:(unfold acallee_saved; lia) H8)|].
    split; [exact (cl_cs regs4 regs2 9 _ HPR ltac:(unfold acallee_saved; lia) H9)|].
    split; [exact (cl_cs regs4 regs2 18 _ HPR ltac:(unfold acallee_saved; lia) H18)|].
    split; [exact (cl_cs regs4 regs2 20 _ HPR ltac:(unfold acallee_saved; lia) H20)|].
    exact (cl_cs regs4 regs2 25 _ HPR ltac:(unfold acallee_saved; lia) H25). }
  split; [destruct Hsp0 as (S1 & S2'); split; apply VA; first [lia | assumption]|].
  split; [exact (cl_frm_keep cx nb fr len ly3 S3 W m4 md4 k W2 mem2 _ _ wr h n dsh_rec HC3 Hbody HK'
    ltac:(intros a Ha; pose proof (Hwr a Ha); lia) Hfrm)|].
  split; [apply VA; [lia | lia | exact H248]|].
  split; [apply VA; [lia | lia | exact H408]|].
  split; [apply VA; [lia | lia | exact H392]|].
  split; [exact Hlen|]. split; [exact Hnb|]. split; [exact Hnbn|].
  exact (cl_body_call cx h n (dxb fr len) dsh_rec ly3 S3 W m4 md4 k ly2 S2 W2 mem2 md2 k _ _ wr os Hbody HC3 HC2 HK'
    ltac:(unfold CLS_STK, CLS_OWN_BCMP, CLS_VIA_PARSE, CLS_FRAME, CLS_PARSE_NEED, ESTACK, MFRAME, LLVMF_STK in *; lia)
    ltac:(lia) Hwr Hos Hnew Hperm2).
- unfold dR_cls.
  split; [exact (cl_cs regs4 regs2 27 _ HPR ltac:(unfold acallee_saved; lia) R27)|].
  split; [exact (cl_cs regs4 regs2 24 _ HPR ltac:(unfold acallee_saved; lia) R24)|].
  split; [exact (cl_cs regs4 regs2 23 _ HPR ltac:(unfold acallee_saved; lia) R23)|].
  split; [exact (cl_cs regs4 regs2 26 _ HPR ltac:(unfold acallee_saved; lia) R26)|].
  exact (cl_cs regs4 regs2 22 _ HPR ltac:(unfold acallee_saved; lia) R22).
- exact Hret.
- destruct (slot_classify.sc_cm_ret_cases FB len (our_of (c_pl cx)) L) as [E | E]; [left; exact E|].
  right. split; [exact E|]. exists (cm_out FB len (our_of (c_pl cx)) L OB).
  destruct (slot_classify.sc_sight FB len (our_of (c_pl cx)) L (slot_classify.fb50_len _) E) as (Hsf & Hl24 & _ & _).
  destruct (slot_classify.sc_cm_ret0 FB len (our_of (c_pl cx)) L OB E) as (_ & _ & _ & Eout).
  unfold cl_sg. rewrite Eout in Hout |- *.
  split; [exact Hl24|]. split; [exact Hout|].
  assert (H50 : 50 <= len) by exact (proj1 Hsf).
  assert (EF : FB = cl_F (c_pl cx) nb len).
  { unfold FB, cl_F. apply cl_fb50. rewrite cl_rest_len; [lia | pose proof Hfrm as (F1 & _); lia | lia]. }
  rewrite <- EF. exact Hsf.
Qed.

Lemma cl_top : forall cx ly3 S3 (W : world SEGS) m md k, DCTX cx ly3 S3 W m md k ->
  d_S cx <= ly_top ly3 /\ alloc_ceiling <= ly_stk_lo ly3.
Proof.
intros cx ly3 S3 W m md k (Hbase & HJ & _).
destruct Hbase as ((HPRE & _) & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (_ & _ & Hceil & _ & _ & _ & _ & Htop1 & _).
pose proof HJ as (_ & Hly & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & _).
change (spZ (c_regs cx)) with (d_S cx) in *. rewrite Etop, Eslo. lia.
Qed.

Lemma cl_base_ro : forall cx h i n now op nb fr len regs regs4 ly3 S3 (W : world SEGS) mem3 m4 md4 k,
  cl_base cx h i n now op nb fr len regs ly3 S3 W mem3 -> DCTX cx ly3 S3 W m4 md4 k ->
  (forall x, m4 x = mem3 x) -> (forall x, rd W m4 x = rd W mem3 x) ->
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 20; 25]%bv -> getr regs4 r = getr regs r) ->
  cl_base cx h i n now op nb fr len regs4 ly3 S3 W m4.
Proof.
intros cx h i n now op nb fr len regs regs4 ly3 S3 W mem3 m4 md4 k HB HC Hpt Hptr RG.
pose proof HB as (Hi & Hn & Hnow & Hop & Hop2 & HrL & Hsp0 & Hfrm & H248 & H408 & H392 & Hlen & Hnb & Hnbn & Hbody).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & Hshadow & _).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W m4 md4 k HC) as (Hal16 & Hlo & Hhi & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
assert (Hav : forall a, aview SEGS (w_H W) m4 a = aview SEGS (w_H W) mem3 a) by (intros a; apply aview_eq_of; apply Hptr).
assert (VM : forall a v, val_mem SEGS (rd W mem3) a 8 v -> val_mem SEGS (rd W m4) a 8 v)
  by (intros a v Hv; eapply YC88.val_mem_aview_kept_x; [|exact Hv]; intros x _; exact (Hav x)).
split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|]. split; [exact Hop|]. split; [exact Hop2|].
split.
{ destruct HrL as (Hsp & Hgp & Htp & H8 & H9 & H18 & H20 & H25). unfold d_rL, spZ in *.
  rewrite !RG by (cbv; tauto). repeat split; assumption. }
split; [destruct Hsp0 as (S1 & S2); split; apply VM; assumption|].
split; [destruct Hfrm as (F1 & F2 & Fnb & F3); split; [exact F1|]; split; [exact F2|]; split; [exact Fnb|];
  eapply YC88.garr8_aview_kept; [|exact F3]; intros x _; exact (Hav x)|].
split; [apply VM; exact H248|]. split; [apply VM; exact H408|]. split; [apply VM; exact H392|].
split; [exact Hlen|]. split; [exact Hnb|]. split; [exact Hnbn|].
apply (d_body_rt B cx h n n (dxb fr len) dsh_rec dsh_rec ly3 S3 W mem3 m4 (d_A cx) (d_A cx) (fun _ => False) Hbody).
- unfold LLVMF_STK, MFRAME in *; lia.
- unfold MFRAME in HA1; lia.
- intros a [].
- intros a _ _. exact (Hav a).
- intros a _ [Hh [b Hb]]. split; [exact Hh|]. exists b. rewrite Hpt. exact Hb.
- exact (cl_frame_keep cx h dsh_rec W mem3 ly3 S3 W m4 md4 k HC Hframe (fun a _ => Hav a)).
- exact (cl_shadow_keep cx dsh_rec W W mem3 m4 Hshadow (fun a _ => Hav a)).
- lia.
Qed.

Lemma cl_fblk : forall cx h n shf nb fr len ly3 S3 (W : world SEGS) m md k,
  DCTX cx ly3 S3 W m md k -> d_body B cx h n (dxb fr len) shf ly3 S3 W m -> d_frm cx nb fr len W m ->
  nb <= c_n cx -> len <= nb -> 50 <= len ->
  0 < fr /\ cls_read W m (d_A cx) fr 50 /\ cls_sep B ly3 S3 fr 50 /\
  garr8 SEGS (rd W m) fr (cls_bytes (slot_classify.fb50 (firstn (Z.to_nat len) (rest_of (c_pl cx) nb)))) /\
  (fr + req_size len <= d_FB cx \/ d_FB cx + 4096 <= fr) /\ In (fr, len) (ablocks B ly3 S3) /\
  fr + req_size len <= alloc_ceiling /\ off_img fr (req_size len) /\ len <= req_size len.
Proof.
intros cx h n shf nb fr len ly3 S3 W m md k HC HB (F1 & F2 & Fnb & F3) Hnbn Hlen H50.
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & Hbl & _ & _ & _ & Hgeo & _).
pose proof Hgeo as (_ & _ & _ & _ & _ & G6 & _).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W m md k HC)
  as (Hal16 & Hlo & Hhi & HF0 & HFc & HFia & HFo & HFal & HFpres & HSpres & HWpres & HAR & Hfin & Efa & Efl).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
assert (Hne : fr <> 0) by (intros E0; specialize (F2 E0); lia).
assert (Hin : In (fr, len) (ablocks B ly3 S3)).
{ pose proof Hbl as (Hp & _). eapply Permutation_in; [apply Permutation_sym; exact Hp|].
  unfold dxb. replace (fr =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hne). left; reflexivity. }
destruct (al_blocks _ _ LAWS ly3 S3 W m md fr len HAR Hin) as (Hfr16 & Hfr0 & Hfrc & Hfra & Hfrp & _).
pose proof (req_size_pos len ltac:(lia)) as Hrq.
pose proof (sep_block_frame SEGS B LAWS ly3 S3 W m md fr len DFRAME_CLASS (c_fpos cx) HAR Hin Hfin) as Hd.
rewrite Efa, fs6 in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
split; [lia|]. split; [|split; [|split; [|split; [lia | split; [exact Hin|
  split; [lia | split; [exact (blk_off_imgP B ly3 S3 W m md fr len HAR Hin) | lia]]]]]]].
- unfold cls_read. split; [lia|]. split; [pose proof alloc_ceiling_lt; lia|].
  split; [exact (amem_range_of_block SEGS B LAWS ly3 S3 W m md fr len fr 50 HAR Hin ltac:(lia) ltac:(lia))|].
  split; [right; unfold CLS_STK, CLS_OWN_BCMP, CLS_VIA_PARSE, CLS_FRAME, CLS_PARSE_NEED, ESTACK, MFRAME, LLVMF_STK in *; lia|].
  split; [intros a Ha; apply (Hfrp a); lia|].
  split; [exact (range_addressable_of_block SEGS B LAWS ly3 S3 W m md fr len fr 50 HAR Hin ltac:(lia) ltac:(lia))|].
  exact (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 W m md fr len fr 50 HAR Hin ltac:(lia) ltac:(lia) ltac:(lia)).
- right. left. exists fr, len. split; [exact Hin|]. lia.
- unfold cls_bytes. rewrite cl_fb50 by (rewrite cl_rest_len; lia). apply cl_garr8_firstn. exact F3.
Qed.

Lemma cl_s1 : forall cx h i n now op nb fr len W c,
  cls_in B MT XM_LIB RLO RHI tfib_K cx h i n now op nb fr len W c -> op mod 4 = 0 -> nb <= c_n cx ->
  SRr SEGS W c (cl_R cx h i n now op nb fr len 0xce4).
Proof.
intros cx h i n now op nb fr len W c Hin Hop0 Hnbn.
unfold cls_in, d_arm_at_pf in Hin. rewrite Hop0 in Hin. cbn [Z.eqb] in Hin.
destruct Hin as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hfq & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc & HP).
destruct HP as (Hi & Hn & Hnow & HrL & HR & HX & Hsp0 & Hbody).
destruct HX as (Hop & Hop2 & Hfrm & H248 & H408 & H392 & Hlen & Hnb).
assert (HB3 : cl_base cx h i n now op nb fr len regs ly3 S3 W mem3)
  by exact (conj Hi (conj Hn (conj Hnow (conj (or_introl Hop0) (conj Hop2 (conj HrL (conj Hsp0 (conj Hfrm (conj H248 (conj H408
    (conj H392 (conj Hlen (conj Hnb (conj Hnbn Hbody)))))))))))))).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & Hshadow & Hobjs & Hblocks & Hinput & Himg & Hoff & Hgeo & _ & Hstk & Hawr).
pose proof Hframe as (E & HdE & Hregs & Hflag & Hh216 & Hh152).
assert (HctxD : DCTX cx ly3 S3 W mem3 md3 k) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HctxD)
  as (Hal16 & Hlo & Hhi & HF0 & HFc & HFia & HFo & HFal & HFpres & HSpres & HWpres & HAR & Hfin & Efa & Efl).
pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HAr2 : 0 <= d_A cx < 2 ^ 64) by (unfold MFRAME, LLVMF_STK in *; lia).
pose proof (d_seat B MT XM_LIB RLO RHI tfib_K LAWS TL fq cx dsh_rec ly3 S3 W regs mem3 md3 k E CLS_OFF cl_sr
  (cl_vals regs []) [] [] [] (d_facts [] [])
  HctxD HdE Hregs Hflag (cl_regs_ok cx E regs [] HdE HrL HAr2)
  (d_facts_ok B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k E (cl_vals regs []) [] [] HctxD HdE I I)
  (Forall_nil _) (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS.
unfold ss_d in HS.
cl_ro_base HS 516%nat. cl_ro_base HS 529%nat. cl_ro_base HS 60%nat.
assert (HEI : img_env VAL A_LIM (d_env cx E (cl_vals regs []))).
{ destruct HdE as (_ & _ & HI & _). intros a Ha. unfold d_env. rewrite ew_havoc_old by (unfold A_LIM, AT_FL in *; lia). exact (HI a Ha). }
assert (SHOK : sh_ok SEGS (SOff 32 0) [] (d_env cx E (cl_vals regs [])) (rd W mem3)) by constructor.
pose (RUN := paj_run (fx := fq) B LAWS).
unfold cfg_at. change (w64 (BASE + CLS_OFF)) with (Z_to_bv 64 (BASE + CLS_OFF)).
paj_run_tok RUN HS HJ SHOK cl_span.
{ cbn [ss_mem]. repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
assert (Hpt := cl_ro_pt _ _ _ _ HF ltac:(vm_compute; reflexivity)).
assert (Hptr := cl_ro_pt _ _ _ _ HFr ltac:(vm_compute; reflexivity)).
clear HF HFr HG.
rewrite (pa_sigma_reac_disco_classify (PI := PI)) in HS.
pose proof (cl_regs_ok cx E regs [] HdE HrL HAr2) as HROK.
assert (RG : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
  getr (ms_regs ms) r = getr regs r).
{ intros r Hr. rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms r HS), (HROK r).
  cbv [In] in Hr. repeat (destruct Hr as [<-|Hr]; [f_equal; vm_compute; reflexivity|]). destruct Hr. }
assert (RMV : forall r r' : bv 5, sr_get (ss_regs (setpc (mkSS 3300 [] [] None (mkFacts [] [] [])) 0)) r = sr_get cl_sr r' -> True)
  by (intros; exact I).
clear RMV.
pose proof HR as (R27 & R24 & R23 & R26 & R22).
assert (R1 : getr (ms_regs ms) 1 = w64 (BASE + 0xce4)).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 1%bv HS).
  match goal with |- context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
  unfold w64. exact (codeptr_val _ 3300 HEI). }
assert (A10 : getr (ms_regs ms) 10 = w64 fr).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 10%bv HS). rewrite <- R27, (HROK 27%bv). f_equal; vm_compute; reflexivity. }
assert (A11 : getr (ms_regs ms) 11 = w64 len).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 11%bv HS). rewrite <- R24, (HROK 24%bv). f_equal; vm_compute; reflexivity. }
assert (A12 : getr (ms_regs ms) 12 = w64 (d_obj cx OOUR)).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 12%bv HS). rewrite <- R26, (HROK 26%bv). f_equal; vm_compute; reflexivity. }
assert (A13 : getr (ms_regs ms) 13 = w64 (d_obj cx OS)).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 13%bv HS). rewrite <- R22, (HROK 22%bv). f_equal; vm_compute; reflexivity. }
pose proof (st_ok_restrict_mkst SEGS (w_H W) _ _ ms HS eq_refl) as Hms. cbn [ss_pc setpc] in Hms.
set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *.
assert (HC4 : DCTX cx ly3 S3 W (ms_mem ms) md4 k) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
pose proof (cl_base_ro cx h i n now op nb fr len regs (ms_regs ms) ly3 S3 W mem3 (ms_mem ms) md4 k HB3 HC4 Hpt Hptr
  ltac:(intros r Hr; apply RG; cbv [In] in Hr |- *; tauto)) as HB4.
assert (HR4 : dR_cls cx nb fr len (ms_regs ms)).
{ unfold dR_cls. rewrite !RG by (cbv; tauto). exact HR. }
pose proof HB4 as (_ & _ & _ & _ & _ & HrL4 & _ & Hfrm4 & _ & _ & _ & _ & _ & _ & Hbody4).
pose proof HrL4 as (Hsp4 & Hgp4 & Htp4 & H84 & _).
pose proof Hbody4 as (T4 & G4 & Lk4 & H4 & Hframe4 & Hshadow4 & Hobjs4 & Hblocks4 & Hinput4 & Himg4 & Hoff4 & Hgeo4 & _ & Hstk4 & Hawr4).
pose proof Hframe4 as (E4 & HdE4 & Hregs4 & _).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W (ms_mem ms) md4 k HC4)
  as (_ & _ & _ & _ & _ & _ & _ & _ & HFpres4 & _ & _ & HAR4 & _ & _ & _).
destruct (cl_achain cx ly3 S3 W (ms_mem ms) md4 k E4 (d_A cx) HC4 HdE4 (Forall_inv Hregs4)
  ltac:(unfold MFRAME in HA1; lia)) as (ch & Hch).
destruct (cl_garr8_ex (w_H W) (ms_mem ms) (d_obj cx OS) 24 ltac:(intros a Ha; apply HFpres4; unfold d_obj in Ha; cbn in Ha; lia))
  as (OB & LOB & HOB).
destruct (cl_top cx ly3 S3 W (ms_mem ms) md4 k HC4) as (Htop & Hslo).
pose proof Hobjs4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HGour & _).
assert (Es0 : s0Z (ms_regs ms) = d_S cx) by (unfold s0Z; rewrite H84; unfold w64; apply unsigned_lit_small; unfold LLVMF_STK in *; lia).
assert (HFB8 : d_FB cx mod 4 = 0) by (rewrite <- (Z.mod_mod (d_FB cx) 32) in HFal by lia; lia).
rewrite Hms.
eapply SRr_bind.
{ apply (TCLS fq LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(DFRAME_CLASS, c_fpos cx)]
    ly3 S3 W (ms_mem ms) md4 k (ms_regs ms) ch fr len (d_obj cx OOUR) (d_obj cx OS)
    (slot_classify.fb50 (firstn (Z.to_nat len) (rest_of (c_pl cx) nb))) (our_of (c_pl cx)) OB HJ Himg4).
  - rewrite R1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite R1. unfold w64. pose proof (@pa_B_ok _ _ PI) as (HB0 & HB1 & _).
    rewrite unsigned_lit_small by lia. pose proof (pa_base_lo (PI := PI)). unfold IMG_LO in *. lia.
  - exact Hgp4.
  - exact Htp4.
  - exact A10.
  - exact A11.
  - exact A12.
  - exact A13.
  - rewrite Hsp4, Es0. exact Hch.
  - rewrite Hsp4. lia.
  - rewrite Hsp4. unfold CLS_STK, CLS_OWN_BCMP, CLS_VIA_PARSE, CLS_FRAME, CLS_PARSE_NEED, ESTACK, MFRAME, LLVMF_STK in *. lia.
  - rewrite Hsp4. unfold MFRAME in HA1. lia.
  - rewrite Hsp4. unfold MFRAME in HA1. lia.
  - rewrite Hfrs. cbn. unfold CLS_DEPTH. lia.
  - pose proof Hfrm4 as (F1 & _). unfold REC_MAX in F1. lia.
  - apply slot_classify.fb50_len.
  - apply length_our.
  - exact LOB.
  - intros H50. destruct (cl_fblk cx h n dsh_rec nb fr len ly3 S3 W (ms_mem ms) md4 k HC4 Hbody4 Hfrm4 Hnbn Hlen H50)
      as (Hf0 & Hfr & Hfs & Hfg & _). rewrite Hsp4. exact (conj Hf0 (conj Hfr (conj Hfs Hfg))).
  - rewrite Hsp4. exact (cl_cread_obj cx ly3 S3 W (ms_mem ms) md4 k OOUR (d_A cx) HC4 Hshadow4 ltac:(vm_compute; reflexivity)
      ltac:(unfold CLS_STK, CLS_OWN_BCMP, CLS_VIA_PARSE, CLS_FRAME, CLS_PARSE_NEED, ESTACK, MFRAME, LLVMF_STK in *; lia)).
  - left. exists DFRAME_CLASS, (c_fpos cx). split; [exact Hfin|]. rewrite Efa, fs6. unfold d_obj. cbn [dobj_off]. lia.
  - exact HGour.
  - unfold d_obj. cbn [dobj_off]. lia.
  - unfold d_obj. cbn [dobj_off]. rewrite Z.add_mod by lia. rewrite HFB8. reflexivity.
  - rewrite Hsp4. exact (cl_cread_obj cx ly3 S3 W (ms_mem ms) md4 k OS (d_A cx) HC4 Hshadow4 ltac:(vm_compute; reflexivity)
      ltac:(unfold CLS_STK, CLS_OWN_BCMP, CLS_VIA_PARSE, CLS_FRAME, CLS_PARSE_NEED, ESTACK, MFRAME, LLVMF_STK in *; lia)).
  - exact HOB.
  - intros a Ha. apply (proj1 (Hawr4 a ltac:(unfold d_obj in Ha; cbn [dobj_off] in Ha; unfold DFRAME_SIZE; lia))).
  - left. pose proof Hgeo4 as (_ & G2 & _). rewrite fs6 in G2. unfold d_obj. cbn [dobj_off]. lia.
  - unfold d_obj. cbn [dobj_off]. lia.
  - intros H50. destruct (cl_fblk cx h n dsh_rec nb fr len ly3 S3 W (ms_mem ms) md4 k HC4 Hbody4 Hfrm4 Hnbn Hlen H50)
      as (_ & _ & _ & _ & Hsep & _). pose proof (req_size_pos len ltac:(lia)). unfold d_obj. cbn [dobj_off]. lia. }
intros W2 c2 _ Hpost. apply SRr_ret.
exact (cl_cls_ret cx h i n now op nb fr len fq ly3 S3 W (ms_regs ms) (ms_mem ms) md4 k acc 0xce4 0 None OB W2 c2
  Hfq Hbase HJ Hfrs Hk Hacc HB4 HR4 R1 Hsp4 (or_introl (conj eq_refl eq_refl)) Hpost).
Qed.

Lemma cl_w64_add : forall a b, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 a) + b) = Z_to_bv 64 (a + b).
Proof.
intros a b. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
rewrite Z.add_mod_idemp_l by (unfold bv_modulus; cbn; lia). reflexivity.
Qed.

Lemma cl_s2 : forall cx h i n now op nb fr len W c,
  cls_in B MT XM_LIB RLO RHI tfib_K cx h i n now op nb fr len W c -> op mod 4 = 1 -> nb <= c_n cx ->
  SRr SEGS W c (cl_R cx h i n now op nb fr len 0xd00).
Proof.
intros cx h i n now op nb fr len W c Hin Hop0 Hnbn.
unfold cls_in, d_arm_at_pf in Hin. rewrite Hop0 in Hin. cbn [Z.eqb] in Hin.
destruct Hin as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hfq & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc & HP).
destruct HP as (Hi & Hn & Hnow & HrL & HR & HX & Hsp0 & Hbody).
destruct HX as (Hop & Hop2 & Hfrm & H248 & H408 & H392 & Hlen & Hnb).
assert (HB3 : cl_base cx h i n now op nb fr len regs ly3 S3 W mem3)
  by exact (conj Hi (conj Hn (conj Hnow (conj (or_intror Hop0) (conj Hop2 (conj HrL (conj Hsp0 (conj Hfrm (conj H248 (conj H408
    (conj H392 (conj Hlen (conj Hnb (conj Hnbn Hbody)))))))))))))).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & Hshadow & Hobjs & Hblocks & Hinput & Himg & Hoff & Hgeo & _ & Hstk & Hawr).
pose proof Hframe as (E & HdE & Hregs & Hflag & Hh216 & Hh152).
assert (HctxD : DCTX cx ly3 S3 W mem3 md3 k) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HctxD)
  as (Hal16 & Hlo & Hhi & HF0 & HFc & HFia & HFo & HFal & HFpres & HSpres & HWpres & HAR & Hfin & Efa & Efl).
pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HAr2 : 0 <= d_A cx < 2 ^ 64) by (unfold MFRAME, LLVMF_STK in *; lia).
pose proof (d_seat B MT XM_LIB RLO RHI tfib_K LAWS TL fq cx dsh_rec ly3 S3 W regs mem3 md3 k E CLSS_OFF cl_sr
  (cl_vals regs []) [] [] [] (d_facts [] [])
  HctxD HdE Hregs Hflag (cl_regs_ok cx E regs [] HdE HrL HAr2)
  (d_facts_ok B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k E (cl_vals regs []) [] [] HctxD HdE I I)
  (Forall_nil _) (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS.
unfold ss_d in HS.
cl_ro_base HS 516%nat. cl_ro_base HS 529%nat. cl_ro_base HS 60%nat.
assert (HEI : img_env VAL A_LIM (d_env cx E (cl_vals regs []))).
{ destruct HdE as (_ & _ & HI & _). intros a Ha. unfold d_env. rewrite ew_havoc_old by (unfold A_LIM, AT_FL in *; lia). exact (HI a Ha). }
assert (SHOK : sh_ok SEGS (SOff 32 0) [] (d_env cx E (cl_vals regs [])) (rd W mem3)) by constructor.
pose (RUN := paj_run (fx := fq) B LAWS).
unfold cfg_at. change (w64 (BASE + CLSS_OFF)) with (Z_to_bv 64 (BASE + CLSS_OFF)).
paj_run_tok RUN HS HJ SHOK cl_span.
{ cbn [ss_mem]. repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
assert (Hpt := cl_ro_pt _ _ _ _ HF ltac:(vm_compute; reflexivity)).
assert (Hptr := cl_ro_pt _ _ _ _ HFr ltac:(vm_compute; reflexivity)).
clear HF HFr HG.
rewrite (pa_sigma_reac_disco_classify_on_segment (PI := PI)) in HS.
pose proof (cl_regs_ok cx E regs [] HdE HrL HAr2) as HROK.
assert (RG : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
  getr (ms_regs ms) r = getr regs r).
{ intros r Hr. rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms r HS), (HROK r).
  cbv [In] in Hr. repeat (destruct Hr as [<-|Hr]; [f_equal; vm_compute; reflexivity|]). destruct Hr. }
pose proof HR as (R27 & R24 & R23 & R26 & R22).
assert (EF : ew (d_env cx E (cl_vals regs [])) 516 = Z_to_bv 64 (d_FB cx)).
{ unfold d_env. rewrite ew_havoc_old by (cbv; lia). destruct HdE as (_ & _ & _ & _ & HFx & _). exact HFx. }
assert (R1 : getr (ms_regs ms) 1 = w64 (BASE + 0xd00)).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 1%bv HS).
  match goal with |- context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
  unfold w64. exact (codeptr_val _ 3328 HEI). }
assert (A10 : getr (ms_regs ms) 10 = w64 (d_obj cx OLOCK)).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 10%bv HS).
  match goal with |- context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
  cbn [sv_denot]. rewrite EF, cl_w64_add. reflexivity. }
assert (A11 : getr (ms_regs ms) 11 = w64 fr).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 11%bv HS). rewrite <- R27, (HROK 27%bv). f_equal; vm_compute; reflexivity. }
assert (A12 : getr (ms_regs ms) 12 = w64 len).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 12%bv HS). rewrite <- R24, (HROK 24%bv). f_equal; vm_compute; reflexivity. }
assert (A13 : getr (ms_regs ms) 13 = w64 (d_obj cx OOUR)).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 13%bv HS). rewrite <- R26, (HROK 26%bv). f_equal; vm_compute; reflexivity. }
assert (A14 : getr (ms_regs ms) 14 = w64 (d_obj cx OS)).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 14%bv HS). rewrite <- R22, (HROK 22%bv). f_equal; vm_compute; reflexivity. }
pose proof (st_ok_restrict_mkst SEGS (w_H W) _ _ ms HS eq_refl) as Hms. cbn [ss_pc setpc] in Hms.
set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *.
assert (HC4 : DCTX cx ly3 S3 W (ms_mem ms) md4 k) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
pose proof (cl_base_ro cx h i n now op nb fr len regs (ms_regs ms) ly3 S3 W mem3 (ms_mem ms) md4 k HB3 HC4 Hpt Hptr
  ltac:(intros r Hr; apply RG; cbv [In] in Hr |- *; tauto)) as HB4.
assert (HR4 : dR_cls cx nb fr len (ms_regs ms)).
{ unfold dR_cls. rewrite !RG by (cbv; tauto). exact HR. }
pose proof HB4 as (_ & _ & _ & _ & _ & HrL4 & _ & Hfrm4 & _ & _ & _ & _ & _ & _ & Hbody4).
pose proof HrL4 as (Hsp4 & Hgp4 & Htp4 & H84 & _).
pose proof Hbody4 as (T4 & G4 & Lk4 & H4 & Hframe4 & Hshadow4 & Hobjs4 & Hblocks4 & Hinput4 & Himg4 & Hoff4 & Hgeo4 & _ & Hstk4 & Hawr4).
pose proof Hframe4 as (E4 & HdE4 & Hregs4 & _).
pose proof Hobjs4 as (_ & _ & _ & _ & _ & _ & LLk & GLk & QLk & HGour & _).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W (ms_mem ms) md4 k HC4)
  as (_ & _ & _ & _ & _ & _ & _ & _ & HFpres4 & _ & _ & HAR4 & _ & _ & _).
destruct (cl_achain cx ly3 S3 W (ms_mem ms) md4 k E4 (d_A cx) HC4 HdE4 (Forall_inv Hregs4)
  ltac:(unfold MFRAME in HA1; lia)) as (ch & Hch).
destruct (cl_garr8_ex (w_H W) (ms_mem ms) (d_obj cx OS) 24 ltac:(intros a Ha; apply HFpres4; unfold d_obj in Ha; cbn in Ha; lia))
  as (OB & LOB & HOB).
destruct (cl_top cx ly3 S3 W (ms_mem ms) md4 k HC4) as (Htop & Hslo).
assert (Es0 : s0Z (ms_regs ms) = d_S cx) by (unfold s0Z; rewrite H84; unfold w64; apply unsigned_lit_small; unfold LLVMF_STK in *; lia).
assert (HFB8 : d_FB cx mod 4 = 0) by (rewrite <- (Z.mod_mod (d_FB cx) 32) in HFal by lia; lia).
pose proof Hgeo4 as (_ & G2 & _). rewrite fs6 in G2.
rewrite Hms.
eapply SRr_bind.
{ apply (TCLSS fq LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(DFRAME_CLASS, c_fpos cx)]
    ly3 S3 W (ms_mem ms) md4 k (ms_regs ms) ch (d_obj cx OLOCK) fr len (d_obj cx OOUR) (d_obj cx OS)
    (slot_classify.fb50 (firstn (Z.to_nat len) (rest_of (c_pl cx) nb))) (our_of (c_pl cx)) OB (Some Lk4) HJ Himg4).
  - rewrite R1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite R1. unfold w64. pose proof (@pa_B_ok _ _ PI) as (HB0 & HB1 & _).
    rewrite unsigned_lit_small by lia. pose proof (pa_base_lo (PI := PI)). unfold IMG_LO in *. lia.
  - exact Hgp4.
  - exact Htp4.
  - exact A10.
  - exact A11.
  - exact A12.
  - exact A13.
  - exact A14.
  - rewrite Hsp4, Es0. exact Hch.
  - rewrite Hsp4. lia.
  - rewrite Hsp4. unfold CLS_STK, CLS_OWN_BCMP, CLS_VIA_PARSE, CLS_FRAME, CLS_PARSE_NEED, ESTACK, MFRAME, LLVMF_STK in *. lia.
  - rewrite Hsp4. unfold MFRAME in HA1. lia.
  - rewrite Hsp4. unfold MFRAME in HA1. lia.
  - rewrite Hfrs. cbn. unfold CLS_DEPTH. lia.
  - pose proof Hfrm4 as (F1 & _). unfold REC_MAX in F1. lia.
  - apply slot_classify.fb50_len.
  - apply length_our.
  - exact LOB.
  - intros H50. destruct (cl_fblk cx h n dsh_rec nb fr len ly3 S3 W (ms_mem ms) md4 k HC4 Hbody4 Hfrm4 Hnbn Hlen H50)
      as (Hf0 & Hfr & Hfs & Hfg & _). rewrite Hsp4. exact (conj Hf0 (conj Hfr (conj Hfs Hfg))).
  - rewrite Hsp4. exact (cl_cread_obj cx ly3 S3 W (ms_mem ms) md4 k OOUR (d_A cx) HC4 Hshadow4 ltac:(vm_compute; reflexivity)
      ltac:(unfold CLS_STK, CLS_OWN_BCMP, CLS_VIA_PARSE, CLS_FRAME, CLS_PARSE_NEED, ESTACK, MFRAME, LLVMF_STK in *; lia)).
  - left. exists DFRAME_CLASS, (c_fpos cx). split; [exact Hfin|]. rewrite Efa, fs6. unfold d_obj. cbn [dobj_off]. lia.
  - exact HGour.
  - unfold d_obj. cbn [dobj_off]. lia.
  - unfold d_obj. cbn [dobj_off]. rewrite Z.add_mod by lia. rewrite HFB8. reflexivity.
  - rewrite Hsp4. exact (cl_cread_obj cx ly3 S3 W (ms_mem ms) md4 k OS (d_A cx) HC4 Hshadow4 ltac:(vm_compute; reflexivity)
      ltac:(unfold CLS_STK, CLS_OWN_BCMP, CLS_VIA_PARSE, CLS_FRAME, CLS_PARSE_NEED, ESTACK, MFRAME, LLVMF_STK in *; lia)).
  - exact HOB.
  - intros a Ha. apply (proj1 (Hawr4 a ltac:(unfold d_obj in Ha; cbn [dobj_off] in Ha; unfold DFRAME_SIZE; lia))).
  - unfold d_obj. cbn [dobj_off]. left. lia.
  - split; [unfold d_obj; cbn [dobj_off]; lia|].
    split; [unfold d_obj; cbn [dobj_off]; rewrite Z.add_mod by lia; rewrite HFB8; reflexivity|].
    split; [exact LLk|].
    split; [rewrite Hsp4; exact (cl_cread_obj cx ly3 S3 W (ms_mem ms) md4 k OLOCK (d_A cx) HC4 Hshadow4 ltac:(vm_compute; reflexivity)
      ltac:(unfold CLS_STK, CLS_OWN_BCMP, CLS_VIA_PARSE, CLS_FRAME, CLS_PARSE_NEED, ESTACK, MFRAME, LLVMF_STK in *; lia))|].
    split; [exact GLk|].
    split; [intros a Ha; apply (proj1 (Hawr4 a ltac:(unfold d_obj in Ha; cbn [dobj_off] in Ha; unfold DFRAME_SIZE; lia)))|].
    unfold d_obj. cbn [dobj_off]. left. lia.
  - unfold d_obj. cbn [dobj_off]. lia.
  - intros H50. destruct (cl_fblk cx h n dsh_rec nb fr len ly3 S3 W (ms_mem ms) md4 k HC4 Hbody4 Hfrm4 Hnbn Hlen H50)
      as (_ & _ & _ & _ & Hsep & _). pose proof (req_size_pos len ltac:(lia)). unfold d_obj. cbn [dobj_off]. lia.
  - split; [unfold d_obj; cbn [dobj_off]; lia|].
    split; [unfold d_obj; cbn [dobj_off]; lia|].
    intros H50. destruct (cl_fblk cx h n dsh_rec nb fr len ly3 S3 W (ms_mem ms) md4 k HC4 Hbody4 Hfrm4 Hnbn Hlen H50)
      as (_ & _ & _ & _ & Hsep & _). pose proof (req_size_pos len ltac:(lia)). unfold d_obj. cbn [dobj_off]. lia. }
intros W2 c2 _ Hpost. apply SRr_ret.
exact (cl_cls_ret cx h i n now op nb fr len fq ly3 S3 W (ms_regs ms) (ms_mem ms) md4 k acc 0xd00 (d_obj cx OLOCK)
  (Some Lk4) OB W2 c2 Hfq Hbase HJ Hfrs Hk Hacc HB4 HR4 R1 Hsp4
  (or_intror (ex_intro _ Lk4 (conj eq_refl (conj eq_refl QLk)))) Hpost).
Qed.

Lemma cl_s3 : forall cx h i n now op nb fr len W c,
  cl_R cx h i n now op nb fr len 0xce4 W c -> SRr SEGS W c (cl_R cx h i n now op nb fr len 0xd00).
Proof.
intros cx h i n now op nb fr len W c Hin.
destruct Hin as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hfq & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
  r & HB3 & HR & Hr10 & Hrr).
pose proof HB3 as (Hi & Hn & Hnow & Hop & Hop2 & HrL & Hsp0 & Hfrm & H248 & H408 & H392 & Hlen & Hnb & Hnbn & Hbody).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & Hshadow & Hobjs & Hblocks & Hinput & Himg & Hoff & Hgeo & _ & Hstk & Hawr).
pose proof Hframe as (E & HdE & Hregs & Hflag & Hh216 & Hh152).
assert (HctxD : DCTX cx ly3 S3 W mem3 md3 k) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HctxD)
  as (Hal16 & Hlo & Hhi & HF0 & HFc & HFia & HFo & HFal & HFpres & HSpres & HWpres & HAR & Hfin & Efa & Efl).
pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HAr2 : 0 <= d_A cx < 2 ^ 64) by (unfold MFRAME, LLVMF_STK in *; lia).
pose proof (d_seat B MT XM_LIB RLO RHI tfib_K LAWS TL fq cx dsh_rec ly3 S3 W regs mem3 md3 k E 0xce4 cl_sr
  (cl_vals regs []) [] [] [] (d_facts [] [])
  HctxD HdE Hregs Hflag (cl_regs_ok cx E regs [] HdE HrL HAr2)
  (d_facts_ok B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k E (cl_vals regs []) [] [] HctxD HdE I I)
  (Forall_nil _) (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS.
unfold ss_d in HS.
cl_ro_base HS 516%nat. cl_ro_base HS 529%nat. cl_ro_base HS 60%nat.
assert (HEI : img_env VAL A_LIM (d_env cx E (cl_vals regs []))).
{ destruct HdE as (_ & _ & HI & _). intros a Ha. unfold d_env. rewrite ew_havoc_old by (unfold A_LIM, AT_FL in *; lia). exact (HI a Ha). }
assert (SHOK : sh_ok SEGS (SOff 32 0) [] (d_env cx E (cl_vals regs [])) (rd W mem3)) by constructor.
pose (RUNTO := paj_run_to (fx := fq) B LAWS).
unfold cfg_at. change (w64 (BASE + 0xce4)) with (Z_to_bv 64 (BASE + 0xce4)).
paj_run_to_tok RUNTO HS HJ SHOK cl_span 0xd00.
{ cbn [ss_mem]. repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
assert (Hpt := cl_ro_pt _ _ _ _ HF ltac:(vm_compute; reflexivity)).
assert (Hptr := cl_ro_pt _ _ _ _ HFr ltac:(vm_compute; reflexivity)).
clear HF HFr HG.
pose proof (cl_regs_ok cx E regs [] HdE HrL HAr2) as HROK.
assert (RG : forall r0 : bv 5, In r0 [2; 3; 4; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
  getr (ms_regs ms) r0 = getr regs r0).
{ intros r0 Hr0. rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms r0 HS), (HROK r0).
  cbv [In] in Hr0. repeat (destruct Hr0 as [<-|Hr0]; [f_equal; vm_compute; reflexivity|]). destruct Hr0. }
pose proof (st_ok_restrict_mkst SEGS (w_H W) _ _ ms HS eq_refl) as Hms. cbn [ss_pc setpc] in Hms.
set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *.
assert (HC4 : DCTX cx ly3 S3 W (ms_mem ms) md4 k) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
pose proof (cl_base_ro cx h i n now op nb fr len regs (ms_regs ms) ly3 S3 W mem3 (ms_mem ms) md4 k HB3 HC4 Hpt Hptr
  ltac:(intros r0 Hr0; apply RG; cbv [In] in Hr0 |- *; tauto)) as HB4.
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev2 & _).
apply SRr_ret. rewrite Hms. unfold cl_R, d_at.
exists fq, ly3, S3, (ms_regs ms), (ms_mem ms), md4, k, acc.
split; [reflexivity|]. split; [exact Hfq|]. split; [exact Hbase|]. split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|].
split; [exact Hnev|]. split; [rewrite MT_TRIV; exact I|]. split; [exact Hacc|].
exists r. split; [exact HB4|].
split; [unfold dR_cls; rewrite !RG by (cbv; tauto); exact HR|].
split; [rewrite RG by (cbv; tauto); exact Hr10|].
destruct Hrr as [E1 | (E0 & Sg & HSg)]; [left; exact E1|].
right. split; [exact E0|]. exists Sg. pose proof HSg as (LSg & GSg & HSf).
split; [exact LSg|]. split; [|exact HSf].
eapply YC88.garr8_aview_kept; [|exact GSg]. intros a _. apply aview_eq_of. apply Hptr.
Qed.

Theorem cl_L1 : cl_L1_stmt B MT XM_LIB RLO RHI tfib_K.
Proof. exact cl_s1. Qed.

Theorem cl_L2 : cl_L2_stmt B MT XM_LIB RLO RHI tfib_K.
Proof. exact cl_s2. Qed.

Theorem cl_L3 : cl_L3_stmt B MT XM_LIB RLO RHI tfib_K.
Proof. exact cl_s3. Qed.

Lemma cl_cur_rng : forall cx nb, d_base B MT XM_LIB RLO RHI tfib_K cx -> 0 <= nb -> nb <= c_n cx ->
  0 <= d_cur cx nb < 2 ^ 64.
Proof.
intros cx nb Hbase Hnb0 Hnbn. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_val as Hac. pose proof alloc_ceiling_lt as Hlt.
destruct Hbase as (HPRE & _).
unfold tfib_lib_pre_x in HPRE.
destruct HPRE as (Hafn & _ & _ & _ & Hdisj & _).
pose proof Hafn as (HAR0 & _).
unfold d_cur.
destruct Hdisj as [(Hn0 & Hpe) | (Hnpos & Hin)].
- rewrite Hn0 in *. assert (nb = 0) by lia. subst nb. rewrite Hpe. unfold A_EMPTY. lia.
- destruct (al_blocks SEGS B LAWS (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) (c_p cx) (c_n cx) HAR0 Hin)
    as (_ & Hp0 & Hpc & _).
  pose proof (req_size_pos (c_n cx) ltac:(lia)) as (_ & Hrq). lia.
Qed.

Lemma cl_base_keep : forall cx h i n now op nb fr len regs regs2 ly3 S3 (W : world SEGS) mem3 md3 k3 ly4 S4 (W2 : world SEGS) mem2 md2 k2 STKc,
  cl_base cx h i n now op nb fr len regs ly3 S3 W mem3 -> DCTX cx ly3 S3 W mem3 md3 k3 -> DCTX cx ly4 S4 W2 mem2 md2 k2 ->
  0 <= STKc -> STKc + 592 <= LLVMF_STK ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx - STKc <= a < d_A cx) -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem3 a) ->
  Permutation (ablocks B ly4 S4) (ablocks B ly3 S3) ->
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 20; 25]%bv -> getr regs2 r = getr regs r) ->
  cl_base cx h i n now op nb fr len regs2 ly4 S4 W2 mem2.
Proof.
intros cx h i n now op nb fr len regs regs2 ly3 S3 W mem3 md3 k3 ly4 S4 W2 mem2 md2 k2 STKc HB HC3 HC2 HS0 HS1 Hav Hperm RG.
pose proof HB as (Hi & Hn & Hnow & Hop & Hop2 & HrL & Hsp0 & Hfrm & H248 & H408 & H392 & Hlen & Hnb & Hnbn & Hbody).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & Hshadow & Hobjs & Hblocks & Hinput & Himg & Hoff & Hgeo & _ & Hstk & Hawr).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k3 HC3)
  as (Hal16 & Hlo & Hhi & HF0 & HFc & HFia & HFo & HFal & HFpres & HSpres & HWpres & HAR & Hfin & Efa & Efl).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2). unfold MFRAME in HA1.
pose proof alloc_ceiling_val as Hac. pose proof alloc_ceiling_lt as Hlt.
assert (HFlt : d_FB cx + 4096 <= d_A cx - STKc) by (unfold LLVMF_STK in *; lia).
assert (HSHlt : shadow_addr (d_FB cx) + 384 < d_A cx - STKc).
{ unfold shadow_addr, SHADOW_OFF.
  pose proof (Z.div_mod (d_FB cx) 8 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound (d_FB cx) 8 ltac:(lia)) as Hmp.
  unfold LLVMF_STK in *. lia. }
assert (VM : forall o v, 0 <= o -> o + 8 <= 472 -> val_mem SEGS (rd W mem3) (d_A cx + o) 8 v ->
  val_mem SEGS (rd W2 mem2) (d_A cx + o) 8 v).
{ intros o v Ho1 Ho2 Hv. eapply YC88.val_mem_aview_kept_x; [|exact Hv]. intros x Hx. change (Z.of_nat 8) with 8 in Hx.
  apply Hav; [unfold LLVMF_STK in *; lia | lia]. }
assert (Hfrng : forall a, (d_S cx - 104 <= a < d_S cx) \/ (d_A cx <= a < d_A cx + 472) \/ (d_FB cx <= a < d_FB cx + 24) \/
  (d_FB cx + 4088 <= a < d_FB cx + 4096) \/ (shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 384) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem3 a).
{ intros a Ha. pose proof (shadow_addr_bounds (d_FB cx) ltac:(unfold kHighMemEnd in *; lia)) as HSHb.
  apply Hav; destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]]; unfold kLowMemEnd, kHighShadowEnd, LLVMF_STK in *; lia. }
assert (Hframe2 : d_frame cx h dsh_rec W2 mem2)
  by exact (cl_frame_keep cx h dsh_rec W mem3 ly4 S4 W2 mem2 md2 k2 HC2 Hframe Hfrng).
assert (Hshadow2 : d_shadow cx dsh_rec W2 mem2)
  by exact (cl_shadow_keep cx dsh_rec W W2 mem3 mem2 Hshadow (fun a Ha => Hfrng a (or_intror (or_intror (or_intror (or_intror Ha)))))).
split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|]. split; [exact Hop|]. split; [exact Hop2|].
split.
{ destruct HrL as (Hsp & Hgp & Htp & H8 & H9 & H18 & H20 & H25). unfold d_rL, spZ in *.
  rewrite !RG by (cbv; tauto). repeat split; assumption. }
split; [destruct Hsp0 as (S1 & S2); split; apply VM; first [lia | assumption]|].
split.
{ destruct Hfrm as (F1 & F2 & Fnb & F3). split; [exact F1|]. split; [exact F2|]; split; [exact Fnb|].
  eapply YC88.garr8_aview_kept; [|exact F3]. intros a Ha. rewrite length_map in Ha.
  destruct (Z.eq_dec fr 0) as [E0 | Hne].
  - subst fr. rewrite (F2 eq_refl) in Ha. change (Z.to_nat 0) with 0%nat in Ha. rewrite firstn_O in Ha. cbn [length] in Ha. lia.
  - pose proof Hblocks as (Hp & _).
    assert (Hin : In (fr, len) (ablocks B ly3 S3)).
    { eapply Permutation_in; [apply Permutation_sym; exact Hp|]. unfold dxb.
      replace (fr =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hne). apply in_or_app; left; left; reflexivity. }
    destruct (al_blocks SEGS B LAWS ly3 S3 W mem3 md3 fr len HAR Hin) as (_ & Hfr0 & Hfrc & _).
    pose proof (req_size_pos len ltac:(lia)) as (_ & Hrq).
    assert (Hll : Z.of_nat (length (firstn (Z.to_nat len) (rest_of (c_pl cx) nb))) <= len) by (rewrite length_firstn; lia).
    apply Hav; unfold LLVMF_STK in *; lia. }
split; [apply VM; [lia | lia | exact H248]|]. split; [apply VM; [lia | lia | exact H408]|]. split; [apply VM; [lia | lia | exact H392]|].
split; [exact Hlen|]. split; [exact Hnb|]. split; [exact Hnbn|].
apply (d_body_call_keep B MT XM_LIB RLO RHI tfib_K LAWS cx h n (dxb fr len) dsh_rec dsh_rec ly3 S3 W mem3
  ly4 S4 W2 mem2 md2 k2 (d_A cx - STKc) (d_A cx) Hbody (conj (proj1 HC2) (proj1 (proj2 HC2)))
  ltac:(unfold LLVMF_STK in *; lia) ltac:(lia) Hav Hperm Hframe2 Hshadow2).
Qed.

Ltac cl_ne8 := let X := fresh in intros X; apply (f_equal bv_unsigned) in X; discriminate X.

Lemma cl_cs8 : forall (r3 r2 : bvmap 5 word), aregs_preserved r3 r2 ->
  forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 20; 25]%bv -> getr r2 r = getr r3 r.
Proof.
intros r3 r2 HP r Hr. cbv [In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]].
- exact (cl_cs r3 r2 2 _ HP ltac:(unfold acallee_saved; lia) eq_refl).
- exact (cl_cs r3 r2 3 _ HP ltac:(unfold acallee_saved; lia) eq_refl).
- exact (cl_cs r3 r2 4 _ HP ltac:(unfold acallee_saved; lia) eq_refl).
- exact (cl_cs r3 r2 8 _ HP ltac:(unfold acallee_saved; lia) eq_refl).
- exact (cl_cs r3 r2 9 _ HP ltac:(unfold acallee_saved; lia) eq_refl).
- exact (cl_cs r3 r2 18 _ HP ltac:(unfold acallee_saved; lia) eq_refl).
- exact (cl_cs r3 r2 20 _ HP ltac:(unfold acallee_saved; lia) eq_refl).
- exact (cl_cs r3 r2 25 _ HP ltac:(unfold acallee_saved; lia) eq_refl).
Qed.

Lemma cl_pre8 : forall cx regs ly3 S3 (W : world SEGS) mem3 md3 k STK ret,
  DCTX cx ly3 S3 W mem3 md3 k -> d_rL B cx regs -> getr regs 1 = w64 (BASE + ret) ->
  0 <= ret < 2 ^ 40 -> ret mod 2 = 0 -> 0 <= STK -> STK + 640 <= LLVMF_STK ->
  afn_pre SEGS B STK ly3 S3 W (regupd regs 8 (Z_to_bv 64 0)) mem3 md3 [].
Proof.
intros cx regs ly3 S3 W mem3 md3 k STK ret Hc HrL Hra Hr0 Hr2 HS0 HS1.
pose proof Hc as (_ & HJ & _).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k Hc) as (HS16 & HSlo & HShi & _).
pose proof alloc_ceiling_val as Hac0. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HAr & HA32). unfold MFRAME in HAr.
pose proof pa_base_lo as HBlo. pose proof pa_B_ok as HB. pose proof alloc_ceiling_val as Hac.
pose proof HrL as (Hsp & Hgp & Htp & _).
set (regs8 := regupd regs 8 (Z_to_bv 64 0)).
assert (G8 : forall r : bv 5, r <> 8%bv -> getr regs8 r = getr regs r).
{ intros r Hr. unfold regs8, getr. destruct (bv_eqb r 0); [reflexivity|]. exact (regupd_other regs 8 _ r Hr). }
assert (G88 : getr regs8 8%bv = Z_to_bv 64 0) by (unfold regs8, getr; rewrite regupd_same; destruct (bv_eqb _ _); reflexivity).
assert (Hsp8 : spZ regs8 = d_A cx) by (unfold spZ; rewrite G8 by cl_ne8; exact Hsp).
apply (afn_pre_at SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(DFRAME_CLASS, c_fpos cx)]
  ly3 S3 W mem3 md3 k regs8 STK (d_A cx - d_S cx) [] HJ).
- rewrite Hsp8. lia.
- lia.
- lia.
- exact HS0.
- unfold LLVMF_STK in *. lia.
- rewrite G8 by cl_ne8. rewrite Hra. unfold w64. apply ret_ok_codeptr_v; assumption.
- unfold raZ. rewrite G8 by cl_ne8. rewrite Hra. unfold w64. rewrite unsigned_lit_small by lia. unfold IMG_LO in HBlo. lia.
- rewrite G8 by cl_ne8. exact Hgp.
- rewrite G8 by cl_ne8. exact Htp.
- unfold s0Z. rewrite G88, unsigned_lit_small by lia. apply achain_low. lia.
Qed.

Lemma cl_postj : forall cx ly3 S3 (W : world SEGS) mem3 md3 k STK ly4 S4 W2 mem4 md4,
  DCTX cx ly3 S3 W mem3 md3 k -> 0 <= STK -> STK + 640 <= LLVMF_STK ->
  ajournal SEGS B STK (d_A cx) [] ly3 S3 W mem3 md3 [] ly4 S4 W2 mem4 md4 0 ->
  DCTX cx ly4 S4 W2 mem4 md4 (k + 0).
Proof.
intros cx ly3 S3 W mem3 md3 k STK ly4 S4 W2 mem4 md4 Hc HS0 HS1 HJ1.
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k Hc) as (HS16 & HSlo & HShi & _).
pose proof alloc_ceiling_val as Hac0. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HAr & HA32). unfold MFRAME in HAr.
destruct Hc as (Hbase & HJ & Hfrs).
split; [exact Hbase|]. split.
- change [(DFRAME_CLASS, c_fpos cx)] with ([] ++ [(DFRAME_CLASS, c_fpos cx)]).
  eapply (ajournal_sub_tok SEGS B LAWS pa_segs_low); [exact HJ | exact HJ1 | unfold LLVMF_STK in *; lia | lia |
    intros a (rg & [] & _)].
- pose proof HJ1 as (_ & _ & _ & _ & _ & Hf1 & _). rewrite Hf1, Hfrs. reflexivity.
Qed.

Lemma cl_dat : forall cx pc kmax accmax
  (P : bvmap 5 word -> alayout -> astate -> world SEGS -> (word -> option byte) -> Model -> Prop)
  (fq : YK11.FPState) ly4 S4 regs4 mem4 md4 k acc (W2 : world SEGS),
  lib.Lib.FP.frm0 (@YK11.fp_csr fq) -> DCTX cx ly4 S4 W2 mem4 md4 k -> 0 <= k <= kmax -> acc <= accmax ->
  P regs4 ly4 S4 W2 mem4 md4 ->
  DAT cx pc kmax accmax P W2 (cfg_at (fx := fq) SEGS (BASE + pc) regs4 mem4 md4).
Proof.
intros cx pc kmax accmax P fq ly4 S4 regs4 mem4 md4 k acc W2 Hfq (Hbase & HJ & Hfrs) Hk Hacc HP.
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _).
unfold d_at. exists fq, ly4, S4, regs4, mem4, md4, k, acc.
split; [reflexivity|]. split; [exact Hfq|]. split; [exact Hbase|]. split; [exact HJ|]. split; [exact Hfrs|]. split; [lia|]. split; [lia|].
split; [rewrite MT_TRIV; exact I|]. split; [exact Hacc|]. exact HP.
Qed.

Lemma cl_breqval : forall (Ed : env) (r M : Z), ew Ed 541%nat = w64 r ->
  branch_taken BC_EQ (sv_denot Ed (SOff 541 0)) (sv_denot Ed (SLit M)) = bv_eqb (Z_to_bv 64 r) (Z_to_bv 64 M).
Proof.
intros Ed r M Hr. cbn [branch_taken sv_denot]. rewrite Hr. unfold w64.
rewrite cl_w64_add, Z.add_0_r. reflexivity.
Qed.

Lemma cl_s4 : forall cx h i n now op nb fr len W c,
  cl_R cx h i n now op nb fr len 0xd00 W c ->
  SRr SEGS W c (fun W' c' => r27_in B MT XM_LIB RLO RHI tfib_K cx h i (nb - len) now nb fr len W' c' \/
    cl_CSR cx h i n now op nb fr len W' c').
Proof.
intros cx h i n now op nb fr len W c Hin.
destruct Hin as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hfq & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
  r & HB3 & HR & Hr10 & Hrr).
pose proof HB3 as (Hi & Hn & Hnow & Hop & Hop2 & HrL & Hsp0 & Hfrm & H248 & H408 & H392 & Hlen & Hnb & Hnbn & Hbody).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & Hshadow & Hobjs & Hblocks & Hinput & Himg & Hoff & Hgeo & _ & Hstk & Hawr).
pose proof Hframe as (E & HdE & Hregs & Hflag & Hh216 & Hh152).
assert (HctxD : DCTX cx ly3 S3 W mem3 md3 k) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HctxD)
  as (Hal16 & Hlo & Hhi & HF0 & HFc & HFia & HFo & HFal & HFpres & HSpres & HWpres & HAR & Hfin & Efa & Efl).
pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HAr2 : 0 <= d_A cx < 2 ^ 64) by (unfold MFRAME, LLVMF_STK in *; lia).
assert (Hcur : 0 <= d_cur cx nb < 2 ^ 64) by (apply cl_cur_rng; [exact Hbase | pose proof Hfrm as (Q1 & _); lia | exact Hnbn]).
assert (HACS : Forall (YP09.chunk_ok SEGS (d_env cx E (cl_vals regs [w64 (d_cur cx nb)])) (rd W mem3) (d_A cx))
  [YP09.mkChunk 248 (CVal 8 (SOff (AT_X + 32) 0))]).
{ apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS (d_env cx E (cl_vals regs [w64 (d_cur cx nb)])) (rd W mem3) (d_A cx) 248 8 (SOff (AT_X + 32) 0) (d_cur cx nb)).
  - cbn [sv_denot]. rewrite Z.add_0_r.
    replace (AT_X + 32)%nat with (AT_X + length (map (fun r0 => getr regs (Z_to_bv 5 (Z.of_nat r0))) (seq 0 32)))%nat
      by (rewrite length_map, length_seq; reflexivity).
    unfold cl_vals. rewrite (d_env_x cx E (map (fun r0 => getr regs (Z_to_bv 5 (Z.of_nat r0))) (seq 0 32) ++ [w64 (d_cur cx nb)])
      (length (map (fun r0 => getr regs (Z_to_bv 5 (Z.of_nat r0))) (seq 0 32)))
      ltac:(rewrite length_app; cbn [length]; lia)).
    rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth]. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact Hcur.
  - lia.
  - exact H248. }
pose proof (d_seat B MT XM_LIB RLO RHI tfib_K LAWS TL fq cx dsh_rec ly3 S3 W regs mem3 md3 k E 0xd00 cl_sr
  (cl_vals regs [w64 (d_cur cx nb)]) [YP09.mkChunk 248 (CVal 8 (SOff (AT_X + 32) 0))] [] [] (d_facts [] [])
  HctxD HdE Hregs Hflag (cl_regs_ok cx E regs [w64 (d_cur cx nb)] HdE HrL HAr2)
  (d_facts_ok B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k E (cl_vals regs [w64 (d_cur cx nb)]) [] [] HctxD HdE I I)
  HACS (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS.
unfold ss_d in HS.
cl_ro_base HS 516%nat. cl_ro_base HS 529%nat. cl_ro_base HS 60%nat.
assert (HEI : img_env VAL A_LIM (d_env cx E (cl_vals regs [w64 (d_cur cx nb)]))).
{ destruct HdE as (_ & _ & HI & _). intros a Ha. unfold d_env. rewrite ew_havoc_old by (unfold A_LIM, AT_FL in *; lia). exact (HI a Ha). }
assert (SHOK : sh_ok SEGS (SOff 32 0) [] (d_env cx E (cl_vals regs [w64 (d_cur cx nb)])) (rd W mem3)) by constructor.
assert (E541 : ew (d_env cx E (cl_vals regs [w64 (d_cur cx nb)])) 541 = w64 r).
{ change 541%nat with (AT_X + 10)%nat.
  rewrite (d_env_x cx E (cl_vals regs [w64 (d_cur cx nb)]) 10
    ltac:(unfold cl_vals; rewrite length_app, length_map, length_seq; cbn; lia)).
  unfold cl_vals. cbn [seq map app nth]. rewrite <- Hr10. f_equal. }
assert (E563 : ew (d_env cx E (cl_vals regs [w64 (d_cur cx nb)])) 563 = w64 (d_cur cx nb)).
{ change 563%nat with (AT_X + 32)%nat.
  rewrite (d_env_x cx E (cl_vals regs [w64 (d_cur cx nb)]) 32
    ltac:(unfold cl_vals; rewrite length_app, length_map, length_seq; cbn; lia)).
  unfold cl_vals. rewrite app_nth2 by (rewrite length_map, length_seq; lia).
  rewrite length_map, length_seq. rewrite Nat.sub_diag. reflexivity. }
pose (RUN := paj_run (fx := fq) B LAWS).
pose (RUNTO := paj_run_to (fx := fq) B LAWS).
pose (BR := paj_branch (fx := fq) (PI := PI)).
unfold cfg_at. change (w64 (BASE + 0xd00)) with (Z_to_bv 64 (BASE + 0xd00)).
paj_run_to_tok RUNTO HS HJ SHOK cl_span 0xd08.
{ cbn [ss_mem]. repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
assert (Hpt1 := cl_ro_pt _ _ _ _ HF ltac:(vm_compute; reflexivity)).
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK cl_span.
- rewrite (cl_breqval _ r 18446744073709551615 E541) in Hc.
  destruct Hrr as [Hrm1 | (E0 & Sg & HSg)]; [| subst r; vm_compute in Hc; discriminate Hc]. subst r. clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK cl_span 0x1b48.
  { cbn [ss_mem]. repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
  assert (Hpt2 := cl_ro_pt _ _ _ _ HF ltac:(vm_compute; reflexivity)).
  assert (Hpt : forall x, ms_mem ms0 x = mem3 x) by (intros x; rewrite Hpt2; apply Hpt1).
  assert (Hptr : forall x, rd W (ms_mem ms0) x = rd W mem3 x) by (intros x; unfold mrestrict; rewrite Hpt; reflexivity).
  clear HF HFr HG.
  pose proof (cl_regs_ok cx E regs [w64 (d_cur cx nb)] HdE HrL HAr2) as HROK.
  pose proof HR as (R27r & R24r & R23r & R26r & R22r).
  pose proof (st_ok_restrict_mkst SEGS (w_H W) _ _ ms0 HS eq_refl) as Hms. cbn [ss_pc setpc] in Hms.
  pose proof (conj Hbase (conj HJ Hfrs)) as HC_ms.
  assert (RG : forall r0 : bv 5, In r0 [2; 3; 4; 8; 9; 18; 20; 22; 23; 24; 25; 26; 27]%bv -> getr (ms_regs ms0) r0 = getr regs r0).
  { intros r0 Hr0. rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms0 r0 HS), (HROK r0).
    cbv [In] in Hr0. repeat (destruct Hr0 as [<-|Hr0]; [f_equal; vm_compute; reflexivity|]). destruct Hr0. }
  assert (A14 : getr (ms_regs ms0) 14 = w64 (d_cur cx nb)).
  { rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms0 14%bv HS).
    match goal with |- context [sr_get ?sr ?rr] => let v := eval vm_compute in (sr_get sr rr) in change (sr_get sr rr) with v end.
    cbn [sv_denot]. rewrite E563, cl_w64_add, Z.add_0_r. reflexivity. }
  pose proof (cl_base_ro cx h i n now op nb fr len regs (ms_regs ms0) ly3 S3 W mem3 (ms_mem ms0) _ k HB3 HC_ms Hpt Hptr
    ltac:(intros r0 Hr0; apply RG; cbv [In] in Hr0 |- *; tauto)) as HB_ms.
  pose proof HB_ms as (_ & _ & _ & _ & _ & HrL_ms & Hsp0_ms & Hfrm_ms & _ & _ & _ & _ & _ & _ & Hbody_ms).
  apply SRr_ret. left. rewrite Hms. unfold r27_in, d_arm_at_pf, d_at.
  exists fq, ly3, S3, (ms_regs ms0), (ms_mem ms0). eexists. exists k, acc.
  split; [reflexivity|]. split; [exact Hfq|]. split; [exact Hbase|]. split; [exact HJ|]. split; [exact Hfrs|].
  split; [exact Hk|]. split; [exact Hnev|]. split; [rewrite MT_TRIV; exact I|]. split; [exact Hacc|].
  split; [exact Hi|]. split; [pose proof Hfrm as (Q1 & _); lia|]. split; [exact Hnow|].
  split; [exact HrL_ms|].
  split.
  { split; [exact A14|]. split; [rewrite (RG 24%bv ltac:(cbv; tauto)); exact R24r|].
    split; [rewrite (RG 23%bv ltac:(cbv; tauto)); exact R23r|]. split; [rewrite (RG 27%bv ltac:(cbv; tauto)); exact R27r|].
    split; [rewrite (RG 22%bv ltac:(cbv; tauto)); exact R22r|]. rewrite (RG 26%bv ltac:(cbv; tauto)); exact R26r. }
  split; [split; [exact Hfrm_ms|]; split; [exact Hlen | reflexivity]|].
  split; [exact Hsp0_ms|].
  apply (cl_body_n cx h n (nb - len) (dxb fr len) dsh_rec ly3 S3 W (ms_mem ms0) Hbody_ms).
  pose proof Hfrm as (Q1 & _). lia.
- rewrite (cl_breqval _ r 18446744073709551615 E541) in Hc.
  destruct Hrr as [Hrm1 | (E0 & Sg & HSg)]; [subst r; vm_compute in Hc; discriminate Hc|]. subst r. clear Hc.
  paj_run_tok RUN HS HJ SHOK cl_span.
  { cbn [ss_mem]. repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
  assert (Hpt1b := cl_ro_pt _ _ _ _ HF ltac:(vm_compute; reflexivity)).
  clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK cl_span.
  2: { rewrite (cl_breqval _ 0 0 E541) in Hc. vm_compute in Hc. discriminate Hc. }
  clear Hc.
  paj_run_tok RUN HS HJ SHOK cl_span.
  { cbn [ss_mem]. repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
  assert (Hpt2 := cl_ro_pt _ _ _ _ HF ltac:(vm_compute; reflexivity)).
  assert (Hpt : forall x, ms_mem ms1 x = mem3 x) by (intros x; rewrite Hpt2, Hpt1b; apply Hpt1).
  assert (Hptr : forall x, rd W (ms_mem ms1) x = rd W mem3 x) by (intros x; unfold mrestrict; rewrite Hpt; reflexivity).
  clear HF HFr HG.
  rewrite (pa_sigma_check_sighting (PI := PI)) in HS.
  pose proof (cl_regs_ok cx E regs [w64 (d_cur cx nb)] HdE HrL HAr2) as HROK.
  pose proof HR as (R27r & R24r & R23r & R26r & R22r).
  assert (RG : forall r0 : bv 5, In r0 [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
    getr (ms_regs ms1) r0 = getr regs r0).
  { intros r0 Hr0. rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms1 r0 HS), (HROK r0).
    cbv [In] in Hr0. repeat (destruct Hr0 as [<-|Hr0]; [f_equal; vm_compute; reflexivity|]). destruct Hr0. }
  assert (R1 : getr (ms_regs ms1) 1 = w64 (BASE + 0xd2c)).
  { rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms1 1%bv HS).
    match goal with |- context [sr_get ?sr ?rr] => let v := eval vm_compute in (sr_get sr rr) in change (sr_get sr rr) with v end.
    unfold w64. exact (codeptr_val _ 3372 HEI). }
  assert (A10 : getr (ms_regs ms1) 10 = w64 (d_obj cx OS)).
  { rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms1 10%bv HS). rewrite <- R22r, (HROK 22%bv). f_equal; vm_compute; reflexivity. }
  assert (A11 : getr (ms_regs ms1) 11 = w64 fr).
  { rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms1 11%bv HS). rewrite <- R27r, (HROK 27%bv). f_equal; vm_compute; reflexivity. }
  assert (A12 : getr (ms_regs ms1) 12 = w64 len).
  { rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms1 12%bv HS). rewrite <- R24r, (HROK 24%bv). f_equal; vm_compute; reflexivity. }
  assert (A13 : getr (ms_regs ms1) 13 = w64 (d_obj cx OOUR)).
  { rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms1 13%bv HS). rewrite <- R26r, (HROK 26%bv). f_equal; vm_compute; reflexivity. }
  assert (A14 : getr (ms_regs ms1) 14 = w64 0).
  { rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms1 14%bv HS).
    match goal with |- context [sr_get ?sr ?rr] => let v := eval vm_compute in (sr_get sr rr) in change (sr_get sr rr) with v end.
    reflexivity. }
  pose proof (st_ok_restrict_mkst SEGS (w_H W) _ _ ms1 HS eq_refl) as Hms. cbn [ss_pc setpc] in Hms.
  pose proof (conj Hbase (conj HJ Hfrs)) as HC4.
  pose proof (cl_base_ro cx h i n now op nb fr len regs (ms_regs ms1) ly3 S3 W mem3 (ms_mem ms1) _ k HB3 HC4 Hpt Hptr
    ltac:(intros r0 Hr0; apply RG; cbv [In] in Hr0 |- *; tauto)) as HB4.
  pose proof HB4 as (_ & _ & _ & _ & _ & HrL4 & _ & Hfrm4 & _ & _ & _ & _ & _ & _ & Hbody4).
  pose proof HrL4 as (Hsp4 & _).
  pose proof Hbody4 as (T4 & G4 & Lk4 & H4 & Hframe4 & Hshadow4 & Hobjs4 & Hblocks4 & Hinput4 & Himg4 & Hoff4 & Hgeo4 & _ & Hstk4 & Hawr4).
  pose proof Hobjs4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HGour & _).
  destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W (ms_mem ms1) _ k HC4)
    as (Hal16' & Hlo' & Hhi' & HF0' & HFc' & HFia' & HFo' & HFal' & HFpres' & HSpres' & HWpres' & HAR' & Hfin' & Efa' & Efl').
  destruct (cl_top cx ly3 S3 W (ms_mem ms1) _ k HC4) as (Htop & Hslo).
  pose proof alloc_ceiling_lt as Hcl. pose proof alloc_ceiling_val as Hcv.
  pose proof HSg as (LSg & GSg & HSf).
  assert (GSg4 : garr8 SEGS (rd W (ms_mem ms1)) (d_obj cx OS) (map (fun b : byte => bv_unsigned b) Sg)).
  { eapply YC88.garr8_aview_kept; [|exact GSg]. intros a _. apply aview_eq_of. apply Hptr. }
  assert (H50 : 50 <= len) by exact (proj1 HSf).
  destruct (cl_fblk cx h n dsh_rec nb fr len ly3 S3 W (ms_mem ms1) _ k HC4 Hbody4 Hfrm4 Hnbn Hlen H50)
    as (Hf0 & Hfr & Hfs & Hfg & Hfsep & Hfin_b & Hfcl & Hfoff & Hfrq).
  pose proof Hfr as (_ & Hf63 & Hfam & _ & _ & Hfra & Hfhv).
  pose proof (cl_cread_obj cx ly3 S3 W (ms_mem ms1) _ k OS (d_A cx) HC4 Hshadow4 ltac:(vm_compute; reflexivity)
    ltac:(unfold CLS_STK, CLS_OWN_BCMP, CLS_VIA_PARSE, CLS_FRAME, CLS_PARSE_NEED, ESTACK, MFRAME, LLVMF_STK in *; lia))
    as (_ & Hs63 & Hsam & _ & _ & Hsra & Hshv).
  pose proof (cl_cread_obj cx ly3 S3 W (ms_mem ms1) _ k OOUR (d_A cx) HC4 Hshadow4 ltac:(vm_compute; reflexivity)
    ltac:(unfold CLS_STK, CLS_OWN_BCMP, CLS_VIA_PARSE, CLS_FRAME, CLS_PARSE_NEED, ESTACK, MFRAME, LLVMF_STK in *; lia))
    as (_ & Hu63 & Huam & _ & _ & Hura & Huhv).
  cbn [dobj_size] in Hs63, Hsam, Hsra, Hshv, Hu63, Huam, Hura, Huhv.
  assert (EFB : slot_classify.fb50 (firstn (Z.to_nat len) (rest_of (c_pl cx) nb)) = cl_F (c_pl cx) nb len).
  { pose proof Hgeo4 as (_ & _ & _ & _ & _ & G6 & _).
    unfold cl_F. apply cl_fb50. rewrite cl_rest_len; [lia | pose proof Hfrm as (F1 & _); lia | lia]. }
  assert (LFB : length (cl_F (c_pl cx) nb len) = 50%nat).
  { rewrite <- EFB. apply slot_classify.fb50_len. }
  assert (HFB8 : d_FB cx mod 4 = 0) by (rewrite <- (Z.mod_mod (d_FB cx) 32) in HFal' by lia; lia).
  pose proof Hgeo4 as (_ & G2 & _). rewrite fs6 in G2.
  pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1' & HA2'). unfold MFRAME in HA1'.
  rewrite Hms.
  eapply SRr_bind.
  { apply (TCHKS fq ly3 S3 W (ms_regs ms1) (ms_mem ms1) _ [] (d_obj cx OS) fr len (d_obj cx OOUR) 0
      Sg (cl_F (c_pl cx) nb len) (our_of (c_pl cx))
      (cl_pre8 cx (ms_regs ms1) ly3 S3 W (ms_mem ms1) _ k TCHECK_SIGHTING_STK 0xd2c HC4 HrL4 R1 ltac:(lia) eq_refl
        ltac:(unfold TCHECK_SIGHTING_STK, ESTACK; lia) ltac:(unfold TCHECK_SIGHTING_STK, ESTACK, LLVMF_STK; lia))
      Himg4 A10 A11 A12 A13 A14).
    - unfold d_obj. cbn [dobj_off]. lia.
    - unfold d_obj. cbn [dobj_off]. rewrite Z.add_mod by lia. rewrite HFB8. reflexivity.
    - exact Hs63.
    - exact Hf0.
    - exact Hf63.
    - unfold d_obj. cbn [dobj_off]. lia.
    - exact Hu63.
    - pose proof Hfrm4 as (F1 & _). unfold REC_MAX in F1. lia.
    - lia.
    - pose proof Hfrm4 as (F1 & _). unfold REC_MAX in F1. lia.
    - exact LSg.
    - exact GSg4.
    - exact LFB.
    - rewrite <- EFB. exact Hfg.
    - apply length_our.
    - exact HGour.
    - exact Hsam.
    - exact Hfam.
    - exact Huam.
    - exact Hsra.
    - exact Hshv.
    - exact Hfra.
    - exact Hfhv.
    - exact Hura.
    - exact Huhv.
    - left. rewrite Hsp4. unfold d_obj. cbn [dobj_off]. unfold TCHECK_SIGHTING_STK, ESTACK, LLVMF_STK in *. lia.
    - left. rewrite Hsp4. unfold TCHECK_SIGHTING_STK, ESTACK, LLVMF_STK in *. lia.
    - unfold off_img in *. rewrite fs6 in Hoff4. unfold d_obj. cbn [dobj_off]. lia.
    - unfold off_img in *. lia.
    - unfold d_obj. cbn [dobj_off]. lia.
    - left. rewrite Hsp4. unfold d_obj. cbn [dobj_off]. unfold TCHECK_SIGHTING_STK, ESTACK, LLVMF_STK in *. lia.
    - exact HSf. }
  cbv beta. intros W2 c2 _ HQ. unfold tcheck_sighting_post, apost_base in HQ.
  destruct HQ as (fx4 & ly4 & S4 & regs4 & mem4 & md4 & -> & _ & Hcsr4 & HJ1 & HP & HPm & Hkept).
  assert (Hfx4 : lib.Lib.FP.frm0 (@YK11.fp_csr fx4)).
  { destruct Hcsr4 as [Ecsr | Ecsr]; [rewrite Ecsr; exact Hfq | exact Ecsr]. }
  rewrite Hsp4 in HJ1, Hkept.
  pose proof (cl_postj cx ly3 S3 W (ms_mem ms1) _ k TCHECK_SIGHTING_STK ly4 S4 W2 mem4 md4 HC4
    ltac:(unfold TCHECK_SIGHTING_STK, ESTACK; lia) ltac:(unfold TCHECK_SIGHTING_STK, ESTACK, LLVMF_STK; lia) HJ1) as HC5.
  apply SRr_ret. right. rewrite R1.
  apply (cl_dat cx 0xd2c (cl_kmax i) (cl_amax i) _ fx4 ly4 S4 regs4 mem4 md4 (k + 0) acc W2 Hfx4 HC5 ltac:(lia) Hacc).
  exists Sg.
  split.
  { apply (cl_base_keep cx h i n now op nb fr len (ms_regs ms1) regs4 ly3 S3 W (ms_mem ms1) _ k ly4 S4 W2 mem4 md4 (k + 0)
      TCHECK_SIGHTING_STK HB4 HC4 HC5 ltac:(unfold TCHECK_SIGHTING_STK, ESTACK; lia)
      ltac:(unfold TCHECK_SIGHTING_STK, ESTACK, LLVMF_STK; lia) Hkept HPm).
    exact (cl_cs8 (ms_regs ms1) regs4 HP). }
  split.
  { unfold dR_cls.
    pose proof (eq_trans (RG 27%bv ltac:(cbv; tauto)) R27r) as Q27.
    pose proof (eq_trans (RG 24%bv ltac:(cbv; tauto)) R24r) as Q24.
    pose proof (eq_trans (RG 23%bv ltac:(cbv; tauto)) R23r) as Q23.
    pose proof (eq_trans (RG 26%bv ltac:(cbv; tauto)) R26r) as Q26.
    pose proof (eq_trans (RG 22%bv ltac:(cbv; tauto)) R22r) as Q22.
    split; [exact (cl_cs (ms_regs ms1) regs4 27 _ HP ltac:(unfold acallee_saved; lia) Q27)|].
    split; [exact (cl_cs (ms_regs ms1) regs4 24 _ HP ltac:(unfold acallee_saved; lia) Q24)|].
    split; [exact (cl_cs (ms_regs ms1) regs4 23 _ HP ltac:(unfold acallee_saved; lia) Q23)|].
    split; [exact (cl_cs (ms_regs ms1) regs4 26 _ HP ltac:(unfold acallee_saved; lia) Q26)|].
    exact (cl_cs (ms_regs ms1) regs4 22 _ HP ltac:(unfold acallee_saved; lia) Q22). }
  split; [exact LSg|]. split; [|exact HSf].
  eapply YC88.garr8_aview_kept; [|exact GSg4]. intros a Ha. rewrite length_map, LSg in Ha.
  unfold d_obj in Ha. cbn [dobj_off] in Ha.
  apply Hkept; unfold TCHECK_SIGHTING_STK, ESTACK, LLVMF_STK in *; lia.
Qed.

Theorem cl_L4 : cl_L4_stmt B MT XM_LIB RLO RHI tfib_K.
Proof. exact cl_s4. Qed.

Lemma cl_push01 : forall G Sg now, 0 <= snd (GateModel.gate_model G Sg now) <= 1.
Proof.
intros G Sg now. unfold GateModel.gate_model.
repeat match goal with
| |- context [match ?x with Some _ => _ | None => _ end] => destruct x
| |- context [if ?c then _ else _] => destruct c
end; cbv beta zeta; cbn [snd fst]; lia.
Qed.

Lemma cl_gate_ret : forall cx h i n now op nb fr len (fq : YK11.FPState) ly3 S3 (W : world SEGS) (regs4 : bvmap 5 word) m4 md4
  k acc Sg G (W2 : world SEGS) c2,
  lib.Lib.FP.frm0 (@YK11.fp_csr fq) -> d_base B MT XM_LIB RLO RHI tfib_K cx ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W m4 md4 k ->
  frames S3 = [(DFRAME_CLASS, c_fpos cx)] ->
  0 <= k <= cl_kmax i -> acc <= cl_amax i ->
  cl_base cx h i n now op nb fr len regs4 ly3 S3 W m4 -> dR_cls cx nb fr len regs4 ->
  getr regs4 1 = w64 (BASE + 0xd40) -> spZ regs4 = d_A cx -> getr regs4 19 = w64 (d_obj cx OG) ->
  cl_sg cx nb len Sg W m4 ->
  treac_disco_gate_should_push_post B fq LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W m4 k regs4 (d_obj cx OG) (d_obj cx OS) now G Sg W2 c2 ->
  cl_GR cx h i n now op nb fr len W2 c2.
Proof.
intros cx h i n now op nb fr len fq ly3 S3 W regs4 m4 md4 k acc Sg G W2 c2
  Hfq Hb HJ3 Hfrs Hk Hacc HB3 HR3 R1 Hsp4 R19 HSg Hpost.
destruct Hpost as (ly2 & S2 & regs2 & mem2 & md2 & Hc & HJ2 & HPR & HR1 & HR10 & Hfr2 & Hperm2 & HK & HGg & HGok & HGs).
assert (HC3 : DCTX cx ly3 S3 W m4 md4 k) by (split; [exact Hb | split; assumption]).
assert (HC2 : DCTX cx ly2 S2 W2 mem2 md2 k) by (split; [exact Hb | split; [exact HJ2 | rewrite Hfr2; exact Hfrs]]).
pose proof HB3 as (Hi & Hn & Hnow & Hop & Hop2 & HrL & Hsp0 & Hfrm & H248 & H408 & H392 & Hlen & Hnb & Hnbn & Hbody).
pose proof HrL as (Hsp & Hgp & Htp & H8 & H9 & H18 & H20 & H25).
pose proof HR3 as (R27 & R24 & R23 & R26 & R22).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W m4 md4 k HC3)
  as (Hal16 & Hlo & Hhi & HF0 & HFc & HFia & HFo & HFal & HFpres & HSpres & HWpres & HAR & Hfin & Efa & Efl).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & Hshadow & Hobjs & Hblocks & Hinput & Himg & Hoff & Hgeo & _ & Hstk & Hawr).
pose proof Hgeo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
set (wr := fun a => d_obj cx OG <= a < d_obj cx OG + 264).
assert (HK' : cl_kept ly3 S3 W m4 W2 mem2 (d_A cx - REAC_DISCO_GATE_SHOULD_PUSH_STK) (d_A cx) wr)
  by (unfold treac_disco_gate_should_push_kept in HK; rewrite Hsp4 in HK; exact HK).
assert (Hwr : forall a, wr a -> d_FB cx + 24 <= a < d_FB cx + DFRAME_SIZE)
  by (intros a Ha; unfold wr, d_obj in Ha; cbn [dobj_off] in Ha; unfold DFRAME_SIZE; lia).
assert (Hwrc : forall a, wr a -> a < alloc_ceiling) by (intros a Ha; pose proof (Hwr a Ha); rewrite fs6 in G2; unfold DFRAME_SIZE in *; lia).
assert (KA : forall a, d_A cx <= a < d_S cx -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) m4 a)
  by exact (cl_view_A cx ly3 S3 W m4 md4 k W2 mem2 _ _ wr HC3 HK' ltac:(lia) Hwrc).
assert (VA : forall o v, 0 <= o -> o + 8 <= 472 -> val_mem SEGS (rd W m4) (d_A cx + o) 8 v ->
  val_mem SEGS (rd W2 mem2) (d_A cx + o) 8 v).
{ intros o v Ho1 Ho2 Hv. eapply YC88.val_mem_aview_kept_x; [|exact Hv]. intros x Hx. apply KA.
  change (Z.of_nat 8) with 8 in Hx. unfold MFRAME in HA1. lia. }
assert (Hos : forall a, wr a -> d_rdset B cx h a -> Exists (fun o => d_objr cx o a) [OG]).
{ intros a Ha _. apply Exists_cons_hd. unfold d_objr. unfold wr in Ha. cbn [dobj_size]. exact Ha. }
assert (Hnew : Forall (fun o => d_obj_new cx o W2 mem2) [OG]).
{ apply Forall_cons; [|apply Forall_nil]. cbn [d_obj_new].
  exists (fst (GateModel.gate_model G Sg now)). split; [exact (proj1 HGok)|]. split; [exact HGg | exact HGok]. }
pose proof HSg as (LSg & GSg & HSf).
unfold cl_GR, d_at. exists fq, ly2, S2, regs2, mem2, md2, k, acc.
split; [rewrite Hc, R1; reflexivity|]. split; [exact Hfq|].
split; [exact Hb|]. split; [exact HJ2|]. split; [rewrite Hfr2; exact Hfrs|]. split; [exact Hk|].
split; [pose proof HJ2 as (_ & _ & _ & _ & _ & _ & Hnev2 & _); unfold cl_kmax in *; lia|].
split; [rewrite MT_TRIV; exact I|]. split; [exact Hacc|].
exists Sg, (fst (GateModel.gate_model G Sg now)), (snd (GateModel.gate_model G Sg now)).
split.
{ unfold cl_base. split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|]. split; [exact Hop|]. split; [exact Hop2|].
  split.
  { unfold d_rL. unfold spZ in Hsp |- *.
    assert (E2 : getr regs2 2 = getr regs4 2) by exact (cl_cs regs4 regs2 2 _ HPR ltac:(unfold acallee_saved; lia) eq_refl).
    rewrite E2. split; [exact Hsp|].
    split; [exact (cl_cs regs4 regs2 3 _ HPR ltac:(unfold acallee_saved; lia) Hgp)|].
    split; [exact (cl_cs regs4 regs2 4 _ HPR ltac:(unfold acallee_saved; lia) Htp)|].
    split; [exact (cl_cs regs4 regs2 8 _ HPR ltac:(unfold acallee_saved; lia) H8)|].
    split; [exact (cl_cs regs4 regs2 9 _ HPR ltac:(unfold acallee_saved; lia) H9)|].
    split; [exact (cl_cs regs4 regs2 18 _ HPR ltac:(unfold acallee_saved; lia) H18)|].
    split; [exact (cl_cs regs4 regs2 20 _ HPR ltac:(unfold acallee_saved; lia) H20)|].
    exact (cl_cs regs4 regs2 25 _ HPR ltac:(unfold acallee_saved; lia) H25). }
  split; [destruct Hsp0 as (S1 & S2'); split; apply VA; first [lia | assumption]|].
  split; [exact (cl_frm_keep cx nb fr len ly3 S3 W m4 md4 k W2 mem2 _ _ wr h n dsh_rec HC3 Hbody HK'
    ltac:(intros a Ha; pose proof (Hwr a Ha); lia) Hfrm)|].
  split; [apply VA; [lia | lia | exact H248]|].
  split; [apply VA; [lia | lia | exact H408]|].
  split; [apply VA; [lia | lia | exact H392]|].
  split; [exact Hlen|]. split; [exact Hnb|]. split; [exact Hnbn|].
  exact (cl_body_call cx h n (dxb fr len) dsh_rec ly3 S3 W m4 md4 k ly2 S2 W2 mem2 md2 k _ _ wr [OG] Hbody HC3 HC2 HK'
    ltac:(unfold REAC_DISCO_GATE_SHOULD_PUSH_STK, ESTACK, MFRAME, LLVMF_STK in *; lia)
    ltac:(lia) Hwr Hos Hnew Hperm2). }
split.
{ unfold dR_cls.
  split; [exact (cl_cs regs4 regs2 27 _ HPR ltac:(unfold acallee_saved; lia) R27)|].
  split; [exact (cl_cs regs4 regs2 24 _ HPR ltac:(unfold acallee_saved; lia) R24)|].
  split; [exact (cl_cs regs4 regs2 23 _ HPR ltac:(unfold acallee_saved; lia) R23)|].
  split; [exact (cl_cs regs4 regs2 26 _ HPR ltac:(unfold acallee_saved; lia) R26)|].
  exact (cl_cs regs4 regs2 22 _ HPR ltac:(unfold acallee_saved; lia) R22). }
split; [exact (cl_cs regs4 regs2 19 _ HPR ltac:(unfold acallee_saved; lia) R19)|].
split; [split; [exact LSg|]; split; [exact HGs | exact HSf]|].
split; [split; [exact (proj1 HGok)|]; split; [exact HGg | exact HGok]|].
split; [exact HR10|]. exact (cl_push01 G Sg now).
Qed.

Lemma cl_s5 : forall cx h i n now op nb fr len W c,
  cl_CSR cx h i n now op nb fr len W c -> SRr SEGS W c (cl_GR cx h i n now op nb fr len).
Proof.
intros cx h i n now op nb fr len W c Hin.
destruct Hin as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hfq & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
  Sg & HB3 & HR & HSg).
pose proof HB3 as (Hi & Hn & Hnow & Hop & Hop2 & HrL & Hsp0 & Hfrm & H248 & H408 & H392 & Hlen & Hnb & Hnbn & Hbody).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & Hshadow & Hobjs & Hblocks & Hinput & Himg & Hoff & Hgeo & _ & Hstk & Hawr).
pose proof Hframe as (E & HdE & Hregs & Hflag & Hh216 & Hh152).
assert (HctxD : DCTX cx ly3 S3 W mem3 md3 k) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HctxD)
  as (Hal16 & Hlo & Hhi & HF0 & HFc & HFia & HFo & HFal & HFpres & HSpres & HWpres & HAR & Hfin & Efa & Efl).
pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HAr2 : 0 <= d_A cx < 2 ^ 64) by (unfold MFRAME, LLVMF_STK in *; lia).
pose proof Hsp0 as (H232 & H344).
assert (HACS : Forall (YP09.chunk_ok SEGS (d_env cx E (cl_vals regs [w64 now])) (rd W mem3) (d_A cx))
  [YP09.mkChunk 344 (CVal 8 (SOff (AT_X + 32) 0))]).
{ apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS (d_env cx E (cl_vals regs [w64 now])) (rd W mem3) (d_A cx) 344 8 (SOff (AT_X + 32) 0) now).
  - cbn [sv_denot]. rewrite Z.add_0_r.
    replace (AT_X + 32)%nat with (AT_X + length (map (fun r0 => getr regs (Z_to_bv 5 (Z.of_nat r0))) (seq 0 32)))%nat
      by (rewrite length_map, length_seq; reflexivity).
    unfold cl_vals. rewrite (d_env_x cx E (map (fun r0 => getr regs (Z_to_bv 5 (Z.of_nat r0))) (seq 0 32) ++ [w64 now])
      (length (map (fun r0 => getr regs (Z_to_bv 5 (Z.of_nat r0))) (seq 0 32)))
      ltac:(rewrite length_app; cbn [length]; lia)).
    rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth]. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact Hnow.
  - lia.
  - exact H344. }
pose proof (d_seat B MT XM_LIB RLO RHI tfib_K LAWS TL fq cx dsh_rec ly3 S3 W regs mem3 md3 k E 0xd2c cl_sr
  (cl_vals regs [w64 now]) [YP09.mkChunk 344 (CVal 8 (SOff (AT_X + 32) 0))] [] [] (d_facts [] [])
  HctxD HdE Hregs Hflag (cl_regs_ok cx E regs [w64 now] HdE HrL HAr2)
  (d_facts_ok B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k E (cl_vals regs [w64 now]) [] [] HctxD HdE I I)
  HACS (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS.
unfold ss_d in HS.
cl_ro_base HS 516%nat. cl_ro_base HS 529%nat. cl_ro_base HS 60%nat.
assert (HEI : img_env VAL A_LIM (d_env cx E (cl_vals regs [w64 now]))).
{ destruct HdE as (_ & _ & HI & _). intros a Ha. unfold d_env. rewrite ew_havoc_old by (unfold A_LIM, AT_FL in *; lia). exact (HI a Ha). }
assert (SHOK : sh_ok SEGS (SOff 32 0) [] (d_env cx E (cl_vals regs [w64 now])) (rd W mem3)) by constructor.
assert (E563 : ew (d_env cx E (cl_vals regs [w64 now])) 563 = w64 now).
{ change 563%nat with (AT_X + 32)%nat.
  rewrite (d_env_x cx E (cl_vals regs [w64 now]) 32
    ltac:(unfold cl_vals; rewrite length_app, length_map, length_seq; cbn; lia)).
  unfold cl_vals. rewrite app_nth2 by (rewrite length_map, length_seq; lia).
  rewrite length_map, length_seq. rewrite Nat.sub_diag. reflexivity. }
assert (EF : ew (d_env cx E (cl_vals regs [w64 now])) 516 = Z_to_bv 64 (d_FB cx)).
{ unfold d_env. rewrite ew_havoc_old by (cbv; lia). destruct HdE as (_ & _ & _ & _ & HFx & _). exact HFx. }
pose (RUN := paj_run (fx := fq) B LAWS).
unfold cfg_at. change (w64 (BASE + 0xd2c)) with (Z_to_bv 64 (BASE + 0xd2c)).
paj_run_tok RUN HS HJ SHOK cl_span.
{ cbn [ss_mem]. repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
assert (Hpt := cl_ro_pt _ _ _ _ HF ltac:(vm_compute; reflexivity)).
assert (Hptr := cl_ro_pt _ _ _ _ HFr ltac:(vm_compute; reflexivity)).
clear HF HFr HG.
rewrite (pa_sigma_reac_disco_gate_should_push (PI := PI)) in HS.
pose proof (cl_regs_ok cx E regs [w64 now] HdE HrL HAr2) as HROK.
pose proof HR as (R27r & R24r & R23r & R26r & R22r).
assert (RG : forall r0 : bv 5, In r0 [2; 3; 4; 8; 9; 18; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
  getr (ms_regs ms) r0 = getr regs r0).
{ intros r0 Hr0. rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms r0 HS), (HROK r0).
  cbv [In] in Hr0. repeat (destruct Hr0 as [<-|Hr0]; [f_equal; vm_compute; reflexivity|]). destruct Hr0. }
assert (R1 : getr (ms_regs ms) 1 = w64 (BASE + 0xd40)).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 1%bv HS).
  match goal with |- context [sr_get ?sr ?rr] => let v := eval vm_compute in (sr_get sr rr) in change (sr_get sr rr) with v end.
  unfold w64. exact (codeptr_val _ 3392 HEI). }
assert (R19 : getr (ms_regs ms) 19 = w64 (d_obj cx OG)).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 19%bv HS).
  match goal with |- context [sr_get ?sr ?rr] => let v := eval vm_compute in (sr_get sr rr) in change (sr_get sr rr) with v end.
  cbn [sv_denot]. rewrite EF, cl_w64_add. reflexivity. }
assert (A10 : getr (ms_regs ms) 10 = w64 (d_obj cx OG)).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 10%bv HS).
  match goal with |- context [sr_get ?sr ?rr] => let v := eval vm_compute in (sr_get sr rr) in change (sr_get sr rr) with v end.
  cbn [sv_denot]. rewrite EF, cl_w64_add. reflexivity. }
assert (A11 : getr (ms_regs ms) 11 = w64 (d_obj cx OS)).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 11%bv HS). rewrite <- R22r, (HROK 22%bv). f_equal; vm_compute; reflexivity. }
assert (A12 : getr (ms_regs ms) 12 = w64 now).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 12%bv HS).
  match goal with |- context [sr_get ?sr ?rr] => let v := eval vm_compute in (sr_get sr rr) in change (sr_get sr rr) with v end.
  cbn [sv_denot]. rewrite E563, cl_w64_add, Z.add_0_r. reflexivity. }
pose proof (st_ok_restrict_mkst SEGS (w_H W) _ _ ms HS eq_refl) as Hms. cbn [ss_pc setpc] in Hms.
pose proof (conj Hbase (conj HJ Hfrs)) as HC4.
pose proof (cl_base_ro cx h i n now op nb fr len regs (ms_regs ms) ly3 S3 W mem3 (ms_mem ms) _ k HB3 HC4 Hpt Hptr
  ltac:(intros r0 Hr0; apply RG; cbv [In] in Hr0 |- *; tauto)) as HB4.
assert (HR4 : dR_cls cx nb fr len (ms_regs ms)).
{ unfold dR_cls. rewrite !RG by (cbv; tauto). exact HR. }
pose proof HB4 as (_ & _ & _ & _ & _ & HrL4 & _ & Hfrm4 & _ & _ & _ & _ & _ & _ & Hbody4).
pose proof HrL4 as (Hsp4 & Hgp4 & Htp4 & _).
pose proof Hbody4 as (T4 & G4 & Lk4 & H4 & Hframe4 & Hshadow4 & Hobjs4 & Hblocks4 & Hinput4 & Himg4 & Hoff4 & Hgeo4 & _ & Hstk4 & Hawr4).
pose proof Hobjs4 as (_ & _ & _ & LG4 & GG4 & QG4 & _).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W (ms_mem ms) _ k HC4)
  as (Hal16' & Hlo' & Hhi' & HF0' & HFc' & HFia' & HFo' & HFal' & HFpres' & HSpres' & HWpres' & HAR' & Hfin' & Efa' & Efl').
pose proof alloc_ceiling_lt as Hcl. pose proof alloc_ceiling_val as Hcv.
pose proof HSg as (LSg & GSg & HSf).
assert (GSg4 : garr8 SEGS (rd W (ms_mem ms)) (d_obj cx OS) (map (fun b : byte => bv_unsigned b) Sg)).
{ eapply YC88.garr8_aview_kept; [|exact GSg]. intros a _. apply aview_eq_of. apply Hptr. }
assert (HSg4 : cl_sg cx nb len Sg W (ms_mem ms)) by exact (conj LSg (conj GSg4 HSf)).
pose proof (cl_cread_obj cx ly3 S3 W (ms_mem ms) _ k OG (d_A cx) HC4 Hshadow4 ltac:(vm_compute; reflexivity)
  ltac:(unfold CLS_STK, CLS_OWN_BCMP, CLS_VIA_PARSE, CLS_FRAME, CLS_PARSE_NEED, ESTACK, MFRAME, LLVMF_STK in *; lia))
  as (_ & Hg63 & Hgam & _ & _ & Hgra & Hghv).
pose proof (cl_cread_obj cx ly3 S3 W (ms_mem ms) _ k OS (d_A cx) HC4 Hshadow4 ltac:(vm_compute; reflexivity)
  ltac:(unfold CLS_STK, CLS_OWN_BCMP, CLS_VIA_PARSE, CLS_FRAME, CLS_PARSE_NEED, ESTACK, MFRAME, LLVMF_STK in *; lia))
  as (_ & Hs63 & Hsam & _ & _ & Hsra & Hshv).
cbn [dobj_size] in Hg63, Hgam, Hgra, Hghv, Hs63, Hsam, Hsra, Hshv.
assert (HFB8 : d_FB cx mod 8 = 0) by (rewrite <- (Z.mod_mod (d_FB cx) 32) in HFal' by lia; lia).
pose proof Hgeo4 as (_ & G2 & _). rewrite fs6 in G2.
unfold MFRAME in HA1.
rewrite Hms.
eapply SRr_bind.
{ apply (TGP fq LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(DFRAME_CLASS, c_fpos cx)]
    ly3 S3 W (ms_mem ms) _ k (ms_regs ms) (d_obj cx OG) (d_obj cx OS) now G4 Sg HJ).
  - rewrite R1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite R1. unfold w64. pose proof (@pa_B_ok _ _ PI) as (HB0 & HB1 & _).
    rewrite unsigned_lit_small by lia. pose proof (pa_base_lo (PI := PI)). unfold IMG_LO in *. lia.
  - exact Hgp4.
  - exact Htp4.
  - exact A10.
  - exact A11.
  - exact A12.
  - exact Hnow.
  - rewrite Hsp4. lia.
  - rewrite Hsp4. unfold REAC_DISCO_GATE_SHOULD_PUSH_STK, ESTACK, LLVMF_STK in *. lia.
  - rewrite Hsp4. lia.
  - unfold d_obj. cbn [dobj_off]. lia.
  - unfold d_obj. cbn [dobj_off]. rewrite Z.add_mod by lia. rewrite HFB8. reflexivity.
  - exact Hg63.
  - right. rewrite Hsp4. unfold d_obj. cbn [dobj_off]. unfold REAC_DISCO_GATE_SHOULD_PUSH_STK, ESTACK, LLVMF_STK in *. lia.
  - intros a Ha. apply Hawr4. unfold d_obj in Ha. cbn [dobj_off] in Ha. unfold DFRAME_SIZE. lia.
  - exact Hgam.
  - exact Hgra.
  - exact Hghv.
  - exact LG4.
  - exact GG4.
  - exact QG4.
  - unfold d_obj. cbn [dobj_off]. lia.
  - unfold d_obj. cbn [dobj_off]. lia.
  - exact Hs63.
  - right. rewrite Hsp4. unfold d_obj. cbn [dobj_off]. unfold REAC_DISCO_GATE_SHOULD_PUSH_STK, ESTACK, LLVMF_STK in *. lia.
  - left. exists DFRAME_CLASS, (c_fpos cx). split; [exact Hfin'|]. rewrite Efa', fs6. unfold d_obj. cbn [dobj_off]. lia.
  - exact Hsam.
  - exact Hsra.
  - exact Hshv.
  - exact LSg.
  - exact GSg4.
  - left. unfold d_obj. cbn [dobj_off]. lia. }
intros W2 c2 _ Hpost. apply SRr_ret.
exact (cl_gate_ret cx h i n now op nb fr len fq ly3 S3 W (ms_regs ms) (ms_mem ms) _ k acc Sg G4 W2 c2
  Hfq Hbase HJ Hfrs Hk Hacc HB4 HR4 R1 Hsp4 R19 HSg4 Hpost).
Qed.

Theorem cl_L5 : cl_L5_stmt B MT XM_LIB RLO RHI tfib_K.
Proof. exact cl_s5. Qed.

Lemma cl_in_nb : forall cx h i n now op nb fr len W c,
  cls_in B MT XM_LIB RLO RHI tfib_K cx h i n now op nb fr len W c -> nb <= c_n cx.
Proof.
intros cx h i n now op nb fr len W c H. unfold cls_in, d_arm_at_pf, d_at in H.
destruct H as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & Hc & Hfq & Hb & HJ & Hfr & Hk & Hnev & Hmo & Hacc & HP).
destruct HP as (_ & _ & _ & _ & _ & (_ & _ & (_ & _ & Hnb & _) & _) & _). exact Hnb.
Qed.

Theorem cls_spec_pf : cls_spec B MT XM_LIB RLO RHI tfib_K.
Proof.
exact (cl_compose B MT XM_LIB RLO RHI tfib_K cl_in_nb cl_L1 cl_L2 cl_L3 cl_L4 cl_L5
  (cl_L6 B MT XM_LIB RLO RHI tfib_K LAWS TL FFL) (cl_loop B MT XM_LIB RLO RHI tfib_K LAWS TL ABCMP)
  (cl_L10 B MT XM_LIB RLO RHI tfib_K LAWS TL FFL DCAN)).
Qed.

End h.
End f.
End d.
