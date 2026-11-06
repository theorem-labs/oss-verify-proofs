(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10 (lane F1 of the generic cf instance layer; integrator ReallocPrimary).
   The cf twin of proofs/cgif/cgif_file_fuzzer/lib/CLdepotcgif.v at c5 30a1993588f (and of CLdepotcgifE.v's
   de_depot_cgif): StackDepotPut's contract at the walks' call sites, at the cf relation, from the unit's released
   depot contract.
   rule 24: no function proved (kind: interface-instance discharge over the unit's released depot contract).

   CLdepotcgif.v proves CLdepot.DepotSub at ARX_cgif and gets the depot fields from CLdepot.depot_field_ok.  Two
   things differ at the cf relation:
   1. The released contract (CLdepot.depot_spec_x, CLdepot.v:94-113; cgif YFl0.tfib_depot_spec, preset A/AFl0.v:68)
      takes cgif's `Wf (as_universe B) S`, but ARcf carries Wf_cf.  The contract reads the model only through its
      depot, so [depot_spec_d_of_x] closes the gap with no new premise: it runs the contract at the state
      [dswap_cf S] (S's depot on cgif's initial state, Wf by YG01.wf_init and Wf_cf's wfc_depot), whose answer
      condition and depot facts are S's (aok and CLdepot.depot_mem_ok read st_depot only).
   2. The image half of DepotSub (the constant cells and the depot's memory carried to the call memory; the depot's
      write set inside the walk's zone) compares the unit's symbols with its zones.  It is two image premises named
      over the class fields only, [dep_keep_img] and [dep_fp_img] (CLdepotcgif.sub_a / sub_d's ds_keep and ds_fp
      scripts, which a unit runs at its image: cgif's AGix.const_kept / depot_mem_ok_agree / footprint_DZONE).
      The model half comes from ARcf here ([depot_at0_cf]: AGix.depot_at0 over ARmcf).
   Fields: [depot_field_cf] (CLdepot.depot_field at any zone pair), [if_depot_cf] (AGif0n.AIface.if_depot; at the
   post-refill state Sp it is also AIfaceM.if_depot_miss, whose U premise is at the entry state and U_cf ignores
   the state), [di_depot_cf] (DGif0.DIface.di_depot), [dpost_aok_cf] (if_dpost_aok / di_dpost_aok) and
   [de_depot_cf] (ErrnoG.de_depot_t, CLdepotcgifE.de_depot_cgif's script over YGcfInstErrno.v's fields).  The depot
   post is [dpost_cf B] := CLdepot.dpost_x im_segs B.  The walk relation is any [ARX] that gives ARcf at the
   caller's ghost set Hp (YGcfInstBase.ARX_cf B IOK Hp through ARX_cf_ARcf).  No image constant; no event term. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG07.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ImgBaseAG ImgBaseDG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require CLdepot ErrnoG ErrnoApart YGcfDIface YGcfInstBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import YGcfInstErrno.
(* stdpp, through the LPS modules, shadows several list names; NoDup / In here are Stdlib's, as Wf_cf's (wfc_depot)
   and YGcfMallocComposeE.v's. *)
From Stdlib Require Import List.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 1. The state swap: the released contract at Wf_cf.                                                              *)

(* S's depot on cgif's initial state. *)
Definition dswap_cf (S : astate) : astate := set_depot (st_depot S) init_state.

(* Wf of the swapped state: cgif's initial state is Wf (YG01.wf_init) and a Wf depot keeps it (YG07.WfP_set_depot). *)
Lemma dswap_wf_cf : forall (U : Univ) S, depot_fits U (st_depot S) -> Wf U (dswap_cf S).
Proof. intros U S HD. exact (WfP_set_depot U 0 0 0 init_state (st_depot S) (wf_init U) HD). Qed.

(* The depot's memory facts read the model only through its depot (AGix.depot_mem_ok_ext, AGix.v:176-183). *)
Lemma depot_mem_ok_ext_cf : forall B ly S1 S2 (rd : reader), st_depot S1 = st_depot S2 ->
CLdepot.depot_mem_ok B ly S1 rd -> CLdepot.depot_mem_ok B ly S2 rd.
Proof.
intros B ly S1 S2 rd E (D1 & D2 & D3). split; [|split; [|exact D3]].
- replace (depot_cells ly S2) with (depot_cells ly S1) by (unfold depot_cells, depot_ids, depot_frames; rewrite E; reflexivity).
  exact D1.
- revert D2. unfold depot_ok, depot_ids, depot_traces. rewrite E. exact (fun H => H).
Qed.

Section w.
Variable segs : list Segment.
Variables (A_DEP TPv : Z).
Variable IMGC : alayout -> Prop.
Variable B : asyms.
(* CLdepot.depot_spec_x (CLdepot.v:94-113, at the admission premise YG01.admits since commit 1470d2b40a0e) with its
   state premise `Wf (as_universe B) S` replaced by the depot part of it, which Wf_cf carries (wfc_depot:
   depot_fits, YG01.v:153). *)
Definition depot_spec_d : Prop :=
forall (W : world segs) (ly : alayout) (S : astate) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (buf : Z) (tr : list Z),
let H := w_H W in let rd := aview segs H mem in let sp := bv_unsigned (getr regs 2) in
layout_ok ly -> IMGC ly -> depot_fits (as_universe B) (st_depot S) -> admits (as_universe B) tr S ->
Forall (cell_holds B ly rd) (as_const B ly) -> CLdepot.depot_mem_ok B ly S rd ->
getr regs 10 = Z_to_bv 64 buf -> getr regs 11 = Z_to_bv 64 (Z.of_nat (length tr)) ->
getr regs 3 = Z_to_bv 64 (as_gp B) -> getr regs 4 = Z_to_bv 64 TPv -> YK0s.ret_ok (getr regs 1) ->
(forall i, (i < length tr)%nat -> val_mem segs (mrestrict H mem) (buf + 8 * Z.of_nat i) 8 (nth i tr 0)) ->
buf mod 8 = 0 -> ly_stk_lo ly <= buf -> buf + 8 * 30 <= ly_stk_hi ly -> buf + 8 * 30 <= sp - CLdepot.DEP_STK \/ sp <= buf ->
sp mod 16 = 0 -> ly_stk_lo ly <= sp - CLdepot.DEP_STK -> sp <= ly_stk_hi ly ->
(forall a, sp - CLdepot.DEP_STK <= a < sp -> apresent H mem a) ->
SRr segs W (mkCfg (mkst regs (Z_to_bv 64 A_DEP) mem (seg_rom segs)) md)
(fun W' c' => W' = W /\ exists z regs' mem' mat,
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) (with_vm_backing (m_vm_lazy md) mat md) /\
aok S (KDepot tr) z /\
regs_preserved regs regs' /\
(forall x : word, ~ (sp - CLdepot.DEP_STK <= bv_unsigned x < sp) -> ~ CLdepot.depot_footprint B ly (bv_unsigned x) ->
  mem' x = mem x) /\
(forall a, apresent H mem a -> apresent H mem' a) /\
CLdepot.depot_mem_ok B ly (CLdepot.depot_after z tr S) (aview segs H mem') /\
Forall (cell_holds B ly (aview segs H mem')) (as_const B ly)).

(* The released contract gives the swapped one: run it at [dswap_cf S]. *)
Theorem depot_spec_d_of_x : CLdepot.depot_spec_x segs A_DEP TPv IMGC B -> depot_spec_d.
Proof.
intros HD W ly S regs mem md buf tr H rd sp LY IMG HDF Htr CST DEP R10 R11 R3 R4 R1 BUF B8 BL BH BD S16 SL SH PRES.
pose proof (dswap_wf_cf (as_universe B) S HDF) as WS.
assert (DEPS : CLdepot.depot_mem_ok B ly (dswap_cf S) rd) by exact (depot_mem_ok_ext_cf B ly S (dswap_cf S) rd eq_refl DEP).
eapply SRr_mono;
  [exact (HD W ly (dswap_cf S) regs mem md buf tr LY IMG WS Htr CST DEPS R10 R11 R3 R4 R1 BUF B8 BL BH BD S16 SL SH PRES)|].
intros W' c' _ (EW & z & regs' & mem' & mat & Hc & AOK & RP & FR & PR & DEP' & CST').
split; [exact EW|]. exists z, regs', mem', mat.
split; [exact Hc|]. split; [exact AOK|]. split; [exact RP|]. split; [exact FR|]. split; [exact PR|].
split; [|exact CST'].
refine (depot_mem_ok_ext_cf B ly (CLdepot.depot_after z tr (dswap_cf S)) (CLdepot.depot_after z tr S) _ _ DEP').
unfold CLdepot.depot_after. destruct (z =? 0); reflexivity.
Qed.
End w.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 2. The model half of DepotSub: the depot's memory facts at the relation's memory (AGix.depot_at0, AGix.v:184-197) *)
Lemma depot_at0_cf : forall B ly S Hp (rd : reader), ARmcf B ly S Hp rd -> CLdepot.depot_mem_ok B ly S rd.
Proof.
intros B ly S Hp rd M. split; [|split].
- apply Forall_forall. intros c Hc. apply (proj1 (Forall_forall _ _) (amc_cells _ _ _ _ _ M)).
  unfold acells_cf. do 6 (apply in_or_app; right). apply in_or_app. left. exact Hc.
- exact (amc_depot _ _ _ _ _ M).
- apply Forall_forall. intros r Hr. cbn in Hr.
  destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]].
  1-3: apply (proj1 (Forall_forall _ _) (amc_junk _ _ _ _ _ M)); unfold ajunk_cf; right; right;
       do 6 (apply in_or_app; right); apply in_or_app; left; cbn; tauto.
  all: apply (proj1 (Forall_forall _ _) (amc_areas _ _ _ _ _ M)); unfold aareas; do 3 (apply in_or_app; right); cbn; tauto.
Qed.

Context {IM : AImg}.

Section f.
Variable B : asyms.
(* The caller's ghost set and the walk relation: any relation that gives ARcf at Hp (YGcfInstBase.ARX_cf B IOK Hp,
   with HAR := YGcfInstBase.ARX_cf_ARcf B IOK Hp). *)
Variable Hp : list Z.
Variable ARX : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop.
Hypothesis HAR : forall inst ly S W mem md, ARX inst ly S W mem md -> ARcf im_segs B ly S Hp W mem md.

(* The depot post (CLdepot.v:88-91) at the unit's segments. *)
Definition dpost_cf : Z -> alayout -> astate -> world im_segs -> list Z -> Z -> (word -> option byte) -> Prop :=
CLdepot.dpost_x im_segs B.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 3. The image half of DepotSub, as image premises over the class fields (CLdepotcgif.sub_a / sub_d).             *)

(* ds_keep: the constant cells and the depot's memory facts hold at any memory that keeps [KEEP] as at [mem0]. *)
Definition dep_keep_img (KEEP : alayout -> Z -> Prop) : Prop :=
forall ly S (W : world im_segs) (mem0 mem : word -> option byte),
layout_ok ly -> im_img_cover ly -> ly_tsd ly = as_tsd B ->
depot_fits (as_universe B) (st_depot S) ->
Forall (cell_holds B ly (aview im_segs (w_H W) mem0)) (as_const B ly) ->
CLdepot.depot_mem_ok B ly S (aview im_segs (w_H W) mem0) ->
(forall x : word, KEEP ly (bv_unsigned x) -> mem x = mem0 x) ->
Forall (cell_holds B ly (aview im_segs (w_H W) mem)) (as_const B ly) /\
CLdepot.depot_mem_ok B ly S (aview im_segs (w_H W) mem).

(* ds_fp: what StackDepotPut may write lies in the zone [DZ] the caller frames out. *)
Definition dep_fp_img (DZ : alayout -> Z -> Prop) : Prop :=
forall ly a, layout_ok ly -> im_img_cover ly -> ly_tsd ly = as_tsd B -> CLdepot.depot_footprint B ly a -> DZ ly a.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 4. The fields.                                                                                                   *)
Section z.
Variable A_DEP : Z.
Variables (DZ KEEP : alayout -> Z -> Prop).

(* CLdepot.depot_field (CLdepot.v:116-135) at the cf relation (CLdepot.depot_field_ok's script over the swap). *)
Theorem depot_field_cf : YGcfDIface.IMG_COVER -> dep_keep_img KEEP -> dep_fp_img DZ ->
CLdepot.depot_spec_x im_segs A_DEP im_tp im_img_cover B ->
CLdepot.depot_field im_segs A_DEP im_tp B ARX (YGcfInstBase.cf_tr_ok B) DZ KEEP.
Proof.
intros HC KP FP HD inst ly S W mem0 md0 tr regs mem md buf HARX HU MEQ R10 R11 R3 R4 R1 BUF B8 BL BH BD S16 SL SH PRES.
destruct (HAR inst ly S W mem0 md0 HARX) as (M & L & _).
pose proof (amc_layout _ _ _ _ _ M) as LY. pose proof (HC ly S md0 L) as IMG.
pose proof (amc_tsd _ _ _ _ _ M) as TSD.
pose proof (wfc_depot _ _ _ _ _ (amc_wf _ _ _ _ _ M)) as HDF.
destruct (KP ly S W mem0 mem LY IMG TSD HDF (amc_const _ _ _ _ _ M) (depot_at0_cf B ly S Hp _ M) MEQ) as [CST DEP].
eapply SRr_mono.
{ exact (depot_spec_d_of_x im_segs A_DEP im_tp im_img_cover B HD W ly S regs mem md buf tr LY IMG HDF HU CST DEP
    R10 R11 R3 R4 R1 BUF B8 BL BH BD S16 SL SH PRES). }
intros W' c' Hle (-> & z & regs' & mem' & mat & -> & AOK & RP & FR & PR' & DEP' & CST'). split; [reflexivity|].
exists z, regs', mem', mat. split; [reflexivity|]. split; [exact RP|].
split; [|split; [exact PR' | exact (conj AOK (conj DEP' CST'))]].
intros x N1 N2. apply FR; [exact N1|].
intros FPx. apply N2. exact (FP ly (bv_unsigned x) LY IMG TSD FPx).
Qed.
End z.

(* The answer the depot post carries (AGif0n.if_dpost_aok / DGif0.di_dpost_aok; CLdepotcgif.dpost_aok_cgif). *)
Theorem dpost_aok_cf : forall inst ly S W tr z m, dpost_cf inst ly S W tr z m -> aok S (KDepot tr) z.
Proof. intros inst ly S W tr z m H. exact (proj1 H). Qed.

(* AGif0n.AIface's if_depot at the cf relation (Allocate keeps the depot zone and the constant cells' zone).  It
   gives AIfaceM.if_depot_miss at the post-refill state: apply it there, U being state-free. *)
Theorem if_depot_cf {AG : AGImg} : YGcfDIface.IMG_COVER -> dep_keep_img (fun ly a => ag_dzone ly a \/ ag_czone ly a) ->
dep_fp_img ag_dzone -> CLdepot.depot_spec_x im_segs ag_depot_put im_tp im_img_cover B ->
CLdepot.depot_field im_segs ag_depot_put im_tp B ARX (YGcfInstBase.cf_tr_ok B) ag_dzone
  (fun ly a => ag_dzone ly a \/ ag_czone ly a).
Proof. intros HC KP FP HD. exact (depot_field_cf ag_depot_put ag_dzone _ HC KP FP HD). Qed.

(* DGif0.DIface's di_depot at the cf relation (Deallocate keeps the depot zone, and the constant cells' zone outside
   the internal allocator's). *)
Theorem di_depot_cf {DI : DImg} : YGcfDIface.IMG_COVER ->
dep_keep_img (fun ly a => dg_dzone ly a \/ (dg_czone ly a /\ ~ dg_izone a)) ->
dep_fp_img dg_dzone -> CLdepot.depot_spec_x im_segs dg_depot im_tp im_img_cover B ->
CLdepot.depot_field im_segs dg_depot im_tp B ARX (YGcfInstBase.cf_tr_ok B) dg_dzone
  (fun ly a => dg_dzone ly a \/ (dg_czone ly a /\ ~ dg_izone a)).
Proof. intros HC KP FP HD. exact (depot_field_cf dg_depot dg_dzone _ HC KP FP HD). Qed.

(* ErrnoG.de_depot_t (DIfaceE.de_depot): di_depot with errno kept on the raw memory (CLdepotcgifE.de_depot_cgif):
   errno lies apart from the depot's stack window (ErrnoApart.errno_apart_stack) and from the depot zone
   (ErrnoApart.errno_apart_dzone_d), the two sets the post does not keep. *)
Theorem de_depot_cf {AG : AGImg} {DI : DImg} : im_syms B -> ErrnoImgCf -> YGcfDIface.IMG_COVER ->
dep_keep_img (fun ly a => dg_dzone ly a \/ (dg_czone ly a /\ ~ dg_izone a)) ->
dep_fp_img dg_dzone -> CLdepot.depot_spec_x im_segs dg_depot im_tp im_img_cover B ->
ErrnoG.de_depot_t B (YGcfInstBase.cf_tr_ok B) ARX dpost_cf.
Proof.
intros TS EI HC KP FP HD inst ly S W mem0 md0 tr regs mem md buf HARX HU MEQ R10 R11 R3 R4 R1 BUF B8 BL BH BD S16 SL SH PRES.
destruct (HAR inst ly S W mem0 md0 HARX) as (M & L & _).
pose proof (amc_layout _ _ _ _ _ M) as LY. pose proof (HC ly S md0 L) as IMG.
destruct (ei_in_img EI B ly TS IMG) as [E1 E2].
pose proof (lo_img ly LY) as (L1 & L2 & L3 & _).
eapply SRr_mono;
  [exact (di_depot_cf HC KP FP HD inst ly S W mem0 md0 tr regs mem md buf HARX HU MEQ R10 R11 R3 R4 R1
            BUF B8 BL BH BD S16 SL SH PRES)|].
intros W' c' _ [EW (z & regs' & mem' & mat & Ec & RP & FR & PR & DP)]. cbv beta.
split; [exact EW|]. exists z, regs', mem', mat.
split; [exact Ec|]. split; [exact RP|]. split; [exact FR|].
split; [|split; [exact PR | exact DP]].
intros i Hi.
assert (EB : bv_unsigned (Z_to_bv 64 (as_errno B + i)) = as_errno B + i).
{ apply unsigned_lit_small. unfold kImgLo, kImgEnd in *. lia. }
assert (HE : as_errno B <= as_errno B + i < as_errno B + 4) by lia.
refine (FR (Z_to_bv 64 (as_errno B + i)) _ _); rewrite EB.
- intros Hs. exact (ErrnoApart.errno_apart_stack (ei_in_img EI) B ly _ _ (as_errno B + i) TS LY IMG SL Hs HE).
- intros Hd. exact (ei_dzone_d EI B ly (as_errno B + i) TS LY IMG Hd HE).
Qed.
End f.
End a.
