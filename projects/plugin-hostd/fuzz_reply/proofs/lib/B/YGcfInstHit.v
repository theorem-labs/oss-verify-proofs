(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10 (lane M of the generic cf instance layer, a working branch; integrator ReallocPrimary).
   The cf twin of proofs/cgif/cgif_file_fuzzer/lib/AGif1.v and AGif1k.v at c5 30a1993588f (with AGif1mE.v's
   ae_depot): the hit interfaces AGif0n.AIface / AGif0n.AIfaceK and ErrnoG.AIfaceE at the call-site relation
   YGcfInstBase.ARXq_cf, generic over CfImg / CfParams / AImg / AGImg.
   - iface_cf : forall Hp, AIface B (U_cf B) malloc_cf (ARXq_cf B IOK Hp) (AOX_cf B) (rpre_cf B) cf_malloc_max
                LIVE_MAX qtight (dpost_cf B) cf_pc_malloc_max cf_pc_spin_shadow;
   - ifaceK_cf, ifaceE_cf : the same arguments, AIfaceK / ErrnoG.AIfaceE.
   - hit_bridge_g / hit_bridge_k : the hit walk's post (AGif0n.at_RETw / at_RETkw) to ARcf at ImgBaseAG.st_final, at a
     generic pop state X and depot post DPOST (YGcfInstMiss.v uses them at the post-refill state).
   The model facts come from ARcf (YGcfInstHitCore.v: the view, the owned set, the shape; YGcfInstHitPost.v: the AR
   link hit_ARcf) and from malloc_cf's contract (YG07cf.malloc_gen_cf).  The unit's facts are the NAMED Section
   hypotheses of Section b below.
   rule 24: no function proved (interface-instance discharge at a model relation; no machine walk is written).
   EVENT-FREE: no event counter, event bound, meter or regime appears in this file; the only event term is the tick
   update `set_nev (st_nev S + 1) S` inside the interfaces' own statements. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import AllocG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ImgBaseAG AGif0n ErrnoG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require CLdepot ErrnoApart YGcfDIface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YGcfImgRows.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0scf YG0qcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YGcfInstBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG02cf YG07cf YGcfTok.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YGcfXsMapped.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YGcfInstHitCore YGcfInstHitPost.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {IM : AImg}.
Local Open Scope am_scope.

Section d.
Variable B : asyms.
(* The post of the depot callee (AGif1.dpost_cgif, AGif1.v:35-38, over the unit's segments): the answer is the model's,
   and the depot's memory facts after the put and the constant cells hold at the memory the callee returns.  It is
   CLdepot.dpost_x (CLdepot.v:88-91) at im_segs, the post the generic depot field CLdepot.depot_field gives. *)
Definition dpost_cf : Z -> alayout -> astate -> world im_segs -> list Z -> Z -> (word -> option byte) -> Prop :=
  CLdepot.dpost_x im_segs B.
End d.

End a.

Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {IM : AImg} {AG : AGImg}.
Local Open Scope am_scope.

(* ================================================================================================================ *)
(* 0. Model arithmetic (no image).                                                                                  *)
(* Every primary request up to 64512 bytes is a primary chunk (AGtop.prim_fp_g, YFij.v:37). *)
Lemma prim_fp_cf : forall n, 0 <= n <= 64512 -> from_primary n = true.
Proof.
intros n Nrange. unfold from_primary, needed_primary, rounded_size, round_up, rz_size, rz_log, kMaxSize. apply Z.leb_le.
pose proof (Z.div_mod (Z.max n 8 + 8 - 1) 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (Z.max n 8 + 8 - 1) 8 ltac:(lia)) as M.
destruct (Z.leb_spec n 48); [change (Z.shiftl 16 0) with 16; lia|].
destruct (Z.leb_spec n 96); [change (Z.shiftl 16 1) with 32; lia|].
destruct (Z.leb_spec n 448); [change (Z.shiftl 16 2) with 64; lia|].
destruct (Z.leb_spec n 3968); [change (Z.shiftl 16 3) with 128; lia|].
destruct (Z.leb_spec n 16128); [change (Z.shiftl 16 4) with 256; lia|].
destruct (Z.leb_spec n 32256); [change (Z.shiftl 16 5) with 512; lia|].
destruct (Z.leb_spec n 64512); [change (Z.shiftl 16 6) with 1024; lia|]. lia.
Qed.

Lemma geom_h : forall n, 0 <= n -> from_primary n = true ->
  16 <= rz_size n <= 2048 /\ rz_size n mod 16 = 0 /\ 1 <= req_size n /\ n <= req_size n /\
  rz_size n + req_size n <= class_size (chunk_class n).
Proof.
intros n Hn0 FP. pose proof (rz_size_bounds n) as [R1 R2]. pose proof (req_size_bounds n Hn0) as (Q1 & Q2 & Q3).
pose proof (primary_geometry n Hn0 FP) as (_ & [G1 G2] & _). lia.
Qed.

Lemma rz_size_small : forall n, n <= 48 -> rz_size n = 16.
Proof. intros n Hn. unfold rz_size, rz_log. destruct (Z.leb_spec n 48); [reflexivity | lia]. Qed.

Lemma req_size_max : forall n, 0 <= n -> req_size n = Z.max n 1.
Proof. intros n Hn. unfold req_size. destruct (Z.eqb_spec n 0); lia. Qed.

Lemma req_size_pos : forall n, 1 <= n -> req_size n = n.
Proof. intros n Hn. unfold req_size. destruct (Z.eqb_spec n 0); lia. Qed.

(* The header's second byte the hit walk writes (AGis.v:67 / AGj6.v:67; AFis.hdr_byte1_ok's check). *)
Lemma hdr_byte1_g_ok : forall jb, 0 <= jb <= 255 -> 0 <= ImgBaseAG.hdr_byte1 jb < 256 /\ Z.land (ImgBaseAG.hdr_byte1 jb) 127 = 17.
Proof.
intros jb Hjb.
assert (C : forallb (fun i => let b := ImgBaseAG.hdr_byte1 (Z.of_nat i) in (0 <=? b) && (b <? 256) && (Z.land b 127 =? 17)) (seq 0 256) = true)
  by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) C (Z.to_nat jb) ltac:(apply in_seq; lia)) as Hx. cbn beta in Hx. rewrite Z2Nat.id in Hx by lia.
apply andb_prop in Hx as [Hx H3]. apply andb_prop in Hx as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.eqb_eq in H3. lia.
Qed.

(* The tick keeps ARmcf's two cells: they read st_regions and st_secs, which the tick leaves alone. *)
Lemma cells_tick : forall B ly S rd, exh_cell_cf B ly S rd -> errb_cells_cf B ly S rd ->
  exh_cell_cf B ly (set_nev (st_nev S + 1) S) rd /\ errb_cells_cf B ly (set_nev (st_nev S + 1) S) rd.
Proof.
intros B ly S rd HE HR. split.
- exact (exh_cell_cf_frame B ly ly S _ rd rd HE (fun c => eq_refl) (fun c _ => eq_refl)).
- exact (errb_cells_cf_frame B ly ly S _ rd rd HR eq_refl eq_refl eq_refl eq_refl (fun a _ => eq_refl) (fun a H => H)).
Qed.

(* The tick keeps ARcf: Wf_cf's lower bounds on the event count survive it (YG02cf.WfP_cf_tick), and the two cells
   (cells_tick). *)
Lemma ARcf_tick_h : forall B ly S Hp W mem md,
  ARcf im_segs B ly S Hp W mem md -> ARcf im_segs B ly (set_nev (st_nev S + 1) S) Hp W mem md.
Proof.
intros B ly S Hp W mem md (M & L & (B1 & B2 & B3) & MW & HS).
split; [|split; [|split; [|split; [exact MW | exact HS]]]].
- pose proof (amc_wf _ _ _ _ _ M) as WM.
  pose proof (cells_tick B ly S _ (amc_exh_cell _ _ _ _ _ M) (amc_errb_cells _ _ _ _ _ M)) as [CE CR].
  destruct M. constructor; try assumption. exact (YG02cf.WfP_cf_tick _ _ _ _ _ WM).
- destruct L. constructor; assumption.
- split; [|exact (conj B2 B3)].
  rewrite (abudget_cf_frame S (set_nev (st_nev S + 1) S) eq_refl eq_refl eq_refl eq_refl). exact B1.
Qed.

(* The cached chunk's offset is a multiple of 32 (AGiy.off_aligned over ARmcf's Wf_cf). *)
Lemma off_split_cf : forall B ly S Hp rd n l off, ARmcf B ly S Hp rd -> 0 <= n -> from_primary n = true ->
  pc_chunks (cache S (chunk_class n)) = l ++ [off] -> off mod 32 = 0 /\ off = 16 * (off / 16).
Proof.
intros B ly S Hp rd n l off M Hn0 FP Hcache.
pose proof (primary_geometry n Hn0 FP) as (G1 & G2 & G3 & G4 & G5).
pose proof (wfc_classes _ _ _ _ _ (amc_wf _ _ _ _ _ M) (chunk_class n) ltac:(lia)) as CL.
pose proof (wrc_elems _ _ _ _ _ _ CL) as EL.
assert (IN : In off (pc_chunks (cache S (chunk_class n)))) by (rewrite Hcache; apply in_or_app; right; left; reflexivity).
pose proof (proj1 (Forall_forall _ _) EL off ltac:(apply in_app_iff; right; apply in_app_iff; left; exact IN)) as [O1 O2].
assert (A32 : off mod 32 = 0).
{ apply Z.mod_divide in O2 as [q Hq]; [|lia]. apply Z.mod_divide in G4 as [r Hr]; [|lia].
  rewrite Hq, Hr. replace (q * (r * 32)) with ((q * r) * 32) by lia. apply Z_mod_mult. }
split; [exact A32|]. apply Z.mod_divide in A32 as [q Hq]; [|lia]. rewrite Hq.
replace (q * 32) with ((q * 2) * 16) by lia. rewrite Z.div_mul by lia. lia.
Qed.

(* ================================================================================================================ *)
(* 1. The unit's premises, and the bridges from the hit walk's post to ARcf.                                       *)
Section b.
Variable B : asyms.
(* the unit's instance object (YGcfInstBase's IOK) *)
Variable IOK : Z -> Prop.

(* ---- the premises the bridges use (YGcfInstHitPost.v's Section t) ---- *)
(* the ledger's image window covers the image (the kit's name) *)
Hypothesis HIMG : YGcfDIface.IMG_COVER.
(* the shadow offset the interface reads is the model's *)
Hypothesis HSHB : ag_shadow = SHADOW_OFF.
(* the depot's write zone lies in the owned static ranges and the depot's two blocks *)
Hypothesis HDZO : forall ly' a, ag_dzone ly' a ->
  Exists (in_zr a) (as_owned_static B) \/ (ly_NB ly' <= a < ly_NB ly' + kNodesBlockSize) \/ (ly_SB ly' <= a < ly_SB ly' + kStoreBlockSize).
(* the depot's write zone misses the instance object and the internal allocator's cells *)
Hypothesis HDZX : forall ly' a, layout_ok ly' -> im_img_cover ly' -> ag_dzone ly' a ->
  ~ (as_inst B <= a < as_inst B + 3632) /\ ~ (as_ialloc_lo B <= a < as_ialloc_hi B) /\ ~ (as_ialloc_flag B <= a < as_ialloc_flag B + 2).
(* StackDepotPut's footprint is in the depot's write zone *)
Hypothesis HFP : forall ly' a, layout_ok ly' -> im_img_cover ly' -> ly_tsd ly' = as_tsd B ->
  CLdepot.depot_footprint B ly' a -> ag_dzone ly' a.
(* the constant cells miss the thread cells the hit walk writes *)
Hypothesis HCW : forall ly' c j cl', layout_ok ly' -> im_img_cover ly' -> ly_tsd ly' = as_tsd B ->
  In c (as_const B ly') -> 0 <= j < Z.max 1 (Z.of_nat (c_w c)) -> 1 <= cl' <= 31 ->
  ~ ImgBaseAG.WINT ly' cl' (aeval B ly' (c_at c) + j).

(* ---- the premises the interfaces add ---- *)
(* the TSD slot of the symbol table is the image class's *)
Hypothesis HTSD : as_tsd B = im_tsd.
(* the unit's instance object is the binary's allocator object (YGcfInstBase.IOK_ok) *)
Hypothesis IOK_inst : IOK_ok B IOK.
(* the binary's allocator object is in AGImg's instance window *)
Hypothesis INST_AG : ag_inst_ok (as_inst B).
(* the instance object's constant cells, wherever the constant cells hold (CfInstSec's INST_CELLS text) *)
Definition INST_CELLS_t : Prop := forall ly (H : word -> bool) (mem : word -> option byte), layout_ok ly -> ly_tsd ly = as_tsd B ->
  Forall (cell_holds B ly (aview im_segs H mem)) (as_const B ly) ->
  val_mem im_segs (mrestrict H mem) (as_inst B + o_space) 8 (ly_space ly) /\
  val_mem im_segs (mrestrict H mem) (as_inst B + 0xe20) 8 0x10000000000 /\
  val_mem im_segs (mrestrict H mem) (as_inst B + 0xe28) 8 0x108000010 /\
  val_mem im_segs (mrestrict H mem) (as_inst B + o_sec) 8 4096 /\
  val_mem im_segs (mrestrict H mem) (as_inst B + o_sec_chunks) 8 (ly_Q ly) /\
  val_mem im_segs (mrestrict H mem) (as_inst B + 80) 8 (ly_Q ly) /\
  val_mem im_segs (mrestrict H mem) (as_inst B + 88) 8 kPtrArrayResv /\
  val_mem im_segs (mrestrict H mem) (as_inst B + o_sec_mutex + 1) 3 0.
Hypothesis INST_CELLS : INST_CELLS_t.
(* the unit's depot field at the cf relation (YGcfInstDepot.if_depot_cf gives it) *)
Hypothesis HDEP : forall Hp, CLdepot.depot_field im_segs ag_depot_put im_tp B (ARXq_cf B IOK Hp) (U_cf B) ag_dzone
  (fun ly a => ag_dzone ly a \/ ag_czone ly a).
(* errno (ifaceE): the symbol facts, errno in the image window, errno apart from the depot's write zone *)
Hypothesis TS : im_syms B.
Hypothesis EII : ErrnoApart.errno_in_img.
Hypothesis EDZ : ErrnoApart.errno_apart_dzone_ag.
(* The hit post's ARcf carries ARmcf's two machine cells (amc_exh_cell / amc_errb_cells, field round 2) from the
   pre-state's, with the rows amc_cells_owned holds; the one row the relation does not hold is the errbuf object's
   separation from the depot's write zone (ag_dzone, a class field): ERRB_AG, the ag_dzone part of the row
   YGcfErrbSep.ERRB_SEP_t (the unit gives YGcfErrbSep.ERRB_SEP_ag B ERRB_SEP). *)
Hypothesis ERRB_AG : forall ly' a, layout_ok ly' -> im_img_cover ly' -> ly_tsd ly' = as_tsd B -> ag_dzone ly' a ->
  ~ (cf_errbuf_obj <= a < cf_errbuf_obj + 56).
(* Printf's two writable image cells (ARmcf's amc_pf_cells, field round 3) lie off the depot's write zone: ERRB_AG's
   twin for their 16 bytes (pf_cells_owned_t places them in the owned static data only). *)
Hypothesis PF_AG : forall ly' a, layout_ok ly' -> im_img_cover ly' -> ly_tsd ly' = as_tsd B -> ag_dzone ly' a ->
  ~ (cf_toolname_cell <= a < cf_toolname_cell + 8 \/ cf_pfcb_cell <= a < cf_pfcb_cell + 8).

(* ---- the g post (AGj1.AR_final's role): at_RETw at a pop state X gives ARcf at the final state ---- *)
Lemma hit_bridge_g : forall Hp ly X W mem0 md0 n tr l off (regs0 : bvmap 5 word) jb odd z (regs' : bvmap 5 word) mem' mat
  (DPOST : Z -> (word -> option byte) -> Prop),
  ARcf im_segs B ly X Hp W mem0 md0 -> 49 <= n <= 64512 -> st_cache_inited X = true ->
  pc_chunks (cache X (chunk_class n)) = l ++ [off] -> wframe W ly regs0 mem0 tr -> 0 <= jb <= 255 ->
  at_RETw W ly regs0 mem0 md0 n (chunk_class n) (Z.of_nat (length (l ++ [off]))) (off / 16) jb (rz_log n) DPOST odd z W
    (mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom im_segs)) (with_vm_backing (m_vm_lazy md0) mat md0)) ->
  (forall z0 m, DPOST z0 m -> CLdepot.depot_mem_ok B ly (CLdepot.depot_after z0 tr X) (aview im_segs (w_H W) m) /\
     Forall (cell_holds B ly (aview im_segs (w_H W) m)) (as_const B ly)) ->
  (odd = true <-> n mod 8 <> 0) ->
  Wf_cf (as_universe B) (ImgBaseAG.st_final X (chunk_class n) l off n tr z) ->
  ARcf im_segs B ly (ImgBaseAG.st_final X (chunk_class n) l off n tr z) Hp W mem' (with_vm_backing (m_vm_lazy md0) mat md0).
Proof.
intros Hp ly X W mem0 md0 n tr l off regs0 jb odd z regs' mem' mat DPOST HAR Nr Hinited Hcache WFR Hjb HRET HDP Hodd MPwf.
assert (Hn0 : 0 <= n) by lia. pose proof (prim_fp_cf n ltac:(lia)) as FP.
destruct (off_split_cf B ly X Hp _ n l off (proj1 HAR) Hn0 FP Hcache) as [_ Hoff].
set (cl := chunk_class n) in *. set (v := off / 16) in *. set (cnt := Z.of_nat (length (l ++ [off]))) in *.
pose proof (YGcfInstHitCore.RZ_rz_size n) as ERZ. pose proof (req_size_pos n ltac:(lia)) as EN.
assert (ESU : ImgBaseAG.SUv ly cl v (rz_log n) = YGcfInstHitPost.hSU ly cl v (rz_size n)).
{ unfold ImgBaseAG.SUv, ImgBaseAG.Uv, ImgBaseAG.SHBv, YGcfInstHitPost.hSU, shadow_addr. rewrite HSHB, ERZ. reflexivity. }
assert (EPB : ImgBaseAG.PBv ly n cl v (rz_log n) = YGcfInstHitPost.hPB ly cl v (rz_size n) (req_size n)).
{ unfold ImgBaseAG.PBv, ImgBaseAG.N8D, ImgBaseAG.SHBv, YGcfInstHitPost.hPB, shadow_addr. rewrite HSHB, ERZ, EN. reflexivity. }
destruct WFR as ((SP1 & SP2 & SP3 & SP4) & _ & _ & _ & _).
destruct HRET as [_ (regs'' & mem'' & mat'' & Ec & _ & _ & (memD & DP & PRD & EQD) & MEQ & PRS & PRW & HM)].
injection Ec as E1 E2 E3. subst regs'' mem'' mat''.
cbv zeta in HM. destruct HM as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10).
destruct (HDP z memD DP) as [DEPD CSTD].
assert (Hsp : ly_stk_lo ly + AFSTACK <= bv_unsigned (getr regs0 2) /\ bv_unsigned (getr regs0 2) <= ly_stk_hi ly) by exact (conj SP1 SP3).
assert (Hodd' : odd = true <-> req_size n mod 8 <> 0) by (rewrite EN; exact Hodd).
assert (MEQF : forall x : word,
  ~ YGcfInstHitPost.hWIN ly cl v (rz_size n) (req_size n) (bv_unsigned (getr regs0 2)) odd (bv_unsigned x) ->
  ~ ag_dzone ly (bv_unsigned x) ->
  ~ (ImgBaseAG.Kv ly cl v + rz_size n <= bv_unsigned x < ImgBaseAG.Kv ly cl v + rz_size n + req_size n) ->
  ~ (YGcfInstHitPost.hSU ly cl v (rz_size n) <= bv_unsigned x < YGcfInstHitPost.hSU ly cl v (rz_size n) + req_size n / 8 * 8 / 8) ->
  mem' x = mem0 x).
{ intros x H1 H2 H3 H4. apply MEQ; [| exact H2 | |].
  - intros Hw. apply H1. unfold ImgBaseAG.WIN, ImgBaseAG.PBW, ImgBaseAG.Uv in Hw. rewrite EPB, ERZ in Hw. exact Hw.
  - intros Hk. apply H3. rewrite ERZ in Hk. rewrite EN. exact Hk.
  - intros Hs. apply H4. unfold ImgBaseAG.N8D in Hs. rewrite ESU in Hs. rewrite EN. exact Hs. }
assert (PRW' : forall a, ImgBaseAG.WINT ly cl a \/ (ImgBaseAG.Kv ly cl v <= a < ImgBaseAG.Kv ly cl v + rz_size n + req_size n) \/
  (odd = true /\ YGcfInstHitPost.hPB ly cl v (rz_size n) (req_size n) <= a < YGcfInstHitPost.hPB ly cl v (rz_size n) (req_size n) + 1) ->
  apresent (w_H W) mem' a).
{ intros a Ha. apply PRW. unfold ImgBaseAG.PBW. rewrite EPB, ERZ.
  destruct Ha as [Ha|[Ha|Ha]]; [left; exact Ha | right; left; rewrite EN in Ha; exact Ha | right; right; exact Ha]. }
assert (HVMG : rz_size n <> 16 -> val_mem im_segs (mrestrict (w_H W) mem') (ImgBaseAG.Kv ly cl v) 8 0xCC6E96B9CC6E96B9 /\
  val_mem im_segs (mrestrict (w_H W) mem') (ImgBaseAG.Kv ly cl v + 8) 8 (ImgBaseAG.Kv ly cl v + rz_size n - 16))
  by (intros _; rewrite <- ERZ; exact (conj V1 V2)).
assert (HV3 : val_mem im_segs (mrestrict (w_H W) mem') (ImgBaseAG.Kv ly cl v + rz_size n - 16) 1 2) by (rewrite <- ERZ; exact V3).
assert (HV4 : exists b, val_mem im_segs (mrestrict (w_H W) mem') (ImgBaseAG.Kv ly cl v + rz_size n - 15) 1 b /\ 0 <= b < 256 /\ Z.land b 127 = 17).
{ exists (ImgBaseAG.hdr_byte1 jb). rewrite <- ERZ. destruct (hdr_byte1_g_ok jb Hjb) as [B1 B2]. exact (conj V4 (conj B1 B2)). }
assert (HV5 : val_mem im_segs (mrestrict (w_H W) mem') (ImgBaseAG.Kv ly cl v + rz_size n - 14) 2 0) by (rewrite <- ERZ; exact V5).
assert (HV6 : val_mem im_segs (mrestrict (w_H W) mem') (ImgBaseAG.Kv ly cl v + rz_size n - 12) 4 (req_size n)) by (rewrite <- ERZ, EN; exact V6).
assert (HV9 : forall x : word, YGcfInstHitPost.hSU ly cl v (rz_size n) <= bv_unsigned x <
  YGcfInstHitPost.hSU ly cl v (rz_size n) + req_size n / 8 * 8 / 8 -> mem' x = Some (Z_to_bv 8 0)).
{ intros x Hx. apply V9. unfold ImgBaseAG.N8D. rewrite ESU. rewrite EN in Hx. exact Hx. }
assert (HV10 : odd = true -> val_mem im_segs (mrestrict (w_H W) mem') (YGcfInstHitPost.hPB ly cl v (rz_size n) (req_size n)) 1 (req_size n mod 8)).
{ intros Ho. rewrite <- EPB, EN. exact (V10 Ho). }
exact (YGcfInstHitPost.hit_ARcf B ly X Hp W mem0 md0 n cl cnt v l off HAR Hn0 FP Hinited Hcache eq_refl eq_refl Hoff
  HIMG HDZO HDZX HFP HCW tr (bv_unsigned (getr regs0 2)) odd z mem' memD mat Hsp Hodd' MPwf DEPD CSTD PRD EQD MEQF PRS PRW'
  HVMG HV3 HV4 HV5 HV6 V7 V8 HV9 HV10 ERRB_AG PF_AG).
Qed.

(* if_post_miss's two cells (CfInstMiss): exh_cell_cf / errb_cells_cf at the final state's memory, ARmcf's fields of
   hit_bridge_g's post.  The pre-state's cells are not read (they are in ARcf's ARmcf); the statement keeps them so
   that callers do not move. *)
Lemma hit_cells_g : forall Hp ly X W mem0 md0 n tr l off (regs0 : bvmap 5 word) jb odd z (regs' : bvmap 5 word) mem' mat
  (DPOST : Z -> (word -> option byte) -> Prop),
  ARcf im_segs B ly X Hp W mem0 md0 -> 49 <= n <= 64512 -> st_cache_inited X = true ->
  pc_chunks (cache X (chunk_class n)) = l ++ [off] -> wframe W ly regs0 mem0 tr -> 0 <= jb <= 255 ->
  at_RETw W ly regs0 mem0 md0 n (chunk_class n) (Z.of_nat (length (l ++ [off]))) (off / 16) jb (rz_log n) DPOST odd z W
    (mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom im_segs)) (with_vm_backing (m_vm_lazy md0) mat md0)) ->
  (forall z0 m, DPOST z0 m -> CLdepot.depot_mem_ok B ly (CLdepot.depot_after z0 tr X) (aview im_segs (w_H W) m) /\
     Forall (cell_holds B ly (aview im_segs (w_H W) m)) (as_const B ly)) ->
  (odd = true <-> n mod 8 <> 0) ->
  Wf_cf (as_universe B) (ImgBaseAG.st_final X (chunk_class n) l off n tr z) ->
  exh_cell_cf B ly X (aview im_segs (w_H W) mem0) -> errb_cells_cf B ly X (aview im_segs (w_H W) mem0) ->
  exh_cell_cf B ly (ImgBaseAG.st_final X (chunk_class n) l off n tr z) (aview im_segs (w_H W) mem') /\
  errb_cells_cf B ly (ImgBaseAG.st_final X (chunk_class n) l off n tr z) (aview im_segs (w_H W) mem').
Proof.
intros Hp ly X W mem0 md0 n tr l off regs0 jb odd z regs' mem' mat DPOST HAR Nr Hinited Hcache WFR Hjb HRET HDP Hodd MPwf _ _.
pose proof (hit_bridge_g Hp ly X W mem0 md0 n tr l off regs0 jb odd z regs' mem' mat DPOST HAR Nr Hinited Hcache WFR Hjb HRET HDP Hodd MPwf)
  as (M' & _).
exact (conj (amc_exh_cell _ _ _ _ _ M') (amc_errb_cells _ _ _ _ _ M')).
Qed.

(* ---- the k post (AGjf's role): at_RETkw (0 <= n <= 48, redzone 16) ---- *)
Lemma hit_bridge_k : forall Hp ly X W mem0 md0 n tr l off (regs0 : bvmap 5 word) jb odd z (regs' : bvmap 5 word) mem' mat
  (DPOST : Z -> (word -> option byte) -> Prop),
  ARcf im_segs B ly X Hp W mem0 md0 -> 0 <= n <= 48 -> st_cache_inited X = true ->
  pc_chunks (cache X (chunk_class n)) = l ++ [off] -> wframe W ly regs0 mem0 tr -> 0 <= jb <= 255 ->
  at_RETkw W ly regs0 mem0 md0 n (chunk_class n) (Z.of_nat (length (l ++ [off]))) (off / 16) jb DPOST odd z W
    (mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom im_segs)) (with_vm_backing (m_vm_lazy md0) mat md0)) ->
  (forall z0 m, DPOST z0 m -> CLdepot.depot_mem_ok B ly (CLdepot.depot_after z0 tr X) (aview im_segs (w_H W) m) /\
     Forall (cell_holds B ly (aview im_segs (w_H W) m)) (as_const B ly)) ->
  (odd = true <-> K6.NPv n mod 8 <> 0) ->
  Wf_cf (as_universe B) (ImgBaseAG.st_final X (chunk_class n) l off n tr z) ->
  ARcf im_segs B ly (ImgBaseAG.st_final X (chunk_class n) l off n tr z) Hp W mem' (with_vm_backing (m_vm_lazy md0) mat md0).
Proof.
intros Hp ly X W mem0 md0 n tr l off regs0 jb odd z regs' mem' mat DPOST HAR Nr Hinited Hcache WFR Hjb HRET HDP Hodd MPwf.
assert (Hn0 : 0 <= n) by lia. pose proof (prim_fp_cf n ltac:(lia)) as FP.
destruct (off_split_cf B ly X Hp _ n l off (proj1 HAR) Hn0 FP Hcache) as [_ Hoff].
set (cl := chunk_class n) in *. set (v := off / 16) in *. set (cnt := Z.of_nat (length (l ++ [off]))) in *.
assert (ERZ : K6.RZ = rz_size n) by (unfold K6.RZ; symmetry; apply rz_size_small; lia).
assert (EN : K6.NPv n = req_size n) by (unfold K6.NPv; symmetry; apply req_size_max; exact Hn0).
assert (ESU : K6.SUv ly cl v = YGcfInstHitPost.hSU ly cl v (rz_size n)).
{ unfold K6.SUv, K6.Uv, ImgBaseAG.SHBv, YGcfInstHitPost.hSU, shadow_addr. rewrite HSHB, ERZ. reflexivity. }
assert (EPB : K6.PBv ly n cl v = YGcfInstHitPost.hPB ly cl v (rz_size n) (req_size n)).
{ unfold K6.PBv, K6.N8D, ImgBaseAG.SHBv, YGcfInstHitPost.hPB, shadow_addr. rewrite HSHB, ERZ, EN. reflexivity. }
destruct WFR as ((SP1 & SP2 & SP3 & SP4) & _ & _ & _ & _).
destruct HRET as [_ (regs'' & mem'' & mat'' & Ec & _ & _ & (memD & DP & PRD & EQD) & MEQ & PRS & PRW & HM)].
injection Ec as E1 E2 E3. subst regs'' mem'' mat''.
cbv zeta in HM. destruct HM as (V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10).
destruct (HDP z memD DP) as [DEPD CSTD].
assert (Hsp : ly_stk_lo ly + AFSTACK <= bv_unsigned (getr regs0 2) /\ bv_unsigned (getr regs0 2) <= ly_stk_hi ly) by exact (conj SP1 SP3).
assert (Hodd' : odd = true <-> req_size n mod 8 <> 0) by (rewrite <- EN; exact Hodd).
assert (MEQF : forall x : word,
  ~ YGcfInstHitPost.hWIN ly cl v (rz_size n) (req_size n) (bv_unsigned (getr regs0 2)) odd (bv_unsigned x) ->
  ~ ag_dzone ly (bv_unsigned x) ->
  ~ (ImgBaseAG.Kv ly cl v + rz_size n <= bv_unsigned x < ImgBaseAG.Kv ly cl v + rz_size n + req_size n) ->
  ~ (YGcfInstHitPost.hSU ly cl v (rz_size n) <= bv_unsigned x < YGcfInstHitPost.hSU ly cl v (rz_size n) + req_size n / 8 * 8 / 8) ->
  mem' x = mem0 x).
{ intros x H1 H2 H3 H4. apply MEQ; [| exact H2 | |].
  - intros Hw. apply H1. unfold K6.WIN, K6.PBW, K6.Uv in Hw. rewrite EPB, ERZ in Hw. exact Hw.
  - intros Hk. apply H3. rewrite ERZ, EN in Hk. exact Hk.
  - intros Hs. apply H4. unfold K6.N8D in Hs. rewrite ESU, EN in Hs. exact Hs. }
assert (PRW' : forall a, ImgBaseAG.WINT ly cl a \/ (ImgBaseAG.Kv ly cl v <= a < ImgBaseAG.Kv ly cl v + rz_size n + req_size n) \/
  (odd = true /\ YGcfInstHitPost.hPB ly cl v (rz_size n) (req_size n) <= a < YGcfInstHitPost.hPB ly cl v (rz_size n) (req_size n) + 1) ->
  apresent (w_H W) mem' a).
{ intros a Ha. apply PRW. unfold K6.PBW. rewrite EPB, ERZ, EN. exact Ha. }
assert (HVMG : rz_size n <> 16 -> val_mem im_segs (mrestrict (w_H W) mem') (ImgBaseAG.Kv ly cl v) 8 0xCC6E96B9CC6E96B9 /\
  val_mem im_segs (mrestrict (w_H W) mem') (ImgBaseAG.Kv ly cl v + 8) 8 (ImgBaseAG.Kv ly cl v + rz_size n - 16))
  by (intros H16; exfalso; apply H16; rewrite <- ERZ; reflexivity).
assert (HV3 : val_mem im_segs (mrestrict (w_H W) mem') (ImgBaseAG.Kv ly cl v + rz_size n - 16) 1 2) by (rewrite <- ERZ; exact V3).
assert (HV4 : exists b, val_mem im_segs (mrestrict (w_H W) mem') (ImgBaseAG.Kv ly cl v + rz_size n - 15) 1 b /\ 0 <= b < 256 /\ Z.land b 127 = 17).
{ exists (K6.hdr_byte1 jb). rewrite <- ERZ. destruct (hdr_byte1_g_ok jb Hjb) as [B1 B2]. exact (conj V4 (conj B1 B2)). }
assert (HV5 : val_mem im_segs (mrestrict (w_H W) mem') (ImgBaseAG.Kv ly cl v + rz_size n - 14) 2 0) by (rewrite <- ERZ; exact V5).
assert (HV6 : val_mem im_segs (mrestrict (w_H W) mem') (ImgBaseAG.Kv ly cl v + rz_size n - 12) 4 (req_size n)) by (rewrite <- ERZ, <- EN; exact V6).
assert (HV9 : forall x : word, YGcfInstHitPost.hSU ly cl v (rz_size n) <= bv_unsigned x <
  YGcfInstHitPost.hSU ly cl v (rz_size n) + req_size n / 8 * 8 / 8 -> mem' x = Some (Z_to_bv 8 0)).
{ intros x Hx. apply V9. unfold K6.N8D. rewrite ESU, EN. exact Hx. }
assert (HV10 : odd = true -> val_mem im_segs (mrestrict (w_H W) mem') (YGcfInstHitPost.hPB ly cl v (rz_size n) (req_size n)) 1 (req_size n mod 8)).
{ intros Ho. rewrite <- EPB, <- EN. exact (V10 Ho). }
exact (YGcfInstHitPost.hit_ARcf B ly X Hp W mem0 md0 n cl cnt v l off HAR Hn0 FP Hinited Hcache eq_refl eq_refl Hoff
  HIMG HDZO HDZX HFP HCW tr (bv_unsigned (getr regs0 2)) odd z mem' memD mat Hsp Hodd' MPwf DEPD CSTD PRD EQD MEQF PRS PRW'
  HVMG HV3 HV4 HV5 HV6 V7 V8 HV9 HV10 ERRB_AG PF_AG).
Qed.

(* if_post_miss_k's two cells (CfInstMiss), ARmcf's fields of hit_bridge_k's post. *)
Lemma hit_cells_k : forall Hp ly X W mem0 md0 n tr l off (regs0 : bvmap 5 word) jb odd z (regs' : bvmap 5 word) mem' mat
  (DPOST : Z -> (word -> option byte) -> Prop),
  ARcf im_segs B ly X Hp W mem0 md0 -> 0 <= n <= 48 -> st_cache_inited X = true ->
  pc_chunks (cache X (chunk_class n)) = l ++ [off] -> wframe W ly regs0 mem0 tr -> 0 <= jb <= 255 ->
  at_RETkw W ly regs0 mem0 md0 n (chunk_class n) (Z.of_nat (length (l ++ [off]))) (off / 16) jb DPOST odd z W
    (mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom im_segs)) (with_vm_backing (m_vm_lazy md0) mat md0)) ->
  (forall z0 m, DPOST z0 m -> CLdepot.depot_mem_ok B ly (CLdepot.depot_after z0 tr X) (aview im_segs (w_H W) m) /\
     Forall (cell_holds B ly (aview im_segs (w_H W) m)) (as_const B ly)) ->
  (odd = true <-> K6.NPv n mod 8 <> 0) ->
  Wf_cf (as_universe B) (ImgBaseAG.st_final X (chunk_class n) l off n tr z) ->
  exh_cell_cf B ly X (aview im_segs (w_H W) mem0) -> errb_cells_cf B ly X (aview im_segs (w_H W) mem0) ->
  exh_cell_cf B ly (ImgBaseAG.st_final X (chunk_class n) l off n tr z) (aview im_segs (w_H W) mem') /\
  errb_cells_cf B ly (ImgBaseAG.st_final X (chunk_class n) l off n tr z) (aview im_segs (w_H W) mem').
Proof.
intros Hp ly X W mem0 md0 n tr l off regs0 jb odd z regs' mem' mat DPOST HAR Nr Hinited Hcache WFR Hjb HRET HDP Hodd MPwf _ _.
pose proof (hit_bridge_k Hp ly X W mem0 md0 n tr l off regs0 jb odd z regs' mem' mat DPOST HAR Nr Hinited Hcache WFR Hjb HRET HDP Hodd MPwf)
  as (M' & _).
exact (conj (amc_exh_cell _ _ _ _ _ M') (amc_errb_cells _ _ _ _ _ M')).
Qed.

(* ================================================================================================================ *)
(* 2. The fields, in AGif1's order.                                                                                 *)
Section f.
Variable Hp : list Z.

(* The instance object's three cells the hit seed reads, from ARcf's constant cells. *)
Lemma inst_cells_cf : forall inst ly S W mem md, IOK inst -> ARcf im_segs B ly S Hp W mem md ->
  val_mem im_segs (mrestrict (w_H W) mem) (inst + 0x20) 8 (ly_space ly) /\
  val_mem im_segs (mrestrict (w_H W) mem) (inst + 0xe20) 8 0x10000000000 /\
  val_mem im_segs (mrestrict (w_H W) mem) (inst + 0xe28) 8 0x108000010.
Proof.
intros inst ly S W mem md HI (M & _). rewrite (IOK_inst inst HI).
destruct (INST_CELLS ly (w_H W) mem (amc_layout _ _ _ _ _ M) (amc_tsd _ _ _ _ _ M) (amc_const _ _ _ _ _ M)) as (C1 & C2 & C3 & _).
exact (conj C1 (conj C2 C3)).
Qed.

Lemma inst_cf : forall inst ly S W mem md, ARXq_cf B IOK Hp inst ly S W mem md -> ag_inst_ok inst.
Proof. intros inst ly S W mem md HX. rewrite (IOK_inst inst (ARXq_cf_iok B IOK Hp inst ly S W mem md HX)). exact INST_AG. Qed.

(* (a) *)
Lemma view_cf : forall inst ly S W mem md n l off,
  ARXq_cf B IOK Hp inst ly S W mem md -> 0 <= n -> from_primary n = true ->
  st_cache_inited S = true -> pc_chunks (cache S (chunk_class n)) = l ++ [off] ->
  off mod 32 = 0 /\ hview B W ly inst mem (chunk_class n) (Z.of_nat (length (l ++ [off]))) (off / 16).
Proof.
intros inst ly S W mem md n l off HX Hn0 FP Hinited Hcache.
pose proof (ARXq_cf_ARcf B IOK Hp inst ly S W mem md HX) as HAR.
pose proof (ARXq_cf_iok B IOK Hp inst ly S W mem md HX) as HI.
destruct (off_split_cf B ly S Hp _ n l off (proj1 HAR) Hn0 FP Hcache) as [A32 Hoff].
split; [exact A32|].
exact (YGcfInstHitCore.hview_cf B ly S Hp W mem md n (chunk_class n) (Z.of_nat (length (l ++ [off]))) (off / 16) l off
  HAR Hn0 FP Hinited Hcache eq_refl eq_refl Hoff inst HIMG HTSD HSHB (inst_cells_cf inst ly S W mem md HI HAR)).
Qed.

(* The depot callee (AGif1.depot_cgif): the unit's depot field at the cf relation. *)
Lemma depot_cf : CLdepot.depot_field im_segs ag_depot_put im_tp B (ARXq_cf B IOK Hp) (U_cf B) ag_dzone
  (fun ly a => ag_dzone ly a \/ ag_czone ly a).
Proof. exact (HDEP Hp). Qed.

(* (c) The common part of the two posts: malloc_cf's contract along the path, the tick, the errbuf map, qtight. *)
Lemma post_common : forall inst ly S W mem0 md0 n tr l off z mem' mat,
  ARXq_cf B IOK Hp inst ly S W mem0 md0 -> rpre_cf B S n -> 0 <= n < cf_malloc_max -> blocks_bytes S + n <= LIVE_MAX ->
  U_cf B tr S ->
  (exists trc, apath (malloc_cf n tr S) trc
    (ck_user (ImgBaseAG.new_chunk (chunk_class n) off n), ImgBaseAG.st_final (set_nev (st_nev S + 1) S) (chunk_class n) l off n tr z) /\
    gflag trc = true) ->
  (ARcf im_segs B ly (set_nev (st_nev S + 1) S) Hp W mem0 md0 ->
   Wf_cf (as_universe B) (ImgBaseAG.st_final (set_nev (st_nev S + 1) S) (chunk_class n) l off n tr z) ->
   ARcf im_segs B ly (ImgBaseAG.st_final (set_nev (st_nev S + 1) S) (chunk_class n) l off n tr z) Hp W mem'
     (with_vm_backing (m_vm_lazy md0) mat md0)) ->
  ARXq_cf B IOK Hp inst ly (ImgBaseAG.st_final (set_nev (st_nev S + 1) S) (chunk_class n) l off n tr z) W mem'
    (with_vm_backing (m_vm_lazy md0) mat md0) /\
  qtight (ImgBaseAG.st_final (set_nev (st_nev S + 1) S) (chunk_class n) l off n tr z).
Proof.
intros inst ly S W mem0 md0 n tr l off z mem' mat HX HR Hn Hlive HU [trc [HP _]] TR.
pose proof (ARXq_cf_iok B IOK Hp inst ly S W mem0 md0 HX) as HI.
pose proof (ARXq_cf_ARcf B IOK Hp inst ly S W mem0 md0 HX) as HAR.
pose proof (ARXq_cf_xsm B IOK Hp inst ly S W mem0 md0 HX) as HXM.
pose proof (ARXq_cf_qtight B IOK Hp inst ly S W mem0 md0 HX) as HQ.
destruct HR as (HUok & HWF & (R1 & R2 & R3) & _).
pose proof (YG07cf.malloc_gen_cf (as_universe B) S n tr HUok HWF Hn Hlive HU R1 R2 R3) as AT.
destruct (YGcfTok.atok_cf_apath _ _ _ _ _ AT HP) as [ns [MP _]].
unfold YG07cf.malloc_post_cf in MP. cbv beta iota in MP. destruct MP as (WF' & _ & _ & _ & _ & QT).
pose proof (QT HQ) as QT'.
split; [|exact QT'].
apply ARXq_cf_start; [exact HI | exact (TR (ARcf_tick_h B ly S Hp W mem0 md0 HAR) WF') | | exact QT'].
apply (YGcfXsMapped.xs_mapped_cf_grow ly S md0 ly _ _ HXM); [|apply YGcfXsMapped.mkeep_wvb].
apply YGcfXsMapped.xs_cf_secs. unfold ImgBaseAG.st_final, ImgBaseAG.depot_after, ImgBaseAG.st_popped. destruct (z =? 0); reflexivity.
Qed.

(* The depot post at the entry state gives the bridges' depot premise at the post-tick state (the tick keeps the
   depot). *)
Lemma dpost_tick : forall inst ly S W tr z0 m, dpost_cf B inst ly S W tr z0 m ->
  CLdepot.depot_mem_ok B ly (CLdepot.depot_after z0 tr (set_nev (st_nev S + 1) S)) (aview im_segs (w_H W) m) /\
  Forall (cell_holds B ly (aview im_segs (w_H W) m)) (as_const B ly).
Proof.
intros inst ly S W tr z0 m (A & D & C). split; [|exact C].
apply (YGcfInstHitPost.depot_mem_ok_ext_h B ly (CLdepot.depot_after z0 tr S)); [|exact D].
unfold CLdepot.depot_after. destruct (z0 =? 0); reflexivity.
Qed.

Lemma post_cf : forall inst ly S W mem0 md0 n tr l off (regs0 : bvmap 5 word) jb odd z (regs' : bvmap 5 word) mem' mat,
  ARXq_cf B IOK Hp inst ly S W mem0 md0 -> rpre_cf B S n -> n < cf_malloc_max -> blocks_bytes S + n <= LIVE_MAX -> U_cf B tr S ->
  49 <= n <= 64512 -> st_cache_inited S = true -> pc_chunks (cache S (chunk_class n)) = l ++ [off] ->
  wframe W ly regs0 mem0 tr ->
  0 <= jb <= 255 ->
  val_mem im_segs (mrestrict (w_H W) mem0) (Kv ly (chunk_class n) (off / 16) + RZ (rz_log n) - 15) 1 jb ->
  at_RETw W ly regs0 mem0 md0 n (chunk_class n) (Z.of_nat (length (l ++ [off]))) (off / 16) jb (rz_log n)
    (fun z m => dpost_cf B inst ly S W tr z m) odd z W
    (mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom im_segs)) (with_vm_backing (m_vm_lazy md0) mat md0)) ->
  (odd = true <-> n mod 8 <> 0) ->
  (exists trc, apath (malloc_cf n tr S) trc
    (ck_user (new_chunk (chunk_class n) off n), st_final (set_nev (st_nev S + 1) S) (chunk_class n) l off n tr z) /\
    gflag trc = true) ->
  ARXq_cf B IOK Hp inst ly (st_final (set_nev (st_nev S + 1) S) (chunk_class n) l off n tr z) W mem' (with_vm_backing (m_vm_lazy md0) mat md0) /\
  qtight (st_final (set_nev (st_nev S + 1) S) (chunk_class n) l off n tr z).
Proof.
intros inst ly S W mem0 md0 n tr l off regs0 jb odd z regs' mem' mat HX HR Hmax Hlive HU Nr Hinited Hcache WFR Hjb _ HRET Hodd HPATH.
apply (post_common inst ly S W mem0 md0 n tr l off z mem' mat HX HR ltac:(lia) Hlive HU HPATH).
intros HAR1 WF'.
exact (hit_bridge_g Hp ly (set_nev (st_nev S + 1) S) W mem0 md0 n tr l off regs0 jb odd z regs' mem' mat
  (fun z0 m => dpost_cf B inst ly S W tr z0 m) HAR1 Nr Hinited Hcache WFR Hjb HRET
  (fun z0 m H => dpost_tick inst ly S W tr z0 m H) Hodd WF').
Qed.

(* (d) *)
Lemma owned_cf : forall inst ly S W mem md n l off odd a,
  ARXq_cf B IOK Hp inst ly S W mem md -> 49 <= n <= 64512 ->
  st_cache_inited S = true -> pc_chunks (cache S (chunk_class n)) = l ++ [off] ->
  0 <= a < 2 ^ 64 -> (odd = true -> n mod 8 <> 0) ->
  hit_writes ly n (chunk_class n) (off / 16) (rz_log n) odd a -> AOX_cf B ly S a.
Proof.
intros inst ly S W mem md n l off odd a HX Nr Hinited Hcache _ Hodd Hw.
pose proof (ARXq_cf_ARcf B IOK Hp inst ly S W mem md HX) as HAR.
assert (Hn0 : 0 <= n) by lia. pose proof (prim_fp_cf n ltac:(lia)) as FP.
destruct (off_split_cf B ly S Hp _ n l off (proj1 HAR) Hn0 FP Hcache) as [_ Hoff].
pose proof (geom_h n Hn0 FP) as (R1 & R2 & Q1 & Q2 & G).
pose proof (YGcfInstHitCore.RZ_rz_size n) as ERZ. pose proof (req_size_pos n ltac:(lia)) as EN.
unfold AOX_cf. left.
exact (YGcfInstHitCore.hit_owned_g B ly S Hp W mem md n (chunk_class n) (Z.of_nat (length (l ++ [off]))) (off / 16) l off
  HAR Hn0 FP Hinited Hcache eq_refl eq_refl Hoff (ImgBaseAG.RZ (rz_log n)) n
  ltac:(rewrite ERZ; lia) ltac:(rewrite ERZ; exact R2) Hn0 ltac:(rewrite ERZ; lia) HSHB HDZO (rz_log n) odd a eq_refl eq_refl Hodd Hw).
Qed.

(* An uninited per-thread cache is empty (Wf_cf's class invariant). *)
Lemma uninit_cf : forall inst ly S W mem md c, ARXq_cf B IOK Hp inst ly S W mem md -> 1 <= c <= 31 ->
  st_cache_inited S = false -> pc_chunks (cache S c) = [].
Proof.
intros inst ly S W mem md c HX Hc CI.
exact (YGcfInstHitCore.uninit_cf _ _ _ _ S c (ARX_cf_wf B IOK Hp inst ly S W mem md (ARXq_cf_ARX B IOK Hp inst ly S W mem md HX)) Hc CI).
Qed.

(* The k path's (c) and (d) (AGif1k.v). *)
Lemma post_cf_k : forall inst ly S W mem0 md0 n tr l off (regs0 : bvmap 5 word) jb odd z (regs' : bvmap 5 word) mem' mat,
  ARXq_cf B IOK Hp inst ly S W mem0 md0 -> rpre_cf B S n -> n < cf_malloc_max -> blocks_bytes S + n <= LIVE_MAX -> U_cf B tr S ->
  0 <= n <= 48 -> st_cache_inited S = true -> pc_chunks (cache S (chunk_class n)) = l ++ [off] ->
  wframe W ly regs0 mem0 tr ->
  0 <= jb <= 255 ->
  val_mem im_segs (mrestrict (w_H W) mem0) (K6.Kv ly (chunk_class n) (off / 16) + K6.RZ - 15) 1 jb ->
  at_RETkw W ly regs0 mem0 md0 n (chunk_class n) (Z.of_nat (length (l ++ [off]))) (off / 16) jb
    (fun z m => dpost_cf B inst ly S W tr z m) odd z W
    (mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom im_segs)) (with_vm_backing (m_vm_lazy md0) mat md0)) ->
  (odd = true <-> K6.NPv n mod 8 <> 0) ->
  (exists trc, apath (malloc_cf n tr S) trc
    (ck_user (new_chunk (chunk_class n) off n), st_final (set_nev (st_nev S + 1) S) (chunk_class n) l off n tr z) /\
    gflag trc = true) ->
  ARXq_cf B IOK Hp inst ly (st_final (set_nev (st_nev S + 1) S) (chunk_class n) l off n tr z) W mem' (with_vm_backing (m_vm_lazy md0) mat md0) /\
  qtight (st_final (set_nev (st_nev S + 1) S) (chunk_class n) l off n tr z).
Proof.
intros inst ly S W mem0 md0 n tr l off regs0 jb odd z regs' mem' mat HX HR Hmax Hlive HU Nr Hinited Hcache WFR Hjb _ HRET Hodd HPATH.
apply (post_common inst ly S W mem0 md0 n tr l off z mem' mat HX HR ltac:(lia) Hlive HU HPATH).
intros HAR1 WF'.
exact (hit_bridge_k Hp ly (set_nev (st_nev S + 1) S) W mem0 md0 n tr l off regs0 jb odd z regs' mem' mat
  (fun z0 m => dpost_cf B inst ly S W tr z0 m) HAR1 Nr Hinited Hcache WFR Hjb HRET
  (fun z0 m H => dpost_tick inst ly S W tr z0 m H) Hodd WF').
Qed.

Lemma owned_cf_k : forall inst ly S W mem md n l off odd a,
  ARXq_cf B IOK Hp inst ly S W mem md -> 0 <= n <= 48 ->
  st_cache_inited S = true -> pc_chunks (cache S (chunk_class n)) = l ++ [off] ->
  0 <= a < 2 ^ 64 -> (odd = true -> K6.NPv n mod 8 <> 0) ->
  hit_writes_k ly n (chunk_class n) (off / 16) odd a -> AOX_cf B ly S a.
Proof.
intros inst ly S W mem md n l off odd a HX Nr Hinited Hcache _ Hodd Hw.
pose proof (ARXq_cf_ARcf B IOK Hp inst ly S W mem md HX) as HAR.
assert (Hn0 : 0 <= n) by lia. pose proof (prim_fp_cf n ltac:(lia)) as FP.
destruct (off_split_cf B ly S Hp _ n l off (proj1 HAR) Hn0 FP Hcache) as [_ Hoff].
pose proof (geom_h n Hn0 FP) as (R1 & R2 & Q1 & Q2 & G).
rewrite (rz_size_small n ltac:(lia)), (req_size_max n Hn0) in G.
unfold AOX_cf. left.
exact (YGcfInstHitCore.hit_owned_k B ly S Hp W mem md n (chunk_class n) (Z.of_nat (length (l ++ [off]))) (off / 16) l off
  HAR Hn0 FP Hinited Hcache eq_refl eq_refl Hoff K6.RZ (K6.NPv n)
  ltac:(unfold K6.RZ; lia) eq_refl ltac:(unfold K6.NPv; lia) ltac:(unfold K6.RZ, K6.NPv; lia) HSHB HDZO odd a eq_refl eq_refl Hodd Hw).
Qed.

(* ErrnoG.ae_depot: the depot field's raw frame (outside the depot's stack window and ag_dzone) keeps errno
   (AGif1mE.errno_kept_depot_cgif over the image premises). *)
Lemma ae_depot_cf : ErrnoG.ae_depot_t B (U_cf B) (ARXq_cf B IOK Hp) (dpost_cf B).
Proof.
intros inst ly S W mem0 md0 tr regs mem md buf HX HU MEQ R10 R11 R3 R4 R1 BUF B8 BL BH BD S16 SL SH PRES.
pose proof (ARXq_cf_ARcf B IOK Hp inst ly S W mem0 md0 HX) as (M & L & _).
pose proof (amc_layout _ _ _ _ _ M) as LY. pose proof (HIMG ly S md0 L) as IMG.
eapply SRr_mono;
  [exact (HDEP Hp inst ly S W mem0 md0 tr regs mem md buf HX HU MEQ R10 R11 R3 R4 R1 BUF B8 BL BH BD S16 SL SH PRES)|].
intros W' c' _ [EW (z & regs' & mem' & mat & Ec & RP & FR & PR & DP)]. cbv beta.
split; [exact EW|]. exists z, regs', mem', mat.
split; [exact Ec|]. split; [exact RP|]. split; [exact FR|].
split; [|split; [exact PR | exact DP]].
intros i Hi.
pose proof (ErrnoApart.errno_below_imgend EII B ly TS LY IMG) as EB1.
destruct (EII B ly TS IMG) as [E1 _]. pose proof (lo_img ly LY) as (L1 & _).
assert (EB : bv_unsigned (w64 (as_errno B + i)) = as_errno B + i)
  by (unfold w64; apply unsigned_lit_small; unfold kImgLo, kImgEnd in *; lia).
assert (HE : as_errno B <= as_errno B + i < as_errno B + 4) by lia.
apply FR; rewrite EB.
- intros Hs. exact (ErrnoApart.errno_apart_stack EII B ly _ _ (as_errno B + i) TS LY IMG SL Hs HE).
- intros Hd. exact (EDZ B ly (as_errno B + i) TS LY IMG Hd HE).
Qed.
End f.

(* ================================================================================================================ *)
(* 3. The interfaces.                                                                                               *)
Theorem iface_cf : forall Hp, AIface B (U_cf B) malloc_cf (ARXq_cf B IOK Hp) (AOX_cf B) (rpre_cf B) cf_malloc_max LIVE_MAX qtight
  (dpost_cf B) cf_pc_malloc_max cf_pc_spin_shadow.
Proof.
intros Hp. constructor.
- exact (inst_cf Hp).
- intros inst ly S W mem md n l off HX _. exact (view_cf Hp inst ly S W mem md n l off HX).
- exact YGcfInstHitCore.shape_cf.
- exact (depot_cf Hp).
- intros inst ly S W tr z m H. exact (proj1 H).
- exact (post_cf Hp).
- intros inst ly S W mem md n l off odd a HX _. exact (owned_cf Hp inst ly S W mem md n l off odd a HX).
- exact (uninit_cf Hp).
Qed.

Theorem ifaceK_cf : forall Hp, AIfaceK B (U_cf B) malloc_cf (ARXq_cf B IOK Hp) (AOX_cf B) (rpre_cf B) cf_malloc_max LIVE_MAX qtight
  (dpost_cf B) cf_pc_malloc_max cf_pc_spin_shadow.
Proof.
intros Hp. constructor.
- exact (post_cf_k Hp).
- intros inst ly S W mem md n l off odd a HX _. exact (owned_cf_k Hp inst ly S W mem md n l off odd a HX).
Qed.

Theorem ifaceE_cf : forall Hp, ErrnoG.AIfaceE B (U_cf B) malloc_cf (ARXq_cf B IOK Hp) (AOX_cf B) (rpre_cf B) cf_malloc_max LIVE_MAX qtight
  (dpost_cf B) cf_pc_malloc_max cf_pc_spin_shadow.
Proof. intros Hp. constructor. exact (ae_depot_cf Hp). Qed.

End b.
End h.
