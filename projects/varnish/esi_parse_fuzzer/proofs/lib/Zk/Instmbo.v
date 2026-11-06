(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation Classical_Prop.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect Mremap.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Tac Image ZBridge SysStep Bytes Walk Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes Decode.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Image OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Walk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Decode.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import MRepAux Mall5lv Mallj6y Mallwlb Mallrkx Malllim Mallzvh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg Monad MProg MProg MTree MRep MRepAux.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require KInv MI_Inv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_WFree.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_W2ig.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Malls02 Mallkgx Mall1es Mall79j KNodes RzImpl KLink KLinkC.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require KLinkC.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MSafe KFrame.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Wje4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Wje4 Mrems6x MI_Kit MI_Ext.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WFree.MI_Read OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_W2ig.MI_Lsjc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallmv3.Mallm24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malls02 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall1es OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall79j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KNodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RzImpl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KLink OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KLinkC OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KLinkC.KLinkR OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MSafe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KFrame OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Wje4.MI_Wezf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Wje4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mrems6x OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ext.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import W_rejt8 W_retp0 InstDefs InstFree Instjhg Instqy7 Instbka Instbrv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Malls6g Mallx0l.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import AllocSpec LayoutP0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require LB_Inv LB_Sum LB_Ctrl LB_WFree LB_Rrk0 LB_Own.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require LB_Wazc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require InstQ.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Sum OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Ctrl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_WFree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Rrk0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Own OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Wazc.LB_Rekey OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.InstQ.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope Z_scope.

(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8z6.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8z6.dlia_nc.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition lb_remap (b : block) (A' n' : Z) (LB : list block) : list block :=
  map (fun x => if aptr_eqb (blk_slot x) (blk_slot b) then (blk_id x, A', n') else x) LB.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Section CEIL.
Context {Clg : Ceiling} {Rr : MRep.RunRandom}.  (* [comment removed for export] *)

Lemma rbf63_facts : forall st m c off n g bm i r ar q res,
  rbf st m c off n g bm i r ar q res -> m_sizeclass (get_meta_rec st g) = 63 ->
  let mr := get_meta_rec st g in let OLDL := m_maplen mr * 4096 in
  i = 0 /\ m_last_idx mr = 0 /\ m_freeable mr = 1 /\ snd bm = 0 /\ c = (fst bm, 16) /\ 0 < m_maplen mr < 2^35
  /\ get_stride mr = OLDL - 16 /\ OLDL = round_up_pg (r_len r) /\ 4096 <= OLDL /\ OLDL mod 4096 = 0
  /\ q = off /\ res = OLDL - 20 - 16 * off - n
  /\ meta_word mr = 32 + 64 * 63 + 4096 * m_maplen mr
  /\ 0 < r_base r /\ r_base r mod 4096 = 0 /\ r_base r + OLDL <= alloc_ceiling /\ (r_base r + OLDL <= 0x10000 \/ 0x63000 <= r_base r).
Proof.
  intros until res. intros RB SC63. cbv zeta.
  pose proof (rb_sc _ _ _ _ _ _ _ _ _ _ _ _ RB) as SC. destruct SC as [[SC48 _]|(_ & L0 & MLP)]; [lia|].
  pose proof (rb_i _ _ _ _ _ _ _ _ _ _ _ _ RB) as Hi. rewrite L0 in Hi. assert (I0 : i = 0) by lia. subst i.
  pose proof (rb_maplen _ _ _ _ _ _ _ _ _ _ _ _ RB) as ML.
  pose proof (rb_top (Clg:=Clg) _ _ _ _ _ _ _ _ _ _ _ _ RB ltac:(lia)) as [B0 OT].
  pose proof (rb_freeable _ _ _ _ _ _ _ _ _ _ _ _ RB) as FR.
  pose proof (rb_c _ _ _ _ _ _ _ _ _ _ _ _ RB) as Ec. pose proof (rb_fst _ _ _ _ _ _ _ _ _ _ _ _ RB) as Fc.
  pose proof (rb_q _ _ _ _ _ _ _ _ _ _ _ _ RB) as [Q16 QR]. pose proof (rb_res _ _ _ _ _ _ _ _ _ _ _ _ RB) as [ERES RES0].
  (first [ pose proof ((rb_rbase _ _ _ _ _ _ _ _ _ _ _ _ RB)) as dR_1; dand4 dR_1 as R0 RAL RC RIMG | pose proof (rb_rbase _ _ _ _ _ _ _ _ _ _ _ _ RB) as (R0 & RAL & RC & RIMG) ]). rewrite <- OT in RC, RIMG.
  assert (STR : get_stride (get_meta_rec st g) = m_maplen (get_meta_rec st g) * 4096 - 16).
  { unfold get_stride. rewrite (proj2 (Z.eqb_eq _ _) L0). destruct (Z.eqb_spec (m_maplen (get_meta_rec st g)) 0); [lia|]. cbn [andb negb]. unfold UNIT. lia. }
  rewrite STR, Z.mul_0_r, Z.add_0_r in Ec. rewrite STR in ERES. rewrite Z.mul_0_r in Q16.
  assert (C1 : c = (fst bm, 16)) by (apply injective_projections; cbn [fst snd]; [exact Fc| unfold UNIT in Ec; lia]).
  assert (C2 : (m_maplen (get_meta_rec st g) * 4096) mod 4096 = 0) by (apply Z_mod_mult).
  assert (C3 : res = m_maplen (get_meta_rec st g) * 4096 - 20 - 16 * off - n) by (unfold IB, UNIT in ERES; lia).
  assert (C4 : meta_word (get_meta_rec st g) = 32 + 64 * 63 + 4096 * m_maplen (get_meta_rec st g)) by (unfold meta_word; rewrite L0, FR, SC63; lia).
  assert (C5 : r_base r + m_maplen (get_meta_rec st g) * 4096 <= alloc_ceiling) by ((let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); exact RC).
  OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; auto; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma brk_quiet_of_INVL X st L BL LS : INVL X st L BL LS -> brk_quiet L.
Proof.
  intros HI. pose proof (ir_brk _ _ _ (proj1 HI)) as P. unfold brk_quiet.
  destruct (c_brk (s_ctx st)); [destruct P as [E _] | pose proof P as E | destruct P as [E _]]; rewrite E; exact Logic.I.
Qed.

Lemma p0_mremap_pre : forall s LB m md b st off g bm i r ar q res,
  p0_ainv (mkIAS s LB Rr) m md -> In b LB -> heap_wit s LB m st ->
  rbf st m (blk_slot b) off (blk_size b) g bm i r ar q res -> m_sizeclass (get_meta_rec st g) = 63 ->
  let B := r_base r in let OLDL := m_maplen (get_meta_rec st g) * 4096 in
  minv md /\ m_halted md = None /\ m_vm_lazy md = [] /\ m_vm_materialized md = []
  /\ map wwZ (vm_reserved (m_vmmaps md)) = p0_reserved
  /\ In (went B OLDL) (vm_maps (m_vmmaps md))
  /\ ceil_ok md   (* [comment removed for export] *)
  /\ (forall nd, 0 < nd <= alloc_ceiling -> nd mod 4096 = 0 -> nsafe (NMremap B OLDL nd MREMAP_MAYMOVE) md).
Proof.
  intros until res. intros AI Hb HW RB SC63. cbv zeta.
  pose proof (ainv_KI _ _ _ AI) as [Hh Hl].
  (first [ dand5 HW as LB0 PERM Hst MRP [BL AR] | destruct HW as (LB0 & PERM & Hst & MRP & [BL AR]) ]). (first [ pose proof (AR) as dR_11; dand8 dR_11 as L LS BLs INV LIVE RESV SEC CR | pose proof AR as (L & LS & BLs & INV & LIVE & RESV & SEC & CR) ]).
  pose proof (p0_KL_of s LB m md x0 st L BLs LS AI Hst INV) as HK.
  (first [ pose proof ((rbf63_facts _ _ _ _ _ _ _ _ _ _ _ _ RB SC63)) as dR_12; dand17 dR_12 as I0 L0 FR1 BM0 EC MLP STR OT O4096 OAL EQ ERES MW R0 RAL RC RIMG | pose proof (rbf63_facts _ _ _ _ _ _ _ _ _ _ _ _ RB SC63) as (I0 & L0 & FR1 & BM0 & EC & MLP & STR & OT & O4096 & OAL & EQ & ERES & MW & R0 & RAL & RC & RIMG) ]).
  pose proof (rb_reg _ _ _ _ _ _ _ _ _ _ _ _ RB) as Hr. pose proof (rb_kind _ _ _ _ _ _ _ _ _ _ _ _ RB) as Kr.
  (* [comment removed for export] *)
  assert (ING : In (r_base r, r_len r) (ld_groups L)).
  { eapply Permutation_in; [apply Permutation_sym; exact (ir_groups _ _ _ (proj1 INV))|].
    apply in_map_iff. exists (fst (blk_slot b), r). split; [reflexivity|].
    apply filter_In. split; [apply OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_W2ig.MI_Lsjc.In_map_to_list_regions; exact Hr|]. cbn [snd]. rewrite Kr. reflexivity. }
  (first [ pose proof ((kl_groups _ _ _ HK _ _ ING)) as dR_13; dand6 dR_13 as G1 G2 G3 G4 G5 G6 | pose proof (kl_groups _ _ _ HK _ _ ING) as (G1 & G2 & G3 & G4 & G5 & G6) ]).
  rewrite mmap_len_round_up, <- OT in G4, G5, G6.
  pose proof alloc_ceiling_val as ACV. 
  split; [exact (kl_minv _ _ _ HK)|]. split; [exact Hh|]. split; [exact Hl|]. split; [exact (kl_mat _ _ _ HK)|].
  split. { rewrite <- (kl_resv _ _ _ HK), RESV. reflexivity. }
  split; [exact G5|]. split; [exact (kl_ceil _ _ _ HK)|].
  intros nd Hnd NDA.
  assert (UB : bv_unsigned (KNodes.w (r_base r)) = r_base r) by (unfold KNodes.w; apply unsigned_lit; lia).
  assert (RO : rlen (m_maplen (get_meta_rec st g) * 4096) = m_maplen (get_meta_rec st g) * 4096) by (rewrite rlen_eq by lia; apply mmap_len_of_aligned; lia).
  assert (RN : rlen nd = nd) by (rewrite rlen_eq by lia; apply mmap_len_of_aligned; lia).
  cbn [nsafe]. split; [reflexivity|]. split; [rewrite UB, page_size_eq; exact RAL|].
  assert (PA : forall x, 0 < x <= alloc_ceiling -> x mod 4096 = 0 -> page_align_is0_b (KNodes.w x) = false).
  { intros x Hx XA. unfold page_align_is0_b, w_is0, KNodes.w. rewrite unsigned_lit by lia.
    unfold page_round_up_Z. rewrite page_size_eq. unfold two_pow_64.
    destruct (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 0)) eqn:E; cbn [orb].
    - exfalso. apply Mrems6x.bv_eqb_true_iff in E. apply (f_equal bv_unsigned) in E. rewrite !unsigned_lit in E by lia. lia.
    - apply Z.leb_gt. Z.div_mod_to_equations. lia. }
  split; [apply PA; lia|]. split; [apply PA; [lia| exact OAL]|].
  unfold mremap_src_ok, mremap_source_b, mremap_backing_uniform_b. rewrite RO, Hl, UB. pose proof (kl_ceil _ _ _ HK) as KCL. unfold ceil_ok in KCL. rewrite KCL.   (* [comment removed for export] *) cbn [region_free forallb orb map_contains].
  assert (EW : Z_to_bv 64 (m_maplen (get_meta_rec st g) * 4096) = wz (m_maplen (get_meta_rec st g) * 4096)) by reflexivity.
  rewrite (proj2 (Z.leb_le _ _) G4). cbn [andb].
  assert (RF : region_free (vm_reserved (m_vmmaps md)) (KNodes.w (r_base r)) (Z_to_bv 64 (m_maplen (get_meta_rec st g) * 4096)) = true).
  { exact (kl_maps_resv _ _ _ HK _ G5). }
  assert (HAS : map_has (vm_maps (m_vmmaps md)) (KNodes.w (r_base r)) (Z_to_bv 64 (m_maplen (get_meta_rec st g) * 4096)) = true).
  { unfold map_has. apply existsb_exists. exists (went (r_base r) (m_maplen (get_meta_rec st g) * 4096)). split; [exact G5|].
    cbv delta [went KLink.wz KNodes.w]. cbn [fst snd]. rewrite !bv_eqb_refl. reflexivity. }
  assert (NA : region_free (vm_noaccess (m_vmmaps md)) (KNodes.w (r_base r)) (Z_to_bv 64 (m_maplen (get_meta_rec st g) * 4096)) = true).
  { pose proof (kl_groups_na _ _ _ HK _ _ ING) as X. rewrite mmap_len_round_up, <- OT in X. exact X. }
  rewrite RF, HAS, NA. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma Forall2_map_map' {A B A' B'} (R : A -> B -> Prop) (R' : A' -> B' -> Prop) (f : A -> A') (h : B -> B') l1 l2 :
  Forall2 R l1 l2 -> (forall x y, In x l1 -> In y l2 -> R x y -> R' (f x) (h y)) -> Forall2 R' (map f l1) (map h l2).
Proof.
  intros F HR. induction F; cbn; constructor.
  - apply HR; [left; reflexivity| left; reflexivity| assumption].
  - apply IHF. intros; apply HR; [right| right|]; assumption.
Qed.

Lemma find_blk_map_other (f : block -> block) LB q :
  (forall x, In x LB -> (blk_addr (f x) =? q) = (blk_addr x =? q) /\ ((blk_addr x =? q) = true -> blk_size (f x) = blk_size x)) ->
  match find_blk (map f LB) q with Some b => Some (blk_size b) | None => None end
  = match find_blk LB q with Some b => Some (blk_size b) | None => None end.
Proof.
  induction LB as [|x LB IH]; intros H; [reflexivity|]. cbn. destruct (H x (or_introl eq_refl)) as [E S].
  rewrite E. destruct (blk_addr x =? q) eqn:Q; [cbn; rewrite S by reflexivity; reflexivity|].
  apply IH. intros y Hy. apply H. right. exact Hy.
Qed.

Lemma find_blk_none LB q : (forall x, In x LB -> blk_addr x <> q) -> find_blk LB q = None.
Proof.
  induction LB as [|x LB IH]; intros H; [reflexivity|]. cbn. destruct (Z.eqb_spec (blk_addr x) q) as [E|NE]; [exfalso; exact (H x (or_introl eq_refl) E)|].
  apply IH. intros y Hy. apply H. right. exact Hy.
Qed.

Lemma find_blk_map_hit (f : block -> block) LB b q :
  In b LB -> blk_addr (f b) = q -> (forall x, In x LB -> x <> b -> f x = x /\ blk_addr x <> q) ->
  find_blk (map f LB) q = Some (f b).
Proof.
  induction LB as [|x LB IH]; intros Hb Hq H; [destruct Hb|]. cbn.
  destruct (Classical_Prop.classic (x = b)) as [->|NE].
  - rewrite (proj2 (Z.eqb_eq _ _) Hq). reflexivity.
  - destruct (H x (or_introl eq_refl) NE) as [Ef NA]. rewrite Ef. destruct (Z.eqb_spec (blk_addr x) q); [congruence|].
    apply IH; [destruct Hb; [congruence| assumption]| exact Hq| intros y Hy; apply H; right; exact Hy].
Qed.

Lemma region_free_ranges_free (l : list (word * word)) (a : word) (n : word) :
  region_free l a n = true -> ranges_free (map wwZ l) (bv_unsigned a) (bv_unsigned n) = true.
Proof.
  intros H. unfold ranges_free. apply forallb_forall. intros [b k] Hin.
  apply in_map_iff in Hin as ([bw kw] & E & Hin). unfold wwZ in E. cbn in E. injection E as <- <-.
  pose proof (region_free_disj _ _ _ _ H Hin) as D. unfold elo, ehi in D. cbn [fst snd] in D |- *.
  unfold iv_disjoint. apply orb_true_intro. destruct D as [D|D]; [left| right]; apply Z.leb_le; lia.
Qed.

Lemma wtm_other mm a bs (x : word) : 0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
  ~ (a <= bv_unsigned x < a + Z.of_nat (length bs)) -> write_to_mem mm (wa a) bs x = mm x.
Proof.
  intros Ha Hb OUT. rewrite write_to_mem_spec by lia.
  destruct (Z.leb_spec0 a (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (a + Z.of_nat (length bs))); cbn [andb]; try reflexivity. exfalso; lia.
Qed.
Lemma wtm_mono mm a bs (x : word) : 0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
  mm x <> None -> write_to_mem mm (wa a) bs x <> None.
Proof.
  intros Ha Hb H. rewrite write_to_mem_spec by lia.
  destruct (Z.leb_spec0 a (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (a + Z.of_nat (length bs))); cbn [andb]; try exact H.
  intros E0. apply nth_error_None in E0. lia.
Qed.

Theorem remap_model : forall s LB m md b st off g bm i r ar q res n (dst : word) md' (mK : mem),
  p0_ainv (mkIAS s LB Rr) m md -> In b LB -> heap_wit s LB m st ->
  blk_addr b = r_base r + snd (blk_slot b) + UNIT * off ->
  rbf st m (blk_slot b) off (blk_size b) g bm i r ar q res ->
  m_sizeclass (get_meta_rec st g) = 63 -> MMAP_THRESHOLD <= n < 2^32 ->
  let mr := get_meta_rec st g in
  let B := r_base r in let OLDL := m_maplen mr * 4096 in
  let ND := needed_of n (UNIT * off) in let NB := bv_unsigned dst in
  let h := m_vmmaps md in
  ( (ND = OLDL /\ NB = B /\ md' = md)
    \/ (ND <> OLDL /\ 0 < NB /\ NB mod 4096 = 0 /\ NB + ND <= alloc_ceiling
        /\ m_vmmaps md' = mremap_maps_next h (wz B) dst (wz ND) /\ minv md' /\ m_halted md' = None /\ m_vm_lazy md' = [] /\ m_vm_materialized md' = []
        /\ ((dst = wz B /\ (ND < OLDL \/ region_free (vm_reserved h ++ map_remove (vm_maps h) (wz B)) (wz B) (wz ND) = true))
            \/ (dst <> wz B /\ region_free (vm_reserved h ++ vm_maps h) dst (wz ND) = true))) ) ->
  (forall o, 0 <= o < Z.min OLDL ND -> mK (wz (NB + o)) = m (wz (B + o))) ->
  (forall o, 0 <= o < ND -> mK (wz (NB + o)) <> None) ->
  (forall a, 0 <= a < alloc_ceiling -> ~ (NB <= a < NB + ND) -> ~ (B <= a < B + OLDL) -> mK (wz a) = m (wz a)) ->
  let A' := NB + 16 + UNIT * off in
  let LB' := lb_remap b A' n LB in
  let mF := remap_mem mK (conc st g) NB ND (UNIT * off) n (meta_word mr) (i + 32 * Z.min res 5) in
  exists s',
    ps_brk s' = ps_brk s /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ p0_ainv (mkIAS s' LB' Rr) mF md'
    /\ (lb_bytes LB' = lb_bytes LB + n - blk_size b /\ zlen LB' = zlen LB)   (* [comment removed for export] *)
    /\ p0_live (mkIAS s' LB' Rr) A' = Some n
    /\ (forall q', q' <> A' -> q' <> blk_addr b -> p0_live (mkIAS s' LB' Rr) q' = p0_live (mkIAS s LB Rr) q')
    /\ (NB <> B -> p0_live (mkIAS s LB Rr) A' = None /\ p0_live (mkIAS s' LB' Rr) (blk_addr b) = None)
    /\ (forall a, in_block LB' a <-> (A' <= a < A' + n) \/ (exists y, In y LB /\ y <> b /\ blk_addr y <= a < blk_addr y + blk_size y))
    /\ (forall a, in_block LB a <-> (blk_addr b <= a < blk_addr b + blk_size b) \/ (exists y, In y LB /\ y <> b /\ blk_addr y <= a < blk_addr y + blk_size y))
    /\ (forall y, In y LB -> y <> b -> (blk_addr y + blk_size y <= NB \/ NB + ND <= blk_addr y) /\ (blk_addr y + blk_size y <= B \/ B + OLDL <= blk_addr y)
                                      /\ 0 <= blk_addr y /\ blk_addr y + blk_size y <= alloc_ceiling)
    /\ (conc st g + 40 <= NB \/ NB + ND <= conc st g) /\ (conc st g + 40 <= B \/ B + OLDL <= conc st g)
    /\ (forall a, conc st g <= a < conc st g + 40 -> p0_owned (mkIAS s LB Rr) a /\ p0_owned (mkIAS s' LB' Rr) a).
Proof.
  intros until mK. intros AI Hb HW HA RB SC63 Hn. cbv zeta. intros KCASE COPYK NEWM OUTK. unfold MMAP_THRESHOLD in Hn.
  pose proof (ainv_KI _ _ _ AI) as [Hh Hl].
  pose proof AI as (HP & OW & RP & QVs). cbn [ia_s ia_LB ia_rr] in HP, OW, RP, QVs.
  (first [ dand5 HW as LB0 PERM Hst MRP [BL AR] | destruct HW as (LB0 & PERM & Hst & MRP & [BL AR]) ]). (first [ pose proof (AR) as dR_16; dand8 dR_16 as L LS BLs INV LIVE RESV SEC CR | pose proof AR as (L & LS & BLs & INV & LIVE & RESV & SEC & CR) ]).
  pose proof alloc_ceiling_val as ACV. 
  (first [ pose proof ((rbf63_facts _ _ _ _ _ _ _ _ _ _ _ _ RB SC63)) as dR_17; dand17 dR_17 as I0 L0 FR1 BM0 EC MLP STR OT O4096 OAL EQ ERES MW R0 RAL RC RIMG | pose proof (rbf63_facts _ _ _ _ _ _ _ _ _ _ _ _ RB SC63) as (I0 & L0 & FR1 & BM0 & EC & MLP & STR & OT & O4096 & OAL & EQ & ERES & MW & R0 & RAL & RC & RIMG) ]).
  subst i. set (c := blk_slot b) in *. set (rid := fst bm) in *.
  assert (Ebm : bm = (rid, 0)) by (apply injective_projections; [reflexivity| exact BM0]).
  pose proof (rb_reg _ _ _ _ _ _ _ _ _ _ _ _ RB) as Hr. rewrite EC in Hr. cbn [fst] in Hr.
  pose proof (rb_kind _ _ _ _ _ _ _ _ _ _ _ _ RB) as Kr.
  pose proof (rb_hosts _ _ _ _ _ _ _ _ _ _ _ _ RB) as Hg. rewrite Ebm in Hg. change (hosts st (rid, 0) g) in Hg.
  pose proof (rb_off _ _ _ _ _ _ _ _ _ _ _ _ RB) as HOFF. pose proof (rb_n _ _ _ _ _ _ _ _ _ _ _ _ RB) as OLD0.
  pose proof (rb_res _ _ _ _ _ _ _ _ _ _ _ _ RB) as [_ RES0].
  pose proof (needed_of_props n (UNIT * off) ltac:(lia) ltac:(unfold UNIT; lia)) as [ND1 NDA].
  set (ND := needed_of n (UNIT * off)) in *. set (NB := bv_unsigned dst) in *. unfold UNIT in ND1.
  set (OLDL := m_maplen (get_meta_rec st g) * 4096) in *.
  pose proof (bv_unsigned_in_range _ dst) as DR. change (bv_modulus 64) with (2^64) in DR. fold NB in DR.
  (* [comment removed for export] *)
  assert (IN0 : In b LB0) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hb]).
  (first [ pose proof ((Forall2_In_l _ _ _ _ CR IN0)) as dR_18; dex1 dR_18 as k; destruct dR_18 as [Hk (KS & KZ & KA)] | pose proof ((Forall2_In_l _ _ _ _ CR IN0)) as dR_18; dand3 dR_18 as k Hk (KS & KZ & KA) | destruct (Forall2_In_l _ _ _ _ CR IN0) as (k & Hk & (KS & KZ & KA)) ]).
  destruct k as [[c2 off2] old2]. cbn [bslot boff bsize fst snd] in KS, KZ, KA. fold c in KS. subst c2. subst old2.
  assert (Cc : conc st c = r_base r + snd c) by (apply conc_region'; rewrite EC; exact Hr).
  assert (EOFF : off2 = off) by (rewrite Cc in KA; rewrite KA in HA; try (generalize alloc_ceiling_val); clear - HA; try pose proof alloc_ceiling_val; unfold UNIT in HA; lia). subst off2.
  rewrite EC in Hk.
  (* [comment removed for export] *)
  assert (NBF : 0 < NB /\ NB mod 4096 = 0 /\ NB + ND <= alloc_ceiling /\ (ND = OLDL /\ NB = r_base r /\ md' = md \/ ND <> OLDL)).
  { destruct KCASE as [(E1 & E2 & E3)|(E1 & X1 & X2 & X3 & _)]; [| idtac; splits; auto]. rewrite E2, E1. idtac. splits; auto; lia. }
  (first [ dand4 NBF as NB0 NBA NBC _ | destruct NBF as (NB0 & NBA & NBC & _) ]).
  assert (ND4096 : 4096 <= ND) by lia.
  assert (NDX : ND < 2 ^ 40) by lia.
  assert (FITn : UNIT + UNIT * off + n + IB <= ND) by (unfold UNIT, IB; lia).
  assert (NDT : ND < UNIT + UNIT * off + n + IB + 4096) by (unfold UNIT, IB; lia).
  (* [comment removed for export] *)
  pose proof (p0_KL_of s LB m md x0 st L BLs LS AI Hst INV) as HK.
  pose proof (KL_groups_perm L _ (ps_brk s) md HK (groups_old_perm st L BLs LS rid r g INV Hg Hr)) as HKg.
  pose proof (brk_quiet_of_INVL _ _ _ _ _ INV) as BQ.
  assert (MML : mmap_len (r_len r) = OLDL) by (rewrite mmap_len_round_up; symmetry; exact OT).
  pose proof (proj1 MRP) as WF0. (first [ pose proof (WF0) as dR_20; dand5 dR_20 as Hres WR DJ WA WG | pose proof WF0 as (Hres & WR & DJ & WA & WG) ]).
  (first [ pose proof (INV) as dR_21; dand7 dR_21 as IR IA IM IL IG IS ISH | pose proof INV as (IR & IA & IM & IL & IG & IS & ISH) ]).
  (* [comment removed for export] *)
  assert (KOUT : KL (MI_Wje4.L' st L rid NB ND) (ps_brk s) md'
     /\ (forall q2 r2, q2 <> rid -> s_regions st !! q2 = Some r2 -> let '(b2, l2) := region_live_range r2 in NB + ND <= b2 \/ b2 + l2 <= NB)
     /\ ranges_free p0_reserved NB ND = true
     /\ minv md' /\ m_halted md' = None /\ m_vm_lazy md' = []
     /\ (NB <> r_base r -> NB + ND <= r_base r \/ r_base r + OLDL <= NB)).
  { unfold MI_Wje4.L'. destruct KCASE as [(E1 & E2 & E3)|(E1 & X1 & X2 & X3 & XV & XM & XH & XL & XMT & XC)].
    - (* [comment removed for export] *)
      rewrite E3, E2, E1. split; [apply (KL_regroup_len L _ _ _ _ (r_len r)); [exact HKg| symmetry; exact MML]|].
      split.
      { intros q2 r2 NE H2. pose proof (ir_disj _ _ _ IR rid q2 r r2 Hr H2 ltac:(congruence)) as D.
        unfold region_live_range at 1 in D. rewrite Kr, <- OT in D. destruct (region_live_range r2) as [b2 l2]. lia. }
      split; [(first [ pose proof ((WR rid r Hr)) as dR_22; dand5 dR_22 as _ _ _ _ RF | destruct (WR rid r Hr) as (_ & _ & _ & _ & RF) ]); rewrite <- OT in RF; exact RF|].
      split; [exact (kl_minv _ _ _ HK)|]. split; [exact Hh|]. split; [exact Hl|]. intros NE. exfalso. exact (NE eq_refl).
    - (* [comment removed for export] *)
      pose proof (KL_mremap L (MI_Wje4.G0 st rid) (ps_brk s) md md' (r_base r) (r_len r) ND dst HKg BQ) as KM. cbv zeta in KM. rewrite MML in KM.
      specialize (KM ltac:(unfold LEN_MAX; lia) NDA X1 X2 ltac:(idtac; exact X3) XV XM XH XMT XC).
      (first [ dand5 KM as HK' D2 D3 D4 D5 | destruct KM as (HK' & D2 & D3 & D4 & D5) ]). fold NB in HK', D2, D3, D5.
      split; [exact HK'|]. split.
      { intros q2 r2 NE H2. (first [ pose proof ((ir_shape _ _ _ IR q2 r2 H2)) as dR_24; dand6 dR_24 as S1 S2 S3 S4 S5 S6 | destruct (ir_shape _ _ _ IR q2 r2 H2) as (S1 & S2 & S3 & S4 & S5 & S6) ]).
        pose proof (round_up_pg_ge (r_len r2)) as RU2. rewrite <- mmap_len_round_up in RU2.
        destruct (r_kind r2) eqn:K2.
        + (* [comment removed for export] *) unfold region_live_range. rewrite K2.
          assert (BR : ld_brkreg L = Some (r_base r2, r_len r2)) by (apply (proj2 (ir_brkreg _ _ _ IR _ _)); exists q2, r2; auto).
          pose proof (D3 _ _ BR) as D. destruct (S6 ltac:(left; exact K2)) as [LM _].
          rewrite (round_up_pg_aligned _ ltac:(unfold PGSZ in LM; exact LM)). unfold PGSZ in *. lia.
        + (* [comment removed for export] *) unfold region_live_range. rewrite K2.
          assert (IM2 : exists kk, In (r_base r2, r_len r2, kk) (ld_metas L)).
          { exists (frontier st q2 r2 / PGSZ - 1). eapply Permutation_in; [apply Permutation_sym; exact (ir_metas _ _ _ IR)|].
            apply in_map_iff. exists (q2, r2). split; [reflexivity|]. apply filter_In. split; [apply OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_W2ig.MI_Lsjc.In_map_to_list_regions; exact H2|]. cbn [snd]. rewrite K2. reflexivity. }
          destruct (D2 (r_base r2) (r_len r2) (or_intror IM2)) as [D|D]; rewrite ?mmap_len_round_up in D; lia.
        + (* [comment removed for export] *) unfold region_live_range. rewrite K2.
          assert (IG2 : In (r_base r2, r_len r2) (MI_Wje4.G0 st rid)).
          { unfold MI_Wje4.G0. apply in_map_iff. exists (q2, r2). split; [reflexivity|]. apply filter_In. split; [| unfold isG; cbn [snd]; rewrite K2; reflexivity].
            apply (proj1 (list_elem_of_In _ _)). apply elem_of_map_to_list. rewrite lookup_delete_ne by congruence. exact H2. }
          destruct (D2 (r_base r2) (r_len r2) (or_introl IG2)) as [D|D]; rewrite ?mmap_len_round_up in D; lia. }
      split.
      { pose proof (region_free_ranges_free _ _ _ D4) as RF. rewrite <- (kl_resv _ _ _ HK), RESV in RF. fold NB in RF.
        unfold KLink.wz in RF. rewrite unsigned_lit in RF by lia. exact RF. }
      split; [exact XM|]. split; [exact XH|]. split; [exact XL|].
      intros NE. apply D5. intros E. apply NE. unfold NB. rewrite E. unfold KLink.wz. apply unsigned_lit. lia. }
  (first [ dand7 KOUT as HK' DISJ NBRF MINV' HALT' LAZY' MOVED | destruct KOUT as (HK' & DISJ & NBRF & MINV' & HALT' & LAZY' & MOVED) ]).
  pose proof (reserved_disjoint1 _ _ NBRF ltac:(lia)) as NIMG.
  (* [comment removed for export] *)
  set (b3 := 0 + 32 * Z.min res 5).
  assert (B3 : Z.land b3 31 = 0) by (subst b3; apply land31_idx; [lia| try (generalize alloc_ceiling_val); clear - RES0; try pose proof alloc_ceiling_val; lia]).
  assert (B3R : 0 <= b3 < 256) by (subst b3; try (generalize alloc_ceiling_val); clear - RES0; try pose proof alloc_ceiling_val; lia).
  assert (OK4 : known st (rid, 16 + UNIT * off - 4) 0).
  { unfold known, SHd. cbn [fst snd]. pose proof (rb_k4 _ _ _ _ _ _ _ _ _ _ _ _ RB) as K. rewrite EC in K. exact K. }
  assert (OK2 : known st (rid, 16 + UNIT * off - 2) (byte_of off 0)).
  { unfold known, SHd. cbn [fst snd]. pose proof (rb_k2 _ _ _ _ _ _ _ _ _ _ _ _ RB) as K. rewrite EC, EQ in K. exact K. }
  assert (OK1 : known st (rid, 16 + UNIT * off - 1) (byte_of off 1)).
  { unfold known, SHd. cbn [fst snd]. pose proof (rb_k1 _ _ _ _ _ _ _ _ _ _ _ _ RB) as K. rewrite EC, EQ in K. exact K. }
  assert (N0 : 0 <= n) by lia.
  pose proof (remap_B st L BLs LS rid r g off (blk_size b) n NB ND INV Hk Hg SC63 Hr ND4096 NDA NDX NB0 NBA NBC FITn NDT HOFF N0 DISJ b3 B3 B3R OK4 OK2 OK1) as INV'.
  pose proof (remap_A st L BLs LS rid r g off (blk_size b) NB ND INV Hk Hg SC63 Hr ND4096 NDA NDX NB0 NBA NBC HOFF DISJ) as INVE.
  set (stF := MI_Wje4.stF st rid g off n NB ND b3) in *.
  set (stE := MI_Wje4.stE st rid g NB ND) in *.
  set (L' := MI_Wje4.L' st L rid NB ND) in *.
  (* [comment removed for export] *)
  set (G := conc st g) in *.
  (first [ pose proof ((rb_mslot _ _ _ _ _ _ _ _ _ _ _ _ RB)) as dR_26; dex3 dR_26 as a ar' kk; dand3 dR_26 as Ha Hkk Egk | pose proof ((rb_mslot _ _ _ _ _ _ _ _ _ _ _ _ RB)) as dR_26; dand6 dR_26 as a ar' kk Ha Hkk Egk | destruct (rb_mslot _ _ _ _ _ _ _ _ _ _ _ _ RB) as (a & ar' & kk & Ha & Hkk & Egk) ]).
  (first [ pose proof ((area_conc st a ar' WF0 Ha)) as dR_27; dex1 dR_27 as ra; dand9 dR_27 as Hra Ca Sa0 Sa1 SaL NK RB0 RBAL RBC | pose proof ((area_conc st a ar' WF0 Ha)) as dR_27; dand10 dR_27 as ra Hra Ca Sa0 Sa1 SaL NK RB0 RBAL RBC | destruct (area_conc st a ar' WF0 Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC) ]).
  pose proof (area_lr_lo st a ar' ra WF0 Ha Hra) as LRa. pose proof (lr_lo_ge ra) as LRa'.
  assert (HG : G = conc st a + (AREA_HDR + META_SIZE * kk)) by (unfold G; rewrite Egk, conc_aadd by (rewrite Hra; eauto); reflexivity).
  unfold AREA_HDR, META_SIZE, NSLOTS in HG, Hkk.
  assert (NEa : fst a <> rid). { intros E. rewrite E, Hr in Hra. injection Hra as Era. rewrite <- Era in NK. exact (NK Kr). }
  assert (G1 : (G + 40 <= NB \/ NB + ND <= G) /\ (G + 40 <= r_base r \/ r_base r + OLDL <= G) /\ G + 40 <= alloc_ceiling /\ (G + 40 <= 0x10000 \/ 0x63000 <= G) /\ 0 <= G).
  { pose proof (DISJ (fst a) ra NEa Hra) as D1.
    assert (LR : let '(b2, l2) := region_live_range ra in b2 = lr_lo ra /\ b2 + l2 = r_base ra + round_up_pg (r_len ra)).
    { unfold region_live_range, lr_lo. destruct (r_kind ra); cbn zeta iota beta; unfold PGSZ; split; lia. }
    destruct (region_live_range ra) as [b2 l2]. destruct LR as [LR1 LR2].
    assert (LRr : lr_lo r = r_base r) by (apply lr_lo_group; exact Kr).
    pose proof (DJ (fst a) ra rid r Hra Hr NEa) as D2. rewrite LRr, <- OT in D2.
    (first [ pose proof ((WR _ _ Hra)) as dR_28; dand5 dR_28 as _ _ _ _ RFa | destruct (WR _ _ Hra) as (_ & _ & _ & _ & RFa) ]). pose proof (round_up_pg_ge (r_len ra)).
    pose proof (reserved_disjoint1 _ _ RFa ltac:(lia)) as A4. rewrite HG, Ca. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). splits; try (generalize alloc_ceiling_val); clear - D1 LR1 LR2 LRa LRa' D2 Sa0 Sa1 Hkk H A4 RBC RB0; try pose proof alloc_ceiling_val; lia. }
  (first [ dand5 G1 as GN GB GC GI G0' | destruct G1 as (GN & GB & GC & GI & G0') ]).
  (* [comment removed for export] *)
  pose proof (mrep_meta_chunk st m g MRP (rb_mslot _ _ _ _ _ _ _ _ _ _ _ _ RB)) as MC. fold G in MC.
  assert (MCK : rw_cells rsegs mK G (meta_cells st (get_meta_rec st g))).
  { eapply InstDefs.rw_cells_agree'; [exact MC|]. unfold meta_cells. cbn [cells_size csize Nat.add]. intros x Hx.
    rewrite <- (definitions.Z_to_bv_bv_unsigned 64 x). apply OUTK; [idtac; (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); try (generalize alloc_ceiling_val); clear - Hx GC G0'; try pose proof alloc_ceiling_val; lia| try (generalize alloc_ceiling_val); clear - Hx GN; try pose proof alloc_ceiling_val; lia| try (generalize alloc_ceiling_val); clear - Hx GB; try pose proof alloc_ceiling_val; lia]. }
  set (mword := meta_word (get_meta_rec st g)) in *.
  set (m1 := write_to_mem mK (wa (G + 16)) (le8 (MRep.wz NB))).
  set (m2 := write_to_mem m1 (wa (G + 32)) (le8 (MRep.wz (mword mod 4096 + ND)))).
  set (mE := write_to_mem m2 (wa (NB + ND - 4)) [b8 0]).
  pose proof (rw_cells_write rsegs mK G _ 16 (C8 (pw st (m_mem (get_meta_rec st g)))) (C8 (MRep.wz NB)) MCK eq_refl eq_refl Logic.I) as MC1.
  change (cbytes (C8 (MRep.wz NB))) with (le8 (MRep.wz NB)) in MC1. change (Z.of_nat 16) with 16 in MC1. fold m1 in MC1.
  unfold meta_cells in MC1. cbn [cell_upd csize Nat.eqb Nat.sub] in MC1.
  pose proof (rw_cells_write rsegs m1 G _ 32 (C8 (MRep.wz mword)) (C8 (MRep.wz (mword mod 4096 + ND))) MC1 eq_refl eq_refl Logic.I) as MC2.
  change (cbytes (C8 (MRep.wz (mword mod 4096 + ND)))) with (le8 (MRep.wz (mword mod 4096 + ND))) in MC2. change (Z.of_nat 32) with 32 in MC2. fold m2 in MC2.
  cbn [cell_upd csize Nat.eqb Nat.sub] in MC2.
  assert (MC3 : rw_cells rsegs mE G [C8 (pw st (m_prev (get_meta_rec st g))); C8 (pw st (m_next (get_meta_rec st g))); C8 (wz NB);
                                    C4 (wz (m_avail (get_meta_rec st g))); C4 (wz (m_freed (get_meta_rec st g))); C8 (wz (mword mod 4096 + ND))]).
  { unfold mE. apply rw_cells_frame; [exact MC2| try (generalize alloc_ceiling_val); clear - NB0 ND4096; try pose proof alloc_ceiling_val; lia| cbn; (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); try (generalize alloc_ceiling_val); clear - NBC NB0 ND4096; try pose proof alloc_ceiling_val; lia| cbn [cells_size csize Nat.add length]; try (generalize alloc_ceiling_val); clear - GN ND4096; try pose proof alloc_ceiling_val; lia]. }
  apply (proj1 (rw_cells_app rsegs mE G [C8 (pw st (m_prev (get_meta_rec st g))); C8 (pw st (m_next (get_meta_rec st g)))] _)) in MC3 as [_ MC3].
  apply (proj1 (rw_cells_app rsegs mE _ [C8 (wz NB)] _)) in MC3 as [GM MC3].
  apply (proj1 (rw_cells_app rsegs mE _ [C4 (wz (m_avail (get_meta_rec st g))); C4 (wz (m_freed (get_meta_rec st g)))] _)) in MC3 as [_ GW].
  cbn [cells_size csize Nat.add] in GM, GW.
  replace (G + Z.of_nat 16) with (G + 16) in GM by lia. replace (G + Z.of_nat 16 + Z.of_nat 8 + Z.of_nat 8) with (G + 32) in GW by lia.
  assert (EMW : mword mod 4096 + ND = meta_word (m_set_maplen (MI_Wje4.ML' ND) (MR st g))).
  { rewrite MW. unfold meta_word. cbn [m_last_idx m_freeable m_sizeclass m_maplen m_set_maplen]. unfold MR. rewrite L0, FR1, SC63.
    pose proof (ML'_eq NB ND ND4096 NDA NDX NB0) as [MLE MLR]. rewrite (land52 0 0 (MI_Wje4.ML' ND)) by lia.
    replace (32 + 64 * 63 + 4096 * m_maplen (get_meta_rec st g)) with (4064 + m_maplen (get_meta_rec st g) * 4096) by lia.
    rewrite Z_mod_plus_full. change (4064 mod 4096) with 4064. try (generalize alloc_ceiling_val); clear - MLE; try pose proof alloc_ceiling_val. lia. }
  rewrite EMW in GW.
  assert (TK : ticks_ok st) by exact (ci_ticks _ _ (Mallx0l.areach_cinv_proof _ _ AR)).
  assert (LE8 : forall v : word, length (le8 v) = 8%nat) by (intros; apply length_le8).
  pose proof NBC as NBC'. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). pose proof GC as GC'. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
  assert (EmE : forall x : word, ~ (G + 16 <= bv_unsigned x < G + 24) -> ~ (G + 32 <= bv_unsigned x < G + 40) -> bv_unsigned x <> NB + ND - 4 -> mE x = mK x).
  { intros x X1 X2 X3. unfold mE, m2, m1.
    rewrite (wtm_other m2 (NB + ND - 4) [b8 0] x) by (cbn [length]; try (generalize alloc_ceiling_val); clear - X3 NB0 NBC' ND4096; try pose proof alloc_ceiling_val; lia). unfold m2.
    rewrite (wtm_other m1 (G + 32) _ x) by (rewrite ?LE8; try (generalize alloc_ceiling_val); clear - X2 GC' G0'; try pose proof alloc_ceiling_val; lia). unfold m1.
    rewrite (wtm_other mK (G + 16) _ x) by (rewrite ?LE8; try (generalize alloc_ceiling_val); clear - X1 GC' G0'; try pose proof alloc_ceiling_val; lia). reflexivity. }
  assert (MONO_E : forall x : word, mK x <> None -> mE x <> None).
  { intros x Hx. unfold mE, m2, m1. apply wtm_mono; [try (generalize alloc_ceiling_val); clear - NB0 ND4096; try pose proof alloc_ceiling_val; lia| cbn [length]; try (generalize alloc_ceiling_val); clear - NBC'; try pose proof alloc_ceiling_val; lia|].
    apply wtm_mono; [try (generalize alloc_ceiling_val); clear - G0'; try pose proof alloc_ceiling_val; lia| rewrite LE8; try (generalize alloc_ceiling_val); clear - GC'; try pose proof alloc_ceiling_val; lia|]. apply wtm_mono; [try (generalize alloc_ceiling_val); clear - G0'; try pose proof alloc_ceiling_val; lia| rewrite LE8; try (generalize alloc_ceiling_val); clear -GC'; try pose proof alloc_ceiling_val; lia|]. exact Hx. }
  assert (COPY' : forall o, 0 <= o < MI_Wje4.OLDL st g -> o < ND -> o <> ND - 4 -> mE (wa (NB + o)) = m (wa (r_base r + o))).
  { intros o Ho1 Ho2 Ho3. change (MI_Wje4.OLDL st g) with OLDL in Ho1.
    rewrite EmE by (unfold wa; rewrite unsigned_lit by (try (generalize alloc_ceiling_val); clear - Ho1 Ho2 NB0 NBC'; try pose proof alloc_ceiling_val; lia); try (generalize alloc_ceiling_val); clear - Ho1 Ho2 Ho3 NB0 NBC' GN; try pose proof alloc_ceiling_val; lia). apply COPYK. try (generalize alloc_ceiling_val); clear - Ho1 Ho2; try pose proof alloc_ceiling_val; lia. }
  assert (ENDB : bytes_at rsegs mE (NB + ND - 4) [b8 0]) by (unfold mE; apply bytes_at_write_same; cbn [length]; try (generalize alloc_ceiling_val); clear - NB0 ND4096 NBC'; try pose proof alloc_ceiling_val; lia).
  assert (MAPPED : wr_at rsegs mE NB ND).
  { split; [try (generalize alloc_ceiling_val); clear - NB0; try pose proof alloc_ceiling_val; lia|]. split; [try (generalize alloc_ceiling_val); clear - NBC'; try pose proof alloc_ceiling_val; lia|]. intros i0 Hi0. rewrite p0_wview_overlay by (unfold wa; rewrite unsigned_lit by (try (generalize alloc_ceiling_val); clear - NB0 NBC' Hi0; try pose proof alloc_ceiling_val; lia); try (generalize alloc_ceiling_val); clear - NIMG Hi0 NB0; try pose proof alloc_ceiling_val; lia).
    apply MONO_E. apply NEWM. exact Hi0. }
  assert (OUT' : forall a0, 0 <= a0 < alloc_ceiling -> ~ (NB <= a0 < NB + ND) -> ~ (r_base r <= a0 < r_base r + MI_Wje4.OLDL st g) ->
            ~ (G + 16 <= a0 < G + 24) -> ~ (G + 32 <= a0 < G + 40) -> mE (wa a0) = m (wa a0)).
  { intros a0 H0 H1 H2 H3 H4. change (MI_Wje4.OLDL st g) with OLDL in H2. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
    rewrite EmE by (unfold wa; rewrite unsigned_lit by (try (generalize alloc_ceiling_val); clear - H0; try pose proof alloc_ceiling_val; lia); try (generalize alloc_ceiling_val); clear - H1 H3 H4 NB0 ND4096; try pose proof alloc_ceiling_val; lia). apply OUTK; [idtac; try (generalize alloc_ceiling_val); clear - H0; try pose proof alloc_ceiling_val; lia| exact H1| exact H2]. }
  pose proof (remap_C st L BLs LS rid r g NB ND INV Hg SC63 Hr ND4096 NDA NDX NB0 NBA NBC DISJ m mE MRP NBRF COPY' GM GW ENDB MAPPED OUT') as [MRE TKE].
  fold stE in MRE, TKE.
  pose proof (E_stride_g _ _ _ _ _ _ _ _ INV Hg SC63 ND4096 NDA NDX NB0) as STR'. fold stE in STR'.
  pose proof (ab_mrep (Clg:=Clg) (MI_Wje4.X1 rid) stE L' (MI_Wje4.BL1 BLs rid) LS (rid, 16) off g (rid, 0) 0 n b3 INVE eq_refl
               (proj2 (E_hosts st rid g NB ND (rid, 0) g) Hg)
               ltac:(rewrite E_last, L0; lia)
               (E_Ec _ _ _ _ _ _ _ _ INV Hg SC63 ND4096 NDA NDX NB0)
               HOFF N0
               ltac:(rewrite STR'; try (generalize alloc_ceiling_val); clear - FITn; try pose proof alloc_ceiling_val; unfold UNIT, IB in *; lia)
               ltac:(rewrite STR'; try (generalize alloc_ceiling_val); clear - NDT FITn; try pose proof alloc_ceiling_val; unfold UNIT, IB in *; lia)
               B3 mE (MI_Wje4.r' NB ND) MRE TKE (E_rid st rid g NB ND) eq_refl ltac:(cbn; lia)) as AB.
  cbn [fst snd r_len r_base MI_Wje4.r' Malloc.r_len Malloc.r_base aadd] in AB. rewrite STR', (E_last st rid g NB ND g), L0 in AB.
  specialize (AB ltac:(rewrite round_up_pg_aligned by exact NDA; unfold UNIT; lia)). destruct AB as [MRF TKF]. fold stF in MRF, TKF.
  replace (NB + (16 + UNIT * off)) with (NB + UNIT * off + 16) in MRF by lia.
  replace (NB + (16 + (ND - UNIT - IB))) with (NB + ND - 4) in MRF by (unfold UNIT, IB; lia).
  assert (MRF' : mrep stF (remap_mem mK G NB ND (UNIT * off) n mword b3)) by exact MRF.
  clear MRF. set (mF := remap_mem mK G NB ND (UNIT * off) n mword b3) in *.
  (* [comment removed for export] *)
  destruct OW as [(L2 & SR2 & HK2 & INCL2) [ND2 _]].
  assert (EMS : forall l : list block, map fst (map blk_id l) = map blk_slot l) by (intros l; rewrite map_map; reflexivity).
  rewrite EMS in ND2, INCL2.
  assert (SLOT_INJ : forall x y, In x LB -> In y LB -> blk_slot x = blk_slot y -> x = y) by (intros x y Hx Hy E; exact (heap_slot_inj s LB m x y HP Hx Hy E)).
  pose proof (Malls6g.areach_facts_proof _ _ AR) as MF.
  assert (BSEP : forall y, In y LB -> y <> b -> fst (blk_slot y) <> rid
            /\ (blk_addr y + blk_size y <= NB \/ NB + ND <= blk_addr y) /\ (blk_addr y + blk_size y <= r_base r \/ r_base r + OLDL <= blk_addr y)
            /\ 0 <= blk_size y /\ 4096 <= blk_addr y /\ blk_addr y + blk_size y <= alloc_ceiling
            /\ (blk_addr y + blk_size y <= G \/ G + 40 <= blk_addr y)).
  { intros y Hy NEy. assert (IN0y : In y LB0) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hy]).
    (first [ pose proof ((Forall2_In_l _ _ _ _ CR IN0y)) as dR_30; dex1 dR_30 as ky; destruct dR_30 as [Hky (YS & YZ & YA)] | pose proof ((Forall2_In_l _ _ _ _ CR IN0y)) as dR_30; dand3 dR_30 as ky Hky (YS & YZ & YA) | destruct (Forall2_In_l _ _ _ _ CR IN0y) as (ky & Hky & (YS & YZ & YA)) ]).
    assert (NR : fst (blk_slot y) <> rid).
    { intros E. pose proof (rm_only_block (Clg:=Clg) st L BLs LS rid g off (blk_size b) NB ND INV Hk Hg SC63 ND4096 NB0 ky Hky ltac:(rewrite <- YS; exact E)) as ->.
      cbn [bslot fst] in YS. apply NEy. apply (SLOT_INJ y b Hy Hb). rewrite YS. exact (eq_sym EC). }
    (first [ pose proof ((rblock_inside_strict st LB0 m y MF MRP IN0y)) as dR_31; dex1 dR_31 as ry; dand8 dR_31 as Hry Kry LOy HIy SZy R4y RCy RIy | pose proof ((rblock_inside_strict st LB0 m y MF MRP IN0y)) as dR_31; dand9 dR_31 as ry Hry Kry LOy HIy SZy R4y RCy RIy | destruct (rblock_inside_strict st LB0 m y MF MRP IN0y) as (ry & Hry & Kry & LOy & HIy & SZy & R4y & RCy & RIy) ]).
    pose proof (DISJ _ _ NR Hry) as D1. unfold region_live_range in D1. rewrite Kry in D1.
    assert (LRr : lr_lo r = r_base r) by (apply lr_lo_group; exact Kr). pose proof (lr_lo_group ry Kry) as LRy.
    pose proof (DJ _ _ rid r Hry Hr NR) as D2. rewrite LRr, LRy, <- OT in D2.
    assert (NEya : fst (blk_slot y) <> fst a) by (intros E; rewrite E, Hra in Hry; injection Hry as <-; exact (NK Kry)).
    pose proof (DJ _ _ (fst a) ra Hry Hra NEya) as D3. rewrite LRy in D3.
    split; [exact NR|]. rewrite HG, Ca. clear - D1 D2 D3 LOy HIy SZy R4y RCy LRa LRa' Sa1 Hkk; try pose proof alloc_ceiling_val. splits; lia. }
  assert (BRNG : r_base r + 16 <= blk_addr b /\ blk_addr b + blk_size b <= r_base r + OLDL - 4 /\ NB + 16 <= NB + 16 + UNIT * off /\ NB + 16 + UNIT * off + n <= NB + ND - 4).
  { pose proof (rb_fit _ _ _ _ _ _ _ _ _ _ _ _ RB) as FT. rewrite STR in FT. rewrite HA, EC. cbn [snd]. try (generalize alloc_ceiling_val); clear - FT HOFF OLD0 FITn N0; try pose proof alloc_ceiling_val. unfold UNIT, IB in *. lia. }
  set (A' := NB + 16 + UNIT * off) in *.
  set (f := fun x : block => if aptr_eqb (blk_slot x) c then (blk_id x, A', n) else x).
  change (lb_remap b A' n LB) with (map f LB).
  assert (Fb : f b = (blk_id b, A', n)) by (unfold f; fold c; rewrite aptr_eqb_refl; reflexivity).
  assert (Fo : forall x, In x LB -> x <> b -> f x = x).
  { intros x Hx NE. unfold f. destruct (MI_Kit.aptr_eqb_spec (blk_slot x) c) as [E|NE']; [exfalso; apply NE; apply (SLOT_INJ x b Hx Hb); exact E| reflexivity]. }
  assert (FS : forall x, blk_slot (f x) = blk_slot x) by (intros x0; unfold f; destruct (aptr_eqb (blk_slot x0) c); reflexivity).
  assert (FSm : forall l : list block, map blk_slot (map f l) = map blk_slot l) by (intros l; rewrite map_map; apply map_ext; intros x0; apply FS).
  (* [comment removed for export] *)
  destruct (stF_ctrl st rid g off n NB ND b3) as [CE _]. fold stF in CE.
  assert (RGF : s_regions stF = <[rid := MI_Wje4.r' NB ND]> (s_regions st)) by (rewrite (ce_regions _ _ CE); reflexivity).
  assert (CF_other : forall p, fst p <> rid -> conc stF p = conc st p).
  { intros p NE. unfold conc, get_region. rewrite RGF, lookup_insert_ne by congruence. reflexivity. }
  assert (CF_rid : forall o, conc stF (rid, o) = NB + o).
  { intros o. unfold conc, get_region. rewrite RGF. cbn [fst snd]. rewrite lookup_insert_eq. reflexivity. }
  set (s' := mkPS (strip stF) (ps_brk s) (ps_fa s) (ps_so s)).
  (first [ pose proof ((rm_ptrs st L BLs LS rid r g 0 0 INV Hg SC63 Hr)) as dR_32; dand8 dR_32 as _ _ _ _ _ _ PB _ | pose proof (rm_ptrs st L BLs LS rid r g 0 0 INV Hg SC63 Hr) as (_ & _ & _ & _ & _ & _ & PB & _) ]).
  assert (HP' : HEAP s' (map f LB) mF).
  { exists stF, (map f LB0). split; [apply Permutation_map; exact PERM|]. split; [reflexivity|]. split; [exact MRF'|]. split.
    - (* [comment removed for export] *) unfold brk_link, ctx in BL |- *. cbn [s' ps_brk]. rewrite (ce_ctx _ _ CE). change (s_ctx (stC st rid g NB ND)) with (s_ctx st).
      unfold ctx in PB. destruct (c_brk (s_ctx st)) as [| |bq bo]; try exact Logic.I. rewrite CF_other by exact PB. exact BL.
    - exists L', LS, (bl_resize (rid, 16) n BLs). split; [exact INV'|]. split; [unfold L', MI_Wje4.L'; cbn [ld_live KInv.set_groups]; rewrite bl_resize_slots; exact LIVE|].
      split; [unfold L', MI_Wje4.L'; cbn [ld_resv KInv.set_groups]; exact RESV|]. split; [rewrite (ce_secret _ _ CE); exact SEC|].
      unfold CORR, bl_resize. eapply Forall2_map_map'; [exact CR|].
      (intros x y Hx Hy; (first [ intro dR_40; dand3 dR_40 as C1 C2 C3 | intros (C1 & C2 & C3) ])). unfold corr1, f. rewrite C1, <- EC. fold c.
      destruct (MI_Kit.aptr_eqb_spec (bslot y) c) as [E|NE]; cbn [blk_slot blk_size blk_addr blk_id bslot bsize boff fst snd].
      + split; [exact C1|]. split; [reflexivity|].
        pose proof (rm_only_block st L BLs LS rid g off (blk_size b) NB ND INV Hk Hg SC63 ND4096 NB0 y Hy ltac:(rewrite E, EC; reflexivity)) as ->.
        cbn [boff bslot fst snd]. rewrite CF_rid. unfold A'. clear; lia.
      + split; [exact C1|]. split; [exact C2|]. rewrite CF_other; [exact C3|].
        intros EQr. apply NE. pose proof (rm_only_block st L BLs LS rid g off (blk_size b) NB ND INV Hk Hg SC63 ND4096 NB0 y Hy EQr) as ->. rewrite EC. reflexivity. }
  exists s'. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  assert (A'R : NB + 16 <= A' /\ A' + n <= NB + ND - 4) by (unfold A'; try (generalize alloc_ceiling_val); clear - BRNG; try pose proof alloc_ceiling_val; lia).
  split.
  { (* [comment removed for export] *) split; [exact HP'|]. split; [| split].
    - (* [comment removed for export] *) cbn [ia_s ia_LB ia_rr]. split; [| split; [rewrite EMS, FSm; exact ND2| exact Logic.I]].
      exists L'. split; [exists stF, (bl_resize (rid, 16) n BLs), LS; split; [reflexivity|]; split; [exact INV'|];
                          unfold L', MI_Wje4.L'; cbn [ld_live KInv.set_groups]; rewrite bl_resize_slots; exact LIVE|].
      split; [exact HK'|]. rewrite EMS, FSm. unfold L', MI_Wje4.L'. cbn [ld_live KInv.set_groups]. rewrite LIVE.
      intros sl Hsl. apply in_map_iff in Hsl as (y & <- & Hy).
      assert (IN0y : In y LB0) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hy]).
      (first [ pose proof ((Forall2_In_l _ _ _ _ CR IN0y)) as dR_33; dex1 dR_33 as ky; destruct dR_33 as [Hky (YS & _ & _)] | pose proof ((Forall2_In_l _ _ _ _ CR IN0y)) as dR_33; dand3 dR_33 as ky Hky (YS & _ & _) | destruct (Forall2_In_l _ _ _ _ CR IN0y) as (ky & Hky & (YS & _ & _)) ]). rewrite YS. apply in_map. exact Hky.
    - (* [comment removed for export] *) cbn [ia_s ia_LB ia_rr]. apply (repl0_agree m _ RP). intros a0 Ha0. unfold MALLOC_REPLACED in Ha0.
      unfold mF. change (remap_mem mK G NB ND (UNIT * off) n mword b3) with (set_size_mem mE (NB + UNIT * off + 16) (NB + ND - 4) n b3).
      rewrite Instbrv.set_size_mem_outside; [| try (generalize alloc_ceiling_val); clear - A'R NB0; try pose proof alloc_ceiling_val; lia| exact N0| try (generalize alloc_ceiling_val); clear - A'R; try pose proof alloc_ceiling_val; lia| try (generalize alloc_ceiling_val); clear - NBC'; try pose proof alloc_ceiling_val; lia| rewrite unsigned_lit by (try (generalize alloc_ceiling_val); clear - Ha0; try pose proof alloc_ceiling_val; lia); try (generalize alloc_ceiling_val); clear - Ha0 A'R NIMG ND4096 NB0; try pose proof alloc_ceiling_val; lia].
      change (Z_to_bv 64 a0) with (wa a0). apply OUT'; [(let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); try (generalize alloc_ceiling_val); clear - Ha0; try pose proof alloc_ceiling_val; lia| try (generalize alloc_ceiling_val); clear - Ha0 NIMG ND4096; try pose proof alloc_ceiling_val; lia| change (MI_Wje4.OLDL st g) with OLDL; try (generalize alloc_ceiling_val); clear - Ha0 RIMG O4096; try pose proof alloc_ceiling_val; lia| try (generalize alloc_ceiling_val); clear - Ha0 GI; try pose proof alloc_ceiling_val; lia| try (generalize alloc_ceiling_val); clear - Ha0 GI; try pose proof alloc_ceiling_val; lia].
    - (* [comment removed for export] *)
      cbn [ia_s ia_LB ia_rr]. change (ps_m s') with (strip stF).
      assert (PBQ : Permutation (map bs (blk0 LB)) (map bs BLs)).
      { rewrite <- (corr_bs st LB0 BLs CR). apply Permutation_map. unfold blk0. apply Permutation_map. apply Permutation_sym. exact PERM. }
      rewrite <- Hst in QVs. destruct (QV_to_witness st BLs (blk0 LB) QVs PBQ) as [SI0 HAQ0].
      pose proof (ML'_eq NB ND ND4096 NDA NDX NB0) as [MLE MLR].
      assert (FITQ : MI_Wje4.ML' ND * 4096 <= bigmap n).
      { rewrite MLE. unfold bigmap. pose proof (MI_Cnt.round_up_pg_spec (n + IB + UNIT)) as [[R1 R2] R3].
        pose proof (Z.div_mod ND 4096 ltac:(lia)) as DM1. rewrite NDA in DM1.
        pose proof (Z.div_mod (round_up_pg (n + IB + UNIT)) 4096 ltac:(lia)) as DM2. rewrite R3 in DM2.
        clear - DM1 DM2 R1 NDT HOFF. unfold PGSZ, UNIT, IB in *. lia. }
      assert (HsQ : s_slots st !! (rid, 16) = Some (g, 0)) by exact (rm_slot st L BLs LS rid g NB ND INV Hg SC63 ND4096 NB0).
      pose proof (SINV_remap x0 st L BLs LS rid r (MI_Wje4.r' NB ND) g (rid, 16) (MI_Wje4.ML' ND) n INV HsQ SC63 Hr Kr eq_refl
                    ltac:(clear - MLR; lia) ltac:(unfold MMAP_THRESHOLD; clear - Hn; lia) FITQ SI0) as SIR.
      pose proof (AQ_remap x0 st L BLs LS rid (MI_Wje4.r' NB ND) g (rid, 16) (MI_Wje4.ML' ND) n INV HsQ SC63
                    ltac:(unfold MMAP_THRESHOLD; clear - Hn; lia) SI0 HAQ0) as AQR.
      change (stR st rid (MI_Wje4.r' NB ND) g (MI_Wje4.ML' ND)) with (stC st rid g NB ND) in SIR, AQR.
      apply (QV_of_witness stF (bl_resz (rid, 16) n BLs) (blk0 (map f LB)) (SINV_ctrl x0 _ stF _ CE SIR) (AQ_ctrl _ stF _ PN CE AQR)).
      assert (E0 : blk0 (map f LB) = bl_resz (rid, 16) n (blk0 LB)).
      { apply blk0_map_resize. intros x. unfold f. rewrite <- EC. fold c. destruct (aptr_eqb (blk_slot x) c); cbn [blk_slot blk_size blk_id fst snd]; auto. }
      rewrite E0. apply bl_resz_perm. apply Permutation_sym. exact PBQ. }
  split.
  { (* [comment removed for export] *)
    destruct (lb_bytes_map_one f b LB (heap_ids_nodup s LB m HP) Hb Fo) as [D1 D2]. rewrite D1, D2, Fb. cbn [blk_size snd]. split; reflexivity. }
  split.
  { (* [comment removed for export] *) unfold p0_live. cbn [ia_LB]. rewrite (find_blk_map_hit f LB b A' Hb); [rewrite Fb; reflexivity| rewrite Fb; reflexivity|].
    intros x Hx NE. split; [exact (Fo x Hx NE)|]. (first [ pose proof ((BSEP x Hx NE)) as dR_34; dand5 dR_34 as _ X1 _ X3 _ | destruct (BSEP x Hx NE) as (_ & X1 & _ & X3 & _) ]). try (generalize alloc_ceiling_val); clear - X1 X3 A'R N0; try pose proof alloc_ceiling_val. lia. }
  split.
  { (* [comment removed for export] *) intros q' Q1 Q2. unfold p0_live. cbn [ia_LB]. apply find_blk_map_other. intros x Hx.
    destruct (Classical_Prop.classic (x = b)) as [->|NE].
    - rewrite Fb. cbn [blk_addr blk_size fst snd]. destruct (Z.eqb_spec A' q'); [congruence|]. destruct (Z.eqb_spec (blk_addr b) q'); [congruence|]. split; [reflexivity| discriminate].
    - rewrite (Fo x Hx NE). split; [reflexivity| reflexivity]. }
  split.
  { (* [comment removed for export] *) intros NEB. split.
    - unfold p0_live. cbn [ia_LB]. rewrite find_blk_none; [reflexivity|]. intros x Hx.
      destruct (Classical_Prop.classic (x = b)) as [->|NE]; [unfold A'; clear - BRNG NEB HA EC; try pose proof alloc_ceiling_val; rewrite HA, EC; cbn [snd]; lia|].
      (first [ pose proof ((BSEP x Hx NE)) as dR_35; dand5 dR_35 as _ X1 _ X3 _ | destruct (BSEP x Hx NE) as (_ & X1 & _ & X3 & _) ]). try (generalize alloc_ceiling_val); clear - X1 X3 A'R N0; try pose proof alloc_ceiling_val. lia.
    - unfold p0_live. cbn [ia_LB]. rewrite find_blk_none; [reflexivity|]. intros x' Hx'. apply in_map_iff in Hx' as (x & <- & Hx).
      destruct (Classical_Prop.classic (x = b)) as [->|NE]; [rewrite Fb; cbn [blk_addr fst snd]; unfold A'; clear - BRNG NEB HA EC; try pose proof alloc_ceiling_val; rewrite HA, EC; cbn [snd]; lia|].
      rewrite (Fo x Hx NE). (first [ pose proof ((BSEP x Hx NE)) as dR_36; dand5 dR_36 as _ _ X2 X3 _ | destruct (BSEP x Hx NE) as (_ & _ & X2 & X3 & _) ]). try (generalize alloc_ceiling_val); clear - X2 X3 BRNG OLD0; try pose proof alloc_ceiling_val. lia. }
  split.
  { (* [comment removed for export] *) intros a0. unfold in_block. split.
    - ((first [ intro dR_41; dex1 dR_41 as x'; destruct dR_41 as [Hx' R] | intro dR_41; dand3 dR_41 as x' Hx' R | intros (x' & Hx' & R) ])). apply in_map_iff in Hx' as (x & <- & Hx).
      destruct (Classical_Prop.classic (x = b)) as [->|NE]; [left; rewrite Fb in R; cbn [blk_addr blk_size fst snd] in R; exact R|].
      right. exists x. rewrite (Fo x Hx NE) in R. auto.
    - intros [R|(y & Hy & NE & R)]; [exists (f b); split; [apply in_map; exact Hb| rewrite Fb; cbn [blk_addr blk_size fst snd]; exact R]|].
      exists (f y). split; [apply in_map; exact Hy|]. rewrite (Fo y Hy NE). exact R. }
  split.
  { intros a0. unfold in_block. split.
    - ((first [ intro dR_42; dex1 dR_42 as x; destruct dR_42 as [Hx R] | intro dR_42; dand3 dR_42 as x Hx R | intros (x & Hx & R) ])). destruct (Classical_Prop.classic (x = b)) as [->|NE]; [left; exact R| right; exists x; auto].
    - intros [R|(y & Hy & NE & R)]; [exists b; auto| exists y; auto]. }
  split.
  { intros y Hy NE. (first [ pose proof ((BSEP y Hy NE)) as dR_37; dand7 dR_37 as _ X1 X2 X3 X4 X5 _ | destruct (BSEP y Hy NE) as (_ & X1 & X2 & X3 & X4 & X5 & _) ]). idtac. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). clear - X1 X2 X3 X4 X5; try pose proof alloc_ceiling_val. splits; lia. }
  split; [exact GN|]. split; [exact GB|].
  (* [comment removed for export] *)
  intros a0 Ha0.
  assert (HZ : heap_zone LayoutP0 a0) by (apply (proj2 (heap_zone_p0 a0)); try (generalize alloc_ceiling_val); clear - Ha0 GC' GI G0'; try pose proof alloc_ceiling_val; lia).
  assert (NIB : forall y, In y LB -> ~ (blk_addr y <= a0 < blk_addr y + blk_size y)).
  { intros y Hy R. destruct (Classical_Prop.classic (y = b)) as [->|NE].
    - try (generalize alloc_ceiling_val); clear - R BRNG GB Ha0 O4096; try pose proof alloc_ceiling_val. lia.
    - (first [ pose proof ((BSEP y Hy NE)) as dR_38; dand7 dR_38 as _ _ _ _ _ _ X6 | destruct (BSEP y Hy NE) as (_ & _ & _ & _ & _ & _ & X6) ]). try (generalize alloc_ceiling_val); clear - R X6 Ha0; try pose proof alloc_ceiling_val. lia. }
  split; (right; split; [exact HZ|]); cbn [ia_LB]; unfold in_block.
  - ((first [ intro dR_43; dex1 dR_43 as y; destruct dR_43 as [Hy R] | intro dR_43; dand3 dR_43 as y Hy R | intros (y & Hy & R) ])). exact (NIB y Hy R).
  - ((first [ intro dR_44; dex1 dR_44 as x'; destruct dR_44 as [Hx' R] | intro dR_44; dand3 dR_44 as x' Hx' R | intros (x' & Hx' & R) ])). apply in_map_iff in Hx' as (x & <- & Hx).
    destruct (Classical_Prop.classic (x = b)) as [->|NE]; [rewrite Fb in R; cbn [blk_addr blk_size fst snd] in R; try (generalize alloc_ceiling_val); clear - R A'R GN Ha0; try pose proof alloc_ceiling_val; lia|].
    rewrite (Fo x Hx NE) in R. exact (NIB x Hx R).
Qed.

End CEIL.
