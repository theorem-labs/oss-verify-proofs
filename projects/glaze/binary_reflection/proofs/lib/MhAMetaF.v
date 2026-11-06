(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
#[local] Ltac Zify.zify ::= WdZS.wd_zs_stock.   (* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.glaze.binary_reflection.images Require Import Plain.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhTac OSSVerify.Proofs.glaze.binary_reflection.lib.MhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.MhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate OSSVerify.Proofs.glaze.binary_reflection.lib.MhAMetaN OSSVerify.Proofs.glaze.binary_reflection.lib.MhNest2 OSSVerify.Proofs.glaze.binary_reflection.lib.MhKXSys OSSVerify.Proofs.glaze.binary_reflection.lib.MhMmapK OSSVerify.Proofs.glaze.binary_reflection.lib.MhAMetaR. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.MhTac OSSVerify.Proofs.glaze.binary_reflection.lib.MhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.MhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate.MhExt OSSVerify.Proofs.glaze.binary_reflection.lib.MhAMetaN.MhExtG OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate.MhList OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate.MhRepT OSSVerify.Proofs.glaze.binary_reflection.lib.MhRotate.MhCover OSSVerify.Proofs.glaze.binary_reflection.lib.MhAMetaN.MhNtfLib OSSVerify.Proofs.glaze.binary_reflection.lib.MhNest2.MhNest OSSVerify.Proofs.glaze.binary_reflection.lib.MhKXSys.MhGap OSSVerify.Proofs.glaze.binary_reflection.lib.MhMmapK.MhAcct OSSVerify.Proofs.glaze.binary_reflection.lib.MhAMetaN OSSVerify.Proofs.glaze.binary_reflection.lib.MhAMetaR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Fail.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (st : mst) (L : list (Z * Z)) (M M' : mem).
  Hypothesis HWF : WF st L.
  Hypothesis HREP : REP st M.
  Variables (regions' : list region) (brk' : brk_state) (cur' ac' sh' cb' : Z).
  #[local] Notation cx := (s_ctx st).
  #[local] Notation areas := (s_areas st).
  Definition fcx : ctx_rec :=
    CX (c_secret cx) (c_mmap_ctr cx) (c_free_head cx) (c_avail_meta cx) (c_avail_cnt cx) ac' sh' (c_area_head cx) (c_area_tail cx) cur'
       (c_active cx) (c_usage cx) (c_unmap_seq cx) (c_bounces cx) (c_seq cx) cb'.
  Definition fst : mst :=
    MST fcx areas (s_meta st) (s_flist st) (s_alist st) (s_groups st) (s_ai st) (s_kind st)
        (s_slot st) regions' brk' (s_canary st) (s_errno st) (s_limbo st).




  Lemma SG : same_groups st fst.
  Proof. constructor; intros; try reflexivity. apply slot_sim_refl. Qed.
  #[local] Notation yG := (SG).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis HRgrp : forall b len x, In (RG b len (RGroup x)) regions' <-> In (RG b len (RGroup x)) (s_regions st).
  Hypothesis HRsup : forall r, In r (s_regions st) -> In r regions'.
  Hypothesis Hgo : guard_of brk' = guard_of (s_brk st).
  Hypothesis Hac' : 0 <= ac'.
  Hypothesis Hcur' : ac' > 0 -> exists b len e, In (RG b len (RMeta e)) regions' /\ 0 <= e /\
                       cur' = b + 4096 * (1 + e) /\ cur' + 4096 * ac' = b + len.
  Hypothesis Hsh' : 0 <= sh' /\ sh' <= Z.of_nat (length areas) + 1 /\ (ac' = 0 -> sh' <= Z.of_nat (length areas)).
  Hypothesis Hshacc' : 2 ^ (sh' + 1) <= Z.of_nat (length areas) + ac' + sh' + 2.
  Hypothesis Hbrk' : match brk' with
                     | BrkUntried => cb' = 0
                     | BrkLive b0 b _ => cb' = b /\ b0 mod 4096 = 0 /\ b mod 4096 = 0 /\ IMG_HI <= b0 /\ b0 + 8192 <= b /\ b <= CEIL
                     | BrkDead _ => cb' = 2 ^ 64 - 1
                     end.

  Lemma f_wf_ctx : wf_ctx fst.
  Proof.
    destruct (WF_ctx st L HWF) as [A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 A18 A19].
    constructor; cbn -[Z.pow NSLOTS AREAMAX HEAPLO CEIL head_of Z.of_nat]; try assumption; lia.
  Qed.

  Lemma f_wf_areas : wf_areas fst.
  Proof.
    destruct (WF_areas st L HWF) as [A B C D]. constructor; cbn [s_areas s_regions s_brk fst]; try assumption.
    rewrite Hgo. intros a Ha. destruct (D a Ha) as [(b & len & Hin & R)|(b & len & e & Hin & R)].
    - left. exists b, len. split; [apply HRsup; exact Hin | exact R].
    - right. exists b, len, e. split; [apply HRsup; exact Hin | exact R].
  Qed.

  Lemma f_wf_lists : wf_lists fst.
  Proof. destruct (WF_lists st L HWF); constructor; assumption. Qed.

  Lemma f_wf_group : forall x, is_group st x -> wf_group fst L x.
  Proof.
    intros x Hx. pose proof (wG_each st L (WF_groups st L HWF) x Hx) as WG.
    destruct WG as [U NF Wr Avr Frr Me Ai Fb Sc St Av Fr Avai High Lsc Nfr S63 Part Full Kind Under FF Slots Depth Fit Single Q16 Pnd].
    constructor; try assumption.
    cbn [s_kind s_regions fst]. destruct (s_kind st x) as [|hm j hoff]; [|exact Kind].
    destruct Kind as (K1 & K2 & K3 & K4). split; [exact K1|]. split; [apply HRgrp; exact K2|]. split; assumption.
  Qed.

  Lemma f_wf_groups : wf_groups fst L.
  Proof.
    destruct (WF_groups st L HWF) as [ND EACH ONE REG FR0 OTH LIM ONEFF].
    constructor; cbn [s_groups s_limbo s_regions fst]; try assumption.
    - intros x Hx. apply f_wf_group. exact Hx.
    - intros b len x Hin. apply HRgrp in Hin. exact (REG b len x Hin).
  Qed.

  Lemma f_wf_geom : wf_geom fst.
  Proof.
    destruct (WF_geom st L HWF) as [INR CELLS AREA APC APA APD GC GA GAR SPAN]. constructor; cbn [s_regions fst]; try assumption.
    intros x Hx. destruct (INR x Hx) as (r & Hr & R1 & R2). exists r. split; [apply HRsup; exact Hr | split; assumption].
  Qed.

  (* [comment removed for export] *)
  Hypothesis HWR' : wf_regions fst.
  Hypothesis HWI' : wf_img fst.

  Lemma f_WF : WF fst L.
  Proof.
    split; [exact f_wf_ctx|]. split; [exact f_wf_areas|]. split; [exact f_wf_lists|]. split; [exact f_wf_groups|].
    split; [exact f_wf_geom|]. split; [exact (wf_live_ext st fst L yG (WF_live st L HWF)) |]. split; [exact HWR' | exact HWI'].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition fctxW (a : Z) : Prop :=
    (ctx_avail_meta_area_count <= a < ctx_avail_meta_area_count + 16) \/ (ctx_avail_meta_areas <= a < ctx_avail_meta_areas + 8) \/
    (ctx_brk <= a < ctx_brk + 8).
  (* [comment removed for export] *)
  Hypothesis HMlow : agree_on (fun a => IMG_LO <= a < CTX) M M'.
  Hypothesis HMctx : agree_on (fun a => CTX <= a < CTX_END /\ ~ fctxW a) M M'.
  Hypothesis HMac : cell M' ctx_avail_meta_area_count 8 ac'.
  Hypothesis HMsh : cell M' ctx_meta_alloc_shift 8 sh'.
  Hypothesis HMcur : cell M' ctx_avail_meta_areas 8 cur'.
  Hypothesis HMcb : cell M' ctx_brk 8 cb'.
  Hypothesis HMkeep : forall a, dfoot st a -> M (Z_to_bv 64 a) <> None -> M' (Z_to_bv 64 a) <> None.
  Hypothesis HMareas : forall ar a, In ar areas -> ar <= a < ar + 4096 -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
  Hypothesis HMgrp : forall t a, is_group st t -> s_kind st t = GTop -> g_mem st t <= a < g_map_end st t -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).

  Lemma f_rep_statics : rep_statics fst M'.
  Proof. apply (rep_statics_tr st fst M M' HREP HMkeep HMlow); reflexivity. Qed.

  Lemma f_rep_ctx : rep_ctx fst M'.
  Proof.
    pose proof (rp_ctx st M HREP) as [C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17].
    assert (TR : forall a k v, CTX <= a -> a + Z.of_nat k <= CTX_END ->
              (a + Z.of_nat k <= ctx_avail_meta_area_count \/ (ctx_avail_meta_area_count + 16 <= a /\ a + Z.of_nat k <= ctx_avail_meta_areas) \/
               (ctx_avail_meta_areas + 8 <= a /\ a + Z.of_nat k <= ctx_brk)) ->
              cell M a k v -> cell M' a k v).
    { intros a k v H1 H2 H3 C. eapply cell_agree; [unfold CTX in *; lia | unfold CTX_END, CTX in *; cbn; lia | | exact C].
      eapply agree_on_mono; [exact HMctx|]. cbn. intros b Hb. split; [lia|]. unfold fctxW.
      unfold ctx_avail_meta_area_count, ctx_avail_meta_areas, ctx_brk, CTX, CTX_END in *. lia. }
    Ltac ctxg TR := eapply TR; [ cbn; unfold ctx_secret, ctx_init_done, ctx_mmap_counter, ctx_free_meta_head, ctx_avail_meta,
               ctx_avail_meta_count, ctx_avail_meta_area_count, ctx_meta_alloc_shift, ctx_meta_area_head, ctx_meta_area_tail,
               ctx_avail_meta_areas, ctx_active, ctx_usage, ctx_unmap_seq, ctx_bounces, ctx_seq, ctx_brk, CTX; lia
             | cbn; unfold ctx_secret, ctx_init_done, ctx_mmap_counter, ctx_free_meta_head, ctx_avail_meta,
               ctx_avail_meta_count, ctx_avail_meta_area_count, ctx_meta_alloc_shift, ctx_meta_area_head, ctx_meta_area_tail,
               ctx_avail_meta_areas, ctx_active, ctx_usage, ctx_unmap_seq, ctx_bounces, ctx_seq, ctx_brk, CTX_END, CTX; lia
             | cbn; unfold ctx_secret, ctx_init_done, ctx_mmap_counter, ctx_free_meta_head, ctx_avail_meta,
               ctx_avail_meta_count, ctx_avail_meta_area_count, ctx_meta_alloc_shift, ctx_meta_area_head, ctx_meta_area_tail,
               ctx_avail_meta_areas, ctx_active, ctx_usage, ctx_unmap_seq, ctx_bounces, ctx_seq, ctx_brk, CTX_END, CTX; lia
             | eauto ].
    constructor; cbn [s_ctx fst fcx c_secret c_mmap_ctr c_free_head c_avail_meta c_avail_cnt c_area_cnt c_shift c_area_head c_area_tail
                      c_cursor c_active c_usage c_unmap_seq c_bounces c_seq c_brk]; try assumption; try (ctxg TR).
    - intros sc Hsc. ctxg TR.
    - intros sc Hsc. ctxg TR.
    - intros i Hi. ctxg TR.
    - intros i Hi. ctxg TR.
  Qed.

  Lemma f_rep_areas : forall ar, In ar (s_areas fst) -> rep_area fst M' ar.
  Proof.
    apply (rep_areas_tr st fst L M M' HWF HREP HMkeep (fun _ => false)); try reflexivity.
    - intros ar a Har Ha NE. exfalso. exact (NE (HMareas ar a Har Ha)).
    - intros x Ux X. discriminate X.
  Qed.

  Lemma f_rep_groups : forall x, is_group fst x -> rep_group fst M' x.
  Proof.
    apply (rep_groups_tr st fst L M M' HWF HREP HMkeep).
    - intros x Hx. exact Hx.
    - intros x Hx. repeat split; reflexivity.
    - intros x Hx E. exact E.
    - intros x k Hx Hk. left. reflexivity.
    - intros x a Hx G. change (is_group st x) in Hx. apply (y_gcell st fst L yG HWF) in G; [|exact Hx].
      destruct (group_in_top st L HWF x Hx) as (t & Ht & Kt & T1 & T2 & _).
      pose proof (gcell_in_span st L HWF x a Hx G). apply (HMgrp t a Ht Kt). lia.
    - intros x a Hx G. left. apply (y_gcell st fst L yG HWF); [exact Hx | exact G].
  Qed.

  Lemma f_REP : REP fst M'.
  Proof.
    constructor; [exact f_rep_statics | exact f_rep_ctx | exact f_rep_areas | exact f_rep_groups].
  Qed.

End Fail.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section D.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (st : mst) (L : list (Z * Z)) (X : list (word * word)) (vm : VmMaps).
  Hypothesis HWF : WF st L.
  Hypothesis HLG : LEDGERX st X vm.
  #[local] Notation cx := (s_ctx st).
  (* [comment removed for export] *)
  Variable dead : bool.
  Definition d_brk : brk_state := if dead then BrkDead (guard_kind (s_brk st)) else s_brk st.
  Definition d_cb : Z := if dead then 2 ^ 64 - 1 else c_brk cx.
  Definition d_st : mst := fst st (s_regions st) d_brk (c_cursor cx) (c_area_cnt cx) (c_shift cx) d_cb.

  Lemma d_guard_of : guard_of d_brk = guard_of (s_brk st).
  Proof. unfold d_brk. destruct dead; [|reflexivity]. destruct (s_brk st) as [| b0 b gk | [[b0 gk]|]]; reflexivity. Qed.
  Lemma d_guard_noacc : guard_noacc d_brk = guard_noacc (s_brk st).
  Proof. unfold d_brk. destruct dead; [|reflexivity]. destruct (s_brk st) as [| b0 b gk | [[b0 gk]|]]; reflexivity. Qed.
  Lemma d_HRgrp : forall b len x, In (RG b len (RGroup x)) (s_regions st) <-> In (RG b len (RGroup x)) (s_regions st).
  Proof. intros; tauto. Qed.
  Lemma d_HRsup : forall r, In r (s_regions st) -> In r (s_regions st). Proof. intros r H; exact H. Qed.
  Lemma d_Hac' : 0 <= c_area_cnt cx. Proof. exact (wc_areacnt st (WF_ctx st L HWF)). Qed.
  Lemma d_Hcur' : c_area_cnt cx > 0 -> exists b len e, In (RG b len (RMeta e)) (s_regions st) /\ 0 <= e /\
                       c_cursor cx = b + 4096 * (1 + e) /\ c_cursor cx + 4096 * c_area_cnt cx = b + len.
  Proof. exact (wc_cursor st (WF_ctx st L HWF)). Qed.
  Lemma d_Hsh' : 0 <= c_shift cx /\ c_shift cx <= Z.of_nat (length (s_areas st)) + 1 /\ (c_area_cnt cx = 0 -> c_shift cx <= Z.of_nat (length (s_areas st))).
  Proof. exact (wc_shift st (WF_ctx st L HWF)). Qed.
  Lemma d_Hshacc' : 2 ^ (c_shift cx + 1) <= Z.of_nat (length (s_areas st)) + c_area_cnt cx + c_shift cx + 2.
  Proof. exact (wc_shacc st (WF_ctx st L HWF)). Qed.
  Lemma d_Hbrk' : match d_brk with
                  | BrkUntried => d_cb = 0
                  | BrkLive b0 b _ => d_cb = b /\ b0 mod 4096 = 0 /\ b mod 4096 = 0 /\ IMG_HI <= b0 /\ b0 + 8192 <= b /\ b <= CEIL
                  | BrkDead _ => d_cb = 2 ^ 64 - 1
                  end.
  Proof. unfold d_brk, d_cb. pose proof (wc_brk st (WF_ctx st L HWF)) as B. destruct dead; [reflexivity | exact B]. Qed.

  Lemma d_t_wf_regions : wf_regions d_st.
  Proof.
    destruct (WF_regions st L HWF) as [RNG DISJ ND LEN GB G63 MT MC BRK BL].
    constructor; cbn [s_regions s_brk s_ctx s_areas d_st fst fcx c_shift]; try assumption.
    unfold d_brk. destruct dead; [|exact BRK].
    destruct (s_brk st) as [|x0 x1 g|g]; cbn [guard_kind].
    - split; [|exact I]. rewrite filter_all_false; [cbn; lia|]. intros r Hr. destruct r as [rb rl [|ex|y]]; [exfalso; exact (BRK rb rl Hr) | reflexivity | reflexivity].
    - destruct BRK as (BR1 & BR2 & BR3). split; [exact BR2 | exact BR3].
    - exact BRK.
  Qed.
  Lemma d_t_wf_img : wf_img d_st.
  Proof. pose proof (WF_img st L HWF) as [WA WR]. constructor; cbn [s_areas s_regions d_st fst]; assumption. Qed.

  Lemma d_WF : WF d_st L.
  Proof.
    exact (f_WF st L HWF (s_regions st) d_brk (c_cursor cx) (c_area_cnt cx) (c_shift cx) d_cb
             d_HRgrp d_HRsup d_guard_of d_Hac' d_Hcur' d_Hsh' d_Hshacc' d_Hbrk' d_t_wf_regions d_t_wf_img).
  Qed.

  (* [comment removed for export] *)
  Lemma d_ledger : forall vm', vm_maps vm' = vm_maps vm -> vm_noaccess vm' = vm_noaccess vm -> vm_reserved vm' = vm_reserved vm ->
    alloc_top vm' = alloc_top vm -> (dead = false -> vm_brk vm' = vm_brk vm /\ vm_start_brk vm' = vm_start_brk vm) ->
    LEDGERX d_st X vm'.
  Proof.
    intros vm' E1 E2 E3 E4 E5. destruct HLG as [LM LN LB LR LT].
    constructor; cbn [s_regions s_brk d_st fst]; rewrite ?E1, ?E2, ?E3, ?E4.
    - exact LM.
    - unfold noacc_of. cbn [s_brk s_regions d_st fst]. rewrite d_guard_noacc. exact LN.
    - unfold d_brk. destruct dead; [exact I|]. destruct (E5 eq_refl) as [E6 E7]. rewrite E6, E7. exact LB.
    - exact LR.
    - exact LT.
  Qed.
End D.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section V.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (st : mst) (L : list (Z * Z)) (X : list (word * word)) (vm : VmMaps).
  Hypothesis HWF : WF st L.
  Hypothesis HLG : LEDGERX st X vm.
  Hypothesis XOK : xok X.
  Hypothesis Hcnt : Z.of_nat (length (s_areas st)) + 1 <= AREAMAX.
  #[local] Notation cx := (s_ctx st).
  #[local] Notation sh := (c_shift (s_ctx st)).
  Hypothesis Hac : c_area_cnt cx = 0.
  #[local] Notation N := (c4_N st).
  Variable p0 : Z.
  Hypothesis Hp0 : p0 mod 4096 = 0 /\ HEAPLO <= p0 /\ p0 + N <= CEIL.
  Hypothesis HRF : region_free (vm_reserved vm ++ vm_maps vm) (Z_to_bv 64 p0) (Z_to_bv 64 N) = true.
  Hypothesis Hp0img : p0 + N <= IMG_LO \/ IMG_HI <= p0.
  Variable dead : bool.

  Definition v_Rn : region := RG p0 N (RMeta 0).
  Definition v_regions : list region := v_Rn :: s_regions st.
  Definition v_ac : Z := 2 * 2 ^ sh - 1.
  Definition v_st : mst := fst st v_regions (d_brk st dead) (p0 + 4096) v_ac (sh + 1) (d_cb st dead).
  Definition v_vm : VmMaps :=
    mkVmMapsFull (vm_reserved vm) ((Z_to_bv 64 p0, Z_to_bv 64 N) :: vm_maps vm) ((Z_to_bv 64 p0, Z_to_bv 64 N) :: vm_noaccess vm)
                 (vm_start_brk vm) (vm_brk vm) (vm_limit vm) (vm_mmap_base vm) (vm_init_sp vm).

  Lemma v_sh_rng : 0 <= sh <= 11. Proof. exact (c4_sh_rng st L HWF Hcnt Hac p0). Qed.
  Lemma v_N_rng : 8192 <= N <= 2 ^ 24 /\ N mod 4096 = 0 /\ N = 4096 * (2 * 2 ^ sh). Proof. exact (c4_N_rng st L HWF Hcnt Hac p0). Qed.
  Lemma v_apart : (forall r, In r (s_regions st) -> p0 + N <= rg_base r \/ rg_base r + rg_len r <= p0) /\
                  (forall e, In e X -> exists ea en, e = (Z_to_bv 64 ea, Z_to_bv 64 en) /\ HEAPLO <= ea /\ 0 < en <= 2 ^ 35 /\ ea + en <= CEIL /\ ea mod 4096 = 0 /\
                                       (p0 + N <= ea \/ ea + en <= p0)).
  Proof. exact (c4_apart st L X vm HWF HLG XOK Hcnt Hac p0 Hp0 HRF). Qed.

  Lemma v_HRgrp : forall b2 l2 x, In (RG b2 l2 (RGroup x)) v_regions <-> In (RG b2 l2 (RGroup x)) (s_regions st).
  Proof. intros. unfold v_regions. cbn. split; [intros [E|H]; [discriminate E | exact H] | intros H; right; exact H]. Qed.
  Lemma v_HRsup : forall r, In r (s_regions st) -> In r v_regions. Proof. intros r H; right; exact H. Qed.
  Lemma v_Hac' : 0 <= v_ac.
  Proof. unfold v_ac. pose proof v_sh_rng. assert (1 <= 2 ^ sh) by (change 1 with (2 ^ 0); apply Z.pow_le_mono_r; lia). lia. Qed.
  Lemma v_Hcur' : v_ac > 0 -> exists b2 l2 e2, In (RG b2 l2 (RMeta e2)) v_regions /\ 0 <= e2 /\ p0 + 4096 = b2 + 4096 * (1 + e2) /\ p0 + 4096 + 4096 * v_ac = b2 + l2.
  Proof. intros _. exists p0, N, 0. pose proof v_N_rng as (N1 & N2 & N3). split; [left; reflexivity|]. unfold v_ac. lia. Qed.
  Lemma v_Hsh' : 0 <= sh + 1 /\ sh + 1 <= Z.of_nat (length (s_areas st)) + 1 /\ (v_ac = 0 -> sh + 1 <= Z.of_nat (length (s_areas st))).
  Proof.
    pose proof (wc_shift st (WF_ctx st L HWF)). pose proof v_sh_rng. unfold v_ac.
    assert (1 <= 2 ^ sh) by (change 1 with (2 ^ 0); apply Z.pow_le_mono_r; lia). lia.
  Qed.
  Lemma v_Hshacc' : 2 ^ (sh + 1 + 1) <= Z.of_nat (length (s_areas st)) + v_ac + (sh + 1) + 2.
  Proof.
    pose proof (wc_shacc st (WF_ctx st L HWF)) as SA. rewrite Hac in SA. pose proof v_sh_rng. unfold v_ac.
    assert (E1 : 2 ^ (sh + 1) = 2 * 2 ^ sh) by (rewrite (Z.pow_add_r 2 sh 1), Z.pow_1_r by lia; lia).
    assert (E2 : 2 ^ (sh + 1 + 1) = 2 * 2 ^ (sh + 1)) by (rewrite (Z.pow_add_r 2 (sh + 1) 1), Z.pow_1_r by lia; lia).
    rewrite E2, E1. rewrite E1 in SA. lia.
  Qed.

  Lemma v_Rn_notin : ~ In v_Rn (s_regions st).
  Proof. intros Hin. pose proof v_N_rng as (N1 & _). destruct (proj1 v_apart _ Hin); cbn in *; lia. Qed.

  Lemma v_t_wf_regions : wf_regions v_st.
  Proof.
    pose proof v_N_rng as (N1 & N2 & N3). destruct Hp0 as (P1 & P2 & P3).
    destruct (WF_regions st L HWF) as [RNG DISJ ND LEN GB G63 MT MC BRK BL].
    constructor; cbn [s_regions s_brk s_ctx v_st fst fcx c_shift s_areas].
    - intros r [<-|Hr]; [cbn; repeat split; try lia; assumption | exact (RNG r Hr)].
    - intros r1 r2 [<-|H1] [<-|H2] Hne.
      + exfalso; exact (Hne eq_refl).
      + destruct (proj1 v_apart r2 H2); cbn; lia.
      + destruct (proj1 v_apart r1 H1); cbn; lia.
      + exact (DISJ r1 r2 H1 H2 Hne).
    - apply NoDup_ListNoDup. constructor; [exact v_Rn_notin | apply NoDup_ListNoDup; exact ND].
    - intros r [<-|Hr]; [cbn; lia | exact (LEN r Hr)].
    - intros b2 l2 x Hin. apply v_HRgrp in Hin. exact (GB b2 l2 x Hin).
    - intros b2 l2 x Hin H63. apply v_HRgrp in Hin. exact (G63 b2 l2 x Hin H63).
    - intros b2 l2 e2 [E|Hin]; [unfold v_Rn in E; injection E; intros <- <- <-; lia | exact (MT b2 l2 e2 Hin)].
    - unfold v_regions. rewrite (count_kind_cons (fun k => match k with RMeta _ => true | _ => false end) v_Rn). cbn [rg_kind v_Rn]. lia.
    - assert (CB : length (List.filter (fun x => match rg_kind x with RBrk => true | _ => false end) v_regions)
                   = length (List.filter (fun x => match rg_kind x with RBrk => true | _ => false end) (s_regions st))).
      { unfold v_regions. rewrite (count_kind_cons (fun k => match k with RBrk => true | _ => false end) v_Rn). reflexivity. }
      unfold d_brk. destruct dead.
      + rewrite CB. destruct (s_brk st) as [|x0 x1 g|g]; cbn [guard_kind].
        * split; [|exact I]. rewrite filter_all_false; [cbn; lia|]. intros r Hr. destruct r as [rb rl [|ex|y]]; [exfalso; exact (BRK rb rl Hr) | reflexivity | reflexivity].
        * destruct BRK as (BR1 & BR2 & BR3). split; [lia | right; exact BR3].
        * destruct BRK as [BR1 BR2]. split; [lia|]. destruct g as [[g0 gg]|]; [right; exact BR2 | exact I].
      + destruct (s_brk st) as [|x0 x1 g|g].
        * intros bb ll [E|Hin]; [unfold v_Rn in E; discriminate E | exact (BRK bb ll Hin)].
        * destruct BRK as (BR1 & BR2 & BR3). rewrite CB. split; [|split; [exact BR2 | right; exact BR3]].
          intros bb ll [E|Hin]; [unfold v_Rn in E; discriminate E | exact (BR1 bb ll Hin)].
        * destruct BRK as [BR1 BR2]. rewrite CB. split; [exact BR1|]. destruct g as [[g0 gg]|]; [right; exact BR2 | exact I].
    - intros bb ll [E|Hin]; [unfold v_Rn in E; discriminate E | exact (BL bb ll Hin)].
  Qed.

  Lemma v_t_wf_img : wf_img v_st.
  Proof.
    pose proof (WF_img st L HWF) as [WA WR]. pose proof v_N_rng as (N1 & _).
    constructor; cbn [s_areas s_regions v_st fst]; [exact WA|].
    intros r [<-|Hr]; [| exact (WR r Hr)]. unfold img_free, v_Rn. cbn. destruct Hp0img as [A|A]; [left | right]; lia.
  Qed.

  Lemma v_WF : WF v_st L.
  Proof.
    exact (f_WF st L HWF v_regions (d_brk st dead) (p0 + 4096) v_ac (sh + 1) (d_cb st dead)
             v_HRgrp v_HRsup (d_guard_of st dead) v_Hac' v_Hcur' v_Hsh' v_Hshacc' (d_Hbrk' st L HWF dead) v_t_wf_regions v_t_wf_img).
  Qed.

  Lemma v_RSUM : RSUM v_regions = RSUM (s_regions st) + N.
  Proof. unfold v_regions. rewrite RSUM_cons. cbn. lia. Qed.
  Lemma v_len : length v_regions = S (length (s_regions st)).
  Proof. reflexivity. Qed.

  Lemma v_ledger : forall vm', vm_maps vm' = vm_maps v_vm -> vm_noaccess vm' = vm_noaccess v_vm -> vm_reserved vm' = vm_reserved vm ->
    alloc_top vm' = alloc_top vm -> (dead = false -> vm_brk vm' = vm_brk vm /\ vm_start_brk vm' = vm_start_brk vm) ->
    LEDGERX v_st X vm'.
  Proof.
    intros vm' E1 E2 E3 E4 E5. pose proof v_N_rng as (N1 & N2 & N3). destruct Hp0 as (P1 & P2 & P3). ceil; unfold HEAPLO in P2, P3.
    destruct HLG as [LM LN LB LR LT]. constructor; cbn [s_regions s_brk v_st fst]; rewrite ?E1, ?E2, ?E3, ?E4; cbn [vm_maps vm_noaccess v_vm].
    - unfold v_regions. cbn [map]. replace (region_entry v_Rn) with (Z_to_bv 64 p0, Z_to_bv 64 N) by reflexivity.
      eapply Permutation_trans; [apply perm_skip; exact LM|]. apply Permutation_middle.
    - unfold noacc_of. cbn [s_brk s_regions v_st fst]. rewrite (d_guard_noacc st dead).
      change (flat_map noacc_of_region v_regions) with (noacc_of_region v_Rn ++ flat_map noacc_of_region (s_regions st)).
      replace (noacc_of_region v_Rn) with [(Z_to_bv 64 p0, Z_to_bv 64 N)] by reflexivity.
      eapply Permutation_trans; [apply perm_skip; exact LN|]. unfold noacc_of. apply Permutation_middle.
    - unfold d_brk. destruct dead; [exact I|]. destruct (E5 eq_refl) as [E6 E7]. rewrite E6, E7. exact LB.
    - exact LR.
    - exact LT.
  Qed.

  Lemma v_new_apart_X : forall r, In r v_regions -> (exists r0, In r0 (s_regions st) /\ rg_base r0 = rg_base r /\ rg_len r0 = rg_len r) \/
    forall e, In e X -> exists ea en, e = (Z_to_bv 64 ea, Z_to_bv 64 en) /\ HEAPLO <= ea /\ 0 < en /\ ea + en <= CEIL /\ (rg_base r + rg_len r <= ea \/ ea + en <= rg_base r).
  Proof.
    intros r [<-|Hr]; [right | left; exists r; split; [exact Hr | split; reflexivity]]. intros e He. destruct (proj2 v_apart e He) as (ea & en & -> & X1 & X2 & X3 & X4 & D).
    exists ea, en. split; [reflexivity|]. cbn. repeat split; lia.
  Qed.
End V.
