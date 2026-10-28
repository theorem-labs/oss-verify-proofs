(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import PropExec CatSim StoreOk.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require Import NodesCfg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Lemma rsteps_msteps : forall n ms ms',
  rsteps segs n ms = MachineOk ms' -> msteps segs ms ms'.
Proof.
  induction n as [|n IH]; intros ms ms' H; cbn [rsteps] in H.
  - injection H as <-. apply mst_refl.
  - destruct (ms_svc_pending ms) as [x|] eqn:Hsvc.
    + injection H as <-. apply mst_refl.
    + destruct (RiscvSemantics.step segs ms) as [ms1| |] eqn:Hs; [|discriminate|discriminate].
      eapply mst_step; [exact Hsvc | exact Hs | exact (IH _ _ H)].
Qed.

(* [comment removed for export] *)
Lemma interp_eff_accesses_grows : forall t m c m1 rs,
  interp_eff_accesses segs t m = MachineOk (@mkAccessReport _ (c, m1) rs) -> mem_grows m m1.
Proof.
  induction t as [c0 | c0 | c0 | c0 | c0 | c0 | n a k IH | n a v k IH]; intros m c m1 rs H; cbn [interp_eff_accesses] in H;
    try discriminate.
  - injection H as <- <- <-. apply mem_grows_refl.
  - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|]; [|discriminate].
    destruct (interp_eff_accesses segs (k (bv_extract 0 n (le_bytes_to_word bs))) m) as [[[c' m'] rs']| |] eqn:Ek;
      [|discriminate|discriminate].
    cbn in H. injection H as <- <- <-. exact (IH _ _ _ _ _ Ek).
  - destruct (store_ok segs m a (width_bytes n)); [|discriminate].
    destruct (interp_eff_accesses segs k (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v))))
      as [[[c' m'] rs']| |] eqn:Ek; [|discriminate|discriminate].
    cbn in H. injection H as <- <- <-.
    eapply mem_grows_trans; [apply write_to_mem_grows | exact (IH _ _ _ _ Ek)].
Qed.

Lemma decode_exec_accesses_grows : forall ms w rep,
  decode_exec_accesses segs ms w = MachineOk rep -> mem_grows (ms_mem ms) (ms_mem (access_value _ rep)).
Proof.
  intros ms w rep H. unfold decode_exec_accesses in H.
  destruct (is_ecall w).
  - injection H as <-. cbn. apply mem_grows_refl.
  - destruct (decode_any w) as [[i isz]|]; [|destruct (is_defined_illegal w); discriminate].
    destruct (interp_eff_accesses segs _ (ms_mem ms)) as [[[c m1] rs]| |] eqn:Ei; [|discriminate|discriminate].
    cbn in H. injection H as <-. cbn. exact (interp_eff_accesses_grows _ _ _ _ _ Ei).
Qed.

Lemma step_mem_grows : forall ms ms',
  RiscvSemantics.step segs ms = MachineOk ms' -> mem_grows (ms_mem ms) (ms_mem ms').
Proof.
  intros ms ms' H. rewrite <- drop_step_accesses in H.
  destruct (step_accesses segs ms) as [rep| |] eqn:E; cbn in H; [|discriminate|discriminate]. injection H as <-.
  unfold step_accesses in E.
  destruct (fetch_word segs (ms_pc ms)) as [w|]; [exact (decode_exec_accesses_grows _ _ _ E)|].
  destruct (fetch_word_ov segs (ms_mem ms) (ms_pc ms)) as [w|]; [exact (decode_exec_accesses_grows _ _ _ E)|].
  destruct (fetch_tail_any segs (ms_mem ms) (ms_pc ms)) as [w|]; [exact (decode_exec_accesses_grows _ _ _ E)|].
  unfold fetch_failure in E.
  destruct (negb (bv_unsigned (ms_pc ms) `mod` 2 =? 0)%Z); [discriminate|].
  match type of E with (match (if ?c then _ else _) with _ => _ end = _) => destruct c; discriminate end.
Qed.

Lemma msteps_mem_grows : forall ms ms', msteps segs ms ms' -> mem_grows (ms_mem ms) (ms_mem ms').
Proof.
  intros ms ms' H. induction H as [ms | ms ms1 ms2 Hsvc Hs Hm IH]; [apply mem_grows_refl|].
  eapply mem_grows_trans; [exact (step_mem_grows _ _ Hs) | exact IH].
Qed.

End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Common.FX Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound FxImage FxRn FxHandoff FxHoBuild FxHandoff2 FxRun FxLazy.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Common.Br Require Import BrDress.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Common Require Import HoBridge.
From Stdlib Require Import Uint63.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
Ltac divmod4096 x := pose proof (Z.div_mod x 4096 ltac:(discriminate)); pose proof (Z.mod_pos_bound x 4096 ltac:(reflexivity)).

(* [comment removed for export] *)
Definition run_summary (IM : fimage) (code : itrie finstr) (bp : int) (k : nat) (F0 : fstate) (saved : list Z)
  : stop * Z * option fval * Z * fval * list fval :=
  let x := fx_run IM code bp k F0 in
  let F' := fst (fst x) in
  (snd (fst x), to_Z (snd x), f_resv F', to_Z (f_pc F'), FxState.rget F' 2%uint63, map (fun r => FxState.rget F' (ioz r)) saved).

(* [comment removed for export] *)
Definition wr_pages_chk (IM : fimage) (d : sdesc) (wl : list Z) : bool :=
  forallb (fun r =>
    if (rd_tag r =? 0)%uint63 then
      match rd_dflt r with None => true | Some _ => false end
      && forallb (fun pd => negb (pd_wr pd) || existsb (Z.eqb (to_Z (pd_pn pd))) wl) (rd_pages r)
      && (let T := rg_pages (region_of r) in
          forallb (fun sg => negb (sg_wr sg)
                             || pages_from (Z.to_nat (to_Z (sg_size sg >> 12))) (sg_base sg >> 12)
                                  (fun pn => match iget pn T with Some _ => true | None => false end)) IM)
    else true) (sd_mem d).

Lemma ireg_ioz : forall r, 0 <= r < 32 -> ireg (Z_to_bv 5 r) = ioz r.
Proof.
  intros r Hr. unfold ireg, ioz. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32.
  apply Z.mod_small. exact Hr.
Qed.

Lemma rget_core_regs : forall ms (r : reg), Sem.rget (core_of ms) r = getr (ms_regs ms) r.
Proof.
  intros ms r. unfold Sem.rget, getr, is_x0, bv_eqb, core_of. cbn [c_regs].
  change (bv_unsigned (0%bv : bv 5)) with 0. destruct (bv_unsigned r =? 0); reflexivity.
Qed.

Section Block.
Variable segs : list Segment.
Variable IM : fimage.
Hypothesis HIM : image_ok segs IM.
Hypothesis HWR : image_wr_ok IM.
Variable code : itrie finstr.
Hypothesis Hcode : code_ok segs code.

(* [comment removed for export] *)
Lemma wr_pages_sound : forall rho d wl x,
  rho 0%uint63 = Z_to_bv 64 0 ->
  wr_pages_chk IM d wl = true ->
  claimed_wr IM rho (f_mem (state_of d)) x ->
  exists r, In r (sd_mem d) /\
    ( (rd_tag r = 0%uint63 /\ In (bv_unsigned x / 4096) wl)
      \/ (rd_tag r <> 0%uint63 /\ exists z, 0 <= z < to_Z (rd_len r) /\ (rd_pages r = [] -> to_Z (rd_lo r) <= z)
                                        /\ x = adr rho (rd_tag r) z) ).
Proof.
  intros rho d wl x Hrho0 Hchk (t & rg & pn & p & j & Hg & Hpn & Hpa & Hwr & Hj & Hjl & ->).
  unfold state_of in Hg. cbn [f_mem] in Hg.
  destruct (iget_iof_list_map_In rd_tag region_of _ _ _ Hg) as (r & Hr & Ht & ->).
  exists r. split; [exact Hr|].
  unfold wr_pages_chk in Hchk. rewrite forallb_forall in Hchk. specialize (Hchk r Hr).
  pose proof (Uint63.to_Z_bounded pn) as Hpn0.
  destruct (rd_tag r =? 0)%uint63 eqn:Et.
  - left. apply Uint63.eqb_spec in Et. split; [congruence|]. subst t. rewrite Et.
    apply andb_prop in Hchk as [Hchk Hsegs]. apply andb_prop in Hchk as [Hdf Hpages].
    unfold adr. rewrite Hrho0, bv_add_Z, u64z by (change wB with (2 ^ 63) in Hpn0; clear - Hpn Hpn0 Hj; lia).
    replace ((0 + (to_Z pn * 4096 + j)) / 4096) with (to_Z pn)
      by (clear - Hpn0 Hj; divmod4096 (0 + (to_Z pn * 4096 + j)); nia).
    unfold page_at in Hpa.
    lazymatch type of Hpa with context [iget pn ?TBL] => destruct (iget pn TBL) as [p'|] eqn:Eg end.
    + injection Hpa as <-.
      destruct (iget_iof_list_map_In pd_pn page_of _ _ _ Eg) as (pd & Hpd & Hpdn & ->).
      rewrite forallb_forall in Hpages. specialize (Hpages pd Hpd). cbn [page_of pg_wr] in Hwr. rewrite Hwr in Hpages.
      cbn [negb orb] in Hpages. apply existsb_exists in Hpages as (q & Hq & Eq). apply Z.eqb_eq in Eq. subst pn. rewrite Eq. exact Hq.
    + rewrite Et in Hpa. change (0 =? 0)%uint63 with true in Hpa. cbn iota in Hpa.
      destruct (find_seg IM (pn << 12)) as [sg|] eqn:Ef.
      * injection Hpa as <-. cbn [pg_wr] in Hwr.
        apply find_seg_spec in Ef as (Hin & H1 & H2). apply Uint63.leb_spec in H1. apply Uint63.ltb_spec in H2.
        rewrite forallb_forall in Hsegs. specialize (Hsegs sg Hin). rewrite Hwr in Hsegs. cbn [negb orb] in Hsegs.
        destruct (proj1 (Forall_forall _ _) HIM sg Hin) as (seg & _ & _ & _ & _ & _ & _ & Hal & Hsz & Hhi & _).
        pose proof (Uint63.to_Z_bounded (sg_base sg)) as Hb0. pose proof (Uint63.to_Z_bounded (sg_size sg)) as Hs0.
        change wB with (2 ^ 63) in Hb0, Hs0, Hpn0.
        assert (Hshl : to_Z (pn << 12)%uint63 = to_Z pn * 4096) by exact (ho_toZ_lsl12 pn Hpn).
        rewrite Hshl in H1, H2.
        assert (Hadd : to_Z (sg_base sg + sg_size sg)%uint63 = to_Z (sg_base sg) + to_Z (sg_size sg)).
        { rewrite Uint63.add_spec. apply Z.mod_small. change wB with (2 ^ 63). clear - Hhi Hb0 Hs0. lia. }
        rewrite Hadd in H2.
        assert (Hb12 : to_Z (sg_base sg >> 12)%uint63 = to_Z (sg_base sg) / 4096).
        { rewrite Uint63.lsr_spec. change (2 ^ to_Z 12%uint63) with 4096. reflexivity. }
        assert (Hs12 : to_Z (sg_size sg >> 12)%uint63 = to_Z (sg_size sg) / 4096).
        { rewrite Uint63.lsr_spec. change (2 ^ to_Z 12%uint63) with 4096. reflexivity. }
        set (fT := fun pn0 : int => match iget pn0 (rg_pages (region_of r)) with Some _ => true | None => false end) in Hsegs.
        assert (HfT : fT pn = true).
        { apply (pages_from_spec (Z.to_nat (to_Z (sg_size sg >> 12))) (sg_base sg >> 12) fT pn).
          - rewrite Hb12, Hs12. clear - Hhi Hb0 Hs0. divmod4096 (to_Z (sg_base sg)). divmod4096 (to_Z (sg_size sg)).
            rewrite Z2Nat.id by lia. lia.
          - exact Hsegs.
          - rewrite Hb12, Hs12. clear - H1 H2 Hb0 Hs0 Hal Hsz Hpn0. divmod4096 (to_Z (sg_base sg)). divmod4096 (to_Z (sg_size sg)).
            rewrite Z2Nat.id by lia. lia. }
        subst fT. cbv beta in HfT. rewrite Eg in HfT. discriminate HfT.
      * cbn [region_of rg_dflt] in Hpa. revert Hpa Hdf. destruct (rd_dflt r); intros Hpa Hdf; [discriminate Hdf | discriminate Hpa].
  - right. split; [intros E; rewrite E in Et; cbn in Et; discriminate Et|].
    cbn [region_of rg_len] in Hjl. exists (to_Z pn * 4096 + j). split; [clear - Hpn0 Hj Hjl; lia|]. split; [|subst t; reflexivity].
    intros Hnil. unfold page_at in Hpa. cbn [region_of rg_pages rg_dflt rg_lo rg_len] in Hpa. rewrite Hnil in Hpa.
    cbn [map iof_list fold_left iget] in Hpa. rewrite <- Ht, Et in Hpa. cbn iota in Hpa.
    revert Hpa. destruct (rd_dflt r) as [kd|]; intros Hpa; [|discriminate Hpa].
    destruct (page_in_region _ pn) eqn:Epr; [|discriminate Hpa].
    unfold page_in_region in Epr. cbn [rg_lo rg_len] in Epr. rewrite !andb_true_iff in Epr. destruct Epr as [[[_ Hlo] _] _].
    apply Uint63.leb_spec in Hlo. rewrite (ho_toZ_lsl12 pn Hpn) in Hlo. cbn [region_of rg_lo] in Hlo. clear - Hlo Hj. lia.
Qed.

(* [comment removed for export] *)
Theorem fx_block_sound :
  forall facts d bs bp k rho ms saved steps pcz vsp vsaved,
  (k <= 61)%nat ->
  ho_check2 IM facts d = true ->
  run_summary IM code bp k (dress (state_of d) bs) saved = (SBreak, steps, None, pcz, vsp, vsaved) ->
  rho 0%uint63 = Z_to_bv 64 0 ->
  Forall (hholds segs rho ms) facts ->
  Forall (ditem_ok rho) bs ->
  ms_pc_val ms = Z_to_bv 64 (to_Z (sd_pc d)) -> ms_svc_pending ms = None -> ms_resv ms = None ->
  exists ms',
    msteps segs ms ms'
    /\ ms_pc_val ms' = Z_to_bv 64 pcz /\ ms_svc_pending ms' = None /\ ms_resv ms' = None
    /\ ms_fregs ms' = ms_fregs ms /\ ms_fcsr ms' = ms_fcsr ms /\ ms_rom ms' = ms_rom ms
    /\ Sem.rget (core_of ms') 2%bv = dv rho vsp
    /\ (forall i r v, nth_error saved i = Some r -> nth_error vsaved i = Some v -> 0 < r < 32 ->
          Sem.rget (core_of ms') (Z_to_bv 5 r) = dv rho v)
    /\ (forall x, ~ claimed_wr IM rho (f_mem (state_of d)) x -> ms_mem ms' x = ms_mem ms x)
    /\ mem_grows (ms_mem ms) (ms_mem ms').
Proof.
  intros facts d bs bp k rho ms saved steps pcz vsp vsaved Hk Hchk Hsum Hrho0 Hfacts Hbs Hpc Hsvc Hresv.
  unfold run_summary in Hsum.
  destruct (fx_run IM code bp k (dress (state_of d) bs)) as [[F' r] cnt] eqn:Erun.
  cbn [fst snd] in Hsum. injection Hsum as Er Ecnt Eresv Epc Esp Esaved.
  assert (HR0 : R segs IM rho (dress (state_of d) bs) ms).
  { apply R_dress; [|exact Hbs]. exact (handoff_R2 segs IM HIM HWR facts d rho ms Hchk Hrho0 Hfacts Hpc Hsvc Hresv). }
  destruct (fx_run_sound_frame segs IM rho Hrho0 code Hcode bp k _ F' r cnt Hk Erun) as (_ & _ & Hsound).
  destruct (Hsound ms HR0) as (ms' & Hsteps & HR' & _ & Hfr & Hrom).
  destruct (fx_run_sound_shape segs IM rho Hrho0 code Hcode bp k _ F' r cnt Hk Erun ms HR0) as (ms'' & Hsteps2 & _ & Hfregs & Hfcsr).
  assert (E'' : ms'' = ms') by (rewrite Hsteps in Hsteps2; injection Hsteps2 as ->; reflexivity). subst ms''.
  exists ms'. split; [exact (rsteps_msteps segs _ _ _ Hsteps)|].
  split; [rewrite (R_pc _ _ _ _ _ HR'), Epc; reflexivity|].
  split; [exact (R_svc _ _ _ _ _ HR')|].
  split; [rewrite (R_resv _ _ _ _ _ HR'), Eresv; reflexivity|].
  split; [exact Hfregs|]. split; [exact Hfcsr|]. split; [exact Hrom|].
  split; [rewrite (R_regs _ _ _ _ _ HR' (2%bv : bv 5)); change (ireg (2%bv : bv 5)) with 2%uint63; rewrite Esp; reflexivity|].
  split.
  { intros i r0 v Hi Hv Hr0. rewrite (R_regs _ _ _ _ _ HR' (Z_to_bv 5 r0)). rewrite (ireg_ioz r0) by lia.
    f_equal. rewrite <- Esaved in Hv. rewrite nth_error_map, Hi in Hv. cbn [option_map] in Hv. congruence. }
  split.
  { intros x Hx. apply Hfr. intros Hc. apply Hx. revert Hc. apply claimed_wr_same. apply dress_same. }
  exact (msteps_mem_grows segs _ _ (rsteps_msteps segs _ _ _ Hsteps)).
Qed.
End Block.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
