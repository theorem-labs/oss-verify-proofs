(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OssFuzzTheorems.openssl.hashtable.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ModelAmb PropExec H0Lim HUTargetPre HUWorldK HUReadBase HUTargetFull HUHandoff HUInitPcs HUFiPre HUFiFx.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.Cfg Require Import ShapeAlgBase ShapeCfg NodesCfg LedgerCfg AllocCfg.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.FX Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxRn FxImage FxHandoff FxMisc FxDrive FxHb.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AxSymExec3Sound AsanPlanCore CxPlan CxPlanSound HUPlanImage HUAtable H0Sinv.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.Br Require Import BrEnv BrMem BrPure BrLedger BrKeep BrMain BrSinv BrInfer BrGlue.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require ConeCfg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Fixpoint tree_leaves (t : dtree) : list (fstate * fledger * int * stop) :=
  match t with DLeaf F L n r => [(F, L, n, r)] | DFork a b => tree_leaves a ++ tree_leaves b end.

Lemma tree_leaves_in : forall t x, leaf_in x t -> In x (tree_leaves t).
Proof.
  induction t as [F0 L0 n0 r0 | a IHa b IHb]; intros x Hx; cbn [leaf_in tree_leaves] in *.
  - left. symmetry. exact Hx.
  - apply in_or_app. destruct Hx as [Hx|Hx]; [left; exact (IHa x Hx) | right; exact (IHb x Hx)].
Qed.

(* [comment removed for export] *)
Definition bufoff (k : Z) : Z := if k =? 0 then 32 else offk k.
Definition TEQ (k : Z) : list teq :=
  [ (118%uint63, 0, [(1, 111%uint63)]); (120%uint63, 0, [(1, 113%uint63)]);
    (112%uint63, bufoff k + 6, [(1, 3%uint63); (1, 111%uint63)]);
    (119%uint63, bufoff k + 6, [(1, 3%uint63); (1, 111%uint63)]) ].

(* [comment removed for export] *)
Lemma br_infer_fields IM F L CS xt teqs TB ah resid pins bd :
  br_infer IM F L CS xt teqs TB ah resid pins = Some bd ->
  bd_xt bd = xt /\ bd_teq bd = teqs /\ bd_tb bd = TB /\ bd_ah bd = ah /\ bd_resid bd = resid.
Proof.
  unfold br_infer. destruct (infer_stack F CS pins) as [[[ts tc] s0]|]; [|discriminate].
  cbv zeta.
  match goal with |- Some (BD (fst ?x) _ _ _ _ _ _ _ _) = _ -> _ => generalize x end.
  intros s3 H. injection H as <-. repeat split; reflexivity.
Qed.

Lemma br_infer_auto_fields IM A keep KF F L CS xt teqs TB ah pins bd :
  br_infer_auto IM A keep KF F L CS xt teqs TB ah pins = Some bd ->
  bd_xt bd = xt /\ bd_teq bd = teqs /\ bd_tb bd = TB /\ bd_ah bd = ah.
Proof.
  unfold br_infer_auto. destruct (br_infer IM F L CS xt teqs TB ah [] pins) as [bd0|] eqn:H0; [|discriminate].
  destruct (br_infer_fields _ _ _ _ _ _ _ _ _ _ _ H0) as (E0 & E1 & E2 & E3 & _).
  generalize (fail_pos IM A keep KF F L bd0 0 (AX2.s_know (CAP.a_ss CS))). intros fp H.
  injection H as <-. cbn [bd_xt bd_teq bd_tb bd_ah]. repeat split; assumption.
Qed.

Lemma resid_kn_nil BD kn : bd_resid BD = [] -> forall i, resid_kn BD i kn = [].
Proof. intros Hr. induction kn as [|k r IH]; intros i; cbn [resid_kn]; [reflexivity|]. rewrite Hr. cbn. apply IH. Qed.

(* [comment removed for export] *)
Lemma rdn_nth segs mem : forall n a bs, rdn segs mem a n = Some bs ->
  forall j, (j < n)%nat ->
    match mem (aoff a j) with Some b => Some b | None => PropExec.seg_rom segs (aoff a j) end = nth_error bs j.
Proof.
  induction n as [|n IH]; intros a bs H j Hj; [lia|]. cbn [rdn] in H.
  destruct (match mem a with Some b => Some b | None => PropExec.seg_rom segs a end) as [b|] eqn:Hb; [|discriminate].
  destruct (rdn segs mem (a + 1)%bv n) as [rest|] eqn:Hr; [|discriminate]. injection H as <-.
  destruct j as [|j].
  - rewrite aoff_0. exact Hb.
  - rewrite <- aoff_S. cbn [nth_error]. apply (IH _ _ Hr). lia.
Qed.

Lemma seg_rom_noseg segs x : find_segment segs (bv_unsigned x) 1 = None -> PropExec.seg_rom segs x = None.
Proof. intros H. unfold PropExec.seg_rom, memory_read. change (Z.of_N 1) with 1. rewrite H. reflexivity. Qed.

Lemma nth_error_skipn {T : Type} (l : list T) : forall n j, nth_error (skipn n l) j = nth_error l (n + j).
Proof. induction l as [|x l IH]; intros [|n] j; cbn; try reflexivity; [destruct j; reflexivity | apply IH]. Qed.

(* [comment removed for export] *)
Definition addr_expr (a : AX2.saddr) : AX2.expr := AX2.EAlu ALU_ADD (AX2.a_base a) (AX2.ELit (AX2.a_off a)).

(* [comment removed for export] *)
Definition resid_entry_ok (XRNG : nat -> Z -> Z -> bool) (k : Z) (bd : bdata) (F : fstate) (K : AX2.kentry) : bool :=
  match K with
  | AX2.KRange (AX2.EVar x) lo hi =>     (* [comment removed for export] *)
      ((lo <=? 0) && (18446744073709551615 <=? hi))     (* [comment removed for export] *)
      || (is_ext_var (bd_vt bd) x && negb (Nat.eqb x 2) && XRNG x lo hi)
  | AX2.KBlob a n 3%nat =>
      (0 <=? AX2.a_off a) && (AX2.a_off a <? 4096)
      && val_match (bd_vt bd) (bd_tl bd) (bd_xt bd) (bd_teq bd) (addr_expr a) (FV 112 w_zero)
      && val_match (bd_vt bd) (bd_tl bd) (bd_xt bd) (bd_teq bd) n (FV 113 w_zero)
  | AX2.KWord a 1%nat (AX2.EVar 9%nat) =>
      is_ext_var (bd_vt bd) 9
      && match aview (bd_vt bd) (f_mem F) (bd_tl bd) (bd_xt bd) a with
         | Some (t, o) => (t =? 3)%uint63 && (o =? bufoff k + 2)
         | None => false
         end
  | _ => false
  end.

Definition resid_chk (XRNG : nat -> Z -> Z -> bool) (k : Z) (CS : CAP.acs) (bd : bdata) (F : fstate) (L : fledger) : bool :=
  ledger_vis_b L 3%uint63 0 (hnb k)
  && forallb (resid_entry_ok XRNG k bd F) (resid_kn bd 0 (AX2.s_know (CAP.a_ss CS))).

Section H0Br.
  Variables (sp0 : word) (k buf : Z) (can : word) (content : list byte) (VM : VmMaps) (R : bvmap 5 word) (M : word -> option byte).
  Variables (stdin0 : AmbIn) (fs0 : Fs.Fs) (tid : word).
  Hypothesis TF : tgt_entry_full sp0 k buf can content VM R M.
  Variable fuel : nat.
  (* [comment removed for export] *)
  Variable envc : Z.
  Hypothesis Henvc : 0 <= envc /\ bv_unsigned sp0 + 192 + 8 * envc < 2 ^ 47 - 32.
  Local Notation STR0 := (bv_unsigned sp0 + 192 + 8 * envc).
  Hypothesis Hzero : M (Z_to_bv 64 STR0) = Some (Z_to_bv 8 0).
  (* [comment removed for export] *)
  Variable TB : list (int * Z * Z).
  Hypothesis HTBlt : tb_tags_lt 200 TB = true.
  Hypothesis HTB : forall mb bw B sec tdz err, fi_root_facts sp0 k buf can VM R M mb bw B sec tdz err ->
    tb_ok (fi_rho sp0 can R mb B sec tdz err) TB.

  (* [comment removed for export] *)
  Variable CSL : list CAP.acs.
  Variable PHI : CAP.acs -> AX2.env -> Prop.
  Definition SINVx (CS : CAP.acs) : AX2.env -> (word -> option byte) -> Prop :=
    fun E M' => SINVt (bv_unsigned sp0) STR0 E M' /\ PHI CS E.
  Variable T : TSet.
  (* [comment removed for export] *)
  Variable EOK : CAP.acs -> AX2.env -> Prop.
  Hypothesis FAMILY : forall CS, In CS CSL -> forall E R' FULL model,
    CXS.cs_ok HSEGS H0T LIM (SINVx CS) (argHt STR0) (bv_unsigned sp0) fs0 E CS R' FULL model ->
    EOK CS E ->
    realizes_cfg ConeCfg.CFG RSEGS (mkCfg (mkst R' (Z_to_bv 64 (CAP.pc CS)) FULL (PropExec.seg_rom RSEGS)) model) T.

  Local Notation fim := (HUReadBase.model_post VM stdin0 fs0 tid).
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variable XVX : CAP.acs -> nat -> word.
  Definition XV (CS : CAP.acs) : nat -> word := fun x => if Nat.eqb x 2 then Z_to_bv 64 envc else XVX CS x.
  Variable XB : nat -> list byte.
  Hypothesis XB12 : XB 1%nat = [] /\ XB 2%nat = [].
  (* [comment removed for export] *)
  Hypothesis HX3 : XB 3%nat = skipn (Z.to_nat (6 + hdr_cfglen content)) content.
  Hypothesis HX9 : forall CS, XVX CS 9%nat = Z_to_bv 64 (bv_unsigned (nth 2 content (Z_to_bv 8 0))).
  (* [comment removed for export] *)
  Variable XRNG : nat -> Z -> Z -> bool.
  Hypothesis HXR : forall CS x lo hi, XRNG x lo hi = true -> lo <= bv_unsigned (XVX CS x) <= hi.

  (* [comment removed for export] *)
  Variable XCHK : CAP.acs -> bdata -> fstate -> fledger -> bool.
  Definition leaf_chk (x : fstate * fledger * int * stop) : bool :=
    let F := fst (fst (fst x)) in let L := snd (fst (fst x)) in
    existsb (fun CS =>
      match br_infer_auto IMH H0T KEEP (kfacts k) F L CS [] (TEQ k) TB 192 kit_pins with
      | Some bd =>
          bridge_check IMH H0T RB LIM bd KEEP (kfacts k) F L CS
          && sinv_check (bd_vt bd) (f_mem F) (bd_tl bd) (bd_xt bd) 1%uint63 8388608
          && (bd_ts bd =? 1)%uint63 && (bd_tc bd =? 8388608)
          && match CAP.a_fd CS with CAP.FdStd => true | _ => false end
          && CAP.a_tidset CS
          && resid_chk XRNG k CS bd F L
          && XCHK CS bd F L
      | None => false
      end) CSL.

  (* [comment removed for export] *)
  Hypothesis HPHI : forall CS bd F L rho', In CS CSL -> XCHK CS bd F L = true -> rho' 0%uint63 = Z_to_bv 64 0 ->
    PHI CS (env_of rho' (XV CS) XB (bd_vt bd)).
  Hypothesis HEOK : forall mb bw B sec tdz err, fi_root_facts sp0 k buf can VM R M mb bw B sec tdz err ->
    forall CS bd F L (rho' : int -> word), In CS CSL -> XCHK CS bd F L = true ->
      (forall t, to_Z t < 200 -> rho' t = fi_rho sp0 can R mb B sec tdz err t) ->
      bd_teq bd = TEQ k -> EOK CS (env_of rho' (XV CS) XB (bd_vt bd)).
  Lemma kfacts_tags : forallb (fun k0 => forallb (fact_tags_lt 200) (kfacts k0)) KS = true.
  Proof. vm_compute. reflexivity. Qed.

  Lemma teq_root : forall mb bw B sec tdz err, fi_root_facts sp0 k buf can VM R M mb bw B sec tdz err ->
    teq_ok (fi_rho sp0 can R mb B sec tdz err) (TEQ k).
  Proof.
    intros mb bw B sec tdz err HR.
    destruct (handoff_teqs sp0 k buf can content VM R M mb B sec tdz err (Z_to_bv 64 0) (Z_to_bv 64 0) TF)
      as (E111 & E112 & E113 & E118 & E119 & E120 & Hc & Hp & Hlen & Hcap & Hsp & Hsp16 & Hcont).
    pose proof (fr_buf _ _ _ _ _ _ _ _ _ _ _ _ _ HR) as Hbuf.
    assert (E3 : bv_unsigned (fi_rho sp0 can R mb B sec tdz err 3%uint63) = bv_unsigned B).
    { unfold fi_rho. rewrite (rho3 sp0 mb B (bv_unsigned can) sec tdz err R). apply Z_to_bv_small. apply bv_unsigned_in_range. }
    unfold teq_ok, TEQ, bufoff, fi_rho in *.
    repeat constructor; cbn [teq_holds teq_sum]; rewrite ?E111, ?E112, ?E113, ?E118, ?E119, ?E120, ?E3;
      exists 0; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Leaf.
    Variables (mb bw B : word) (sec tdz err : Z).
    Hypothesis HR : fi_root_facts sp0 k buf can VM R M mb bw B sec tdz err.
    Variables (F' : fstate) (L' : fledger) (n' : int) (r : stop) (rho' : int -> word) (ms' : machine_state) (m' : Model).
    Hypothesis Hleaf : leaf_in (F', L', n', r) (the_tree k fuel).
    Hypothesis HD : FiInv sp0 VM R M stdin0 fs0 tid n' rho' F' L' ms' m'.
    Hypothesis Hext : dext 200%uint63 (fi_rho sp0 can R mb B sec tdz err) fim n' rho' m'.
    Local Notation rho0 := (fi_rho sp0 can R mb B sec tdz err).

    Lemma lf_agree : forall t, to_Z t < 200 -> rho' t = rho0 t.
    Proof. destruct Hext as (_ & H & _). intros t Ht. apply H. exact Ht. Qed.

    Lemma lf_rho0 : rho' 0%uint63 = Z_to_bv 64 0.
    Proof. destruct HD as ((_ & H & _) & _). exact H. Qed.

    Lemma lf_sp : 0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000 /\ bv_unsigned sp0 mod 16 = 0.
    Proof.
      destruct (handoff_teqs sp0 k buf can content VM R M mb B sec tdz err (Z_to_bv 64 0) (Z_to_bv 64 0) TF)
        as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsp & Hsp16 & _). split; assumption.
    Qed.

    Lemma lf_isp : bv_unsigned (vm_init_sp (m_vmmaps m')) = bv_unsigned sp0.
    Proof.
      destruct Hext as (_ & _ & _ & Hsp & _). rewrite Hsp.
      change (m_vmmaps fim) with VM. rewrite (fr_isp _ _ _ _ _ _ _ _ _ _ _ _ _ HR). reflexivity.
    Qed.

    Lemma lf_isp2 : bv_unsigned sp0 = bv_unsigned (rho' 1%uint63) + 8388608.
    Proof.
      rewrite (lf_agree 1%uint63) by (cbn; lia). unfold fi_rho.
      rewrite (rho1 sp0 mb B (bv_unsigned can) sec tdz err R). pose proof lf_sp as [Hsp _].
      rewrite Z_to_bv_small; [lia|]. pose proof (bv_unsigned_in_range _ sp0) as Hr. unfold bv_modulus in *. lia.
    Qed.

    Lemma lf_xi : same_but_vm fim m'.
    Proof. destruct HD as ((_ & _ & _ & _ & _ & _ & _ & _ & HXI & _) & _). exact HXI. Qed.

    Lemma lf_zero : ms_mem ms' (Z_to_bv 64 STR0) = Some (Z_to_bv 8 0).
    Proof.
      rewrite (DInvX_high _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 STR0) HD); [exact Hzero|].
      cbv beta. rewrite Z_to_bv_small; [lia|]. pose proof (bv_unsigned_in_range _ sp0). unfold bv_modulus in *. lia.
    Qed.

    Lemma lf_kf : Forall (hholds RSEGS rho' (fi_ms R M)) (kfacts k).
    Proof.
      pose proof (fi_kfacts sp0 k buf can VM R M mb bw B sec tdz err HR) as H0.
      pose proof (tgt_k_range _ _ _ _ _ _ _ _ TF) as Hk.
      pose proof (proj1 (forallb_forall _ _) kfacts_tags k Hk) as Htags.
      apply Forall_forall. intros f Hf.
      apply (hholds_agree RSEGS 200%uint63 rho0 rho' (fi_ms R M) f).
      - split; [exact lf_rho0 | exact lf_agree].
      - exact (proj1 (forallb_forall _ _) Htags f Hf).
      - exact (proj1 (Forall_forall _ _) H0 f Hf).
    Qed.

    Lemma lf_tb : tb_ok rho' TB.
    Proof. exact (tb_ok_ext rho0 rho' 200%uint63 TB (fun t Ht => lf_agree t Ht) HTBlt (HTB _ _ _ _ _ _ HR)). Qed.

    Lemma lf_teq : teq_ok rho' (TEQ k).
    Proof.
      apply (teq_ok_ext rho0 rho' 200%uint63 (TEQ k) (fun t Ht => lf_agree t Ht)); [reflexivity|].
      exact (teq_root _ _ _ _ _ _ HR).
    Qed.

    Lemma lf_regions : forall t rg, iget t (f_mem F') = Some rg -> region_ok rho' t rg.
    Proof.
      intros t rg Hg. destruct HD as ((HRn & _) & _).
      exact (R_region_ok RSEGS IMH rho' F' ms' t rg (Rn_R RSEGS IMH n' rho' F' ms' HRn lf_rho0) Hg).
    Qed.

    (* [comment removed for export] *)
    Section Resid.
      Variables (CS : CAP.acs) (bd : bdata).
      Hypothesis Hbc : bridge_check IMH H0T RB LIM bd KEEP (kfacts k) F' L' CS = true.
      Hypothesis Hts : bd_ts bd = 1%uint63.
      Hypothesis Htc : bd_tc bd = 8388608.
      Hypothesis Eah : bd_ah bd = 192.
      Hypothesis Eteq : bd_teq bd = TEQ k.
      Hypothesis Ext : bd_xt bd = [].
      Hypothesis Hrc : resid_chk XRNG k CS bd F' L' = true.
      Local Notation E := (env_of rho' (XV CS) XB (bd_vt bd)).
      Local Notation MR := (CXS.Mr H0T (argHt STR0) E CS m' (ms_mem ms')).

      Lemma rs_vis : ledger_vis_b L' 3%uint63 0 (hnb k) = true.
      Proof. unfold resid_chk in Hrc. apply andb_prop in Hrc. exact (proj1 Hrc). Qed.

      Lemma rs_isp2 : bv_unsigned sp0 = bv_unsigned (rho' (bd_ts bd)) + bd_tc bd.
      Proof. rewrite Hts, Htc. exact lf_isp2. Qed.

      Lemma rs_argH : forall a, argHt STR0 E a = true -> bv_unsigned sp0 + bd_ah bd <= bv_unsigned a.
      Proof. intros a Ha. unfold argHt in Ha. apply Z.eqb_eq in Ha. rewrite Eah. lia. Qed.

      (* [comment removed for export] *)
      Lemma rs_mem : forall i, 0 <= i < hnb k ->
        MR (adr rho' 3%uint63 i) = M (adr rho' 3%uint63 i)
        /\ bv_unsigned (adr rho' 3%uint63 i) = bv_unsigned (rho' 3%uint63) + i
        /\ PropExec.seg_rom RSEGS (adr rho' 3%uint63 i) = None.
      Proof.
        intros i Hi.
        destruct (br_kept_mem ConeCfg.CFG RSEGS IMH (segments_reserved RSEGS) RB LIM RTgt KEEP M
                    (XI_frame fim) [] (ms_fregs (fi_ms R M)) (ms_fcsr (fi_ms R M)) (FxMisc.seg_rom RSEGS)
                    (fun x => bv_unsigned sp0 <= bv_unsigned x) (proj1 res_bounds) H0T (argHt STR0) (bv_unsigned sp0)
                    h0t_res_cover eq_refl bd (XV CS) XB n' rho' F' L' ms' m' CS (kfacts k) HD eq_refl eq_refl eq_refl Hbc
                    (fi_ms R M) eq_refl lf_isp rs_isp2 rs_argH 3%uint63 0 (hnb k) ltac:(left; reflexivity) rs_vis i Hi)
          as [Hm Hu].
        rewrite Z.add_0_l in Hm, Hu. split; [exact Hm|]. split; [lia|].
        apply seg_rom_noseg.
        pose proof (br_nosegb_sound ConeCfg.CFG RSEGS IMH (segments_reserved RSEGS) RB LIM RTgt KEEP M
                    (XI_frame fim) [] (ms_fregs (fi_ms R M)) (ms_fcsr (fi_ms R M)) (FxMisc.seg_rom RSEGS)
                    (fun x => bv_unsigned sp0 <= bv_unsigned x) (proj1 res_bounds) H0T (argHt STR0) (bv_unsigned sp0)
                    h0t_in_hull h0t_res_cover h0t_hull_ne eq_refl bd (XV CS) XB n' rho' F' L' ms' m' CS (kfacts k) HD eq_refl eq_refl eq_refl Hbc
                    (fi_ms R M) eq_refl lf_isp rs_isp2 rs_argH 3%uint63 0 (hnb k)) as NS.
        rewrite <- (Z.add_0_l i). apply NS; [|exact Hi].
        unfold nosegb. apply orb_true_iff. right. pose proof rs_vis as Hv. unfold ledger_vis_b in Hv.
        apply andb_prop in Hv. rewrite (proj1 Hv). reflexivity.
      Qed.

      (* [comment removed for export] *)
      Lemma rs_content :
        let rho0' := fi_rho sp0 can R mb B sec tdz err in
        bv_unsigned (rho' 3%uint63) = bv_unsigned B
        /\ bufoff k + Z.of_nat (length content) <= hnb k /\ 0 <= bufoff k
        /\ forall j, (j < length content)%nat ->
             MR (adr rho' 3%uint63 (bufoff k + Z.of_nat j)) = nth_error content j.
      Proof.
        cbv zeta.
        destruct (handoff_teqs sp0 k buf can content VM R M mb B sec tdz err (Z_to_bv 64 0) (Z_to_bv 64 0) TF)
          as (_ & _ & _ & _ & _ & _ & Hc & Hp & Hlen & Hcap & _ & _ & Hcont).
        pose proof (fr_buf _ _ _ _ _ _ _ _ _ _ _ _ _ HR) as Hbuf. fold (bufoff k) in Hbuf.
        pose proof (tgt_k_range _ _ _ _ _ _ _ _ TF) as Hk.
        assert (E3 : bv_unsigned (rho' 3%uint63) = bv_unsigned B).
        { rewrite (lf_agree 3%uint63) by (cbn; lia). unfold fi_rho.
          rewrite (rho3 sp0 mb B (bv_unsigned can) sec tdz err R). apply Z_to_bv_small. apply bv_unsigned_in_range. }
        assert (Hoff : 0 <= bufoff k /\ bufoff k + Z.of_nat (length content) <= hnb k).
        { unfold bufoff, hnb, offk, nbk in *. destruct (Z.eqb_spec k 0) as [->|Hk0]; [lia|].
          unfold KS in Hk. cbn [In] in Hk. set (c := capk k) in *. lia. }
        split; [exact E3|]. split; [lia|]. split; [lia|].
        intros j Hj. set (i' := bufoff k + Z.of_nat j).
        destruct (rs_mem i' ltac:(unfold i'; lia)) as (Hm & Hu & Hns).
        rewrite Hm. pose proof (rdn_nth RSEGS M _ _ _ Hcont j Hj) as Hr.
        assert (Ea : aoff (Z_to_bv 64 buf) j = adr rho' 3%uint63 i').
        { apply bv_eq. rewrite Hu, E3. unfold aoff. rewrite bv_add_unsigned.
          pose proof (bv_unsigned_in_range _ B) as HB. unfold bv_modulus in HB.
          assert (Hsm : 0 <= buf + Z.of_nat j < 2 ^ 64).
          { pose proof (i63_range 0). destruct (rs_mem i' ltac:(unfold i'; lia)) as (_ & Hu' & _).
            pose proof (bv_unsigned_in_range _ (adr rho' 3%uint63 i')) as Hr'. unfold bv_modulus in Hr'. rewrite Hu', E3 in Hr'.
            unfold i' in Hr'. lia. }
          rewrite !Z_to_bv_small by (unfold bv_modulus; lia).
          unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia. unfold i'. lia. }
        rewrite Ea, Hns in Hr. destruct (M (adr rho' 3%uint63 i')); exact Hr.
      Qed.

      Lemma rs_tl : tl_ok (bd_vt bd) (f_mem F') (bd_tl bd) = true.
      Proof. exact (bridge_check_tl _ _ _ _ _ _ _ _ _ _ Hbc). Qed.
      Lemma rs_teq : teq_ok rho' (bd_teq bd).
      Proof. rewrite Eteq. exact lf_teq. Qed.
      Lemma rs_xt : xt_ok rho' (XV CS) XB (bd_vt bd) (bd_xt bd).
      Proof. rewrite Ext. constructor. Qed.

      Lemma rs_tagval t z : to_Z t < 200 -> bv_unsigned (fi_rho sp0 can R mb B sec tdz err t) = z ->
        forall e, val_match (bd_vt bd) (bd_tl bd) (bd_xt bd) (bd_teq bd) e (FV t w_zero) = true -> bv_unsigned (AX2.edenot E e) = z.
      Proof.
        intros Ht Hz e Hvm.
        rewrite (val_match_sound rho' (XV CS) XB (bd_vt bd) (f_mem F') (bd_tl bd) (bd_xt bd) (bd_teq bd) lf_regions lf_rho0 rs_tl rs_xt rs_teq e _ Hvm).
        rewrite (fk_dv_plain rho' (FV t w_zero)) by (cbn [vtag]; lia). cbn [vtag vw].
        rewrite (lf_agree t Ht). rewrite bv_add_unsigned. change (bv_unsigned (wbv w_zero)) with 0. rewrite Z.add_0_r.
        rewrite bv_wrap_small by apply bv_unsigned_in_range. exact Hz.
      Qed.

      Lemma rs_entry K : resid_entry_ok XRNG k bd F' K = true -> AX2S.kentry_ok RSEGS E MR K.
      Proof.
        intros HK.
        destruct (handoff_teqs sp0 k buf can content VM R M mb B sec tdz err (Z_to_bv 64 0) (Z_to_bv 64 0) TF)
          as (_ & E112 & E113 & _ & _ & _ & Hc & Hp & Hlen & Hcap & _ & _ & _).
        pose proof (fr_buf _ _ _ _ _ _ _ _ _ _ _ _ _ HR) as Hbuf. fold (bufoff k) in Hbuf.
        destruct rs_content as (E3 & Hfit & Hoff0 & Hbytes).
        pose proof (bv_unsigned_in_range _ B) as HB. unfold bv_modulus in HB.
        assert (Hnb : bv_unsigned B + hnb k < 2 ^ 63).
        { destruct (rs_mem 0 ltac:(lia)) as (_ & _ & _).
          pose proof rs_vis as Hv. unfold ledger_vis_b in Hv. apply andb_prop in Hv as [He _].
          destruct HD as ((_ & _ & _ & _ & Hinv & _ & Hmir & _) & _ & _ & _ & _ & Hex).
          destruct Hex as [Hmaps _].
          assert (Hin : Forall (ent_in (f_mem F')) (fl_maps L')).
          { destruct Hmir as (Hm1 & _ & _). apply Forall_forall. intros e0 He0.
            exact (proj1 (proj1 (ent_ok_iff rho' (f_mem F') _ e0) (proj1 (Forall_forall _ _) Hm1 e0 He0))). }
          destruct (in_entry_sound rho' (f_mem F') L' (m_vmmaps m') _ _ _ _ lf_regions Hinv Hmaps Hin 3%uint63 0 (hnb k) He)
            as (e0 & _ & _ & _ & _ & _ & _ & _ & rg & Hg & _ & Hrhi).
          destruct (lf_regions _ rg Hg) as (_ & _ & Hb63 & _). rewrite E3 in Hb63. lia. }
        destruct K as [a w v | a n0 | a n0 j | | | e rlo rhi | | | |]; try discriminate.
        - (* [comment removed for export] *)
          destruct w as [|[|w]]; try discriminate. destruct v as [|x| | | | | |]; try discriminate.
          do 9 (destruct x as [|x]; try discriminate). destruct x; try discriminate.
          cbn [resid_entry_ok] in HK. apply andb_prop in HK as [Hext9 Hav].
          destruct (aview (bd_vt bd) (f_mem F') (bd_tl bd) (bd_xt bd) a) as [[t o]|] eqn:Hv; [|discriminate].
          apply andb_prop in Hav as [Ht Ho]. apply Uint63.eqb_spec in Ht. apply Z.eqb_eq in Ho. subst t o.
          pose proof (aview_sound rho' (XV CS) XB (bd_vt bd) (f_mem F') (bd_tl bd) (bd_xt bd) lf_regions lf_rho0 rs_tl rs_xt a _ _ Hv) as Hs.
          rewrite E3 in Hs.
          assert (Hc2 : (2 < length content)%nat) by lia.
          assert (Hflat : AX2S.flat E a 1) by (unfold AX2S.flat; rewrite Hs; lia).
          cbn [AX2S.kentry_ok]. split; [lia|]. split; [exact Hflat|].
          assert (Ead : AX2.adenot E a = adr rho' 3%uint63 (bufoff k + Z.of_nat 2)).
          { apply bv_eq. rewrite (AX2S.flat_u _ _ _ Hflat), Hs.
            destruct (rs_mem (bufoff k + Z.of_nat 2) ltac:(lia)) as (_ & Hu & _). rewrite Hu, E3. lia. }
          apply rdn_intro; [reflexivity|]. intros j0 Hj0. assert (j0 = 0%nat) by lia. subst j0.
          rewrite aoff_0, Ead. unfold rview. rewrite (Hbytes 2%nat Hc2).
          rewrite (nth_error_nth' content (Z_to_bv 8 0) Hc2). cbn [nth_error word_to_le_bytes Z_to_le_bytes].
          do 2 f_equal. cbn [AX2.edenot]. rewrite ev_env_of.
          unfold is_ext_var in Hext9. unfold XV. cbn [Nat.eqb].
          destruct (vt_get (bd_vt bd) 9) as [[| |]|]; try discriminate;
            cbn [vden]; unfold XV; cbn [Nat.eqb]; rewrite (HX9 CS);
            rewrite Z_to_bv_small by (pose proof (bv_unsigned_in_range _ (nth 2 content (Z_to_bv 8 0))) as Hr8;
                                       unfold bv_modulus in *; change (2 ^ 8) with 256 in Hr8; lia);
            symmetry; apply Z_to_bv_bv_unsigned.
        - (* [comment removed for export] *)
          do 3 (destruct j as [|j]; try discriminate). destruct j; try discriminate.
          cbn [resid_entry_ok] in HK. apply andb_prop in HK as [HK Hvn]. apply andb_prop in HK as [HK Hva].
          apply andb_prop in HK as [Ho0 Ho1]. apply Z.leb_le in Ho0. apply Z.ltb_lt in Ho1.
          pose proof (rs_tagval 112%uint63 _ ltac:(cbn; lia) E112 _ Hva) as Ua.
          pose proof (rs_tagval 113%uint63 _ ltac:(cbn; lia) E113 _ Hvn) as Un.
          unfold addr_expr in Ua. cbn [AX2.edenot] in Ua.
          pose proof (AX2S.u_add_eqm (AX2.edenot E (AX2.a_base a)) (Z_to_bv 64 (AX2.a_off a))) as [q Hq].
          rewrite Ua in Hq. rewrite (Z_to_bv_small 64 (AX2.a_off a)) in Hq by (unfold bv_modulus; lia).
          pose proof (br_u64 (AX2.edenot E (AX2.a_base a))) as Hub.
          assert (Hlo : 4096 <= bv_unsigned B).
          { destruct (rs_mem 0 ltac:(lia)) as (_ & _ & _).
            destruct HD as ((_ & _ & _ & _ & Hinv & _) & _ & _ & _ & _ & Hex). destruct Hex as [Hmaps _].
            destruct Hinv as [_ _ _ _ _ Hal Htop _ _ _ _ _ _ _ _ _].
            pose proof rs_vis as Hv. unfold ledger_vis_b in Hv. apply andb_prop in Hv as [He _].
            unfold in_entry_b in He. apply andb_prop in He as [_ He]. apply existsb_exists in He as (e0 & Hin0 & Hc0).
            destruct (covers_spec _ _ _ _ Hc0) as (off0 & len0 & -> & Hoa & Hob).
            assert (Hp0 : In (den rho' (3%uint63, off0, len0)) (vm_maps (m_vmmaps m'))) by (rewrite Hmaps; apply in_map; exact Hin0).
            pose proof (proj1 (Forall_forall _ _) Hal _ Hp0) as [Hal1 _].
            pose proof (proj1 (Forall_forall _ _) Htop _ Hp0) as [Ht1 _].
            pose proof (i63_range off0). assert (Hoffz : to_Z off0 = 0) by lia.
            unfold e_lo, den in Hal1, Ht1. cbn [fst] in Hal1, Ht1. unfold adr in Hal1, Ht1. rewrite Hoffz in Hal1, Ht1.
            rewrite bv_add_unsigned in Hal1, Ht1. change (bv_unsigned (Z_to_bv 64 0)) with 0 in Hal1, Ht1.
            rewrite Z.add_0_r, bv_wrap_small in Hal1, Ht1 by apply bv_unsigned_in_range. rewrite E3 in Hal1, Ht1.
            unfold page_size in Hal1. destruct (Z_lt_le_dec (bv_unsigned B) 4096) as [Hlt|]; [|lia].
            rewrite Z.mod_small in Hal1 by lia. lia. }
          assert (Hq0 : q = 0) by lia. subst q.
          assert (Hst : AX2S.estart E a = buf + 6 + hdr_cfglen content) by (unfold AX2S.estart; lia).
          cbn [AX2S.kentry_ok]. unfold AX2S.elenZ. rewrite Un.
          assert (Hflat : AX2S.flat E a (hdr_paylen content)) by (unfold AX2S.flat; rewrite Hst; lia).
          split; [exact Hflat|]. rewrite eb_env_of, HX3.
          split. { rewrite length_skipn. unfold hdr_paylen in *. lia. }
          intros i Hi. rewrite Hst.
          set (j := (Z.to_nat (6 + hdr_cfglen content) + Z.to_nat i)%nat).
          assert (Hj : (j < length content)%nat) by (unfold j, hdr_paylen in *; lia).
          assert (Ead : Z_to_bv 64 (buf + 6 + hdr_cfglen content + i) = adr rho' 3%uint63 (bufoff k + Z.of_nat j)).
          { apply bv_eq. destruct (rs_mem (bufoff k + Z.of_nat j) ltac:(lia)) as (_ & Hu & _). rewrite Hu, E3.
            rewrite Z_to_bv_small by (unfold bv_modulus; unfold j; lia). unfold j. lia. }
          rewrite Ead, (Hbytes j Hj). unfold j. rewrite <- (nth_error_skipn content (Z.to_nat (6 + hdr_cfglen content)) (Z.to_nat i)).
          apply nth_error_nth'. rewrite length_skipn. unfold hdr_paylen in *. lia.
        - (* [comment removed for export] *)
          destruct e as [|x| | | | | |]; try discriminate.
          cbn [resid_entry_ok] in HK. apply orb_prop in HK as [Hvac|HK].
          { apply andb_prop in Hvac as [Hlo Hhi]. apply Z.leb_le in Hlo. apply Z.leb_le in Hhi.
            cbn [AX2S.kentry_ok].
            pose proof (bv_unsigned_in_range _ (AX2.edenot E (AX2.EVar x))) as Hr. unfold bv_modulus in Hr.
            change (2 ^ Z.of_N 64) with 18446744073709551616 in Hr. lia. }
          apply andb_prop in HK as [HK Hxr]. apply andb_prop in HK as [Hxe Hx2].
          apply negb_true_iff in Hx2. pose proof (HXR CS x rlo rhi Hxr) as Hr.
          cbn [AX2S.kentry_ok AX2.edenot]. rewrite ev_env_of.
          unfold is_ext_var in Hxe.
          destruct (vt_get (bd_vt bd) x) as [[| |]|]; try discriminate;
            cbn [vden]; unfold XV; rewrite Hx2; exact Hr.
      Qed.

      Lemma lf_resid : resid_ok RSEGS H0T (argHt STR0) bd (XV CS) XB rho' ms' m' CS.
      Proof.
        unfold resid_ok. pose proof Hrc as Hr'. unfold resid_chk in Hr'. apply andb_prop in Hr' as [_ Hall].
        rewrite forallb_forall in Hall. apply Forall_forall. intros K HK. exact (rs_entry K (Hall K HK)).
      Qed.
    End Resid.

    Hypothesis Hchk : leaf_chk (F', L', n', r) = true.

    Theorem h0br_leaf : realizes_cfg ConeCfg.CFG RSEGS (mkCfg ms' m') T.
    Proof.
      pose proof Hchk as Hc. unfold leaf_chk in Hc. cbn [fst snd] in Hc.
      apply existsb_exists in Hc as (CS & HCS & Hc).
      destruct (br_infer_auto IMH H0T KEEP (kfacts k) F' L' CS [] (TEQ k) TB 192 kit_pins) as [bd|] eqn:Hinf; [|discriminate].
      apply andb_prop in Hc as [Hc Hx]. apply andb_prop in Hc as [Hc Hrc]. apply andb_prop in Hc as [Hc Htid]. apply andb_prop in Hc as [Hc Hfd].
      apply andb_prop in Hc as [Hc Htc]. apply andb_prop in Hc as [Hc Hts]. apply andb_prop in Hc as [Hbc Hsv].
      apply Uint63.eqb_spec in Hts. apply Z.eqb_eq in Htc.
      destruct (br_infer_auto_fields _ _ _ _ _ _ _ _ _ _ _ _ _ Hinf) as (Ext & Eteq & Etb & Eah).
      assert (HXT : xt_ok rho' (XV CS) XB (bd_vt bd) (bd_xt bd)) by (rewrite Ext; constructor).
      pose proof lf_sp as [Hspw Hsp16]. pose proof lf_isp2 as Hisp2.
      set (E := env_of rho' (XV CS) XB (bd_vt bd)).
      (* [comment removed for export] *)
      assert (Hsinv : SINVx CS E (ms_mem ms')).
      { split; [|exact (HPHI CS bd F' L' rho' HCS Hx lf_rho0)].
        destruct (sinv_facts rho' (XV CS) XB (bd_vt bd) (f_mem F') (bd_tl bd) (bd_xt bd) 1%uint63 8388608 lf_rho0 lf_regions
                    (bridge_check_tl _ _ _ _ _ _ _ _ _ _ Hbc) HXT Hsv) as (S1 & S2 & S3 & S4 & S5 & S6).
        fold E in S1, S2, S3, S4, S5, S6. rewrite <- Hisp2 in S1, S2, S6.
        unfold SINVt. split; [exact S1|]. split.
        { apply br_eqm_small.
          - eapply AX2S.eqm_trans; [exact S6|]. unfold XV. cbn [Nat.eqb].
            rewrite Z_to_bv_small by (unfold bv_modulus; lia). apply AX2S.eqm_refl.
          - apply br_u64.
          - lia. }
        split; [exact S4|]. split; [exact S3|]. split; [exact S5|].
        split; [exact (proj1 XB12)|]. split; [exact (proj2 XB12)|].
        split; [unfold CAP.pgdown; exact S2 | exact lf_zero]. }
      (* [comment removed for export] *)
      assert (HB := bridge_sound ConeCfg.CFG RSEGS IMH (segments_reserved RSEGS) RB LIM RTgt KEEP M
                      (XI_frame fim) [] (ms_fregs (fi_ms R M)) (ms_fcsr (fi_ms R M)) (FxMisc.seg_rom RSEGS)
                      (fun x => bv_unsigned sp0 <= bv_unsigned x) (proj1 res_bounds)
                      H0T (SINVx CS) (argHt STR0) (bv_unsigned sp0) fs0 h0t_in_hull h0t_res_cover h0t_hull_ne eq_refl
                      bd (XV CS) XB n' rho' F' L' ms' m' CS (kfacts k) HD eq_refl eq_refl eq_refl Hbc).
      rewrite Etb, Eteq, Eah, Hts, Htc in HB.
      specialize (HB lf_tb lf_teq HXT (fi_ms R M) (mk_fimage_ok RSEGS IMH IMH_eq) eq_refl lf_kf lf_isp Hisp2).
      assert (HargH : forall a, argHt STR0 E a = true -> bv_unsigned sp0 + 192 <= bv_unsigned a).
      { intros a Ha. unfold argHt in Ha. apply Z.eqb_eq in Ha. lia. }
      specialize (HB HargH (lf_resid CS bd Hbc Hts Htc Eah Eteq Ext Hrc)).
      assert (Hfds : CXS.fds_ok E (CAP.a_fd CS) m').
      { destruct (CAP.a_fd CS); try discriminate. cbn [CXS.fds_ok].
        rewrite (same_but_vm_fds _ _ lf_xi). reflexivity. }
      assert (Hfs : m_fs m' = fs0) by (rewrite (same_but_vm_fs _ _ lf_xi); reflexivity).
      specialize (HB Hfds Hfs ltac:(intros Hf; rewrite Hf in Htid; discriminate) Hsinv).
      destruct HB as [Hms HC]. rewrite Hms.
      apply (FAMILY CS HCS E (ms_regs ms') (ms_mem ms') m' HC).
      exact (HEOK _ _ _ _ _ _ HR CS bd F' L' rho' HCS Hx lf_agree Eteq).
    Qed.
  End Leaf.
End H0Br.

(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import HUFiTail.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Top.
  Variable KT : list byte -> Fs.Fs -> TSet.
  Variable TB : Z -> list (int * Z * Z).                  (* [comment removed for export] *)
  Variable CSL : Z -> list CAP.acs.                        (* [comment removed for export] *)
  Variable PHI : CAP.acs -> AX2.env -> Prop.
  Variable EOK : list byte -> Z -> Z -> CAP.acs -> AX2.env -> Prop.   (* [comment removed for export] *)
  Variable XVX : list byte -> CAP.acs -> nat -> word.     (* [comment removed for export] *)
  Variable XB : list byte -> nat -> list byte.
  Variable XRNG : nat -> Z -> Z -> bool.                   (* [comment removed for export] *)
  Variable XCHK : Z -> CAP.acs -> bdata -> fstate -> fledger -> bool.

  (* [comment removed for export] *)
  Hypothesis CHK : forall k, In k KS -> forallb (leaf_chk k (TB k) (CSL k) XRNG (XCHK k)) (tree_leaves (the_tree k FUEL)) = true.
  (* [comment removed for export] *)
  Hypothesis HTBlt : forall k, tb_tags_lt 200 (TB k) = true.
  Hypothesis XB12 : forall content, XB content 1%nat = [] /\ XB content 2%nat = [].
  Hypothesis HX3 : forall content, XB content 3%nat = skipn (Z.to_nat (6 + hdr_cfglen content)) content.
  Hypothesis HX9 : forall content CS, XVX content CS 9%nat = Z_to_bv 64 (bv_unsigned (nth 2 content (Z_to_bv 8 0))).
  Hypothesis HXR : forall content CS x lo hi, XRNG x lo hi = true -> lo <= bv_unsigned (XVX content CS x) <= hi.

  Definition SINVy (sp0 : word) (envc : Z) (CS : CAP.acs) : AX2.env -> (word -> option byte) -> Prop :=
    fun E M' => SINVt (bv_unsigned sp0) (bv_unsigned sp0 + 192 + 8 * envc) E M' /\ PHI CS E.

  (* [comment removed for export] *)
  Hypothesis HTB : forall sp0 k buf can content VM R M mb bw B sec tdz err,
    valid_sp sp0 -> tgt_entry_full sp0 k buf can content VM R M -> root_extra sp0 VM M ->
    fi_root_facts sp0 k buf can VM R M mb bw B sec tdz err ->
    tb_ok (fi_rho sp0 can R mb B sec tdz err) (TB k).
  (* [comment removed for export] *)
  Hypothesis FAMILY : forall sp0 k buf can content VM R M envc fs0,
    valid_sp sp0 -> tgt_entry_full sp0 k buf can content VM R M ->
    0 <= envc /\ bv_unsigned sp0 + 192 + 8 * envc < 2 ^ 47 - 32 ->
    forall CS, In CS (CSL k) -> forall E R' FULL model,
      CXS.cs_ok HSEGS H0T LIM (SINVy sp0 envc CS) (argHt (bv_unsigned sp0 + 192 + 8 * envc)) (bv_unsigned sp0) fs0
                E CS R' FULL model ->
      EOK content k envc CS E ->
      realizes_cfg ConeCfg.CFG RSEGS (mkCfg (mkst R' (Z_to_bv 64 (CAP.pc CS)) FULL (PropExec.seg_rom RSEGS)) model) (KT content fs0).
  Hypothesis HPHI : forall k content envc CS bd F L rho', In CS (CSL k) -> XCHK k CS bd F L = true -> rho' 0%uint63 = Z_to_bv 64 0 ->
    PHI CS (env_of rho' (XV envc (XVX content) CS) (XB content) (bd_vt bd)).
  Hypothesis HEOK : forall sp0 k buf can content VM R M envc mb bw B sec tdz err,
    tgt_entry_full sp0 k buf can content VM R M ->
    fi_root_facts sp0 k buf can VM R M mb bw B sec tdz err ->
    forall CS bd F L (rho' : int -> word), In CS (CSL k) -> XCHK k CS bd F L = true ->
      (forall t, to_Z t < 200 -> rho' t = fi_rho sp0 can R mb B sec tdz err t) ->
      bd_teq bd = TEQ k -> EOK content k envc CS (env_of rho' (XV envc (XVX content) CS) (XB content) (bd_vt bd)).
  Lemma chk_leaf : forall k x, In k KS -> leaf_in x (the_tree k FUEL) -> leaf_chk k (TB k) (CSL k) XRNG (XCHK k) x = true.
  Proof.
    intros k x Hk Hleaf.
    exact (proj1 (forallb_forall (leaf_chk k (TB k) (CSL k) XRNG (XCHK k)) (tree_leaves (the_tree k FUEL))) (CHK k Hk) x
             (tree_leaves_in (the_tree k FUEL) x Hleaf)).
  Qed.

  Theorem h0br_leaf_tail : leaf_tail_stmt KT.
  Proof.
    unfold leaf_tail_stmt.
    intros sp0 k buf can content VM R M stdin0 fs0 tid Hsp Htid TF [(envc & He0 & He1 & Hz) Hbrk]
           mb bw B sec tdz err HR F' L' n' r rho' ms' m' Hleaf HD Hext _.
    pose proof (chk_leaf k _ (tgt_k_range _ _ _ _ _ _ _ _ TF) Hleaf) as Hlc.
    apply (h0br_leaf sp0 k buf can content VM R M stdin0 fs0 tid TF FUEL envc (conj He0 He1) Hz (TB k) (HTBlt k)
             (fun mb0 bw0 B0 sec0 tdz0 err0 HR0 => HTB sp0 k buf can content VM R M mb0 bw0 B0 sec0 tdz0 err0 Hsp TF
                                                     (conj (ex_intro _ envc (conj He0 (conj He1 Hz))) Hbrk) HR0)
             (CSL k) PHI (KT content fs0) (EOK content k envc)
             (fun CS HCS E R' FULL model HC HE => FAMILY sp0 k buf can content VM R M envc fs0 Hsp TF (conj He0 He1) CS HCS E R' FULL model HC HE)
             (XVX content) (XB content) (XB12 content) (HX3 content) (HX9 content) XRNG (HXR content) (XCHK k)
             (fun CS bd F L rho0 HCS Hx H0 => HPHI k content envc CS bd F L rho0 HCS Hx H0)
             (fun mb0 bw0 B0 sec0 tdz0 err0 HR0 CS bd F L rho0 HCS Hx Hag Eteq =>
                HEOK sp0 k buf can content VM R M envc mb0 bw0 B0 sec0 tdz0 err0 TF HR0 CS bd F L rho0 HCS Hx Hag Eteq)
             mb bw B sec tdz err HR F' L' n' r rho' ms' m' Hleaf HD Hext Hlc).
  Qed.
End Top.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition TB_std (k : Z) : list (int * Z * Z) :=
  [ (1%uint63, 0x7fff80000000 - 8388608, 0x7fffffffff40 - 8388608);
    (2%uint63, 0x354000, 0x354000 + 0x80000000);
    (6%uint63, 1, 4194303);
    (7%uint63, 0, 4294967295);          (* [comment removed for export] *)
    (111%uint63, 0, 32767);
    (113%uint63, 0, (if k =? 0 then 65535 else capk k)) ].

Lemma TB_std_lt : forall k, tb_tags_lt 200 (TB_std k) = true.
Proof. intros k. reflexivity. Qed.

Lemma TB_std_root : forall sp0 k buf can content VM R M mb bw B sec tdz err,
  valid_sp sp0 -> tgt_entry_full sp0 k buf can content VM R M -> root_extra sp0 VM M ->
  fi_root_facts sp0 k buf can VM R M mb bw B sec tdz err ->
  tb_ok (fi_rho sp0 can R mb B sec tdz err) (TB_std k).
Proof.
  intros sp0 k buf can content VM R M mb bw B sec tdz err (Hs1 & Hs2 & Hs16) TF [(envc & He0 & He1 & _) Hbrk] HR.
  destruct (handoff_teqs sp0 k buf can content VM R M mb B sec tdz err (Z_to_bv 64 0) (Z_to_bv 64 0) TF)
    as (E111 & _ & E113 & _ & _ & _ & Hc & Hp & Hlen & Hcap & _ & _ & _).
  pose proof (fr_exact _ _ _ _ _ _ _ _ _ _ _ _ _ HR) as (_ & _ & Xs & _).
  pose proof (fr_tid _ _ _ _ _ _ _ _ _ _ _ _ _ HR) as Htid.
  pose proof (fr_err _ _ _ _ _ _ _ _ _ _ _ _ _ HR) as Herr.
  rewrite Xs, hreserved_top in Hbrk. unfold brk_aslr_max in Hbrk. unfold sp_window_lo, sp_window_hi in *.
  pose proof (bv_unsigned_in_range _ mb) as Hmb. unfold bv_modulus in Hmb.
  pose proof (rho1 sp0 mb B (bv_unsigned can) sec tdz err R (Z_to_bv 64 0) (Z_to_bv 64 0)) as E1. unfold T_STK in E1.
  pose proof (rho2 sp0 mb B (bv_unsigned can) sec tdz err R (Z_to_bv 64 0) (Z_to_bv 64 0)) as E2. unfold T_BRK in E2.
  pose proof (rho6 sp0 mb B (bv_unsigned can) sec tdz err R (Z_to_bv 64 0) (Z_to_bv 64 0)) as E6. unfold T_TID in E6.
  pose proof (rho7 sp0 mb B (bv_unsigned can) sec tdz err R (Z_to_bv 64 0) (Z_to_bv 64 0)) as E7. unfold T_ERR in E7.
  assert (Hsp40 : bv_unsigned sp0 <= 0x7fffffffff40) by (Z.div_mod_to_equations; lia).
  unfold tb_ok, TB_std, fi_rho in *.
  apply Forall_cons; [cbv beta iota; rewrite E1, Z_to_bv_small by (unfold bv_modulus; lia); lia|].
  apply Forall_cons; [cbv beta iota; rewrite E2, Z_to_bv_small by (unfold bv_modulus; lia); lia|].
  apply Forall_cons; [cbv beta iota; rewrite E6, Z_to_bv_small by (unfold bv_modulus; lia); lia|].
  apply Forall_cons; [cbv beta iota; rewrite E7, Z_to_bv_small by (unfold bv_modulus; lia); lia|].
  apply Forall_cons; [cbv beta iota; rewrite E111; lia|].
  apply Forall_cons; [cbv beta iota; rewrite E113; destruct (k =? 0); lia|].
  apply Forall_nil.
Qed.


(* [comment removed for export] *)
Definition h0br_leaf_tail_std KT CSL PHI EOK XVX XB XRNG XCHK CHK XB12 HX3 HX9 HXR :=
  h0br_leaf_tail KT TB_std CSL PHI EOK XVX XB XRNG XCHK CHK TB_std_lt XB12 HX3 HX9 HXR
    (fun sp0 k buf can content VM R M mb bw B sec tdz err Hsp TF Hre HR =>
       TB_std_root sp0 k buf can content VM R M mb bw B sec tdz err Hsp TF Hre HR).
