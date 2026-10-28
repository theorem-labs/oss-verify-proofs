From Stdlib Require Import ZArith NArith List Bool PArith Lia Sorting.Permutation.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocInv MallocLayout MallocIface MallocLaws.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj Glue3.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Contract.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CfgGlue CursorGlue ObjUnbase ObjXform TobjJV.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVx.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L5 Require Import S_hf hf_defs.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L9 Require S_vr.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L10.S_pc.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L6.S_pg.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L11 Require Import hf_tri_defs hf_vr.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G2.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_defs.
Import HfAddrU.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module PCU := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L10.S_pc.
Module PGU := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L6.S_pg.
Module GL := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G2.Lib_handle_f_glue.
Module AR := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_arith.

Definition trb_z0 : sv := SLit 0.
Definition trb_pcK3 : Z := 0x199f4.
Definition trb_ra_rp : Z := 0x199b8.
Definition trb_ra_ts : Z := 0x19ab4.
Definition trb_ra_tp : Z := 0x19afc.
Definition trb_c14 : Z := 0x0AAAAAAAAAAAAAA9.

Definition trb_cps : list Z :=
  [vrU_entry; pcU_entry; pgU_entry; 0x18abc; 0x193ac; 0x193f4; 0x19394; 0x195c8; 0x19854;
   VRU.vr_ret; 0x19900; 0x1996c; trb_pcK3; 0x19b88; PGU.TessPolygonAddrU.pgU_ret].

Definition trb_opt (d : sstate) (x : option sstate) : sstate := match x with Some s => s | None => d end.

Definition trb_leaf (S : sstate) (pc : Z) : sstate :=
  match sym_run segsU FUEL_U trb_cps S true with
  | Some l => nth 0 (filter (fun st => Z.eqb (ss_pc st) pc) (map lf_state l)) S
  | None => S
  end.

Definition trb_c (o w : Z) (v : sv) : cell := mkCell (SLit o) w v.

Definition trb_rp0 : sv * sv * sv := (t_d rp1, SLit 0, t_k rp1).
Definition nz_av_k : list (positive * Z * positive) := [(110%positive, 4, 112%positive)].
Definition nz_rp_k : list (positive * Z * positive) := [(315%positive, 4, 317%positive)].
Definition nz_ts_k : list (positive * Z * positive) := [(321%positive, 1, 323%positive)].

Definition trb_kt_facts : list sprop :=
  tri_facts0 ++ [SPUle (n3U am2) (t_k tr1); SPNot (SPBranch BC_NE pS2 (SLit 0))] ++ nz_tr ++
  [SPUle (SLit 1) av_k].
Definition trb_kr_facts : list sprop :=
  trb_kt_facts ++ TobjJVx.nz_facts nz_av_k ++ [SPUle (n3U pA) (t_k rp1)] ++ TobjJVx.nz_facts nz_rp_k.
Definition trb_kq_facts : list sprop :=
  trb_kr_facts ++ [SPUle needA (t_k ts1)] ++ TobjJVx.nz_facts nz_ts_k.

Definition trb_KR_regs (r10 : sv) : list (nat * sv) :=
  [(1%nat, SLit trb_ra_rp); (9%nat, am2); (10%nat, r10); (18%nat, xb 784); (19%nat, pS2);
   (21%nat, t_d co1); (22%nat, snotU (t_d co1)); (23%nat, t_d tr1); (24%nat, pA); (25%nat, am2)].

Definition KR_U : sstate :=
  HSX_U VRU.vr_ret (trb_KR_regs (SLit 1)) K1_fcells pP coA trb_rp0 (coK pA) DUnknown [] trb_kr_facts.
Definition FR_U : sstate :=
  HSX_U VRU.vr_ret (trb_KR_regs (SLit 0)) K1_fcells pP coA trb_rp0 (coK pA) DUnknown []
    (trb_kt_facts ++ TobjJVx.nz_facts nz_av_k).

Definition trb_K3_regs : list (nat * sv) :=
  [(1%nat, SLit trb_ra_rp); (9%nat, am2); (10%nat, av_d); (11%nat, snotU av_d);
   (12%nat, SMd M_MUL (SLit 12) pI); (13%nat, pI); (14%nat, SLit trb_c14); (15%nat, snotU (t_d rp1));
   (16%nat, SLit 1); (18%nat, xb 784); (19%nat, pS2); (20%nat, t_d rp1); (21%nat, t_d co1);
   (22%nat, snotU (t_d co1)); (23%nat, t_d tr1); (24%nat, pA); (25%nat, am2)].

Definition KL3_U : sstate :=
  HSX_U trb_pcK3 trb_K3_regs K1_fcells pP coA trb_rp0 (coK pA) DUnknown []
    (trb_kr_facts ++ [SPUlt pI pA; SPUle pI (SLit (2 ^ 20)); hint12 pI]).

Definition trb_KQ_regs (ra : Z) (r10 : sv) : list (nat * sv) :=
  [(1%nat, SLit ra); (9%nat, am2); (10%nat, r10); (18%nat, needA); (19%nat, xb 816); (20%nat, t_d rp1);
   (21%nat, t_d co1); (22%nat, snotU (t_d co1)); (23%nat, t_d tr1); (24%nat, pA); (25%nat, am2)].

Definition KQ_U : sstate :=
  HSX_U VRU.vr_ret (trb_KQ_regs trb_ra_ts (SLit 1)) K1_fcells pP coA trb_rp0 (coK pA) DUnknown [] trb_kq_facts.
Definition FQ_U : sstate :=
  HSX_U VRU.vr_ret (trb_KQ_regs trb_ra_ts (SLit 0)) K1_fcells pP coA trb_rp0 (coK pA) DUnknown [] trb_kr_facts.

Definition trb_desc : list cell :=
  [trb_c (-176) 8 (t_d rp1); trb_c (-168) 4 pA; trb_c (-160) 8 (SLit 0); trb_c (-152) 4 (SLit 0);
   trb_c (-144) 8 (t_d tr1); trb_c (-136) 4 (n3U am2); trb_c (-128) 8 (t_d ts1); trb_c (-120) 8 needA;
   trb_c (-112) 8 (SLit 0)].

Definition KP_ok_U : sstate :=
  HSX_U PGU.TessPolygonAddrU.pgU_ret (trb_KQ_regs trb_ra_tp pST)
    ([trb_c (-200) 8 (t_d tr1); trb_c (-192) 4 am2; trb_c (-188) 4 (SLit 0); trb_c (-184) 4 pST] ++
     trb_desc ++ K1_fcells)
    pP coA trb_rp0 (coK pA) (trK am2) [] trb_kq_facts.
Definition KP_inv_U : sstate :=
  HSX_U PGU.TessPolygonAddrU.pgU_ret (trb_KQ_regs trb_ra_tp (SLit 2))
    ([trb_c (-200) 8 (SLit 0); trb_c (-192) 8 (SLit 0); trb_c (-184) 4 (SLit 2)] ++ trb_desc ++ K1_fcells)
    pP coA trb_rp0 (coK pA) DUnknown [] trb_kq_facts.

Definition E_rp_U : sstate := Eval vm_compute in trb_leaf KTok_U vrU_entry.
Definition E_ts_U : sstate := Eval vm_compute in trb_leaf KL3_U vrU_entry.
Definition E_tp_U : sstate := Eval vm_compute in trb_leaf KQ_U pgU_entry.

Definition trb_cuts : list edesc :=
  [(KR_U, tvH, (60, trb_z0)); (FR_U, tvH, (60, trb_z0)); (KL3_U, tvH, (58, SAlu ALU_SUB pA pI));
   (KQ_U, tvH, (54, trb_z0)); (FQ_U, tvH, (54, trb_z0)); (KP_ok_U, tvH, (50, trb_z0));
   (KP_inv_U, tvH, (50, trb_z0))].

Definition trb_exits : list edesc :=
  [(E_rp_U, tvH, (62, trb_z0)); (E_ts_U, tvH, (56, trb_z0)); (E_tp_U, tvH, (52, trb_z0))].

(* vec_reserve call sites *)

Definition trb_xs1 : list xform := [XSplit 1 (SLit (-32))].
Definition E_rpA : sstate := add_facts (TobjJVx.nz_facts nz_av_k) E_rp_U.
Definition E2_rp : sstate := Eval vm_compute in trb_opt E_rpA (TobjJVx.norm_xu trb_xs1 1 (-32) E_rpA).
Definition s_rp : wsub := Eval vm_compute in
  [(19%positive, SAlu ALU_ADD xD (SLit 32)); (15%positive, t_d rp1); (16%positive, SLit 0);
   (17%positive, t_k rp1); (18%positive, SLit 4)] ++ infer_sub 10 E2_rp VRU.Pre_vr.
Definition E2_ts : sstate := Eval vm_compute in trb_opt E_ts_U (TobjJVx.norm_xu trb_xs1 1 (-32) E_ts_U).
Definition s_ts : wsub := Eval vm_compute in
  [(19%positive, SAlu ALU_ADD xD (SLit 32)); (15%positive, t_d ts1); (16%positive, snd (fst ts1));
   (17%positive, t_k ts1); (18%positive, SLit 1)] ++ infer_sub 10 E2_ts VRU.Pre_vr.

(* tess_polygon call site *)

Definition trb_xs_tp1 : list xform :=
  [XSplit 0 (SLit (-200)); XSplit 1 (SLit (-180)); XSplit 2 (SLit (-176)); XSplit 3 (SLit (-104));
   XSplit 5 (SLit (- PGU.pgU_frame)); XSplit 33 (SMd M_MUL pA (SLit 12));
   XSplit 35 (SMd M_MUL (SAlu ALU_ADD pA (SLit (-2))) (SLit 12))].
Definition trb_tp_facts : list sprop := SPUle (SLit 4) pA :: AR.ts_facts.
Definition trb_fA : sprop := SPUle (SAlu ALU_SLL pA (SLit 4)) (t_k ts1).

Definition Etp1U (E : sstate) : sstate := trb_opt E (apply_xforms E trb_xs_tp1).
Definition Etp2aU (E : sstate) : sstate := trb_opt E (unbase_obj_at (Etp1U E) 1 (-200)).
Definition Etp2bU (E : sstate) : sstate := trb_opt E (unbase_obj_at (Etp2aU E) 3 (-176)).
Definition Etp2U (E : sstate) : sstate := trb_opt E (unbase_obj_at (Etp2bU E) 5 (- PGU.pgU_frame)).
Definition Etp3U (E : sstate) : sstate := TobjJVx.narrow_at (SLit 24) (Etp2U E) 3.
Definition Etp4U (E : sstate) : sstate := add_facts [trb_fA] (add_facts trb_tp_facts (Etp3U E)).
Definition Etp5U (E : sstate) : sstate := trb_opt E (apply_xforms (Etp4U E) GL.xs_tp2).
Definition Etp6U (E : sstate) : sstate :=
  reshape_obj_at (reshape_obj_at (reshape_obj_at (Etp5U E) 38 GL.O_nxt') 40 GL.O_prv') 42 GL.O_rfx'.

Definition tp_pre_checkU (E : sstate) : bool :=
  match apply_xforms E trb_xs_tp1 with
  | Some S1 =>
    match unbase_obj_at S1 1 (-200) with
    | Some S2a =>
      match unbase_obj_at S2a 3 (-176) with
      | Some S2b =>
        match unbase_obj_at S2b 5 (- PGU.pgU_frame) with
        | Some S2 =>
          let S3 := TobjJVx.narrow_at (SLit 24) S2 3 in
          let S4 := add_facts trb_tp_facts S3 in
          match nth_error (ss_objs S2) 3 with
          | Some o3 => match ob_dflt o3 with DUnknown => true | _ => false end
          | None => false
          end &&
          same_but_objs S2 S3 &&
          forallb (sprop_below (ss_next S3)) trb_tp_facts &&
          GL.memb (SPBranch BC_LTU (SLit 2) pA) (ss_facts S3) &&
          GL.memb (SPNot (SPBranch BC_EQ pA (SLit 3))) (ss_facts S3) &&
          GL.memb (SPUle pA (SLit (2 ^ 20))) (ss_facts S3) &&
          GL.memb (SPUle needA (t_k ts1)) (ss_facts S3) &&
          forallb (sprop_below (ss_next S4)) [trb_fA] &&
          SymStep.uleq (ss_facts S4) (SAlu ALU_SLL pA (SLit 4)) 0 (t_k ts1) &&
          match apply_xforms (add_facts [trb_fA] S4) GL.xs_tp2 with
          | Some S5 =>
            GL.tp_need_facts (ss_facts S5) &&
            GL.obj_shape S5 38 (t_d ts1) AR.o16A AR.oNXTe &&
            obj_wf (ss_next S5) GL.O_nxt' &&
            GL.obj_shape (reshape_obj_at S5 38 GL.O_nxt') 40 (t_d ts1) AR.oPRV AR.oPRVe &&
            obj_wf (ss_next S5) GL.O_prv' &&
            GL.obj_shape (reshape_obj_at (reshape_obj_at S5 38 GL.O_nxt') 40 GL.O_prv') 42 (t_d ts1) AR.oRFX AR.oRFXe &&
            obj_wf (ss_next S5) GL.O_rfx'
          | None => false
          end
        | None => false
        end
      | None => false
      end
    | None => false
    end
  | None => false
  end.

Lemma trb_four_le : forall rho,
  holds rho (SPBranch BC_LTU (SLit 2) pA) -> holds rho (SPNot (SPBranch BC_EQ pA (SLit 3))) ->
  4 <= bv_unsigned (eval rho pA).
Proof.
  intros rho H1 H2. cbn [holds Sem.branch_taken] in H1, H2. unfold Prelude.bv_ltu, Prelude.bv_eqb in H1, H2.
  rewrite !U_lit in H1, H2. unfold M64v in *. rewrite !Z.mod_small in H1, H2 by lia.
  apply Z.ltb_lt in H1. destruct (Z.eqb_spec (bv_unsigned (eval rho pA)) 3) as [E3|E3];
    [exfalso; apply H2; reflexivity | lia].
Qed.

Lemma tp_pre_soundU : forall (J : jpred) (E : sstate) (rho : valuation) (w : world),
  tp_pre_checkU E = true -> SPJ segsU J E rho w -> SPJ segsU J (Etp6U E) rho w.
Proof.
  intros J E rho w P0 Hw. unfold tp_pre_checkU in P0.
  destruct (apply_xforms E trb_xs_tp1) as [S1|] eqn:X1; [|discriminate].
  destruct (unbase_obj_at S1 1 (-200)) as [S2a|] eqn:X2a; [|discriminate].
  destruct (unbase_obj_at S2a 3 (-176)) as [S2b|] eqn:X2b; [|discriminate].
  destruct (unbase_obj_at S2b 5 (- PGU.pgU_frame)) as [S2|] eqn:X2; [|discriminate].
  cbv zeta in P0.
  set (S3 := TobjJVx.narrow_at (SLit 24) S2 3) in *.
  apply andb_prop in P0 as [P0 Hm]. apply andb_prop in P0 as [P0 Hule]. apply andb_prop in P0 as [P0 Hbelow2].
  apply andb_prop in P0 as [P0 M4]. apply andb_prop in P0 as [P0 M3]. apply andb_prop in P0 as [P0 M2].
  apply andb_prop in P0 as [P0 M1]. apply andb_prop in P0 as [P0 Hbelow]. apply andb_prop in P0 as [Hd3 Hsame].
  apply GL.memb_In in M1. apply GL.memb_In in M2. apply GL.memb_In in M3. apply GL.memb_In in M4.
  destruct (apply_xforms (add_facts [trb_fA] (add_facts trb_tp_facts S3)) GL.xs_tp2) as [S5|] eqn:X5; [|discriminate].
  apply andb_prop in Hm as [Hm W42]. apply andb_prop in Hm as [Hm Sh42]. apply andb_prop in Hm as [Hm W40].
  apply andb_prop in Hm as [Hm Sh40]. apply andb_prop in Hm as [Hm W38]. apply andb_prop in Hm as [Hneed5 Sh38].
  destruct (nth_error (ss_objs S2) 3) as [o3|] eqn:N3; [|discriminate].
  assert (E6 : Etp6U E = reshape_obj_at (reshape_obj_at (reshape_obj_at S5 38 GL.O_nxt') 40 GL.O_prv') 42 GL.O_rfx').
  { unfold Etp6U, Etp5U, Etp4U, Etp3U, Etp2U, Etp2bU, Etp2aU, Etp1U. rewrite X1. cbn [trb_opt]. rewrite X2a. cbn [trb_opt].
    rewrite X2b. cbn [trb_opt]. rewrite X2. cbn [trb_opt]. subst S3. rewrite X5. reflexivity. }
  rewrite E6.
  assert (H2 : SPJ segsU J S2 rho w).
  { eapply SPJ_unbase; [exact X2|]. eapply SPJ_unbase; [exact X2b|]. eapply SPJ_unbase; [exact X2a|].
    eapply SPJ_xforms; [exact X1 | exact Hw]. }
  assert (H3 : SPJ segsU J S3 rho w).
  { subst S3. eapply (TobjJVx.SPJ_narrow segsU (SLit 24) _ rho S2 3 o3 w N3); [|exact Hsame|exact H2].
    destruct (ob_dflt o3); try discriminate; reflexivity. }
  assert (H4 : SPJ segsU J (add_facts trb_tp_facts S3) rho w).
  { apply (SPJ_refacts_J segsU _ rho S3 trb_tp_facts w H3 Hbelow).
    intros tr md _ HF.
    pose proof (proj1 (Forall_forall _ _) HF _ M1) as F1. pose proof (proj1 (Forall_forall _ _) HF _ M2) as F2.
    pose proof (proj1 (Forall_forall _ _) HF _ M3) as F3. pose proof (proj1 (Forall_forall _ _) HF _ M4) as F4.
    pose proof (trb_four_le rho F1 F2) as A4.
    cbn [holds] in F3. rewrite U_lit in F3. unfold M64v in F3. rewrite Z.mod_small in F3 by lia.
    unfold trb_tp_facts. constructor.
    - cbn [holds]. rewrite U_lit. unfold M64v. rewrite Z.mod_small by lia. exact A4.
    - apply (AR.ts_facts_ok rho); [split; [exact A4 | exact F3] | exact F4]. }
  assert (H4b : SPJ segsU J (add_facts [trb_fA] (add_facts trb_tp_facts S3)) rho w).
  { apply (SPJ_refacts_J segsU _ rho _ [trb_fA] w H4 Hbelow2).
    intros tr md _ HF. constructor; [|constructor].
    pose proof (uleq_sound rho _ _ 0 _ HF Hule) as U1. unfold SymSoundV.U in U1. unfold trb_fA. cbn [holds]. lia. }
  assert (H5 : SPJ segsU J S5 rho w). { eapply SPJ_xforms; [exact X5 | exact H4b]. }
  destruct (GL.obj_shapeP _ _ _ _ _ Sh38) as (o38 & N38 & B38 & L38 & Hi38 & D38).
  destruct (GL.obj_shapeP _ _ _ _ _ Sh40) as (o40 & N40 & B40 & L40 & Hi40 & D40).
  destruct (GL.obj_shapeP _ _ _ _ _ Sh42) as (o42 & N42 & B42 & L42 & Hi42 & D42).
  eapply (SPJ_reshape segsU _ rho _ 42 o42 GL.O_rfx' w N42 eq_refl eq_refl D42 W42).
  { intros HF. destruct (GL.tp_need_factsP _ rho Hneed5 HF) as [A1 A2].
    unfold obj_lo_of, obj_hi_of, GL.O_rfx'. cbn [ob_base ob_lo ob_hi]. rewrite B42, L42, Hi42.
    destruct (AR.rfx_eqs rho A1 A2) as [E1 E2]. cbn [t_d ts1 pT]. cbn [eval] in E1, E2 |- *. lia. }
  eapply (SPJ_reshape segsU _ rho _ 40 o40 GL.O_prv' w N40 eq_refl eq_refl D40 W40).
  { intros HF. destruct (GL.tp_need_factsP _ rho Hneed5 HF) as [A1 A2].
    unfold obj_lo_of, obj_hi_of, GL.O_prv'. cbn [ob_base ob_lo ob_hi]. rewrite B40, L40, Hi40.
    destruct (AR.prv_eqs rho A1 A2) as [E1 E2]. cbn [t_d ts1 pT]. cbn [eval] in E1, E2 |- *. lia. }
  eapply (SPJ_reshape segsU _ rho S5 38 o38 GL.O_nxt' w N38 eq_refl eq_refl D38 W38); [|exact H5].
  intros HF. destruct (GL.tp_need_factsP _ rho Hneed5 HF) as [A1 A2].
  unfold obj_lo_of, obj_hi_of, GL.O_nxt'. cbn [ob_base ob_lo ob_hi]. rewrite B38, L38, Hi38.
  destruct (AR.nxt_eqs rho A1 A2) as [E1 E2]. cbn [t_d ts1 pT]. cbn [eval] in E1, E2 |- *. lia.
Qed.

Definition norm_tp2U (C1 : sstate) : option sstate :=
  match apply_xforms C1 GL.xs_tp3 with
  | Some C2 =>
    match TobjJVx.merge_arr_at C2 29 with
    | Some C3 =>
      match apply_xforms C3 GL.xs_tp4 with
      | Some C4 => unbase_obj_at C4 1 (-272)
      | None => None
      end
    | None => None
    end
  | None => None
  end.
Definition norm_tpU (C : sstate) : option sstate :=
  norm_tp2U (reshape_obj_at (reshape_obj_at (reshape_obj_at C 7 GL.O_nxt0) 8 GL.O_prv0) 9 GL.O_rfx0).

Definition tpcont_checkU (n : positive) (C T : sstate) (vT : sv) (rT rE : Z) (vE : sv) : bool :=
  let C1 := reshape_obj_at C 7 GL.O_nxt0 in
  let C2 := reshape_obj_at C1 8 GL.O_prv0 in
  GL.obj_shape C 7 AR.pNXT' (SLit 0) AR.o4A && GL.obj_shape C1 8 AR.pPRV' (SLit 0) AR.o4A &&
  GL.obj_shape C2 9 AR.pRFX' (SLit 0) AR.orfx && obj_wf (ss_next C) GL.O_nxt0 &&
  obj_wf (ss_next C) GL.O_prv0 && obj_wf (ss_next C) GL.O_rfx0 && GL.tp_need_facts (ss_facts C) &&
  match norm_tpU C with
  | Some X => TobjJVx.entE_check NP n X T tvH tvH vT rT rE vE
  | None => false
  end.

Lemma tpcont_soundU : forall (J : jpred) n C T vT rT rE vE, tpcont_checkU n C T vT rT rE vE = true ->
  exists X, norm_tpU C = Some X /\ TobjJVx.entE_check NP n X T tvH tvH vT rT rE vE = true /\
    (forall rho w, SPJ segsU J C rho w -> SPJ segsU J X rho w).
Proof.
  intros J n C T vT rT rE vE Hc. unfold tpcont_checkU in Hc. cbv zeta in Hc.
  apply andb_prop in Hc as [Hc NX]. apply andb_prop in Hc as [Hc NF0]. apply andb_prop in Hc as [Hc W9].
  apply andb_prop in Hc as [Hc W8]. apply andb_prop in Hc as [Hc W7]. apply andb_prop in Hc as [Hc S9].
  apply andb_prop in Hc as [S7 S8].
  destruct (norm_tpU C) as [Xs|] eqn:EN; [|discriminate]. exists Xs. split; [reflexivity|]. split; [exact NX|].
  intros rho w Hw.
  destruct (GL.obj_shapeP _ _ _ _ _ S7) as (o7 & N7 & B7 & L7 & Hi7 & D7).
  destruct (GL.obj_shapeP _ _ _ _ _ S8) as (o8 & N8 & B8 & L8 & Hi8 & D8).
  destruct (GL.obj_shapeP _ _ _ _ _ S9) as (o9 & N9 & B9 & L9 & Hi9 & D9).
  unfold norm_tpU, norm_tp2U in EN.
  destruct (apply_xforms (reshape_obj_at (reshape_obj_at (reshape_obj_at C 7 GL.O_nxt0) 8 GL.O_prv0) 9 GL.O_rfx0)
    GL.xs_tp3) as [C4|] eqn:E4; [|discriminate].
  destruct (TobjJVx.merge_arr_at C4 29) as [C5|] eqn:E5; [|discriminate].
  destruct (apply_xforms C5 GL.xs_tp4) as [C6|] eqn:E6; [|discriminate].
  eapply SPJ_unbase; [exact EN|]. eapply SPJ_xforms; [exact E6|]. eapply TobjJVx.SPJ_merge_arr; [exact E5|].
  eapply SPJ_xforms; [exact E4|].
  eapply (SPJ_reshape segsU _ rho _ 9 o9 GL.O_rfx0 w N9 eq_refl eq_refl D9 W9).
  { intros HF. destruct (GL.tp_need_factsP _ rho NF0 HF) as [A1 A2].
    unfold obj_lo_of, obj_hi_of, GL.O_rfx0. cbn [ob_base ob_lo ob_hi]. rewrite B9, L9, Hi9.
    destruct (AR.rfx_eqs rho A1 A2) as [E1 E2]. cbn [t_d ts1 pT]. cbn [eval] in E1, E2 |- *. lia. }
  eapply (SPJ_reshape segsU _ rho _ 8 o8 GL.O_prv0 w N8 eq_refl eq_refl D8 W8).
  { intros HF. destruct (GL.tp_need_factsP _ rho NF0 HF) as [A1 A2].
    unfold obj_lo_of, obj_hi_of, GL.O_prv0. cbn [ob_base ob_lo ob_hi]. rewrite B8, L8, Hi8.
    destruct (AR.prv_eqs rho A1 A2) as [E1 E2]. cbn [t_d ts1 pT]. cbn [eval] in E1, E2 |- *. lia. }
  eapply (SPJ_reshape segsU _ rho C 7 o7 GL.O_nxt0 w N7 eq_refl eq_refl D7 W7); [|exact Hw].
  intros HF. destruct (GL.tp_need_factsP _ rho NF0 HF) as [A1 A2].
  unfold obj_lo_of, obj_hi_of, GL.O_nxt0. cbn [ob_base ob_lo ob_hi]. rewrite B7, L7, Hi7.
  destruct (AR.nxt_eqs rho A1 A2) as [E1 E2]. cbn [t_d ts1 pT]. cbn [eval] in E1, E2 |- *. lia.
Qed.

Definition Etp6_U : sstate := Eval vm_compute in Etp6U E_tp_U.
Definition s_tp_U : wsub := Eval vm_compute in (20%positive, n3U am2) :: infer_sub 10 Etp6_U (PGU.Pre_pg_U []).
Definition R_tp : list sobj := Eval vm_compute in
  match entails_fr Etp6_U (PGU.Pre_pg_U []) s_tp_U with Some r => r | None => [] end.

Lemma trb_tp_pre : tp_pre_checkU E_tp_U = true.
Proof. vm_compute. reflexivity. Qed.

Lemma trb_tp_E6 : Etp6U E_tp_U = Etp6_U.
Proof. vm_compute. reflexivity. Qed.

Lemma trb_tp_inv : tpcont_checkU (ss_next Etp6_U)
  (add_facts (ss_facts Etp6_U) (import_post s_tp_U NF PGU.P_inv_U (ss_next Etp6_U) R_tp)) KP_inv_U trb_z0 50 52 trb_z0 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma trb_tp_ok : tpcont_checkU (ss_next Etp6_U)
  (add_facts (ss_facts Etp6_U) (import_post s_tp_U NF PGU.P_ok_U (ss_next Etp6_U) R_tp)) KP_ok_U trb_z0 50 52 trb_z0 = true.
Proof. vm_compute. reflexivity. Qed.

Section Trb.
Variable Kc : list event -> Model -> Prop.
Variable FB : list (Z * Z).
Variable rho0 : valuation.
Hypothesis ML : malloc_laws segsU C_U.
Variable TR : assn -> assn -> Prop.
Variable FAM : Z -> assn.
Hypothesis TR_facts : forall J S rho (Q' : assn),
  (Forall (holds rho) (ss_facts S) -> TR (SPJ segsU J S rho) Q') -> TR (SPJ segsU J S rho) Q'.
Hypothesis TR_ex : forall (A : Type) (J : A -> jpred) S rho (Q' : assn),
  (forall x, TR (SPJ segsU (J x) S rho) Q') -> TR (SPJ segsU (fun r t m => exists x, J x r t m) S rho) Q'.
Hypothesis TR_pre : forall (P P' Q' : assn), (forall w, P' w -> P w) -> TR P Q' -> TR P' Q'.
Hypothesis TR_exw : forall (A : Type) (P : A -> assn) (Q' : assn),
  (forall a, TR (P a) Q') -> TR (fun w => exists a, P a w) Q'.
Hypothesis TR_pureh : forall (X : Prop) (P Q' : assn), (X -> TR P Q') -> TR (fun w => X /\ P w) Q'.
Hypothesis TR_callP : ltac:(argty (client_callT segsU C_U NP Kc rho0 (P0_hf FB) FB ML (fun _ => VRU.P0_vr)
  VRU.Pre_vr VRU.tv0 VRU.PD_vr NF eq_refl TR TR_facts TR_ex TR_pre)).
Hypothesis TR_callJ : ltac:(argty (pure_callT segsU C_U NP Kc rho0 (P0_hf FB) FB ML TR TR_facts TR_pre)).
Hypothesis CVR : forall FBc rho1,
  TR (SPJ segsU (JG_pre segsU C_U Kc VRU.P0_vr FBc VRU.tv0) VRU.Pre_vr rho1)
     (LQP segsU NF rho1 (VRU.Posts_vr Kc FBc)).
Hypothesis CPC : forall tv rho rho1,
  TR (SP segsU (fun tr md => JG segsU C_U NP Kc rho0 (P0_hf FB) FB tv rho tr md) PCU.Pre_pc_U rho1)
     (LQ segsU (fun tr md => JG segsU C_U NP Kc rho0 (P0_hf FB) FB tv rho tr md) NF rho1 PCU.Posts_pc_U).
Hypothesis CTP : forall tv rho rho1,
  TR (SP segsU (fun tr md => JG segsU C_U NP Kc rho0 (P0_hf FB) FB tv rho tr md) (PGU.Pre_pg_U []) rho1)
     (LQ segsU (fun tr md => JG segsU C_U NP Kc rho0 (P0_hf FB) FB tv rho tr md) NF rho1 PGU.Posts_pg_U).
Hypothesis REENTER : forall T tv rv rho b, In (T, tv, rv) trb_cuts ->
  0 <= emeas (T, tv, rv) rho /\ emeas (T, tv, rv) rho < b ->
  TR (SPJ segsU (JG segsU C_U NP Kc rho0 (P0_hf FB) FB tv) T rho) (FAM b).
Hypothesis POST : forall P tv rho b, In (P, JLG segsU C_U Kc (P0_hf FB) FB tv) (Posts_hf_U Kc FB) ->
  TR (SPJ segsU (JG segsU C_U NP Kc rho0 (P0_hf FB) FB tv) P rho) (FAM b).

Let XS := X_vr_site Kc FB rho0 ML TR FAM TR_facts TR_ex TR_pre TR_exw TR_pureh TR_callP CVR trb_cuts REENTER.
Let PURE := pure_callT segsU C_U NP Kc rho0 (P0_hf FB) FB ML TR TR_facts TR_pre TR_callJ.
Let ENT := TobjJVx.entE_TR segsU C_U NP Kc rho0 (P0_hf FB) FB ML TR TR_pre TR_exw TR_pureh.

Lemma X_E_rp : forall rho,
  TR (SPJ segsU (JG segsU C_U NP Kc rho0 (P0_hf FB) FB tvH) E_rp_U rho) (FAM (emeas (E_rp_U, tvH, (62, trb_z0)) rho)).
Proof.
  intros rho. change (emeas (E_rp_U, tvH, (62, trb_z0)) rho) with (emeas (E_rpA, tvH, (62, trb_z0)) rho).
  eapply TR_pre.
  2: { eapply (XS E_rpA E2_rp trb_xs1 1 (-32) s_rp 6 nz_rp_k KR_U FR_U trb_z0 60 trb_z0 60 62 trb_z0 315 317 4 rho).
       - vm_compute. reflexivity.
       - vm_compute. reflexivity.
       - lia.
       - vm_compute. reflexivity.
       - vm_compute. reflexivity.
       - vm_compute. reflexivity.
       - vm_compute. tauto.
       - lia.
       - unfold trb_cuts. left. reflexivity.
       - unfold trb_cuts. right. left. reflexivity. }
  intros w Hw. unfold E_rpA. apply SPJ_refacts_J; [exact Hw | vm_compute; reflexivity |].
  intros tr md HJ HF.
  eapply (TobjJVx.nz_facts_sound segsU C_U NP Kc rho0 (P0_hf FB) FB (ss_facts E_rp_U) tvH nz_av_k);
    [vm_compute; reflexivity | exact HF | exact HJ].
Qed.

Lemma X_E_ts : forall rho,
  TR (SPJ segsU (JG segsU C_U NP Kc rho0 (P0_hf FB) FB tvH) E_ts_U rho) (FAM (emeas (E_ts_U, tvH, (56, trb_z0)) rho)).
Proof.
  intros rho.
  eapply (XS E_ts_U E2_ts trb_xs1 1 (-32) s_ts 8 nz_ts_k KQ_U FQ_U trb_z0 54 trb_z0 54 56 trb_z0 321 323 1 rho).
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - lia.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. tauto.
  - lia.
  - unfold trb_cuts. right. right. right. left. reflexivity.
  - unfold trb_cuts. right. right. right. right. left. reflexivity.
Qed.

Lemma X_E_tp : forall rho,
  TR (SPJ segsU (JG segsU C_U NP Kc rho0 (P0_hf FB) FB tvH) E_tp_U rho) (FAM (emeas (E_tp_U, tvH, (52, trb_z0)) rho)).
Proof.
  intros rho. eapply TR_pre.
  2: { apply (PURE Etp6_U (PGU.Pre_pg_U []) s_tp_U R_tp PGU.Posts_pg_U rho tvH _ (CTP tvH rho));
         [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity |
          vm_compute; reflexivity |].
       intros L rho' HinL Hag. destruct HinL as [<-|[<-|[]]]; cbn [lf_state].
       - destruct (tpcont_soundU (JG segsU C_U NP Kc rho0 (P0_hf FB) FB tvH) _ _ _ _ _ _ _ trb_tp_inv) as (X & HN & HC & HS).
         eapply TR_pre.
         2: { eapply (ENT _ X KP_inv_U tvH tvH tvH _ _ _ _ rho rho' _ HC (Permutation_refl _) (agree_below_vals _ _ _ Hag)).
              intros rho'' Hm. apply (REENTER KP_inv_U tvH (50, trb_z0) rho'');
                [unfold trb_cuts; right; right; right; right; right; right; left; reflexivity | exact Hm]. }
         intros w Hw. exact (HS rho' w Hw).
       - destruct (tpcont_soundU (JG segsU C_U NP Kc rho0 (P0_hf FB) FB tvH) _ _ _ _ _ _ _ trb_tp_ok) as (X & HN & HC & HS).
         eapply TR_pre.
         2: { eapply (ENT _ X KP_ok_U tvH tvH tvH _ _ _ _ rho rho' _ HC (Permutation_refl _) (agree_below_vals _ _ _ Hag)).
              intros rho'' Hm. apply (REENTER KP_ok_U tvH (50, trb_z0) rho'');
                [unfold trb_cuts; right; right; right; right; right; left; reflexivity | exact Hm]. }
         intros w Hw. exact (HS rho' w Hw). }
  intros w Hw. rewrite <- trb_tp_E6. exact (tp_pre_soundU _ E_tp_U rho w trb_tp_pre Hw).
Qed.

Lemma trb_exits_okT : forall X tvX rvX rho, In (X, tvX, rvX) trb_exits ->
  TR (SPJ segsU (JG segsU C_U NP Kc rho0 (P0_hf FB) FB tvX) X rho) (FAM (emeas (X, tvX, rvX) rho)).
Proof using Kc FB rho0 ML TR FAM TR_facts TR_ex TR_pre TR_exw TR_pureh TR_callP TR_callJ CVR CPC CTP REENTER POST.
  intros X tvX rvX rho Hin. unfold trb_exits in Hin.
  destruct Hin as [H|[H|[H|[]]]]; injection H as <- <- <-.
  - apply X_E_rp.
  - apply X_E_ts.
  - apply X_E_tp.
Qed.

End Trb.
