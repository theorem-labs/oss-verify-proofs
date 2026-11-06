(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCState BzCSortM BzArrD CmpMem CmpCut CmpFsKit0 AsanKit AsanCut AsanCutB0 AsanKitB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCQsortM1 BzCQsortM2 BzCSewA BzCSewC BzCSewF.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCLemmasMs BzCLemmasMs2 BzCLemmasMs3 CmpCutMS CmpMsKit CmpMsKit2.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.
Local Ltac lia ::= CmpLiaC.lia_c.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.
Local Ltac simpl_arr_sizes ::= CmpFast.sas7_all.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
Import BzCSewC.BzCSewB.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import B0_cmp_fsV B0_cmp_msV B0_cmp_msW B0_cmp_msX.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.
Section B0MS.
  Variable X : msenv. Variable Y : amenv. Variables SHF SHn : Z. Variable Q : machine_state -> Prop.
  Hypothesis XOK : msenv_ok X. Hypothesis XSEP : msenv_sep X. Hypothesis YOK : amenv_ok X Y. Hypothesis YSX : amenv_sepx X Y.
  Notation usp := (bv_unsigned (me_sp X)). Notation P := (am_P Y).
  Notation A1 := (me_A1 X). Notation A2 := (me_A2 X). Notation FT := (me_FT X). Notation n := (me_n X). Notation qo := (me_qo X).
  Notation gp := (me_gp X). Notation tp := (me_tp X). Notation F := (me_F X). Notation fc := (me_fc X).
  Notation cSB := (Z_to_bv 64 2147450880). Notation BD := (am_BD Y). Notation CS := (am_CS Y). Notation CE := (am_CE Y).
  Notation WCF := [(A1, A1 + ARR1_SIZE); (CS, CS + 1024)]%Z.
  Notation WCB := [(A1, A1 + ARR1_SIZE); (CE, CE + 1024)]%Z.
  (* [comment removed for export] *)

  Ltac rd32_at FTB idx :=
    lazymatch type of FTB with u32arr ?segs ?mm ?A (zw32 ?a ?nn) =>
      let RD := fresh "RD" in
      pose proof (zw32_read segs mm A a nn idx _ FTB ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD;
      wstep; clear RD; try rewrite (sx32_of_Z_signed (zget a idx)) by lia
    end.
  Tactic Notation "zw32_store_at" constr(ARR) constr(i) constr(v) tactic(tac) :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m ?ad (le4 ?w)) _) =>
      lazymatch type of ARR with u32arr ?segs m ?A (zw32 ?a ?n) =>
        let H := fresh "ARRw" in
        pose proof (zw32_write segs m A a n i w v ARR ltac:(lia) ltac:(tac)) as H;
        let E := addr_expr ad in
        try replace (wa (A + 4 * i)) with (wa E) in H by (unfold wa; f_equal; lia);
        clear ARR; store_done; rename H into ARR
      end end.
  Ltac rdptr AR1 AOK idx :=
    lazymatch type of AR1 with u8arr ?segs ?mm ?A (zb8 ?a ?nn) =>
      let RD := fresh "RD" in
      pose proof (zb8_read4 segs mm A a nn idx _ AR1 ltac:(lia) ltac:(lia) AOK ltac:(unfold wa; f_equal; lia)) as RD;
      wstep; clear RD; try rewrite (sx32_of_Z (rd32 a idx)) by lia
    end.
  Ltac rdblk AR2 AOK idx :=
    lazymatch type of AR2 with u8arr ?segs ?mm ?A (zb8 ?a ?nn) =>
      let RD := fresh "RD" in
      pose proof (zb8_read1 segs mm A a nn idx _ AR2 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD;
      wstep; clear RD; cbv beta;
      let B := fresh "By" in pose proof (AOK idx) as B;
      rewrite (unsigned_lit8 (zget a idx)) by lia
    end.

  (* [comment removed for export] *)
  Lemma B0_cfwd : forall (f : nat) (j ss SHc : Z) (a1 a2 bd cs : zarr) (sq : slq)
      (x1 x5 x6 x7 x12 x13 x14 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word) (me m : word -> option byte),
    (0 <= ss < 256)%Z -> (j < zget cs ss)%Z -> saddr (CS + 4 * ss) SHc ->
    (forall k, let '(r, jk) := ms_copy_fwd k a1 cs a2 bd n ss j in fwdF a2 bd n ss (fst r) (snd r) jk) ->
    (let '(r, jF) := ms_copy_fwd f a1 cs a2 bd n ss j in zget (snd r) ss <= jF)%Z ->
    zbok a1 -> zbok a2 -> zbok bd -> pr n a1 0 (n - 1) ->
    u8arr b0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr b0segs m A2 (zb8 a2 ARR2_SIZE) ->
    u8arr b0segs m BD (zb8 bd 256) -> u32arr b0segs m CS (zw32 cs 256) ->
    rw_cells b0segs m P (slm_cells X Y SHF SHn sq) -> mem_inv b0segs m ->
    munch WCF me m -> wmono b0segs me m ->
    shzW b0segs WCF me A1 (A1 + ARR1_SIZE) -> shzW b0segs WCF me A2 (A2 + ARR2_SIZE) -> shzW b0segs WCF me CS (CS + 1024) ->
    (forall m' (a1' cs' : zarr) (jF : Z) (x5' x6' x7' x28' x12' : word),
      ms_copy_fwd f a1 cs a2 bd n ss j = (a1', cs', jF) ->
      zbok a1' -> pr n a1' 0 (n - 1) -> (forall c, 0 <= c < 256 -> 0 <= zget cs' c <= n)%Z ->
      u8arr b0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr b0segs m' A2 (zb8 a2 ARR2_SIZE) ->
      u8arr b0segs m' BD (zb8 bd 256) -> u32arr b0segs m' CS (zw32 cs' 256) ->
      rw_cells b0segs m' P (slm_cells X Y SHF SHn sq) -> mem_inv b0segs m' ->
      munch WCF me m' -> wmono b0segs me m' ->
      evt b0segs Q (MS (mkR x1 (Z_to_bv 64 P) gp tp x5' x6' x7' (me_sp X) (Z_to_bv 64 P)
                            (Z_to_bv 64 (CS + 4 * ss)) (Z_to_bv 64 (A1 + 4 * jF)) x12' (Z_to_bv 64 (zget cs' ss)) x14 (Z_to_bv 64 SHc) (Z_to_bv 64 jF) (Z_to_bv 64 (A1 + 4 * jF))
                            x18 x19 x20 x21 x22 x23 x24 x25 x26 cSB x28' x29 x30 x31)
                       F (Z_to_bv 64 0xa3f9c) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR x1 (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                          (Z_to_bv 64 (CS + 4 * ss)) (Z_to_bv 64 (A1 + 4 * j)) x12 x13 x14 (Z_to_bv 64 SHc) (Z_to_bv 64 j) (Z_to_bv 64 (A1 + 4 * j))
                          x18 x19 x20 x21 x22 x23 x24 x25 x26 cSB x28 x29 x30 x31)
                     F (Z_to_bv 64 0xa3e4c) fc None m (seg_rom b0segs)).
  Proof.
    induction f as [|f IH].
    { intros. exfalso. cbn [ms_copy_fwd fst snd] in H3. lia. }
    intros j ss SHc a1 a2 bd cs sq x1 x5 x6 x7 x12 x13 x14 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 me m
           Hss Hj ASC FWF FIN A1OK A2OK BDOK PR AR1 AR2 BDB CB SLB MI MU WM SH1 SH2 SHC K.
    msenv_open XOK. amenv_open YOK. pose proof XSEP as SP. unfold msenv_sep, apartm in SP. cps_destruct SP as (AP12 & AP1F & AP2F & _).
    pose proof (amsx_1_BD X Y YSX) as AS1b. pose proof (amsx_1_CS X Y YSX) as AS1c. pose proof (amsx_2_BD X Y YSX) as AS2b. pose proof (amsx_2_CS X Y YSX) as AS2c. box_ors.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2.
    pose proof (zb8_length bd 256 ltac:(lia)) as Lbd. pose proof (zw32_length cs 256 ltac:(lia)) as Lc.
    open_slb_in SLB.
    pose proof (FWF 0%nat) as F0. cbn [ms_copy_fwd fst snd] in F0. destruct F0 as [CR F0]. destruct (F0 Hj) as [Hjn F0c]. clear F0.
    pose proof (CR ss ltac:(lia)) as Css.
    rewrite ms_copy_fwd_S in FIN, K. replace (j <? zget cs ss) with true in FIN, K by (symmetry; apply Z.ltb_lt; lia).
    cbv zeta in FIN. cbv zeta in K. unfold kwrap in FIN, K, F0c.
    pose proof (PR j ltac:(lia)) as Pj. set (pj := rd32 a1 j) in *.
    (* [comment removed for export] *)
    brun. rdptr AR1 A1OK j. fold pj.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. rewrite (sign_sel (pj + -1) n) by lia.
    set (sel := (if (pj + -1 <? 0)%Z then n else 0%Z)).
    set (kk := (if (pj - 1 <? 0)%Z then (pj - 1 + n)%Z else (pj - 1)%Z)) in *.
    assert (SEL : ((pj = 0)%Z /\ sel = n /\ kk = (n - 1)%Z) \/ ((1 <= pj)%Z /\ sel = 0%Z /\ kk = (pj - 1)%Z))
      by (subst sel kk; destruct (Z.ltb_spec (pj + -1) 0); destruct (Z.ltb_spec (pj - 1) 0); lia).
    clearbody sel.
    wstep. replace (sel + (pj + -1))%Z with kk by lia.
    assert (Hkk : (0 <= kk < n)%Z) by lia.
    (* [comment removed for export] *)
    brun. rdblk AR2 A2OK kk. unfold rd8 in FIN, K, F0c. set (c1 := zget a2 kk) in *.
    (* [comment removed for export] *)
    brun. rdblk BDB BDOK c1.
    wstep; if_cases Kb; zify_cond_z Kb.
    - (* [comment removed for export] *)
      replace (zget bd c1 =? 0) with false in FIN, K by (symmetry; apply Z.eqb_neq; lia).
      (* [comment removed for export] *)
      brun. rd32_at CB ss.
      wstep. wstep. wstep. wstep; if_cases Kc; zify_cond_z Kc.
      + lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          enter_with (IH (j + 1)%Z ss SHc a1 a2 bd cs sq x1 _ _ _ _ _ x14 x18 x19 x20 x21 x22 x23 x24 x25 x26 _ x29 x30 x31 me mm) end;
          [st_eq| lia| lia| exact ASC| | exact FIN| exact A1OK| exact A2OK| exact BDOK| exact PR| exact AR1| exact AR2| exact BDB| exact CB| exact SLB| exact MI| exact MU| exact WM
          | exact SH1| exact SH2| exact SHC| exact K].
        intros k. pose proof (FWF (S k)) as Fk. rewrite ms_copy_fwd_S in Fk. replace (j <? zget cs ss) with true in Fk by (symmetry; apply Z.ltb_lt; lia).
        cbv zeta in Fk. unfold kwrap in Fk. fold pj in Fk. fold kk in Fk. unfold rd8 in Fk. fold c1 in Fk.
        replace (zget bd c1 =? 0) with false in Fk by (symmetry; apply Z.eqb_neq; lia). exact Fk.
      + rewrite ms_copy_fwd_stop in K by lia. wstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm a1 cs (j + 1)%Z _ _ _ _ _) end;
          [st_eq| reflexivity| exact A1OK| exact PR| exact CR| exact AR1| exact AR2| exact BDB| exact CB| exact SLB| exact MI| exact MU| exact WM].
    - (* [comment removed for export] *)
      replace (zget bd c1 =? 0) with true in FIN, K by (symmetry; apply Z.eqb_eq; lia). specialize (F0c ltac:(lia)).
      pose proof (CR c1 ltac:(lia)) as Cc1.
      brun. rd32_at CB c1.
      (* [comment removed for export] *)
      brun.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (u32arr_store_ok b0segs mm CS _ c1 _ CB ltac:(rewrite zw32_length_nat; lia) eq_refl) as SO1 end.
      wstep. zw32_store_at CB c1 (zget cs c1 + 1)%Z (apply unsigned_lit_mod32).
      pose proof (FWF 1%nat) as F1. rewrite ms_copy_fwd_S in F1. replace (j <? zget cs ss) with true in F1 by (symmetry; apply Z.ltb_lt; lia).
      cbv zeta in F1. unfold kwrap in F1. fold pj in F1. fold kk in F1. unfold rd8 in F1. fold c1 in F1.
      replace (zget bd c1 =? 0) with true in F1 by (symmetry; apply Z.eqb_eq; lia). cbn [ms_copy_fwd fst snd] in F1. destruct F1 as [CR1 _].
      pose proof (CR1 ss ltac:(lia)) as Css1.
      (* [comment removed for export] *)
      brun.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (SO2 : store_ok b0segs mm (wa (A1 + 4 * zget cs c1)) 4 = true)
          by (eapply (u8arr_storeN_ok b0segs _ A1 _ (4 * zget cs c1) 4 _ AR1); [lia| rewrite zb8_length_nat; lia| unfold wa; f_equal; lia]) end.
      wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ _) _) =>
        pose proof (zb8_write4 b0segs mm A1 a1 ARR1_SIZE (zget cs c1) (Z_to_bv 64 kk) AR1 ltac:(lia) ltac:(lia)) as AR1w end.
      clear AR1. store_done. rename AR1w into AR1. rewrite (unsigned_lit kk) in AR1 by lia.
      assert (OK1 : zbok (wr32 a1 (zget cs c1) kk)) by (apply zbok_wr32; exact A1OK).
      assert (PR1 : pr n (wr32 a1 (zget cs c1) kk) 0 (n - 1)) by (apply pr_wr32; [lia| exact PR| lia]).
      (* [comment removed for export] *)
      brun. rd32_at CB ss.
      wstep. wstep. wstep. wstep; if_cases Kc; zify_cond_z Kc.
      + lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          enter_with (IH (j + 1)%Z ss SHc (wr32 a1 (zget cs c1) kk) a2 bd (zset cs c1 (zget cs c1 + 1)) sq x1 _ _ _ _ _ x14 x18 x19 x20 x21 x22 x23 x24 x25 x26 _ x29 x30 x31 me mm) end;
          [st_eq| lia| lia| exact ASC| | exact FIN| exact OK1| exact A2OK| exact BDOK| exact PR1| exact AR1| exact AR2| exact BDB| exact CB| exact SLB| exact MI| exact MU| exact WM
          | exact SH1| exact SH2| exact SHC| exact K].
        intros k. pose proof (FWF (S k)) as Fk. rewrite ms_copy_fwd_S in Fk. replace (j <? zget cs ss) with true in Fk by (symmetry; apply Z.ltb_lt; lia).
        cbv zeta in Fk. unfold kwrap in Fk. fold pj in Fk. fold kk in Fk. unfold rd8 in Fk. fold c1 in Fk.
        replace (zget bd c1 =? 0) with true in Fk by (symmetry; apply Z.eqb_eq; lia). exact Fk.
      + rewrite ms_copy_fwd_stop in K by lia. wstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ (j + 1)%Z _ _ _ _ _) end;
          [st_eq| reflexivity| exact OK1| exact PR1| exact CR1| exact AR1| exact AR2| exact BDB| exact CB| exact SLB| exact MI| exact MU| exact WM].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.

  (* [comment removed for export] *)
  Lemma B0_cbwd : forall (f : nat) (j ss SHc : Z) (a1 a2 bd ce : zarr) (sq : slq)
      (x1 x5 x6 x7 x12 x13 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x30 x31 : word) (me m : word -> option byte),
    (0 <= ss < 256)%Z -> (zget ce ss < j)%Z -> saddr (CE + 4 * ss) SHc ->
    (forall k, let '(r, jk) := ms_copy_bwd k a1 ce a2 bd n ss j in bwdF a2 bd n ss (fst r) (snd r) jk) ->
    (let '(r, jF) := ms_copy_bwd f a1 ce a2 bd n ss j in jF <= zget (snd r) ss)%Z ->
    zbok a1 -> zbok a2 -> zbok bd -> pr n a1 0 (n - 1) ->
    u8arr b0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr b0segs m A2 (zb8 a2 ARR2_SIZE) ->
    u8arr b0segs m BD (zb8 bd 256) -> u32arr b0segs m CE (zw32 ce 256) ->
    rw_cells b0segs m P (slm_cells X Y SHF SHn sq) -> mem_inv b0segs m ->
    munch WCB me m -> wmono b0segs me m ->
    shzW b0segs WCB me A1 (A1 + ARR1_SIZE) -> shzW b0segs WCB me A2 (A2 + ARR2_SIZE) -> shzW b0segs WCB me CE (CE + 1024) ->
    (forall m' (a1' ce' : zarr) (jF : Z) (x5' x6' x7' x28' x17' : word),
      ms_copy_bwd f a1 ce a2 bd n ss j = (a1', ce', jF) ->
      zbok a1' -> pr n a1' 0 (n - 1) -> (forall c, 0 <= c < 256 -> -1 <= zget ce' c < n)%Z ->
      u8arr b0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr b0segs m' A2 (zb8 a2 ARR2_SIZE) ->
      u8arr b0segs m' BD (zb8 bd 256) -> u32arr b0segs m' CE (zw32 ce' 256) ->
      rw_cells b0segs m' P (slm_cells X Y SHF SHn sq) -> mem_inv b0segs m' ->
      munch WCB me m' -> wmono b0segs me m' ->
      evt b0segs Q (MS (mkR x1 (Z_to_bv 64 P) gp tp x5' x6' x7' (me_sp X) (Z_to_bv 64 P)
                            (Z_to_bv 64 (CE + 4 * ss)) (Z_to_bv 64 (A1 + 4 * jF)) (Z_to_bv 64 (zget ce' ss)) x13 (Z_to_bv 64 SHc) (Z_to_bv 64 jF) (Z_to_bv 64 (A1 + 4 * jF)) x17'
                            x18 x19 x20 x21 x22 x23 x24 x25 x26 cSB x28' (Z_to_bv 64 (18446744073709551615 - BD)) x30 x31)
                       F (Z_to_bv 64 0xa4150) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR x1 (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                          (Z_to_bv 64 (CE + 4 * ss)) (Z_to_bv 64 (A1 + 4 * j)) x12 x13 (Z_to_bv 64 SHc) (Z_to_bv 64 j) (Z_to_bv 64 (A1 + 4 * j)) x17
                          x18 x19 x20 x21 x22 x23 x24 x25 x26 cSB x28 (Z_to_bv 64 (18446744073709551615 - BD)) x30 x31)
                     F (Z_to_bv 64 0xa3ff4) fc None m (seg_rom b0segs)).
  Proof.
    induction f as [|f IH].
    { intros. exfalso. cbn [ms_copy_bwd fst snd] in H3. lia. }
    intros j ss SHc a1 a2 bd ce sq x1 x5 x6 x7 x12 x13 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x30 x31 me m
           Hss Hj ASC FWF FIN A1OK A2OK BDOK PR AR1 AR2 BDB CB SLB MI MU WM SH1 SH2 SHC K.
    msenv_open XOK. amenv_open YOK. pose proof XSEP as SP. unfold msenv_sep, apartm in SP. cps_destruct SP as (AP12 & AP1F & AP2F & _).
    pose proof (amsx_1_BD X Y YSX) as AS1b. pose proof (amsx_1_CE X Y YSX) as AS1c. pose proof (amsx_2_BD X Y YSX) as AS2b. pose proof (amsx_2_CE X Y YSX) as AS2c. box_ors.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2.
    pose proof (zb8_length bd 256 ltac:(lia)) as Lbd. pose proof (zw32_length ce 256 ltac:(lia)) as Lc.
    open_slb_in SLB.
    pose proof (FWF 0%nat) as F0. cbn [ms_copy_bwd fst snd] in F0. destruct F0 as [CR F0]. destruct (F0 Hj) as [Hjn F0c]. clear F0.
    pose proof (CR ss ltac:(lia)) as Css.
    rewrite ms_copy_bwd_S in FIN, K. replace (zget ce ss <? j) with true in FIN, K by (symmetry; apply Z.ltb_lt; lia).
    cbv zeta in FIN. cbv zeta in K. unfold kwrap in FIN, K, F0c.
    pose proof (PR j ltac:(lia)) as Pj. set (pj := rd32 a1 j) in *.
    (* [comment removed for export] *)
    brun. rdptr AR1 A1OK j. fold pj.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. rewrite (sign_sel (pj + -1) n) by lia.
    set (sel := (if (pj + -1 <? 0)%Z then n else 0%Z)).
    set (kk := (if (pj - 1 <? 0)%Z then (pj - 1 + n)%Z else (pj - 1)%Z)) in *.
    assert (SEL : ((pj = 0)%Z /\ sel = n /\ kk = (n - 1)%Z) \/ ((1 <= pj)%Z /\ sel = 0%Z /\ kk = (pj - 1)%Z))
      by (subst sel kk; destruct (Z.ltb_spec (pj + -1) 0); destruct (Z.ltb_spec (pj - 1) 0); lia).
    clearbody sel.
    wstep. replace (sel + (pj + -1))%Z with kk by lia.
    assert (Hkk : (0 <= kk < n)%Z) by lia.
    (* [comment removed for export] *)
    brun. rdblk AR2 A2OK kk. unfold rd8 in FIN, K, F0c. set (c1 := zget a2 kk) in *.
    (* [comment removed for export] *)
    brun. rdblk BDB BDOK c1.
    wstep; if_cases Kb; zify_cond_z Kb.
    - (* [comment removed for export] *)
      replace (zget bd c1 =? 0) with false in FIN, K by (symmetry; apply Z.eqb_neq; lia).
      (* [comment removed for export] *)
      brun. rd32_at CB ss.
      wstep. wstep. wstep. wstep; if_cases Kc; zify_cond_z Kc.
      + lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          enter_with (IH (j - 1)%Z ss SHc a1 a2 bd ce sq x1 _ _ _ _ x13 _ x18 x19 x20 x21 x22 x23 x24 x25 x26 _ x30 x31 me mm) end;
          [st_eq| lia| lia| exact ASC| | exact FIN| exact A1OK| exact A2OK| exact BDOK| exact PR| exact AR1| exact AR2| exact BDB| exact CB| exact SLB| exact MI| exact MU| exact WM
          | exact SH1| exact SH2| exact SHC| exact K].
        intros k. pose proof (FWF (S k)) as Fk. rewrite ms_copy_bwd_S in Fk. replace (zget ce ss <? j) with true in Fk by (symmetry; apply Z.ltb_lt; lia).
        cbv zeta in Fk. unfold kwrap in Fk. fold pj in Fk. fold kk in Fk. unfold rd8 in Fk. fold c1 in Fk.
        replace (zget bd c1 =? 0) with false in Fk by (symmetry; apply Z.eqb_neq; lia). exact Fk.
      + rewrite ms_copy_bwd_stop in K by lia. wstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm a1 ce (j - 1)%Z _ _ _ _ _) end;
          [st_eq| reflexivity| exact A1OK| exact PR| exact CR| exact AR1| exact AR2| exact BDB| exact CB| exact SLB| exact MI| exact MU| exact WM].
    - (* [comment removed for export] *)
      replace (zget bd c1 =? 0) with true in FIN, K by (symmetry; apply Z.eqb_eq; lia). specialize (F0c ltac:(lia)).
      pose proof (CR c1 ltac:(lia)) as Cc1.
      brun. rd32_at CB c1.
      (* [comment removed for export] *)
      brun.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (u32arr_store_ok b0segs mm CE _ c1 _ CB ltac:(rewrite zw32_length_nat; lia) eq_refl) as SO1 end.
      wstep. zw32_store_at CB c1 (zget ce c1 - 1)%Z (rewrite unsigned_lit_mod32; reflexivity).
      pose proof (FWF 1%nat) as F1. rewrite ms_copy_bwd_S in F1. replace (zget ce ss <? j) with true in F1 by (symmetry; apply Z.ltb_lt; lia).
      cbv zeta in F1. unfold kwrap in F1. fold pj in F1. fold kk in F1. unfold rd8 in F1. fold c1 in F1.
      replace (zget bd c1 =? 0) with true in F1 by (symmetry; apply Z.eqb_eq; lia). cbn [ms_copy_bwd fst snd] in F1. destruct F1 as [CR1 _].
      pose proof (CR1 ss ltac:(lia)) as Css1.
      (* [comment removed for export] *)
      brun.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (SO2 : store_ok b0segs mm (wa (A1 + 4 * zget ce c1)) 4 = true)
          by (eapply (u8arr_storeN_ok b0segs _ A1 _ (4 * zget ce c1) 4 _ AR1); [lia| rewrite zb8_length_nat; lia| unfold wa; f_equal; lia]) end.
      wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ _) _) =>
        pose proof (zb8_write4 b0segs mm A1 a1 ARR1_SIZE (zget ce c1) (Z_to_bv 64 kk) AR1 ltac:(lia) ltac:(lia)) as AR1w end.
      clear AR1. store_done. rename AR1w into AR1. rewrite (unsigned_lit kk) in AR1 by lia.
      assert (OK1 : zbok (wr32 a1 (zget ce c1) kk)) by (apply zbok_wr32; exact A1OK).
      assert (PR1 : pr n (wr32 a1 (zget ce c1) kk) 0 (n - 1)) by (apply pr_wr32; [lia| exact PR| lia]).
      (* [comment removed for export] *)
      brun. rd32_at CB ss.
      wstep. wstep. wstep. wstep; if_cases Kc; zify_cond_z Kc.
      + lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          enter_with (IH (j - 1)%Z ss SHc (wr32 a1 (zget ce c1) kk) a2 bd (zset ce c1 (zget ce c1 - 1)) sq x1 _ _ _ _ x13 _ x18 x19 x20 x21 x22 x23 x24 x25 x26 _ x30 x31 me mm) end;
          [st_eq| lia| lia| exact ASC| | exact FIN| exact OK1| exact A2OK| exact BDOK| exact PR1| exact AR1| exact AR2| exact BDB| exact CB| exact SLB| exact MI| exact MU| exact WM
          | exact SH1| exact SH2| exact SHC| exact K].
        intros k. pose proof (FWF (S k)) as Fk. rewrite ms_copy_bwd_S in Fk. replace (zget ce ss <? j) with true in Fk by (symmetry; apply Z.ltb_lt; lia).
        cbv zeta in Fk. unfold kwrap in Fk. fold pj in Fk. fold kk in Fk. unfold rd8 in Fk. fold c1 in Fk.
        replace (zget bd c1 =? 0) with true in Fk by (symmetry; apply Z.eqb_eq; lia). exact Fk.
      + rewrite ms_copy_bwd_stop in K by lia. wstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ (j - 1)%Z _ _ _ _ _) end;
          [st_eq| reflexivity| exact OK1| exact PR1| exact CR1| exact AR1| exact AR2| exact BDB| exact CB| exact SLB| exact MI| exact MU| exact WM].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.
End B0MS.
End ACeilS1.
