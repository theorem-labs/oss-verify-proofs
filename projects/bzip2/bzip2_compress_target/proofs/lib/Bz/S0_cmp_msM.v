(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsS0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Musl Require Import MuslStr.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzTac BzTac2 BzArr BzCMem BzCState BzCSortM BzArrD CmpMem CmpCut CmpCut0 CmpFsKit0 BzCQsortM1 BzCQsortM2 BzCSewA.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCSewC.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCSewF.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCSortM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpFsKit0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCQsortM1 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCQsortM2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCSewA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCSewC.BzCSewB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCSewF.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCLemmasMs CmpCutMS CmpMsKit S0_cmp_gtu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCLemmasMs2 BzCLemmasMs3 CmpMsKit2 S0_cmp_msV S0_cmp_msL.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas7.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section S0MS.
  Variable X : msenv. Variable Q : machine_state -> Prop.
  Hypothesis XOK : msenv_ok X. Hypothesis XSEP : msenv_sep X.
  Notation usp := (bv_unsigned (me_sp X)). Notation p := (bv_unsigned (me_sp X) - 4928)%Z.
  Notation A1 := (me_A1 X). Notation A2 := (me_A2 X). Notation FT := (me_FT X). Notation n := (me_n X). Notation qo := (me_qo X).
  Notation gp := (me_gp X). Notation tp := (me_tp X). Notation F := (me_F X). Notation fc := (me_fc X).

  Ltac rd32_at FTB idx :=
    lazymatch type of FTB with u32arr ?segs ?mm ?A (zw32 ?a ?nn) =>
      let RD := fresh "RD" in
      pose proof (zw32_read segs mm A a nn idx _ FTB ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD;
      wstep; clear RD; try rewrite (sx32_of_Z_signed (zget a idx)) by lia
    end.
  (* [comment removed for export] *)
  Tactic Notation "zw32_store_at" constr(ARR) constr(i) constr(v) tactic(tac) :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m ?ad (le4 ?w)) _) =>
      lazymatch type of ARR with u32arr ?segs m ?A (zw32 ?a ?n) =>
        let H := fresh "ARRw" in
        pose proof (zw32_write segs m A a n i w v ARR ltac:(lia) ltac:(tac)) as H;
        let E := addr_expr ad in
        try replace (wa (A + 4 * i)) with (wa E) in H by (unfold wa; f_equal; lia);
        clear ARR; store_done; rename H into ARR
      end end.

  (* [comment removed for export] *)
  Lemma S0_cinit : forall (cnt : nat) (j ss : Z) (ft cs ce : zarr)
      (x0 x4 x5 x6 x7 x8 x12 x13 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 : word) (me m : word -> option byte),
    Z.of_nat cnt = (256 - j)%Z -> (0 <= j < 256)%Z -> (0 <= ss < 256)%Z ->
    (forall v, 0 <= v <= 65536 -> 0 <= zget ft v < 4194304)%Z ->
    u32arr s0segs m FT (zw32 ft 65537) -> u32arr s0segs m (p + 1320) (zw32 cs 256) -> u32arr s0segs m (p + 296) (zw32 ce 256) -> mem_inv s0segs m ->
    munch [(p + 296, p + 2344)]%Z me m -> wmono s0segs me m ->
    (forall m' (x12' x13' : word), let r := ms_copy_init cnt cs ce ft ss j in
      u32arr s0segs m' FT (zw32 ft 65537) -> u32arr s0segs m' (p + 1320) (zw32 (fst r) 256) -> u32arr s0segs m' (p + 296) (zw32 (snd r) 256) -> mem_inv s0segs m' ->
      munch [(p + 296, p + 2344)]%Z me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (mkR x0 (Z_to_bv 64 p) gp tp x4 x5 x6 x7 x8
                            (Z_to_bv 64 (p + 1320)) (Z_to_bv 64 (FT + 4 + 4 * ss + 1024 * 256)) (Z_to_bv 64 (p + 1320 + 4 * 256)) x12' x13' (Z_to_bv 64 18446744073707454463) x15 x16
                            x17 x18 x19 (Z_to_bv 64 (p + 1320)) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30)
                       F (Z_to_bv 64 0x1a320) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR x0 (Z_to_bv 64 p) gp tp x4 x5 x6 x7 x8
                          (Z_to_bv 64 (p + 296 + 4 * j)) (Z_to_bv 64 (FT + 4 + 4 * ss + 1024 * j)) (Z_to_bv 64 (p + 1320 + 4 * j)) x12 x13 (Z_to_bv 64 18446744073707454463) x15 x16
                          x17 x18 x19 (Z_to_bv 64 (p + 1320)) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30)
                     F (Z_to_bv 64 0x1a2f4) fc None m (seg_rom s0segs)).
  Proof.
    induction cnt as [|cnt IH]; [intros; exfalso; lia|].
    intros j ss ft cs ce x0 x4 x5 x6 x7 x8 x12 x13 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 me m
           Hcnt Hj Hss FTV FTB CS CE MI MU WM K.
    msenv_open XOK.
    pose proof (zw32_length ft 65537 ltac:(lia)) as Lft. pose proof (zw32_length cs 256 ltac:(lia)) as Lcs. pose proof (zw32_length ce 256 ltac:(lia)) as Lce.
    rewrite ms_copy_init_S in K. rewrite shl8 in K.
    pose proof (FTV (256 * j + ss)%Z ltac:(lia)) as V0. pose proof (FTV (256 * j + ss + 1)%Z ltac:(lia)) as V1.
    (* [comment removed for export] *)
    rd32_at FTB (256 * j + ss)%Z. rd32_at FTB (256 * j + ss + 1)%Z.
    wstep. rewrite land_CM64 by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok s0segs mm (p + 1320) _ j _ CS ltac:(rewrite zw32_length_nat; lia) eq_refl) as SO1 end.
    wstep. zw32_store_at CS j (clearmask (zget ft (256 * j + ss))) (apply unsigned_lit_mod32).
    wstep. rewrite land_CM64 by lia. wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok s0segs mm (p + 296) _ j _ CE ltac:(rewrite zw32_length_nat; lia) eq_refl) as SO2 end.
    wstep. zw32_store_at CE j (clearmask (zget ft (256 * j + ss + 1)) - 1)%Z (apply unsigned_lit_mod32).
    (* [comment removed for export] *)
    wstep. wstep. wstep.
    wstep; if_cases Kc; zify_cond_z Kc.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (IH (j + 1)%Z ss ft _ _ x0 x4 x5 x6 x7 x8 _ _ x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 me mm) end;
        [st_eq| lia| lia| lia| exact FTV| exact FTB| exact CS| exact CE| exact MI| exact MU| exact WM| exact K].
    - assert (cnt = 0%nat) as -> by lia. cbn [ms_copy_init] in K.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _) end;
        [st_eq| exact FTB| exact CS| exact CE| exact MI| exact MU| exact WM].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Time Qed.
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

  Definition WCF : list (Z * Z) := [(A1, A1 + ARR1_SIZE); (p + 1320, p + 2344)]%Z.
  Definition WCB : list (Z * Z) := [(A1, A1 + ARR1_SIZE); (p + 296, p + 1320)]%Z.

  (* [comment removed for export] *)
  Lemma S0_cfwd : forall (f : nat) (j ss : Z) (a1 a2 bd cs : zarr)
      (x0 x4 x5 x6 x7 x8 x13 x14 x15 x17 x18 x20 x22 x23 x24 x25 x27 x28 x29 x30 : word) (me m : word -> option byte),
    (0 <= ss < 256)%Z -> (j < zget cs ss)%Z ->
    (forall k, let '(r, jk) := ms_copy_fwd k a1 cs a2 bd n ss j in fwdF a2 bd n ss (fst r) (snd r) jk) ->
    (let '(r, jF) := ms_copy_fwd f a1 cs a2 bd n ss j in zget (snd r) ss <= jF)%Z ->
    zbok a1 -> zbok a2 -> zbok bd -> pr n a1 0 (n - 1) ->
    u8arr s0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr s0segs m A2 (zb8 a2 ARR2_SIZE) ->
    u8arr s0segs m (p + 2344) (zb8 bd 256) -> u32arr s0segs m (p + 1320) (zw32 cs 256) -> mem_inv s0segs m ->
    munch WCF me m -> wmono s0segs me m ->
    (forall m' (a1' cs' : zarr) (jF : Z) (x12' x13' x14' x15' : word),
      ms_copy_fwd f a1 cs a2 bd n ss j = (a1', cs', jF) ->
      zbok a1' -> pr n a1' 0 (n - 1) -> (forall c, 0 <= c < 256 -> 0 <= zget cs' c <= n)%Z ->
      u8arr s0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 a2 ARR2_SIZE) ->
      u8arr s0segs m' (p + 2344) (zb8 bd 256) -> u32arr s0segs m' (p + 1320) (zw32 cs' 256) -> mem_inv s0segs m' ->
      munch WCF me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (mkR x0 (Z_to_bv 64 p) gp tp x4 x5 x6 x7 x8
                            (Z_to_bv 64 (zget cs' ss)) (Z_to_bv 64 (p + 1320 + 4 * ss)) (Z_to_bv 64 jF) x12' x13' x14' x15' (Z_to_bv 64 (p + 1320))
                            x17 x18 (Z_to_bv 64 A2) x20 (Z_to_bv 64 n) x22 x23 x24 x25 (Z_to_bv 64 A1) x27 x28 x29 x30)
                       F (Z_to_bv 64 0x1a3a4) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR x0 (Z_to_bv 64 p) gp tp x4 x5 x6 x7 x8
                          (Z_to_bv 64 (zget cs ss)) (Z_to_bv 64 (p + 1320 + 4 * ss)) (Z_to_bv 64 j) (Z_to_bv 64 (A1 + 4 * j)) x13 x14 x15 (Z_to_bv 64 (p + 1320))
                          x17 x18 (Z_to_bv 64 A2) x20 (Z_to_bv 64 n) x22 x23 x24 x25 (Z_to_bv 64 A1) x27 x28 x29 x30)
                     F (Z_to_bv 64 0x1a344) fc None m (seg_rom s0segs)).
  Proof.
    induction f as [|f IH].
    { intros. exfalso. cbn [ms_copy_fwd fst snd] in H2. lia. }
    intros j ss a1 a2 bd cs x0 x4 x5 x6 x7 x8 x13 x14 x15 x17 x18 x20 x22 x23 x24 x25 x27 x28 x29 x30 me m
           Hss Hj FWF FIN A1OK A2OK BDOK PR AR1 AR2 BD CS MI MU WM K.
    msenv_open XOK. pose proof XSEP as SP. unfold msenv_sep, apartm in SP. cps_destruct SP as (AP12 & AP1F & AP2F & _).
    unfold WCF in *.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2.
    pose proof (zb8_length bd 256 ltac:(lia)) as Lbd. pose proof (zw32_length cs 256 ltac:(lia)) as Lcs.
    pose proof (FWF 0%nat) as F0. cbn [ms_copy_fwd fst snd] in F0. destruct F0 as [CSR F0]. destruct (F0 Hj) as [Hjn F0c]. clear F0.
    pose proof (CSR ss ltac:(lia)) as Css.
    rewrite ms_copy_fwd_S in FIN, K. replace (j <? zget cs ss) with true in FIN, K by (symmetry; apply Z.ltb_lt; lia).
    cbv zeta in FIN. cbv zeta in K. unfold kwrap in FIN, K, F0c.
    pose proof (PR j ltac:(lia)) as Pj. set (pj := rd32 a1 j) in *.
    (* [comment removed for export] *)
    rdptr AR1 A1OK j. fold pj.
    wstep. wstep. wstep. rewrite (sign_sel (pj + -1) n) by lia.
    set (sel := (if (pj + -1 <? 0)%Z then n else 0%Z)).
    set (kk := (if (pj - 1 <? 0)%Z then (pj - 1 + n)%Z else (pj - 1)%Z)) in *.
    assert (SEL : ((pj = 0)%Z /\ sel = n /\ kk = (n - 1)%Z) \/ ((1 <= pj)%Z /\ sel = 0%Z /\ kk = (pj - 1)%Z))
      by (subst sel kk; destruct (Z.ltb_spec (pj + -1) 0); destruct (Z.ltb_spec (pj - 1) 0); lia).
    clearbody sel.
    wstep. replace (sel + (pj + -1))%Z with kk by lia.
    assert (Hkk : (0 <= kk < n)%Z) by lia.
    (* [comment removed for export] *)
    wstep. rdblk AR2 A2OK kk. unfold rd8 in FIN, K, F0c. set (c1 := zget a2 kk) in *.
    wstep. wstep. wstep. rdblk BD BDOK c1.
    wstep; if_cases Kb; zify_cond_z Kb.
    - (* [comment removed for export] *)
      replace (zget bd c1 =? 0) with false in FIN, K by (symmetry; apply Z.eqb_neq; lia).
      (* [comment removed for export] *)
      wstep. wstep. wstep; if_cases Kc; zify_cond_z Kc.
      + lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          enter_with (IH (j + 1)%Z ss a1 a2 bd cs x0 x4 x5 x6 x7 x8 _ _ _ x17 x18 x20 x22 x23 x24 x25 x27 x28 x29 x30 me mm) end;
          [st_eq| lia| lia| | exact FIN| exact A1OK| exact A2OK| exact BDOK| exact PR| exact AR1| exact AR2| exact BD| exact CS| exact MI| exact MU| exact WM| exact K].
        intros k. pose proof (FWF (S k)) as Fk. rewrite ms_copy_fwd_S in Fk. replace (j <? zget cs ss) with true in Fk by (symmetry; apply Z.ltb_lt; lia).
        cbv zeta in Fk. unfold kwrap in Fk. fold pj in Fk. fold kk in Fk. unfold rd8 in Fk. fold c1 in Fk.
        replace (zget bd c1 =? 0) with false in Fk by (symmetry; apply Z.eqb_neq; lia). exact Fk.
      + rewrite ms_copy_fwd_stop in K by lia.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm a1 cs (j + 1)%Z _ _ _ _) end;
          [st_eq| reflexivity| exact A1OK| exact PR| exact CSR| exact AR1| exact AR2| exact BD| exact CS| exact MI| exact MU| exact WM].
    - (* [comment removed for export] *)
      replace (zget bd c1 =? 0) with true in FIN, K by (symmetry; apply Z.eqb_eq; lia). specialize (F0c ltac:(lia)).
      pose proof (CSR c1 ltac:(lia)) as Cc1.
      wstep. wstep. rd32_at CS c1.
      wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (u32arr_store_ok s0segs mm (p + 1320) _ c1 _ CS ltac:(rewrite zw32_length_nat; lia) eq_refl) as SO1 end.
      wstep. zw32_store_at CS c1 (zget cs c1 + 1)%Z (apply unsigned_lit_mod32).
      pose proof (FWF 1%nat) as F1. rewrite ms_copy_fwd_S in F1. replace (j <? zget cs ss) with true in F1 by (symmetry; apply Z.ltb_lt; lia).
      cbv zeta in F1. unfold kwrap in F1. fold pj in F1. fold kk in F1. unfold rd8 in F1. fold c1 in F1.
      replace (zget bd c1 =? 0) with true in F1 by (symmetry; apply Z.eqb_eq; lia). cbn [ms_copy_fwd fst snd] in F1. destruct F1 as [CSR1 _].
      pose proof (CSR1 ss ltac:(lia)) as Css1.
      rd32_at CS ss.
      wstep. wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (SO2 : store_ok s0segs mm (wa (A1 + 4 * zget cs c1)) 4 = true)
          by (eapply (u8arr_storeN_ok s0segs _ A1 _ (4 * zget cs c1) 4 _ AR1); [lia| rewrite zb8_length_nat; lia| unfold wa; f_equal; lia]) end.
      wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ _) _) =>
        pose proof (zb8_write4 s0segs mm A1 a1 ARR1_SIZE (zget cs c1) (Z_to_bv 64 kk) AR1 ltac:(lia) ltac:(lia)) as AR1w end.
      clear AR1. store_done. rename AR1w into AR1. rewrite (unsigned_lit kk) in AR1 by lia.
      assert (OK1 : zbok (wr32 a1 (zget cs c1) kk)) by (apply zbok_wr32; exact A1OK).
      assert (PR1 : pr n (wr32 a1 (zget cs c1) kk) 0 (n - 1)) by (apply pr_wr32; [lia| exact PR| lia]).
      (* [comment removed for export] *)
      wstep. wstep. wstep; if_cases Kc; zify_cond_z Kc.
      + lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          enter_with (IH (j + 1)%Z ss (wr32 a1 (zget cs c1) kk) a2 bd (zset cs c1 (zget cs c1 + 1)) x0 x4 x5 x6 x7 x8 _ _ _ x17 x18 x20 x22 x23 x24 x25 x27 x28 x29 x30 me mm) end;
          [st_eq| lia| lia| | exact FIN| exact OK1| exact A2OK| exact BDOK| exact PR1| exact AR1| exact AR2| exact BD| exact CS| exact MI| exact MU| exact WM| exact K].
        intros k. pose proof (FWF (S k)) as Fk. rewrite ms_copy_fwd_S in Fk. replace (j <? zget cs ss) with true in Fk by (symmetry; apply Z.ltb_lt; lia).
        cbv zeta in Fk. unfold kwrap in Fk. fold pj in Fk. fold kk in Fk. unfold rd8 in Fk. fold c1 in Fk.
        replace (zget bd c1 =? 0) with true in Fk by (symmetry; apply Z.eqb_eq; lia). exact Fk.
      + rewrite ms_copy_fwd_stop in K by lia.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ (j + 1)%Z _ _ _ _) end;
          [st_eq| reflexivity| exact OK1| exact PR1| exact CSR1| exact AR1| exact AR2| exact BD| exact CS| exact MI| exact MU| exact WM].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Time Qed.

  (* [comment removed for export] *)
  Lemma S0_cbwd : forall (f : nat) (j ss : Z) (a1 a2 bd ce : zarr)
      (x0 x4 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x20 x22 x23 x24 x25 x27 x28 x29 x30 : word) (me m : word -> option byte),
    (0 <= ss < 256)%Z -> (zget ce ss < j)%Z ->
    (forall k, let '(r, jk) := ms_copy_bwd k a1 ce a2 bd n ss j in bwdF a2 bd n ss (fst r) (snd r) jk) ->
    (let '(r, jF) := ms_copy_bwd f a1 ce a2 bd n ss j in jF <= zget (snd r) ss)%Z ->
    zbok a1 -> zbok a2 -> zbok bd -> pr n a1 0 (n - 1) ->
    u8arr s0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr s0segs m A2 (zb8 a2 ARR2_SIZE) ->
    u8arr s0segs m (p + 2344) (zb8 bd 256) -> u32arr s0segs m (p + 296) (zw32 ce 256) -> mem_inv s0segs m ->
    munch WCB me m -> wmono s0segs me m ->
    (forall m' (a1' ce' : zarr) (jF : Z) (x13' x14' x15' x16' : word),
      ms_copy_bwd f a1 ce a2 bd n ss j = (a1', ce', jF) ->
      zbok a1' -> pr n a1' 0 (n - 1) -> (forall c, 0 <= c < 256 -> -1 <= zget ce' c < n)%Z ->
      u8arr s0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 a2 ARR2_SIZE) ->
      u8arr s0segs m' (p + 2344) (zb8 bd 256) -> u32arr s0segs m' (p + 296) (zw32 ce' 256) -> mem_inv s0segs m' ->
      munch WCB me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (mkR x0 (Z_to_bv 64 p) gp tp x4 x5 x6 x7 x8
                            x9 (Z_to_bv 64 (p + 296 + 4 * ss)) (Z_to_bv 64 (zget ce' ss)) (Z_to_bv 64 jF) x13' x14' x15' x16'
                            x17 x18 (Z_to_bv 64 A2) x20 (Z_to_bv 64 n) x22 x23 x24 x25 (Z_to_bv 64 A1) x27 x28 x29 x30)
                       F (Z_to_bv 64 0x1a440) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR x0 (Z_to_bv 64 p) gp tp x4 x5 x6 x7 x8
                          x9 (Z_to_bv 64 (p + 296 + 4 * ss)) (Z_to_bv 64 (zget ce ss)) (Z_to_bv 64 j) (Z_to_bv 64 (A1 + 4 * j)) x14 x15 x16
                          x17 x18 (Z_to_bv 64 A2) x20 (Z_to_bv 64 n) x22 x23 x24 x25 (Z_to_bv 64 A1) x27 x28 x29 x30)
                     F (Z_to_bv 64 0x1a3dc) fc None m (seg_rom s0segs)).
  Proof.
    induction f as [|f IH].
    { intros. exfalso. cbn [ms_copy_bwd fst snd] in H2. lia. }
    intros j ss a1 a2 bd ce x0 x4 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x20 x22 x23 x24 x25 x27 x28 x29 x30 me m
           Hss Hj BWF FIN A1OK A2OK BDOK PR AR1 AR2 BD CE MI MU WM K.
    msenv_open XOK. pose proof XSEP as SP. unfold msenv_sep, apartm in SP. cps_destruct SP as (AP12 & AP1F & AP2F & _).
    unfold WCB in *.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2.
    pose proof (zb8_length bd 256 ltac:(lia)) as Lbd. pose proof (zw32_length ce 256 ltac:(lia)) as Lce.
    pose proof (BWF 0%nat) as F0. cbn [ms_copy_bwd fst snd] in F0. destruct F0 as [CER F0]. destruct (F0 Hj) as [Hjn F0c]. clear F0.
    pose proof (CER ss ltac:(lia)) as Css.
    rewrite ms_copy_bwd_S in FIN, K. replace (zget ce ss <? j) with true in FIN, K by (symmetry; apply Z.ltb_lt; lia).
    cbv zeta in FIN. cbv zeta in K. unfold kwrap in FIN, K, F0c.
    pose proof (PR j ltac:(lia)) as Pj. set (pj := rd32 a1 j) in *.
    (* [comment removed for export] *)
    rdptr AR1 A1OK j. fold pj.
    wstep. wstep. wstep. rewrite (sign_sel (pj + -1) n) by lia.
    set (sel := (if (pj + -1 <? 0)%Z then n else 0%Z)).
    set (kk := (if (pj - 1 <? 0)%Z then (pj - 1 + n)%Z else (pj - 1)%Z)) in *.
    assert (SEL : ((pj = 0)%Z /\ sel = n /\ kk = (n - 1)%Z) \/ ((1 <= pj)%Z /\ sel = 0%Z /\ kk = (pj - 1)%Z))
      by (subst sel kk; destruct (Z.ltb_spec (pj + -1) 0); destruct (Z.ltb_spec (pj - 1) 0); lia).
    clearbody sel.
    wstep. replace (sel + (pj + -1))%Z with kk by lia.
    assert (Hkk : (0 <= kk < n)%Z) by lia.
    (* [comment removed for export] *)
    wstep. rdblk AR2 A2OK kk. unfold rd8 in FIN, K, F0c. set (c1 := zget a2 kk) in *.
    wstep. wstep. wstep. rdblk BD BDOK c1.
    wstep; if_cases Kb; zify_cond_z Kb.
    - replace (zget bd c1 =? 0) with false in FIN, K by (symmetry; apply Z.eqb_neq; lia).
      (* [comment removed for export] *)
      wstep. wstep. wstep; if_cases Kc; zify_cond_z Kc.
      + lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          enter_with (IH (j - 1)%Z ss a1 a2 bd ce x0 x4 x5 x6 x7 x8 x9 _ _ _ x17 x18 x20 x22 x23 x24 x25 x27 x28 x29 x30 me mm) end;
          [st_eq| lia| lia| | exact FIN| exact A1OK| exact A2OK| exact BDOK| exact PR| exact AR1| exact AR2| exact BD| exact CE| exact MI| exact MU| exact WM| exact K].
        intros k. pose proof (BWF (S k)) as Fk. rewrite ms_copy_bwd_S in Fk. replace (zget ce ss <? j) with true in Fk by (symmetry; apply Z.ltb_lt; lia).
        cbv zeta in Fk. unfold kwrap in Fk. fold pj in Fk. fold kk in Fk. unfold rd8 in Fk. fold c1 in Fk.
        replace (zget bd c1 =? 0) with false in Fk by (symmetry; apply Z.eqb_neq; lia). exact Fk.
      + rewrite ms_copy_bwd_stop in K by lia.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm a1 ce (j - 1)%Z _ _ _ _) end;
          [st_eq| reflexivity| exact A1OK| exact PR| exact CER| exact AR1| exact AR2| exact BD| exact CE| exact MI| exact MU| exact WM].
    - (* [comment removed for export] *)
      replace (zget bd c1 =? 0) with true in FIN, K by (symmetry; apply Z.eqb_eq; lia). specialize (F0c ltac:(lia)).
      pose proof (CER c1 ltac:(lia)) as Cc1.
      wstep. wstep. wstep. rd32_at CE c1.
      wstep. wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (u32arr_store_ok s0segs mm (p + 296) _ c1 _ CE ltac:(rewrite zw32_length_nat; lia) eq_refl) as SO1 end.
      wstep. zw32_store_at CE c1 (zget ce c1 - 1)%Z (rewrite unsigned_lit_mod32; reflexivity).
      pose proof (BWF 1%nat) as F1. rewrite ms_copy_bwd_S in F1. replace (zget ce ss <? j) with true in F1 by (symmetry; apply Z.ltb_lt; lia).
      cbv zeta in F1. unfold kwrap in F1. fold pj in F1. fold kk in F1. unfold rd8 in F1. fold c1 in F1.
      replace (zget bd c1 =? 0) with true in F1 by (symmetry; apply Z.eqb_eq; lia). cbn [ms_copy_bwd fst snd] in F1. destruct F1 as [CER1 _].
      pose proof (CER1 ss ltac:(lia)) as Css1.
      wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (SO2 : store_ok s0segs mm (wa (A1 + 4 * zget ce c1)) 4 = true)
          by (eapply (u8arr_storeN_ok s0segs _ A1 _ (4 * zget ce c1) 4 _ AR1); [lia| rewrite zb8_length_nat; lia| unfold wa; f_equal; lia]) end.
      wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ _) _) =>
        pose proof (zb8_write4 s0segs mm A1 a1 ARR1_SIZE (zget ce c1) (Z_to_bv 64 kk) AR1 ltac:(lia) ltac:(lia)) as AR1w end.
      clear AR1. store_done. rename AR1w into AR1. rewrite (unsigned_lit kk) in AR1 by lia.
      assert (OK1 : zbok (wr32 a1 (zget ce c1) kk)) by (apply zbok_wr32; exact A1OK).
      assert (PR1 : pr n (wr32 a1 (zget ce c1) kk) 0 (n - 1)) by (apply pr_wr32; [lia| exact PR| lia]).
      rd32_at CE ss.
      (* [comment removed for export] *)
      wstep. wstep. wstep; if_cases Kc; zify_cond_z Kc.
      + lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          enter_with (IH (j - 1)%Z ss (wr32 a1 (zget ce c1) kk) a2 bd (zset ce c1 (zget ce c1 - 1)) x0 x4 x5 x6 x7 x8 x9 _ _ _ x17 x18 x20 x22 x23 x24 x25 x27 x28 x29 x30 me mm) end;
          [st_eq| lia| lia| | exact FIN| exact OK1| exact A2OK| exact BDOK| exact PR1| exact AR1| exact AR2| exact BD| exact CE| exact MI| exact MU| exact WM| exact K].
        intros k. pose proof (BWF (S k)) as Fk. rewrite ms_copy_bwd_S in Fk. replace (zget ce ss <? j) with true in Fk by (symmetry; apply Z.ltb_lt; lia).
        cbv zeta in Fk. unfold kwrap in Fk. fold pj in Fk. fold kk in Fk. unfold rd8 in Fk. fold c1 in Fk.
        replace (zget bd c1 =? 0) with true in Fk by (symmetry; apply Z.eqb_eq; lia). exact Fk.
      + rewrite ms_copy_bwd_stop in K by lia.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ (j - 1)%Z _ _ _ _) end;
          [st_eq| reflexivity| exact OK1| exact PR1| exact CER1| exact AR1| exact AR2| exact BD| exact CE| exact MI| exact MU| exact WM].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Time Qed.

  (* [comment removed for export] *)
  Lemma S0_mark : forall (cnt : nat) (j ss : Z) (ft : zarr)
      (x0 x4 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 : word) (me m : word -> option byte),
    Z.of_nat cnt = (256 - j)%Z -> (0 <= j < 256)%Z -> (0 <= ss < 256)%Z -> ftv ft ->
    u32arr s0segs m FT (zw32 ft 65537) -> mem_inv s0segs m -> munch [(FT, FT + 262148)]%Z me m -> wmono s0segs me m ->
    (forall m' (x9' : word), let ft' := ms_mark cnt ft ss j in ftv ft' ->
      u32arr s0segs m' FT (zw32 ft' 65537) -> mem_inv s0segs m' -> munch [(FT, FT + 262148)]%Z me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (mkR x0 (Z_to_bv 64 p) gp tp x4 x5 x6 x7 (Z_to_bv 64 FT)
                            x9' (Z_to_bv 64 2097152) x11 x12 x13 x14 x15 x16
                            (Z_to_bv 64 (FT + 262144 + 4 * ss)) (Z_to_bv 64 (FT + 262144 + 4 * ss)) x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30)
                       F (Z_to_bv 64 0x1a47c) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR x0 (Z_to_bv 64 p) gp tp x4 x5 x6 x7 (Z_to_bv 64 FT)
                          x9 (Z_to_bv 64 2097152) x11 x12 x13 x14 x15 x16
                          (Z_to_bv 64 (FT + 262144 + 4 * ss)) (Z_to_bv 64 (FT + 4 * ss + 1024 * j)) x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30)
                     F (Z_to_bv 64 0x1a468) fc None m (seg_rom s0segs)).
  Proof.
    induction cnt as [|cnt IH]; [intros; exfalso; lia|].
    intros j ss ft x0 x4 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 me m Hcnt Hj Hss FTV FTB MI MU WM K.
    msenv_open XOK. pose proof (zw32_length ft 65537 ltac:(lia)) as Lft.
    rewrite ms_mark_S in K. cbv zeta in K. rewrite shl8 in K.
    pose proof (FTV (256 * j + ss)%Z ltac:(lia)) as V0.
    (* [comment removed for export] *)
    rd32_at FTB (256 * j + ss)%Z.
    wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok s0segs mm FT _ (256 * j + ss)%Z _ FTB ltac:(rewrite zw32_length_nat; lia) eq_refl) as SO end.
    wstep. zw32_store_at FTB (256 * j + ss)%Z (Z.lor (zget ft (256 * j + ss)) SETMASK) (unfold SETMASK; apply unsigned_lit_mod32).
    pose proof (ftv_mark1 ft (256 * j + ss)%Z FTV ltac:(lia)) as FTV1.
    wstep. wstep; if_cases Kc; zify_cond_z Kc.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (IH (j + 1)%Z ss _ x0 x4 x5 x6 x7 _ x11 x12 x13 x14 x15 x16 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 me mm) end;
        [st_eq| lia| lia| lia| exact FTV1| exact FTB| exact MI| exact MU| exact WM| exact K].
    - assert (cnt = 0%nat) as -> by lia. cbn [ms_mark] in K.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _) end; [st_eq| exact FTV1| exact FTB| exact MI| exact MU| exact WM].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Time Qed.

  Definition W2 : list (Z * Z) := [(A1, A1 + ARR1_SIZE); (FT, FT + 262148); (p + 296, p + 2600)]%Z.

  (* [comment removed for export] *)
  Lemma S0_step2 : forall (i ss : Z) (a1 a2 ft bd cs ce : zarr) (w48 w56 w64 : word)
      (x0 x4 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x24 x27 x28 x29 x30 : word) (me m : word -> option byte),
    let ci := ms_copy_init 256 cs ce ft ss 0 in let cs0 := fst ci in let ce0 := snd ci in
    let j0 := clearmask (zget ft (Z.shiftl ss 8)) in
    let rf := ms_copy_fwd (S (Z.to_nat n)) a1 cs0 a2 bd n ss j0 in let a1F := fst (fst rf) in let csF := snd (fst rf) in
    let j1 := (clearmask (zget ft (Z.shiftl (ss + 1) 8)) - 1)%Z in
    let rb := ms_copy_bwd (S (Z.to_nat n)) a1F ce0 a2 bd n ss j1 in let a1B := fst (fst rb) in let ceB := snd (fst rb) in
    let ftm := ms_mark 256 ft ss 0 in
    (0 <= i <= 255)%Z -> (0 <= ss < 256)%Z ->
    zget bd ss = 0%Z -> ftv ft ->
    (forall k, let '(r, jk) := ms_copy_fwd k a1 cs0 a2 bd n ss j0 in fwdF a2 bd n ss (fst r) (snd r) jk) ->
    (zget csF ss <= snd rf)%Z ->
    (forall k, let '(r, jk) := ms_copy_bwd k a1F ce0 a2 bd n ss j1 in bwdF a2 bd n ss (fst r) (snd r) jk) ->
    (snd rb <= zget ceB ss)%Z ->
    (zget csF ss - 1 = zget ceB ss \/ (zget csF ss = 0 /\ zget ceB ss = n - 1))%Z ->
    zbok a1 -> zbok a2 -> zbok bd -> pr n a1 0 (n - 1) ->
    u8arr s0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr s0segs m A2 (zb8 a2 ARR2_SIZE) -> u32arr s0segs m FT (zw32 ft 65537) ->
    u8arr s0segs m (p + 2344) (zb8 bd 256) -> u32arr s0segs m (p + 1320) (zw32 cs 256) -> u32arr s0segs m (p + 296) (zw32 ce 256) ->
    rw_cells s0segs m (p + 16) (sca_cells X (mkSCA w48 w56 w64 (Z_to_bv 64 (256 * ss)) (Z_to_bv 64 ss) (Z_to_bv 64 (FT + 1024 * ss)))) ->
    mem_inv s0segs m -> munch W2 me m -> wmono s0segs me m ->
    (forall (last : bool) m' (x4' x5' x6' x9' x11' x12' x13' x14' x15' x16' x27' x28' x29' x30' : word),
      last = (i =? 255)%Z ->
      zbok a1B -> pr n a1B 0 (n - 1) -> ftv ftm ->
      (forall c, 0 <= c < 256 -> 0 <= zget csF c <= n)%Z -> (forall c, 0 <= c < 256 -> -1 <= zget ceB c < n)%Z ->
      u8arr s0segs m' A1 (zb8 a1B ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 a2 ARR2_SIZE) -> u32arr s0segs m' FT (zw32 ftm 65537) ->
      u8arr s0segs m' (p + 2344) (zb8 (zset bd ss 1) 256) -> u32arr s0segs m' (p + 1320) (zw32 csF 256) -> u32arr s0segs m' (p + 296) (zw32 ceB 256) ->
      rw_cells s0segs m' (p + 16) (sca_cells X (mkSCA w48 w56 w64 (Z_to_bv 64 (256 * ss)) (Z_to_bv 64 ss) (Z_to_bv 64 (FT + 1024 * ss)))) ->
      mem_inv s0segs m' -> munch W2 me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (mkR x0 (Z_to_bv 64 p) gp tp x4' x5' x6' (Z_to_bv 64 (p + 2344 + ss)) (Z_to_bv 64 FT)
                            (Z_to_bv 64 255) (Z_to_bv 64 2097152) x11' x12' x13' x14' x15' x16'
                            (Z_to_bv 64 (FT + 262144 + 4 * ss)) (Z_to_bv 64 (FT + 262144 + 4 * ss)) (Z_to_bv 64 A2) (Z_to_bv 64 (FT + 4 * (256 * ss + 256))) (Z_to_bv 64 n)
                            (Z_to_bv 64 0) (Z_to_bv 64 (p + 3624)) x24 (Z_to_bv 64 i) (Z_to_bv 64 A1) x27' x28' x29' x30')
                       F (Z_to_bv 64 (if last then 0x1a6a8 else 0x1a48c)) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR x0 (Z_to_bv 64 p) gp tp x4 x5 x6 x7 (Z_to_bv 64 FT)
                          x9 x10 x11 x12 x13 x14 x15 x16
                          x17 x18 (Z_to_bv 64 A2) (Z_to_bv 64 (p + 1320)) (Z_to_bv 64 n) (Z_to_bv 64 0) (Z_to_bv 64 (p + 3624))
                          x24 (Z_to_bv 64 i) (Z_to_bv 64 A1) x27 x28 x29 x30)
                     F (Z_to_bv 64 0x1a2b8) fc None m (seg_rom s0segs)).
  Proof.
    intros i ss a1 a2 ft bd cs ce w48 w56 w64 x0 x4 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x24 x27 x28 x29 x30 me m.
    intros ci cs0 ce0 j0 rf a1F csF j1 rb a1B ceB ftm Hi Hss BD0 FTV FWF FWfin BWF BWfin A1007 A1OK A2OK BDOK PR AR1 AR2 FTB BD CS CE SCA MI MU WM K.
    msenv_open XOK. pose proof XSEP as SP. unfold msenv_sep, apartm in SP. cps_destruct SP as (AP12 & AP1F & AP2F & _).
    unfold W2 in *.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2.
    pose proof (zb8_length bd 256 ltac:(lia)) as Lbd. pose proof (zw32_length cs 256 ltac:(lia)) as Lcs. pose proof (zw32_length ce 256 ltac:(lia)) as Lce.
    pose proof (zw32_length ft 65537 ltac:(lia)) as Lft.
    open_sc_in SCA.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. rdblk BD BDOK ss. rewrite BD0.
    wstep; if_cases Kz; zify_cond_z Kz; [| exfalso; lia]. clear Kz.
    (* [comment removed for export] *)
    do 7 wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (S0_cinit 256 0 ss ft cs ce _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm mm) end;
      [st_eq| lia| lia| lia| exact FTV| exact FTB| exact CS| exact CE| exact MI| apply munch_refl| apply wmono_refl|].
    intros m1 z12 z13. cbv zeta. intros FTB1 CS1 CE1 MI1 MU1 WM1. fold ci in CS1, CE1. fold cs0 in CS1. fold ce0 in CE1.
    clear FTB CS CE MI. lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename m into m0; rename mm into m end.
    transport_after_call s0segs m0 m MU1 WM1. clear MU1 WM1.
    pose proof (zw32_length cs0 256 ltac:(lia)) as Lcs0. pose proof (zw32_length ce0 256 ltac:(lia)) as Lce0.
    pose proof (FWF 0%nat) as F0. cbn [ms_copy_fwd fst snd] in F0. destruct F0 as [CSR _]. pose proof (CSR ss ltac:(lia)) as Css.
    pose proof (FTV (256 * ss)%Z ltac:(lia)) as Vs0.
    assert (Hj0 : j0 = clearmask (zget ft (256 * ss))) by (subst j0; rewrite shl8; reflexivity).
    pose proof (clearmask_bounds (zget ft (256 * ss)) ltac:(lia)) as J0r. rewrite <- Hj0 in J0r.
    (* [comment removed for export] *)
    wstep. rd32_at FTB1 (256 * ss)%Z. wstep. wstep. rd32_at CS1 ss. wstep. rewrite land_CM64, <- Hj0 by lia.
    (* [comment removed for export] *)
    assert (JOINB : forall m' (a1'' ce' : zarr) (jB : Z) (y4 y5 y6 y12 y13 y14 y15 y16 y27 y28 y29 y30 : word),
      rb = (a1'', ce', jB) -> zbok a1'' -> pr n a1'' 0 (n - 1) ->
      (forall c, 0 <= c < 256 -> 0 <= zget csF c <= n)%Z -> (forall c, 0 <= c < 256 -> -1 <= zget ce' c < n)%Z ->
      u8arr s0segs m' A1 (zb8 a1'' ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 a2 ARR2_SIZE) -> u32arr s0segs m' FT (zw32 ft 65537) ->
      u8arr s0segs m' (p + 2344) (zb8 bd 256) -> u32arr s0segs m' (p + 1320) (zw32 csF 256) -> u32arr s0segs m' (p + 296) (zw32 ce' 256) ->
      rw_cells s0segs m' (p + 16) (sca_cells X (mkSCA w48 w56 w64 (Z_to_bv 64 (256 * ss)) (Z_to_bv 64 ss) (Z_to_bv 64 (FT + 1024 * ss)))) ->
      mem_inv s0segs m' -> munch [(A1, A1 + ARR1_SIZE); (FT, FT + 262148); (p + 296, p + 2600)]%Z me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (mkR x0 (Z_to_bv 64 p) gp tp y4 y5 y6 (Z_to_bv 64 (p + 2344 + ss)) (Z_to_bv 64 FT)
                            (Z_to_bv 64 (zget csF ss)) (Z_to_bv 64 (p + 296 + ss * 4)) (Z_to_bv 64 (zget ce' ss)) y12 y13 y14 y15 y16
                            (Z_to_bv 64 (ss * 4)) (Z_to_bv 64 (FT + ss * 4)) (Z_to_bv 64 A2) (Z_to_bv 64 (FT + (256 * ss + 256) * 4)) (Z_to_bv 64 n)
                            (Z_to_bv 64 0) (Z_to_bv 64 (p + 3624)) x24 (Z_to_bv 64 i) (Z_to_bv 64 A1) y27 y28 y29 y30)
                       F (Z_to_bv 64 0x1a440) fc None m' (seg_rom s0segs))).
    { intros m' a1'' ce' jB y4 y5 y6 y12 y13 y14 y15 y16 y27 y28 y29 y30 Erb OK'' PR'' CSR' CER' AR1' AR2' FTB' BD' CS' CE' SCA' MI' MU' WM'.
      clear AR1 AR2 FTB1 BD CS1 CE1 SCA MI1 MU WM. open_sc_in SCA'.
      assert (EceB : ceB = ce') by (subst ceB; rewrite Erb; reflexivity). rewrite EceB in A1007.
      pose proof (CSR' ss ltac:(lia)) as Cs1. pose proof (CER' ss ltac:(lia)) as Ce1.
      assert (EaB : a1B = a1'') by (subst a1B; rewrite Erb; reflexivity).
      (* [comment removed for export] *)
      assert (OKK : forall m'' (z9 z10 : word), m'' = m' ->
        evt s0segs Q (MS (mkR x0 (Z_to_bv 64 p) gp tp y4 y5 y6 (Z_to_bv 64 (p + 2344 + ss)) (Z_to_bv 64 FT)
                            z9 z10 (Z_to_bv 64 (zget ce' ss)) y12 y13 y14 y15 y16
                            (Z_to_bv 64 (ss * 4)) (Z_to_bv 64 (FT + ss * 4)) (Z_to_bv 64 A2) (Z_to_bv 64 (FT + (256 * ss + 256) * 4)) (Z_to_bv 64 n)
                            (Z_to_bv 64 0) (Z_to_bv 64 (p + 3624)) x24 (Z_to_bv 64 i) (Z_to_bv 64 A1) y27 y28 y29 y30)
                       F (Z_to_bv 64 0x1a45c) fc None m'' (seg_rom s0segs))).
      { intros m'' z9 z10 ->.
        (* [comment removed for export] *)
        wstep. wstep. wstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          enter_with (S0_mark 256 0 ss ft _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm mm) end;
          [st_eq| lia| lia| lia| exact FTV| exact FTB'| exact MI'| apply munch_refl| apply wmono_refl|].
        intros m2 v9. cbv zeta. intros FTVm FTB2 MI2 MU2 WM2. fold ftm in FTVm, FTB2.
        clear FTB' MI'. transport_after_call s0segs m' m2 MU2 WM2. clear MU2 WM2.
        (* [comment removed for export] *)
        wstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          assert (SOb : store_ok s0segs mm (wa (p + 2344 + ss)) 1 = true)
            by (eapply (u8arr_storeN_ok s0segs _ (p + 2344) _ ss 1 _ BD'); [lia| rewrite zb8_length_nat; lia| unfold wa; f_equal; lia]) end.
        wstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm ?ad ?bs) _) =>
          change bs with (le1 (Z_to_bv 64 1));
          pose proof (zb8_write1 s0segs mm (p + 2344) bd 256 ss (Z_to_bv 64 1) BD' ltac:(lia)) as BDw end.
        clear BD'. store_done. rename BDw into BD'. change (wr8 bd ss (bv_unsigned (Z_to_bv 64 1))) with (zset bd ss 1) in BD'.
        wstep. wstep; if_cases Kl; zify_cond_z Kl.
        - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K true mm _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
            [st_eq| symmetry; apply Z.eqb_eq; lia| rewrite EaB; exact OK''| rewrite EaB; exact PR''| exact FTVm| exact CSR'| rewrite EceB; exact CER'
            | rewrite EaB; exact AR1'| exact AR2'| exact FTB2| exact BD'| exact CS'| rewrite EceB; exact CE'| exact SCA'| exact MI2| exact MU'| exact WM'].
        - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K false mm _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
            [st_eq| symmetry; apply Z.eqb_neq; lia| rewrite EaB; exact OK''| rewrite EaB; exact PR''| exact FTVm| exact CSR'| rewrite EceB; exact CER'
            | rewrite EaB; exact AR1'| exact AR2'| exact FTB2| exact BD'| exact CS'| rewrite EceB; exact CE'| exact SCA'| exact MI2| exact MU'| exact WM']. }
      wstep. wstep; if_cases K7.
      { enter_with (OKK m' _ _); [st_eq| reflexivity]. }
      lazymatch type of K7 with ?c = false => first [apply bveqb_lit_false in K7 | idtac "K7?"] | _ => idtac end.
      wstep; if_cases K8; zify_cond_z K8; [exfalso; Z.div_mod_to_equations; lia|].
      wstep. wstep; if_cases K9; [| first [apply bveqb_lit_false in K9 | idtac "K9?"]; exfalso; Z.div_mod_to_equations; lia].
      enter_with (OKK m' _ _); [st_eq| reflexivity]. }
    (* [comment removed for export] *)
    assert (JOINF : forall m' (a1' cs' : zarr) (jF : Z) (y12 y13 y14 y15 : word),
      rf = (a1', cs', jF) -> zbok a1' -> pr n a1' 0 (n - 1) -> (forall c, 0 <= c < 256 -> 0 <= zget cs' c <= n)%Z ->
      u8arr s0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 a2 ARR2_SIZE) -> u32arr s0segs m' FT (zw32 ft 65537) ->
      u8arr s0segs m' (p + 2344) (zb8 bd 256) -> u32arr s0segs m' (p + 1320) (zw32 cs' 256) -> u32arr s0segs m' (p + 296) (zw32 ce0 256) ->
      rw_cells s0segs m' (p + 16) (sca_cells X (mkSCA w48 w56 w64 (Z_to_bv 64 (256 * ss)) (Z_to_bv 64 ss) (Z_to_bv 64 (FT + 1024 * ss)))) ->
      mem_inv s0segs m' -> munch [(A1, A1 + ARR1_SIZE); (FT, FT + 262148); (p + 296, p + 2600)]%Z me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (mkR x0 (Z_to_bv 64 p) gp tp x4 x5 x6 (Z_to_bv 64 (p + 2344 + ss)) (Z_to_bv 64 FT)
                            (Z_to_bv 64 (zget cs' ss)) (Z_to_bv 64 (p + 1320 + 4 * ss)) (Z_to_bv 64 jF) y12 y13 y14 y15 (Z_to_bv 64 (p + 1320))
                            (Z_to_bv 64 (ss * 4)) (Z_to_bv 64 (FT + ss * 4)) (Z_to_bv 64 A2) (Z_to_bv 64 (p + 1320)) (Z_to_bv 64 n)
                            (Z_to_bv 64 0) (Z_to_bv 64 (p + 3624)) x24 (Z_to_bv 64 i) (Z_to_bv 64 A1) x27 x28 x29 x30)
                       F (Z_to_bv 64 0x1a3a4) fc None m' (seg_rom s0segs))).
    { intros m' a1' cs' jF y12 y13 y14 y15 Erf OK' PR' CSR' AR1' AR2' FTB' BD' CS' CE' SCA' MI' MU' WM'.
      clear AR1 AR2 FTB1 BD CS1 CE1 SCA MI1 MU WM. open_sc_in SCA'.
      assert (EaF : a1F = a1') by (subst a1F; rewrite Erf; reflexivity). assert (EcF : csF = cs') by (subst csF; rewrite Erf; reflexivity).
      pose proof (BWF 0%nat) as B0. cbn [ms_copy_bwd fst snd] in B0. destruct B0 as [CER _]. pose proof (CER ss ltac:(lia)) as Ces.
      pose proof (FTV (256 * ss + 256)%Z ltac:(lia)) as Vs1.
      assert (Hj1 : j1 = (clearmask (zget ft (256 * ss + 256)) - 1)%Z) by (subst j1; rewrite shl8; f_equal; f_equal; f_equal; lia).
      pose proof (clearmask_bounds (zget ft (256 * ss + 256)) ltac:(lia)) as J1r.
      (* [comment removed for export] *)
      wstep. wstep. wstep. wstep. rd32_at FTB' (256 * ss + 256)%Z. wstep. wstep. rd32_at CE' ss. wstep. wstep. rewrite land_CM64 by lia. wstep.
      replace (clearmask (zget ft (256 * ss + 256)) + -1)%Z with j1 by lia.
      wstep; if_cases Kb; zify_cond_z Kb.
      - (* [comment removed for export] *)
        assert (Erb : rb = (a1', ce0, j1)) by (subst rb; rewrite EaF; apply ms_copy_bwd_stop; lia).
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (JOINB mm a1' ce0 j1 _ _ _ _ _ _ _ _ _ _ _ _) end;
          [st_eq| exact Erb| exact OK'| exact PR'| rewrite EcF; exact CSR'| exact CER| exact AR1'| exact AR2'| exact FTB'| exact BD'| rewrite EcF; exact CS'| exact CE'| exact SCA'| exact MI'| exact MU'| exact WM'].
        rewrite EcF. reflexivity.
      - (* [comment removed for export] *)
        wstep. wstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mq end.
        enter_with (S0_cbwd (S (Z.to_nat n)) j1 ss a1' a2 bd ce0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mq mq);
          [st_eq| lia| lia| rewrite <- EaF; exact BWF| rewrite <- EaF; fold rb; subst ceB; destruct rb as [[? ?] ?]; exact BWfin
          | exact OK'| exact A2OK| exact BDOK| exact PR'| exact AR1'| exact AR2'| exact BD'| exact CE'| exact MI'| apply munch_refl| apply wmono_refl|].
        intros m2 a1'' ce' jB u13 u14 u15 u16 Erb2 OK'' PR'' CER'' AR1'' AR2'' BD'' CE'' MI2 MU2 WM2.
        clear AR1' AR2' BD' CE' MI'. unfold WCB in MU2. transport_after_call s0segs mq m2 MU2 WM2. clear MU2 WM2.
        assert (Erb : rb = (a1'', ce', jB)) by (subst rb; rewrite EaF; exact Erb2).
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (JOINB mm a1'' ce' jB _ _ _ _ _ _ _ _ _ _ _ _) end;
          [st_eq| exact Erb| exact OK''| exact PR''| rewrite EcF; exact CSR'| exact CER''| exact AR1''| exact AR2''| exact FTB'| exact BD''| rewrite EcF; exact CS'| exact CE''| exact SCA'| exact MI2| exact MU'| exact WM'].
        rewrite EcF. reflexivity. }
    clear JOINB.
    wstep; if_cases Kf; zify_cond_z Kf.
    - (* [comment removed for export] *)
      assert (Erf : rf = (a1, cs0, j0)) by (subst rf; apply ms_copy_fwd_stop; lia).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (JOINF mm a1 cs0 j0 _ _ _ _) end;
        [st_eq| exact Erf| exact A1OK| exact PR| exact CSR| exact AR1| exact AR2| exact FTB1| exact BD| exact CS1| exact CE1| exact SCA| exact MI1| exact MU| exact WM].
    - (* [comment removed for export] *)
      wstep. wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mq end.
      enter_with (S0_cfwd (S (Z.to_nat n)) j0 ss a1 a2 bd cs0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mq mq);
        [st_eq| lia| lia| exact FWF| fold rf; subst csF; destruct rf as [[? ?] ?]; exact FWfin
        | exact A1OK| exact A2OK| exact BDOK| exact PR| exact AR1| exact AR2| exact BD| exact CS1| exact MI1| apply munch_refl| apply wmono_refl|].
      intros m2 a1' cs' jF u12 u13 u14 u15 Erf OK' PR' CSR' AR1' AR2' BD' CS' MI2 MU2 WM2.
      clear AR1 AR2 BD CS1 MI1. unfold WCF in MU2. transport_after_call s0segs mq m2 MU2 WM2. clear MU2 WM2.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (JOINF mm a1' cs' jF _ _ _ _) end;
        [st_eq| exact Erf| exact OK'| exact PR'| exact CSR'| exact AR1'| exact AR2'| exact FTB1| exact BD'| exact CS'| exact CE1| exact SCA| exact MI2| exact MU| exact WM].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Time Qed.
End S0MS.

End ACeilS1.
