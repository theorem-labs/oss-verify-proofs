(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsS0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCStream BzCState BzCMtf BzArrD BzCRebuildF CmpMem CmpCut CmpCut0 CmpCutSM CmpCutSmA CmpCutSmA0 CmpCutSmB CmpCutSmB0 CmpCutSmC CmpCutSmC0 BzCFactsSmA BzCFactsGm BzCFactsSd BzCFactsSd2 CmpFsKit0 CmpHmKit CmpSmKit CmpSmKit2 CmpSmKit20 S0_cmp_asg.
From Stdlib Require Lia. Unset Lia Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCut6.   (* [comment removed for export] *)
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
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
Ltac lin16 H := lazymatch type of H with (?x mod 16 = 0)%Z =>
  let E := fresh "E16" in pose proof (Z.div_mod x 16 ltac:(lia)) as E; rewrite H, Z.add_0_r in E; clear H;
  let q := fresh "q16" in set (q := (x / 16)%Z) in E; clearbody q; rename E into H end.
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
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section SC3.
  Variables (cx : cctx) (e0 : est) (Q : machine_state -> Prop).
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Hypothesis CX : cctx_ok cx. Hypothesis SEP : cctx_sep cx.
  Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation J := (c_J cx).
  Notation usp := (bv_unsigned sp).
  Notation A := (sm_alpha e0). Notation nG := (smA_ng e0).
  Hypothesis HA : (3 <= A <= 258)%Z. Hypothesis HNG : (2 <= nG <= 6)%Z.
  Ltac simpl_arr_sizes ::= CmpFast.sas10.   (* [comment removed for export] *)
  Local Ltac simpl_sizes ::=
    rewrite ?length_app;
    cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ smB_slots3 smC_hi3];
    rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1, ?length_app; cbn [length].
  Ltac openCX :=
    let XA20 := ident:(XA20) in let XA21 := ident:(XA21) in let XF0 := ident:(XF0) in let XF1 := ident:(XF1) in let Xb0 := ident:(Xb0) in let Xb1 := ident:(Xb1) in let Xf0 := ident:(Xf0) in let Xf1 := ident:(Xf1) in let MA2 := ident:(MA2) in let MF := ident:(MF) in let Mb := ident:(Mb) in let Mf := ident:(Mf) in let LJb := ident:(LJb) in let H := fresh "CXL" in pose proof CX as H; bz_ceil; bz_params; unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in H; cbv zeta in H;
    cps_destruct H as (?XE0 & ?XE1 & ?XA10 & ?XA11 & ?XA20 & ?XA21 & ?XF0 & ?XF1 & ?Xb0 & ?Xb1 & ?Xf0 & ?Xf1 & ?ME & ?MA1 & ?MA2 & ?MF & ?Mb & ?Mf & ?LJ & ?LJb);
    clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 MA2 MF Mb Mf LJb;
    let S := fresh "SP" in pose proof SEP as S; unfold cctx_sep, apart, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE in S; cbv zeta in S;
    destruct S as (?AEA1 & _).
  Ltac bzu :=
    repeat match goal with
    | |- context [Z.shiftr ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftr_div a k) by lia
    | |- context [Z.shiftl ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftl_mul a k) by lia
    | |- context [Z.modulo ?x 18446744073709551616] => rewrite (Z.mod_small x 18446744073709551616) by lia
    | |- context [bv_wrap 32 ?x] => change (bv_wrap 32 x) with (Z.modulo x 4294967296)
    | |- context [Z.modulo ?x 4294967296] => rewrite (Z.mod_small x 4294967296) by lia
    | |- context [bv_swrap 32 ?x] => rewrite (swrap32_id x) by lia
    | |- context [bv_signed (Z_to_bv 64 ?x)] => rewrite (signed_lit_small x) by lia
    | |- context [bv_unsigned (Z_to_bv 64 ?x)] => rewrite (unsigned_lit x) by lia
    | |- context [sx32 (Z_to_bv 64 ?x)] => rewrite (sx32_of_Z x) by lia
    | |- context [Z.lxor ?x 9223372036854775808] => rewrite (lxor_sign_small x) by (change (2^63)%Z with 9223372036854775808%Z; lia)
    | |- context [Z.lxor ?x 18446744073709551615] => rewrite (zb_lxor_ones x) by (change (2^64)%Z with 18446744073709551616%Z; lia)
    end; zb_fold_lits.
  Ltac lstep := zstep; bzu.

  (* [comment removed for export] *)
  Notation MR ra nSel t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 :=
    (mkR ra sp gp tp (Z_to_bv 64 A) t1 t2 (Z_to_bv 64 E) (Z_to_bv 64 nSel) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6).

  (* [comment removed for export] *)
  Definition PAGREE (pm p : zarr) : Prop := forall k, (1 <= k < nG)%Z -> zdef pm k = true /\ zget pm k = zget p k.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_sc_posinit : forall (n : nat) (i : Z) (pm : zarr) (i16 : list byte) (m mf : word -> option byte) (nSel : Z)
      (ra t1 t2 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    (i + Z.of_nat n = nG)%Z -> (0 <= i)%Z -> (1 <= n)%nat ->
    u8arr s0segs m (usp + 872) (ovb pm i16 16) ->
    mem_inv s0segs m -> munch [(usp + 872, usp + 888)]%Z mf m -> wmono s0segs mf m ->
    (CEIL <= usp)%Z -> (usp + 1008 <= 18446744073709551616)%Z ->
    (forall m' (a2 : word),
      u8arr s0segs m' (usp + 872) (ovb (yy_init n pm i) i16 16) ->
      mem_inv s0segs m' -> munch [(usp + 872, usp + 888)]%Z mf m' -> wmono s0segs mf m' ->
      evt s0segs Q (MS (MR ra nSel t1 t2 (Z_to_bv 64 nG) (Z_to_bv 64 (usp + 872)) a2 (Z_to_bv 64 nG) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x1732c) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (MR ra nSel t1 t2 (Z_to_bv 64 i) (Z_to_bv 64 (usp + 872)) a2 (Z_to_bv 64 nG) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x1731c) fc None m (seg_rom s0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros i pm i16 m mf nSel ra t1 t2 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Hi Hi0 Hn POS MI MU WM CE SPB K.
    openCX. try lin16 ME. try lin16 MA1. try lin16 MA2. try lin16 MF. try lin16 Mb. try lin16 Mf. bz_ceil; bz_params; unfold CEIL in CE. pose proof (ovb_length_nat pm i16 16) as LP.
    rewrite yy_init_S in K.
    (* [comment removed for export] *)
    lstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u8arr_store_ok s0segs mm (usp + 872) _ i _ POS ltac:(rewrite ovb_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO end.
    lstep. store_addr (usp + 872 + i)%Z. ovb_store1 POS i.
    replace (wr8 pm i (bv_unsigned (Z_to_bv 64 i))) with (zset pm i i) in POS by (unfold wr8; rewrite unsigned_lit by lia; rewrite Z.mod_small by lia; reflexivity).
    (* [comment removed for export] *)
    lstep. lstep; if_cases Ke; zify_cond_z Ke.
    - enter_with (IH (i + 1)%Z _ i16 _ mf nSel); [st_eq| lia| lia| lia| exact POS| assumption| exact MU| exact WM| bz_ceil; bz_params; unfold CEIL; lia| exact SPB| exact K].
    - assert (n = 0)%nat by lia. subst n. cbn [yy_init] in K.
      enter_with (K _ _); [st_eq| exact POS| assumption| exact MU| exact WM].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_sc_search : forall (n : nat) (j mm : Z) (pos0 pm : zarr) (i16 : list byte) (m mf : word -> option byte) (nSel ll : Z)
      (ra t1 t2 a0 a1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    (mm - j = Z.of_nat n)%Z -> (0 <= j <= mm)%Z -> (mm < nG)%Z ->
    (forall k, 0 <= k < nG -> 0 <= zget pos0 k < nG)%Z -> (0 <= ll < nG)%Z ->
    zget pos0 mm = ll -> (forall k, j <= k < mm -> zget pos0 k <> ll)%Z ->
    (forall k, 1 <= k <= j -> zdef pm k = true /\ zget pm k = zget pos0 (k - 1))%Z ->
    (forall k, j < k < nG -> zdef pm k = true /\ zget pm k = zget pos0 k)%Z ->
    u8arr s0segs m (usp + 872) (ovb pm i16 16) ->
    mem_inv s0segs m -> munch [(usp + 872, usp + 888)]%Z mf m -> wmono s0segs mf m ->
    (CEIL <= usp)%Z -> (usp + 1008 <= 18446744073709551616)%Z ->
    (forall m' pm' (a6 a7 : word),
      (forall k, 1 <= k <= mm -> zdef pm' k = true /\ zget pm' k = zget pos0 (k - 1))%Z ->
      (forall k, mm < k < nG -> zdef pm' k = true /\ zget pm' k = zget pos0 k)%Z ->
      u8arr s0segs m' (usp + 872) (ovb pm' i16 16) ->
      mem_inv s0segs m' -> munch [(usp + 872, usp + 888)]%Z mf m' -> wmono s0segs mf m' ->
      evt s0segs Q (MS (MR ra nSel t1 t2 a0 a1 (Z_to_bv 64 ll) (Z_to_bv 64 (usp + 873)) (Z_to_bv 64 mm) (Z_to_bv 64 ll) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x17380) fc None m' (seg_rom s0segs))) ->
    (j < mm)%Z ->
    evt s0segs Q (MS (MR ra nSel t1 t2 a0 a1 (Z_to_bv 64 (zget pos0 j)) (Z_to_bv 64 (usp + 873)) (Z_to_bv 64 j) (Z_to_bv 64 ll) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x17364) fc None m (seg_rom s0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros j mm pos0 pm i16 m mf nSel ll ra t1 t2 a0 a1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Hn Hj Hmm PB Hll Em NOT SH REST POS MI MU WM CE SPB K LT.
    openCX. try lin16 ME. try lin16 MA1. try lin16 MA2. try lin16 MF. try lin16 Mb. try lin16 Mf. bz_ceil; bz_params; unfold CEIL in CE. pose proof (ovb_length_nat pm i16 16) as LP.
    pose proof (PB j ltac:(lia)) as Pj. pose proof (PB (j + 1)%Z ltac:(lia)) as Pj1.
    destruct (REST (j + 1)%Z ltac:(lia)) as [D1 V1].
    (* [comment removed for export] *)
    lstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm0 _) =>
      pose proof (ovb_read1 s0segs mm0 (usp + 872) pm i16 16 (j + 1) _ POS ltac:(lia) D1 ltac:(unfold wa; f_equal; lia)) as RD end.
    lstep. clear RD. rewrite V1. cbv beta. rewrite (unsigned_lit8 (zget pos0 (j + 1))) by lia.
    (* [comment removed for export] *)
    lstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm0 _) =>
      pose proof (u8arr_store_ok s0segs mm0 (usp + 872) _ (j + 1) _ POS ltac:(rewrite ovb_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO end.
    lstep. store_addr (usp + 872 + (j + 1))%Z. ovb_store1 POS (j + 1)%Z.
    replace (wr8 pm (j + 1) (bv_unsigned (Z_to_bv 64 (zget pos0 j)))) with (zset pm (j + 1) (zget pos0 j)) in POS by (unfold wr8; rewrite unsigned_lit by lia; rewrite Z.mod_small by lia; reflexivity).
    (* [comment removed for export] *)
    lstep. lstep; if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      assert (j + 1 < mm)%Z by (destruct (Z.eq_dec (j + 1) mm) as [EQ|]; [exfalso; rewrite <- EQ in Em; lia| lia]).
      enter_with (IH (j + 1)%Z mm pos0 _ i16 _ mf nSel ll);
        [st_eq| lia| lia| lia| exact PB| lia| exact Em| intros k Hk; apply NOT; lia| | | exact POS| assumption| exact MU| exact WM| bz_ceil; bz_params; unfold CEIL; lia| exact SPB| exact K| lia].
      + intros k Hk. destruct (Z.eq_dec k (j + 1)) as [->|NK].
        * rewrite zdef_zset_same, zget_zset_same. split; [reflexivity| f_equal; lia].
        * rewrite zdef_zset_other, zget_zset_other by lia. apply SH. lia.
      + intros k Hk. rewrite zdef_zset_other, zget_zset_other by lia. apply REST. lia.
    - (* [comment removed for export] *)
      assert (EJ : (j + 1 = mm)%Z) by (destruct (Z.eq_dec (j + 1) mm) as [|NE]; [assumption| exfalso; apply (NOT (j + 1)%Z); lia]).
      lstep.
      enter_with (K _ _ _ _);
        [st_eq| | | exact POS| assumption| exact MU| exact WM].
      + intros k Hk. destruct (Z.eq_dec k (j + 1)) as [->|NK].
        * rewrite zdef_zset_same, zget_zset_same. split; [reflexivity| f_equal; lia].
        * rewrite zdef_zset_other, zget_zset_other by lia. apply SH. lia.
      + intros k Hk. rewrite zdef_zset_other, zget_zset_other by lia. apply REST. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_sc_mtf : forall (n : nat) (i : Z) (P pm sel sm : zarr) (i16 : list byte) (m mf : word -> option byte) (nSel : Z) (w584 : word)
      (ra t1 t2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    (i + Z.of_nat n = nSel)%Z -> (0 <= i)%Z -> (1 <= n)%nat -> (nSel <= 18002)%Z ->
    PP nG P -> PAGREE pm P ->
    (forall k, 0 <= k < nSel -> zdef sel k = true /\ 0 <= zget sel k < nG)%Z ->
    u8arr s0segs m (E + 1704) (ovb sel (jseg J 1704 18002) 18002) ->
    u8arr s0segs m (E + 19706) (ovb sm (jseg J 19706 18002) 18002) ->
    u8arr s0segs m (usp + 872) (ovb pm i16 16) ->
    rw_cells s0segs m (usp + 576) [C8 (Z_to_bv 64 999999999); C8 w584; C8 (Z_to_bv 64 (flag6 nG)); C8 (Z_to_bv 64 (E + 1704)); C8 (Z_to_bv 64 (e_nInUse e0))] ->
    mem_inv s0segs m -> munch [(E + 19706, E + 37708); (usp + 872, usp + 888)]%Z mf m -> wmono s0segs mf m ->
    (CEIL <= usp)%Z -> (usp + 1008 <= 18446744073709551616)%Z ->
    (forall m' pm' (a2 a4 a5 a6 a7 : word),
      let r := sm_selmtf n P sel sm i in
      PP nG (fst r) -> PAGREE pm' (fst r) ->
      u8arr s0segs m' (E + 1704) (ovb sel (jseg J 1704 18002) 18002) ->
      u8arr s0segs m' (E + 19706) (ovb (snd r) (jseg J 19706 18002) 18002) ->
      u8arr s0segs m' (usp + 872) (ovb pm' i16 16) ->
      rw_cells s0segs m' (usp + 576) [C8 (Z_to_bv 64 999999999); C8 w584; C8 (Z_to_bv 64 (flag6 nG)); C8 (Z_to_bv 64 (E + 1704)); C8 (Z_to_bv 64 (e_nInUse e0))] ->
      mem_inv s0segs m' -> munch [(E + 19706, E + 37708); (usp + 872, usp + 888)]%Z mf m' -> wmono s0segs mf m' ->
      evt s0segs Q (MS (MR ra nSel t1 t2 (Z_to_bv 64 nSel) (Z_to_bv 64 (E + 19706)) a2 (Z_to_bv 64 (usp + 873)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x17390) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (MR ra nSel t1 t2 (Z_to_bv 64 i) (Z_to_bv 64 (E + 19706)) (Z_to_bv 64 (zget P 0)) (Z_to_bv 64 (usp + 873)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x17348) fc None m (seg_rom s0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros i P pm sel sm i16 m mf nSel w584 ra t1 t2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           Hi Hi0 Hn HnS PPH PAG SELOK SEL SELM POS C576 MI MU WM CE SPB K.
    openCX. try lin16 ME. try lin16 MA1. try lin16 MA2. try lin16 MF. try lin16 Mb. try lin16 Mf. bz_ceil; bz_params; unfold CEIL in CE.
    pose proof (jseg_length J 1704 18002 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ4. pose proof (ovb_length_nat sel (jseg J 1704 18002) 18002) as LS4.
    pose proof (jseg_length J 19706 18002 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ5. pose proof (ovb_length_nat sm (jseg J 19706 18002) 18002) as LS5.
    pose proof (ovb_length_nat pm i16 16) as LP.
    destruct (SELOK i ltac:(lia)) as [Dsi Rsi]. destruct PPH as [P1 P2]. pose proof (P1 0%Z ltac:(lia)) as P00.
    (* [comment removed for export] *)
    cbn [sm_selmtf] in K.
    cps_destruct (first_occ P (zget sel i) nG (P2 _ Rsi)) as (mm & Hmm & Emm & NOT).
    pose proof (pos_search_spec 8 P P (zget sel i) 0 mm nG ltac:(lia) ltac:(lia) ltac:(lia) Emm ltac:(intros k Hk; apply NOT; lia)
                  ltac:(intros; lia) ltac:(intros; reflexivity)) as SR. cbv zeta in SR.
    destruct (sm_pos_search 8 P (zget sel i) (zget P 0) 0) as [[P' tmp] jj]. cbn [fst snd] in SR. cps_destruct SR as (Ej & Et & SH & REST). subst jj tmp.
    set (P1n := zset P' 0 (zget sel i)) in K.
    assert (PP' : PP nG P1n).
    { split.
      - intros k Hk. subst P1n. rewrite zget_zset. destruct (Z.eqb_spec k 0) as [->|NK]; [lia|].
        destruct (Z.le_gt_cases k mm) as [L|L]; [rewrite SH by lia; apply P1; lia| rewrite REST by lia; apply P1; lia].
      - intros v Hv. cps_destruct (P2 v Hv) as (k & Hk & Ek). subst P1n.
        destruct (Z.lt_trichotomy k mm) as [L|[->|L]].
        + exists (k + 1)%Z. split; [lia|]. rewrite zget_zset_other by lia. rewrite SH by lia. replace (k + 1 - 1)%Z with k by lia. exact Ek.
        + exists 0%Z. split; [lia|]. rewrite zget_zset_same. rewrite <- Ek. symmetry. exact Emm.
        + exists k. split; [lia|]. rewrite zget_zset_other by lia. rewrite REST by lia. exact Ek. }
    (* [comment removed for export] *)
    lstep. lstep.
    pose proof (ovb_read1 s0segs m (E + 1704) sel (jseg J 1704 18002) 18002 i _ SEL ltac:(lia) Dsi ltac:(unfold wa; f_equal; lia)) as RD.
    lstep. clear RD. cbv beta. rewrite (unsigned_lit8 (zget sel i)) by lia.
    (* [comment removed for export] *)
    assert (K8 : forall m1 pm1 (xa6 xa7 : word),
      (forall k, 1 <= k <= mm -> zdef pm1 k = true /\ zget pm1 k = zget P (k - 1))%Z ->
      (forall k, mm < k < nG -> zdef pm1 k = true /\ zget pm1 k = zget P k)%Z ->
      u8arr s0segs m1 (usp + 872) (ovb pm1 i16 16) ->
      u8arr s0segs m1 (E + 19706) (ovb sm (jseg J 19706 18002) 18002) ->
      rw_cells s0segs m1 (usp + 576) [C8 (Z_to_bv 64 999999999); C8 w584; C8 (Z_to_bv 64 (flag6 nG)); C8 (Z_to_bv 64 (E + 1704)); C8 (Z_to_bv 64 (e_nInUse e0))] ->
      u8arr s0segs m1 (E + 1704) (ovb sel (jseg J 1704 18002) 18002) ->
      mem_inv s0segs m1 -> munch [(E + 19706, E + 37708); (usp + 872, usp + 888)]%Z mf m1 -> wmono s0segs mf m1 ->
      evt s0segs Q (MS (MR ra nSel t1 t2 (Z_to_bv 64 i) (Z_to_bv 64 (E + 19706)) (Z_to_bv 64 (zget sel i)) (Z_to_bv 64 (usp + 873)) (Z_to_bv 64 mm) (Z_to_bv 64 (zget sel i)) xa6 xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x17380) fc None m1 (seg_rom s0segs))).
    { intros m1 pm1 xa6 xa7 SH1 REST1 POS1 SELM1 C5761 SEL1 MI1 MU1 WM1.
      pose proof (ovb_length_nat pm1 i16 16) as LP1.
      (* [comment removed for export] *)
      lstep. lstep.
      pose proof (u8arr_store_ok s0segs m1 (E + 19706) _ i _ SELM1 ltac:(rewrite ovb_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO.
      lstep. store_addr (E + 19706 + i)%Z. ovb_store1 SELM1 i.
      replace (wr8 sm i (bv_unsigned (Z_to_bv 64 mm))) with (zset sm i mm) in SELM1 by (unfold wr8; rewrite unsigned_lit by lia; rewrite Z.mod_small by lia; reflexivity).
      assert (PAG1 : PAGREE pm1 P1n).
      { intros k Hk. subst P1n. rewrite zget_zset_other by lia.
        destruct (Z.le_gt_cases k mm) as [L|L]; [rewrite SH by lia; apply SH1; lia| rewrite REST by lia; apply REST1; lia]. }
      (* [comment removed for export] *)
      lstep; if_cases Ke; zify_cond_z Ke.
      - enter_with (IH (i + 1)%Z P1n pm1 sel (zset sm i mm) i16 _ mf nSel w584);
          [st_eq| lia| lia| lia| lia| exact PP'| exact PAG1| exact SELOK| exact SEL1| exact SELM1| exact POS1| exact C5761| assumption| exact MU1| exact WM1| bz_ceil; bz_params; unfold CEIL; lia| exact SPB| exact K].
        subst P1n. rewrite zget_zset_same. reflexivity.
      - assert (n = 0)%nat by lia. subst n. cbn [sm_selmtf] in K.
        enter_with (K _ pm1 _ _ _ _ _); [st_eq| exact PP'| exact PAG1| exact SEL1| exact SELM1| exact POS1| exact C5761| assumption| exact MU1| exact WM1]. }
    (* [comment removed for export] *)
    lstep; if_cases Kq; zify_cond_z Kq.
    - (* [comment removed for export] *)
      assert (M1 : (0 < mm)%Z) by (destruct (Z.eq_dec mm 0) as [EQ|]; [exfalso; rewrite EQ in Emm; lia| lia]).
      lstep.
      enter_with (S0_sc_search (Z.to_nat mm) 0 mm P pm i16 m m nSel (zget sel i));
        [st_eq| lia| lia| lia| exact P1| lia| exact Emm| intros k Hk; apply NOT; lia| intros; lia| intros k Hk; apply PAG; lia
        | exact POS| exact MI| apply munch_refl| apply wmono_refl| bz_ceil; bz_params; unfold CEIL; lia| exact SPB| | lia].
      clear POS MI. intros m1 pm1 xa6 xa7 SH1 REST1 POS1 MI1 MU1 WM1.
      transport_after_call s0segs m m1 MU1 WM1. clear MU1 WM1.
      eapply (K8 m1 pm1); [exact SH1| exact REST1| exact POS1| exact SELM| exact C576| exact SEL| exact MI1| exact MU| exact WM].
    - (* [comment removed for export] *)
      assert (M0 : mm = 0%Z) by (destruct (Z.eq_dec mm 0) as [|NE]; [assumption| exfalso; apply (NOT 0%Z); lia]).
      lstep. lstep. subst mm.
      enter_with (K8 m pm _ _); [st_eq| intros; lia| intros k Hk; apply PAG; lia| exact POS| exact SELM| exact C576| exact SEL| exact MI| exact MU| exact WM].
  Qed.

  (* [comment removed for export] *)
  Notation CR ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t s6 s7 s8 t3 t4 t5 t6 :=
    (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 E) (Z_to_bv 64 t) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (E + 37708 + 258 * t)) (Z_to_bv 64 258) (Z_to_bv 64 (-1)) (Z_to_bv 64 3004)
         s6 s7 s8 (Z_to_bv 64 18) (Z_to_bv 64 (37708 + A)) (Z_to_bv 64 1032) t3 t4 t5 t6).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_sc_minmax : forall (n : nat) (v t mn mx : Z) (len : zarr) (m : word -> option byte)
      (ra t0 t1 t2 a2 a3 a4 a5 a6 a7 s6 t3 t4 t5 t6 : word),
    (v + Z.of_nat n = A)%Z -> (0 <= v)%Z -> (1 <= n)%nat -> (0 <= t < nG)%Z -> (0 <= mn <= 32)%Z -> (0 <= mx <= 17)%Z ->
    (forall tt vv, 0 <= tt < nG -> 0 <= vv < A -> zdef len (258 * tt + vv) = true /\ 1 <= zget len (258 * tt + vv) <= 17)%Z ->
    u8arr s0segs m (E + 37708) (ovb len (jseg J 37708 1548) 1548) ->
    (CEIL <= usp)%Z -> (usp + 1008 <= 18446744073709551616)%Z ->
    (forall (a2 : word), let r := sm_minmax n len t v mn mx in
      (0 <= fst r <= 32)%Z -> (0 <= snd r <= 17)%Z ->
      evt s0segs Q (MS (CR ra t0 t1 t2 (Z_to_bv 64 (E + 37708 + 258 * t + A)) (Z_to_bv 64 (E + 37708 + 258 * t + A)) a2 a3 a4 a5 a6 a7 t s6 (Z_to_bv 64 (snd r)) (Z_to_bv 64 (fst r)) t3 t4 t5 t6)
                       F (Z_to_bv 64 0x17418) fc None m (seg_rom s0segs))) ->
    evt s0segs Q (MS (CR ra t0 t1 t2 (Z_to_bv 64 (E + 37708 + 258 * t + A)) (Z_to_bv 64 (E + 37708 + 258 * t + v)) a2 a3 a4 a5 a6 a7 t s6 (Z_to_bv 64 mx) (Z_to_bv 64 mn) t3 t4 t5 t6)
                     F (Z_to_bv 64 0x173fc) fc None m (seg_rom s0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros v t mn mx len m ra t0 t1 t2 a2 a3 a4 a5 a6 a7 s6 t3 t4 t5 t6 Hv Hv0 Hn Ht Hmn Hmx LENF LEN CE SPB K.
    openCX. try lin16 ME. try lin16 MA1. try lin16 MA2. try lin16 MF. try lin16 Mb. try lin16 Mf. bz_ceil; bz_params; unfold CEIL in CE.
    pose proof (jseg_length J 37708 1548 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ6. pose proof (ovb_length_nat len (jseg J 37708 1548) 1548) as LL.
    destruct (LENF t v ltac:(lia) ltac:(lia)) as [Dl Rl].
    cbn [sm_minmax] in K. set (l := zget len (258 * t + v)) in *.
    (* [comment removed for export] *)
    pose proof (ovb_read1 s0segs m (E + 37708) len (jseg J 37708 1548) 1548 (258 * t + v) _ LEN ltac:(lia) Dl ltac:(unfold wa; f_equal; lia)) as RD.
    fold l in RD. lstep. clear RD. cbv beta. rewrite (unsigned_lit8 l) by lia.
    (* [comment removed for export] *)
    assert (STEP : forall (xs7 xs8 : word), xs7 = Z_to_bv 64 (if mx <? l then l else mx)%Z -> xs8 = Z_to_bv 64 (if l <? mn then l else mn)%Z ->
      evt s0segs Q (MS (CR ra t0 t1 t2 (Z_to_bv 64 (E + 37708 + 258 * t + A)) (Z_to_bv 64 (E + 37708 + 258 * t + v)) (Z_to_bv 64 l) a3 a4 a5 a6 a7 t s6 xs7 xs8 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x17410) fc None m (seg_rom s0segs))).
    { intros xs7 xs8 -> ->.
      lstep. lstep; if_cases Ke; zify_cond_z Ke.
      - enter_with (IH (v + 1)%Z t (if l <? mn then l else mn)%Z (if mx <? l then l else mx)%Z len m);
          [st_eq| lia| lia| lia| lia| destruct (Z.ltb_spec l mn); lia| destruct (Z.ltb_spec mx l); lia| exact LENF| exact LEN| bz_ceil; bz_params; unfold CEIL; lia| exact SPB| exact K].
      - assert (n = 0)%nat by lia. subst n. cbn [sm_minmax] in K.
        enter_with (K _); [st_eq| cbn [fst]; destruct (Z.ltb_spec l mn); lia| cbn [snd]; destruct (Z.ltb_spec mx l); lia]. }
    lstep; if_cases K1; zify_cond_z K1.
    - (* [comment removed for export] *)
      lstep; if_cases K2; zify_cond_z K2.
      + apply STEP; f_equal; [destruct (Z.ltb_spec mx l); lia| destruct (Z.ltb_spec l mn); lia].
      + lstep. apply STEP; f_equal; [destruct (Z.ltb_spec mx l); lia| destruct (Z.ltb_spec l mn); lia].
    - lstep. lstep; if_cases K2; zify_cond_z K2.
      + apply STEP; f_equal; [destruct (Z.ltb_spec mx l); lia| destruct (Z.ltb_spec l mn); lia].
      + lstep. apply STEP; f_equal; [destruct (Z.ltb_spec mx l); lia| destruct (Z.ltb_spec l mn); lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_sc_assign : forall (n t : nat) (code len : zarr) (nSel lo : Z) (m mf : word -> option byte) (sv w24 w56 : word)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 t3 t4 t5 t6 : word),
    (Z.of_nat t + Z.of_nat n = nG)%Z -> (1 <= n)%nat ->
    (forall tt vv, 0 <= tt < nG -> 0 <= vv < A -> zdef len (258 * tt + vv) = true /\ 1 <= zget len (258 * tt + vv) <= 17)%Z ->
    u8arr s0segs m (E + 37708) (ovb len (jseg J 37708 1548) 1548) ->
    u32arr s0segs m (E + 39256) (ovw code (jseg J 39256 6192) 1548) ->
    rw_cells s0segs m (usp + 8) (smB_slots3 cx e0 usp sv w24 w56) ->
    rw_cells s0segs m (usp + 560) (smC_hi3 cx e0 nSel) ->
    mem_inv s0segs m -> stk s0segs m lo usp -> (lo + 16 <= usp)%Z -> (CEIL <= lo)%Z ->
    munch [(E + 39256, E + 45448); (usp - 16, usp)]%Z mf m -> wmono s0segs mf m ->
    (usp + 1008 <= 18446744073709551616)%Z ->
    (forall m' (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 t3 t4 t5 t6 : word),
      u8arr s0segs m' (E + 37708) (ovb len (jseg J 37708 1548) 1548) ->
      u32arr s0segs m' (E + 39256) (ovw (sm_assign n code len A (Z.of_nat t)) (jseg J 39256 6192) 1548) ->
      rw_cells s0segs m' (usp + 8) (smB_slots3 cx e0 usp sv w24 w56) ->
      rw_cells s0segs m' (usp + 560) (smC_hi3 cx e0 nSel) ->
      mem_inv s0segs m' -> stk s0segs m' lo usp ->
      munch [(E + 39256, E + 45448); (usp - 16, usp)]%Z mf m' -> wmono s0segs mf m' ->
      evt s0segs Q (MS (CR ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 nG (Z_to_bv 64 nG) s7 s8 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x17474) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (CR ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z.of_nat t) s6 s7 s8 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x173dc) fc None m (seg_rom s0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros t code len nSel lo m mf sv w24 w56 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 t3 t4 t5 t6 Ht Hn LENF LEN CODE S8 HI MI ST STK CLO MU WM SPB K.
    openCX. try lin16 ME. try lin16 MA1. try lin16 MA2. try lin16 MF. try lin16 Mb. try lin16 Mf. bz_ceil; bz_params; unfold CEIL in CLO. assert (HAd : A = (e_nInUse e0 + 2)%Z) by reflexivity.
    pose proof (jseg_length J 37708 1548 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ6. pose proof (jseg_length J 39256 6192 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ7.
    unfold smB_slots3 in S8. cbv zeta in S8. unfold smC_hi3 in HI.
    cbn [sm_assign] in K.
    pose proof (sm_minmax_spec (Z.to_nat A) len (Z.of_nat t) 0 32 0 ltac:(lia) ltac:(lia)) as MM. cbv zeta in MM.
    destruct (sm_minmax (Z.to_nat A) len (Z.of_nat t) 0 32 0) as [mn mx] eqn:EMM. cbn [fst snd] in MM. cps_destruct MM as (M1 & M2 & M3 & M4).
    rewrite Z2Nat.id in M3, M4 by lia.
    destruct (M4 ltac:(intros j Hj; apply (proj2 (LENF (Z.of_nat t) j ltac:(lia) ltac:(lia))))) as [N1 N2].
    pose proof (M3 0%Z ltac:(lia)) as M30. pose proof (proj2 (LENF (Z.of_nat t) 0%Z ltac:(lia) ltac:(lia))) as L00.
    assert (MN : (1 <= mn <= 17)%Z) by lia. assert (MX : (1 <= mx <= 17)%Z) by lia.
    (* [comment removed for export] *)
    lstep. lstep. lstep; if_cases K0; zify_cond_z K0; [exfalso; revert K0; rewrite ?signed_lit by lia; lia|].
    lstep. lstep. lstep. lstep. lstep.
    enter_with (S0_sc_minmax (Z.to_nat A) 0 (Z.of_nat t) 32 0 len m);
      [st_eq| lia| lia| lia| lia| lia| lia| exact LENF| exact LEN| bz_ceil; bz_params; unfold CEIL; lia| exact SPB|].
    intros ya2. cbv zeta. rewrite EMM. cbn [fst snd]. intros _ _.
    (* [comment removed for export] *)
    lstep; if_cases K1; zify_cond_z K1; [| exfalso; lia].
    lstep. lstep; if_cases K2; zify_cond_z K2; [| exfalso; lia].
    (* [comment removed for export] *)
    lstep. lstep. lstep. lstep. lstep. lstep. lstep. lstep.
    pose proof S0_hbAssignCodes as HAS. unfold hbAssignCodes_spec in HAS. cbn [ci_segs ci_hbAssignCodes S0C] in HAS.
    eapply evt_cut.
    { eapply (HAS _ sp gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m (E + 39256)%Z (E + 37708)%Z (258 * Z.of_nat t)%Z (258 * Z.of_nat t)%Z mn mx A 1548%Z 1548%Z lo code len (jseg J 39256 6192) (jseg J 37708 1548));
        [ f_equal; lia | f_equal; lia | reflexivity | reflexivity | reflexivity
        | exact CODE | exact LEN | exact MI | exact ST | lia
        | lia | lia | lia | lia | lia | lia | lia
        | clear -ME; Z.div_mod_to_equations; lia | lia | bz_ceil; bz_params; unfold CEIL; lia | lia | bz_ceil; bz_params; unfold CEIL; lia
        | unfold apart; lia | lia | lia
        | intros i Hi; destruct (LENF (Z.of_nat t) i ltac:(lia) Hi) as [D R]; split; [exact D| apply M3; lia] ]. }
    clear CODE MI ST. unfold hbAssignCodes_post.
    intros ms' PO; destruct_exs PO. destruct PO as [EQ [MUc [WMc [MI2 [ST CODE]]]]]; subst ms'.
    lazymatch type of MUc with munch _ m ?m' => transport_after_call s0segs m m' MUc WMc; clear MUc WMc; try clear m end.
    lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    (* [comment removed for export] *)
    lstep. lstep. lstep. lstep; if_cases Ke; zify_cond_z Ke.
    - enter_with (IH (S t) _ len nSel lo _ mf sv w24 w56);
        [st_eq| lia| lia| exact LENF| exact LEN| exact CODE| unfold smB_slots3; cbv zeta; exact S8| unfold smC_hi3; exact HI| exact MI2| exact ST| lia| bz_ceil; bz_params; unfold CEIL; lia| assumption| assumption| exact SPB|].
      intros mm; intros *. replace (Z.of_nat (S t)) with (Z.of_nat t + 1)%Z by lia. apply K.
    - assert (n = 0)%nat by lia. subst n. cbn [sm_assign] in K.
      enter_with (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
        [st_eq| exact LEN| exact CODE| unfold smB_slots3; cbv zeta; exact S8| unfold smC_hi3; exact HI| exact MI2| exact ST| assumption| assumption].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_smC_body : forall (c0 f0 p0 h0 w0 q0 : zarr) (m : word -> option byte) (sv w24 w56 w584 : word) (J184 i16 : list byte) (lo : Z)
      (ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    let it := smB_it e0 c0 f0 h0 w0 q0 in let nSel := smB_nsel e0 c0 f0 h0 w0 q0 in
    sd_facts (est_C e0 c0 f0 p0 h0 w0 q0) nG nSel ->
    u8arr s0segs m (E + 1704) (ovb (it_sel it) (jseg J 1704 18002) 18002) ->
    u8arr s0segs m (E + 19706) (ovb (e_selectorMtf e0) (jseg J 19706 18002) 18002) ->
    u8arr s0segs m (E + 37708) (ovb (it_len it) (jseg J 37708 1548) 1548) ->
    u32arr s0segs m (E + 39256) (ovw (e_code e0) (jseg J 39256 6192) 1548) ->
    rw_cells s0segs m (usp + 8) (smB_slots3 cx e0 usp sv w24 w56) ->
    u8arr s0segs m (usp + 184) J184 -> Z.of_nat (length J184) = 392%Z ->
    rw_cells s0segs m (usp + 576) [C8 (Z_to_bv 64 999999999); C8 w584; C8 (Z_to_bv 64 (flag6 nG)); C8 (Z_to_bv 64 (E + 1704)); C8 (Z_to_bv 64 (e_nInUse e0))] ->
    u8arr s0segs m (usp + 872) i16 -> Z.of_nat (length i16) = 16%Z ->
    stk s0segs m lo usp -> (lo + 16 <= usp)%Z -> (CEIL <= lo)%Z -> mem_inv s0segs m -> (usp + 1008 <= 18446744073709551616)%Z ->
    (forall m' (J184' i16' : list byte) (ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
       u8arr s0segs m' (E + 1704) (ovb (it_sel it) (jseg J 1704 18002) 18002) ->
       u8arr s0segs m' (E + 19706) (ovb (snd (smC_pm e0 c0 f0 p0 h0 w0 q0)) (jseg J 19706 18002) 18002) ->
       u8arr s0segs m' (E + 37708) (ovb (it_len it) (jseg J 37708 1548) 1548) ->
       u32arr s0segs m' (E + 39256) (ovw (smC_code e0 c0 f0 h0 w0 q0) (jseg J 39256 6192) 1548) ->
       rw_cells s0segs m' (usp + 8) (smB_slots3 cx e0 usp sv w24 w56) ->
       u8arr s0segs m' (usp + 184) J184' -> Z.of_nat (length J184') = 376%Z ->
       rw_cells s0segs m' (usp + 560) (smC_hi3 cx e0 nSel) ->
       u8arr s0segs m' (usp + 872) i16' -> Z.of_nat (length i16') = 16%Z ->
       stk s0segs m' lo usp -> mem_inv s0segs m' -> munch (smC_W3 cx usp) m m' -> wmono s0segs m m' ->
       evt s0segs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 E) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 nG) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x17474) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 E) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 nSel) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x172f0) fc None m (seg_rom s0segs)).
  Proof.
    intros c0 f0 p0 h0 w0 q0 m sv w24 w56 w584 J184 i16 lo ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.
    cbv zeta. intros SDF SEL SELM LEN CODE S8 J184H L184 C576 I16 L16 ST STK CLO MI SPB K.
    openCX. try lin16 ME. try lin16 MA1. try lin16 MA2. try lin16 MF. try lin16 Mb. try lin16 Mf. bz_ceil; bz_params; unfold CEIL in CLO. assert (HAd : A = (e_nInUse e0 + 2)%Z) by reflexivity.
    set (it := smB_it e0 c0 f0 h0 w0 q0) in *. set (nSel := smB_nsel e0 c0 f0 h0 w0 q0) in *.
    pose proof SDF as SF. unfold sd_facts in SF. cbv zeta in SF.
    cbn [e_nInUse e_nMTF e_arr1 e_inUse e_selectorMtf e_selector e_len e_code est_C] in SF.
    cps_destruct SF as (FA & FG & FS & FM & F35 & FZB & FMV & FIU & FSM & FSEL & FLEN & FCODE & FCNT).
    change (e_nInUse e0 + 2)%Z with A in FA, FMV, FLEN, FCODE. fold it in FSEL, FLEN.
    unfold smB_slots3 in S8. cbv zeta in S8.
    pose proof (munch_refl (smC_W3 cx usp) m) as MU0. unfold smC_W3 in MU0. pose proof (wmono_refl s0segs m) as WM0.
    (* [comment removed for export] *)
    lstep. lstep. lstep. lstep; if_cases K0; zify_cond_z K0; [| exfalso; revert K0; rewrite ?signed_lit by lia; lia].
    lstep. lstep. lstep. lstep.
    (* [comment removed for export] *)
    pose proof (ovb_init s0segs m (usp + 872) 16 i16 ltac:(replace (Z.to_nat 16) with (length i16) by lia; exact (rw_cells_of_u8arr s0segs m _ i16 I16)) ltac:(lia)) as POS.
    enter_with (S0_sc_posinit (Z.to_nat nG) 0 znew i16 m m nSel);
      [st_eq| lia| lia| lia| exact POS| exact MI| apply munch_refl| apply wmono_refl| bz_ceil; bz_params; unfold CEIL; lia| exact SPB|].
    clear POS MI. intros m1 xa2 POS MI MU1 WM1.
    transport_after_call s0segs m m1 MU1 WM1. clear MU1 WM1.
    (* [comment removed for export] *)
    lstep; if_cases K1; zify_cond_z K1; [exfalso; revert K1; rewrite ?signed_lit by lia; lia|].
    lstep.
    assert (PD0 : zdef (yy_init (Z.to_nat nG) znew 0) 0 = true) by (rewrite yy_init_def; replace ((0 <=? 0) && (0 <? 0 + Z.of_nat (Z.to_nat nG)))%bool with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia); reflexivity).
    assert (PV0 : zget (yy_init (Z.to_nat nG) znew 0) 0 = 0%Z) by (rewrite yy_init_get; replace ((0 <=? 0) && (0 <? 0 + Z.of_nat (Z.to_nat nG)))%bool with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia); reflexivity).
    pose proof (ovb_read1 s0segs m1 (usp + 872) _ i16 16 0 _ POS ltac:(lia) PD0 ltac:(unfold wa; f_equal; lia)) as RD.
    lstep. clear RD. rewrite PV0. cbv beta. rewrite (unsigned_lit8 0) by lia.
    lstep. lstep. lstep. lstep.
    (* [comment removed for export] *)
    assert (PP0 : PP nG (yy_init (Z.to_nat nG) znew 0)) by (apply PP_init; lia).
    assert (PAG0 : PAGREE (yy_init (Z.to_nat nG) znew 0) (yy_init (Z.to_nat nG) p0 0)).
    { intros k Hk. rewrite yy_init_def, !yy_init_get.
      replace ((0 <=? k) && (k <? 0 + Z.of_nat (Z.to_nat nG)))%bool with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia). split; reflexivity. }
    assert (PPm : PP nG (yy_init (Z.to_nat nG) p0 0)) by (apply PP_init; lia).
    assert (PV0m : zget (yy_init (Z.to_nat nG) p0 0) 0 = 0%Z).
    { rewrite yy_init_get. replace ((0 <=? 0) && (0 <? 0 + Z.of_nat (Z.to_nat nG)))%bool with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia). reflexivity. }
    enter_with (S0_sc_mtf (Z.to_nat nSel) 0 (yy_init (Z.to_nat nG) p0 0) (yy_init (Z.to_nat nG) znew 0) (it_sel it) (e_selectorMtf e0) i16 m1 m1 nSel w584);
      [st_eq| lia| lia| lia| lia| exact PPm| exact PAG0| exact FSEL| exact SEL| exact SELM| exact POS| exact C576| exact MI| apply munch_refl| apply wmono_refl| bz_ceil; bz_params; unfold CEIL; lia| exact SPB|].
    clear SEL SELM POS C576 MI. intros m2 pm2 ya2 ya4 ya5 ya6 ya7. cbv zeta. intros PP2 PAG2 SEL SELM POS C576 MI MU2 WM2.
    transport_after_call s0segs m1 m2 MU2 WM2. clear MU2 WM2.
    change (sm_selmtf (Z.to_nat nSel) (yy_init (Z.to_nat nG) p0 0) (it_sel it) (e_selectorMtf e0) 0) with (smC_pm e0 c0 f0 p0 h0 w0 q0) in SELM.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    rewrite <- (firstn_skipn 376 J184) in J184H. apply (proj1 (u8arr_app s0segs _ _ _ _)) in J184H. destruct J184H as [J184a J560].
    rewrite length_firstn in J560. replace (usp + 184 + Z.of_nat (Nat.min 376 (length J184)))%Z with (usp + 560)%Z in J560 by lia.
    pose proof (rw_cells_of_u8arr s0segs _ _ _ J560) as C560. rewrite length_skipn in C560. replace (length J184 - 376)%nat with 16%nat in C560 by lia.
    cps_destruct (rw_cells_junk16_C8 s0segs _ _ _ C560) as (nd & rr & CC). clear C560 J560.
    (* [comment removed for export] *)
    lstep. lstep. lstep. lstep. lstep. lstep. lstep. lstep. lstep. lstep. lstep. lstep. lstep. lstep. (lstep; lit_store). lstep. lstep. lstep. lstep.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (HI : rw_cells s0segs mm (usp + 560) (smC_hi3 cx e0 nSel)) end.
    { unfold smC_hi3. lazymatch goal with |- rw_cells _ ?mm _ [?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7] =>
        change (rw_cells s0segs mm (usp + 560) ([c1; c2] ++ [c3; c4; c5; c6; c7])) end.
      apply (proj2 (rw_cells_app2 _ _ _ _ _)). split.
      - lazymatch goal with H : rw_cells _ _ (usp + 560)%Z _ |- _ => exact H end || (lazymatch goal with H : rw_cells _ _ (usp + 560)%Z ?L |- rw_cells _ _ _ ?L2 => replace L2 with L; [exact H| CmpFast.rlf] end).
      - cbn [cells_size csize Nat.add]. replace (usp + 560 + Z.of_nat 16)%Z with (usp + 576)%Z by lia.
        lazymatch goal with H : rw_cells _ _ (usp + 576)%Z ?L |- rw_cells _ _ _ ?L2 => first [exact H| replace L2 with L; [exact H| CmpFast.rlf]] end. }
    repeat match goal with H : rw_cells _ _ (usp + 576)%Z _ |- _ => clear H | H : rw_cells _ _ (usp + 560)%Z [_; _] |- _ => clear H end.
    (* [comment removed for export] *)
    enter_with (S0_sc_assign (Z.to_nat nG) 0%nat (e_code e0) (it_len it) nSel lo _ _ sv w24 w56);
      [st_eq| lia| lia| exact FLEN| exact LEN| exact CODE| unfold smB_slots3; cbv zeta; exact S8| exact HI| exact MI| exact ST| lia| bz_ceil; bz_params; unfold CEIL; lia
      | apply munch_refl| apply wmono_refl| exact SPB|].
    clear LEN CODE S8 HI MI ST. intros m3 zra z0 z1 z2 za0 za1 za2 za3 za4 za5 za6 za7 zs7 zs8 z3 z4 z5 z6 LEN CODE S8 HI MI ST MU3 WM3.
    unfold smB_slots3 in S8. cbv zeta in S8. unfold smC_hi3 in HI.
    lazymatch type of MU3 with munch _ ?ma ?mb => transport_after_call s0segs ma mb MU3 WM3 end. clear MU3 WM3.
    change (sm_assign (Z.to_nat nG) (e_code e0) (it_len it) A (Z.of_nat 0)) with (smC_code e0 c0 f0 h0 w0 q0) in CODE.
    (* [comment removed for export] *)
    destruct (u8arr_of_cells s0segs _ _ _ (rw_cells_of_u8arr s0segs _ _ _ POS)) as [PJ LPJ]. cbn [cells_bytes cbytes app] in PJ, LPJ. rewrite app_nil_r in PJ.
    enter_with (K m3 (firstn 376 J184) _);
      [st_eq| exact SEL| exact SELM| exact LEN| exact CODE| unfold smB_slots3; cbv zeta; exact S8| exact J184a| rewrite length_firstn; lia| unfold smC_hi3; exact HI
      | exact PJ| rewrite ovb_length; lia| exact ST| exact MI| exact MU0| exact WM0].
  Qed.
End SC3.

Theorem S0_smC : S0_smC_spec sd_facts.
Proof.
  unfold S0_smC_spec. intros until fc. cbv zeta. intros SEL SELM LEN CODE S8 J184H L184 C576 I16 L16 ST STK CLO MI CX SEP SPB SDF K.
  pose proof SDF as SF. unfold sd_facts in SF. cbv zeta in SF. cbn [e_nInUse est_C] in SF.
  cps_destruct SF as (FA & FG & _).
  eapply S0_smC_body; try eassumption.
Qed.

End ACeilS1.
