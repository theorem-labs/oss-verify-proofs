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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCStream BzCState BzCMtf BzArrD BzCRebuildF CmpMem CmpCut CmpCutSM CmpCutSmA BzCFactsSmA CmpFsKit CmpHmKit CmpSmKit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit AsanCut AsanCutB0 AsanKitB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsV.   (* [comment removed for export] *)
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
Local Ltac simpl_arr_sizes ::= CmpFast.sas10_all.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_smV.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section B0SMB.
  Variables (cx : cctx) (g : eg) (e : est) (Q : machine_state -> Prop).
  Variables (gp tp s0 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (P SHE : Z) (s9 : word).
  Hypothesis CX : cctx_ok cx. Hypothesis SF : smA_facts e.
  Hypothesis CEP : (CEIL <= P)%Z. Hypothesis PHI : (P + 1712 <= 18446744073709551616)%Z.
  Hypothesis AE : sanchor (c_E cx) SHE.
  Notation E := (c_E cx). Notation J := (c_J cx).
  Notation mf := (e_mtfFreq e). Notation A := (sm_alpha e). Notation nG := (smA_ng e). Notation nMTF := (sm_nmtf e). Notation nInUse := (e_nInUse e).
  Notation cSB := (Z_to_bv 64 2147450880). Notation cP := (Z_to_bv 64 P).
  Notation NOT z := (Z_to_bv 64 (18446744073709551615 - z)).
  Notation Wlen := [(E + 37708, E + 39256)]%Z.
  Ltac openCX :=
    let H := fresh "CXL" in pose proof CX as H; bz_ceil; bz_params; unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in H; cbv zeta in H;
    cps_destruct H as (?XE0 & ?XE1 & ?XA10 & ?XA11 & ?XA20 & ?XA21 & ?XF0 & ?XF1 & ?Xb0 & ?Xb1 & ?Xf0 & ?Xf1 & ?ME & ?MA1 & ?MA2 & ?MF & ?Mb & ?Mf & ?LJ & ?LJb).
  Ltac openSF :=
    let H := fresh "SFL" in pose proof SF as H; unfold smA_facts in H; cbv zeta in H; cps_destruct H as (?NI & ?NM & ?MFD & ?IPK & ?IPT).
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Notation RIb a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s10 s11 :=
    (mkR (Z_to_bv 64 15) cP gp tp (Z_to_bv 64 (A - 1)) (Z_to_bv 64 (E + 672)) (Z_to_bv 64 258) s0 cP a0 a1 a2 a3 a4 a5 a6 a7
         cSB s3 (Z_to_bv 64 257) s5 s6 s7 (NOT (E + 672)) s9 s10 s11 (Z_to_bv 64 A) (Z_to_bv 64 1) (Z_to_bv 64 3) (Z_to_bv 64 6)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma B0_smA_grow : forall (f : nat) (ge aF gs tF remF : Z) (m : word -> option byte)
      (a0 a6 a7 s3 s6 s10 s11 : word),
    (A - 1 - ge < Z.of_nat f)%Z ->
    (0 <= gs)%Z -> (gs - 1 <= ge <= A - 1)%Z -> (aF < tF)%Z -> (0 < tF <= nMTF)%Z -> (0 <= aF <= remF)%Z ->
    aF = sumF (fun v => zget mf v) gs (Z.to_nat (ge + 1 - gs)) ->
    remF = sumF (fun v => zget mf v) gs (Z.to_nat (A - gs)) -> (remF <= nMTF)%Z ->
    u32arr b0segs m (E + 672) (ovw mf (jseg J 672 1032) 258) ->
    shzW b0segs [] m E (E + ESTATE_SIZE) ->
    (forall (pcx ge' aF' : Z) (a0 a5 a6 : word),
      (pcx = 0x8c0ac \/ pcx = 0x8c0b8)%Z ->
      sm_grow f mf tF A ge aF = (ge', aF') -> (ge <= ge' <= A - 1)%Z -> aF' = sumF (fun v => zget mf v) gs (Z.to_nat (ge' + 1 - gs)) -> (0 <= aF' <= remF)%Z ->
      evt b0segs Q (MS (RIb a0 (Z_to_bv 64 aF') (Z_to_bv 64 tF) (Z_to_bv 64 258) (Z_to_bv 64 A) a5 a6 a7 s3 (Z_to_bv 64 gs) s6 (Z_to_bv 64 ge') s10 s11)
                       F (Z_to_bv 64 pcx) fc None m (seg_rom b0segs))) ->
    evt b0segs Q (MS (RIb a0 (Z_to_bv 64 aF) (Z_to_bv 64 tF) (Z_to_bv 64 258) (Z_to_bv 64 A) (Z_to_bv 64 (ge + 1)) a6 a7 s3 (Z_to_bv 64 gs) s6 (Z_to_bv 64 (A - 1)) s10 s11)
                     F (Z_to_bv 64 0x8c048) fc None m (seg_rom b0segs)).
  Proof.
    induction f as [|f IH]. { intros; lia. }
    intros ge aF gs tF remF m a0 a6 a7 s3 s6 s10 s11 Hf Hgs Hge HaF HtF BaF EaF EremF HremF MTF SHe K.
    openCX. try clear ME MA1 MA2 MF Mb Mf. openSF. unfold CEIL in CEP. unfold sm_alpha, sm_nmtf in *. unfold ESTATE_SIZE in SHe.
    pose proof (munch_refl [] m) as MU.
    pose proof (jseg_length J 672 1032 ltac:(lia) ltac:(lia) ltac:(lia)) as LJm. pose proof (ovw_length mf (jseg J 672 1032) 258 ltac:(lia)) as LM.
    rewrite sm_grow_S in K.
    (* [comment removed for export] *)
    wstep; if_cases Kx; zify_cond_z Kx.
    { enter_with (K 0x8c0ac%Z ge aF _ _ _); [st_eq| left; reflexivity| | lia| exact EaF| lia].
      replace ((aF <? tF) && (ge <? nInUse + 2 - 1))%Z%bool with false by (symmetry; apply Bool.andb_false_iff; right; apply Z.ltb_ge; lia). reflexivity. }
    replace ((aF <? tF) && (ge <? nInUse + 2 - 1))%Z%bool with true in K
      by (symmetry; apply Bool.andb_true_iff; split; apply Z.ltb_lt; lia).
    pose proof (MFD (ge + 1)%Z ltac:(lia)) as [Dq Rq].
    (* [comment removed for export] *)
    assert (EaF' : (aF + zget mf (ge + 1))%Z = sumF (fun v => zget mf v) gs (Z.to_nat (ge + 2 - gs))).
    { rewrite EaF. replace (Z.to_nat (ge + 2 - gs)) with (S (Z.to_nat (ge + 1 - gs))) by lia. rewrite sumF_S_last. f_equal. f_equal. lia. }
    assert (BaF' : (0 <= aF + zget mf (ge + 1) <= remF)%Z).
    { rewrite EaF', EremF. apply sumF_prefix_le; [lia|]. intros b Hb. apply (proj1 (proj2 (MFD b ltac:(lia)))). }
    (* [comment removed for export] *)
    brun.
    (* [comment removed for export] *)
    pose proof (ovw_read b0segs m (E + 672) mf (jseg J 672 1032) 258 (ge + 1) _ MTF ltac:(lia) Dq ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. try rewrite (sx32_of_Z (zget mf (ge + 1))) by lia.
    (* [comment removed for export] *)
    wstep. wstep. try rewrite (sx32_of_Z (aF + zget mf (ge + 1))) by lia. brun_to 0x8c090%Z.
    try rewrite (sx32_of_Z (aF + zget mf (ge + 1))) by lia. try rewrite (sx32_of_Z (ge + 1 + 1)) by lia.
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - enter_with (IH (ge + 1)%Z (aF + zget mf (ge + 1))%Z gs tF remF m); [st_eq| lia| lia| lia| lia| lia| lia| | exact EremF| lia| exact MTF| unfold ESTATE_SIZE; exact SHe|].
      + rewrite EaF'. f_equal. lia.
      + intros pcx ge' aF' y0 y5 y6 Hpc E' Hge' EaF2 B2. eapply K; [exact Hpc| exact E'| lia| exact EaF2| exact B2].
    - (* [comment removed for export] *)
      wstep. wstep. try rewrite (sx32_of_Z (ge + 1 + 1 + -1)) by lia.
      enter_with (K 0x8c0b8%Z (ge + 1)%Z (aF + zget mf (ge + 1))%Z _ _ _); [st_eq| right; reflexivity| | lia| | lia].
      + apply sm_grow_stop. lia.
      + rewrite EaF'. f_equal. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma B0_smA_setrow : forall (n : nat) (v t gs ge : Z) (len : zarr) (me m : word -> option byte)
      (a0 a5 a6 a7 s3 : word),
    (v + Z.of_nat n = A)%Z -> (0 <= v)%Z -> (1 <= n)%nat -> (0 <= t < 6)%Z ->
    (0 <= gs <= 258)%Z -> (gs - 1 <= ge <= 258)%Z ->
    u8arr b0segs m (E + 37708) (ovb len (jseg J 37708 1548) 1548) -> mem_inv b0segs m ->
    munch Wlen me m -> wmono b0segs me m ->
    shzW b0segs Wlen me E (E + ESTATE_SIZE) ->
    frdW b0segs Wlen me (P + 1560) [C8 (NOT (E + 37708))] ->
    (forall m' (a0 a6 a7 : word),
      u8arr b0segs m' (E + 37708) (ovb (sm_setrow n len t gs ge v) (jseg J 37708 1548) 1548) -> mem_inv b0segs m' ->
      munch Wlen me m' -> wmono b0segs me m' ->
      evt b0segs Q (MS (RIb a0 (Z_to_bv 64 t) (Z_to_bv 64 A) (Z_to_bv 64 (258 * t)) (NOT (E + 37708 + 258 * t)) a5 a6 a7 s3 (Z_to_bv 64 gs) (Z_to_bv 64 (t + 1)) (Z_to_bv 64 ge)
                            (Z_to_bv 64 (E + 37708 + 258 * t)) (Z_to_bv 64 (E + 37708 + 258 * t)))
                       F (Z_to_bv 64 0x8c210) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (RIb a0 (Z_to_bv 64 t) (Z_to_bv 64 v) (Z_to_bv 64 (258 * t)) (NOT (E + 37708 + 258 * t)) a5 a6 a7 s3 (Z_to_bv 64 gs) (Z_to_bv 64 (t + 1)) (Z_to_bv 64 ge)
                          (Z_to_bv 64 (E + 37708 + 258 * t)) (Z_to_bv 64 (E + 37708 + 258 * t)))
                     F (Z_to_bv 64 0x8c15c) fc None m (seg_rom b0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros v t gs ge len me m a0 a5 a6 a7 s3 Hv Hv0 Hn Ht Hgs Hge LEN MI MU WM SHe V1560 K.
    openCX. try clear ME MA1 MA2 MF Mb Mf. openSF. unfold CEIL in CEP. unfold sm_alpha in *. unfold ESTATE_SIZE in SHe.
    pose proof (jseg_length J 37708 1548 ltac:(lia) ltac:(lia) ltac:(lia)) as LJl. pose proof (ovb_length len (jseg J 37708 1548) 1548 ltac:(lia)) as LL.
    rewrite sm_setrow_S in K.
    pose proof (u8arr_store_ok b0segs m (E + 37708) _ (258 * t + v) _ LEN ltac:(rewrite ovb_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO.
    pose proof (V1560 m MU) as RO.
    (* [comment removed for export] *)
    wstep; if_cases K1; zify_cond_z K1;
      [ brun_to 0x8c1e4%Z | wstep; if_cases K2; zify_cond_z K2; [ brun_to 0x8c1e4%Z | brun_to 0x8c1a0%Z ] ].
    all: clear RO.
    all: wstep; store_addr (E + 37708 + (258 * t + v))%Z.
    3: change (Z_to_le_bytes 1 0) with (le1 (Z_to_bv 64 0)).
    all: ovb_store1 LEN (258 * t + v)%Z.
    all: lazymatch type of LEN with context [wr8 ?l0 ?i0 ?w] =>
           replace (wr8 l0 i0 w) with (zset l0 i0 (setrow_val gs ge v)) in LEN
             by (unfold wr8, setrow_val, BZ_LESSER_ICOST, BZ_GREATER_ICOST; rewrite unsigned_lit by lia; rewrite Z.mod_small by lia;
                 destruct (Z.leb_spec gs v), (Z.leb_spec v ge); cbn [andb]; first [reflexivity| exfalso; lia]) end.
    (* [comment removed for export] *)
    3: wstep.
    all: wstep; wstep; if_cases Ke; zify_cond_z Ke;
      [ enter_with (IH (v + 1)%Z t gs ge (zset len (258 * t + v) (setrow_val gs ge v)) me);
          [st_eq| lia| lia| lia| lia| lia| lia| exact LEN| assumption| assumption| assumption| unfold ESTATE_SIZE; exact SHe| exact V1560| exact K]
      | assert (n = 0)%nat by lia; subst n; cbn [sm_setrow] in K; wstep;
        enter_with (K _ _ _ _); [st_eq| exact LEN| assumption| assumption| assumption] ].
  Qed.

  (* [comment removed for export] *)
  Lemma b0_divw_lit : forall a b, (0 <= a < 2147483648)%Z -> (0 < b < 2147483648)%Z ->
    v_divw (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a / b).
  Proof.
    intros a b Ha Hb. unfold v_divw. rewrite !unsigned_lit by lia. unfold bv_wrap, bv_modulus.
    change (2 ^ Z.of_N 32)%Z with 4294967296%Z. rewrite (Z.mod_small b 4294967296%Z ltac:(lia)).
    replace (b =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
    rewrite (swrap32_small a) by lia. rewrite (swrap32_small b) by lia. rewrite Z.quot_div_nonneg by lia.
    pose proof (Z.div_pos a b ltac:(lia) ltac:(lia)). pose proof (Z.div_le_upper_bound a b a ltac:(lia) ltac:(nia)).
    rewrite swrap32_small by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation smGROW := (B0_smA_grow).
  Notation smSETROW := (B0_smA_setrow).
  Lemma B0_smA_iloop : forall (n k : nat) (me m : word -> option byte)
      (a0 a2 a3 a4 a5 a6 a7 s6 s7 : word),
    let s := sip_k e k in
    ip_nPart s = Z.of_nat n -> (1 <= n)%nat -> (Z.of_nat k + Z.of_nat n = nG)%Z ->
    u8arr b0segs m (E + 37708) (ovb (ip_len s) (jseg J 37708 1548) 1548) ->
    u32arr b0segs m (E + 672) (ovw mf (jseg J 672 1032) 258) ->
    rw_cells b0segs m (E + 640) (EHEAD2 cx g e) -> mem_inv b0segs m ->
    munch Wlen me m -> wmono b0segs me m ->
    shzW b0segs Wlen me E (E + ESTATE_SIZE) ->
    frdW b0segs Wlen me (P + 112) [C8 (Z_to_bv 64 (SHE + 82))] -> frdW b0segs Wlen me (P + 120) [C8 (Z_to_bv 64 (E + 656))] ->
    frdW b0segs Wlen me (P + 1464) [C8 (Z_to_bv 64 (E + 37708))] -> frdW b0segs Wlen me (P + 1480) [C8 (Z_to_bv 64 nG)] ->
    frdW b0segs Wlen me (P + 1512) [C8 (Z_to_bv 64 A)] -> frdW b0segs Wlen me (P + 1536) [C8 (Z_to_bv 64 18446744071562067969)] ->
    frdW b0segs Wlen me (P + 1544) [C8 (Z_to_bv 64 0)] -> frdW b0segs Wlen me (P + 1560) [C8 (NOT (E + 37708))] ->
    (forall m' (a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 : word), let s' := sip_k e (k + n) in
      u8arr b0segs m' (E + 37708) (ovb (ip_len s') (jseg J 37708 1548) 1548) ->
      u32arr b0segs m' (E + 672) (ovw mf (jseg J 672 1032) 258) ->
      rw_cells b0segs m' (E + 640) (EHEAD2 cx g e) -> mem_inv b0segs m' ->
      munch Wlen me m' -> wmono b0segs me m' ->
      evt b0segs Q (MS (RIb a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (ip_remF s')) (Z_to_bv 64 (ip_gs s')) s6 s7 (Z_to_bv 64 (E + 37708 + 258 * (0 - 1))) (Z_to_bv 64 (E + 37708 + 258 * (0 - 1))))
                       F (Z_to_bv 64 0x8c318) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (RIb a0 (Z_to_bv 64 (ip_nPart s)) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (ip_remF s)) (Z_to_bv 64 (ip_gs s)) s6 s7
                          (Z_to_bv 64 (E + 37708 + 258 * (ip_nPart s - 1))) (Z_to_bv 64 (E + 37708 + 258 * (ip_nPart s - 1))))
                     F (Z_to_bv 64 0x8c000) fc None m (seg_rom b0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros k me m a0 a2 a3 a4 a5 a6 a7 s6 s7 s HnP Hn Hk LEN MTF EH2 MI MU WM SHe V112 V120 V1464 V1480 V1512 V1536 V1544 V1560 K.
    openCX. try clear ME MA1 MA2 MF Mb Mf. openSF. unfold CEIL in CEP. assert (HA : A = (nInUse + 2)%Z) by reflexivity. assert (HM : nMTF = e_nMTF e) by reflexivity.
    pose proof (sm_nGroups_range (e_nMTF e)) as NGR. change (sm_nGroups (e_nMTF e)) with nG in NGR.
    pose proof (IPK k ltac:(lia)) as IK. cbv zeta in IK. fold s in IK. cps_destruct IK as (EnP & Hgs & EremF & HremF).
    pose proof (jseg_length J 37708 1548 ltac:(lia) ltac:(lia) ltac:(lia)) as LJl. pose proof (ovb_length_nat (ip_len s) (jseg J 37708 1548) 1548) as LLn.
    pose proof (jseg_length J 672 1032 ltac:(lia) ltac:(lia) ltac:(lia)) as LJm. pose proof (ovw_length mf (jseg J 672 1032) 258 ltac:(lia)) as LM.
    unfold EHEAD2 in EH2. unfold ESTATE_SIZE in SHe.
    set (nP := ip_nPart s) in *. set (gs := ip_gs s) in *. set (remF := ip_remF s) in *.
    (* [comment removed for export] *)
    destruct (ex_intro (fun t => t = (remF / nP)%Z) (remF / nP)%Z eq_refl) as [tF EtF].
    assert (HtF : (0 <= tF <= remF)%Z).
    { rewrite EtF. split; [apply Z.div_pos; lia|]. pose proof (Z.div_le_compat_l remF 1 nP ltac:(lia) ltac:(lia)) as Hd. rewrite Z.div_1_r in Hd. exact Hd. }
    change (id (tF = remF / nP)%Z) in EtF.
    (* [comment removed for export] *)
    wstep. try rewrite (sx32_of_Z_signed (gs + -1)) by lia. brun_to 0x8c010%Z. wstep. rewrite (b0_divw_lit remF nP) by lia. replace (remF / nP)%Z with tF by exact EtF.
    assert (ADJ : forall ge1, ip_adj nG s ge1 = ((gs <? ge1) && negb (nP =? nG) && negb (nP =? 1) && ((nG - nP) mod 2 =? 1))%Z%bool) by (intros; reflexivity).
    set (ROW := (E + 37708 + 258 * (nP - 1))%Z) in *.
    (* [comment removed for export] *)
    assert (POSTADJ : forall ge1 aF1 ge2 aF2 (ya0 ya2 ya3 ya4 ya5 ya6 ya7 : word),
      sm_grow 260%nat mf tF A (gs - 1) 0 = (ge1, aF1) -> (gs - 1 <= ge1 <= A - 1)%Z ->
      aF1 = sumF (fun v => zget mf v) gs (Z.to_nat (ge1 + 1 - gs)) -> (0 <= aF1 <= remF)%Z ->
        (ge2 = (if ip_adj nG s ge1 then ge1 - 1 else ge1))%Z -> (aF2 = (if ip_adj nG s ge1 then aF1 - zget mf ge1 else aF1))%Z ->
        (gs - 1 <= ge2 <= A - 1)%Z -> (0 <= aF2 <= remF)%Z ->
      evt b0segs Q (MS (RIb ya0 (Z_to_bv 64 aF2) ya2 ya3 ya4 ya5 ya6 ya7 (Z_to_bv 64 remF) (Z_to_bv 64 gs) (Z_to_bv 64 nP) (Z_to_bv 64 ge2) (Z_to_bv 64 ROW) (Z_to_bv 64 ROW))
                       F (Z_to_bv 64 0x8c120) fc None m (seg_rom b0segs))).
    { intros ge1 aF1 ge2 aF2 ya0 ya2 ya3 ya4 ya5 ya6 ya7 EG Hge1 EaF1 BaF1 Ege2 EaF2 Hge2 BaF2.
      (* [comment removed for export] *)
      pose proof (V112 m MU) as RO. pose proof (V120 m MU) as RO2. brun_to 0x8c138%Z. clear RO RO2.
      try rewrite (sx32_of_Z aF2) by lia.
      wstep; if_cases Kv; zify_cond_z Kv; [exfalso; lia|].
      (* [comment removed for export] *)
      pose proof (V1512 m MU) as RO. wstep. clear RO. wstep; if_cases Ka; zify_cond_z Ka; [exfalso; lia|].
      pose proof (V1464 m MU) as RO. brun_to 0x8c15c%Z. clear RO.
      subst ROW.
      enter_with (smSETROW (Z.to_nat A) 0 (nP - 1) gs ge2 (ip_len s) m m _ _ _ _ _);
        [st_eq| lia| lia| lia| lia| lia| lia| exact LEN| exact MI| apply munch_refl| apply wmono_refl| | |].
      { eapply (shzW_sub b0segs Wlen Wlen me m); [exact SHe| exact MU| a_sub_fp| lia| unfold ESTATE_SIZE; lia]. }
      { eapply (frdW_sub b0segs Wlen Wlen me m); [exact V1560| exact MU| a_sub_fp]. }
      intros m2 za0 za6 za7 LEN2 MI2 MU2 WM2. clear LEN MI. transport_after_call b0segs m m2 MU2 WM2. clear MU2 WM2.
      (* [comment removed for export] *)
      wstep. try rewrite (sx32_of_Z (ge2 + 1)) by lia. try rewrite (sx32_of_Z_signed (ge2 + 1)) by lia. wstep; b_guard.
      wstep. try rewrite (sx32_of_Z remF) by lia. wstep. wstep. try rewrite (sx32_of_Z (remF - aF2)) by lia. try rewrite (sx32_of_Z_signed (remF - aF2)) by lia.
      wstep; b_guard. wstep. wstep.
      (* [comment removed for export] *)
      assert (Es' : sip_k e (S k) = SIP (sm_setrow (Z.to_nat A) (ip_len s) (nP - 1) gs ge2 0) (nP - 1) (remF - aF2) (ge2 + 1)).
      { rewrite sip_k_S. fold s. rewrite (sm_init_iter_spec mf nG A s ge1 aF1).
        2:{ unfold id in EtF. subst nP gs remF. rewrite <- EtF. exact EG. }
        cbv zeta. subst nP gs remF. rewrite <- Ege2, <- EaF2. reflexivity. }
      (* [comment removed for export] *)
      wstep; if_cases Kb; zify_cond_z Kb.
      - (* [comment removed for export] *)
        pose proof (IH (S k)) as IH'. cbv zeta in IH'. rewrite Es' in IH'. cbn [ip_nPart ip_remF ip_gs ip_len] in IH'.
        enter_with (IH' me m2 _ _ _ _ _ _ _ _ _);
          [st_eq| lia| lia| lia| exact LEN2| assumption| assumption| exact MI2| assumption| assumption| exact SHe| exact V112| exact V120| exact V1464| exact V1480| exact V1512| exact V1536| exact V1544| exact V1560|].
        intros m' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9. replace (S k + n)%nat with (k + S n)%nat by lia. exact (K m' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9).
      - (* [comment removed for export] *)
        assert (n = 0)%nat by lia. subst n. wstep.
        pose proof K as K'. cbv zeta in K'. replace (k + 1)%nat with (S k) in K' by lia. rewrite Es' in K'. cbn [ip_nPart ip_remF ip_gs ip_len] in K'.
        enter_with (K' m2 _ _ _ _ _ _ _ _ _ _); [st_eq| exact LEN2| assumption| assumption| exact MI2| assumption| assumption]. }
    (* [comment removed for export] *)
    assert (POSTGROW2 : forall ge1 aF1 (xa0 xa2 xa3 xa4 xa5 xa6 xa7 : word),
      sm_grow 260%nat mf tF A (gs - 1) 0 = (ge1, aF1) -> (gs - 1 <= ge1 <= A - 1)%Z ->
      aF1 = sumF (fun v => zget mf v) gs (Z.to_nat (ge1 + 1 - gs)) -> (0 <= aF1 <= remF)%Z -> (nP <> 1)%Z ->
      evt b0segs Q (MS (RIb xa0 (Z_to_bv 64 aF1) xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 remF) (Z_to_bv 64 gs) (Z_to_bv 64 nP) (Z_to_bv 64 ge1) (Z_to_bv 64 ROW) (Z_to_bv 64 ROW))
                       F (Z_to_bv 64 0x8c0bc) fc None m (seg_rom b0segs))).
    { intros ge1 aF1 xa0 xa2 xa3 xa4 xa5 xa6 xa7 EG Hge1 EaF1 BaF1 K3.
      (* [comment removed for export] *)
      pose proof (V1480 m MU) as RO. wstep. clear RO. wstep; if_cases K2; zify_cond_z K2.
      { eapply (POSTADJ ge1 aF1 ge1 aF1); [exact EG| lia| exact EaF1| lia| | | lia| lia]; rewrite (ADJ ge1); replace (nP =? nG)%Z with true by (symmetry; apply Z.eqb_eq; lia);
          destruct (gs <? ge1)%Z; reflexivity. }
      (* [comment removed for export] *)
      wstep; if_cases K1; zify_cond_z K1.
      { eapply (POSTADJ ge1 aF1 ge1 aF1); [exact EG| lia| exact EaF1| lia| | | lia| lia]; rewrite (ADJ ge1); replace (gs <? ge1)%Z with false by (symmetry; apply Z.ltb_ge; lia); reflexivity. }
      (* [comment removed for export] *)
      pose proof (V1480 m MU) as RO. wstep. clear RO. wstep. try rewrite (sx32_of_Z (nG - nP)) by lia. try rewrite (sx32_of_Z_signed (nG - nP)) by lia.
      pose proof (V1536 m MU) as RO. wstep. clear RO. wstep.
      try rewrite (land_mask31 (nG - nP)) by lia.
      destruct (ex_intro (fun p => p = ((nG - nP) mod 2)%Z) ((nG - nP) mod 2)%Z eq_refl) as [par Epar].
      assert (Hpar : (0 <= par <= 1)%Z) by (rewrite Epar; Z.div_mod_to_equations; lia).
      rewrite <- Epar. change (id (par = (nG - nP) mod 2)%Z) in Epar.
      (* [comment removed for export] *)
      wstep; if_cases K4; zify_cond_z K4.
      { eapply (POSTADJ ge1 aF1 ge1 aF1); [exact EG| lia| exact EaF1| lia| | | lia| lia]; rewrite (ADJ ge1); unfold id in Epar; rewrite <- Epar;
          replace (par =? 1)%Z with false by (symmetry; apply Z.eqb_neq; lia);
          destruct (gs <? ge1)%Z, (nP =? nG)%Z, (nP =? 1)%Z; reflexivity. }
      (* [comment removed for export] *)
      assert (AT : ip_adj nG s ge1 = true).
      { rewrite (ADJ ge1). unfold id in Epar. rewrite <- Epar. replace (gs <? ge1)%Z with true by (symmetry; apply Z.ltb_lt; lia).
        replace (nP =? nG)%Z with false by (symmetry; apply Z.eqb_neq; lia). replace (nP =? 1)%Z with false by (symmetry; apply Z.eqb_neq; lia).
        replace (par =? 1)%Z with true by (symmetry; apply Z.eqb_eq; lia). reflexivity. }
      pose proof (MFD ge1 ltac:(lia)) as [Dg Rg].
      assert (BaF2 : (0 <= aF1 - zget mf ge1)%Z).
      { rewrite EaF1. replace (Z.to_nat (ge1 + 1 - gs)) with (S (Z.to_nat (ge1 - gs))) by lia. rewrite sumF_S_last.
        replace (gs + Z.of_nat (Z.to_nat (ge1 - gs)))%Z with ge1 by lia.
        pose proof (sumF_nonneg (Z.to_nat (ge1 - gs)) (fun v => zget mf v) gs ltac:(intros b Hb; apply (proj1 (proj2 (MFD b ltac:(lia)))))). lia. }
      (* [comment removed for export] *)
      brun.
      pose proof (ovw_read b0segs m (E + 672) mf (jseg J 672 1032) 258 ge1 _ MTF ltac:(lia) Dg ltac:(unfold wa; f_equal; lia)) as RD.
      (* [comment removed for export] *)
      wstep. clear RD. try rewrite (sx32_of_Z (zget mf ge1)) by lia.
      wstep. wstep. try rewrite (sx32_of_Z (aF1 - zget mf ge1)) by lia. try rewrite (sx32_of_Z_signed (aF1 - zget mf ge1)) by lia.
      wstep; b_guard. wstep. try rewrite (sx32_of_Z_signed (ge1 + -1)) by lia. try rewrite (sx32_of_Z (ge1 + -1)) by lia. wstep.
      enter_with (POSTADJ ge1 aF1 (ge1 - 1)%Z (aF1 - zget mf ge1)%Z _ _ _ _ _ _ _); [st_eq| exact EG| lia| exact EaF1| lia| rewrite AT; reflexivity| rewrite AT; reflexivity| lia| lia]. }
    (* [comment removed for export] *)
    assert (POSTGROW : forall (pcx ge1 aF1 : Z) (xa0 xa2 xa3 xa4 xa5 xa6 xa7 : word),
      (pcx = 0x8c0ac \/ pcx = 0x8c0b8)%Z ->
      sm_grow 260%nat mf tF A (gs - 1) 0 = (ge1, aF1) -> (gs - 1 <= ge1 <= A - 1)%Z ->
      aF1 = sumF (fun v => zget mf v) gs (Z.to_nat (ge1 + 1 - gs)) -> (0 <= aF1 <= remF)%Z ->
      evt b0segs Q (MS (RIb xa0 (Z_to_bv 64 aF1) xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 remF) (Z_to_bv 64 gs) (Z_to_bv 64 nP) (Z_to_bv 64 ge1) (Z_to_bv 64 ROW) (Z_to_bv 64 ROW))
                       F (Z_to_bv 64 pcx) fc None m (seg_rom b0segs))).
    { intros pcx ge1 aF1 xa0 xa2 xa3 xa4 xa5 xa6 xa7 Hpc EG Hge1 EaF1 BaF1.
      destruct Hpc as [-> | ->]; (wstep; if_cases K3; zify_cond_z K3;
        [ eapply (POSTADJ ge1 aF1 ge1 aF1); [exact EG| lia| exact EaF1| lia| | | lia| lia]; rewrite (ADJ ge1); replace (nP =? 1)%Z with true by (symmetry; apply Z.eqb_eq; lia);
            destruct (gs <? ge1)%Z, (nP =? nG)%Z; reflexivity
        | try (a_pc_is_lit; a_at_pc 0x8c0b0%Z; wstep); eapply (POSTGROW2 ge1 aF1); [exact EG| lia| exact EaF1| exact BaF1| lia] ]). }
    (* [comment removed for export] *)
    assert (E0 : 0%Z = sumF (fun v => zget mf v) gs (Z.to_nat (gs - 1 + 1 - gs))) by (replace (Z.to_nat (gs - 1 + 1 - gs)) with 0%nat by lia; reflexivity).
    wstep; if_cases K5; zify_cond_z K5.
    { wstep. eapply (POSTGROW 0x8c0ac%Z (gs - 1)%Z 0%Z); [left; reflexivity| apply sm_grow_stop; lia| lia| exact E0| lia]. }
    (* [comment removed for export] *)
    pose proof (V1544 m MU) as RO. wstep. clear RO. brun_to 0x8c024%Z.
    wstep; if_cases K7; zify_cond_z K7; [exfalso; lia|]. wstep. wstep. wstep. wstep; if_cases K8; zify_cond_z K8; [exfalso; lia|].
    wstep. wstep. wstep. try rewrite (sx32_of_Z (A - 1 + 1)) by lia. try rewrite (sx32_of_Z_signed (A - 1 + 1)) by lia. wstep.
    enter_with (smGROW 260%nat (gs - 1)%Z 0%Z gs tF remF m _ _ _ _ _ _ _);
      [st_eq| lia| lia| lia| lia| lia| lia| exact E0| exact EremF| lia| exact MTF| |].
    { eapply (shzW_sub b0segs Wlen [] me m); [exact SHe| exact MU| a_sub_fp| lia| unfold ESTATE_SIZE; lia]. }
    intros pcx ge' aF' y0 y5 y6 Hpc EG' Hge' EaF' BaF'. eapply (POSTGROW pcx ge' aF'); [exact Hpc| exact EG'| lia| exact EaF'| exact BaF'].
  Qed.
End B0SMB.
End ACeilS1.
