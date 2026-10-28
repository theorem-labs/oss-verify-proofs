(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState BzCMtf BzArrD BzCLemmas1 CmpMem BzSepTac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut CmpCutSM CmpCutSmA CmpCutSD CmpSdKit CmpSdTac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpArith.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCNumZ BzCLemmasSd BzCLemmasSd2.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpArith2 BzWalkArith2 BzWalkArith4.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From Stdlib Require Lia. Unset Lia Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut6.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.
Local Ltac U.Bz.BzTac.mlia ::= CmpFast.mlia_fast.
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac U.Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.
Local Ltac lia ::= CmpLiaC.lia_c.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpStEq.
Local Ltac U.Bz.BzTac.st_eq ::= CmpStEq.st_eq_fast.
Local Ltac simpl_arr_sizes ::= CmpFast.sas10_all.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpArith2.CmpSdArith OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCLemmasSd2.BzCLemmasSd3.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import UKit U0_sd4P CmpCut0 S0_cmp_asg BzCFactsSd BzCFactsSd2 CmpHmKit CmpSmKit.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCFactsGm BzCHuff.

Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Definition asg_postZ (ra : word) (spz : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (Ecode : Z) (code' : zarr) (Jc : list byte) (NC lo : Z) (W : list (Z * Z))
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR ra (Z_to_bv 64 spz) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom s0segs)
    /\ munch W m m' /\ wmono s0segs m m' /\ mem_inv s0segs m' /\ stk s0segs m' lo spz
    /\ u32arr s0segs m' Ecode (ovw code' Jc NC).

Lemma U0_hbAssignCodes_Z : forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (Ecode Elen cb lb minLen maxLen alphaSize NC NL lo spz : Z) (code len : zarr) (Jc Jl : list byte),
  (0 <= spz < 18446744073709551616)%Z ->
  a0 = Z_to_bv 64 (Ecode + 4 * cb) -> a1 = Z_to_bv 64 (Elen + lb) ->
  a2 = Z_to_bv 64 minLen -> a3 = Z_to_bv 64 maxLen -> a4 = Z_to_bv 64 alphaSize ->
  u32arr s0segs m Ecode (ovw code Jc NC) -> u8arr s0segs m Elen (ovb len Jl NL) -> mem_inv s0segs m ->
  stk s0segs m lo spz -> (lo + 16 <= spz)%Z ->
  (0 <= cb)%Z -> (cb + alphaSize <= NC)%Z -> (0 <= lb)%Z -> (lb + alphaSize <= NL)%Z -> (0 <= alphaSize <= 258)%Z ->
  (1 <= minLen <= 32)%Z -> (0 <= maxLen <= 17)%Z -> (Ecode mod 4 = 0)%Z -> (0 < Ecode)%Z -> (Ecode + 4 * NC <= CEIL)%Z -> (0 < Elen)%Z -> (Elen + NL <= CEIL)%Z ->
  apart Ecode (4 * NC) Elen NL ->
  (spz <= Ecode \/ Ecode + 4 * NC <= spz - 16)%Z -> (spz <= Elen \/ Elen + NL <= spz - 16)%Z ->
  (forall i, 0 <= i < alphaSize -> zdef len (lb + i) = true /\ minLen <= zget len (lb + i) <= maxLen)%Z ->
  evt s0segs (asg_postZ ra spz gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
              Ecode (hbAssignCodes code len cb lb minLen maxLen alphaSize) Jc NC lo
              [(Ecode + 4 * cb, Ecode + 4 * (cb + alphaSize)); (spz - 16, spz)]%Z m)
      (MS (mkR ra (Z_to_bv 64 spz) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 147980) fc None m (seg_rom s0segs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
         Ecode Elen cb lb minLen maxLen alphaSize NC NL lo spz code len Jc Jl Hsp.
  pose proof (S0_hbAssignCodes ra (Z_to_bv 64 spz) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
                         Ecode Elen cb lb minLen maxLen alphaSize NC NL lo code len Jc Jl) as G.
  cbv zeta in G. cbn [ci_segs ci_hbAssignCodes S0C] in G. unfold hbAssignCodes_post in G.
  rewrite (unsigned_lit spz) in G by lia. exact G.
Qed.

Lemma h34_firstn4_le8 : forall w : word, firstn 4 (le8 w) = le4 w.
Proof. intros w. unfold le8, le4, word_to_le_bytes. reflexivity. Qed.
Lemma h34_skipn_le8 : forall (n : nat) (w : word) (l : list byte), (8 <= n)%nat -> skipn n (le8 w ++ l) = skipn (n - 8) l.
Proof. intros n w l Hn. rewrite skipn_app, length_le8. rewrite skipn_all2 by (rewrite length_le8; lia). reflexivity. Qed.

Section SDC.
  Variables (cx : cctx) (g : eg) (e0 : est) (Q : machine_state -> Prop).
  Variables (gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variable P : Z.
  Hypothesis CX : cctx_ok cx. Hypothesis SEP : cctx_sep cx.
  Hypothesis CEP : (CEIL <= P)%Z. Hypothesis PHI : (P + 1200 <= 18446744073709551616)%Z.
  Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation A2 := (c_A2 cx). Notation J := (c_J cx).
  Notation A := (sm_alpha e0). Notation nG := (smA_ng e0).
  Hypothesis HA : (3 <= A <= 258)%Z. Hypothesis HNG : (2 <= nG <= 6)%Z.
  Notation cP := (Z_to_bv 64 P). Notation cE := (Z_to_bv 64 E).
  Notation NOT z := (Z_to_bv 64 (18446744073709551615 - z)).
  Notation LR t := (E + 37708 + 258 * t)%Z.
  Notation Wpos := [(P + 1044, P + 1060)]%Z.
  Notation Wmtf := [(E + 19706, E + 37708); (P + 1044, P + 1060)]%Z.
  Notation Was := [(E + 39256, E + 45448); (P - 16, P)]%Z.
  Notation WC := [(E + 19706, E + 37708); (E + 39256, E + 45448); (P + 888, P + 1040); (P + 1044, P + 1060); (P - 16, P)]%Z.
  Notation HX nSel H := (SDW (h888 H) (h896 H) (h904 H) (h912 H) (h920 H) (h928 H) (h936 H) (Z_to_bv 64 nSel) (Z_to_bv 64 3005)
                             (h960 H) (h968 H) (h976 H) (h984 H) (NOT (E + 39256)) (Z_to_bv 64 (E + 39256)) (h1008 H) (h1016 H)
                             (Z_to_bv 64 3004) (h1032 H)).
  Ltac openCX := openCX_d CX SEP CEP.

  Definition PAGREE (pm p : zarr) : Prop := forall k, (1 <= k < nG)%Z -> zdef pm k = true /\ zget pm k = zget p k.

  Lemma hc_rd976 : forall (m : word -> option byte) (H : sdw),
    rw_cells s0segs m (P + 888) (sd_hc H) -> ov_read_bytes s0segs m (wa (P + 976)) 4 = Some (le4 (h976 H)).
  Proof.
    intros m H HH. destruct HH as [[Hwf Hb] Hw].
    replace (wa (P + 976)) with (wa (P + 888 + Z.of_nat 88)) by (unfold wa; f_equal; lia).
    rewrite (bytes_at_ov_read s0segs m _ _ 88 4 Hb).
    2:{ unfold sd_hc. cbn [cells_bytes cbytes]. rewrite !length_app, !length_le8. cbn. lia. }
    f_equal; unfold sd_hc; cbn [cells_bytes cbytes]; rewrite !h34_skipn_le8 by lia; cbn [Nat.sub]; rewrite skipn_O;
      rewrite firstn_app, length_le8; cbn [Nat.sub]; rewrite firstn_O, app_nil_r; apply h34_firstn4_le8.
  Qed.

  Section MTF.
  Variables (ra s1 s2 s3 s4 s5 s6 s7 s8 s10 s11 t5 t6 : word).
  Notation MR t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 :=
    (mkR ra cP gp tp t0 t1 t2 cE s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (NOT (E + 37708)) s10 s11 t3 t4 t5 t6).
  Notation MRb t0 t1 t2 a0 a1 a7 t3 nSel :=
    (MR t0 t1 t2 a0 a1 (Z_to_bv 64 (P + 1045)) (Z_to_bv 64 18002) (Z_to_bv 64 (E + 19706)) (NOT (E + 19706)) (Z_to_bv 64 (-5)) a7 t3 (Z_to_bv 64 nSel)).

  Lemma U0_sc_posinit : forall (n : nat) (i : Z) (pm : zarr) (i16 : list byte) (m mf : word -> option byte)
      (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 : word),
    (i + Z.of_nat n = nG)%Z -> (0 <= i)%Z -> (1 <= n)%nat ->
    u8arr s0segs m (P + 1044) (ovb pm i16 16) ->
    mem_inv s0segs m -> munch Wpos mf m -> wmono s0segs mf m ->
    frdW s0segs Wpos mf (P + 928) [C8 (Z_to_bv 64 nG)] ->
    (forall m',
      u8arr s0segs m' (P + 1044) (ovb (yy_init n pm i) i16 16) ->
      mem_inv s0segs m' -> munch Wpos mf m' -> wmono s0segs mf m' ->
      evt s0segs Q (MS (MR t0 t1 t2 (Z_to_bv 64 nG) (Z_to_bv 64 6) (Z_to_bv 64 (P + 1044)) (Z_to_bv 64 nG) a4 a5 a6 a7 t3 t4)
                       F (Z_to_bv 64 111740) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (MR t0 t1 t2 (Z_to_bv 64 i) (Z_to_bv 64 6) (Z_to_bv 64 (P + 1044)) a3 a4 a5 a6 a7 t3 t4)
                     F (Z_to_bv 64 111712) fc None m (seg_rom s0segs)).
  Proof using All.
    induction n as [|n IH]. { intros; lia. }
    intros i pm i16 m mf t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 Hi Hi0 Hn POS MI MU WM V928 K.
    openCX. pose proof (ovb_length_nat pm i16 16) as LP.
    rewrite yy_init_S in K.
    wstep; u_guard.
    wstep.
    pose proof (u8arr_store_ok s0segs m (P + 1044) _ i _ POS ltac:(rewrite ovb_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO.
    wstep. store_addr (P + 1044 + i)%Z. ovb_store1 POS i.
    replace (wr8 pm i (bv_unsigned (Z_to_bv 64 i))) with (zset pm i i) in POS by (unfold wr8; rewrite unsigned_lit by lia; rewrite Z.mod_small by lia; reflexivity).
    wstep.
    lazymatch goal with MU' : munch _ _ ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (V928 mm MU') as RO end. wstep. clear RO.
    wstep; if_cases Ke; zify_cond_z Ke.
    - enter_with (IH (i + 1)%Z _ i16 _ mf); [st_eq| lia| lia| lia| exact POS| assumption| exact MU| exact WM| exact V928| exact K].
    - assert (n = 0)%nat by lia. subst n. cbn [yy_init] in K.
      enter_with K; [st_eq| exact POS| assumption| exact MU| exact WM].
  Qed.

  Lemma U0_sc_search : forall (n : nat) (j mm : Z) (pos0 pm : zarr) (i16 : list byte) (m mf : word -> option byte) (nSel ll : Z)
      (a0 a1 t3 : word),
    (mm - j = Z.of_nat n)%Z -> (0 <= j <= mm)%Z -> (mm < nG)%Z ->
    (forall k, 0 <= k < nG -> 0 <= zget pos0 k < nG)%Z -> (0 <= ll < nG)%Z ->
    zget pos0 mm = ll -> (forall k, j <= k < mm -> zget pos0 k <> ll)%Z ->
    (forall k, 1 <= k <= j -> zdef pm k = true /\ zget pm k = zget pos0 (k - 1))%Z ->
    (forall k, j < k < nG -> zdef pm k = true /\ zget pm k = zget pos0 k)%Z ->
    u8arr s0segs m (P + 1044) (ovb pm i16 16) ->
    mem_inv s0segs m -> munch Wpos mf m -> wmono s0segs mf m ->
    (forall m' pm',
      (forall k, 1 <= k <= mm -> zdef pm' k = true /\ zget pm' k = zget pos0 (k - 1))%Z ->
      (forall k, mm < k < nG -> zdef pm' k = true /\ zget pm' k = zget pos0 k)%Z ->
      u8arr s0segs m' (P + 1044) (ovb pm' i16 16) ->
      mem_inv s0segs m' -> munch Wpos mf m' -> wmono s0segs mf m' ->
      evt s0segs Q (MS (MRb (Z_to_bv 64 (- mm)) (Z_to_bv 64 (P + 1045 + mm)) (Z_to_bv 64 ll) a0 a1 (Z_to_bv 64 ll) (Z_to_bv 64 ll) nSel)
                       F (Z_to_bv 64 111876) fc None m' (seg_rom s0segs))) ->
    (j < mm)%Z ->
    evt s0segs Q (MS (MRb (Z_to_bv 64 (- j)) (Z_to_bv 64 (P + 1045 + j)) (Z_to_bv 64 (zget pos0 j)) a0 a1 (Z_to_bv 64 ll) t3 nSel)
                     F (Z_to_bv 64 111844) fc None m (seg_rom s0segs)).
  Proof using All.
    induction n as [|n IH]. { intros; lia. }
    intros j mm pos0 pm i16 m mf nSel ll a0 a1 t3 Hn Hj Hmm PB Hll Em NOC SH REST POS MI MU WM K LT.
    openCX. pose proof (ovb_length_nat pm i16 16) as LP.
    pose proof (PB j ltac:(lia)) as Pj. pose proof (PB (j + 1)%Z ltac:(lia)) as Pj1.
    destruct (REST (j + 1)%Z ltac:(lia)) as [D1 V1].
    wstep; u_guard.
    pose proof (ovb_read1 s0segs m (P + 1044) pm i16 16 (j + 1) _ POS ltac:(lia) D1 ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. rewrite V1. cbv beta. rewrite (unsigned_lit8 (zget pos0 (j + 1))) by lia.
    pose proof (u8arr_store_ok s0segs m (P + 1044) _ (j + 1) _ POS ltac:(rewrite ovb_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO.
    wstep. store_addr (P + 1044 + (j + 1))%Z. ovb_store1 POS (j + 1)%Z.
    replace (wr8 pm (j + 1) (bv_unsigned (Z_to_bv 64 (zget pos0 j)))) with (zset pm (j + 1) (zget pos0 j)) in POS by (unfold wr8; rewrite unsigned_lit by lia; rewrite Z.mod_small by lia; reflexivity).
    wstep. wstep. wstep. wstep; if_cases Kc; zify_cond_z Kc.
    - assert (j + 1 < mm)%Z by (destruct (Z.eq_dec (j + 1) mm) as [EQ|]; [exfalso; rewrite <- EQ in Em; lia| lia]).
      enter_with (IH (j + 1)%Z mm pos0 _ i16 _ mf nSel ll a0 a1 _);
        [st_eq| lia| lia| lia| exact PB| lia| exact Em| intros k Hk; apply NOC; lia| | | exact POS| assumption| exact MU| exact WM| exact K| lia].
      + intros k Hk. destruct (Z.eq_dec k (j + 1)) as [->|NK].
        * rewrite zdef_zset_same, zget_zset_same. split; [reflexivity| f_equal; lia].
        * rewrite zdef_zset_other, zget_zset_other by lia. apply SH. lia.
      + intros k Hk. rewrite zdef_zset_other, zget_zset_other by lia. apply REST. lia.
    - assert (EJ : (j + 1 = mm)%Z) by (destruct (Z.eq_dec (j + 1) mm) as [|NE]; [assumption| exfalso; apply (NOC (j + 1)%Z); lia]).
      enter_with K; [st_eq| | | exact POS| assumption| exact MU| exact WM].
      + intros k Hk. destruct (Z.eq_dec k (j + 1)) as [->|NK].
        * rewrite zdef_zset_same, zget_zset_same. split; [reflexivity| f_equal; lia].
        * rewrite zdef_zset_other, zget_zset_other by lia. apply SH. lia.
      + intros k Hk. rewrite zdef_zset_other, zget_zset_other by lia. apply REST. lia.
  Qed.

  Lemma U0_sc_mtf : forall (n : nat) (i : Z) (Pm pm sel sm : zarr) (i16 : list byte) (m mf : word -> option byte) (nSel : Z)
      (t0 t1 t2 a7 t3 : word),
    (i + Z.of_nat n = nSel)%Z -> (0 <= i)%Z -> (1 <= n)%nat -> (nSel <= 18002)%Z ->
    PP nG Pm -> PAGREE pm Pm ->
    (forall k, 0 <= k < nSel -> zdef sel k = true /\ 0 <= zget sel k < nG)%Z ->
    u8arr s0segs m (E + 1704) (ovb sel (jseg J 1704 18002) 18002) ->
    u8arr s0segs m (E + 19706) (ovb sm (jseg J 19706 18002) 18002) ->
    u8arr s0segs m (P + 1044) (ovb pm i16 16) ->
    mem_inv s0segs m -> munch Wmtf mf m -> wmono s0segs mf m ->
    frdW s0segs Wmtf mf (P + 816) [C8 (Z_to_bv 64 (E + 1704))] -> frdW s0segs Wmtf mf (P + 824) [C8 (NOT (E + 1704))] ->
    (forall m' pm' (t0 t1 t2 a0 a7 t3 : word),
      let r := sm_selmtf n Pm sel sm i in
      PP nG (fst r) -> PAGREE pm' (fst r) ->
      u8arr s0segs m' (E + 1704) (ovb sel (jseg J 1704 18002) 18002) ->
      u8arr s0segs m' (E + 19706) (ovb (snd r) (jseg J 19706 18002) 18002) ->
      u8arr s0segs m' (P + 1044) (ovb pm' i16 16) ->
      mem_inv s0segs m' -> munch Wmtf mf m' -> wmono s0segs mf m' ->
      evt s0segs Q (MS (MRb t0 t1 t2 a0 (Z_to_bv 64 nSel) a7 t3 nSel) F (Z_to_bv 64 111908) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (MRb t0 t1 t2 (Z_to_bv 64 (zget Pm 0)) (Z_to_bv 64 i) a7 t3 nSel) F (Z_to_bv 64 111788) fc None m (seg_rom s0segs)).
  Proof using All.
    induction n as [|n IH]. { intros; lia. }
    intros i Pm pm sel sm i16 m mf nSel t0 t1 t2 a7 t3
           Hi Hi0 Hn HnS PPH PAG SELOK SEL SELM POS MI MU WM V816 V824 K.
    openCX.
    pose proof (jseg_length J 1704 18002 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ4. pose proof (ovb_length_nat sel (jseg J 1704 18002) 18002) as LS4.
    pose proof (jseg_length J 19706 18002 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ5. pose proof (ovb_length_nat sm (jseg J 19706 18002) 18002) as LS5.
    pose proof (ovb_length_nat pm i16 16) as LP.
    destruct (SELOK i ltac:(lia)) as [Dsi Rsi]. destruct PPH as [P1 P2]. pose proof (P1 0%Z ltac:(lia)) as P00.
    cbn [sm_selmtf] in K.
    cps_destruct (first_occ Pm (zget sel i) nG (P2 _ Rsi)) as (mm & Hmm & Emm & NOC).
    pose proof (pos_search_spec 8 Pm Pm (zget sel i) 0 mm nG ltac:(lia) ltac:(lia) ltac:(lia) Emm ltac:(intros k Hk; apply NOC; lia)
                  ltac:(intros; lia) ltac:(intros; reflexivity)) as SR. cbv zeta in SR.
    destruct (sm_pos_search 8 Pm (zget sel i) (zget Pm 0) 0) as [[P' tmp] jj]. cbn [fst snd] in SR. cps_destruct SR as (Ej & Et & SH & REST). subst jj tmp.
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
    wstep; u_guard.
    pose proof (V824 m MU) as RO. wstep. clear RO.
    wstep; u_guard.
    pose proof (V816 m MU) as RO. wstep. clear RO.
    wstep.
    pose proof (ovb_read1 s0segs m (E + 1704) sel (jseg J 1704 18002) 18002 i _ SEL ltac:(lia) Dsi ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. cbv beta. rewrite (unsigned_lit8 (zget sel i)) by lia.
    assert (K8 : forall m1 pm1 (xt1 xt2 xa7 xt3 : word),
      (forall k, 1 <= k <= mm -> zdef pm1 k = true /\ zget pm1 k = zget Pm (k - 1))%Z ->
      (forall k, mm < k < nG -> zdef pm1 k = true /\ zget pm1 k = zget Pm k)%Z ->
      u8arr s0segs m1 (P + 1044) (ovb pm1 i16 16) ->
      u8arr s0segs m1 (E + 19706) (ovb sm (jseg J 19706 18002) 18002) ->
      u8arr s0segs m1 (E + 1704) (ovb sel (jseg J 1704 18002) 18002) ->
      mem_inv s0segs m1 -> munch Wmtf mf m1 -> wmono s0segs mf m1 ->
      evt s0segs Q (MS (MRb (Z_to_bv 64 mm) xt1 xt2 (Z_to_bv 64 (zget sel i)) (Z_to_bv 64 i) xa7 xt3 nSel) F (Z_to_bv 64 111884) fc None m1 (seg_rom s0segs))).
    { intros m1 pm1 xt1 xt2 xa7 xt3 SH1 REST1 POS1 SELM1 SEL1 MI1 MU1 WM1.
      pose proof (ovb_length_nat pm1 i16 16) as LP1.
      wstep; u_guard.
      wstep. wstep.
      pose proof (u8arr_store_ok s0segs m1 (E + 19706) _ i _ SELM1 ltac:(rewrite ovb_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO.
      wstep. store_addr (E + 19706 + i)%Z. ovb_store1 SELM1 i.
      replace (wr8 sm i (bv_unsigned (Z_to_bv 64 mm))) with (zset sm i mm) in SELM1 by (unfold wr8; rewrite unsigned_lit by lia; rewrite Z.mod_small by lia; reflexivity).
      assert (PAG1 : PAGREE pm1 P1n).
      { intros k Hk. subst P1n. rewrite zget_zset_other by lia.
        destruct (Z.le_gt_cases k mm) as [L|L]; [rewrite SH by lia; apply SH1; lia| rewrite REST by lia; apply REST1; lia]. }
      assert (EP0 : zget P1n 0 = zget sel i) by (subst P1n; apply zget_zset_same).
      wstep; if_cases Ke; zify_cond_z Ke.
      - rewrite <- EP0.
        enter_with (IH (i + 1)%Z P1n pm1 sel (zset sm i mm) i16 _ mf nSel);
          [st_eq| lia| lia| lia| lia| exact PP'| exact PAG1| exact SELOK| exact SEL1| exact SELM1| exact POS1| assumption| exact MU1| exact WM1| exact V816| exact V824| exact K].
      - assert (n = 0)%nat by lia. subst n. cbn [sm_selmtf] in K.
        enter_with (K _ pm1); [st_eq| exact PP'| exact PAG1| exact SEL1| exact SELM1| exact POS1| assumption| exact MU1| exact WM1]. }
    wstep; if_cases Kq; zify_cond_z Kq.
    - assert (M1 : (0 < mm)%Z) by (destruct (Z.eq_dec mm 0) as [EQ|]; [exfalso; rewrite EQ in Emm; lia| lia]).
      wstep. wstep. wstep.
      enter_with (U0_sc_search (Z.to_nat mm) 0 mm Pm pm i16 m m nSel (zget sel i));
        [st_eq| lia| lia| lia| exact P1| lia| exact Emm| intros k Hk; apply NOC; lia| intros; lia| intros k Hk; apply PAG; lia
        | exact POS| exact MI| apply munch_refl| apply wmono_refl| | lia].
      clear POS MI. intros m1 pm1 SH1 REST1 POS1 MI1 MU1 WM1.
      transport_after_call s0segs m m1 MU1 WM1. clear MU1 WM1.
      wstep. wstep.
      replace (0 - Z.land (- mm) 18446744073709551615)%Z with (mm - 18446744073709551616)%Z.
      2:{ change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia. rewrite <- (Z.mod_add (- mm) 1 (2^64)%Z) by lia. rewrite Z.mod_small by lia. lia. }
      rewrite <- (Z_to_bv_mod64 (mm - 18446744073709551616)).
      replace ((mm - 18446744073709551616) mod 2 ^ 64)%Z with mm by (rewrite <- (Z.mod_add _ 1 (2^64)%Z) by lia; rewrite Z.mod_small by lia; lia).
      enter_with (K8 m1 pm1); [st_eq| exact SH1| exact REST1| exact POS1| exact SELM| exact SEL| exact MI1| exact MU| exact WM].
    - assert (M0 : mm = 0%Z) by (destruct (Z.eq_dec mm 0) as [|NE]; [assumption| exfalso; apply (NOC 0%Z); lia]).
      wstep. wstep. subst mm.
      enter_with (K8 m pm); [st_eq| intros; lia| intros k Hk; apply PAG; lia| exact POS| exact SELM| exact SEL| exact MI| exact MU| exact WM].
  Qed.
  End MTF.

  Notation CR t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t s3 s5 s6 t3 t4 t5 t6 :=
    (mkR (NOT (E + 39256)) cP gp tp t0 t1 t2 cE (Z_to_bv 64 t) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 258) s3 (Z_to_bv 64 18) s5 s6
         (Z_to_bv 64 5) (Z_to_bv 64 6) (NOT (E + 37708)) (Z_to_bv 64 1032) (Z_to_bv 64 (LR t)) t3 t4 t5 t6).

  Lemma U0_sc_minmax : forall (n : nat) (v t mn mx : Z) (len : zarr) (W : list (Z * Z)) (m mf : word -> option byte)
      (t0 t1 t2 a2 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    (v + Z.of_nat n = A)%Z -> (0 <= v)%Z -> (1 <= n)%nat -> (0 <= t < nG)%Z -> (0 <= mn <= 32)%Z -> (0 <= mx <= 17)%Z ->
    (forall tt vv, 0 <= tt < nG -> 0 <= vv < A -> zdef len (258 * tt + vv) = true /\ 1 <= zget len (258 * tt + vv) <= 17)%Z ->
    u8arr s0segs m (E + 37708) (ovb len (jseg J 37708 1548) 1548) ->
    munch W mf m ->
    frdW s0segs W mf (P + 984) [C8 (Z_to_bv 64 A)] ->
    (let r := sm_minmax n len t v mn mx in
      (0 <= fst r <= 32)%Z -> (0 <= snd r <= 17)%Z ->
      evt s0segs Q (MS (CR t0 t1 t2 (Z_to_bv 64 A) (NOT (LR t)) (Z_to_bv 64 A) (Z_to_bv 64 (E + 39256)) a4 a5 a6 a7 t (Z_to_bv 64 (258 * t))
                           (Z_to_bv 64 (snd r)) (Z_to_bv 64 (fst r)) t3 t4 t5 t6)
                       F (Z_to_bv 64 112088) fc None m (seg_rom s0segs))) ->
    evt s0segs Q (MS (CR t0 t1 t2 (Z_to_bv 64 v) (NOT (LR t)) a2 (Z_to_bv 64 (E + 39256)) a4 a5 a6 a7 t (Z_to_bv 64 (258 * t))
                         (Z_to_bv 64 mx) (Z_to_bv 64 mn) t3 t4 t5 t6)
                     F (Z_to_bv 64 112036) fc None m (seg_rom s0segs)).
  Proof using All.
    induction n as [|n IH]. { intros; lia. }
    intros v t mn mx len W m mf t0 t1 t2 a2 a4 a5 a6 a7 t3 t4 t5 t6 Hv Hv0 Hn Ht Hmn Hmx LENF LEN MU V984 K.
    openCX.
    pose proof (jseg_length J 37708 1548 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ6. pose proof (ovb_length_nat len (jseg J 37708 1548) 1548) as LL.
    destruct (LENF t v ltac:(lia) ltac:(lia)) as [Dl Rl].
    cbn [sm_minmax] in K. set (l := zget len (258 * t + v)) in *.
    pose proof (V984 m MU) as RO.
    wstep; u_guard. wstep; u_guard. wstep.
    pose proof (ovb_read1 s0segs m (E + 37708) len (jseg J 37708 1548) 1548 (258 * t + v) _ LEN ltac:(lia) Dl ltac:(unfold wa; f_equal; lia)) as RD.
    fold l in RD. wstep. clear RD. cbv beta. rewrite (unsigned_lit8 l) by lia.
    assert (STEP : forall (xs5 xs6 : word), xs5 = Z_to_bv 64 (if mx <? l then l else mx)%Z -> xs6 = Z_to_bv 64 (if l <? mn then l else mn)%Z ->
      evt s0segs Q (MS (CR t0 t1 t2 (Z_to_bv 64 v) (NOT (LR t)) (Z_to_bv 64 l) (Z_to_bv 64 (E + 39256)) a4 a5 a6 a7 t (Z_to_bv 64 (258 * t)) xs5 xs6 t3 t4 t5 t6)
                       F (Z_to_bv 64 112076) fc None m (seg_rom s0segs))).
    { intros xs5 xs6 -> ->.
      wstep. wstep. wstep; if_cases Ke; zify_cond_z Ke.
      - enter_with (IH (v + 1)%Z t (if l <? mn then l else mn)%Z (if mx <? l then l else mx)%Z len W m mf);
          [st_eq| lia| lia| lia| lia| destruct (Z.ltb_spec l mn); lia| destruct (Z.ltb_spec mx l); lia| exact LENF| exact LEN| exact MU| exact V984| exact K].
      - assert (n = 0)%nat by lia. subst n. cbn [sm_minmax] in K.
        enter_with K; [st_eq| cbn [fst]; destruct (Z.ltb_spec l mn); lia| cbn [snd]; destruct (Z.ltb_spec mx l); lia]. }
    wstep; if_cases K1; zify_cond_z K1.
    - wstep; if_cases K2; zify_cond_z K2.
      + enter_with (STEP _ _); [st_eq| f_equal; destruct (Z.ltb_spec mx l); lia| f_equal; destruct (Z.ltb_spec l mn); lia].
      + wstep. enter_with (STEP _ _); [st_eq| f_equal; destruct (Z.ltb_spec mx l); lia| f_equal; destruct (Z.ltb_spec l mn); lia].
    - wstep. wstep; if_cases K2; zify_cond_z K2.
      + enter_with (STEP _ _); [st_eq| f_equal; destruct (Z.ltb_spec mx l); lia| f_equal; destruct (Z.ltb_spec l mn); lia].
      + wstep. enter_with (STEP _ _); [st_eq| f_equal; destruct (Z.ltb_spec mx l); lia| f_equal; destruct (Z.ltb_spec l mn); lia].
  Qed.

  Lemma U0_sc_assign : forall (n t : nat) (code len : zarr) (lo : Z) (H : sdw) (m mf : word -> option byte)
      (t0 t1 t2 a0 a1 a2 a4 a5 a6 a7 s3 s6 t3 t4 t5 t6 : word),
    (Z.of_nat t + Z.of_nat n = nG)%Z -> (1 <= n)%nat ->
    (forall tt vv, 0 <= tt < nG -> 0 <= vv < A -> zdef len (258 * tt + vv) = true /\ 1 <= zget len (258 * tt + vv) <= 17)%Z ->
    u8arr s0segs m (E + 37708) (ovb len (jseg J 37708 1548) 1548) ->
    u32arr s0segs m (E + 39256) (ovw code (jseg J 39256 6192) 1548) ->
    rw_cells s0segs m (P + 888) (sd_hc H) ->
    h928 H = Z_to_bv 64 nG -> h960 H = Z_to_bv 64 (E + 37708) -> h968 H = Z_to_bv 64 A -> h984 H = Z_to_bv 64 A ->
    h992 H = NOT (E + 39256) -> h1000 H = Z_to_bv 64 (E + 39256) ->
    mem_inv s0segs m -> stk s0segs m lo P -> (lo + 16 <= P)%Z -> (CEIL <= lo)%Z ->
    munch Was mf m -> wmono s0segs mf m ->
    (forall m' (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 t3 t4 t5 t6 : word),
      u8arr s0segs m' (E + 37708) (ovb len (jseg J 37708 1548) 1548) ->
      u32arr s0segs m' (E + 39256) (ovw (sm_assign n code len A (Z.of_nat t)) (jseg J 39256 6192) 1548) ->
      rw_cells s0segs m' (P + 888) (sd_hc H) ->
      mem_inv s0segs m' -> stk s0segs m' lo P -> munch Was mf m' -> wmono s0segs mf m' ->
      evt s0segs Q (MS (CR t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 nG s3 s5 s6 t3 t4 t5 t6) F (Z_to_bv 64 112240) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (CR t0 t1 t2 a0 a1 a2 (Z_to_bv 64 (E + 39256)) a4 a5 a6 a7 (Z.of_nat t) s3 (Z_to_bv 64 A) s6 t3 t4 t5 t6)
                     F (Z_to_bv 64 111988) fc None m (seg_rom s0segs)).
  Proof using All.
    induction n as [|n IH]. { intros; lia. }
    intros t code len lo H m mf t0 t1 t2 a0 a1 a2 a4 a5 a6 a7 s3 s6 t3 t4 t5 t6 Ht Hn LENF LEN CODE HC HS28 HS60 HS68 HS84 HS92 HS00
           MI ST STK CLO MU WM K.
    openCX. unfold CEIL in CLO.
    pose proof (jseg_length J 37708 1548 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ6. pose proof (jseg_length J 39256 6192 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ7.
    cbn [sm_assign] in K.
    pose proof (sm_minmax_spec (Z.to_nat A) len (Z.of_nat t) 0 32 0 ltac:(lia) ltac:(lia)) as MM. cbv zeta in MM.
    destruct (sm_minmax (Z.to_nat A) len (Z.of_nat t) 0 32 0) as [mn mx] eqn:EMM. cbn [fst snd] in MM. cps_destruct MM as (M1 & M2 & M3 & M4).
    rewrite Z2Nat.id in M3, M4 by lia.
    destruct (M4 ltac:(intros j Hj; apply (proj2 (LENF (Z.of_nat t) j ltac:(lia) ltac:(lia))))) as [N1 N2].
    pose proof (M3 0%Z ltac:(lia)) as M30. pose proof (proj2 (LENF (Z.of_nat t) 0%Z ltac:(lia) ltac:(lia))) as L00.
    assert (MN : (1 <= mn <= 17)%Z) by lia. assert (MX : (1 <= mx <= 17)%Z) by lia.
    unfold sd_hc in HC. rewrite HS28, HS60, HS68, HS84, HS92, HS00 in HC.
    wstep. wstep; if_cases K0; zify_cond_z K0; [exfalso; revert K0; rewrite ?signed_lit by lia; lia|].
    urun_to 112036%Z.
    assert (V84 : frdW s0segs [] m (P + 984) [C8 (Z_to_bv 64 A)]).
    { eapply (frdW_cell_at s0segs _ _ (P + 888) _ 96); [apply frdW_intro; [exact HC| exact I]| reflexivity| lia]. }
    enter_with (U0_sc_minmax (Z.to_nat A) 0 (Z.of_nat t) 32 0 len [] m m);
      [st_eq| lia| lia| lia| lia| lia| lia| exact LENF| exact LEN| apply munch_refl| exact V84|].
    clear V84. cbv zeta. rewrite EMM. cbn [fst snd]. intros _ _.
    wstep; if_cases Kb1; zify_cond_z Kb1; [| exfalso; lia].
    wstep; if_cases Kb2; zify_cond_z Kb2; [exfalso; lia|].
    urun_to 147980%Z.
    eapply evt_cut.
    { eapply (U0_hbAssignCodes_Z _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m (E + 39256)%Z (E + 37708)%Z
                (258 * Z.of_nat t)%Z (258 * Z.of_nat t)%Z mn mx A 1548%Z 1548%Z lo P code len (jseg J 39256 6192) (jseg J 37708 1548));
        [ lia | f_equal; lia | f_equal; lia | reflexivity | reflexivity | reflexivity
        | exact CODE | exact LEN | exact MI | exact ST | lia
        | lia | lia | lia | lia | lia | lia | lia
        | clear - ME; Z.div_mod_to_equations; lia | lia | bz_ceil; bz_params; unfold CEIL; lia | lia | bz_ceil; bz_params; unfold CEIL; lia
        | unfold apart; lia | lia | lia
        | intros i Hi; destruct (LENF (Z.of_nat t) i ltac:(lia) Hi) as [D R]; split; [exact D| apply M3; lia] ]. }
    clear CODE MI ST. unfold asg_postZ.
    intros ms' PO; destruct_exs PO. destruct PO as [EQ [MUc [WMc [MI [ST CODE]]]]]; subst ms'.
    lazymatch type of MUc with munch _ m ?m' => transport_after_call s0segs m m' MUc WMc; clear MUc WMc; try clear m end.
    lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    wstep. wstep. wstep. wstep. wstep. wstep; if_cases Ke; zify_cond_z Ke.
    - enter_with (IH (S t) _ len lo H _ mf);
        [st_eq| lia| lia| exact LENF| exact LEN| exact CODE
        | unfold sd_hc; rewrite HS28, HS60, HS68, HS84, HS92, HS00; exact HC
        | exact HS28| exact HS60| exact HS68| exact HS84| exact HS92| exact HS00
        | exact MI| exact ST| lia| unfold CEIL; lia| exact MU| exact WM|].
      intros mm; intros *. replace (Z.of_nat (S t)) with (Z.of_nat t + 1)%Z by lia. apply K.
    - assert (n = 0)%nat by lia. subst n. cbn [sm_assign] in K.
      enter_with K;
        [st_eq| exact LEN| exact CODE| unfold sd_hc; rewrite HS28, HS60, HS68, HS84, HS92, HS00; exact HC| exact MI| exact ST| exact MU| exact WM].
  Qed.

  Lemma U0_smC_body : forall (c0 f0 p0 h0 w0 q0 : zarr) (m : word -> option byte) (H : sdw) (i16 : list byte) (lo : Z)
      (ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 : word),
    let e := est_C e0 c0 f0 p0 h0 w0 q0 in
    let it := smB_it e0 c0 f0 h0 w0 q0 in let nSel := smB_nsel e0 c0 f0 h0 w0 q0 in
    sd_facts e nG nSel ->
    u8arr s0segs m (E + 1704) (ovb (it_sel it) (jseg J 1704 18002) 18002) ->
    u8arr s0segs m (E + 19706) (ovb (e_selectorMtf e0) (jseg J 19706 18002) 18002) ->
    u8arr s0segs m (E + 37708) (ovb (it_len it) (jseg J 37708 1548) 1548) ->
    u32arr s0segs m (E + 39256) (ovw (e_code e0) (jseg J 39256 6192) 1548) ->
    rw_cells s0segs m (P + 888) (sd_hc H) ->
    h928 H = Z_to_bv 64 nG -> h960 H = Z_to_bv 64 (E + 37708) -> h968 H = Z_to_bv 64 A ->
    h976 H = Z_to_bv 64 nSel -> h984 H = Z_to_bv 64 A ->
    frdW s0segs WC m (P + 816) [C8 (Z_to_bv 64 (E + 1704))] -> frdW s0segs WC m (P + 824) [C8 (NOT (E + 1704))] ->
    u8arr s0segs m (P + 1044) i16 -> Z.of_nat (length i16) = 16%Z ->
    stk s0segs m lo P -> (lo + 16 <= P)%Z -> (CEIL <= lo)%Z -> mem_inv s0segs m ->
    rw_cells s0segs m E (EHEAD1 cx g e0) -> rw_cells s0segs m (E + 640) (EHEAD2 cx g e0) ->
    u8arr s0segs m A2 (zb8 (zbl (e_arr2 e0) (e_nblock e0) (e_bw e0)) ARR2_SIZE) ->
    u8arr s0segs m A1 (zb8 (e_arr1 e0) ARR1_SIZE) ->
    u8arr s0segs m (E + 128) (ovb (e_inUse e0) (jseg J 128 256) 256) ->
    (forall m' (i16' : list byte) (t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 : word),
       MA3 cx g e nG P m' (HX nSel H) i16' (e_bw e) m' ->
       h928 (HX nSel H) = Z_to_bv 64 nG -> h944 (HX nSel H) = Z_to_bv 64 nSel -> h976 (HX nSel H) = Z_to_bv 64 nSel ->
       h960 (HX nSel H) = Z_to_bv 64 (E + 37708) -> h968 (HX nSel H) = Z_to_bv 64 A ->
       Z.of_nat (length i16') = 16%Z ->
       u8arr s0segs m' A1 (zb8 (e_arr1 e) ARR1_SIZE) ->
       u8arr s0segs m' (E + 128) (ovb (e_inUse e) (jseg J 128 256) 256) ->
       u8arr s0segs m' (E + 19706) (ovb (e_selectorMtf e) (jseg J 19706 18002) 18002) ->
       u8arr s0segs m' (E + 1704) (ovb (e_selector e) (jseg J 1704 18002) 18002) ->
       u8arr s0segs m' (E + 37708) (ovb (e_len e) (jseg J 37708 1548) 1548) ->
       u32arr s0segs m' (E + 39256) (ovw (e_code e) (jseg J 39256 6192) 1548) ->
       stk s0segs m' lo P -> mem_inv s0segs m' -> munch WC m m' -> wmono s0segs m m' ->
       evt s0segs Q (MS (mkR (NOT (E + 39256)) cP gp tp t0 t1 t2 cE s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (NOT (E + 37708)) s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 112240) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra cP gp tp t0 t1 t2 cE s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (NOT (E + 37708)) s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 111668) fc None m (seg_rom s0segs)).
  Proof using All.
    intros c0 f0 p0 h0 w0 q0 m H i16 lo ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6.
    cbv zeta. intros SDF SEL SELM LEN CODE HC HS28 HS60 HS68 HS76 HS84 V816 V824 I16 L16 ST STK CLO MI EH1 EH2 AR2 AR1 INU K.
    openCX. unfold CEIL in CLO. assert (HAd : A = (e_nInUse e0 + 2)%Z) by reflexivity.
    set (it := smB_it e0 c0 f0 h0 w0 q0) in *. set (nSel := smB_nsel e0 c0 f0 h0 w0 q0) in *.
    pose proof SDF as SF. unfold sd_facts in SF. cbv zeta in SF.
    cbn [e_nInUse e_nMTF e_arr1 e_inUse e_selectorMtf e_selector e_len e_code est_C] in SF.
    cps_destruct SF as (FA & FG & FS & FM & F35 & FZB & FMV & FIU & FSM & FSEL & FLEN & FCODE & FCNT).
    change (e_nInUse e0 + 2)%Z with A in FA, FMV, FLEN, FCODE. fold it in FSEL, FLEN.
    unfold EHEAD1 in EH1. unfold EHEAD2 in EH2.
    pose proof (hc_rd976 m H HC) as RD76. rewrite HS76 in RD76.
    unfold sd_hc in HC. rewrite HS28, HS60, HS68, HS76, HS84 in HC.
    pose proof (munch_refl WC m) as MU0. pose proof (wmono_refl s0segs m) as WM0.
    wstep. clear RD76.
    wstep. wstep. wstep. wstep; if_cases K0; zify_cond_z K0; [| exfalso; revert K0; rewrite ?signed_lit by lia; lia].
    wstep. wstep. wstep.
    lazymatch type of I16 with u8arr _ ?mm _ _ =>
      pose proof (ovb_init s0segs mm (P + 1044) 16 i16 ltac:(replace (Z.to_nat 16) with (length i16) by lia; exact (rw_cells_of_u8arr s0segs mm _ i16 I16)) ltac:(lia)) as POS end.
    clear I16.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (U0_sc_posinit ra s1 s2 s3 s4 s5 s6 s7 s8 s10 s11 t5 t6 (Z.to_nat nG) 0 znew i16 mm mm);
        [st_eq| lia| lia| lia| exact POS| exact MI| apply munch_refl| apply wmono_refl
        | eapply (frdW_cell_at s0segs _ _ (P + 888) _ 40); [apply frdW_intro; [exact HC| cbn [disjoint_from]; simpl_sizes; Lib.Step.slia]| reflexivity| lia] |] end.
    clear POS MI. intros mq1 POS MI MU1 WM1.
    lazymatch type of MU1 with munch _ ?ma ?mb => transport_after_call s0segs ma mb MU1 WM1 end. clear MU1 WM1.
    wstep. wstep; if_cases K1; zify_cond_z K1; [exfalso; revert K1; rewrite ?signed_lit by lia; lia|].
    wstep.
    assert (PD0 : zdef (yy_init (Z.to_nat nG) znew 0) 0 = true).
    { rewrite yy_init_def. apply Bool.orb_true_iff. left. apply Bool.andb_true_iff. split; [apply Z.leb_le| apply Z.ltb_lt]; lia. }
    assert (PV0 : zget (yy_init (Z.to_nat nG) znew 0) 0 = 0%Z).
    { rewrite yy_init_get. replace ((0 <=? 0) && (0 <? 0 + Z.of_nat (Z.to_nat nG)))%bool with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia). reflexivity. }
    pose proof (ovb_read1 s0segs mq1 (P + 1044) _ i16 16 0 _ POS ltac:(lia) PD0 ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. rewrite PV0. cbv beta. rewrite (unsigned_lit8 0) by lia.
    urun_to 111788%Z.
    assert (PP0 : PP nG (yy_init (Z.to_nat nG) znew 0)) by (apply PP_init; lia).
    assert (PAG0 : PAGREE (yy_init (Z.to_nat nG) znew 0) (yy_init (Z.to_nat nG) p0 0)).
    { intros k Hk. rewrite yy_init_def, !yy_init_get.
      replace ((0 <=? k) && (k <? 0 + Z.of_nat (Z.to_nat nG)))%bool with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia). split; reflexivity. }
    assert (PPm : PP nG (yy_init (Z.to_nat nG) p0 0)) by (apply PP_init; lia).
    assert (PV0m : zget (yy_init (Z.to_nat nG) p0 0) 0 = 0%Z).
    { rewrite yy_init_get. replace ((0 <=? 0) && (0 <? 0 + Z.of_nat (Z.to_nat nG)))%bool with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia). reflexivity. }
    enter_with (U0_sc_mtf ra s1 s2 s3 s4 s5 s6 s7 s8 s10 s11 t5 t6 (Z.to_nat nSel) 0 (yy_init (Z.to_nat nG) p0 0) (yy_init (Z.to_nat nG) znew 0) (it_sel it) (e_selectorMtf e0) i16 mq1 mq1 nSel);
      [st_eq| lia| lia| lia| lia| exact PPm| exact PAG0| exact FSEL| exact SEL| exact SELM| exact POS| exact MI| apply munch_refl| apply wmono_refl
      | eapply frdW_sub; [exact V816| exact MU0| u_sub_fp] | eapply frdW_sub; [exact V824| exact MU0| u_sub_fp] |].
    clear SEL SELM POS MI. intros mq2 pm2 yt0 yt1 yt2 ya0 ya7 yt3. cbv zeta. intros PP2 PAG2 SEL SELM POS MI MU2 WM2.
    lazymatch type of MU2 with munch _ ?ma ?mb => transport_after_call s0segs ma mb MU2 WM2 end. clear MU2 WM2.
    change (sm_selmtf (Z.to_nat nSel) (yy_init (Z.to_nat nG) p0 0) (it_sel it) (e_selectorMtf e0) 0) with (smC_pm e0 c0 f0 p0 h0 w0 q0) in SELM.
    pose proof (u8arr_store_ok s0segs mq2 (P + 1044) _ 0 _ POS ltac:(rewrite ovb_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO.
    wstep. store_addr (P + 1044 + 0)%Z. ovb_store1 POS 0%Z.
    do 19 (wstep; lit_store).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    enter_with (U0_sc_assign (Z.to_nat nG) 0%nat (e_code e0) (it_len it) lo (HX nSel H) mm mm);
      [st_eq| lia| lia| exact FLEN| exact LEN| exact CODE
      | unfold sd_hc; cbn [h888 h896 h904 h912 h920 h928 h936 h944 h952 h960 h968 h976 h984 h992 h1000 h1008 h1016 h1024 h1032];
        rewrite HS28, HS60, HS68, HS76, HS84; exact HC
      | exact HS28| exact HS60| exact HS68| exact HS84| reflexivity| reflexivity
      | exact MI| exact ST| lia| unfold CEIL; lia| apply munch_refl| apply wmono_refl|] end.
    clear LEN CODE HC MI ST. intros mq4 z0 z1 z2 za0 za1 za2 za3 za4 za5 za6 za7 zs3 zs5 zs6 z3 z4 z5 z6 LEN CODE HC MI ST MU4 WM4.
    lazymatch type of MU4 with munch _ ?ma ?mb => transport_after_call s0segs ma mb MU4 WM4 end. clear MU4 WM4.
    change (sm_assign (Z.to_nat nG) (e_code e0) (it_len it) A (Z.of_nat 0)) with (smC_code e0 c0 f0 h0 w0 q0) in CODE.
    enter_with (K mq4 (ovb (wr8 pm2 0 (bv_unsigned ya0)) i16 16));
      [st_eq
      | unfold MA3; split; [exact EH1|]; split; [exact EH2|]; split; [exact AR2|]; split; [exact HC|]; split; [exact POS|];
        split; [exact MI|]; split; [apply munch_refl| apply wmono_refl]
      | exact HS28| reflexivity| exact HS76| exact HS60| exact HS68| rewrite ovb_length; lia
      | exact AR1| exact INU| exact SELM| exact SEL| exact LEN| exact CODE| exact ST| exact MI| exact MU0| exact WM0].
  Qed.
End SDC.
End ACeilS1.
