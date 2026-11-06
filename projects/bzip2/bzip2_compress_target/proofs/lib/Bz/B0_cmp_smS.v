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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCStream BzCState BzCMtf BzCHuff BzArrD BzCRebuildF CmpMem CmpCut CmpCutSM CmpCutSmA CmpCutSmB CmpCutSmC BzCFactsSmA BzCFactsGm BzCFactsSd BzCFactsSd2 CmpFsKit CmpHmKit CmpSmKit CmpSmKit2.
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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_smV.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import B0_cmp_asg B0_cmp_msV B0_cmp_sdV.

(* [comment removed for export] *)
Ltac lin16 H := lazymatch type of H with (?x mod 16 = 0)%Z =>
  let E := fresh "E16" in pose proof (Z.div_mod x 16 ltac:(lia)) as E; rewrite H, Z.add_0_r in E; clear H;
  let q := fresh "q16" in set (q := (x / 16)%Z) in E; clearbody q; rename E into H end.
(* [comment removed for export] *)
Ltac openCX_a CX :=
  let XF0 := ident:(XF0) in let XF1 := ident:(XF1) in let Xb0 := ident:(Xb0) in let Xb1 := ident:(Xb1) in
  let Xf0 := ident:(Xf0) in let Xf1 := ident:(Xf1) in let ME := ident:(ME) in let MA1 := ident:(MA1) in let MA2 := ident:(MA2) in let MF := ident:(MF) in
  let Mb := ident:(Mb) in let Mf := ident:(Mf) in let LJb := ident:(LJb) in
  let H := fresh "CXL" in pose proof CX as H; bz_ceil; bz_params; unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in H; cbv zeta in H;
  cps_destruct H as (?XE0 & ?XE1 & ?XA10 & ?XA11 & ?XA20 & ?XA21 & ?XF0 & ?XF1 & ?Xb0 & ?Xb1 & ?Xf0 & ?Xf1 & ?ME & ?MA1 & ?MA2 & ?MF & ?Mb & ?Mf & ?LJ & ?LJb);
  clear XF0 XF1 Xb0 Xb1 Xf0 Xf1 MA1 MA2 MF Mb Mf LJb; lin16 ME.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

(* [comment removed for export] *)
Definition asg_postZ (ra : word) (spz : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (Ecode : Z) (code' : zarr) (Jc : list byte) (NC lo : Z) (W : list (Z * Z))
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR ra (Z_to_bv 64 spz) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom b0segs)
    /\ munch W m m' /\ wmono b0segs m m' /\ mem_inv b0segs m' /\ stk b0segs m' lo spz
    /\ u32arr b0segs m' Ecode (ovw code' Jc NC).

Lemma B0_hbAssignCodes_Z : forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (Ecode Elen cb lb minLen maxLen alphaSize NC NL lo spz : Z) (code len : zarr) (Jc Jl : list byte),
  (0 <= spz < 18446744073709551616)%Z ->
  let W := [(Ecode + 4 * cb, Ecode + 4 * (cb + alphaSize)); (spz - 32, spz)]%Z in
  a0 = Z_to_bv 64 (Ecode + 4 * cb) -> a1 = Z_to_bv 64 (Elen + lb) ->
  a2 = Z_to_bv 64 minLen -> a3 = Z_to_bv 64 maxLen -> a4 = Z_to_bv 64 alphaSize ->
  u32arr b0segs m Ecode (ovw code Jc NC) -> u8arr b0segs m Elen (ovb len Jl NL) -> mem_inv b0segs m ->
  stk b0segs m lo spz -> (lo + 32 <= spz)%Z ->
  (0 <= cb)%Z -> (cb + alphaSize <= NC)%Z -> (0 <= lb)%Z -> (lb + alphaSize <= NL)%Z -> (0 <= alphaSize <= 258)%Z ->
  (1 <= minLen <= 32)%Z -> (0 <= maxLen <= 17)%Z -> (Ecode mod 4 = 0)%Z -> (0 < Ecode)%Z -> (Ecode + 4 * NC <= CEIL)%Z -> (0 < Elen)%Z -> (Elen + NL <= CEIL)%Z ->
  apart Ecode (4 * NC) Elen NL ->
  (spz <= Ecode \/ Ecode + 4 * NC <= spz - 32)%Z -> (spz <= Elen \/ Elen + NL <= spz - 32)%Z ->
  (forall i, 0 <= i < alphaSize -> zdef len (lb + i) = true /\ minLen <= zget len (lb + i) <= maxLen)%Z ->
  aconsts B0C m -> (0x62b000 <= lo)%Z -> (0x62b000 <= Ecode)%Z -> (0x62b000 <= Elen)%Z ->
  shzW b0segs W m Ecode (Ecode + 4 * NC) -> shzW b0segs W m Elen (Elen + NL) ->
  evt b0segs (asg_postZ ra spz gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
              Ecode (hbAssignCodes code len cb lb minLen maxLen alphaSize) Jc NC lo W m)
      (MS (mkR ra (Z_to_bv 64 spz) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xa8d70) fc None m (seg_rom b0segs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
         Ecode Elen cb lb minLen maxLen alphaSize NC NL lo spz code len Jc Jl Hsp.
  pose proof (B0_hbAssignCodes ra (Z_to_bv 64 spz) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
                         Ecode Elen cb lb minLen maxLen alphaSize NC NL lo code len Jc Jl) as G.
  cbv zeta in G. cbn [aci_segs aci_c ci_segs B0C aci_hi ci_hi ci_hbAssignCodes] in G. unfold hbAssignCodes_post in G.
  rewrite (unsigned_lit spz) in G by lia. cbv zeta. exact G.
Qed.

Section SC3.
  Variables (cx : cctx) (e0 : est) (Q : machine_state -> Prop).
  Variables (gp tp s0 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (P SHE FB SHF : Z).
  Hypothesis CX : cctx_ok cx. Hypothesis SEP : cctx_sep cx.
  Hypothesis CEP : (CEIL <= P)%Z. Hypothesis PHI : (P + 1712 <= 18446744073709551616)%Z.
  Hypothesis EIMG : (0x62b000 <= c_E cx)%Z.   (* [comment removed for export] *)
  Hypothesis FBL : (0 < FB)%Z. Hypothesis FBH : (FB + 160 <= CEIL)%Z.
  Hypothesis SEFB : id ((c_E cx + 55768 <= FB)%Z \/ (FB + 160 <= c_E cx)%Z).
  Hypothesis SHL : (SH_LO <= SHF)%Z. Hypothesis SHH : (SHF + 20 <= SH_HI)%Z. Hypothesis AF : sanchor FB SHF.
  Hypothesis SESH : id ((c_E cx + 55768 <= SHF)%Z \/ (SHF + 20 <= c_E cx)%Z).
  Hypothesis SFSH : id ((FB + 160 <= SHF)%Z \/ (SHF + 20 <= FB)%Z).
  Hypothesis SPSH : id ((SHF + 20 <= P)%Z \/ (P + 1712 <= SHF)%Z).
  (* [comment removed for export] *)
  Hypothesis OFFE : id ((c_E cx + 55768 <= SH_LO)%Z \/ (SH_HI <= c_E cx)%Z).
  Hypothesis OFFF : id ((FB + 160 <= SH_LO)%Z \/ (SH_HI <= FB)%Z).
  Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation J := (c_J cx).
  Notation A := (sm_alpha e0). Notation nG := (smA_ng e0).
  Hypothesis HA : (3 <= A <= 258)%Z. Hypothesis HNG : (2 <= nG <= 6)%Z.
  Notation cSB := (Z_to_bv 64 2147450880). Notation cP := (Z_to_bv 64 P).
  Ltac openCX := openCX_a CX.
  (* [comment removed for export] *)
  Ltac bzl :=
    repeat match goal with
    | |- context [Z.shiftr ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftr_div a k) by lia
    | |- context [Z.shiftl ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftl_mul a k) by lia
    | |- context [Z.modulo ?e 18446744073709551616] => rewrite (Z.mod_small e 18446744073709551616) by lia
    | |- context [bv_swrap 32 ?e] => rewrite (swrap32_id e) by lia
    end; zb_fold_lits.
  Ltac lstep := zstep; bzl.
  Notation NOT z := (Z_to_bv 64 (18446744073709551615 - z)).
  Notation Wpos := [(FB + 128, FB + 134)]%Z.

  (* [comment removed for export] *)
  Definition PAGREE (pm p : zarr) : Prop := forall k, (1 <= k < nG)%Z -> zdef pm k = true /\ zget pm k = zget p k.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma B0_sc_posinit : forall (n : nat) (i : Z) (pm : zarr) (i6 : list byte) (m mf : word -> option byte)
      (ra t0 t1 t2 a0 a3 a4 a5 a6 a7 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3 t4 t5 t6 : word),
    (i + Z.of_nat n = nG)%Z -> (0 <= i)%Z -> (1 <= n)%nat ->
    u8arr b0segs m (FB + 128) (ovb pm i6 6) ->
    mem_inv b0segs m -> munch Wpos mf m -> wmono b0segs mf m ->
    frdW b0segs Wpos mf (P + 80) [C8 (Z_to_bv 64 (FB + 128))] -> frdW b0segs Wpos mf (P + 1480) [C8 (Z_to_bv 64 nG)] ->
    shpW b0segs Wpos mf (FB + 128) (FB + 134) ->
    (forall m' (a0 a3 a4 : word),
      u8arr b0segs m' (FB + 128) (ovb (yy_init n pm i) i6 6) ->
      mem_inv b0segs m' -> munch Wpos mf m' -> wmono b0segs mf m' ->
      evt b0segs Q (MS (mkR ra cP gp tp t0 t1 t2 s0 cP a0 (Z_to_bv 64 nG) (Z_to_bv 64 6) a3 a4 a5 a6 a7 cSB x3 x4 x5 x6 x7 x8 x9 x10 x11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x93b70) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR ra cP gp tp t0 t1 t2 s0 cP a0 (Z_to_bv 64 i) (Z_to_bv 64 6) a3 a4 a5 a6 a7 cSB x3 x4 x5 x6 x7 x8 x9 x10 x11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x93b30) fc None m (seg_rom b0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros i pm i6 m mf ra t0 t1 t2 a0 a3 a4 a5 a6 a7 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3 t4 t5 t6 Hi Hi0 Hn POS MI MU WM V80 V1480 SHp K.
    openCX. pose proof (ovb_length_nat pm i6 6) as LP.
    rewrite yy_init_S in K.
    (* [comment removed for export] *)
    brun. pose proof (V80 m MU) as RO. wstep. clear RO.
    (* [comment removed for export] *)
    brun_to 0x93b48%Z. ack_rd (FB + 128 + i)%Z 1%Z. ack_merge.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u8arr_store_ok b0segs mm (FB + 128) _ i _ POS ltac:(rewrite ovb_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO end.
    lstep. store_addr (FB + 128 + i)%Z. ovb_store1 POS i.
    replace (wr8 pm i (bv_unsigned (Z_to_bv 64 i))) with (zset pm i i) in POS by (unfold wr8; rewrite unsigned_lit by lia; rewrite Z.mod_small by lia; reflexivity).
    (* [comment removed for export] *)
    lstep.
    lazymatch goal with MU' : munch _ _ ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (V1480 mm MU') as RO end. wstep. clear RO.
    lstep; if_cases Ke; zify_cond_z Ke.
    - enter_with (IH (i + 1)%Z _ i6 _ mf); [st_eq| lia| lia| lia| exact POS| assumption| exact MU| exact WM| exact V80| exact V1480| exact SHp| exact K].
    - assert (n = 0)%nat by lia. subst n. cbn [yy_init] in K.
      lstep.
      enter_with (K _ _ _ _); [st_eq| exact POS| assumption| exact MU| exact WM].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section MTF.
  Variables (x3 x5 x6 x7 x8 x9 x10 x11 : word).
  Notation MRb ra t0 t1 t2 a0 a1 a2 t3 t4 t5 nSel :=
    (mkR ra cP gp tp t0 t1 t2 s0 cP a0 a1 a2 (Z_to_bv 64 (FB + 129)) (Z_to_bv 64 18002) (Z_to_bv 64 (E + 19706)) (NOT (E + 19706)) (Z_to_bv 64 (-5))
         cSB x3 (Z_to_bv 64 E) x5 x6 x7 x8 x9 x10 x11 t3 t4 t5 (Z_to_bv 64 nSel)).

  (* [comment removed for export] *)
  Lemma B0_sc_search : forall (n : nat) (j mm : Z) (pos0 pm : zarr) (i6 : list byte) (m mf : word -> option byte) (nSel ll : Z)
      (ra a1 a2 t4 t5 : word),
    (mm - j = Z.of_nat n)%Z -> (0 <= j <= mm)%Z -> (mm < nG)%Z ->
    (forall k, 0 <= k < nG -> 0 <= zget pos0 k < nG)%Z -> (0 <= ll < nG)%Z ->
    zget pos0 mm = ll -> (forall k, j <= k < mm -> zget pos0 k <> ll)%Z ->
    (forall k, 1 <= k <= j -> zdef pm k = true /\ zget pm k = zget pos0 (k - 1))%Z ->
    (forall k, j < k < nG -> zdef pm k = true /\ zget pm k = zget pos0 k)%Z ->
    u8arr b0segs m (FB + 128) (ovb pm i6 6) ->
    mem_inv b0segs m -> munch Wpos mf m -> wmono b0segs mf m ->
    shpW b0segs Wpos mf (FB + 128) (FB + 134) ->
    (forall m' pm' (t4' t5' : word),
      (forall k, 1 <= k <= mm -> zdef pm' k = true /\ zget pm' k = zget pos0 (k - 1))%Z ->
      (forall k, mm < k < nG -> zdef pm' k = true /\ zget pm' k = zget pos0 k)%Z ->
      u8arr b0segs m' (FB + 128) (ovb pm' i6 6) ->
      mem_inv b0segs m' -> munch Wpos mf m' -> wmono b0segs mf m' ->
      evt b0segs Q (MS (MRb ra (Z_to_bv 64 ll) (Z_to_bv 64 (- mm)) (Z_to_bv 64 (FB + 129 + mm)) (Z_to_bv 64 (FB + 129 + mm)) a1 a2 (Z_to_bv 64 ll) t4' t5' nSel)
                       F (Z_to_bv 64 0x93c38) fc None m' (seg_rom b0segs))) ->
    (j < mm)%Z ->
    evt b0segs Q (MS (MRb ra (Z_to_bv 64 ll) (Z_to_bv 64 (- j)) (Z_to_bv 64 (FB + 129 + j)) (Z_to_bv 64 (FB + 129 + j)) a1 a2 (Z_to_bv 64 (zget pos0 j)) t4 t5 nSel)
                     F (Z_to_bv 64 0x93bf4) fc None m (seg_rom b0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros j mm pos0 pm i6 m mf nSel ll ra a1 a2 t4 t5 Hn Hj Hmm PB Hll Em NOT SH REST POS MI MU WM SHp K LT.
    openCX. pose proof (ovb_length_nat pm i6 6) as LP.
    pose proof (PB j ltac:(lia)) as Pj. pose proof (PB (j + 1)%Z ltac:(lia)) as Pj1.
    destruct (REST (j + 1)%Z ltac:(lia)) as [D1 V1].
    (* [comment removed for export] *)
    lstep; if_cases Kg; zify_cond_z Kg.
    2:{ exfalso. change 18446744073709551615%Z with (Z.ones 64) in Kg. rewrite Z.land_ones in Kg by lia.
        destruct (Z.eq_dec j 0) as [->|NZ]; [cbn in Kg; lia|].
        rewrite <- (Z.mod_add (- j) 1 (2^64)%Z) in Kg by lia. rewrite Z.mod_small in Kg by lia. lia. }
    (* [comment removed for export] *)
    brun_to 0x93c04%Z. ack_rd (FB + 129 + j)%Z 1%Z. ack_merge.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm0 _) =>
      pose proof (ovb_read1 b0segs mm0 (FB + 128) pm i6 6 (j + 1) _ POS ltac:(lia) D1 ltac:(unfold wa; f_equal; lia)) as RD end.
    lstep. clear RD. rewrite V1. cbv beta. rewrite (unsigned_lit8 (zget pos0 (j + 1))) by lia.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm0 _) =>
      pose proof (u8arr_store_ok b0segs mm0 (FB + 128) _ (j + 1) _ POS ltac:(rewrite ovb_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO end.
    lstep. store_addr (FB + 128 + (j + 1))%Z. ovb_store1 POS (j + 1)%Z.
    replace (wr8 pm (j + 1) (bv_unsigned (Z_to_bv 64 (zget pos0 j)))) with (zset pm (j + 1) (zget pos0 j)) in POS by (unfold wr8; rewrite unsigned_lit by lia; rewrite Z.mod_small by lia; reflexivity).
    (* [comment removed for export] *)
    lstep. lstep. lstep. lstep. lstep; if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      assert (j + 1 < mm)%Z by (destruct (Z.eq_dec (j + 1) mm) as [EQ|]; [exfalso; rewrite <- EQ in Em; lia| lia]).
      enter_with (IH (j + 1)%Z mm pos0 _ i6 _ mf nSel ll);
        [st_eq| lia| lia| lia| exact PB| lia| exact Em| intros k Hk; apply NOT; lia| | | exact POS| assumption| exact MU| exact WM| exact SHp| exact K| lia].
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
  Notation Wmtf := [(E + 19706, E + 37708); (FB + 128, FB + 134)]%Z.
  Lemma B0_sc_mtf : forall (n : nat) (i : Z) (Pm pm sel sm : zarr) (i6 : list byte) (m mf : word -> option byte) (nSel : Z)
      (ra t0 t1 t2 a0 t3 t4 t5 : word),
    (i + Z.of_nat n = nSel)%Z -> (0 <= i)%Z -> (1 <= n)%nat -> (nSel <= 18002)%Z ->
    PP nG Pm -> PAGREE pm Pm ->
    (forall k, 0 <= k < nSel -> zdef sel k = true /\ 0 <= zget sel k < nG)%Z ->
    u8arr b0segs m (E + 1704) (ovb sel (jseg J 1704 18002) 18002) ->
    u8arr b0segs m (E + 19706) (ovb sm (jseg J 19706 18002) 18002) ->
    u8arr b0segs m (FB + 128) (ovb pm i6 6) ->
    mem_inv b0segs m -> munch Wmtf mf m -> wmono b0segs mf m ->
    frdW b0segs Wmtf mf (P + 1384) [C8 (Z_to_bv 64 (E + 1704))] -> frdW b0segs Wmtf mf (P + 1392) [C8 (NOT (E + 1704))] ->
    shzW b0segs Wmtf mf E (E + ESTATE_SIZE) -> shpW b0segs Wmtf mf (FB + 128) (FB + 134) ->
    (forall m' pm' (t0 t1 t2 a0 a1 t3 t4 t5 : word),
      let r := sm_selmtf n Pm sel sm i in
      PP nG (fst r) -> PAGREE pm' (fst r) ->
      u8arr b0segs m' (E + 1704) (ovb sel (jseg J 1704 18002) 18002) ->
      u8arr b0segs m' (E + 19706) (ovb (snd r) (jseg J 19706 18002) 18002) ->
      u8arr b0segs m' (FB + 128) (ovb pm' i6 6) ->
      mem_inv b0segs m' -> munch Wmtf mf m' -> wmono b0segs mf m' ->
      evt b0segs Q (MS (MRb ra t0 t1 t2 a0 a1 (Z_to_bv 64 nSel) t3 t4 t5 nSel) F (Z_to_bv 64 0x93c84) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (MRb ra t0 t1 t2 a0 (Z_to_bv 64 (zget Pm 0)) (Z_to_bv 64 i) t3 t4 t5 nSel) F (Z_to_bv 64 0x93ba8) fc None m (seg_rom b0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros i Pm pm sel sm i6 m mf nSel ra t0 t1 t2 a0 t3 t4 t5
           Hi Hi0 Hn HnS PPH PAG SELOK SEL SELM POS MI MU WM V1384 V1392 SHe SHp K.
    openCX. unfold ESTATE_SIZE in SHe.
    pose proof (jseg_length J 1704 18002 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ4. pose proof (ovb_length_nat sel (jseg J 1704 18002) 18002) as LS4.
    pose proof (jseg_length J 19706 18002 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ5. pose proof (ovb_length_nat sm (jseg J 19706 18002) 18002) as LS5.
    pose proof (ovb_length_nat pm i6 6) as LP.
    destruct (SELOK i ltac:(lia)) as [Dsi Rsi]. destruct PPH as [P1 P2]. pose proof (P1 0%Z ltac:(lia)) as P00.
    (* [comment removed for export] *)
    cbn [sm_selmtf] in K.
    cps_destruct (first_occ Pm (zget sel i) nG (P2 _ Rsi)) as (mm & Hmm & Emm & NOT).
    pose proof (pos_search_spec 8 Pm Pm (zget sel i) 0 mm nG ltac:(lia) ltac:(lia) ltac:(lia) Emm ltac:(intros k Hk; apply NOT; lia)
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
    (* [comment removed for export] *)
    lstep; if_cases Kg1; zify_cond_z Kg1; [|exfalso; lia].
    pose proof (V1392 m MU) as RO. lstep. clear RO.
    lstep; if_cases Kg2; zify_cond_z Kg2; [|exfalso; lia].
    pose proof (V1384 m MU) as RO. lstep. clear RO.
    (* [comment removed for export] *)
    brun_to 0x93bd4%Z.
    pose proof (ovb_read1 b0segs m (E + 1704) sel (jseg J 1704 18002) 18002 i _ SEL ltac:(lia) Dsi ltac:(unfold wa; f_equal; lia)) as RD.
    lstep. clear RD. cbv beta. rewrite (unsigned_lit8 (zget sel i)) by lia.
    (* [comment removed for export] *)
    assert (K8 : forall m1 pm1 (xt0 xt2 xa0 xt3 xt4 xt5 : word),
      (forall k, 1 <= k <= mm -> zdef pm1 k = true /\ zget pm1 k = zget Pm (k - 1))%Z ->
      (forall k, mm < k < nG -> zdef pm1 k = true /\ zget pm1 k = zget Pm k)%Z ->
      u8arr b0segs m1 (FB + 128) (ovb pm1 i6 6) ->
      u8arr b0segs m1 (E + 19706) (ovb sm (jseg J 19706 18002) 18002) ->
      u8arr b0segs m1 (E + 1704) (ovb sel (jseg J 1704 18002) 18002) ->
      mem_inv b0segs m1 -> munch Wmtf mf m1 -> wmono b0segs mf m1 ->
      evt b0segs Q (MS (MRb ra xt0 (Z_to_bv 64 mm) xt2 xa0 (Z_to_bv 64 (zget sel i)) (Z_to_bv 64 i) xt3 xt4 xt5 nSel) F (Z_to_bv 64 0x93c40) fc None m1 (seg_rom b0segs))).
    { intros m1 pm1 xt0 xt2 xa0 xt3 xt4 xt5 SH1 REST1 POS1 SELM1 SEL1 MI1 MU1 WM1.
      pose proof (ovb_length_nat pm1 i6 6) as LP1.
      (* [comment removed for export] *)
      lstep; if_cases Kg3; zify_cond_z Kg3; [|exfalso; lia].
      brun_to 0x93c60%Z.
      pose proof (u8arr_store_ok b0segs m1 (E + 19706) _ i _ SELM1 ltac:(rewrite ovb_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO.
      lstep. store_addr (E + 19706 + i)%Z. ovb_store1 SELM1 i.
      replace (wr8 sm i (bv_unsigned (Z_to_bv 64 mm))) with (zset sm i mm) in SELM1 by (unfold wr8; rewrite unsigned_lit by lia; rewrite Z.mod_small by lia; reflexivity).
      assert (PAG1 : PAGREE pm1 P1n).
      { intros k Hk. subst P1n. rewrite zget_zset_other by lia.
        destruct (Z.le_gt_cases k mm) as [L|L]; [rewrite SH by lia; apply SH1; lia| rewrite REST by lia; apply REST1; lia]. }
      (* [comment removed for export] *)
      lstep; if_cases Ke; zify_cond_z Ke.
      - enter_with (IH (i + 1)%Z P1n pm1 sel (zset sm i mm) i6 _ mf nSel);
          [st_eq| lia| lia| lia| lia| exact PP'| exact PAG1| exact SELOK| exact SEL1| exact SELM1| exact POS1| assumption| exact MU1| exact WM1| exact V1384| exact V1392| exact SHe| exact SHp| exact K].
        subst P1n. rewrite zget_zset_same. reflexivity.
      - assert (n = 0)%nat by lia. subst n. cbn [sm_selmtf] in K.
        lstep.
        enter_with (K _ pm1 _ _ _ _ _ _ _ _); [st_eq| exact PP'| exact PAG1| exact SEL1| exact SELM1| exact POS1| assumption| exact MU1| exact WM1]. }
    (* [comment removed for export] *)
    lstep; if_cases Kq; zify_cond_z Kq.
    - (* [comment removed for export] *)
      assert (M1 : (0 < mm)%Z) by (destruct (Z.eq_dec mm 0) as [EQ|]; [exfalso; rewrite EQ in Emm; lia| lia]).
      lstep. lstep. lstep. lstep.
      enter_with (B0_sc_search (Z.to_nat mm) 0 mm Pm pm i6 m m nSel (zget sel i));
        [st_eq| lia| lia| lia| exact P1| lia| exact Emm| intros k Hk; apply NOT; lia| intros; lia| intros k Hk; apply PAG; lia
        | exact POS| exact MI| apply munch_refl| apply wmono_refl| eapply shpW_sub; [exact SHp| exact MU| sub_fp_solve| lia| lia]| | lia].
      clear POS MI. intros m1 pm1 xt4 xt5 SH1 REST1 POS1 MI1 MU1 WM1.
      transport_after_call b0segs m m1 MU1 WM1. clear MU1 WM1.
      (* [comment removed for export] *)
      lstep. lstep.
      replace (0 - Z.land (- mm) 18446744073709551615)%Z with (mm - 18446744073709551616)%Z.
      2:{ change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia. rewrite <- (Z.mod_add (- mm) 1 (2^64)%Z) by lia. rewrite Z.mod_small by lia. lia. }
      rewrite <- (Z_to_bv_mod64 (mm - 18446744073709551616)).
      replace ((mm - 18446744073709551616) mod 2 ^ 64)%Z with mm by (rewrite <- (Z.mod_add _ 1 (2^64)%Z) by lia; rewrite Z.mod_small by lia; lia).
      enter_with (K8 m1 pm1 _ _ _ _ _ _); [st_eq| exact SH1| exact REST1| exact POS1| exact SELM| exact SEL| exact MI1| exact MU| exact WM].
    - (* [comment removed for export] *)
      assert (M0 : mm = 0%Z) by (destruct (Z.eq_dec mm 0) as [|NE]; [assumption| exfalso; apply (NOT 0%Z); lia]).
      lstep. lstep. subst mm.
      enter_with (K8 m pm _ _ _ _ _ _); [st_eq| intros; lia| intros k Hk; apply PAG; lia| exact POS| exact SELM| exact SEL| exact MI| exact MU| exact WM].
  Qed.
  End MTF.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation LR t := (E + 37708 + 258 * t)%Z.
  Notation CRb ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t s7 s8 s10 t3 t4 t5 t6 :=
    (mkR ra cP gp tp t0 t1 t2 s0 cP a0 a1 a2 a3 a4 a5 a6 a7 cSB (Z_to_bv 64 t) (Z_to_bv 64 258) (Z_to_bv 64 3004) (Z_to_bv 64 1032) s7 s8
         (Z_to_bv 64 (LR t)) s10 (Z_to_bv 64 6) t3 t4 t5 t6).

  (* [comment removed for export] *)
  Lemma B0_sc_minmax : forall (n : nat) (v t mn mx : Z) (len : zarr) (W : list (Z * Z)) (m mf : word -> option byte)
      (t0 t1 t2 a0 a3 a4 a5 a6 a7 s10 t3 t4 t5 t6 : word),
    (v + Z.of_nat n = A)%Z -> (0 <= v)%Z -> (1 <= n)%nat -> (0 <= t < nG)%Z -> (0 <= mn <= 32)%Z -> (0 <= mx <= 17)%Z ->
    (forall tt vv, 0 <= tt < nG -> 0 <= vv < A -> zdef len (258 * tt + vv) = true /\ 1 <= zget len (258 * tt + vv) <= 17)%Z ->
    u8arr b0segs m (E + 37708) (ovb len (jseg J 37708 1548) 1548) ->
    munch W mf m -> shzW b0segs W mf E (E + ESTATE_SIZE) ->
    frdW b0segs W mf (P + 1472) [C8 (Z_to_bv 64 (LR t))] ->
    (forall (a0 a3 : word), let r := sm_minmax n len t v mn mx in
      (0 <= fst r <= 32)%Z -> (0 <= snd r <= 17)%Z ->
      evt b0segs Q (MS (CRb (Z_to_bv 64 A) t0 t1 t2 a0 (Z_to_bv 64 A) (NOT (LR t)) a3 a4 a5 a6 a7 t (Z_to_bv 64 (snd r)) (Z_to_bv 64 (fst r)) s10 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x93d6c) fc None m (seg_rom b0segs))) ->
    evt b0segs Q (MS (CRb (Z_to_bv 64 A) t0 t1 t2 a0 (Z_to_bv 64 v) (NOT (LR t)) a3 a4 a5 a6 a7 t (Z_to_bv 64 mx) (Z_to_bv 64 mn) s10 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x93d14) fc None m (seg_rom b0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros v t mn mx len W m mf t0 t1 t2 a0 a3 a4 a5 a6 a7 s10 t3 t4 t5 t6 Hv Hv0 Hn Ht Hmn Hmx LENF LEN MU SHe V72 K.
    openCX. unfold ESTATE_SIZE in SHe.
    pose proof (jseg_length J 37708 1548 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ6. pose proof (ovb_length_nat len (jseg J 37708 1548) 1548) as LL.
    destruct (LENF t v ltac:(lia) ltac:(lia)) as [Dl Rl].
    cbn [sm_minmax] in K. set (l := zget len (258 * t + v)) in *.
    (* [comment removed for export] *)
    brun_to 0x93d38%Z. pose proof (V72 m MU) as RO. lstep. clear RO. lstep.
    pose proof (ovb_read1 b0segs m (E + 37708) len (jseg J 37708 1548) 1548 (258 * t + v) _ LEN ltac:(lia) Dl ltac:(unfold wa; f_equal; lia)) as RD.
    fold l in RD. lstep. clear RD. cbv beta. rewrite (unsigned_lit8 l) by lia.
    (* [comment removed for export] *)
    assert (STEP : forall (xa3 xs7 xs8 : word), xs7 = Z_to_bv 64 (if mx <? l then l else mx)%Z -> xs8 = Z_to_bv 64 (if l <? mn then l else mn)%Z ->
      evt b0segs Q (MS (CRb (Z_to_bv 64 A) t0 t1 t2 (Z_to_bv 64 l) (Z_to_bv 64 v) (NOT (LR t)) xa3 a4 a5 a6 a7 t xs7 xs8 s10 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x93d54) fc None m (seg_rom b0segs))).
    { intros xa3 xs7 xs8 -> ->.
      lstep. lstep; if_cases Ke; zify_cond_z Ke.
      - enter_with (IH (v + 1)%Z t (if l <? mn then l else mn)%Z (if mx <? l then l else mx)%Z len W m mf);
          [st_eq| lia| lia| lia| lia| destruct (Z.ltb_spec l mn); lia| destruct (Z.ltb_spec mx l); lia| exact LENF| exact LEN| exact MU| exact SHe| exact V72| exact K].
      - assert (n = 0)%nat by lia. subst n. cbn [sm_minmax] in K.
        lstep.
        enter_with (K _ _); [st_eq| cbn [fst]; destruct (Z.ltb_spec l mn); lia| cbn [snd]; destruct (Z.ltb_spec mx l); lia]. }
    lstep; if_cases K1; zify_cond_z K1.
    - (* [comment removed for export] *)
      lstep; if_cases K2; zify_cond_z K2.
      + enter_with (STEP _ _ _); [st_eq| f_equal; destruct (Z.ltb_spec mx l); lia| f_equal; destruct (Z.ltb_spec l mn); lia].
      + lstep. enter_with (STEP _ _ _); [st_eq| f_equal; destruct (Z.ltb_spec mx l); lia| f_equal; destruct (Z.ltb_spec l mn); lia].
    - lstep. lstep; if_cases K2; zify_cond_z K2.
      + enter_with (STEP _ _ _); [st_eq| f_equal; destruct (Z.ltb_spec mx l); lia| f_equal; destruct (Z.ltb_spec l mn); lia].
      + lstep. enter_with (STEP _ _ _); [st_eq| f_equal; destruct (Z.ltb_spec mx l); lia| f_equal; destruct (Z.ltb_spec l mn); lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation Was := [(E + 39256, E + 45448); (P + 1472, P + 1480); (P - 32, P)]%Z.
  Notation HAS v00 v08 v24 v32 v48 v56 v72 v88 v20 v28 :=
    (sd_hi cx nG (SDW v00 v08 (Z_to_bv 64 A) v24 v32 v48 v56 v72 v88 (Z_to_bv 64 (E + 39256)) (NOT (E + 39256)) (Z_to_bv 64 A) v20 v28)).
  Lemma B0_sc_assign : forall (n t : nat) (code len : zarr) (lo : Z) (v00 v08 v24 v32 v48 v56 v88 v20 v28 : word) (m mf : word -> option byte)
      (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s10 t3 t4 t5 t6 : word),
    (Z.of_nat t + Z.of_nat n = nG)%Z -> (1 <= n)%nat ->
    (forall tt vv, 0 <= tt < nG -> 0 <= vv < A -> zdef len (258 * tt + vv) = true /\ 1 <= zget len (258 * tt + vv) <= 17)%Z ->
    u8arr b0segs m (E + 37708) (ovb len (jseg J 37708 1548) 1548) ->
    u32arr b0segs m (E + 39256) (ovw code (jseg J 39256 6192) 1548) ->
    rw_cells b0segs m (P + 1384) (HAS v00 v08 v24 v32 v48 v56 (Z_to_bv 64 (LR (Z.of_nat t))) v88 v20 v28) ->
    mem_inv b0segs m -> stk b0segs m lo P -> (lo + 32 <= P)%Z -> (CEIL <= lo)%Z ->
    munch Was mf m -> wmono b0segs mf m ->
    acoW Was mf -> shzW b0segs Was mf E (E + ESTATE_SIZE) ->
    (forall m' (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s10 t3 t4 t5 t6 : word),
      u8arr b0segs m' (E + 37708) (ovb len (jseg J 37708 1548) 1548) ->
      u32arr b0segs m' (E + 39256) (ovw (sm_assign n code len A (Z.of_nat t)) (jseg J 39256 6192) 1548) ->
      rw_cells b0segs m' (P + 1384) (HAS v00 v08 v24 v32 v48 v56 (Z_to_bv 64 (LR nG)) v88 v20 v28) ->
      mem_inv b0segs m' -> stk b0segs m' lo P ->
      munch Was mf m' -> wmono b0segs mf m' ->
      evt b0segs Q (MS (CRb ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 nG s7 s8 s10 t3 t4 t5 t6) F (Z_to_bv 64 0x93e0c) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (CRb (Z_to_bv 64 A) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z.of_nat t) (Z_to_bv 64 A) s8 s10 t3 t4 t5 t6) F (Z_to_bv 64 0x93cdc) fc None m (seg_rom b0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros t code len lo v00 v08 v24 v32 v48 v56 v88 v20 v28 m mf t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s10 t3 t4 t5 t6 Ht Hn LENF LEN CODE HI MI ST STK CLO MU WM ACW SHe K.
    openCX. unfold CEIL in CLO. assert (HAd : A = (e_nInUse e0 + 2)%Z) by reflexivity. pose proof SHe as SHe'. unfold ESTATE_SIZE in SHe.
    pose proof (jseg_length J 37708 1548 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ6. pose proof (jseg_length J 39256 6192 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ7.
    unfold sd_hi in HI. cbv zeta in HI. cbn [w1400 w1408 w1416 w1424 w1432 w1448 w1456 w1472 w1488 w1496 w1504 w1512 w1520 w1528] in HI.
    cbn [sm_assign] in K.
    pose proof (sm_minmax_spec (Z.to_nat A) len (Z.of_nat t) 0 32 0 ltac:(lia) ltac:(lia)) as MM. cbv zeta in MM.
    destruct (sm_minmax (Z.to_nat A) len (Z.of_nat t) 0 32 0) as [mn mx] eqn:EMM. cbn [fst snd] in MM. cps_destruct MM as (M1 & M2 & M3 & M4).
    rewrite Z2Nat.id in M3, M4 by lia.
    destruct (M4 ltac:(intros j Hj; apply (proj2 (LENF (Z.of_nat t) j ltac:(lia) ltac:(lia))))) as [N1 N2].
    pose proof (M3 0%Z ltac:(lia)) as M30. pose proof (proj2 (LENF (Z.of_nat t) 0%Z ltac:(lia) ltac:(lia))) as L00.
    assert (MN : (1 <= mn <= 17)%Z) by lia. assert (MX : (1 <= mx <= 17)%Z) by lia.
    (* [comment removed for export] *)
    lstep. lstep; if_cases K0; zify_cond_z K0; [exfalso; revert K0; rewrite ?signed_lit by lia; lia|].
    (* [comment removed for export] *)
    brun_to 0x93d14%Z.
    assert (V72 : frdW b0segs [] m (P + 1472) [C8 (Z_to_bv 64 (LR (Z.of_nat t)))]).
    { eapply (frdW_cell_at b0segs _ _ (P + 1384) _ 88); [apply frdW_intro; [exact HI| exact I]| reflexivity| lia]. }
    enter_with (B0_sc_minmax (Z.to_nat A) 0 (Z.of_nat t) 32 0 len [] m m);
      [st_eq| lia| lia| lia| lia| lia| lia| exact LENF| exact LEN| apply munch_refl| eapply (shzW_sub b0segs _ _ mf m); [exact SHe'| exact MU| sub_fp_solve| lia| lia]| exact V72|].
    clear V72. intros ya0 ya3. cbv zeta. rewrite EMM. cbn [fst snd]. intros _ _.
    (* [comment removed for export] *)
    lstep. lstep; if_cases Kb1; zify_cond_z Kb1; [| exfalso; lia].
    lstep; if_cases Kb2; zify_cond_z Kb2; [exfalso; lia|].
    (* [comment removed for export] *)
    brun_to 0xa8d70%Z.
    pose proof (ACW m MU) as AC.
    call (B0_hbAssignCodes_Z _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m (E + 39256)%Z (E + 37708)%Z (258 * Z.of_nat t)%Z (258 * Z.of_nat t)%Z mn mx A 1548%Z 1548%Z lo P code len (jseg J 39256 6192) (jseg J 37708 1548));
        [ lia | f_equal; lia | f_equal; lia | reflexivity | reflexivity | reflexivity
        | exact CODE | exact LEN | exact MI | exact ST | lia
        | lia | lia | lia | lia | lia | lia | lia
        | clear - ME; Z.div_mod_to_equations; lia | lia | unfold CEIL; lia | lia | unfold CEIL; lia
        | unfold apart; lia | lia | lia
        | intros i Hi; destruct (LENF (Z.of_nat t) i ltac:(lia) Hi) as [D R]; split; [exact D| apply M3; lia]
        | exact AC | lia | lia | lia
        | eapply (shzW_sub b0segs _ _ mf m); [exact SHe| exact MU| sub_fp_solve| lia| lia]
        | eapply (shzW_sub b0segs _ _ mf m); [exact SHe| exact MU| sub_fp_solve| lia| lia] | ].
    clear AC.
    (* [comment removed for export] *)
    lstep. lstep. lstep. lstep. lstep. wstep. lstep. lstep; if_cases Ke; zify_cond_z Ke.
    - replace (E + 37708 + 258 * Z.of_nat t + 258)%Z with (LR (Z.of_nat (S t))) in HI by lia.
      enter_with (IH (S t) _ len lo v00 v08 v24 v32 v48 v56 v88 v20 v28 _ mf);
        [st_eq| lia| lia| exact LENF| exact LEN| eassumption| unfold sd_hi; cbv zeta; exact HI
        | assumption| assumption| lia| unfold CEIL; lia| assumption| assumption| exact ACW| exact SHe'|].
      intros mm; intros *. replace (Z.of_nat (S t)) with (Z.of_nat t + 1)%Z by lia. apply K.
    - assert (n = 0)%nat by lia. subst n. cbn [sm_assign] in K.
      replace (E + 37708 + 258 * Z.of_nat t + 258)%Z with (LR nG) in HI by lia.
      enter_with (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
        [st_eq| exact LEN| eassumption| unfold sd_hi; cbv zeta; exact HI| assumption| assumption| assumption| assumption].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma pos_reader : forall (W : list (Z * Z)) (m : word -> option byte),
    rw_cells b0segs m (SHF + 16) [C1 (Z_to_bv 8 6)] -> app_fp W -> shpW b0segs W m (FB + 128) (FB + 134).
  Proof.
    intros W m SHC AW. pose proof AF as [AF1 AF2]. bz_ceil.
    assert (B : bytes_at b0segs m (shad (FB + 128)) (ushadow 6)).
    { unfold shad, SHB. rewrite (sanchor_addr_lit FB SHF 128 16 AF eq_refl).
      destruct SHC as [[_ B] _]. cbn [cells_bytes cbytes app] in B. exact B. }
    replace (FB + 134)%Z with (FB + 128 + 6)%Z by lia.
    refine (proj2 (sh_of_ushadow b0segs W m (FB + 128) 6 B _ ltac:(lia) ltac:(lia) _ AW)).
    - clear - AF1. Z.div_mod_to_equations. lia.
    - unfold CEIL in FBH. change (2^47)%Z with 140737488355328%Z. lia.
  Qed.
  Notation Wmtf := [(E + 19706, E + 37708); (FB + 128, FB + 134)]%Z.
  Lemma app_fp_Wmtf : app_fp Wmtf.
  Proof. pose proof OFFE as O1. pose proof OFFF as O2. unfold id in O1, O2. cbn [app_fp]. unfold SH_LO, SH_HI in *. repeat split; lia. Qed.
  Lemma app_fp_Wpos : app_fp Wpos.
  Proof. pose proof OFFF as O2. unfold id in O2. cbn [app_fp]. unfold SH_LO, SH_HI in *. repeat split; lia. Qed.

  (* [comment removed for export] *)
  Lemma h34_firstn4_le8 : forall w : word, firstn 4 (le8 w) = le4 w.
  Proof. intros w. unfold le8, le4, word_to_le_bytes. reflexivity. Qed.
  Lemma h34_skipn_le8 : forall (n : nat) (w : word) (l : list byte), (8 <= n)%nat -> skipn n (le8 w ++ l) = skipn (n - 8) l.
  Proof. intros n w l Hn. rewrite skipn_app, length_le8. rewrite skipn_all2 by (rewrite length_le8; lia). reflexivity. Qed.
  Lemma hi_rd1520 : forall (m : word -> option byte) (H : sdw),
    rw_cells b0segs m (P + 1384) (sd_hi cx nG H) -> ov_read_bytes b0segs m (wa (P + 1520)) 4 = Some (le4 (w1520 H)).
  Proof.
    intros m H HH. destruct HH as [[Hwf Hb] Hw].
    replace (wa (P + 1520)) with (wa (P + 1384 + Z.of_nat 136)) by (unfold wa; f_equal; lia).
    rewrite (bytes_at_ov_read b0segs m _ _ 136 4 Hb).
    2:{ unfold sd_hi. cbv zeta. cbn [cells_bytes cbytes]. rewrite !length_app, !length_le8. cbn. lia. }
    f_equal; unfold sd_hi; cbv zeta; cbn [cells_bytes cbytes]; rewrite !h34_skipn_le8 by lia; cbn [Nat.sub]; rewrite skipn_O;
      rewrite firstn_app, length_le8; cbn [Nat.sub]; rewrite firstn_O, app_nil_r; apply h34_firstn4_le8.
  Qed.

  Ltac lit_store :=
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?v)) _) => change (Z_to_le_bytes 8 v) with (le8 (Z_to_bv 64 v)); mem_after_store
    | _ => idtac
    end.

  Notation WC := [(E + 19706, E + 37708); (E + 39256, E + 45448); (P + 1384, P + 1568); (FB + 128, FB + 134); (SHF + 16, SHF + 17); (P - 32, P)]%Z.
  Lemma B0_smC_body : forall (c0 f0 p0 h0 w0 q0 : zarr) (m : word -> option byte) (w64 w72 w104 v00 v08 v24 v32 v48 v56 v88 v96 v04 v28 : word) (i6 : list byte) (lo : Z)
      (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3 t4 t5 t6 : word),
    let it := smB_it e0 c0 f0 h0 w0 q0 in let nSel := smB_nsel e0 c0 f0 h0 w0 q0 in
    sd_facts (est_C e0 c0 f0 p0 h0 w0 q0) nG nSel ->
    u8arr b0segs m (E + 1704) (ovb (it_sel it) (jseg J 1704 18002) 18002) ->
    u8arr b0segs m (E + 19706) (ovb (e_selectorMtf e0) (jseg J 19706 18002) 18002) ->
    u8arr b0segs m (E + 37708) (ovb (it_len it) (jseg J 37708 1548) 1548) ->
    u32arr b0segs m (E + 39256) (ovw (e_code e0) (jseg J 39256 6192) 1548) ->
    rw_cells b0segs m (P + 32) (sd_loA cx FB SHF SHE w64 w72 w104) ->
    rw_cells b0segs m (P + 1384) (sd_hi cx nG (SDW v00 v08 (Z_to_bv 64 A) v24 v32 v48 v56 (Z_to_bv 64 (E + 37708)) v88 v96 v04 (Z_to_bv 64 A) (Z_to_bv 64 nSel) v28)) ->
    u8arr b0segs m (FB + 128) i6 -> Z.of_nat (length i6) = 6%Z ->
    rw_cells b0segs m (SHF + 16) [C1 sf8b] ->
    stk b0segs m lo P -> (lo + 32 <= P)%Z -> (CEIL <= lo)%Z -> mem_inv b0segs m ->
    acoW WC m -> shzW b0segs WC m E (E + ESTATE_SIZE) ->
    (forall m' (i6' : list byte) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3 t4 t5 t6 : word),
       u8arr b0segs m' (E + 1704) (ovb (it_sel it) (jseg J 1704 18002) 18002) ->
       u8arr b0segs m' (E + 19706) (ovb (snd (smC_pm e0 c0 f0 p0 h0 w0 q0)) (jseg J 19706 18002) 18002) ->
       u8arr b0segs m' (E + 37708) (ovb (it_len it) (jseg J 37708 1548) 1548) ->
       u32arr b0segs m' (E + 39256) (ovw (smC_code e0 c0 f0 h0 w0 q0) (jseg J 39256 6192) 1548) ->
       rw_cells b0segs m' (P + 32) (sd_loA cx FB SHF SHE w64 w72 w104) ->
       rw_cells b0segs m' (P + 1384) (sd_hi cx nG (SDW v00 v08 (Z_to_bv 64 A) v24 v32 (Z_to_bv 64 nSel) v56 (Z_to_bv 64 (LR nG)) v88 (Z_to_bv 64 (E + 39256)) (NOT (E + 39256))
                                                      (Z_to_bv 64 A) (Z_to_bv 64 nSel) (Z_to_bv 64 3005))) ->
       u8arr b0segs m' (FB + 128) i6' -> Z.of_nat (length i6') = 6%Z ->
       rw_cells b0segs m' (SHF + 16) [C1 sf8b] ->
       stk b0segs m' lo P -> mem_inv b0segs m' -> munch WC m m' -> wmono b0segs m m' ->
       evt b0segs Q (MS (mkR ra cP gp tp t0 t1 t2 s0 cP a0 a1 a2 a3 a4 a5 a6 a7 cSB x3 x4 x5 x6 x7 x8 x9 x10 x11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x93e0c) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR (Z_to_bv 64 A) cP gp tp t0 t1 t2 s0 cP a0 a1 a2 a3 a4 a5 a6 a7 cSB x3 x4 x5 x6 x7 x8 x9 x10 x11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x93afc) fc None m (seg_rom b0segs)).
  Proof.
    intros c0 f0 p0 h0 w0 q0 m w64 w72 w104 v00 v08 v24 v32 v48 v56 v88 v96 v04 v28 i6 lo t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3 t4 t5 t6.
    cbv zeta. intros SDF SEL SELM LEN CODE LOA HIs POS L6 SHC ST STK CLO MI ACW SHe K.
    openCX. unfold CEIL in CLO. assert (HAd : A = (e_nInUse e0 + 2)%Z) by reflexivity.
    pose proof CEP as CEP'. unfold CEIL in CEP'. pose proof FBH as FBH'. unfold CEIL in FBH'. pose proof SHL as SHL'. pose proof SHH as SHH'. unfold SH_LO, SH_HI in SHL', SHH'.
    set (it := smB_it e0 c0 f0 h0 w0 q0) in *. set (nSel := smB_nsel e0 c0 f0 h0 w0 q0) in *.
    pose proof SDF as SF. unfold sd_facts in SF. cbv zeta in SF.
    cbn [e_nInUse e_nMTF e_arr1 e_inUse e_selectorMtf e_selector e_len e_code est_C] in SF.
    cps_destruct SF as (FA & FG & FS & FM & F35 & FZB & FMV & FIU & FSM & FSEL & FLEN & FCODE & FCNT).
    change (e_nInUse e0 + 2)%Z with A in FA, FMV, FLEN, FCODE. fold it in FSEL, FLEN.
    pose proof (hi_rd1520 m _ HIs) as RD20. cbn [w1520] in RD20.
    unfold sd_loA in LOA. unfold sd_hi in HIs. cbv zeta in LOA, HIs.
    cbn [w1400 w1408 w1416 w1424 w1432 w1448 w1456 w1472 w1488 w1496 w1504 w1512 w1520 w1528] in HIs.
    pose proof (munch_refl WC m) as MU0. pose proof (wmono_refl b0segs m) as WM0.
    (* [comment removed for export] *)
    lstep. clear RD20. rewrite (sx32_of_Z nSel) by lia.
    lstep. lstep. wstep. lstep; if_cases K0; zify_cond_z K0; [| exfalso; revert K0; rewrite ?signed_lit by lia; lia].
    (* [comment removed for export] *)
    lstep. lstep. lstep. lstep. change (le1 (Z_to_bv 64 6)) with [Z_to_bv 8 6]. mem_after_store.
    (* [comment removed for export] *)
    lazymatch type of POS with u8arr _ ?mm _ _ =>
      pose proof (ovb_init b0segs mm (FB + 128) 6 i6 ltac:(replace (Z.to_nat 6) with (length i6) by lia; exact (rw_cells_of_u8arr b0segs mm _ i6 POS)) ltac:(lia)) as POS' end.
    clear POS. rename POS' into POS.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (B0_sc_posinit (Z.to_nat nG) 0 znew i6 mm mm);
        [st_eq| lia| lia| lia| exact POS| exact MI| apply munch_refl| apply wmono_refl
        | eapply (frdW_cell_at b0segs _ _ (P + 32) _ 48); [apply frdW_intro; [exact LOA| cbn [disjoint_from]; simpl_sizes; Lib.Step.slia]| reflexivity| lia]
        | eapply (frdW_cell_at b0segs _ _ (P + 1384) _ 96); [apply frdW_intro; [exact HIs| cbn [disjoint_from]; simpl_sizes; Lib.Step.slia]| reflexivity| lia]
        | apply pos_reader; [exact SHC| exact app_fp_Wpos] |] end.
    clear POS MI. intros mq1 xa0 xa3 xa4 POS MI MU1 WM1.
    lazymatch type of MU1 with munch _ ?ma ?mb => transport_after_call b0segs ma mb MU1 WM1 end. clear MU1 WM1.
    (* [comment removed for export] *)
    lstep. lstep. lstep; if_cases K1; zify_cond_z K1; [exfalso; revert K1; rewrite ?signed_lit by lia; lia|].
    lstep. lstep.
    assert (PD0 : zdef (yy_init (Z.to_nat nG) znew 0) 0 = true) by (rewrite yy_init_def; replace ((0 <=? 0) && (0 <? 0 + Z.of_nat (Z.to_nat nG)))%bool with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia); reflexivity).
    assert (PV0 : zget (yy_init (Z.to_nat nG) znew 0) 0 = 0%Z) by (rewrite yy_init_get; replace ((0 <=? 0) && (0 <? 0 + Z.of_nat (Z.to_nat nG)))%bool with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia); reflexivity).
    pose proof (ovb_read1 b0segs mq1 (FB + 128) _ i6 6 0 _ POS ltac:(lia) PD0 ltac:(unfold wa; f_equal; lia)) as RD.
    lstep. clear RD. rewrite PV0. cbv beta. rewrite (unsigned_lit8 0) by lia.
    (* [comment removed for export] *)
    brun_to 0x93ba8%Z.
    (* [comment removed for export] *)
    assert (PP0 : PP nG (yy_init (Z.to_nat nG) znew 0)) by (apply PP_init; lia).
    assert (PAG0 : PAGREE (yy_init (Z.to_nat nG) znew 0) (yy_init (Z.to_nat nG) p0 0)).
    { intros k Hk. rewrite yy_init_def, !yy_init_get.
      replace ((0 <=? k) && (k <? 0 + Z.of_nat (Z.to_nat nG)))%bool with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia). split; reflexivity. }
    assert (PPm : PP nG (yy_init (Z.to_nat nG) p0 0)) by (apply PP_init; lia).
    assert (PV0m : zget (yy_init (Z.to_nat nG) p0 0) 0 = 0%Z).
    { rewrite yy_init_get. replace ((0 <=? 0) && (0 <? 0 + Z.of_nat (Z.to_nat nG)))%bool with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia). reflexivity. }
    enter_with (B0_sc_mtf _ _ _ _ _ _ _ _ (Z.to_nat nSel) 0 (yy_init (Z.to_nat nG) p0 0) (yy_init (Z.to_nat nG) znew 0) (it_sel it) (e_selectorMtf e0) i6 mq1 mq1 nSel);
      [st_eq| lia| lia| lia| lia| exact PPm| exact PAG0| exact FSEL| exact SEL| exact SELM| exact POS| exact MI| apply munch_refl| apply wmono_refl
      | eapply (frdW_cell_at b0segs _ _ (P + 1384) _ 0); [apply frdW_intro; [exact HIs| cbn [disjoint_from]; simpl_sizes; Lib.Step.slia]| reflexivity| lia]
      | eapply (frdW_cell_at b0segs _ _ (P + 1384) _ 8); [apply frdW_intro; [exact HIs| cbn [disjoint_from]; simpl_sizes; Lib.Step.slia]| reflexivity| lia]
      | eapply (shzW_sub b0segs _ _ m mq1); [exact SHe| exact MU0| sub_fp_solve| lia| lia]
      | apply pos_reader; [exact SHC| exact app_fp_Wmtf] |].
    clear SEL SELM POS MI. intros mq2 pm2 yt0 yt1 yt2 ya0 ya1 yt3 yt4 yt5. cbv zeta. intros PP2 PAG2 SEL SELM POS MI MU2 WM2.
    lazymatch type of MU2 with munch _ ?ma ?mb => transport_after_call b0segs ma mb MU2 WM2 end. clear MU2 WM2.
    change (sm_selmtf (Z.to_nat nSel) (yy_init (Z.to_nat nG) p0 0) (it_sel it) (e_selectorMtf e0) 0) with (smC_pm e0 c0 f0 p0 h0 w0 q0) in SELM.
    (* [comment removed for export] *)
    lstep.
    pose proof (u8arr_store_ok b0segs mq2 (FB + 128) _ 0 _ POS ltac:(rewrite ovb_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO.
    lstep. store_addr (FB + 128 + 0)%Z. ovb_store1 POS 0%Z.
    (* [comment removed for export] *)
    lstep. lstep. lstep. lstep. lstep. lstep. lstep. lstep.
    lstep. change (le1 (Z_to_bv 64 (-8))) with [sf8b]. mem_after_store.
    lstep. lstep. lstep. (wstep; lit_store). lstep. wstep.
    brun_to 0x93cdc%Z.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (HI : rw_cells b0segs mm (P + 1384) (HAS v00 v08 v24 v32 (Z_to_bv 64 nSel) v56 (Z_to_bv 64 (LR (Z.of_nat 0%nat))) v88 (Z_to_bv 64 nSel) (Z_to_bv 64 3005))) end.
    { unfold sd_hi. cbv zeta. cbn [w1400 w1408 w1416 w1424 w1432 w1448 w1456 w1472 w1488 w1496 w1504 w1512 w1520 w1528].
      replace (LR (Z.of_nat 0%nat)) with (E + 37708)%Z by (change (Z.of_nat 0) with 0%Z; ring). exact HIs. }
    clear HIs.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    enter_with (B0_sc_assign (Z.to_nat nG) 0%nat (e_code e0) (it_len it) lo _ _ _ _ _ _ _ _ _ mm mm);
      [st_eq| lia| lia| exact FLEN| exact LEN| exact CODE| exact HI| exact MI| exact ST| lia| unfold CEIL; lia
      | apply munch_refl| apply wmono_refl
      | eapply (acoW_sub _ _ m mm); [exact ACW| exact MU0| sub_fp_solve]
      | eapply (shzW_sub b0segs _ _ m mm); [exact SHe| exact MU0| sub_fp_solve| lia| lia] |] end.
    clear LEN CODE HI MI ST. intros mq4 zra z0 z1 z2 za0 za1 za2 za3 za4 za5 za6 za7 zs7 zs8 zs10 z3 z4 z5 z6 LEN CODE HI MI ST MU4 WM4.
    lazymatch type of MU4 with munch _ ?ma ?mb => transport_after_call b0segs ma mb MU4 WM4 end. clear MU4 WM4.
    change (sm_assign (Z.to_nat nG) (e_code e0) (it_len it) A (Z.of_nat 0)) with (smC_code e0 c0 f0 h0 w0 q0) in CODE.
    (* [comment removed for export] *)
    destruct (u8arr_of_cells b0segs _ _ _ (rw_cells_of_u8arr b0segs _ _ _ POS)) as [PJ LPJ]. cbn [cells_bytes cbytes app] in PJ, LPJ. rewrite app_nil_r in PJ.
    enter_with (K mq4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
      [st_eq| exact SEL| exact SELM| exact LEN| exact CODE| unfold sd_loA; cbv zeta; exact LOA| exact HI
      | exact PJ| rewrite ovb_length; lia| exact SHC| exact ST| exact MI| exact MU0| exact WM0].
  Qed.
End SC3.
End ACeilS1.
