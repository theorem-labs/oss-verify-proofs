(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCStream BzCState BzCMtf BzCHuff BzArrD BzCRebuildF CmpMem CmpCut CmpCutSM CmpCutSmA CmpCutSmB CmpCutSmC BzCFactsSmA BzCFactsGm BzCFactsSd BzCFactsSd2 CmpFsKit CmpHmKit CmpSmKit CmpSmKit2.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit AsanCut.
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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_asg A0_cmp_msV A0_cmp_sdV.

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
             F (ret_pc ra) fc None m' (seg_rom a0segs)
    /\ munch W m m' /\ wmono a0segs m m' /\ mem_inv a0segs m' /\ stk a0segs m' lo spz
    /\ u32arr a0segs m' Ecode (ovw code' Jc NC).

Lemma A0_hbAssignCodes_Z : forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (Ecode Elen cb lb minLen maxLen alphaSize NC NL lo spz : Z) (code len : zarr) (Jc Jl : list byte),
  (0 <= spz < 18446744073709551616)%Z ->
  let W := [(Ecode + 4 * cb, Ecode + 4 * (cb + alphaSize)); (spz - 16, spz)]%Z in
  a0 = Z_to_bv 64 (Ecode + 4 * cb) -> a1 = Z_to_bv 64 (Elen + lb) ->
  a2 = Z_to_bv 64 minLen -> a3 = Z_to_bv 64 maxLen -> a4 = Z_to_bv 64 alphaSize ->
  u32arr a0segs m Ecode (ovw code Jc NC) -> u8arr a0segs m Elen (ovb len Jl NL) -> mem_inv a0segs m ->
  stk a0segs m lo spz -> (lo + 16 <= spz)%Z ->
  (0 <= cb)%Z -> (cb + alphaSize <= NC)%Z -> (0 <= lb)%Z -> (lb + alphaSize <= NL)%Z -> (0 <= alphaSize <= 258)%Z ->
  (1 <= minLen <= 32)%Z -> (0 <= maxLen <= 17)%Z -> (Ecode mod 4 = 0)%Z -> (0 < Ecode)%Z -> (Ecode + 4 * NC <= CEIL)%Z -> (0 < Elen)%Z -> (Elen + NL <= CEIL)%Z ->
  apart Ecode (4 * NC) Elen NL ->
  (spz <= Ecode \/ Ecode + 4 * NC <= spz - 16)%Z -> (spz <= Elen \/ Elen + NL <= spz - 16)%Z ->
  (forall i, 0 <= i < alphaSize -> zdef len (lb + i) = true /\ minLen <= zget len (lb + i) <= maxLen)%Z ->
  aconsts A0C m -> (0x61e000 <= lo)%Z -> (0x61e000 <= Ecode)%Z -> (0x61e000 <= Elen)%Z ->
  shzW a0segs W m Ecode (Ecode + 4 * NC) -> shzW a0segs W m Elen (Elen + NL) ->
  evt a0segs (asg_postZ ra spz gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
              Ecode (hbAssignCodes code len cb lb minLen maxLen alphaSize) Jc NC lo W m)
      (MS (mkR ra (Z_to_bv 64 spz) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9df04) fc None m (seg_rom a0segs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
         Ecode Elen cb lb minLen maxLen alphaSize NC NL lo spz code len Jc Jl Hsp.
  pose proof (A0_hbAssignCodes ra (Z_to_bv 64 spz) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
                         Ecode Elen cb lb minLen maxLen alphaSize NC NL lo code len Jc Jl) as G.
  cbv zeta in G. cbn [aci_segs aci_c ci_segs A0C aci_hi ci_hi ci_hbAssignCodes] in G. unfold hbAssignCodes_post in G.
  rewrite (unsigned_lit spz) in G by lia. cbv zeta. exact G.
Qed.

Section SC3.
  Variables (cx : cctx) (e0 : est) (Q : machine_state -> Prop).
  Variables (gp tp s0 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (P SHE FB SHF : Z).
  Hypothesis CX : cctx_ok cx. Hypothesis SEP : cctx_sep cx.
  Hypothesis CEP : (CEIL <= P)%Z. Hypothesis PHI : (P + 1616 <= 18446744073709551616)%Z.
  Hypothesis EIMG : (0x61e000 <= c_E cx)%Z.   (* [comment removed for export] *)
  Hypothesis FBL : (0 < FB)%Z. Hypothesis FBH : (FB + 160 <= CEIL)%Z.
  Hypothesis SEFB : id ((c_E cx + 55768 <= FB)%Z \/ (FB + 160 <= c_E cx)%Z).
  Hypothesis SHL : (SH_LO <= SHF)%Z. Hypothesis SHH : (SHF + 20 <= SH_HI)%Z. Hypothesis AF : sanchor FB SHF.
  Hypothesis SESH : id ((c_E cx + 55768 <= SHF)%Z \/ (SHF + 20 <= c_E cx)%Z).
  Hypothesis SFSH : id ((FB + 160 <= SHF)%Z \/ (SHF + 20 <= FB)%Z).
  Hypothesis SPSH : id ((SHF + 20 <= P)%Z \/ (P + 1616 <= SHF)%Z).
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

  (* [comment removed for export] *)
  Notation MR ra nSel t0 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s11 t3 t4 t5 t6 :=
    (mkR ra cP gp tp t0 (Z_to_bv 64 E) (Z_to_bv 64 (FB + 128)) s0 cP a0 a1 a2 a3 a4 a5 a6 a7
         (Z_to_bv 64 SHF) (Z_to_bv 64 nSel) cSB (Z_to_bv 64 nSel) s6 s7 s8 s9 (Z_to_bv 64 nG) s11 t3 t4 t5 t6).
  Notation Wpos := [(FB + 128, FB + 134)]%Z.

  (* [comment removed for export] *)
  Definition PAGREE (pm p : zarr) : Prop := forall k, (1 <= k < nG)%Z -> zdef pm k = true /\ zget pm k = zget p k.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma A0_sc_posinit : forall (n : nat) (i : Z) (pm : zarr) (i6 : list byte) (m mf : word -> option byte) (nSel : Z)
      (ra t0 a0 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word),
    (i + Z.of_nat n = nG)%Z -> (0 <= i)%Z -> (1 <= n)%nat ->
    u8arr a0segs m (FB + 128) (ovb pm i6 6) ->
    mem_inv a0segs m -> munch Wpos mf m -> wmono a0segs mf m ->
    shpW a0segs Wpos mf (FB + 128) (FB + 134) ->
    (forall m' (a0 a2 a3 : word),
      u8arr a0segs m' (FB + 128) (ovb (yy_init n pm i) i6 6) ->
      mem_inv a0segs m' -> munch Wpos mf m' -> wmono a0segs mf m' ->
      evt a0segs Q (MS (MR ra nSel t0 a0 (Z_to_bv 64 nG) a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x8f300) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (MR ra nSel t0 a0 (Z_to_bv 64 i) a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x8f2d0) fc None m (seg_rom a0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros i pm i6 m mf nSel ra t0 a0 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s11 t3 t4 t5 t6 Hi Hi0 Hn POS MI MU WM SHp K.
    openCX. pose proof (ovb_length_nat pm i6 6) as LP.
    rewrite yy_init_S in K.
    (* [comment removed for export] *)
    arun_to 0x8f2dc%Z. ack_rd (FB + 128 + i)%Z 1%Z. ack_merge.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u8arr_store_ok a0segs mm (FB + 128) _ i _ POS ltac:(rewrite ovb_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO end.
    lstep. store_addr (FB + 128 + i)%Z. ovb_store1 POS i.
    replace (wr8 pm i (bv_unsigned (Z_to_bv 64 i))) with (zset pm i i) in POS by (unfold wr8; rewrite unsigned_lit by lia; rewrite Z.mod_small by lia; reflexivity).
    (* [comment removed for export] *)
    lstep. lstep; if_cases Ke; zify_cond_z Ke.
    - enter_with (IH (i + 1)%Z _ i6 _ mf nSel); [st_eq| lia| lia| lia| exact POS| assumption| exact MU| exact WM| exact SHp| exact K].
    - assert (n = 0)%nat by lia. subst n. cbn [yy_init] in K.
      lstep.
      enter_with (K _ _ _ _); [st_eq| exact POS| assumption| exact MU| exact WM].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma A0_sc_search : forall (n : nat) (j mm : Z) (pos0 pm : zarr) (i6 : list byte) (m mf : word -> option byte) (nSel ll : Z)
      (ra t0 a1 a2 a6 a7 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word),
    (mm - j = Z.of_nat n)%Z -> (0 <= j <= mm)%Z -> (mm < nG)%Z ->
    (forall k, 0 <= k < nG -> 0 <= zget pos0 k < nG)%Z -> (0 <= ll < nG)%Z ->
    zget pos0 mm = ll -> (forall k, j <= k < mm -> zget pos0 k <> ll)%Z ->
    (forall k, 1 <= k <= j -> zdef pm k = true /\ zget pm k = zget pos0 (k - 1))%Z ->
    (forall k, j < k < nG -> zdef pm k = true /\ zget pm k = zget pos0 k)%Z ->
    u8arr a0segs m (FB + 128) (ovb pm i6 6) ->
    mem_inv a0segs m -> munch Wpos mf m -> wmono a0segs mf m ->
    shpW a0segs Wpos mf (FB + 128) (FB + 134) ->
    (forall m' pm' (t0 a6 a7 : word),
      (forall k, 1 <= k <= mm -> zdef pm' k = true /\ zget pm' k = zget pos0 (k - 1))%Z ->
      (forall k, mm < k < nG -> zdef pm' k = true /\ zget pm' k = zget pos0 k)%Z ->
      u8arr a0segs m' (FB + 128) (ovb pm' i6 6) ->
      mem_inv a0segs m' -> munch Wpos mf m' -> wmono a0segs mf m' ->
      evt a0segs Q (MS (MR ra nSel t0 (Z_to_bv 64 ll) a1 a2 (Z_to_bv 64 (FB + 129)) (Z_to_bv 64 ll) (Z_to_bv 64 mm) a6 a7 s6 s7 s8 s9 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x8f384) fc None m' (seg_rom a0segs))) ->
    (j < mm)%Z ->
    evt a0segs Q (MS (MR ra nSel t0 (Z_to_bv 64 ll) a1 a2 (Z_to_bv 64 (FB + 129)) (Z_to_bv 64 (zget pos0 j)) (Z_to_bv 64 j) a6 a7 s6 s7 s8 s9 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x8f348) fc None m (seg_rom a0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros j mm pos0 pm i6 m mf nSel ll ra t0 a1 a2 a6 a7 s6 s7 s8 s9 s11 t3 t4 t5 t6 Hn Hj Hmm PB Hll Em NOT SH REST POS MI MU WM SHp K LT.
    openCX. pose proof (ovb_length_nat pm i6 6) as LP.
    pose proof (PB j ltac:(lia)) as Pj. pose proof (PB (j + 1)%Z ltac:(lia)) as Pj1.
    destruct (REST (j + 1)%Z ltac:(lia)) as [D1 V1].
    (* [comment removed for export] *)
    arun_to 0x8f354%Z. ack_rd (FB + 129 + j)%Z 1%Z. ack_merge.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm0 _) =>
      pose proof (ovb_read1 a0segs mm0 (FB + 128) pm i6 6 (j + 1) _ POS ltac:(lia) D1 ltac:(unfold wa; f_equal; lia)) as RD end.
    lstep. clear RD. rewrite V1. cbv beta. rewrite (unsigned_lit8 (zget pos0 (j + 1))) by lia.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm0 _) =>
      pose proof (u8arr_store_ok a0segs mm0 (FB + 128) _ (j + 1) _ POS ltac:(rewrite ovb_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO end.
    lstep. store_addr (FB + 128 + (j + 1))%Z. ovb_store1 POS (j + 1)%Z.
    replace (wr8 pm (j + 1) (bv_unsigned (Z_to_bv 64 (zget pos0 j)))) with (zset pm (j + 1) (zget pos0 j)) in POS by (unfold wr8; rewrite unsigned_lit by lia; rewrite Z.mod_small by lia; reflexivity).
    (* [comment removed for export] *)
    lstep. lstep. lstep; if_cases Kc; zify_cond_z Kc.
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
      lstep. lstep.
      enter_with (K _ _ _ _ _);
        [st_eq| | | exact POS| assumption| exact MU| exact WM].
      + intros k Hk. destruct (Z.eq_dec k (j + 1)) as [->|NK].
        * rewrite zdef_zset_same, zget_zset_same. split; [reflexivity| f_equal; lia].
        * rewrite zdef_zset_other, zget_zset_other by lia. apply SH. lia.
      + intros k Hk. rewrite zdef_zset_other, zget_zset_other by lia. apply REST. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation Wmtf := [(E + 19706, E + 37708); (FB + 128, FB + 134)]%Z.
  Lemma A0_sc_mtf : forall (n : nat) (i : Z) (Pm pm sel sm : zarr) (i6 : list byte) (m mf : word -> option byte) (nSel : Z)
      (ra t0 a0 a5 a6 a7 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word),
    (i + Z.of_nat n = nSel)%Z -> (0 <= i)%Z -> (1 <= n)%nat -> (nSel <= 18002)%Z ->
    PP nG Pm -> PAGREE pm Pm ->
    (forall k, 0 <= k < nSel -> zdef sel k = true /\ 0 <= zget sel k < nG)%Z ->
    u8arr a0segs m (E + 1704) (ovb sel (jseg J 1704 18002) 18002) ->
    u8arr a0segs m (E + 19706) (ovb sm (jseg J 19706 18002) 18002) ->
    u8arr a0segs m (FB + 128) (ovb pm i6 6) ->
    mem_inv a0segs m -> munch Wmtf mf m -> wmono a0segs mf m ->
    frdW a0segs Wmtf mf (P + 1392) [C8 (Z_to_bv 64 (E + 1704))] ->
    shzW a0segs Wmtf mf E (E + ESTATE_SIZE) -> shpW a0segs Wmtf mf (FB + 128) (FB + 134) ->
    (forall m' pm' (t0 a0 a4 a5 a6 a7 : word),
      let r := sm_selmtf n Pm sel sm i in
      PP nG (fst r) -> PAGREE pm' (fst r) ->
      u8arr a0segs m' (E + 1704) (ovb sel (jseg J 1704 18002) 18002) ->
      u8arr a0segs m' (E + 19706) (ovb (snd r) (jseg J 19706 18002) 18002) ->
      u8arr a0segs m' (FB + 128) (ovb pm' i6 6) ->
      mem_inv a0segs m' -> munch Wmtf mf m' -> wmono a0segs mf m' ->
      evt a0segs Q (MS (MR ra nSel t0 a0 (Z_to_bv 64 nSel) (Z_to_bv 64 (E + 19706)) (Z_to_bv 64 (FB + 129)) a4 a5 a6 a7 s6 s7 s8 s9 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x8f3c0) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (MR ra nSel t0 a0 (Z_to_bv 64 i) (Z_to_bv 64 (E + 19706)) (Z_to_bv 64 (FB + 129)) (Z_to_bv 64 (zget Pm 0)) a5 a6 a7 s6 s7 s8 s9 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x8f31c) fc None m (seg_rom a0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros i Pm pm sel sm i6 m mf nSel ra t0 a0 a5 a6 a7 s6 s7 s8 s9 s11 t3 t4 t5 t6
           Hi Hi0 Hn HnS PPH PAG SELOK SEL SELM POS MI MU WM V1392 SHe SHp K.
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
    pose proof (V1392 m MU) as RO. lstep. clear RO.
    arun_to 0x8f334%Z.
    pose proof (ovb_read1 a0segs m (E + 1704) sel (jseg J 1704 18002) 18002 i _ SEL ltac:(lia) Dsi ltac:(unfold wa; f_equal; lia)) as RD.
    lstep. clear RD. cbv beta. rewrite (unsigned_lit8 (zget sel i)) by lia.
    (* [comment removed for export] *)
    assert (K8 : forall m1 pm1 (xt0 xa6 xa7 : word),
      (forall k, 1 <= k <= mm -> zdef pm1 k = true /\ zget pm1 k = zget Pm (k - 1))%Z ->
      (forall k, mm < k < nG -> zdef pm1 k = true /\ zget pm1 k = zget Pm k)%Z ->
      u8arr a0segs m1 (FB + 128) (ovb pm1 i6 6) ->
      u8arr a0segs m1 (E + 19706) (ovb sm (jseg J 19706 18002) 18002) ->
      u8arr a0segs m1 (E + 1704) (ovb sel (jseg J 1704 18002) 18002) ->
      mem_inv a0segs m1 -> munch Wmtf mf m1 -> wmono a0segs mf m1 ->
      evt a0segs Q (MS (MR ra nSel xt0 (Z_to_bv 64 (zget sel i)) (Z_to_bv 64 i) (Z_to_bv 64 (E + 19706)) (Z_to_bv 64 (FB + 129)) (Z_to_bv 64 (zget sel i)) (Z_to_bv 64 mm) xa6 xa7 s6 s7 s8 s9 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x8f384) fc None m1 (seg_rom a0segs))).
    { intros m1 pm1 xt0 xa6 xa7 SH1 REST1 POS1 SELM1 SEL1 MI1 MU1 WM1.
      pose proof (ovb_length_nat pm1 i6 6) as LP1.
      (* [comment removed for export] *)
      arun_to 0x8f39c%Z.
      pose proof (u8arr_store_ok a0segs m1 (E + 19706) _ i _ SELM1 ltac:(rewrite ovb_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO.
      lstep. store_addr (E + 19706 + i)%Z. ovb_store1 SELM1 i.
      replace (wr8 sm i (bv_unsigned (Z_to_bv 64 mm))) with (zset sm i mm) in SELM1 by (unfold wr8; rewrite unsigned_lit by lia; rewrite Z.mod_small by lia; reflexivity).
      assert (PAG1 : PAGREE pm1 P1n).
      { intros k Hk. subst P1n. rewrite zget_zset_other by lia.
        destruct (Z.le_gt_cases k mm) as [L|L]; [rewrite SH by lia; apply SH1; lia| rewrite REST by lia; apply REST1; lia]. }
      (* [comment removed for export] *)
      lstep; if_cases Ke; zify_cond_z Ke.
      - enter_with (IH (i + 1)%Z P1n pm1 sel (zset sm i mm) i6 _ mf nSel);
          [st_eq| lia| lia| lia| lia| exact PP'| exact PAG1| exact SELOK| exact SEL1| exact SELM1| exact POS1| assumption| exact MU1| exact WM1| exact V1392| exact SHe| exact SHp| exact K].
        subst P1n. rewrite zget_zset_same. reflexivity.
      - assert (n = 0)%nat by lia. subst n. cbn [sm_selmtf] in K.
        lstep.
        enter_with (K _ pm1 _ _ _ _ _ _); [st_eq| exact PP'| exact PAG1| exact SEL1| exact SELM1| exact POS1| assumption| exact MU1| exact WM1]. }
    (* [comment removed for export] *)
    lstep; if_cases Kq; zify_cond_z Kq.
    - (* [comment removed for export] *)
      assert (M1 : (0 < mm)%Z) by (destruct (Z.eq_dec mm 0) as [EQ|]; [exfalso; rewrite EQ in Emm; lia| lia]).
      lstep.
      enter_with (A0_sc_search (Z.to_nat mm) 0 mm Pm pm i6 m m nSel (zget sel i));
        [st_eq| lia| lia| lia| exact P1| lia| exact Emm| intros k Hk; apply NOT; lia| intros; lia| intros k Hk; apply PAG; lia
        | exact POS| exact MI| apply munch_refl| apply wmono_refl| eapply shpW_sub; [exact SHp| exact MU| sub_fp_solve| lia| lia]| | lia].
      clear POS MI. intros m1 pm1 xt0 xa6 xa7 SH1 REST1 POS1 MI1 MU1 WM1.
      transport_after_call a0segs m m1 MU1 WM1. clear MU1 WM1.
      eapply (K8 m1 pm1); [exact SH1| exact REST1| exact POS1| exact SELM| exact SEL| exact MI1| exact MU| exact WM].
    - (* [comment removed for export] *)
      assert (M0 : mm = 0%Z) by (destruct (Z.eq_dec mm 0) as [|NE]; [assumption| exfalso; apply (NOT 0%Z); lia]).
      lstep. lstep. subst mm.
      enter_with (K8 m pm _ _ _); [st_eq| intros; lia| intros k Hk; apply PAG; lia| exact POS| exact SELM| exact SEL| exact MI| exact MU| exact WM].
  Qed.

  (* [comment removed for export] *)
  Notation CR ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t s6 s7 t3 t4 t5 t6 :=
    (mkR ra cP gp tp t0 t1 t2 s0 cP a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 3004) (Z_to_bv 64 (E + 37708 + 258 * t)) cSB (Z_to_bv 64 t) s6 s7
         (Z_to_bv 64 (-1)) (Z_to_bv 64 18) (Z_to_bv 64 1032) (Z_to_bv 64 258) t3 t4 t5 t6).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma A0_sc_minmax : forall (n : nat) (v t mn mx : Z) (len : zarr) (W : list (Z * Z)) (m mf : word -> option byte)
      (ra t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    (v + Z.of_nat n = A)%Z -> (0 <= v)%Z -> (1 <= n)%nat -> (0 <= t < nG)%Z -> (0 <= mn <= 32)%Z -> (0 <= mx <= 17)%Z ->
    (forall tt vv, 0 <= tt < nG -> 0 <= vv < A -> zdef len (258 * tt + vv) = true /\ 1 <= zget len (258 * tt + vv) <= 17)%Z ->
    u8arr a0segs m (E + 37708) (ovb len (jseg J 37708 1548) 1548) ->
    munch W mf m -> shzW a0segs W mf E (E + ESTATE_SIZE) ->
    (forall (a3 : word), let r := sm_minmax n len t v mn mx in
      (0 <= fst r <= 32)%Z -> (0 <= snd r <= 17)%Z ->
      evt a0segs Q (MS (CR ra t0 t1 t2 (Z_to_bv 64 (E + 37708 + 258 * t + A)) (Z_to_bv 64 0) (Z_to_bv 64 (E + 37708 + 258 * t + A)) a3 a4 a5 a6 a7 t (Z_to_bv 64 (snd r)) (Z_to_bv 64 (fst r)) t3 t4 t5 t6)
                       F (Z_to_bv 64 0x8f474) fc None m (seg_rom a0segs))) ->
    evt a0segs Q (MS (CR ra t0 t1 t2 (Z_to_bv 64 (E + 37708 + 258 * t + v)) (Z_to_bv 64 (A - v)) (Z_to_bv 64 (E + 37708 + 258 * t + v)) a3 a4 a5 a6 a7 t (Z_to_bv 64 mx) (Z_to_bv 64 mn) t3 t4 t5 t6)
                     F (Z_to_bv 64 0x8f424) fc None m (seg_rom a0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros v t mn mx len W m mf ra t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Hv Hv0 Hn Ht Hmn Hmx LENF LEN MU SHe K.
    openCX. unfold ESTATE_SIZE in SHe.
    pose proof (jseg_length J 37708 1548 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ6. pose proof (ovb_length_nat len (jseg J 37708 1548) 1548) as LL.
    destruct (LENF t v ltac:(lia) ltac:(lia)) as [Dl Rl].
    cbn [sm_minmax] in K. set (l := zget len (258 * t + v)) in *.
    (* [comment removed for export] *)
    arun_to 0x8f434%Z.
    pose proof (ovb_read1 a0segs m (E + 37708) len (jseg J 37708 1548) 1548 (258 * t + v) _ LEN ltac:(lia) Dl ltac:(unfold wa; f_equal; lia)) as RD.
    fold l in RD. lstep. clear RD. cbv beta. rewrite (unsigned_lit8 l) by lia.
    (* [comment removed for export] *)
    assert (STEP : forall (xs6 xs7 : word), xs6 = Z_to_bv 64 (if mx <? l then l else mx)%Z -> xs7 = Z_to_bv 64 (if l <? mn then l else mn)%Z ->
      evt a0segs Q (MS (CR ra t0 t1 t2 (Z_to_bv 64 (E + 37708 + 258 * t + v)) (Z_to_bv 64 (A - v)) (Z_to_bv 64 (E + 37708 + 258 * t + v)) (Z_to_bv 64 l) a4 a5 a6 a7 t xs6 xs7 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x8f448) fc None m (seg_rom a0segs))).
    { intros xs6 xs7 -> ->.
      lstep. lstep. lstep. lstep; if_cases Ke; zify_cond_z Ke.
      - enter_with (IH (v + 1)%Z t (if l <? mn then l else mn)%Z (if mx <? l then l else mx)%Z len W m mf);
          [st_eq| lia| lia| lia| lia| destruct (Z.ltb_spec l mn); lia| destruct (Z.ltb_spec mx l); lia| exact LENF| exact LEN| exact MU| exact SHe| exact K].
      - assert (n = 0)%nat by lia. subst n. cbn [sm_minmax] in K.
        lstep.
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
  Notation Was := [(E + 39256, E + 45448); (P + 208, P + 216); (P - 16, P)]%Z.
  Lemma A0_sc_assign : forall (n t : nat) (code len : zarr) (nSel lo : Z) (H : sdw) (w16 w24 : word) (m mf : word -> option byte)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 t3 t4 t5 t6 : word),
    (Z.of_nat t + Z.of_nat n = nG)%Z -> (1 <= n)%nat ->
    (forall tt vv, 0 <= tt < nG -> 0 <= vv < A -> zdef len (258 * tt + vv) = true /\ 1 <= zget len (258 * tt + vv) <= 17)%Z ->
    u8arr a0segs m (E + 37708) (ovb len (jseg J 37708 1548) 1548) ->
    u32arr a0segs m (E + 39256) (ovw code (jseg J 39256 6192) 1548) ->
    rw_cells a0segs m (P + 16) (sd_loA cx A nG FB SHF SHE w16 w24) ->
    rw_cells a0segs m (P + 160) (sd_loB cx A nG (e_nInUse e0) SHE (Z_to_bv 64 (E + 37708 + 258 * Z.of_nat t))) ->
    rw_cells a0segs m (P + 1336) (sd_hi cx A nG nSel H) ->
    mem_inv a0segs m -> stk a0segs m lo P -> (lo + 16 <= P)%Z -> (CEIL <= lo)%Z ->
    munch Was mf m -> wmono a0segs mf m ->
    acoW Was mf -> shzW a0segs Was mf E (E + ESTATE_SIZE) ->
    (forall m' (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 t3 t4 t5 : word),
      u8arr a0segs m' (E + 37708) (ovb len (jseg J 37708 1548) 1548) ->
      u32arr a0segs m' (E + 39256) (ovw (sm_assign n code len A (Z.of_nat t)) (jseg J 39256 6192) 1548) ->
      rw_cells a0segs m' (P + 16) (sd_loA cx A nG FB SHF SHE w16 w24) ->
      rw_cells a0segs m' (P + 160) (sd_loB cx A nG (e_nInUse e0) SHE (Z_to_bv 64 (E + 37708 + 258 * nG))) ->
      rw_cells a0segs m' (P + 1336) (sd_hi cx A nG nSel H) ->
      mem_inv a0segs m' -> stk a0segs m' lo P ->
      munch Was mf m' -> wmono a0segs mf m' ->
      evt a0segs Q (MS (CR ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 nG s6 s7 t3 t4 t5 (Z_to_bv 64 E))
                       F (Z_to_bv 64 0x8f4d8) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (CR ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z.of_nat t) s6 s7 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x8f408) fc None m (seg_rom a0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros t code len nSel lo H w16 w24 m mf ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 t3 t4 t5 t6 Ht Hn LENF LEN CODE LOA LOB HI MI ST STK CLO MU WM ACW SHe K.
    openCX. unfold CEIL in CLO. assert (HAd : A = (e_nInUse e0 + 2)%Z) by reflexivity. pose proof SHe as SHe'. unfold ESTATE_SIZE in SHe.
    pose proof (jseg_length J 37708 1548 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ6. pose proof (jseg_length J 39256 6192 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ7.
    unfold sd_loA in LOA. unfold sd_loB in LOB. unfold sd_hi in HI. cbv zeta in LOA, LOB, HI.
    cbn [sm_assign] in K.
    pose proof (sm_minmax_spec (Z.to_nat A) len (Z.of_nat t) 0 32 0 ltac:(lia) ltac:(lia)) as MM. cbv zeta in MM.
    destruct (sm_minmax (Z.to_nat A) len (Z.of_nat t) 0 32 0) as [mn mx] eqn:EMM. cbn [fst snd] in MM. cps_destruct MM as (M1 & M2 & M3 & M4).
    rewrite Z2Nat.id in M3, M4 by lia.
    destruct (M4 ltac:(intros j Hj; apply (proj2 (LENF (Z.of_nat t) j ltac:(lia) ltac:(lia))))) as [N1 N2].
    pose proof (M3 0%Z ltac:(lia)) as M30. pose proof (proj2 (LENF (Z.of_nat t) 0%Z ltac:(lia) ltac:(lia))) as L00.
    assert (MN : (1 <= mn <= 17)%Z) by lia. assert (MX : (1 <= mx <= 17)%Z) by lia.
    (* [comment removed for export] *)
    lstep. lstep; if_cases K0; zify_cond_z K0; [exfalso; revert K0; rewrite ?signed_lit by lia; lia|].
    lstep. lstep. lstep. lstep. lstep.
    enter_with (A0_sc_minmax (Z.to_nat A) 0 (Z.of_nat t) 32 0 len Was m mf);
      [st_eq| lia| lia| lia| lia| lia| lia| exact LENF| exact LEN| exact MU| exact SHe'|].
    intros ya3. cbv zeta. rewrite EMM. cbn [fst snd]. intros _ _.
    (* [comment removed for export] *)
    lstep; if_cases K1; zify_cond_z K1; [| exfalso; lia].
    lstep. lstep; if_cases K2; zify_cond_z K2; [| exfalso; lia].
    (* [comment removed for export] *)
    lstep. lstep. lstep. lstep. lstep. lstep. lstep. lstep. lstep.
    pose proof (ACW m MU) as AC.
    call (A0_hbAssignCodes_Z _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m (E + 39256)%Z (E + 37708)%Z (258 * Z.of_nat t)%Z (258 * Z.of_nat t)%Z mn mx A 1548%Z 1548%Z lo P code len (jseg J 39256 6192) (jseg J 37708 1548));
        [ lia | f_equal; lia | f_equal; lia | reflexivity | reflexivity | reflexivity
        | exact CODE | exact LEN | exact MI | exact ST | lia
        | lia | lia | lia | lia | lia | lia | lia
        | clear - ME; Z.div_mod_to_equations; lia | lia | unfold CEIL; lia | lia | unfold CEIL; lia
        | unfold apart; lia | lia | lia
        | intros i Hi; destruct (LENF (Z.of_nat t) i ltac:(lia) Hi) as [D R]; split; [exact D| apply M3; lia]
        | exact AC | lia | lia | lia
        | eapply (shzW_sub a0segs _ _ mf m); [exact SHe| exact MU| sub_fp_solve| lia| lia]
        | eapply (shzW_sub a0segs _ _ mf m); [exact SHe| exact MU| sub_fp_solve| lia| lia] | ].
    clear AC.
    (* [comment removed for export] *)
    lstep. lstep. lstep. wstep. lstep. lstep. lstep. lstep; if_cases Ke; zify_cond_z Ke.
    - replace (E + 37708 + 258 * Z.of_nat t + 258)%Z with (E + 37708 + 258 * Z.of_nat (S t))%Z in LOB by lia.
      enter_with (IH (S t) _ len nSel lo H w16 w24 _ mf);
        [st_eq| lia| lia| exact LENF| exact LEN| eassumption| unfold sd_loA; cbv zeta; exact LOA| unfold sd_loB; cbv zeta; exact LOB| unfold sd_hi; cbv zeta; exact HI
        | assumption| assumption| lia| unfold CEIL; lia| assumption| assumption| exact ACW| exact SHe'|].
      intros mm; intros *. replace (Z.of_nat (S t)) with (Z.of_nat t + 1)%Z by lia. apply K.
    - assert (n = 0)%nat by lia. subst n. cbn [sm_assign] in K.
      replace (E + 37708 + 258 * Z.of_nat t + 258)%Z with (E + 37708 + 258 * nG)%Z in LOB by lia.
      enter_with (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
        [st_eq| exact LEN| eassumption| unfold sd_loA; cbv zeta; exact LOA| unfold sd_loB; cbv zeta; exact LOB| unfold sd_hi; cbv zeta; exact HI| assumption| assumption| assumption| assumption].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma pos_reader : forall (W : list (Z * Z)) (m : word -> option byte),
    rw_cells a0segs m (SHF + 16) [C1 (Z_to_bv 8 6)] -> app_fp W -> shpW a0segs W m (FB + 128) (FB + 134).
  Proof.
    intros W m SHC AW. pose proof AF as [AF1 AF2]. bz_ceil.
    assert (B : bytes_at a0segs m (shad (FB + 128)) (ushadow 6)).
    { unfold shad, SHB. rewrite (sanchor_addr_lit FB SHF 128 16 AF eq_refl).
      destruct SHC as [[_ B] _]. cbn [cells_bytes cbytes app] in B. exact B. }
    replace (FB + 134)%Z with (FB + 128 + 6)%Z by lia.
    refine (proj2 (sh_of_ushadow a0segs W m (FB + 128) 6 B _ ltac:(lia) ltac:(lia) _ AW)).
    - clear - AF1. Z.div_mod_to_equations. lia.
    - unfold CEIL in FBH. change (2^47)%Z with 140737488355328%Z. lia.
  Qed.
  Lemma app_fp_Wmtf : app_fp Wmtf.
  Proof. pose proof OFFE as O1. pose proof OFFF as O2. unfold id in O1, O2. cbn [app_fp]. unfold SH_LO, SH_HI in *. repeat split; lia. Qed.
  Lemma app_fp_Wpos : app_fp Wpos.
  Proof. pose proof OFFF as O2. unfold id in O2. cbn [app_fp]. unfold SH_LO, SH_HI in *. repeat split; lia. Qed.

  Notation WC := [(E + 19706, E + 37708); (E + 39256, E + 45448); (P + 208, P + 216); (P + 1344, P + 1440); (FB + 128, FB + 134); (SHF + 16, SHF + 17); (P - 16, P)]%Z.
  Lemma A0_smC_body : forall (c0 f0 p0 h0 w0 q0 : zarr) (m : word -> option byte) (w16 w24 v1336 v1360 : word) (CO FV totc gs : Z) (i6 : list byte) (lo : Z)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word),
    let it := smB_it e0 c0 f0 h0 w0 q0 in let nSel := smB_nsel e0 c0 f0 h0 w0 q0 in
    sd_facts (est_C e0 c0 f0 p0 h0 w0 q0) nG nSel ->
    u8arr a0segs m (E + 1704) (ovb (it_sel it) (jseg J 1704 18002) 18002) ->
    u8arr a0segs m (E + 19706) (ovb (e_selectorMtf e0) (jseg J 19706 18002) 18002) ->
    u8arr a0segs m (E + 37708) (ovb (it_len it) (jseg J 37708 1548) 1548) ->
    u32arr a0segs m (E + 39256) (ovw (e_code e0) (jseg J 39256 6192) 1548) ->
    rw_cells a0segs m (P + 16) (sd_loA cx A nG FB SHF SHE w16 w24) ->
    rw_cells a0segs m (P + 160) (sd_loB cx A nG (e_nInUse e0) SHE (Z_to_bv 64 (E + 37708))) ->
    rw_cells a0segs m (P + 1336) [C8 v1336] ->
    rw_cells a0segs m (P + 1344) (sm_hi cx e0 CO FV v1360 totc gs) ->
    u8arr a0segs m (FB + 128) i6 -> Z.of_nat (length i6) = 6%Z ->
    rw_cells a0segs m (SHF + 16) [C1 sf8b] ->
    stk a0segs m lo P -> (lo + 16 <= P)%Z -> (CEIL <= lo)%Z -> mem_inv a0segs m ->
    acoW WC m -> shzW a0segs WC m E (E + ESTATE_SIZE) ->
    (forall m' (i6' : list byte) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 : word),
       u8arr a0segs m' (E + 1704) (ovb (it_sel it) (jseg J 1704 18002) 18002) ->
       u8arr a0segs m' (E + 19706) (ovb (snd (smC_pm e0 c0 f0 p0 h0 w0 q0)) (jseg J 19706 18002) 18002) ->
       u8arr a0segs m' (E + 37708) (ovb (it_len it) (jseg J 37708 1548) 1548) ->
       u32arr a0segs m' (E + 39256) (ovw (smC_code e0 c0 f0 h0 w0 q0) (jseg J 39256 6192) 1548) ->
       rw_cells a0segs m' (P + 16) (sd_loA cx A nG FB SHF SHE w16 w24) ->
       rw_cells a0segs m' (P + 160) (sd_loB cx A nG (e_nInUse e0) SHE (Z_to_bv 64 (E + 37708 + 258 * nG))) ->
       rw_cells a0segs m' (P + 1336) (sd_hi cx A nG nSel (SDW v1336 (Z_to_bv 64 (E + 37708)) (Z_to_bv 64 999999999) (Z_to_bv 64 nSel) (Z_to_bv 64 CO) (Z_to_bv 64 FV)
                                                             (Z_to_bv 64 (E + 45448)) (Z_to_bv 64 3005))) ->
       u8arr a0segs m' (FB + 128) i6' -> Z.of_nat (length i6') = 6%Z ->
       rw_cells a0segs m' (SHF + 16) [C1 sf8b] ->
       stk a0segs m' lo P -> mem_inv a0segs m' -> munch WC m m' -> wmono a0segs m m' ->
       evt a0segs Q (MS (mkR ra cP gp tp t0 t1 t2 s0 cP a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 cSB s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 (Z_to_bv 64 E))
                         F (Z_to_bv 64 0x8f4d8) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR ra cP gp tp t0 t1 t2 s0 cP a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 cSB (Z_to_bv 64 nSel) s6 s7 s8 s9 (Z_to_bv 64 nG) s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x8f29c) fc None m (seg_rom a0segs)).
  Proof.
    intros c0 f0 p0 h0 w0 q0 m w16 w24 v1336 v1360 CO FV totc gs i6 lo ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s6 s7 s8 s9 s11 t3 t4 t5 t6.
    cbv zeta. intros SDF SEL SELM LEN CODE LOA LOB C1336 HIs POS L6 SHC ST STK CLO MI ACW SHe K.
    openCX. unfold CEIL in CLO. assert (HAd : A = (e_nInUse e0 + 2)%Z) by reflexivity.
    pose proof CEP as CEP'. unfold CEIL in CEP'. pose proof FBH as FBH'. unfold CEIL in FBH'. pose proof SHL as SHL'. pose proof SHH as SHH'. unfold SH_LO, SH_HI in SHL', SHH'.
    set (it := smB_it e0 c0 f0 h0 w0 q0) in *. set (nSel := smB_nsel e0 c0 f0 h0 w0 q0) in *.
    pose proof SDF as SF. unfold sd_facts in SF. cbv zeta in SF.
    cbn [e_nInUse e_nMTF e_arr1 e_inUse e_selectorMtf e_selector e_len e_code est_C] in SF.
    cps_destruct SF as (FA & FG & FS & FM & F35 & FZB & FMV & FIU & FSM & FSEL & FLEN & FCODE & FCNT).
    change (e_nInUse e0 + 2)%Z with A in FA, FMV, FLEN, FCODE. fold it in FSEL, FLEN.
    unfold sd_loA in LOA. unfold sd_loB in LOB. unfold sm_hi in HIs. cbv zeta in LOA, LOB, HIs.
    pose proof (munch_refl WC m) as MU0. pose proof (wmono_refl a0segs m) as WM0.
    (* [comment removed for export] *)
    lstep. lstep. lstep. lstep. lstep; if_cases K0; zify_cond_z K0; [| exfalso; revert K0; rewrite ?signed_lit by lia; lia].
    (* [comment removed for export] *)
    lstep. lstep. lstep. change (le1 (Z_to_bv 64 6)) with [Z_to_bv 8 6]. mem_after_store.
    (* [comment removed for export] *)
    lstep. lstep.
    (* [comment removed for export] *)
    lazymatch type of POS with u8arr _ ?mm _ _ =>
      pose proof (ovb_init a0segs mm (FB + 128) 6 i6 ltac:(replace (Z.to_nat 6) with (length i6) by lia; exact (rw_cells_of_u8arr a0segs mm _ i6 POS)) ltac:(lia)) as POS' end.
    clear POS. rename POS' into POS.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (A0_sc_posinit (Z.to_nat nG) 0 znew i6 mm mm nSel);
        [st_eq| lia| lia| lia| exact POS| exact MI| apply munch_refl| apply wmono_refl| apply pos_reader; [exact SHC| exact app_fp_Wpos] |] end.
    clear POS MI. intros m1 xa0 xa2 xa3 POS MI MU1 WM1.
    lazymatch type of MU1 with munch _ ?ma ?mb => transport_after_call a0segs ma mb MU1 WM1 end. clear MU1 WM1.
    (* [comment removed for export] *)
    lstep; if_cases K1; zify_cond_z K1; [exfalso; revert K1; rewrite ?signed_lit by lia; lia|].
    lstep.
    assert (PD0 : zdef (yy_init (Z.to_nat nG) znew 0) 0 = true) by (rewrite yy_init_def; replace ((0 <=? 0) && (0 <? 0 + Z.of_nat (Z.to_nat nG)))%bool with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia); reflexivity).
    assert (PV0 : zget (yy_init (Z.to_nat nG) znew 0) 0 = 0%Z) by (rewrite yy_init_get; replace ((0 <=? 0) && (0 <? 0 + Z.of_nat (Z.to_nat nG)))%bool with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia); reflexivity).
    pose proof (ovb_read1 a0segs m1 (FB + 128) _ i6 6 0 _ POS ltac:(lia) PD0 ltac:(unfold wa; f_equal; lia)) as RD.
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
    enter_with (A0_sc_mtf (Z.to_nat nSel) 0 (yy_init (Z.to_nat nG) p0 0) (yy_init (Z.to_nat nG) znew 0) (it_sel it) (e_selectorMtf e0) i6 m1 m1 nSel);
      [st_eq| lia| lia| lia| lia| exact PPm| exact PAG0| exact FSEL| exact SEL| exact SELM| exact POS| exact MI| apply munch_refl| apply wmono_refl
      | eapply (frdW_cell_at a0segs _ _ (P + 1344) _ 48); [apply frdW_intro; [exact HIs| cbn [disjoint_from]; simpl_sizes; Lib.Step.slia]| reflexivity| lia]
      | eapply (shzW_sub a0segs _ _ m m1); [exact SHe| exact MU0| sub_fp_solve| lia| lia]
      | apply pos_reader; [exact SHC| exact app_fp_Wmtf] |].
    clear SEL SELM POS MI. intros m2 pm2 yt0 ya0 ya4 ya5 ya6 ya7. cbv zeta. intros PP2 PAG2 SEL SELM POS MI MU2 WM2.
    lazymatch type of MU2 with munch _ ?ma ?mb => transport_after_call a0segs ma mb MU2 WM2 end. clear MU2 WM2.
    change (sm_selmtf (Z.to_nat nSel) (yy_init (Z.to_nat nG) p0 0) (it_sel it) (e_selectorMtf e0) 0) with (smC_pm e0 c0 f0 p0 h0 w0 q0) in SELM.
    (* [comment removed for export] *)
    wstep. wstep. lstep. lstep. lstep. lstep. lstep. lstep. lstep.
    lstep. change (le1 (Z_to_bv 64 (-8))) with [sf8b]. mem_after_store.
    lstep. lstep. lstep. (wstep; lit_store). lstep. wstep. lstep. lstep.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (HI : rw_cells a0segs mm (P + 1336) (sd_hi cx A nG nSel (SDW v1336 (Z_to_bv 64 (E + 37708)) (Z_to_bv 64 999999999) (Z_to_bv 64 nSel) (Z_to_bv 64 CO) (Z_to_bv 64 FV)
                                                             (Z_to_bv 64 (E + 45448)) (Z_to_bv 64 3005)))) end.
    { unfold sd_hi. cbv zeta. cbn [w1336 w1344 w1352 w1360 w1376 w1384 w1400 w1408].
      lazymatch goal with |- rw_cells _ ?mm _ (?c1 :: ?rest) => change (rw_cells a0segs mm (P + 1336) ([c1] ++ rest)) end.
      apply (proj2 (rw_cells_app2 _ _ _ _ _)). split; [exact C1336|].
      cbn [cells_size csize Nat.add]. replace (P + 1336 + Z.of_nat 8)%Z with (P + 1344)%Z by lia.
      lazymatch goal with H : rw_cells _ _ (P + 1344)%Z ?L |- rw_cells _ _ _ ?L2 => first [exact H| replace L2 with L; [exact H| CmpFast.rlf]] end. }
    clear C1336 HIs.
    (* [comment removed for export] *)
    lazymatch type of LOB with rw_cells _ ?mm _ _ =>
      assert (LOB0 : rw_cells a0segs mm (P + 160) (sd_loB cx A nG (e_nInUse e0) SHE (Z_to_bv 64 (E + 37708 + 258 * Z.of_nat 0%nat)))) end.
    { unfold sd_loB; cbv zeta. replace (E + 37708 + 258 * Z.of_nat 0%nat)%Z with (E + 37708)%Z by (change (Z.of_nat 0) with 0%Z; ring). exact LOB. }
    clear LOB. rename LOB0 into LOB.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    enter_with (A0_sc_assign (Z.to_nat nG) 0%nat (e_code e0) (it_len it) nSel lo _ w16 w24 mm mm);
      [st_eq| lia| lia| exact FLEN| exact LEN| exact CODE| unfold sd_loA; cbv zeta; exact LOA| exact LOB| exact HI| exact MI| exact ST| lia| unfold CEIL; lia
      | apply munch_refl| apply wmono_refl
      | eapply (acoW_sub _ _ m mm); [exact ACW| exact MU0| sub_fp_solve]
      | eapply (shzW_sub a0segs _ _ m mm); [exact SHe| exact MU0| sub_fp_solve| lia| lia] |] end.
    clear LEN CODE LOA LOB HI MI ST. intros m4 zra z0 z1 z2 za0 za1 za2 za3 za4 za5 za6 za7 zs6 zs7 z3 z4 z5 LEN CODE LOA LOB HI MI ST MU4 WM4.
    lazymatch type of MU4 with munch _ ?ma ?mb => transport_after_call a0segs ma mb MU4 WM4 end. clear MU4 WM4.
    change (sm_assign (Z.to_nat nG) (e_code e0) (it_len it) A (Z.of_nat 0)) with (smC_code e0 c0 f0 h0 w0 q0) in CODE.
    (* [comment removed for export] *)
    destruct (u8arr_of_cells a0segs _ _ _ (rw_cells_of_u8arr a0segs _ _ _ POS)) as [PJ LPJ]. cbn [cells_bytes cbytes app] in PJ, LPJ. rewrite app_nil_r in PJ.
    enter_with (K m4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
      [st_eq| exact SEL| exact SELM| exact LEN| exact CODE| exact LOA| exact LOB| exact HI
      | exact PJ| rewrite ovb_length; lia| exact SHC| exact ST| exact MI| exact MU0| exact WM0].
  Qed.
End SC3.
End ACeilS1.
