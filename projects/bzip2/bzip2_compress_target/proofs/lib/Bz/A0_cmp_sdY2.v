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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCStream BzCState BzCMtf BzArrD BzCLemmas1 CmpMem BzSepTac CmpCut CmpCutSM CmpCutSmA CmpCutSD CmpSdKit CmpSdTac CmpArith CmpArith2 BzCNumZ BzWalkArith2 BzWalkArith4 BzCLemmasSd BzCLemmasSd2 CmpFsKit CmpHmKit.
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
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith2.CmpSdArith OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasSd2.BzCLemmasSd3.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_sdV.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require A0_cmp_sdY.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Section SDY2.
  Variables (cx : cctx) (Q : machine_state -> Prop).
  Variables (gp tp s0 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (P SHE FB SHF FL A nG : Z) (w16 w24 : word).
  Notation usp := (bv_unsigned s0). Notation E := (c_E cx).
  Hypothesis FBL : (0 < FB)%Z. Hypothesis FBH : (FB + 256 <= 18446744073709551616)%Z.
  Hypothesis SHL : (0 < SHF)%Z. Hypothesis SHH : (SHF + 32 <= 18446744073709551616)%Z.
  Hypothesis FLL : (0 < FL)%Z. Hypothesis FLH : (FL + 1 <= 18446744073709551616)%Z.
  Hypothesis USPL : (1616 <= usp)%Z.
  (* [comment removed for export] *)
  Hypothesis SFSH : id ((FB + 256 <= SHF)%Z \/ (SHF + 32 <= FB)%Z).
  Notation cSB := (Z_to_bv 64 2147450880). Notation cP := (Z_to_bv 64 P).
  Notation Wepi1 := [(SHF, SHF + 32); (FB, FB + 8)]%Z.
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac sbl := wstep; lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?w)) _) => rewrite (le1_lit w); mem_after_store end.
  Ltac sbz := wstep; lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 0))) _) => change (le1 (Z_to_bv 64 0)) with [z8]; mem_after_store
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 0)) _) => change (Z_to_le_bytes 1 0) with [z8]; mem_after_store
    | _ => idtac end.
  Ltac rdv V := lazymatch goal with MU' : munch _ _ ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    let RO := fresh "RO" in pose proof (V mm MU') as RO; unfold sd_loA in RO; cbv zeta in RO; wstep; clear RO end.

  Lemma A0_sm_E1 : forall (m : word -> option byte) (sh : list byte) (w0 : word)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    Z.of_nat (length sh) = 32%Z ->
    u8arr a0segs m SHF sh -> rw_cells a0segs m FB [C8 w0] ->
    mem_inv a0segs m ->
    frdW a0segs Wepi1 m (P + 16) (sd_loA cx A nG FB SHF SHE w16 w24) ->
    (forall m' (a0' : word),
        rw_cells a0segs m' SHF A0_cmp_sdY.sh_f5 -> rw_cells a0segs m' FB [C8 (Z_to_bv 64 1172321806)] ->
        mem_inv a0segs m' -> munch Wepi1 m m' -> wmono a0segs m m' ->
        evt a0segs Q (MS (mkR ra cP gp tp t0 t1 t2 s0 cP a0' (Z_to_bv 64 FB) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 SHF) s3 cSB s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 0x954f4) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR ra cP gp tp t0 t1 t2 s0 cP a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 SHF) s3 cSB s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 0x95440) fc None m (seg_rom a0segs)).
  Proof.
    intros m sh w0 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 L32 SHU HD MI VA K.
    pose proof (munch_refl Wepi1 m) as MU. pose proof (wmono_refl a0segs m) as WM.
    (* [comment removed for export] *)
    pose proof (rw_cells_of_u8arr a0segs m SHF sh SHU) as SHC. replace (length sh) with 32%nat in SHC by lia. clear SHU.
    apply (rw_cells_split_CB a0segs _ _ [] 32 _ [] (repeat 1%nat 32)) in SHC; [| reflexivity].
    cbn [repeat mk_CB_cells app] in SHC.
    repeat (match type of SHC with context [CB 1 (firstn ?a ?b)] => let v := fresh "shb" in set (v := firstn a b) in SHC; clearbody v end).
    (* [comment removed for export] *)
    wstep. do 5 sbl.
    (* [comment removed for export] *)
    wstep. wstep. rdv VA. (wstep; lit_store).
    (* [comment removed for export] *)
    rdv VA. wstep; if_cases Kz; zify_cond_z Kz; [exfalso; lia|].
    (* [comment removed for export] *)
    wstep. do 32 sbl.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => eapply (K mm) end; [unfold A0_cmp_sdY.sh_f5, A0_cmp_sdY.sf5b; exact SHC| exact HD| assumption| exact MU| exact WM].
  Qed.

  (* [comment removed for export] *)
  Lemma A0_sm_E1b : forall (m : word -> option byte)
      (ra sp t0 t1 t2 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    ro_cells a0segs m (FB + 248) [C8 (Z_to_bv 64 FL)] ->
    evt a0segs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 FL) (Z_to_bv 64 FB) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x954f8) fc None m (seg_rom a0segs)) ->
    evt a0segs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 FB) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x954f4) fc None m (seg_rom a0segs)).
  Proof.
    intros m ra sp t0 t1 t2 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FLP K.
    wstep. exact K.
  Qed.

  (* [comment removed for export] *)
  Lemma A0_sm_E2 : forall (m : word -> option byte) (b1 : byte)
      (ra sp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    rw_cells a0segs m FL [C1 b1] -> mem_inv a0segs m ->
    (forall m', rw_cells a0segs m' FL [C1 z8] -> mem_inv a0segs m' -> munch [(FL, FL + 1)]%Z m m' -> wmono a0segs m m' ->
       evt a0segs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 FL) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x954fc) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 FL) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x954f8) fc None m (seg_rom a0segs)).
  Proof.
    intros m b1 ra sp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FLG MI K.
    pose proof (munch_refl [(FL, FL + 1)]%Z m) as MU. pose proof (wmono_refl a0segs m) as WM.
    sbz.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => eapply (K mm) end; [exact FLG| assumption| exact MU| exact WM].
  Qed.

  (* [comment removed for export] *)
  Lemma A0_sm_E3 : forall (m : word -> option byte) (f8 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 rra : word)
      (ra sp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    rw_cells a0segs m (usp + -112) [C8 f8; C8 r11; C8 r10; C8 r9; C8 r8; C8 r7; C8 r6; C8 r5; C8 r4; C8 r3; C8 r2; C8 r1; C8 r0; C8 rra] ->
    evt a0segs Q (MS (mkR rra s0 gp tp t0 t1 t2 r0 r1 a0 a1 a2 a3 a4 a5 a6 a7 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 t3 t4 t5 t6)
                      (bvmap_set 8 f8 F) (ret_pc rra) fc None m (seg_rom a0segs)) ->
    evt a0segs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 0x954fc) fc None m (seg_rom a0segs)).
  Proof.
    intros m f8 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 rra ra sp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SAV K.
    pose proof (bv_unsigned_in_range _ s0) as RSP. unfold bv_modulus in RSP. change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z in RSP.
    (* [comment removed for export] *)
    wstep. wstep.
    do 13 wstep. wstep. wstep. wstep.
    exact K.
  Qed.
End SDY2.
End ACeilS1.
