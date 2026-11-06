(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsS0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzTac BzTac2 BzArr BzCMem BzCStream BzCState BzCMtf BzArrD BzCRebuildF CmpMem CmpCut CmpCut0 CmpCutSM CmpCutSmA CmpCutSmA0 BzCFactsSmA CmpFsKit0 CmpHmKit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require S0_cmp_smB.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require S0_cmp_smB.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMtf OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCRebuildF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmA0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsSmA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpFsKit0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpHmKit OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_cmp_smB.S0_cmp_smA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_cmp_smB.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Musl Require Import S0_memset.
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


Section S0SMZ.
  Variables (cx : cctx) (g : eg) (e : est) (Q : machine_state -> Prop).
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (sv : word).
  (* [comment removed for export] *)
  Variables (xs9 xs10 xs11 : word).
  Hypothesis CX : cctx_ok cx. Hypothesis SEP : cctx_sep cx. Hypothesis IMG : cctx_img S0C cx. Hypothesis SF : smA_facts e.
  Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation A2 := (c_A2 cx). Notation J := (c_J cx).
  Notation usp := (bv_unsigned sp).
  Notation mf := (e_mtfFreq e). Notation A := (sm_alpha e). Notation nG := (smA_ng e). Notation nMTF := (sm_nmtf e). Notation nInUse := (e_nInUse e).
  (* [comment removed for export] *)
  Ltac simpl_arr_sizes ::= CmpFast.sas10.   (* [comment removed for export] *)
  Ltac openCX :=
    let H := fresh "CXL" in pose proof CX as H; bz_ceil; bz_params; unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in H; cbv zeta in H;
    cps_destruct H as (?XE0 & ?XE1 & ?XA10 & ?XA11 & ?XA20 & ?XA21 & ?XF0 & ?XF1 & ?Xb0 & ?Xb1 & ?Xf0 & ?Xf1 & ?ME & ?MA1 & ?MA2 & ?MF & ?Mb & ?Mf & ?LJ & ?LJb);
    let S := fresh "SP" in pose proof SEP as S; unfold cctx_sep, apart, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE in S; cbv zeta in S;
    cps_destruct S as (?AEA1 & ?AEA2 & ?AEF & _ & _ & ?AA12 & ?A1F & _).
  Ltac openSF :=
    let H := fresh "SFL" in pose proof SF as H; unfold smA_facts in H; cbv zeta in H; cps_destruct H as (?NI & ?NM & ?MFD & ?IPK & ?IPT).
  (* [comment removed for export] *)
  Notation OFS := (258 * nG + 37450 + A)%Z.
  Notation RI ra t0 a0 a1 a2 a3 a4 s1 s2 s4 s6 s7 s8 s9 t3 t4 t5 t6 :=
    (mkR ra sp gp tp t0 (Z_to_bv 64 3) (Z_to_bv 64 (-1)) (Z_to_bv 64 E) s1 a0 a1 a2 a3 a4 (Z_to_bv 64 (E + 676)) (Z_to_bv 64 (-258)) (Z_to_bv 64 1)
         s2 (Z_to_bv 64 OFS) s4 (Z_to_bv 64 (E + 672)) s6 s7 s8 s9 (Z_to_bv 64 (-2147483647)) (Z_to_bv 64 4294967296) t3 t4 t5 t6).

  (* [comment removed for export] *)
  Notation RMS ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1 s2 t3 t4 t5 t6 :=
    (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 E) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (-1)) (Z_to_bv 64 A) (Z_to_bv 64 (E + 672)) (Z_to_bv 64 A1) (Z_to_bv 64 (E + 128))
         (Z_to_bv 64 A) xs9 xs10 xs11 t3 t4 t5 t6).
  Lemma rw_cells_app_iff : forall segs m A pre post,
    rw_cells segs m A (pre ++ post) <-> rw_cells segs m A pre /\ rw_cells segs m (A + Z.of_nat (cells_size pre))%Z post.
  Proof.
    intros segs m A pre post. unfold rw_cells, cells_at.
    rewrite cells_wf_app, cells_bytes_app, cells_size_app, bytes_at_app.
    split.
    - intros [[[W1 W2] [B1 B2]] WR].
      rewrite (cells_bytes_length pre W1) in B2.
      rewrite Nat2Z.inj_add in WR. apply wr_at_app in WR; [|lia|lia]. destruct WR as [R1 R2].
      split; [ split; [ split; [exact W1 | exact B1] | exact R1 ] | split; [ split; [exact W2 | exact B2] | exact R2 ] ].
    - intros [[[W1 B1] R1] [[W2 B2] R2]].
      rewrite (cells_bytes_length pre W1). rewrite Nat2Z.inj_add.
      split; [ split; [ split; [exact W1 | exact W2] | split; [exact B1 | exact B2] ] |].
      apply wr_at_app; [lia|lia|]. split; [exact R1 | exact R2].
  Qed.
  Hypothesis GM : g_mtf g = true.
  Notation SLOTS22 a b c d e5 f g h i j k l m2 n o p q r s2 t u v :=
    ([C8 a; C8 b; C8 c; C8 d; C8 e5; C8 f; C8 g; C8 h; C8 i; C8 j; C8 k; C8 l; C8 m2; C8 n; C8 o; C8 p; C8 q; C8 r; C8 s2; C8 t; C8 u; C8 v]).
  Notation EH2cells := ([C4 (if g_bs g then Z_to_bv 64 (bw_buff (e_bw e)) else jw4 J 640); C4 (if g_bs g then Z_to_bv 64 (bw_live (e_bw e)) else jw4 J 644);
     C4 (Z_to_bv 64 (e_blockCRC e)); C4 (Z_to_bv 64 (e_combinedCRC e)); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 (e_blockNo e)); C4 (Z_to_bv 64 BLOCKSIZE100K); C4 (Z_to_bv 64 nMTF)]).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_smA_setup1 : forall (m : word -> option byte)
      (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w136 w144 w152 w160 w168 w176 : word) (w576 w584 w592 w600 : word)
      (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    rw_cells s0segs m (E + 640) EH2cells ->
    rw_cells s0segs m (usp + 8) (SLOTS22 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 (Z_to_bv 64 (E + 37708)) w136 w144 w152 w160 w168 w176) ->
    rw_cells s0segs m (usp + 576) [C8 w576; C8 w584; C8 w592; C8 w600; C8 (Z_to_bv 64 nInUse)] ->
    rw_cells s0segs m 0x28628 [C8 (Z_to_bv 64 0x285d8)] -> rw_cells s0segs m 0x285d8 [C8 sv] ->
    mem_inv s0segs m -> (CEIL <= usp)%Z -> (usp + 1008 <= 18446744073709551616)%Z ->
    (forall m',
      rw_cells s0segs m' (E + 640) EH2cells ->
      rw_cells s0segs m' (usp + 8) (SLOTS22 (Z_to_bv 64 37450) (Z_to_bv 64 (E + 128)) w24 (Z_to_bv 64 A) sv w48 w56 w64 w72 w80 w88 (Z_to_bv 64 nG) w104 w112 w120 (Z_to_bv 64 (E + 37708)) w136 (Z_to_bv 64 A1) w152 w160 (Z_to_bv 64 A) w176) ->
      rw_cells s0segs m' (usp + 576) [C8 w576; C8 w584; C8 (Z_to_bv 64 (flag6 nG)); C8 (Z_to_bv 64 OFS); C8 (Z_to_bv 64 nInUse)] ->
      rw_cells s0segs m' 0x28628 [C8 (Z_to_bv 64 0x285d8)] -> rw_cells s0segs m' 0x285d8 [C8 sv] ->
      mem_inv s0segs m' -> munch [(usp + 8, usp + 184); (usp + 576, usp + 616)]%Z m m' -> wmono s0segs m m' ->
      evt s0segs Q (MS (RI (Z_to_bv 64 0x15dcc) t0 (Z_to_bv 64 nG) (Z_to_bv 64 A) (Z_to_bv 64 (nG + 145)) (Z_to_bv 64 258) (Z_to_bv 64 nG)
                            (Z_to_bv 64 nMTF) (Z_to_bv 64 0) (Z_to_bv 64 (E + 37708 + 258 * (nG - 1))) (Z_to_bv 64 0) (Z_to_bv 64 (E + 128)) (Z_to_bv 64 A) xs9 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x15ebc) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RMS (Z_to_bv 64 0x15dcc) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 (E + 37708 + 258 * 6)) t3 t4 t5 t6)
                     F (Z_to_bv 64 0x15dd8) fc None m (seg_rom s0segs)).
  Proof.
    intros m w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w136 w144 w152 w160 w168 w176 w576 w584 w592 w600
           t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 EH2 SA SC GOTc SVc MI CE SPB K.
    openCX. try lin16 ME. try lin16 MA1. try lin16 MA2. try lin16 MF. try lin16 Mb. try lin16 Mf. clear AEA1 AEA2 AEF AA12 A1F. openSF. bz_ceil; bz_params; unfold CEIL in CE. assert (HA : A = (nInUse + 2)%Z) by reflexivity. assert (HM : nMTF = e_nMTF e) by reflexivity.
    pose proof (sm_nGroups_range (e_nMTF e)) as NGR. change (sm_nGroups (e_nMTF e)) with nG in NGR.
    pose proof (munch_refl [(usp + 8, usp + 184); (usp + 576, usp + 616)]%Z m) as MU0. pose proof (wmono_refl s0segs m) as WM0.
    (* [comment removed for export] *)
    wstep. try rewrite (sx32_of_Z (e_nMTF e)) by lia.
    wstep; if_cases Ka; zify_cond_z Ka; [| exfalso; lia].
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (munch_refl [(usp + 576, usp + 616)]%Z mm) as MUk; pose proof (wmono_refl s0segs mm) as WMk;
    assert (K988 : forall m2 (fl : Z) (xa0' : word), fl = flag6 nG ->
      rw_cells s0segs m2 (usp + 576) [C8 w576; C8 w584; C8 (Z_to_bv 64 fl); C8 w600; C8 (Z_to_bv 64 nInUse)] ->
      munch [(usp + 576, usp + 616)]%Z mm m2 -> wmono s0segs mm m2 -> mem_inv s0segs m2 ->
      evt s0segs Q (MS (mkR (Z_to_bv 64 0x15dcc) sp gp tp t0 t1 t2 (Z_to_bv 64 E) (Z_to_bv 64 nMTF) xa0' a1 a2 a3 (Z_to_bv 64 nG) a5 a6 a7
                            (Z_to_bv 64 (E + 37708 + 258 * 6)) (Z_to_bv 64 (-1)) (Z_to_bv 64 A) (Z_to_bv 64 (E + 672)) (Z_to_bv 64 A1) (Z_to_bv 64 (E + 128)) (Z_to_bv 64 A) xs9 xs10 xs11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x15e50) fc None m2 (seg_rom s0segs)))
    end.
    2:{ (* [comment removed for export] *)
        wstep; if_cases K1; zify_cond_z K1.
        - (* [comment removed for export] *)
          wstep. wstep; if_cases K2; zify_cond_z K2.
          + (* [comment removed for export] *)
            wstep. wstep; if_cases K3; zify_cond_z K3.
            * (* [comment removed for export] *)
              pose proof (sm_nGroups_ge1200 (e_nMTF e) ltac:(lia)) as HG. change (sm_nGroups (e_nMTF e)) with nG in HG.
              destruct (Z.ltb_spec (e_nMTF e / 32) 75) as [D|D];
                (wstep; (wstep; flags); wstep; (wstep; lit_store); wstep).
              -- replace (e_nMTF e <? 2400)%Z with true in HG by (symmetry; apply Z.ltb_lt; Z.div_mod_to_equations; lia).
                 enter_with (K988 _ 0%Z _); [st_eq| unfold flag6; rewrite HG; reflexivity| exact SC| exact MUk| exact WMk| assumption].
              -- replace (e_nMTF e <? 2400)%Z with false in HG by (symmetry; apply Z.ltb_ge; Z.div_mod_to_equations; lia).
                 enter_with (K988 _ 1%Z _); [st_eq| unfold flag6; rewrite HG; reflexivity| exact SC| exact MUk| exact WMk| assumption].
            * (* [comment removed for export] *)
              pose proof (sm_nGroups_lt1200 (e_nMTF e) ltac:(lia)) as HG. change (sm_nGroups (e_nMTF e)) with nG in HG.
              (wstep; lit_store). wstep. wstep.
              enter_with (K988 _ 0%Z _); [st_eq| unfold flag6; rewrite HG; reflexivity| exact SC| exact MUk| exact WMk| assumption].
          + pose proof (sm_nGroups_lt600 (e_nMTF e) ltac:(lia)) as HG. change (sm_nGroups (e_nMTF e)) with nG in HG.
            (wstep; lit_store). wstep. wstep.
            enter_with (K988 _ 0%Z _); [st_eq| unfold flag6; rewrite HG; reflexivity| exact SC| exact MUk| exact WMk| assumption].
        - pose proof (sm_nGroups_lt200 (e_nMTF e) ltac:(lia)) as HG. change (sm_nGroups (e_nMTF e)) with nG in HG.
          (wstep; lit_store). wstep. wstep.
          enter_with (K988 _ 0%Z _); [st_eq| unfold flag6; rewrite HG; reflexivity| exact SC| exact MUk| exact WMk| assumption]. }
    (* [comment removed for export] *)
    intros m2 fl xa0' Hfl SC2 MU2 WM2 MI2. clear SC MI. subst fl.
    lazymatch type of MU2 with munch _ ?mm _ => transport_after_call s0segs mm m2 MU2 WM2 end. clear MU2 WM2 MUk WMk.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. (wstep; lit_store).
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. (wstep; lit_store).
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. (wstep; lit_store). wstep. (wstep; lit_store).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (K mm); [st_eq| exact EH2| exact SA| | exact GOTc| exact SVc| assumption| exact MU0| exact WM0] end.
    lazymatch type of SC2 with rw_cells _ _ _ ?L => lazymatch goal with |- rw_cells _ _ _ ?L2 => replace L2 with L; [exact SC2| CmpFast.rlf] end end.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_smA_setup2 : forall (m : word -> option byte)
      (w24 w48 w56 w64 w72 w80 w88 w104 w112 w120 w136 w152 w160 w176 : word) (w576 w584 : word)
      (ra t0 a1 a2 a3 a4 s1 s4 s6 s8 s9 t3 t4 t5 t6 : word),
    rw_cells s0segs m (usp + 8) (SLOTS22 (Z_to_bv 64 37450) (Z_to_bv 64 (E + 128)) w24 (Z_to_bv 64 A) sv w48 w56 w64 w72 w80 w88 (Z_to_bv 64 nG) w104 w112 w120 (Z_to_bv 64 (E + 37708)) w136 (Z_to_bv 64 A1) w152 w160 (Z_to_bv 64 A) w176) ->
    rw_cells s0segs m (usp + 576) [C8 w576; C8 w584; C8 (Z_to_bv 64 (flag6 nG)); C8 (Z_to_bv 64 OFS); C8 (Z_to_bv 64 nInUse)] ->
    mem_inv s0segs m -> (CEIL <= usp)%Z -> (usp + 1008 <= 18446744073709551616)%Z ->
    (forall m' (t0 t1 t2 s1' a0 a1 a2 a3 a4 a5 a6 a7 : word),
      rw_cells s0segs m' (usp + 8) (smA_slots3 cx e usp sv w24 w56) ->
      rw_cells s0segs m' (usp + 576) [C8 (Z_to_bv 64 999999999); C8 w584; C8 (Z_to_bv 64 (flag6 nG)); C8 (Z_to_bv 64 (E + 1704)); C8 (Z_to_bv 64 nInUse)] ->
      mem_inv s0segs m' -> munch [(usp + 8, usp + 184); (usp + 576, usp + 616)]%Z m m' -> wmono s0segs m m' ->
      evt s0segs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 E) s1' a0 a1 a2 a3 a4 a5 a6 a7
                            (Z_to_bv 64 (E + 45448)) (Z_to_bv 64 A1) s4 (Z_to_bv 64 (usp + 616)) s6 (Z_to_bv 64 (usp + 616 + 4 * nG))
                            (Z_to_bv 64 (usp + 888 + 2 * nG)) (Z_to_bv 64 A) (Z_to_bv 64 (-1)) (Z_to_bv 64 1032) t3 t4 t5 t6)
                       F (Z_to_bv 64 0x160e8) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RI ra t0 (Z_to_bv 64 0) a1 a2 a3 a4 s1 (Z_to_bv 64 nG) s4 s6 (Z_to_bv 64 1) s8 s9 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x16010) fc None m (seg_rom s0segs)).
  Proof.
    intros m w24 w48 w56 w64 w72 w80 w88 w104 w112 w120 w136 w152 w160 w176 w576 w584 ra t0 a1 a2 a3 a4 s1 s4 s6 s8 s9 t3 t4 t5 t6 SA SC MI CE SPB K.
    openCX. try lin16 ME. try lin16 MA1. try lin16 MA2. try lin16 MF. try lin16 Mb. try lin16 Mf. clear AEA1 AEA2 AEF AA12 A1F. openSF. bz_ceil; bz_params; unfold CEIL in CE. assert (HA : A = (nInUse + 2)%Z) by reflexivity. assert (HM : nMTF = e_nMTF e) by reflexivity.
    pose proof (sm_nGroups_range (e_nMTF e)) as NGR. change (sm_nGroups (e_nMTF e)) with nG in NGR.
    pose proof (munch_refl [(usp + 8, usp + 184); (usp + 576, usp + 616)]%Z m) as MU0. pose proof (wmono_refl s0segs m) as WM0.
    (* [comment removed for export] *)
    (wstep; lit_store). wstep. (wstep; flags). wstep. wstep. wstep. (wstep; lit_store). wstep. (wstep; lit_store).
    (* [comment removed for export] *)
    wstep. wstep. wstep. (wstep; lit_store). wstep. wstep. (wstep; lit_store). wstep. wstep. wstep.
    (* [comment removed for export] *)
    wstep. wstep. wstep. (wstep; lit_store). wstep. wstep. wstep. wstep. wstep.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. (wstep; lit_store).
    (* [comment removed for export] *)
    wstep. (wstep; lit_store). wstep. wstep. wstep. wstep. (wstep; lit_store). wstep. (wstep; lit_store). wstep. (wstep; lit_store).
    (* [comment removed for export] *)
    wstep. wstep. (wstep; lit_store). (wstep; lit_store). (wstep; lit_store).
    replace (Z.land 18446744073709551615 (flag6 nG mod 18446744073709551616)) with (flag6 nG) in SA
      by (unfold flag6; destruct (nG =? 6)%Z; reflexivity).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (K mm); [st_eq| | exact SC| assumption| exact MU0| exact WM0] end.
    lazymatch type of SA with rw_cells _ _ _ ?L => replace (smA_slots3 cx e usp sv w24 w56) with L;
      [exact SA| unfold smA_slots3; cbv zeta; CmpFast.rlf ] end.
  Qed.
  Notation smLENROWS := (S0_smA_lenrows cx e Q sp gp tp F fc xs9 xs10 xs11 CX SEP SF).
  Notation smILOOP := (S0_smA_iloop cx g e Q sp gp tp F fc CX SEP SF).

  (* [comment removed for export] *)
  Lemma S0_smA_body : forall (m : word -> option byte)
      (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w136 w144 w152 w160 w168 w176 : word)
      (w576 w584 w592 w600 w608 : word)
      (ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s8 t3 t4 t5 t6 : word),
    emem cx s0segs g e m -> amem cx s0segs e m -> cimg_mem S0C m sv ->
    rw_cells s0segs m (usp + 8)
      [C8 w8; C8 w16; C8 w24; C8 w32; C8 w40; C8 w48; C8 w56; C8 w64; C8 w72; C8 w80; C8 w88; C8 w96; C8 w104; C8 w112; C8 w120;
       C8 (Z_to_bv 64 (E + 37708)); C8 w136; C8 w144; C8 w152; C8 w160; C8 w168; C8 w176] ->
    rw_cells s0segs m (usp + 576) [C8 w576; C8 w584; C8 w592; C8 w600; C8 w608] ->
    mem_inv s0segs m -> (CEIL <= usp)%Z -> (usp + 1008 <= 18446744073709551616)%Z ->
    (forall m' (ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 t3 t4 t5 t6 : word),
       emem cx s0segs g (est_A e) m' -> amem cx s0segs (est_A e) m' -> cimg_mem S0C m' sv ->
       rw_cells s0segs m' (usp + 8) (smA_slots3 cx e usp sv w24 w56) ->
       rw_cells s0segs m' (usp + 576) [C8 (Z_to_bv 64 999999999); C8 w584; C8 (Z_to_bv 64 (flag6 nG)); C8 (Z_to_bv 64 (E + 1704)); C8 (Z_to_bv 64 (e_nInUse e))] ->
       mem_inv s0segs m' -> munch (smA_W3 cx usp) m m' -> wmono s0segs m m' ->
       evt s0segs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 E) s1 a0 a1 a2 a3 a4 a5 a6 a7
                              (Z_to_bv 64 (E + 45448)) (Z_to_bv 64 A1) s4 (Z_to_bv 64 (usp + 616)) s6 (Z_to_bv 64 (usp + 616 + 4 * nG))
                              (Z_to_bv 64 (usp + 888 + 2 * nG)) (Z_to_bv 64 A) (Z_to_bv 64 (-1)) (Z_to_bv 64 1032) t3 t4 t5 t6)
                         F (Z_to_bv 64 0x160e8) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 E) s1 a0 a1 a2 a3 a4 a5 a6 a7
                           s2 s3 s4 (Z_to_bv 64 (E + 672)) (Z_to_bv 64 A1) (Z_to_bv 64 (E + 128)) s8 xs9 xs10 xs11 t3 t4 t5 t6)
                      F (Z_to_bv 64 0x15d90) fc None m (seg_rom s0segs)).
  Proof.
    intros m w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w136 w144 w152 w160 w168 w176 w576 w584 w592 w600 w608
           ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s8 t3 t4 t5 t6 EM AM CM SA SC MI CE SPB K.
    openCX. try lin16 ME. try lin16 MA1. try lin16 MA2. try lin16 MF. try lin16 Mb. try lin16 Mf. openSF. bz_ceil; bz_params; unfold CEIL in CE. assert (HA : A = (nInUse + 2)%Z) by reflexivity. assert (HM : nMTF = e_nMTF e) by reflexivity.
    pose proof (sm_nGroups_range (e_nMTF e)) as NGR. change (sm_nGroups (e_nMTF e)) with nG in NGR.
    cps_destruct EM as (EH1 & INU & UNS & EH2 & MTF & SEL & SELM & LEN & CODE & RFQ & LPK).
    cps_destruct AM as (AR1 & AR2 & FTB). cps_destruct CM as (GOTc & GOTcrc & SVc & CRC). cbn [ci_segs ci_got ci_stderrp ci_crc ci_crcx S0C] in GOTc, GOTcrc, SVc, CRC.
    pose proof IMG as IMG'. unfold cctx_img, img_apart, IMG_LO3 in IMG'. cbn [ci_hi S0C] in IMG'. cps_destruct IMG' as (IE & IA1 & IA2 & IFT & _).
    unfold ESTATE_SIZE, FTAB_WORDS in *.
    pose proof (jseg_length J 128 256 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ1.
    pose proof (jseg_length J 384 256 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ2.
    pose proof (jseg_length J 672 1032 ltac:(lia) ltac:(lia) ltac:(lia)) as LJm.
    pose proof (jseg_length J 1704 18002 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ4.
    pose proof (jseg_length J 19706 18002 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ5.
    pose proof (jseg_length J 37708 1548 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ6.
    pose proof (jseg_length J 39256 6192 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ7.
    pose proof (jseg_length J 45448 6192 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ8.
    pose proof (jseg_length J 51640 4128 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ9.
    pose proof (munch_refl (smA_W3 cx usp) m) as MU0. unfold smA_W3 in MU0.
    pose proof (wmono_refl s0segs m) as WM0.
    unfold EHEAD1 in EH1. unfold EHEAD2 in EH2. rewrite GM in EH1, EH2.
    (* [comment removed for export] *)
    wstep. try rewrite (sx32_of_Z nInUse) by lia. wstep. wstep. try rewrite (sx32_of_Z (nInUse + 2)) by lia. wstep.
    wstep; if_cases Kp; zify_cond_z Kp; [| exfalso; lia].
    (* [comment removed for export] *)
    wstep. wstep. wstep.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (smLENROWS 6%nat 0 (e_len e) mm mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ w576 w584 w592 w600);
      [st_eq| lia| lia| lia| exact LEN| exact SC| exact MI| bz_ceil; bz_params; unfold CEIL; lia| exact SPB| apply munch_refl| apply wmono_refl|];
      clear LEN SC MI; intros m1 x0 x1 x2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 x3 x4 x5 x6 LEN SC MI1 MU1 WM1;
      transport_after_call s0segs mm m1 MU1 WM1; clear MU1 WM1 end.
    change (sm_len_init 6 (e_len e) A 0) with (smA_len e) in LEN.
    (* [comment removed for export] *)
    enter_with (S0_smA_setup1 m1 _ _ w24 _ _ w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w136 _ w152 w160 _ w176 w576 w584 w592 w600);
      [st_eq| exact EH2| exact SA| exact SC| exact GOTc| exact SVc| exact MI1| bz_ceil; bz_params; unfold CEIL; lia| exact SPB|].
    clear EH2 SA SC GOTc SVc MI1. intros m2 EH2 SA SC GOTc SVc MI2 MU2 WM2.
    transport_after_call s0segs m1 m2 MU2 WM2. clear MU2 WM2.
    (* [comment removed for export] *)
    lazymatch type of SA with rw_cells _ ?mm _ [?c0; ?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8; ?c9; ?c10; ?c11; ?c12; ?c13; ?c14; ?c15; ?c16; ?c17; ?c18; ?c19; ?c20; ?c21] =>
      change (rw_cells s0segs mm (usp + 8) ([c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10] ++ ([c11] ++ [c12; c13; c14; c15; c16; c17; c18; c19; c20; c21]))) in SA end.
    apply (proj1 (rw_cells_app_iff _ _ _ _ _)) in SA. destruct SA as [SAa SA]. apply (proj1 (rw_cells_app_iff _ _ _ _ _)) in SA. destruct SA as [SA96 SAb].
    cbn [cells_size csize Nat.add] in SA96, SAb.
    replace (usp + 8 + Z.of_nat 88)%Z with (usp + 96)%Z in SA96 by lia. replace (usp + 8 + Z.of_nat 88 + Z.of_nat 8)%Z with (usp + 104)%Z in SAb by lia.
    pose proof (smILOOP (Z.to_nat nG) 0%nat m2 m2) as LOOP.
    cbv zeta in LOOP. change (sip_k e 0) with (sip0 e) in LOOP. cbn [ip_nPart ip_remF ip_gs ip_len sip0] in LOOP.
    replace (0 + Z.to_nat nG)%nat with (Z.to_nat nG) in LOOP by lia. rewrite <- IPT in LOOP. change (sm_init_tables 8 mf nG A (sip0 e)) with (smA_ip e) in LOOP.
    enter_with LOOP;
      [st_eq| lia| lia| lia| exact LEN| exact MTF| unfold EHEAD2; rewrite GM; exact EH2| exact SA96| exact SC| exact MI2| bz_ceil; bz_params; unfold CEIL; lia| exact SPB| apply munch_refl| apply wmono_refl|].
    clear LOOP. intros m3 ya1 ya2 ya3 ya4 ys8 ys9 LEN3 MTF3 EH2' SA96' SC3 MI3 MU3 WM3.
    clear LEN MTF EH2 SA96 SC MI2. transport_after_call s0segs m2 m3 MU3 WM3. clear MU3 WM3.
    unfold EHEAD2 in EH2'. rewrite GM in EH2'.
    assert (SA : rw_cells s0segs m3 (usp + 8)
      (SLOTS22 (Z_to_bv 64 37450) (Z_to_bv 64 (E + 128)) w24 (Z_to_bv 64 A) sv w48 w56 w64 w72 w80 w88 (Z_to_bv 64 nG) w104 w112 w120 (Z_to_bv 64 (E + 37708)) w136 (Z_to_bv 64 A1) w152 w160 (Z_to_bv 64 A) w176)).
    { change (rw_cells s0segs m3 (usp + 8) ([C8 (Z_to_bv 64 37450); C8 (Z_to_bv 64 (E + 128)); C8 w24; C8 (Z_to_bv 64 A); C8 sv; C8 w48; C8 w56; C8 w64; C8 w72; C8 w80; C8 w88] ++
              ([C8 (Z_to_bv 64 nG)] ++ [C8 w104; C8 w112; C8 w120; C8 (Z_to_bv 64 (E + 37708)); C8 w136; C8 (Z_to_bv 64 A1); C8 w152; C8 w160; C8 (Z_to_bv 64 A); C8 w176]))).
      apply (proj2 (rw_cells_app_iff _ _ _ _ _)). split; [exact SAa|]. cbn [cells_size csize Nat.add].
      apply (proj2 (rw_cells_app_iff _ _ _ _ _)). split; [replace (usp + 8 + Z.of_nat 88)%Z with (usp + 96)%Z by lia; exact SA96'|].
      cbn [cells_size csize Nat.add]. replace (usp + 8 + Z.of_nat 88 + Z.of_nat 8)%Z with (usp + 104)%Z by lia. exact SAb. }
    clear SAa SA96' SAb.
    (* [comment removed for export] *)
    enter_with (S0_smA_setup2 m3 w24 w48 w56 w64 w72 w80 w88 w104 w112 w120 w136 w152 w160 w176 _ w584);
      [st_eq| exact SA| exact SC3| exact MI3| bz_ceil; bz_params; unfold CEIL; lia| exact SPB|].
    clear SA SC3 MI3. intros m4 z0 z1 z2 zs1 za0 za1 za2 za3 za4 za5 za6 za7 SA SC MI4 MU4 WM4.
    transport_after_call s0segs m3 m4 MU4 WM4. clear MU4 WM4.
    (* [comment removed for export] *)
    unfold emem, amem, cimg_mem, est_A, EHEAD1, EHEAD2 in K.
    cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos e_nInUse
         e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf e_len e_code e_rfreq e_len_pack
         ci_segs ci_got ci_stderrp ci_crc ci_crcx S0C] in K.
    rewrite GM in K. unfold FTAB_WORDS in K.
    enter_with (K m4);
      [ st_eq
      | split; [exact EH1|]; split; [exact INU|]; split; [exact UNS|]; split; [exact EH2'|]; split; [exact MTF3|];
        split; [exact SEL|]; split; [exact SELM|]; split; [exact LEN3|]; split; [exact CODE|]; split; [exact RFQ| exact LPK]
      | split; [exact AR1|]; split; [exact AR2| exact FTB]
      | split; [exact GOTc|]; split; [exact GOTcrc|]; split; [exact SVc| exact CRC]
      | exact SA
      | exact SC
      | assumption
      | exact MU0
      | exact WM0 ].
  Qed.
End S0SMZ.

Theorem S0_smA : S0_smA_spec smA_facts.
Proof.
  unfold S0_smA_spec. intros until fc. cbv zeta. intros GM EM AM CM SA SC MI CX SEP IMG CE SPB SF K.
  eapply S0_smA_body; eassumption.
Qed.

End ACeilS1.
