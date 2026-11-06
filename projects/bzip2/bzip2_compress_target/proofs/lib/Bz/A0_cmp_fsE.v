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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCSortF BzArrD CmpMem CmpCut BzCLemmasFs BzCFactsFs CmpFsKit0 AsanKit AsanCut.
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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsV.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Section A0FS.
  Variable X : fsenv. Variable Y : afenv. Variable Q : machine_state -> Prop. Variables l1 r1 lq nnd rr Hh : Z.
  Variables (v200 v208 w5 w10 w11 w16 w17 : word).
  Hypothesis XOK : fsenv_ok X. Hypothesis XSEP : fsenv_sep X. Hypothesis YOK : afenv_ok X Y.
  Notation usp := (bv_unsigned (fe_sp X)). Notation P := (ae_P Y).
  Notation A1 := (fe_A1 X). Notation A2 := (fe_A2 X). Notation FT := (fe_FT X). Notation nb := (fe_nb X).
  Notation gp := (fe_gp X). Notation tp := (fe_tp X). Notation F := (fe_F X). Notation fc := (fe_fc X).
  Notation cSB := (Z_to_bv 64 2147450880).
  Notation WP := [(A1, A1 + ARR1_SIZE); (P + 144, P + 184)]%Z.
  (* [comment removed for export] *)
  Notation QP ra t1 t2 a2 a3 a4 lo hi s10 t3 t4 med t6 :=
    (mkR ra (Z_to_bv 64 P) gp tp w5 t1 t2 (fe_sp X) (Z_to_bv 64 P) w10 w11 a2 a3 a4 (Z_to_bv 64 lo) w16 w17
         (Z_to_bv 64 1) (Z_to_bv 64 l1) (Z_to_bv 64 A2) (Z_to_bv 64 A1) cSB (Z_to_bv 64 hi) (Z_to_bv 64 FT) (Z_to_bv 64 (-1)) s10 (Z_to_bv 64 r1) t3 t4 (Z_to_bv 64 med) t6).
  Notation SC v144 v160 v176 := (SCq X Y lq nnd v144 rr v160 Hh v176 v200 v208).

  Ltac prep XOK XSEP fm ec :=
    fsenv_open XOK; afenv_open YOK;
    let SP := fresh "SP" in pose proof XSEP as SP; unfold fsenv_sep, apartv in SP; cps_destruct SP as (?AP12 & _ & _);
    let L1 := fresh "L1" in let L2 := fresh "L2" in
    pose proof (zb8_length fm ARR1_SIZE ltac:(lia)) as L1; pose proof (zb8_length ec ARR2_SIZE ltac:(lia)) as L2.
  Ltac rd_fm fm j AR1 FMOK :=
    let RD := fresh "RD" in
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (zb8_read4 a0segs mm A1 fm ARR1_SIZE j _ AR1 ltac:(lia) ltac:(lia) FMOK ltac:(unfold wa; f_equal; lia)) as RD end;
    wstep; clear RD.
  Ltac rd_ec ec x AR2 ECOK :=
    let RD := fresh "RD" in
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (zb8_read4 a0segs mm A2 ec ARR2_SIZE x _ AR2 ltac:(lia) ltac:(lia) ECOK ltac:(unfold wa; f_equal; lia)) as RD end;
    wstep; clear RD.
  Ltac st_fm fm i AR1 :=
    let SO := fresh "SO" in
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u8arr_storeN_ok a0segs mm A1 _ (4 * i) 4 _ AR1 ltac:(lia) ltac:(rewrite zb8_length_nat; lia) eq_refl) as SO end;
    wstep; zb8_store4 AR1 i; try clear SO.

  (* [comment removed for export] *)
  Lemma A0_plo : forall (f : nat) (u unHi ltLo gtHi med hi lo : Z) (fm ec : zarr) (me m : word -> option byte) (a3 a4 t3 t4 v160 : word),
    (0 <= lo)%Z -> (hi < nb)%Z -> (lo <= ltLo <= u)%Z -> (u <= unHi)%Z -> (unHi <= gtHi <= hi)%Z -> (unHi - u + 2 <= Z.of_nat f)%Z ->
    (0 <= med < nb)%Z -> fm_range fm nb -> ec_range ec nb -> zbok fm -> zbok ec ->
    u8arr a0segs m A1 (zb8 fm ARR1_SIZE) -> u8arr a0segs m A2 (zb8 ec ARR2_SIZE) ->
    rw_cells a0segs m (P + 80) (SC (Z_to_bv 64 gtHi) v160 (Z_to_bv 64 unHi)) -> mem_inv a0segs m ->
    munch WP me m -> wmono a0segs me m ->
    shzW a0segs WP me A1 (A1 + ARR1_SIZE) -> shzW a0segs WP me A2 (A2 + ARR2_SIZE) ->
    (* [comment removed for export] *)
    (forall m' (x1 x6 x12 x13 x14 x28 x29 x31 : word), let p' := fpart_lo f ec med (FP fm u unHi ltLo gtHi) in
      u8arr a0segs m' A1 (zb8 (fp_fm p') ARR1_SIZE) -> u8arr a0segs m' A2 (zb8 ec ARR2_SIZE) ->
      rw_cells a0segs m' (P + 80) (SC (Z_to_bv 64 gtHi) v160 (Z_to_bv 64 unHi)) -> mem_inv a0segs m' ->
      munch WP me m' -> wmono a0segs me m' -> fm_range (fp_fm p') nb -> zbok (fp_fm p') ->
      fp_unHi p' = unHi -> fp_gtHi p' = gtHi -> (ltLo <= fp_ltLo p' <= fp_unLo p')%Z -> (u <= fp_unLo p' <= unHi + 1)%Z ->
      evt a0segs Q (MS (QP x1 x6 (Z_to_bv 64 (fp_unLo p')) x12 x13 x14 lo hi (Z_to_bv 64 (fp_ltLo p')) x28 x29 med x31)
                       F (Z_to_bv 64 0x9b9dc) fc None m' (seg_rom a0segs))) ->
    (* [comment removed for export] *)
    (forall m' (x6 x12 x13 x28 x29 x31 : word), let p' := fpart_lo f ec med (FP fm u unHi ltLo gtHi) in
      u8arr a0segs m' A1 (zb8 (fp_fm p') ARR1_SIZE) -> u8arr a0segs m' A2 (zb8 ec ARR2_SIZE) ->
      rw_cells a0segs m' (P + 80) (SC (Z_to_bv 64 gtHi) v160 (Z_to_bv 64 unHi)) -> mem_inv a0segs m' ->
      munch WP me m' -> wmono a0segs me m' -> fm_range (fp_fm p') nb -> zbok (fp_fm p') ->
      fp_unHi p' = unHi -> fp_gtHi p' = gtHi -> (ltLo <= fp_ltLo p' <= fp_unLo p')%Z -> (fp_unLo p' = unHi + 1)%Z ->
      evt a0segs Q (MS (QP (Z_to_bv 64 (fp_ltLo p')) x6 (Z_to_bv 64 (fp_unLo p')) x12 x13 (Z_to_bv 64 unHi) lo hi (Z_to_bv 64 gtHi) x28 x29 med x31)
                       F (Z_to_bv 64 0x9bb58) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (QP (Z_to_bv 64 unHi) (Z_to_bv 64 (unHi - u + 1)) (Z_to_bv 64 u) (Z_to_bv 64 (A1 + 4 * u)) a3 a4 lo hi (Z_to_bv 64 ltLo) t3 t4 med (Z_to_bv 64 (A1 + 4 * u)))
                     F (Z_to_bv 64 0x9b900) fc None m (seg_rom a0segs)).
  Proof.
    induction f as [|f IH]; intros u unHi ltLo gtHi med hi lo fm ec me m a3 a4 t3 t4 v160 Hlo Hhi Hlt Hu Hg Hf Hmed FMR ECR FMOK' ECOK' AR1 AR2 SC MI MU WM SH1 SH2 K KB; cbv zeta in K, KB; [lia|].
    prep XOK XSEP fm ec. bz_params. unfold SCq in SC, K, KB.
    rewrite fpart_lo_S in K, KB. cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi] in K, KB.
    replace (unHi <? u)%Z with false in K, KB by (symmetry; apply Z.ltb_ge; lia).
    pose proof (proj2 FMR u ltac:(lia)) as Fu. pose proof (ECR (rd32 fm u) ltac:(lia)) as Eu. pose proof (proj2 FMR ltLo ltac:(lia)) as Fl.
    (* [comment removed for export] *)
    arun. rd_fm fm u AR1 FMOK'. try rewrite (zx32_of_Z (rd32 fm u)) by lia.
    (* [comment removed for export] *)
    arun. rd_ec ec (rd32 fm u) AR2 ECOK'. try rewrite (sx32_of_Z (rd32 ec (rd32 fm u))) by lia.
    (* [comment removed for export] *)
    wstep; if_cases K0; zify_cond_z K0.
    - (* [comment removed for export] *)
      replace (rd32 ec (rd32 fm u) - med =? 0)%Z with true in K, KB by (symmetry; apply Z.eqb_eq; lia). cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi] in K, KB.
      (* [comment removed for export] *)
      arun. rd_fm fm ltLo AR1 FMOK'. try rewrite (sx32_of_Z (rd32 fm ltLo)) by lia.
      (* [comment removed for export] *)
      arun. st_fm fm u AR1. rewrite (unsigned_lit (rd32 fm ltLo)) in AR1 by lia.
      (* [comment removed for export] *)
      pose proof (zb8_length (wr32 fm u (rd32 fm ltLo)) ARR1_SIZE ltac:(lia)) as L1'.
      st_fm (wr32 fm u (rd32 fm ltLo)) ltLo AR1. rewrite (unsigned_lit (rd32 fm u)) in AR1 by lia.
      change (wr32 (wr32 fm u (rd32 fm ltLo)) ltLo (rd32 fm u)) with (fswap fm u ltLo) in AR1.
      assert (FMR1 : fm_range (fswap fm u ltLo) nb) by (apply fswap_range; [exact FMR| lia| lia]).
      (* [comment removed for export] *)
      arun. if_cases Kc; zify_cond_z Kc.
      + (* [comment removed for export] *)
        arun. if_cases Kd; zify_cond_z Kd; [exfalso; lia|]. arun_to 0x9b900%Z.
        enter_with (IH (u + 1)%Z unHi (ltLo + 1)%Z gtHi med hi lo (fswap fm u ltLo) ec me);
          [st_eq| lia| lia| lia| lia| lia| lia| lia| exact FMR1| exact ECR| unfold fswap; apply zbok_wr32, zbok_wr32; exact FMOK'| exact ECOK'| exact AR1| exact AR2| exact SC| exact MI| exact MU| exact WM| exact SH1| exact SH2| |].
        * intros m' x1 x6 x12 x13 x14 x28 x29 x31. cbv zeta. intros AR1' AR2' SC' MI' MU' WM' FMR' FMOK'' E1 E2 R1 R2.
          eapply (K m' x1 x6 x12 x13 x14 x28 x29 x31); [exact AR1'| exact AR2'| exact SC'| exact MI'| exact MU'| exact WM'| exact FMR'| exact FMOK''| exact E1| exact E2| lia| lia].
        * intros m' x6 x12 x13 x28 x29 x31. cbv zeta. intros AR1' AR2' SC' MI' MU' WM' FMR' FMOK'' E1 E2 R1 R2.
          eapply (KB m' x6 x12 x13 x28 x29 x31); [exact AR1'| exact AR2'| exact SC'| exact MI'| exact MU'| exact WM'| exact FMR'| exact FMOK''| exact E1| exact E2| lia| lia].
      + (* [comment removed for export] *)
        arun. if_cases Kd; zify_cond_z Kd; [| exfalso; lia].
        rewrite fpart_lo_stop in KB by (cbn; lia). cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi] in KB.
        enter_with (KB _ _ _ _ _ _ _); [st_eq| exact AR1| exact AR2| exact SC| exact MI| exact MU| exact WM| exact FMR1| unfold fswap; apply zbok_wr32, zbok_wr32; exact FMOK'| reflexivity| reflexivity| lia| lia].
    - replace (rd32 ec (rd32 fm u) - med =? 0)%Z with false in K, KB by (symmetry; apply Z.eqb_neq; lia).
      (* [comment removed for export] *)
      wstep; if_cases Kp; zify_cond_z Kp.
      + (* [comment removed for export] *)
        replace (0 <? rd32 ec (rd32 fm u) - med)%Z with true in K by (symmetry; apply Z.ltb_lt; lia). cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi] in K.
        enter_with (K m _ _ _ _ _ _ _ _); [st_eq| exact AR1| exact AR2| exact SC| exact MI| exact MU| exact WM| exact FMR| exact FMOK'| reflexivity| reflexivity| lia| lia].
      + (* [comment removed for export] *)
        replace (0 <? rd32 ec (rd32 fm u) - med)%Z with false in K, KB by (symmetry; apply Z.ltb_ge; lia). cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi] in K, KB.
        (* [comment removed for export] *)
        arun. if_cases Kc; zify_cond_z Kc.
        * enter_with (IH (u + 1)%Z unHi ltLo gtHi med hi lo fm ec me);
            [st_eq| lia| lia| lia| lia| lia| lia| lia| exact FMR| exact ECR| exact FMOK'| exact ECOK'| exact AR1| exact AR2| exact SC| exact MI| exact MU| exact WM| exact SH1| exact SH2| |].
          -- intros m' x1 x6 x12 x13 x14 x28 x29 x31. cbv zeta. intros AR1' AR2' SC' MI' MU' WM' FMR' FMOK'' E1 E2 R1 R2.
             eapply (K m' x1 x6 x12 x13 x14 x28 x29 x31); [exact AR1'| exact AR2'| exact SC'| exact MI'| exact MU'| exact WM'| exact FMR'| exact FMOK''| exact E1| exact E2| lia| lia].
          -- intros m' x6 x12 x13 x28 x29 x31. cbv zeta. intros AR1' AR2' SC' MI' MU' WM' FMR' FMOK'' E1 E2 R1 R2.
             eapply (KB m' x6 x12 x13 x28 x29 x31); [exact AR1'| exact AR2'| exact SC'| exact MI'| exact MU'| exact WM'| exact FMR'| exact FMOK''| exact E1| exact E2| lia| lia].
        * (* [comment removed for export] *)
          wstep. wstep.
          rewrite fpart_lo_stop in K by (cbn; lia). cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi] in K.
          enter_with (K m _ _ _ _ _ _ _ _); [st_eq| exact AR1| exact AR2| exact SC| exact MI| exact MU| exact WM| exact FMR| exact FMOK'| reflexivity| reflexivity| lia| lia].
  Qed.

  (* [comment removed for export] *)
  Definition KBbrk (hi lo med : Z) (ec : zarr) (me : word -> option byte) (pf : fpart) : Prop :=
    forall m' (x6 x12 x13 x28 x29 x31 v144 v160 v176 : word),
      u8arr a0segs m' A1 (zb8 (fp_fm pf) ARR1_SIZE) -> u8arr a0segs m' A2 (zb8 ec ARR2_SIZE) ->
      rw_cells a0segs m' (P + 80) (SC v144 v160 v176) -> mem_inv a0segs m' ->
      munch WP me m' -> wmono a0segs me m' -> fm_range (fp_fm pf) nb -> zbok (fp_fm pf) ->
      fp_ok lo hi pf -> (fp_unHi pf < fp_unLo pf)%Z ->
      evt a0segs Q (MS (QP (Z_to_bv 64 (fp_ltLo pf)) x6 (Z_to_bv 64 (fp_unLo pf)) x12 x13 (Z_to_bv 64 (fp_unHi pf)) lo hi (Z_to_bv 64 (fp_gtHi pf)) x28 x29 med x31)
                       F (Z_to_bv 64 0x9bb58) fc None m' (seg_rom a0segs)).
  (* [comment removed for export] *)
  Definition KCcont (hi lo med : Z) (ec : zarr) (me : word -> option byte) (sz f' : nat) (pf : fpart) : Prop :=
    forall (p3 : fpart) m' (x6 x7 x12 x28 x29 x31 v144 v160 v176 : word),
      (fp_unLo p3 <= fp_unHi p3)%Z -> fp_ok lo hi p3 -> (fp_unHi p3 - fp_unLo p3 + 2 <= 2 * Z.of_nat f')%Z ->
      fpart_loop f' sz ec med p3 = pf ->
      u8arr a0segs m' A1 (zb8 (fp_fm p3) ARR1_SIZE) -> u8arr a0segs m' A2 (zb8 ec ARR2_SIZE) ->
      rw_cells a0segs m' (P + 80) (SC v144 v160 v176) -> mem_inv a0segs m' ->
      munch WP me m' -> wmono a0segs me m' -> fm_range (fp_fm p3) nb -> zbok (fp_fm p3) ->
      evt a0segs Q (MS (QP (Z_to_bv 64 (fp_ltLo p3)) x6 x7 x12 (Z_to_bv 64 (fp_unLo p3)) (Z_to_bv 64 (fp_unHi p3)) lo hi (Z_to_bv 64 (fp_gtHi p3)) x28 x29 med x31)
                       F (Z_to_bv 64 0x9b8cc) fc None m' (seg_rom a0segs)).

  (* [comment removed for export] *)
  Lemma A0_phi : forall (f : nat) (uh w unLo ltLo g med hi lo : Z) (fm ec : zarr) (me m : word -> option byte) (t1 a3 a4 t3 v144 : word) (sz f' : nat) (pf : fpart),
    (0 <= lo)%Z -> (hi < nb)%Z -> (lo <= ltLo <= unLo)%Z -> (unLo <= uh)%Z -> (uh <= g <= hi)%Z -> (uh <= w <= hi)%Z -> (uh - unLo + 2 <= Z.of_nat f)%Z ->
    (hi - lo + 1 = Z.of_nat sz)%Z -> (uh - unLo <= 2 * Z.of_nat f')%Z ->
    (0 <= med < nb)%Z -> fm_range fm nb -> ec_range ec nb -> zbok fm -> zbok ec -> (med < rd32 ec (rd32 fm unLo))%Z ->
    (let p2 := fpart_hi f ec med (FP fm unLo uh ltLo g) in
     (if (fp_unHi p2 <? fp_unLo p2)%Z then p2
      else fpart_loop f' sz ec med (FP (fswap (fp_fm p2) (fp_unLo p2) (fp_unHi p2)) (fp_unLo p2 + 1) (fp_unHi p2 - 1) (fp_ltLo p2) (fp_gtHi p2))) = pf) ->
    u8arr a0segs m A1 (zb8 fm ARR1_SIZE) -> u8arr a0segs m A2 (zb8 ec ARR2_SIZE) ->
    rw_cells a0segs m (P + 80) (SC v144 (Z_to_bv 64 ltLo) (Z_to_bv 64 w)) -> mem_inv a0segs m ->
    munch WP me m -> wmono a0segs me m ->
    shzW a0segs WP me A1 (A1 + ARR1_SIZE) -> shzW a0segs WP me A2 (A2 + ARR2_SIZE) ->
    KBbrk hi lo med ec me pf -> KCcont hi lo med ec me sz f' pf ->
    evt a0segs Q (MS (QP (Z_to_bv 64 (A1 + 4 * uh)) t1 (Z_to_bv 64 unLo) (Z_to_bv 64 (A1 + 4 * uh)) a3 a4 lo hi (Z_to_bv 64 g) t3 (Z_to_bv 64 (uh + 1)) med (Z_to_bv 64 uh))
                     F (Z_to_bv 64 0x9ba0c) fc None m (seg_rom a0segs)).
  Proof.
    induction f as [|f IH]; intros uh w unLo ltLo g med hi lo fm ec me m t1 a3 a4 t3 v144 sz f' pf Hlo Hhi Hlt Hu Hg Hw Hf Hsz Hf' Hmed FMR ECR FMOK' ECOK' HNP RES AR1 AR2 SC MI MU WM SH1 SH2 KB KC; cbv zeta in RES; [lia|].
    prep XOK XSEP fm ec. bz_params. unfold KBbrk, KCcont in KB, KC. unfold SCq in SC, KB, KC. bz_params.
    rewrite fpart_hi_S in RES. cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi] in RES.
    replace (uh <? unLo)%Z with false in RES by (symmetry; apply Z.ltb_ge; lia).
    pose proof (proj2 FMR uh ltac:(lia)) as Fu. pose proof (ECR (rd32 fm uh) ltac:(lia)) as Eu.
    pose proof (proj2 FMR g ltac:(lia)) as Fg. pose proof (proj2 FMR unLo ltac:(lia)) as Fl.
    (* [comment removed for export] *)
    arun. rd_fm fm uh AR1 FMOK'. try rewrite (zx32_of_Z (rd32 fm uh)) by lia.
    (* [comment removed for export] *)
    arun. rd_ec ec (rd32 fm uh) AR2 ECOK'. try rewrite (sx32_of_Z (rd32 ec (rd32 fm uh))) by lia.
    (* [comment removed for export] *)
    wstep; if_cases K0; zify_cond_z K0.
    - (* [comment removed for export] *)
      replace (rd32 ec (rd32 fm uh) - med =? 0)%Z with true in RES by (symmetry; apply Z.eqb_eq; lia). cbv iota in RES.
      assert (Hne : uh <> unLo) by (intros E; rewrite E in K0; lia).
      assert (HNP1 : (med < rd32 ec (rd32 (fswap fm uh g) unLo))%Z) by (rewrite rd32_fswap_other by lia; exact HNP).
      (* [comment removed for export] *)
      arun. rd_fm fm g AR1 FMOK'. try rewrite (sx32_of_Z (rd32 fm g)) by lia.
      (* [comment removed for export] *)
      arun. st_fm fm uh AR1. rewrite (unsigned_lit (rd32 fm g)) in AR1 by lia.
      pose proof (zb8_length (wr32 fm uh (rd32 fm g)) ARR1_SIZE ltac:(lia)) as L1'.
      st_fm (wr32 fm uh (rd32 fm g)) g AR1. rewrite (unsigned_lit (rd32 fm uh)) in AR1 by lia.
      change (wr32 (wr32 fm uh (rd32 fm g)) g (rd32 fm uh)) with (fswap fm uh g) in AR1.
      assert (FMR1 : fm_range (fswap fm uh g) nb) by (apply fswap_range; [exact FMR| lia| lia]).
      assert (FMOK1 : zbok (fswap fm uh g)) by (unfold fswap; apply zbok_wr32, zbok_wr32; exact FMOK').
      (* [comment removed for export] *)
      arun. if_cases Kc; zify_cond_z Kc.
      + (* [comment removed for export] *)
        arun_to 0x9ba0c%Z.
        enter_with (IH (uh - 1)%Z (uh - 1)%Z unLo ltLo (g - 1)%Z med hi lo (fswap fm uh g) ec me _ _ _ _ _ _ sz f' pf);
          [st_eq| lia| lia| lia| lia| lia| lia| lia| lia| lia| lia| exact FMR1| exact ECR| exact FMOK1| exact ECOK'| exact HNP1| exact RES| exact AR1| exact AR2| exact SC| exact MI| exact MU| exact WM| exact SH1| exact SH2| exact KB| exact KC].
      + (* [comment removed for export] *)
        arun_to 0x9bb58%Z.
        rewrite fpart_hi_stop in RES by (cbn; lia). cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi] in RES.
        replace (uh - 1 <? unLo)%Z with true in RES by (symmetry; apply Z.ltb_lt; lia). subst pf.
        enter_with (KB _ _ _ _ _ _ _ _ _ _); [cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi]; st_eq| exact AR1| exact AR2| exact SC| exact MI| exact MU| exact WM| exact FMR1| exact FMOK1| unfold fp_ok; cbn; lia| cbn; lia].
    - replace (rd32 ec (rd32 fm uh) - med =? 0)%Z with false in RES by (symmetry; apply Z.eqb_neq; lia). cbv iota in RES.
      (* [comment removed for export] *)
      wstep; if_cases Kn; zify_cond_z Kn.
      + (* [comment removed for export] *)
        replace (rd32 ec (rd32 fm uh) - med <? 0)%Z with true in RES by (symmetry; apply Z.ltb_lt; lia). cbv iota in RES.
        cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi] in RES.
        assert (Hne : uh <> unLo) by (intros E; rewrite E in Kn; lia).
        replace (uh <? unLo)%Z with false in RES by (symmetry; apply Z.ltb_ge; lia).
        (* [comment removed for export] *)
        arun. rd_fm fm unLo AR1 FMOK'. try rewrite (sx32_of_Z (rd32 fm unLo)) by lia.
        (* [comment removed for export] *)
        st_fm fm unLo AR1. rewrite (unsigned_lit (rd32 fm uh)) in AR1 by lia.
        pose proof (zb8_length (wr32 fm unLo (rd32 fm uh)) ARR1_SIZE ltac:(lia)) as L1'.
        arun.
        st_fm (wr32 fm unLo (rd32 fm uh)) uh AR1. rewrite (unsigned_lit (rd32 fm unLo)) in AR1 by lia.
        change (wr32 (wr32 fm unLo (rd32 fm uh)) uh (rd32 fm unLo)) with (fswap fm unLo uh) in AR1.
        assert (FMR1 : fm_range (fswap fm unLo uh) nb) by (apply fswap_range; [exact FMR| lia| lia]).
        assert (FMOK1 : zbok (fswap fm unLo uh)) by (unfold fswap; apply zbok_wr32, zbok_wr32; exact FMOK').
        (* [comment removed for export] *)
        arun. if_cases Kc; zify_cond_z Kc.
        * enter_with (KC (FP (fswap fm unLo uh) (unLo + 1) (uh - 1) ltLo g) _ _ _ _ _ _ _ _ _ _);
            [cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi]; st_eq| cbn; lia| unfold fp_ok; cbn; lia| cbn; lia| exact RES| exact AR1| exact AR2| exact SC| exact MI| exact MU| exact WM| exact FMR1| exact FMOK1].
        * (* [comment removed for export] *)
          arun. if_cases Kd; zify_cond_z Kd; [| exfalso; lia].
          rewrite fpart_loop_stop in RES by (cbn; lia). subst pf.
          enter_with (KB _ _ _ _ _ _ _ _ _ _); [cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi]; st_eq| exact AR1| exact AR2| exact SC| exact MI| exact MU| exact WM| exact FMR1| exact FMOK1| unfold fp_ok; cbn; lia| cbn; lia].
      + (* [comment removed for export] *)
        replace (rd32 ec (rd32 fm uh) - med <? 0)%Z with false in RES by (symmetry; apply Z.ltb_ge; lia). cbv iota in RES.
        (* [comment removed for export] *)
        arun. if_cases Kc; zify_cond_z Kc.
        * enter_with (IH (uh - 1)%Z w unLo ltLo g med hi lo fm ec me m _ _ _ _ _ sz f' pf);
            [st_eq| lia| lia| lia| lia| lia| lia| lia| lia| lia| lia| exact FMR| exact ECR| exact FMOK'| exact ECOK'| exact HNP| exact RES| exact AR1| exact AR2| exact SC| exact MI| exact MU| exact WM| exact SH1| exact SH2| exact KB| exact KC].
        * (* [comment removed for export] *)
          arun. if_cases Kd; zify_cond_z Kd; [exfalso; lia|]. arun_to 0x9bb58%Z.
          rewrite fpart_hi_stop in RES by (cbn; lia). cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi] in RES.
          replace (uh - 1 <? unLo)%Z with true in RES by (symmetry; apply Z.ltb_lt; lia). subst pf.
          enter_with (KB _ _ _ _ _ _ _ _ _ _); [cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi]; st_eq| exact AR1| exact AR2| exact SC| exact MI| exact MU| exact WM| exact FMR| exact FMOK'| unfold fp_ok; cbn; lia| cbn; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma A0_ploop : forall (f' : nat) (pp : fpart) (med hi lo : Z) (ec : zarr) (me m : word -> option byte) (t1 t2 a2 t3 t4 t6 v144 v160 v176 : word) (sz : nat) (pf : fpart),
    (0 <= lo)%Z -> (hi < nb)%Z -> (fp_unLo pp <= fp_unHi pp)%Z -> fp_ok lo hi pp -> (hi - lo + 1 = Z.of_nat sz)%Z ->
    (fp_unHi pp - fp_unLo pp + 2 <= 2 * Z.of_nat f')%Z -> fpart_loop f' sz ec med pp = pf ->
    (0 <= med < nb)%Z -> fm_range (fp_fm pp) nb -> ec_range ec nb -> zbok (fp_fm pp) -> zbok ec ->
    u8arr a0segs m A1 (zb8 (fp_fm pp) ARR1_SIZE) -> u8arr a0segs m A2 (zb8 ec ARR2_SIZE) ->
    rw_cells a0segs m (P + 80) (SC v144 v160 v176) -> mem_inv a0segs m ->
    munch WP me m -> wmono a0segs me m ->
    shzW a0segs WP me A1 (A1 + ARR1_SIZE) -> shzW a0segs WP me A2 (A2 + ARR2_SIZE) ->
    KBbrk hi lo med ec me pf ->
    evt a0segs Q (MS (QP (Z_to_bv 64 (fp_ltLo pp)) t1 t2 a2 (Z_to_bv 64 (fp_unLo pp)) (Z_to_bv 64 (fp_unHi pp)) lo hi (Z_to_bv 64 (fp_gtHi pp)) t3 t4 med t6)
                     F (Z_to_bv 64 0x9b8cc) fc None m (seg_rom a0segs)).
  Proof.
    induction f' as [|f' IH]; intros pp med hi lo ec me m t1 t2 a2 t3 t4 t6 v144 v160 v176 sz pf Hlo Hhi Hul OK Hsz Hf RES Hmed FMR ECR FMOK' ECOK' AR1 AR2 SC MI MU WM SH1 SH2 KB; [lia|].
    destruct pp as [fm unLo unHi ltLo gtHi]. cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi] in *. unfold fp_ok in OK. cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi] in OK.
    prep XOK XSEP fm ec. bz_params. pose proof KB as KB'. unfold KBbrk in KB'. unfold SCq in SC, KB'.
    rewrite fpart_loop_S in RES. cbv zeta in RES.
    (* [comment removed for export] *)
    arun. if_cases Kd; zify_cond_z Kd; [exfalso; lia|].
    (* [comment removed for export] *)
    arun_to 0x9b900%Z.
    enter_with (A0_plo (S sz) unLo unHi ltLo gtHi med hi lo fm ec me _ _ _ _ _ _);
      [st_eq| lia| lia| lia| lia| lia| lia| lia| exact FMR| exact ECR| exact FMOK'| exact ECOK'| exact AR1| exact AR2| unfold SCq; exact SC| exact MI| exact MU| exact WM| exact SH1| exact SH2| |].
    2:{ (* [comment removed for export] *)
      intros m' x6 x12 x13 x28 x29 x31. cbv zeta. intros AR1' AR2' SC' MI' MU' WM' FMR' FMOK2 E1 E2 R1 R2.
      remember (fpart_lo (S sz) ec med (FP fm unLo unHi ltLo gtHi)) as p1 eqn:Ep1.
      destruct p1 as [fm1 unLo1 unHi1 ltLo1 gtHi1]. cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi] in *. subst unHi1 gtHi1.
      rewrite fpart_hi_stop in RES by (cbn; lia). cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi] in RES.
      replace (unHi <? unLo1)%Z with true in RES by (symmetry; apply Z.ltb_lt; lia). subst pf.
      enter_with (KB' _ _ _ _ _ _ _ _ _ _); [cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi]; st_eq| exact AR1'| exact AR2'| unfold SCq in SC'; exact SC'| exact MI'| exact MU'| exact WM'| exact FMR'| exact FMOK2| unfold fp_ok; cbn; lia| cbn; lia]. }
    intros m' x1 x6 x12 x13 x14 x28 x29 x31. cbv zeta. intros AR1' AR2' SC' MI' MU' WM' FMR' FMOK2 E1 E2 R1 R2.
    remember (fpart_lo (S sz) ec med (FP fm unLo unHi ltLo gtHi)) as p1 eqn:Ep1.
    destruct p1 as [fm1 unLo1 unHi1 ltLo1 gtHi1]. cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi] in *. subst unHi1 gtHi1.
    clear AR1 AR2 SC MI MU WM. bz_params. unfold SCq in SC'.
    pose proof (zb8_length fm1 ARR1_SIZE ltac:(lia)) as L1'.
    (* [comment removed for export] *)
    arun. if_cases Kb; zify_cond_z Kb.
    - (* [comment removed for export] *)
      rewrite fpart_hi_stop in RES by (cbn; lia). cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi] in RES.
      replace (unHi <? unLo1)%Z with true in RES by (symmetry; apply Z.ltb_lt; lia). subst pf.
      enter_with (KB' _ _ _ _ _ _ _ _ _ _); [cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi]; st_eq| exact AR1'| exact AR2'| exact SC'| exact MI'| exact MU'| exact WM'| exact FMR'| exact FMOK2| unfold fp_ok; cbn; lia| cbn; lia].
    - pose proof (fpart_lo_exit (S sz) ec med (FP fm unLo unHi ltLo gtHi) ltac:(cbn; lia)) as HNP.
      rewrite <- Ep1 in HNP. cbn [fp_fm fp_unLo fp_unHi] in HNP. destruct HNP as [HNP|HNP]; [lia|].
      (* [comment removed for export] *)
      arun_to 0x9ba0c%Z.
      enter_with (A0_phi (S sz) unHi unHi unLo1 ltLo1 gtHi med hi lo fm1 ec me _ _ _ _ _ _ sz f' pf);
        [st_eq| lia| lia| lia| lia| lia| lia| lia| lia| lia| lia| exact FMR'| exact ECR| exact FMOK2| exact ECOK'| exact HNP| exact RES| exact AR1'| exact AR2'| unfold SCq; exact SC'| exact MI'| exact MU'| exact WM'| exact SH1| exact SH2| exact KB|].
      (* [comment removed for export] *)
      unfold KCcont. intros p3 m'' y6 y7 y12 y28 y29 y31 u144 u160 u176 H1 H2 H3 H4 AR1'' AR2'' SC'' MI'' MU'' WM'' FMR'' FMOK3.
      eapply (IH p3 med hi lo ec me m'' _ _ _ _ _ _ _ _ _ sz pf); try eassumption; try lia.
  Qed.
End A0FS.

End ACeilS1.
