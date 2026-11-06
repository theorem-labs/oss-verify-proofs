(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Wf_nat.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 StoreFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel BzTac BzDefs BzInv BzTables BzLemmasT BzLemmasMtf BzContracts BzWalkArith DecCut S0_bzd_out S0_bzd_loop1 BzSepTac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem CmpArith BzCLemmas1.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDOut BzDOK BzDOKp BzDFrame DecCutF DecTacF.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOKp OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDFrame OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import S0F_bzd_out S0F_bzd_outS S0F_bzd_loop1.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit DecCutA DecCutFA A0F_decV A0F_bzdV.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFastZ StoreFastC.   (* [comment removed for export] *)
Local Ltac mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | mem_after_store_fast ].
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Ltac unhide_disj := repeat match goal with H : id (?A \/ ?B) |- _ => unfold id in H end.
Ltac hide_disj := repeat match goal with H : ?A \/ ?B |- _ => change (A \/ B) with (id (A \/ B)) in H end.
Local Ltac tlia ::= first [ Zify.zify; xlia zchecker
                         | sf_unhide; unhide_disj;
                           first [ zify_prune_neg; Zify.zify; xlia zchecker
                                 | zify_prune_plain; Zify.zify; xlia zchecker
                                 | Zify.zify; xlia zchecker ] ].
Local Ltac tslia ::= tslia_sep.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import NatLit.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require NormFast RelLiaA SasFastF RelLiaS.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= RelLiaA.lia_rf.
Local Ltac BzTac.bz32 ::= NormFast.bz32_m.
Local Ltac BzTac2.bz32l ::= NormFast.bz32l_m.
Local Ltac Zify.zify_pre_hook ::= NormFast.nf_pre_natlen.
Local Ltac DecCutF.unset_Z ::= NormFast.unset_Z_subst.
Local Ltac simpl_arr_sizes ::= SasFastF.sas6F_all.
Local Ltac tlia ::= RelLiaS.tlia_bzd_r.
Local Ltac BzSepTac.tlia1 ::= RelLiaS.tlia1_r.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
Local Ltac AsanKit.a_norm ::= AsanKit.sh_fold.
Section ACeilS1. Context {ACEIL__ : ACeil}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FAST_aspec (rand pc : Z) : Prop := forall (c : foctx) (SHS : Z) (w0 : word),
  foctx_okA c AIHI0 -> foctx_okFA c AIHI0 -> sanchor (b_s (o_cx c)) SHS -> obz_sh DI_A0 c (FWBA c) (o_m0 c) ->
  A0_FKjoin c SHS w0 (FROfA DI_A0 c) -> A0_FKexit c SHS w0 (FROfA DI_A0 c) ->
  forall (t0 t2 a0 a1 a3 a4 a5 a6 s3 s4 s7 t3 t4 t5 t6 w32 w104 w112 : word) (m : word -> option byte) (dbytes rest : list byte),
    DSgA DI_A0 c m (o_J c) (o_d c) (o_s c) -> DESTgA DI_A0 c m (o_s c) dbytes rest ->
    rw_cells a0segs m (bv_unsigned (o_SP c))
      (bzd_slots (b_s (o_cx c)) SHS w0 w32 w104 w112 (Z_to_bv 64 (SHS + -2147450877)) (Z_to_bv 64 (SHS + -2147450878)) (Z_to_bv 64 (SHS + -2147450872))
                 (Z_to_bv 64 (SHS + -2147450873)) (Z_to_bv 64 (SHS + -2147450875)) (Z_to_bv 64 (SHS + -2147450744)) (Z_to_bv 64 (SHS + -2147442870))) ->
    FROfA DI_A0 c m -> munch (FWBA c) (o_m0 c) m -> wmono a0segs (o_m0 c) m ->
    d_rand (o_d c) = rand ->
    evt a0segs (o_KQ c (unRLE (o_d c) (o_s c)))
        (MS (A0RR c SHS (Z_to_bv 64 (SHS + 398)) t0 (Z_to_bv 64 (SHS + -2147450879)) t2 a0 a1 (Z_to_bv 64 (SHS + -2147450486)) a3 a4 a5 a6
                  (Z_to_bv 64 (SHS + -2147450878)) s3 s4 s7 t3 t4 t5 t6)
            (o_F c) (Z_to_bv 64 pc) (o_fc c) None m (seg_rom a0segs)).
(* [comment removed for export] *)
Definition SMALL_aspec (rand pc : Z) : Prop := forall (c : foctx) (SHS : Z) (w0 : word),
  foctx_okA c AIHI0 -> foctx_okSA c AIHI0 -> sanchor (b_s (o_cx c)) SHS -> obz_sh DI_A0 c (FWBA c) (o_m0 c) ->
  A0_FKjoin c SHS w0 (FROsA DI_A0 c) -> A0_FKexit c SHS w0 (FROsA DI_A0 c) ->
  forall (t0 t2 a2 a3 a4 a5 a6 s3 s4 s7 t3 t4 t5 t6 w32 : word) (m : word -> option byte) (dbytes rest : list byte),
    DSgA DI_A0 c m (o_J c) (o_d c) (o_s c) -> DESTgA DI_A0 c m (o_s c) dbytes rest ->
    rw_cells a0segs m (bv_unsigned (o_SP c))
      (bzd_slots (b_s (o_cx c)) SHS w0 w32 (Z_to_bv 64 (SHS + -2147450484)) (Z_to_bv 64 (SHS + -2147450485)) (Z_to_bv 64 (SHS + -2147450877))
                 (Z_to_bv 64 (SHS + -2147450878)) (Z_to_bv 64 (SHS + -2147450872)) (Z_to_bv 64 (SHS + -2147450873))
                 (Z_to_bv 64 (SHS + -2147450875)) (Z_to_bv 64 (SHS + -2147450744)) (Z_to_bv 64 (SHS + -2147442870))) ->
    FROsA DI_A0 c m -> munch (FWBA c) (o_m0 c) m -> wmono a0segs (o_m0 c) m ->
    d_rand (o_d c) = rand ->
    evt a0segs (o_KQ c (unRLE (o_d c) (o_s c)))
        (MS (A0RR c SHS (Z_to_bv 64 (SHS + 398)) t0 (Z_to_bv 64 (SHS + -2147450879)) t2 (Z_to_bv 64 (s_avail_out (o_s c))) (Z_to_bv 64 (b_strm (o_cx c)))
                  a2 a3 a4 a5 a6 (Z_to_bv 64 (SHS + -2147450878)) s3 s4 s7 t3 t4 t5 t6)
            (o_F c) (Z_to_bv 64 pc) (o_fc c) None m (seg_rom a0segs)).
Definition FASTNR_aspec : Prop := FAST_aspec 0 0x86a00.
Definition FASTR_aspec : Prop := FAST_aspec 1 0x85e3c.
Definition SMALLNR_aspec : Prop := SMALL_aspec 0 0x85c1c.
Definition SMALLR_aspec : Prop := SMALL_aspec 1 0x8456c.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Ctx.
  Variable z : bzdctx.
  Variable SHS : Z.                                              (* [comment removed for export] *)
  Variable w0 : word.                                            (* [comment removed for export] *)
  Variable QF : Z * dst * dstrm -> machine_state -> Prop.        (* [comment removed for export] *)
  Notation cx := (z_cx z).
  Notation S := (b_s (z_cx z)). Notation STRM := (b_strm (z_cx z)). Notation SRC := (b_src (z_cx z)). Notation len := (b_len (z_cx z)).
  Notation DST := (b_dst (z_cx z)). Notation dlen := (b_dlen (z_cx z)). Notation n := (b_n (z_cx z)).
  Notation TT := (b_tt (z_cx z)). Notation L16 := (b_ll16 (z_cx z)). Notation L4 := (b_ll4 (z_cx z)).
  Notation usp := (bv_unsigned (z_sp z)). Notation uspi := (bv_unsigned (z_spi z)).

  (* [comment removed for export] *)
  Definition bzdctx_okA : Prop :=
    ((0 < S /\ S + 64144 <= alloc_ceiling) /\ (0 < STRM /\ STRM + 80 <= alloc_ceiling) /\
     (0 < SRC /\ 0 <= len < 2^27 /\ SRC + len <= alloc_ceiling) /\ (0 < DST /\ DST + dlen <= alloc_ceiling) /\ (0 <= dlen < 2^27) /\
     (S mod 16 = 0 /\ STRM mod 8 = 0) /\ (b_small cx = 0 \/ b_small cx = 1) /\ 0 <= n <= 9 /\
     (alloc_ceiling <= z_lo z /\ z_lo z + 400 <= usp /\ usp < 2^64) /\
     uspi = usp - 400 /\ Z_to_bv 64 (uspi + 400) = z_sp z /\ Z.of_nat (length (z_payload z)) = len)%Z /\
    sanchor S SHS /\
    (disj S 64144 STRM 80 /\ disj S 64144 SRC len /\ disj S 64144 DST dlen /\ disj STRM 80 SRC len /\ disj STRM 80 DST dlen /\ disj SRC len DST dlen /\
     bzd_img_apart AIHI0 S 64144 /\ bzd_img_apart AIHI0 STRM 80 /\ bzd_img_apart AIHI0 DST dlen) /\
    (TT <> 0%Z -> (0 < TT /\ TT + 400000 * n <= alloc_ceiling)%Z /\ disj S 64144 TT (400000 * n) /\ disj STRM 80 TT (400000 * n) /\
                  disj DST dlen TT (400000 * n) /\ bzd_img_apart AIHI0 TT (400000 * n)) /\
    (L16 <> 0%Z -> (0 < L16 /\ L16 + 200000 * n <= alloc_ceiling)%Z /\ disj S 64144 L16 (200000 * n) /\ disj STRM 80 L16 (200000 * n) /\
                   disj DST dlen L16 (200000 * n) /\ bzd_img_apart AIHI0 L16 (200000 * n)) /\
    (L4 <> 0%Z -> (0 < L4 /\ L4 + 50000 * n <= alloc_ceiling)%Z /\ disj S 64144 L4 (50000 * n) /\ disj STRM 80 L4 (50000 * n) /\
                  disj DST dlen L4 (50000 * n) /\ bzd_img_apart AIHI0 L4 (50000 * n)) /\
    (L16 <> 0%Z -> L4 <> 0%Z -> disj L16 (200000 * n) L4 (50000 * n)).

  (* [comment removed for export] *)
  Definition FSAVA : list cell :=
    [C8 (z_s11 z); C8 (z_s10 z); C8 (z_s9 z); C8 (z_s8 z); C8 (z_s7 z); C8 (z_s6 z); C8 (z_s5 z);
     C8 (z_s4 z); C8 (z_s3 z); C8 (z_s2 z); C8 (z_s1 z); C8 (z_s0 z); C8 (z_ra z)].

  (* [comment removed for export] *)
  Definition WLA : list ivl :=
    [(S, S + 68); (S + 1092, S + 1096); (S + 3152, S + 3196); (STRM, STRM + 44); (DST, DST + dlen); (uspi, uspi + 296)]%Z.

  (* [comment removed for export] *)
  Definition FIMGA (m : word -> option byte) : Prop := u32arr a0segs m 802816 crc_words.
  Definition FDESTA (m : word -> option byte) (s : dstrm) (dbytes rest : list byte) : Prop :=
    u8arr a0segs m DST dbytes /\ Z.of_nat (length dbytes) = dlen /\
    dbytes = map (Z_to_bv 8) (rev (s_out s)) ++ rest /\ Z.of_nat (length (s_out s)) = (dlen - s_avail_out s)%Z.

  (* [comment removed for export] *)
  Definition FCHA (m : word -> option byte) (J : jk) (d : dst) (s : dstrm) (dbytes rest : list byte)
                  (w32 w104 w112 w120 w184 w192 w200 w208 w240 w248 : word) : Prop :=
    DecCutA.dmem DI_A0 cx (z_g1 z) (z_sv z) (z_payload z) m (dvF cx J d s) /\ FIMGA m /\ FDESTA m s dbytes rest /\
    rw_cells a0segs m uspi (bzd_slots S SHS w0 w32 w104 w112 w120 w184 w192 w200 w208 w240 w248) /\
    rw_cells a0segs m (uspi + 296) FSAVA /\ stk a0segs m (z_lo z) uspi.

  (* [comment removed for export] *)
  Definition bzd_sh (W : list ivl) (m0 : word -> option byte) : Prop :=
    shzW a0segs W m0 S (S + 64144) /\ shzW a0segs W m0 STRM (STRM + 80) /\ shpW a0segs W m0 DST (DST + dlen) /\
    shzW a0segs W m0 802816 (802816 + 1024) /\ shzW a0segs W m0 804096 (804096 + 2048) /\
    (b_small cx = 0%Z -> shzW a0segs W m0 TT (TT + 400000 * n)) /\
    (b_small cx = 1%Z -> shzW a0segs W m0 L16 (L16 + 200000 * n) /\ shzW a0segs W m0 L4 (L4 + 50000 * n)).

  (* [comment removed for export] *)
  Definition ZRA (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s7 t3 t4 t5 t6 : word) :=
    mkR ra (z_spi z) (z_gp z) (z_tp z) t0 t1 t2 (Z_to_bv 64 1) (Z_to_bv 64 S) a0 a1 a2 a3 a4 a5 a6 a7
        (Z_to_bv 64 (S + 16)) (Z_to_bv 64 (S + 3188)) s4 (Z_to_bv 64 SHS) (Z_to_bv 64 (S + 12)) s7 (Z_to_bv 64 (S + 3184))
        (Z_to_bv 64 2147450880) (Z_to_bv 64 (S + 1096)) (Z_to_bv 64 (S + 3152)) t3 t4 t5 t6.

  (* [comment removed for export] *)
  Definition A0_KRet (W : list ivl) : Prop :=
    forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte) (rv : Z) (J' : jk) (d' : dst) (s' : dstrm)
           (dbytes rest : list byte),
      DecCutA.dmem DI_A0 cx (z_g1 z) (z_sv z) (z_payload z) m' (dvF cx J' d' s') -> FIMGA m' -> FDESTA m' s' dbytes rest ->
      stk a0segs m' (z_lo z) usp ->
      munch W (z_m0 z) m' -> wmono a0segs (z_m0 z) m' -> mem_inv a0segs m' ->
      dpureF cx (bs_of cx J' s') (z_payload z) J' d' s' -> (-5 <= rv <= 4)%Z ->
      evt a0segs (QF (rv, d', s'))
          (MS (mkR (z_ra z) (z_sp z) (z_gp z) (z_tp z) t0 t1 t2 (z_s0 z) (z_s1 z) (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7
                   (z_s2 z) (z_s3 z) (z_s4 z) (z_s5 z) (z_s6 z) (z_s7 z) (z_s8 z) (z_s9 z) (z_s10 z) (z_s11 z) t3 t4 t5 t6)
              (z_F z) (ret_pc (z_ra z)) (z_fc z) None m' (seg_rom a0segs)).

  (* [comment removed for export] *)
  Definition A0_KCall (W : list ivl) (f : nat) : Prop :=
    forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s7 t3 t4 t5 t6 w32 w104 w112 w120 w184 w192 w200 w208 w240 w248 : word)
           (m' : word -> option byte) (J' : jk) (d' : dst) (s' : dstrm) (dbytes rest : list byte),
      FCHA m' J' d' s' dbytes rest w32 w104 w112 w120 w184 w192 w200 w208 w240 w248 ->
      munch W (z_m0 z) m' -> wmono a0segs (z_m0 z) m' -> mem_inv a0segs m' ->
      dpureF cx (bs_of cx J' s') (z_payload z) J' d' s' -> d_state d' = 14%Z ->
      (0 <= d_cccrc d' < 4294967296)%Z -> (0 <= s_avail_out s' <= dlen)%Z ->
      (len / 6 - d_blockNo d' <= Z.of_nat f)%Z ->
      evt a0segs (QF (K_call f d' s'))
          (MS (ZRA (Z_to_bv 64 0x87038) t0 t1 t2 (Z_to_bv 64 S) a1 a2 a3 a4 a5 a6 a7 s4 s7 t3 t4 t5 t6)
              (z_F z) (Z_to_bv 64 0x9e368) (z_fc z) None m' (seg_rom a0segs)).

  (* [comment removed for export] *)
  Definition FLKA (f : nat) : Prop :=
    forall (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s7 t3 t4 t5 t6 w32 w104 w112 w120 w184 w192 w200 w208 w240 w248 : word)
           (m : word -> option byte) (rv : Z) (J : jk) (d : dst) (s : dstrm) (dbytes rest : list byte),
      FCHA m J d s dbytes rest w32 w104 w112 w120 w184 w192 w200 w208 w240 w248 ->
      munch WLA (z_m0 z) m -> wmono a0segs (z_m0 z) m -> mem_inv a0segs m ->
      FFACTS z J rv d s ->
      (d_state d = BZ_X_OUTPUT -> (len / 6 - d_blockNo d < Z.of_nat f)%Z) ->
      evt a0segs (QF (K_L f (rv, d, s)))
          (MS (ZRA ra t0 t1 t2 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s4 s7 t3 t4 t5 t6) (z_F z) (Z_to_bv 64 0x87038) (z_fc z) None m (seg_rom a0segs)).

  (* [comment removed for export] *)
  Definition fmkcA (m1 : word -> option byte) (J : jk) (d : dst) (s : dstrm) (f : nat) : foctx :=
    FOC cx J d s (z_g1 z) (z_sv z) (z_spi z) (z_gp z) (z_tp z) (z_F z) (z_fc z) (fun R => QF (K_U f R)) m1.
End Ctx.
End ACeilS1.
