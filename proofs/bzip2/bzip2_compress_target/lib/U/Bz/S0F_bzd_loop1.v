(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Wf_nat.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzDefs BzInv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzContracts BzContracts0 BzWalkArith DecCut S0_bzd_out S0_bzd_loop1.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem CmpArith BzCLemmas1.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDOut BzDOK BzDOKp BzDFrame. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecCutF DecTacF.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOK OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOKp OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDFrame OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCutF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacF.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import S0F_bzd_out.
From Stdlib Require Lia. Unset Lia Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import NatLit.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzImg0TacF.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require RelLia.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac StoreFast.tlia ::= RelLia.tlia_r.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Section ACeilS1. Context {ACEIL__ : ACeil}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition act_okF (A : act14) : Prop :=
  ctx_ok (a_cx A) /\ (a_lo A <= a_usp A - D14)%Z /\ (CEILING <= a_lo A)%Z /\ (a_usp A < 2^64)%Z /\
  Z.of_nat (length (a_payload A)) = b_len (a_cx A) /\ (1 <= b_n (a_cx A))%Z /\ (a_usp A <= b_strm (a_cx A))%Z /\
  (b_small (a_cx A) = 0%Z -> b_tt (a_cx A) <> 0%Z) /\
  (b_small (a_cx A) = 1%Z -> b_ll16 (a_cx A) <> 0%Z /\ b_ll4 (a_cx A) <> 0%Z) /\
  (b_small (a_cx A) = 0%Z \/ b_small (a_cx A) = 1%Z).

(* [comment removed for export] *)
Definition dec14F_spec (I : dimg) : Prop :=
  forall (A : act14) (J : jk) (d : dst) (s : dstrm) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    act_okF A ->
    dmem I (a_cx A) (a_g1 A) (a_sv A) (a_payload A) (a_m0 A) (dvF (a_cx A) J d s) ->
    dpureF (a_cx A) (a_b0 A) (a_payload A) J d s ->
    d_state d = 14%Z -> a_b0 A = bs_of (a_cx A) J s -> (0 <= s_avail_out s <= b_dlen (a_cx A))%Z ->
    stk (di_segs I) (a_m0 A) (a_lo A) (a_usp A) -> mem_inv (di_segs I) (a_m0 A) ->
    evt (di_segs I) (fun ms' => FPOST14 I A (decompress d s) ms' /\ dpost14W (decompress d s))
        (MS (mkR (a_ra A) (a_sp A) (a_gp A) (a_tp A) t0 t1 t2 (a_s0 A) (a_s1 A) (Z_to_bv 64 (a_S A)) a1 a2 a3 a4 a5 a6 a7
                 (a_s2 A) (a_s3 A) (a_s4 A) (a_s5 A) (a_s6 A) (a_s7 A) (a_s8 A) (a_s9 A) (a_s10 A) (a_s11 A) t3 t4 t5 t6)
            (a_F A) (Z_to_bv 64 (di_dec I)) (a_fc A) None (a_m0 A) (seg_rom (di_segs I))).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma not_crc_final : forall cb, (0 <= cb < 4294967296)%Z ->
  ((Z.lxor (bv_unsigned (sx32 (Z_to_bv 64 cb))) 18446744073709551615) mod 4294967296 = crc_final cb mod 4294967296)%Z.
Proof.
  intros cb H. rewrite low32_lxor, low32_sx32, low32_lit, (low32_small cb) by lia.
  change (18446744073709551615 mod 4294967296)%Z with 4294967295%Z. unfold crc_final. rewrite low32_small; [reflexivity|].
  apply crc_final_range. lia.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cccrc_step : forall cc crc, (0 <= cc < 4294967296)%Z -> (0 <= crc < 4294967296)%Z ->
  ((Z.lxor (Z.lor ((bv_unsigned (sx32 (Z_to_bv 64 cc)) * 2) mod 18446744073709551616) (bv_unsigned (sx32 (Z_to_bv 64 cc)) mod 4294967296 / 2147483648))
          (bv_unsigned (sx32 (Z_to_bv 64 crc)))) mod 4294967296
   = Z.lxor (Z.lor (Z.shiftl cc 1) (Z.shiftr cc 31) mod 4294967296) crc)%Z.
Proof.
  intros cc crc Hcc Hcrc.
  rewrite low32_lxor, low32_lor, mod64_mod32, low32_mul, !low32_sx32, !low32_lit, (low32_small cc), (low32_small crc) by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2^1)%Z with 2%Z. change (2^31)%Z with 2147483648%Z.
  rewrite (low32_small (cc / 2147483648)) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  f_equal. rewrite (low32_lor (cc * 2) (cc / 2147483648)). rewrite (low32_small (cc / 2147483648)) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Ctx.
  Variable z : bzdctx.
  Notation cx := (z_cx z).
  Notation S := (b_s (z_cx z)). Notation STRM := (b_strm (z_cx z)). Notation usp := (bv_unsigned (z_sp z)).
  Notation DST := (b_dst (z_cx z)). Notation dlen := (b_dlen (z_cx z)). Notation uspi := (bv_unsigned (z_spi z)).

  (* [comment removed for export] *)
  Definition FIMG (m : word -> option byte) : Prop := u32arr s0segs m 0x33178 crc_words.

  (* [comment removed for export] *)
  Definition FDEST (m : word -> option byte) (s : dstrm) (dbytes rest : list byte) : Prop :=
    u8arr s0segs m DST dbytes /\ Z.of_nat (length dbytes) = dlen /\
    dbytes = map (Z_to_bv 8) (rev (s_out s)) ++ rest /\ Z.of_nat (length (s_out s)) = (dlen - s_avail_out s)%Z.

  (* [comment removed for export] *)
  Definition FCH (m : word -> option byte) (J : jk) (d : dst) (s : dstrm) (dbytes rest : list byte) : Prop :=
    dmem DI_S0 cx (z_g1 z) (z_sv z) (z_payload z) m (dvF cx J d s) /\ FIMG m /\ FDEST m s dbytes rest /\
    rw_cells s0segs m uspi (FRM z) /\ stk s0segs m (z_lo z) uspi.

  (* [comment removed for export] *)
  Definition bzd_fpost (R : Z * dst * dstrm) : machine_state -> Prop := fun ms' =>
    let '(rv, d', s') := R in
    exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte) (J' : jk) (dbytes rest : list byte),
      ms' = MS (mkR (z_ra z) (z_sp z) (z_gp z) (z_tp z) t0 t1 t2 (z_s0 z) (z_s1 z) (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7
                    (z_s2 z) (z_s3 z) (z_s4 z) (z_s5 z) (z_s6 z) (z_s7 z) (z_s8 z) (z_s9 z) (z_s10 z) (z_s11 z) t3 t4 t5 t6)
               (z_F z) (ret_pc (z_ra z)) (z_fc z) None m' (seg_rom s0segs)
      /\ munch (WBZ z) (z_m0 z) m' /\ wmono s0segs (z_m0 z) m' /\ mem_inv s0segs m'
      /\ stk s0segs m' (z_lo z) usp
      /\ dmem DI_S0 cx (z_g1 z) (z_sv z) (z_payload z) m' (dvF cx J' d' s') /\ FIMG m' /\ FDEST m' s' dbytes rest
      /\ dpureF cx (bs_of cx J' s') (z_payload z) J' d' s'
      /\ (-5 <= rv <= 4)%Z.   (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition FFACTS (J : jk) (rv : Z) (d : dst) (s : dstrm) : Prop :=
    dpureF cx (bs_of cx J s) (z_payload z) J d s /\ (1 <= d_state d <= 50)%Z /\ (0 <= d_cccrc d < 4294967296)%Z /\
    (0 <= s_avail_out s <= dlen)%Z /\ dpost14W (rv, d, s).

  (* [comment removed for export] *)
  Definition FLKp (rpc : Z) (f : nat) : Prop :=
    forall (rax t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x9 x19 x24 t3 t4 t5 t6 : word) (m : word -> option byte)
           (rv : Z) (J : jk) (d : dst) (s : dstrm) (dbytes rest : list byte),
      FCH m J d s dbytes rest ->
      munch (WBZ z) (z_m0 z) m -> wmono s0segs (z_m0 z) m -> mem_inv s0segs m ->
      FFACTS J rv d s ->
      (d_state d = BZ_X_OUTPUT -> (b_len cx / 6 - d_blockNo d < Z.of_nat f)%Z) ->
      evt s0segs (bzd_fpost (K_L f (rv, d, s)))
          (MS (ZR z rax t0 t1 t2 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 x9 x19 x24 t3 t4 t5 t6) (z_F z) (Z_to_bv 64 rpc) (z_fc z) None m (seg_rom s0segs)).
  Definition FLK (f : nat) : Prop := FLKp 0x1481c f.
  Definition FLK2 (f : nat) : Prop := FLKp 0x15c94 f.

  (* [comment removed for export] *)
  Definition fmkc (m1 : word -> option byte) (J : jk) (d : dst) (s : dstrm) (f : nat) : foctx :=
    FOC cx J d s (z_g1 z) (z_sv z) (z_spi z) (z_gp z) (z_tp z) (z_F z) (z_fc z) (fun R => bzd_fpost (K_U f R)) m1.
End Ctx.

Section BZD.
  Variable z : bzdctx.
  Hypothesis ZOK : bzdctx_ok z.
  Notation cx := (z_cx z).
  Notation S := (b_s (z_cx z)). Notation STRM := (b_strm (z_cx z)). Notation usp := (bv_unsigned (z_sp z)).
  Notation DST := (b_dst (z_cx z)). Notation dlen := (b_dlen (z_cx z)). Notation lo := (z_lo z). Notation uspi := (bv_unsigned (z_spi z)).

  Ltac zok :=
    let CX := ident:(CX) in let Z' := fresh "ZOK" in pose proof ZOK as Z';
    cps_destruct Z' as (CX & USP & LO1 & LO2 & FJL & PAYL & SPI & SPI2);
    let CL := fresh "CL" in pose proof (proj1 CX) as CL; unfold ctx_lin in CL; cbv zeta in CL;
    bz_ceil; unfold DSTATE_SIZE, CEILING, STACK_TOP, IMG_HI_MAX, D14 in *;
    pose proof (word_urange (z_sp z)) as USPR; pose proof (word_urange (z_spi z)) as USPIR.

  (* [comment removed for export] *)
  Lemma dpureF_set8 : forall J d s oc ol nu k0 tp rn rt cb out av tout tol toh,
    dpureF cx (bs_of cx J s) (z_payload z) J d s -> (0 <= nu)%Z ->
    let J' := jk_set_o J tol toh in let d' := set8 d oc ol nu k0 tp rn rt cb in let s' := smod s out av tout in
    dpureF cx (bs_of cx J' s') (z_payload z) J' d' s'.
  Proof.
    intros until toh. intros DP Hnu. cbv zeta. unfold dpureF, jk_wf, jk_static, in_rel, drep in *. focbn_in DP. focbn.
    decompose [and] DP. repeat match goal with |- _ /\ _ => split end; try assumption; try reflexivity; try lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma bzd_fepi : forall (rax t0 t1 t2 x8 x9 x10 a1 a2 a3 a4 a5 a6 a7 x18 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
      (m : word -> option byte) (rv : Z) (J : jk) (d : dst) (s : dstrm) (dbytes rest : list byte),
    rw_cells s0segs m uspi (FRM z) -> stk s0segs m lo uspi ->
    munch (WBZ z) (z_m0 z) m -> wmono s0segs (z_m0 z) m -> mem_inv s0segs m ->
    dmem DI_S0 cx (z_g1 z) (z_sv z) (z_payload z) m (dvF cx J d s) -> FIMG m -> FDEST z m s dbytes rest ->
    dpureF cx (bs_of cx J s) (z_payload z) J d s -> (-5 <= rv <= 4)%Z ->
    evt s0segs (bzd_fpost z (rv, d, s))
        (MS (mkR rax (z_spi z) (z_gp z) (z_tp z) t0 t1 t2 x8 x9 x10 a1 a2 a3 a4 a5 a6 a7
                 x18 (Z_to_bv 64 rv) x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
            (z_F z) (Z_to_bv 64 0x15cd4) (z_fc z) None m (seg_rom s0segs)).
  Proof.
    intros until rest. intros FR ST MU WM MI DM IM DE DP RV. zok. unfold FRM, FRMj in FR.
    wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep.
    wstep.
    release_frame FR ST (bv_unsigned (z_sp z)).
    wstep. rewrite SPI2.
    apply evt_done. unfold bzd_fpost. hnf.
    do 18 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    split; [exact DM|]. split; [exact IM|]. split; [exact DE|]. split; [exact DP| exact RV].
  Qed.
End BZD.
End ACeilS1.
