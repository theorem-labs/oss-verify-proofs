(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr SysStep.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Tac DA_Eg3i.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import ExN ExW.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require JunkName.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.JunkName.split_for_access_jn H segs m A cs kn n.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stepobi.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Tac.astep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Tac.azstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition EXIT_ECALL : Z := 0x98784.
Definition WRITEV_ECALL1 : Z := 0x9df44.

(* [comment removed for export] *)
Definition part2c_post (sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists ra' t0 t1 t2 a1 a2 a3 a4 a5 a6 t3 t4 t5 t6 m',
    ms' = MSsvc (mkR ra' sp gp tp t0 t1 t2 s0 s1 s0 a1 a2 a3 a4 a5 a6 (Z_to_bv 64 94)
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 EXIT_ECALL) (Z_to_bv 64 94) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.

Section Part2.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
            (wp0 rp0 wp2 rp2 : word) (xra xs0 : word).
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
  Hypothesis LO : lo + 304 <= bv_unsigned sp.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis SPHI : bv_unsigned sp + 16 <= 2^47.
  (* [comment removed for export] *)
  Hypothesis FRX : rw_cells rsegs m (bv_unsigned sp) [C8 xs0; C8 xra].
  Hypothesis NL : ro_cells rsegs m NEED_LOCKS [C1 (Z_to_bv 8 0)].
  Hypothesis OFL : ro_cells rsegs m OFL_HEAD [C8 (Z_to_bv 64 0)].
  Hypothesis UIN : ro_cells rsegs m 0xadbf0 [C8 (Z_to_bv 64 STDIN_F)].
  Hypothesis UOUT : ro_cells rsegs m 0xadb00 [C8 (Z_to_bv 64 STDOUT_F)].
  Hypothesis UERR : ro_cells rsegs m 0xada10 [C8 (Z_to_bv 64 STDERR_F)].
  Hypothesis FIN : file_clean m STDIN_F wp0 rp0.
  Hypothesis FERR : file_clean m STDERR_F wp2 rp2.

  Section Clean.
    Variables (wp1 rp1 : word).
    Hypothesis FOUT : file_clean m STDOUT_F wp1 rp1.

    #[using="FOUT rp1 wp1 FERR FIN UERR UOUT UIN OFL NL FRX SPHI CEIL LO ST MI xs0 xra rp2 wp2 rp0 wp0 lo Clg"] Lemma exit_part2_clean :
      evt rsegs (part2c_post sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
          (MS (mkR (Z_to_bv 64 0x98a18) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x9e49c) fc None m (seg_rom rsegs)).
    Proof.
      destruct FIN as (I1 & I2 & I3 & I4 & I5). destruct FERR as (E1 & E2 & E3 & E4 & E5). destruct FOUT as (O1 & O2 & O3 & O4 & O5).
      unfold NEED_LOCKS in NL. unfold OFL_HEAD in OFL. unfold STDIN_F, STDOUT_F, STDERR_F in *. lit_addrs.
      assert (CEILv : 0x7fff7f800000 <= lo) by (pose proof alloc_ceiling_val; lia).
      pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
      carve_frame 16%nat ST.
      run_to 0x9e884. at_pc 0x9e884. carve_frame 16%nat ST.
      run_to 0x9e4ac. at_pc 0x9e4ac. release_frame FR0 ST (bv_unsigned sp + -16).
      run_to 0x98784. at_pc 0x98784.
      step_ecall. unfold part2c_post, EXIT_ECALL.
      hot_eexists_all. split; [reflexivity|]. split; [exact MU|]. split; [exact WM| exact MI].
    Qed.
  End Clean.

  Section Pending.
    Variables (wb wp : Z) (wend bufp bufsz rp1 canary : word) (pending : list byte).
    Hypothesis SOUT : stdout_pending m wb wp wend bufp bufsz rp1 canary pending.

    (* [comment removed for export] *)
    Definition wcells (m' : word -> option byte) : Prop :=
         rw_cells rsegs m' (bv_unsigned sp + -16) [C8 s0; C8 (Z_to_bv 64 0x98a18)]
      /\ rw_cells rsegs m' 711224 [C8 wend; C8 (Z_to_bv 64 wp)] /\ rw_cells rsegs m' 711248 [C8 (Z_to_bv 64 wb)]
      /\ ro_cells rsegs m' 711280 [C8 bufp; C8 bufsz] /\ ro_cells rsegs m' 711312 [C4 (Z_to_bv 64 1)]
      /\ ro_cells rsegs m' 711200 [C8 rp1; C8 rp1] /\ ro_cells rsegs m' 6325272 [C8 canary]
      /\ ro_cells rsegs m' 711184 [C8 (Z_to_bv 64 710952)]
      /\ ro_cells rsegs m' 711092 [C4 (Z_to_bv 64 4294967295)] /\ ro_cells rsegs m' 710992 [C8 wp2] /\ ro_cells rsegs m' 711008 [C8 wp2]
      /\ ro_cells rsegs m' 710960 [C8 rp2] /\ ro_cells rsegs m' 710968 [C8 rp2]
      /\ bytes_at rsegs m' wb pending.

    (* [comment removed for export] *)
    Definition wframe (j8 : list byte) (base rem : Z) : list cell :=
      [CB 8 j8; C8 (Z_to_bv 64 base); C8 (Z_to_bv 64 rem); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 canary;
       C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 (Z_to_bv 64 711192); C8 (Z_to_bv 64 0x9e54c)].

    (* [comment removed for export] *)
    Definition wst (ra' : word) (t0' t1' t2' a3' a4' a5' a6' s4' t3' t4' t5' t6' : word) (rem pc : Z) (m' : word -> option byte) : machine_state :=
      MSsvc (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 0) (Z_to_bv 64 711192)
                 (Z_to_bv 64 1) (Z_to_bv 64 (bv_unsigned sp + -120)) (Z_to_bv 64 2) a3' a4' a5' a6' (Z_to_bv 64 66)
                 (Z_to_bv 64 2) (Z_to_bv 64 (bv_unsigned sp + -120)) s4' (Z_to_bv 64 6325272) (Z_to_bv 64 rem) s7 s8 s9 s10 s11 t3' t4' t5' t6')
            F (Z_to_bv 64 pc) (Z_to_bv 64 66) fc None m' (seg_rom rsegs).

    Definition part2p_post : machine_state -> Prop :=
      fun ms' => exists a3' j8 m',
        ms' = wst (Z_to_bv 64 0x9e54c) t0 t1 t2 a3' a4 a5 a6 s4 t3 t4 t5 t6 (wp - wb) WRITEV_ECALL1 m'
        /\ munch [(bv_unsigned sp - 128, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ stk rsegs m' lo (bv_unsigned sp + -128)
        /\ rw_cells rsegs m' (bv_unsigned sp + -128) (wframe j8 wb (wp - wb))
        /\ wcells m'.

    #[using="SOUT FERR FIN UERR UOUT UIN OFL NL FRX SPHI CEIL LO ST MI xs0 xra rp0 wp0 Clg"] Lemma exit_part2_pending : evt rsegs part2p_post
          (MS (mkR (Z_to_bv 64 0x98a18) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x9e49c) fc None m (seg_rom rsegs)).
    Proof.
      destruct FIN as (I1 & I2 & I3 & I4 & I5). destruct FERR as (E1 & E2 & E3 & E4 & E5).
      destruct SOUT. destruct sp_ssp as [G1 G2].
      unfold NEED_LOCKS in NL. unfold OFL_HEAD in OFL. unfold STDIN_F, STDOUT_F, STDERR_F, STDIO_WRITE, SSP_GOT, SSP_GUARD, STDOUT_BUF in *. lit_addrs.
      assert (CEILv : 0x7fff7f800000 <= lo) by (pose proof alloc_ceiling_val; lia).
      pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
      carve_frame 16%nat ST.
      run_to 0x9e884. at_pc 0x9e884. carve_frame 16%nat ST.
      run_to 0x9e4ac. at_pc 0x9e4ac. release_frame FR0 ST (bv_unsigned sp + -16).
      run_to 0x9e534. at_pc 0x9e534. azstep. br_not_taken.
      run_to 0x9debc. at_pc 0x9debc.
      carve_frame 112%nat ST.
      run_to 0x9df1c. at_pc 0x9df1c.
      assert (LX : 0 < Z.lxor wp wb).
      { assert (Z.lxor wp wb <> 0) by (intros HH; apply Z.lxor_eq in HH; lia).
        pose proof (proj2 (Z.lxor_nonneg wp wb) ltac:(lia)). lia. }
      azstep. replace (Z.b2z (0 <? Z.lxor wp wb)) with 1 by (rewrite (proj2 (Z.ltb_lt _ _) LX); reflexivity).
      azstep. br_not_taken. run_to 0x9df44. at_pc 0x9df44.
      step_ecall. unfold part2p_post, wst, wframe, wcells, WRITEV_ECALL1.
      hot_eexists_all. split; [reflexivity|].
      repeat (split; [eassumption|]). eassumption.
    Qed.

    (* [comment removed for export] *)
    Definition done_post (m1 : word -> option byte) : machine_state -> Prop :=
      fun ms' => exists ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' t3' t4' t5' t6' m',
        ms' = MSsvc (mkR ra' sp gp tp t0' t1' t2' s0 s1 s0 a1' a2' a3' a4' a5' a6' (Z_to_bv 64 94)
                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (Z_to_bv 64 EXIT_ECALL) (Z_to_bv 64 94) fc None m' (seg_rom rsegs)
        /\ munch [(711224, 711224 + 16); (711248, 711248 + 8)] m1 m' /\ wmono rsegs m1 m' /\ mem_inv rsegs m'.

    #[using="CEIL LO Clg"] Lemma writev_done : forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' t3' t4' t5' t6' : word)
        (m1 : word -> option byte) (j8 : list byte) (base rem : Z),
      mem_inv rsegs m1 -> stk rsegs m1 lo (bv_unsigned sp + -128) ->
      rw_cells rsegs m1 (bv_unsigned sp + -128) (wframe j8 base rem) -> wcells m1 ->
      evt rsegs (done_post m1)
          (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 0) (Z_to_bv 64 711192)
                   a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' (Z_to_bv 64 6325272) (Z_to_bv 64 rem) s7 s8 s9 s10 s11 t3' t4' t5' t6')
              F (Z_to_bv 64 0x9df50) fc None m1 (seg_rom rsegs)).
    Proof.
      intros until rem. intros MI1 ST1 FRW WC.
      (first [ dand14 WC as FRE Wpos Wbase Wbuf Wfd Wrpos Wcan Wuerr We1 We2 We3 We4 We5 Wbytes | destruct WC as (FRE & Wpos & Wbase & Wbuf & Wfd & Wrpos & Wcan & Wuerr & We1 & We2 & We3 & We4 & We5 & Wbytes) ]).
      unfold wframe in FRW.
      assert (CEILv : 0x7fff7f800000 <= lo) by (pose proof alloc_ceiling_val; lia).
      pose proof (munch_refl [(711224, 711224 + 16); (711248, 711248 + 8)] m1) as MU. pose proof (wmono_refl rsegs m1) as WM.
      run_to 0x9df74. at_pc 0x9df74. bstep. bstep.
      run_to 0x98784. at_pc 0x98784.
      step_ecall. unfold done_post, EXIT_ECALL.
      hot_eexists_all. split; [reflexivity|]. split; [exact MU|]. split; [exact WM| exact MI1].
    Qed.

    (* [comment removed for export] *)
    Definition more_post (ra' t0' t1' t2' s4' t3' t4' t5' t6' : word) (base rem k : Z) (j8 : list byte) (m1 : word -> option byte)
        : machine_state -> Prop :=
      fun ms' => exists a3' a4' a5' a6' m',
        ms' = wst ra' t0' t1' t2' a3' a4' a5' a6' (Z_to_bv 64 (bv_unsigned sp + -120)) t3' t4' t5' t6' (rem - k) 0x9dfcc m'
        /\ munch [(bv_unsigned sp - 128, bv_unsigned sp + -16)] m1 m' /\ wmono rsegs m1 m' /\ mem_inv rsegs m'
        /\ stk rsegs m' lo (bv_unsigned sp + -128)
        /\ rw_cells rsegs m' (bv_unsigned sp + -128) (wframe j8 (base + k) (rem - k))
        /\ wcells m'.

    #[using="SOUT SPHI CEIL LO m Clg"] Lemma writev_more : forall (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' t3' t4' t5' t6' : word)
        (m1 : word -> option byte) (j8 : list byte) (base rem k : Z),
      mem_inv rsegs m1 -> stk rsegs m1 lo (bv_unsigned sp + -128) ->
      rw_cells rsegs m1 (bv_unsigned sp + -128) (wframe j8 base rem) -> wcells m1 ->
      1 <= k < rem -> 0 <= base -> base + rem <= 0x60a000 ->
      evt rsegs (more_post ra' t0' t1' t2' s4' t3' t4' t5' t6' base rem k j8 m1)
          (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 0) (Z_to_bv 64 711192)
                   (Z_to_bv 64 k) a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 2) (Z_to_bv 64 (bv_unsigned sp + -120)) s4'
                   (Z_to_bv 64 6325272) (Z_to_bv 64 rem) s7 s8 s9 s10 s11 t3' t4' t5' t6')
              F (Z_to_bv 64 0x9dfdc) fc None m1 (seg_rom rsegs)).
    Proof.
      intros until k. intros MI1 ST1 FRW WC K1 B0 BHI.
      (first [ dand14 WC as FRE Wpos Wbase Wbuf Wfd Wrpos Wcan Wuerr We1 We2 We3 We4 We5 Wbytes | destruct WC as (FRE & Wpos & Wbase & Wbuf & Wfd & Wrpos & Wcan & Wuerr & We1 & We2 & We3 & We4 & We5 & Wbytes) ]).
      destruct SOUT. clear sp_lock sp_wpos sp_wbase sp_write sp_buf sp_fd sp_rpos sp_bytes sp_ssp.
      unfold wframe in FRW. unfold STDOUT_BUF in sp_range.
      assert (CEILv : 0x7fff7f800000 <= lo) by (pose proof alloc_ceiling_val; lia).
      pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp + -16)] m1) as MU. pose proof (wmono_refl rsegs m1) as WM.
      azstep. br_not_taken. azstep. azstep.
      replace (Z.b2z (rem <? k)) with 0 by (rewrite (proj2 (Z.ltb_ge rem k) ltac:(lia)); reflexivity).
      do 6 azstep. rewrite Z.land_0_l, Z.sub_0_r.
      azstep. azstep. at_pc 0x9e008. azstep. br_taken.
      run_to 0x9dfcc. at_pc 0x9dfcc.
      step_ecall. unfold more_post, wst, wframe, wcells.
      hot_eexists_all. split; [reflexivity|].
      repeat (split; [eassumption|]). eassumption.
    Qed.

    (* [comment removed for export] *)
    Definition after_post (t0' t1' t2' a2' a3' a4' a5' a6' a7' s4' t3' t4' t5' t6' : word) (ra k rem : Z) (m1 : word -> option byte)
        : machine_state -> Prop :=
      fun ms' =>
        ms' = MS (mkR (Z_to_bv 64 ra) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 0) (Z_to_bv 64 711192)
                      (Z_to_bv 64 k) (Z_to_bv 64 (-4095)) a2' a3' a4' a5' a6' a7' (Z_to_bv 64 2) (Z_to_bv 64 (bv_unsigned sp + -120)) s4'
                      (Z_to_bv 64 6325272) (Z_to_bv 64 rem) s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (Z_to_bv 64 (if Z.eqb k rem then 0x9df50 else 0x9dfdc)) fc None m1 (seg_rom rsegs).

    Lemma writev_after1 : forall (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' t3' t4' t5' t6' : word) (m1 : word -> option byte) (k rem : Z),
      mem_inv rsegs m1 -> 1 <= k <= rem -> rem <= 1024 ->
      evt rsegs (after_post t0' t1' t2' a2' a3' a4' a5' a6' a7' s4' t3' t4' t5' t6' 0x9df4c k rem m1)
          (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 0) (Z_to_bv 64 711192)
                   (Z_to_bv 64 k) a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 2) (Z_to_bv 64 (bv_unsigned sp + -120)) s4'
                   (Z_to_bv 64 6325272) (Z_to_bv 64 rem) s7 s8 s9 s10 s11 t3' t4' t5' t6')
              F (Z_to_bv 64 0x9df48) fc None m1 (seg_rom rsegs)).
    Proof.
      intros until rem. intros MI1 K1 R1.
      pose proof (munch_refl ([] : list (Z * Z)) m1) as MU. pose proof (wmono_refl rsegs m1) as WM.
      azstep. azstep. azstep. azstep. br_taken. azstep. at_pc 0x9df4c.
      azstep. if_cases K; zify_cond K.
      - apply evt_done. unfold after_post. replace (k =? rem) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
      - apply evt_done. unfold after_post. replace (k =? rem) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity.
    Qed.

    Lemma writev_after2 : forall (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s3' t3' t4' t5' t6' : word) (m1 : word -> option byte) (k rem : Z),
      mem_inv rsegs m1 -> 1 <= k <= rem -> rem <= 1024 ->
      evt rsegs (after_post t0' t1' t2' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (bv_unsigned sp + -120)) t3' t4' t5' t6' 0x9dfd4 k rem m1)
          (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 0) (Z_to_bv 64 711192)
                   (Z_to_bv 64 k) a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 2) s3' (Z_to_bv 64 (bv_unsigned sp + -120))
                   (Z_to_bv 64 6325272) (Z_to_bv 64 rem) s7 s8 s9 s10 s11 t3' t4' t5' t6')
              F (Z_to_bv 64 0x9dfd0) fc None m1 (seg_rom rsegs)).
    Proof.
      intros until rem. intros MI1 K1 R1.
      pose proof (munch_refl ([] : list (Z * Z)) m1) as MU. pose proof (wmono_refl rsegs m1) as WM.
      azstep. azstep. azstep. azstep. br_taken. azstep. at_pc 0x9dfd4. azstep.
      azstep. if_cases K; zify_cond K.
      - apply evt_done. unfold after_post. replace (k =? rem) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity.
      - apply evt_done. unfold after_post. replace (k =? rem) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
    Qed.
  End Pending.
End Part2.
