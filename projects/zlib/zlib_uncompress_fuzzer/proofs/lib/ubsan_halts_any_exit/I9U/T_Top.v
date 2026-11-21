(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit Require Import RunCtx.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.IK Require IConj.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.IK.IConj.
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel Require ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit Require PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Frame Hoare AllocSim.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit Require U9LibStmt.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.IK Require MstepsGrows.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U Require TBase T_Entry T_U2C T_U2A.

Module T_ZA.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U.TBase OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U.T_Entry.T_Loop OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U.T_U2C.T_Ret OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U.T_Entry OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U.T_U2Cw.T_Uw OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U.T_U2C.T_LeaveA OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U.T_U2C.T_Leave OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U.T_U2C.T_Inflate OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U.T_U2A OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U.T_U2C.T_U2B OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U.T_U2C.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

Lemma le_cell_range : forall k bs i, 0 < k <= 8 -> 0 <= le_cell k bs i < 2 ^ (8 * k).
Proof.
  intros k bs i Hk. unfold le_cell.
  pose proof (bytes_le_to_Z_nonneg (firstn (Z.to_nat k) (skipn (Z.to_nat (k * i)) bs))) as H0.
  pose proof (bytes_le_to_Z_bound (firstn (Z.to_nat k) (skipn (Z.to_nat (k * i)) bs))) as H1.
  pose proof (firstn_le_length (Z.to_nat k) (skipn (Z.to_nat (k * i)) bs)) as Hl.
  assert (2 ^ (8 * Z.of_nat (length (firstn (Z.to_nat k) (skipn (Z.to_nat (k * i)) bs)))) <= 2 ^ (8 * k)).
  { apply Z.pow_le_mono_r; lia. }
  lia.
Qed.

Lemma mem_wr_arrk_exists {RCa1 : RunCtx}  : forall k M base n,
  0 < k <= 8 -> 0 <= n -> 0 <= base -> base + k * n <= two64 ->
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M base (k * n) ->
  exists f, mem_arr k (run_segments R_segs rc_inp rc_sp rc_mb) M base n f /\ (forall i, 0 <= f i < 2 ^ (8 * k)).
Proof.
  intros k M base n Hk Hn Hb Hbn W.
  destruct (mem_wr_readable (run_segments R_segs rc_inp rc_sp rc_mb) wr_rd_R M base (k * n) W ltac:(lia)) as (bs & Hbs & Hlen).
  exists (le_cell k bs). split.
  - apply (mem_arr_of_bytes (run_segments R_segs rc_inp rc_sp rc_mb) k M base n bs Hbs); lia.
  - intros i. apply le_cell_range. exact Hk.
Qed.

Section ZA.
Context {RCa1 : RunCtx}.
Variables (u p q n gp tp s5 s6 s7 s8 s9 s10 s11 : Z) (fin : Z -> Z) (MD : Model) (T : TSet).
Variable zc : Z.
Hypothesis Hh : m_halted MD = None.
Hypothesis Hfin : forall i, 0 <= i < n -> 0 <= fin i < 256.
Hypothesis Hu0 : zc + FRA <= u. Hypothesis Hzimg : DATA_LO + DATA_LEN <= zc. Hypothesis Hu1 : u + 208 <= 140737488355328. Hypothesis Hua : u mod 16 = 0.
Hypothesis Hp0 : 0 < p. Hypothesis Hp1 : p + STATE_SIZE <= zc. Hypothesis Hpa : p mod 16 = 0.
Hypothesis Hq1 : 1 <= q. Hypothesis Hn0 : 0 <= n. Hypothesis Hn1 : n < 67108864. Hypothesis Hqn : q + n <= zc.
Hypothesis Spq : ZSEP (p + STATE_SIZE <= q \/ q + n <= p).
Hypothesis Spob : ZSEP (p + STATE_SIZE <= BUF \/ BUF + 262144 <= p).
Hypothesis Sobq : ZSEP (BUF + 262144 <= q \/ q + n <= BUF).
Hypothesis Sprom : ZSEP (p + STATE_SIZE <= ROM_LO_ALL \/ ROMHI_T <= p).
Hypothesis Rgp : 0 <= gp < two64. Hypothesis Rtp : 0 <= tp < two64.
Hypothesis Rs5 : 0 <= s5 < two64. Hypothesis Rs6 : 0 <= s6 < two64. Hypothesis Rs7 : 0 <= s7 < two64. Hypothesis Rs8 : 0 <= s8 < two64.
Hypothesis Rs9 : 0 <= s9 < two64. Hypothesis Rs10 : 0 <= s10 < two64. Hypothesis Rs11 : 0 <= s11 < two64.
Hypothesis MEMCPY : memcpy_spec_t.
Hypothesis ADLER : adler32_spec_t.
Hypothesis A_HEAD : arm_stmt L_HEAD HEAD.
Hypothesis A_DICTID : arm_stmt L_DICTID DICTID.
Hypothesis A_DICT : arm_stmt L_DICT DICT.
Hypothesis A_TYPE : arm_stmt L_TYPE TYPE.
Hypothesis A_TYPEDO : arm_stmt L_TYPEDO TYPEDO.
Hypothesis A_STORED : arm_stmt L_STORED STORED.
Hypothesis A_COPY_ : arm_stmt L_COPY_ COPY_.
Hypothesis A_COPY : arm_stmt L_COPY COPY.
Hypothesis A_TABLE : arm_stmt L_TABLE TABLE.
Hypothesis A_LENLENS : arm_stmt L_LENLENS LENLENS.
Hypothesis A_CODELENS : arm_stmt L_CODELENS CODELENS.
Hypothesis A_LEN_ : arm_stmt L_LEN_ LEN_.
Hypothesis A_LEN : arm_stmt L_LEN LEN.
Hypothesis A_LENEXT : arm_stmt L_LENEXT LENEXT.
Hypothesis A_DIST : arm_stmt L_DIST DIST.
Hypothesis A_DISTEXT : arm_stmt L_DISTEXT DISTEXT.
Hypothesis A_MATCH : arm_stmt L_MATCH MATCH.
Hypothesis A_LIT : arm_stmt L_LIT LIT.
Hypothesis A_CHECK : arm_stmt_ob L_CHECK CHECK.
Hypothesis A_LENGTH : arm_stmt L_LENGTH LENGTH.

Definition st_init (vlen vofs vext vlb vdb vnc vnl vnd vsh : Z) : ist :=
  IST HEAD 0 (-1) 0 0 0 0 262144 0 vlen vofs vext (CDyn 0) (CDyn 0) vlb vdb vnc vnl vnd vsh 0 0 0.

Lemma ainv_init : forall (lf cf : Z -> Z) vlen vofs vext vlb vdb vnc vnl vnd vsh W0 ra,
  (forall i, 0 <= i < N_LENS -> 0 <= lf i < 65536) -> (forall i, 0 <= i < N_CODES -> 0 <= cf i < 4294967296) ->
  0 <= vlen < 4294967296 -> 0 <= vofs < 4294967296 -> 0 <= vext < 4294967296 -> 0 <= vlb < 4294967296 -> 0 <= vdb < 4294967296 ->
  0 <= vnc < 4294967296 -> 0 <= vnl < 4294967296 -> 0 <= vnd < 4294967296 -> 0 <= vsh < 4294967296 ->
  ainv (cxc u p q n gp tp s5 s6 s7 s8 s9 s10 s11 zc 0 0 0 W0 ra) (st_init vlen vofs vext vlb vdb vnc vnl vnd vsh) lf cf.
Proof.
  intros lf cf vlen vofs vext vlb vdb vnc vnl vnd vsh W0 ra Hlf Hcf R1 R2 R3 R4 R5 R6 R7 R8 R9.
  pose proof two64_eq as TW64.
  unfold ainv, RNG, WIN, MODE, st_init, cxc; icx_cbn. cbv [N_CODES N_LENS WIN_SIZE]. cbv [N_CODES N_LENS] in Hlf, Hcf.
  split; [| split].
  - split_conj; first [assumption | lia_std | change (2 ^ 0) with 1; lia_std].
  - split; [intros _; split; reflexivity | intros C; exfalso; exact (C eq_refl)].
  - split_conj.
    + left. reflexivity.
    + intros _. split; [left; reflexivity | reflexivity].
    + intros E. exfalso. revert E. cbv. discriminate.
    + intros E. exfalso. revert E. cbv. discriminate.
    + intros E. exfalso. revert E. unfold codes_liveP. cbv [LEN_ LIT HEAD]. lia_std.
    + intros E. exfalso. revert E. cbv. discriminate.
    + intros E. exfalso. revert E. cbv. discriminate.
    + intros E. exfalso. revert E. cbv. discriminate.
    + intros E. exfalso. revert E. cbv. discriminate.
    + intros [E|E]; exfalso; revert E; cbv; discriminate.
Qed.

Theorem za_cps : forall Rb l M,
  zget_l Rb l kSP = u + -32 -> zget_l Rb l kS2 = u -> zget_l Rb l kS1 = 7176 -> zget_l Rb l kA0 = p ->
  zget_l Rb l kS3 = n -> zget_l Rb l kS4 = 262144 -> zget_l Rb l kS5 = s5 ->
  zget_l Rb l kGP = gp -> zget_l Rb l kTP = tp ->
  zget_l Rb l kS6 = s6 -> zget_l Rb l kS7 = s7 -> zget_l Rb l kS8 = s8 -> zget_l Rb l kS9 = s9 ->
  zget_l Rb l kS10 = s10 -> zget_l Rb l kS11 = s11 ->
  rom_ok M -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -1024) 1232 -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M p STATE_SIZE ->
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M q n fin ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -32) BUF -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -24) (u + 160) -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -16) (u + 168) ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -8) RA_II ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u) q -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 8) 0 ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 64) A_ZCALLOC -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 72) A_ZCFREE -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 80) 0 ->
  KZE2 u p gp tp s5 s6 s7 s8 s9 s10 s11 MD T M 0 ->
  KZW u p q n gp tp s5 s6 s7 s8 s9 s10 s11 fin MD T M zc 0 ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_ZA (zupd Rb l) M MD) T.
Proof.
  intros Rb l M Lsp Ls2 Ls1 La0 Ls3 Ls4 Ls5 Lgp Ltp Ls6 Ls7 Ls8 Ls9 Ls10 Ls11
         ROM Wstk Wp Hin Fm32 Fm24 Fm16 Fm8 S8 S16 S72 S80 S88 HZE2 HZW.
  pose proof two64_eq as TW64.
  assert (Hwph : wok p q n zc 0).
  pose proof Hzimg as Hz'. cbv [DATA_LO DATA_LEN] in Hz'.
  { unfold wok, ZSEP. cbv [WIN_SIZE ]. split_conj; try lia_std; try (left; reflexivity). reflexivity. }
  eapply (za_prefix_t Rb l M MD T u p q n zc gp tp s5 s6 s7 s8 s9 s10 s11 fin Hh); try eassumption.
  intros R' M' vlen vofs vext vlb vdb vnc vnl vnd vsh.
  intros Gsp Gs0 Gs1 Gs2 Gs3 Gs4 Gs5 Ggp Gtp Gs6 Gs7 Gs8 Gs9 Gs10 Gs11
         ROM' Wstk' Wp' Hin' T8 T16 T32 T40 T64 T72 T80 T88
         P0 P8 P12 P16 P24 P48 P56 P60 P64 P68 P72 P80 P88 P92 P96 P100 P104 P112 P120 P124 P128 P132 P136 P140 P144 P7144 P7148
         Rlen Rofs Rext Rlb Rdb Rnc Rnl Rnd Rsh HP.
  zkeys. unfold ZSEP in *. cbv [STATE_SIZE FRA ROM_LO_ALL BUF A_ZCALLOC A_ZCFREE HEAD] in *.
  destruct (mem_wr_arrk_exists 2 M' (p + 168) 320 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(eapply mem_wr_sub; [exact Wp' | lia | lia])) as (lf & Hlens & Hlf).
  destruct (mem_wr_arrk_exists 4 M' (p + 1384) 1444 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(eapply mem_wr_sub; [exact Wp' | lia | lia])) as (cf & Hcodes & Hcf).
  change (2 ^ (8 * 2)) with 65536 in Hlf. change (2 ^ (8 * 4)) with 4294967296 in Hcf.
  pose proof (ainv_init lf cf vlen vofs vext vlb vdb vnc vnl vnd vsh (8 * (n - 0) + 0 + (262144 - 0)) RA_C2
                ltac:(intros i _; apply Hlf) ltac:(intros i _; apply Hcf) Rlen Rofs Rext Rlb Rdb Rnc Rnl Rnd Rsh) as AI.
  assert (HZE1 : KZE1 u p gp tp s5 s6 s7 s8 s9 s10 s11 MD T M 0) by (intros R1 M1; intros; exfalso; lia_std).
  eapply (pcall_all u p q n gp tp s5 s6 s7 s8 s9 s10 s11 fin MD T M zc Hh Hfin Hu0 Hzimg Hu1 Hua Hp0 Hp1 Hpa Hq1 Hn0 Hn1 Hqn
            Spq Spob Sobq Sprom Rgp Rtp Rs5 Rs6 Rs7 Rs8 Rs9 Rs10 Rs11 MEMCPY ADLER
            A_HEAD A_DICTID A_DICT A_TYPE A_TYPEDO A_STORED A_COPY_ A_COPY A_TABLE A_LENLENS A_CODELENS
            A_LEN_ A_LEN A_LENEXT A_DIST A_DISTEXT A_MATCH A_LIT A_CHECK A_LENGTH 0 Hwph HZE2 HZE1 HZW
            (M2v n (st_init vlen vofs vext vlb vdb vnc vnl vnd vsh) + 1) false R' M' (st_init vlen vofs vext vlb vdb vnc vnl vnd vsh) lf cf).
  - exact AI.
  - lia.
  - unfold u2regs. zkeys. split_conj; assumption.
  - unfold e_mem, cxc, st_init, i_cst, i_hooks, st_at, st_rest, strm_at, cp_addr, wsz; icx_cbn. cbv [STATE_SIZE o_codes BUF A_ZCALLOC A_ZCFREE N_LENS N_CODES].
    cbn [Z.eqb].
    split_conj; try assumption;
      first [ apply buf_writable
            | intros i Hi; exfalso; lia_std
            | match goal with H : mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) ?My ?a ?v |- mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) ?My ?a ?v' => replace v' with v by lia_std; exact H
                            | H : mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) ?My ?a ?v |- mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) ?My ?a ?v' => replace v' with v by lia_std; exact H end
            |
              apply (s_bk_intro _ _ _ 4294967295); [ exact P7148 | lia_std | cbv; intros E; discriminate E | cbv; intros E; discriminate E ]
            | match goal with |- ?G => idtac "EMSIDE" G end ].
  - eapply (framed_mpostL_trans _ _ _ _ _ _ (mpostL_refl (run_segments R_segs rc_inp rc_sp rc_mb) M (fp_u2 u p 0)) HP).
    intros x Hx; eapply ranges_within_outside; [| exact Hx]; unfold fp_u2; cbv [STATE_SIZE WIN_SIZE]; cbn [Z.eqb]; ranges_within_tac.
Qed.
End ZA.
End T_ZA.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.IK Require ZStep ZMem ZTac ZPrune ZSysLite ZCall ZCallL ZArr ZRd IGlue IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U Require Base.

Module T_ZC.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.ShapeAlg OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.Frame OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.Hoare OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.AllocSim.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.U9LibStmt.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.IK.ZStep OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.IK.ZMem OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.IK.ZTac OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.IK.ZPrune OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.IK.ZSysLite OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.IK.ZCall OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.IK.ZCallL OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.IK.ZArr OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.IK.ZRd OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.IK.IGlue OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.IK.IDefs OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.IK.MstepsGrows.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U.Base.
Import ListNotations. Open Scope bv_scope. Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.

(* uncompress2_z's epilogue (0x14ee8; UBSan): ld ra, s0 .. s4 (frame 160, no s5), addi, ret. *)
Definition L_EPI_T : Z := 0x14f48.

Ltac zreg := cbv [zget_l kRA kSP kGP kTP kT0 kT1 kT2 kS0 kS1 kA0 kA1 kA2 kA3 kA4 kA5 kA6 kA7
                  kS2 kS3 kS4 kS5 kS6 kS7 kS8 kS9 kS10 kS11 kT3 kT4 kT5 kT6];
             cbn [alookup Pos.eqb]; rewrite ?zget_zupd; cbv [zget_l]; cbn [alookup Pos.eqb];
             zrefold_getl; zbase; first [ reflexivity | assumption | OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.IK.ITac.zarith_goal; lia ].
Ltac zkeys := cbv [kRA kSP kGP kTP kT0 kT1 kT2 kS0 kS1 kA0 kA1 kA2 kA3 kA4 kA5 kA6 kA7
                   kS2 kS3 kS4 kS5 kS6 kS7 kS8 kS9 kS10 kS11 kT3 kT4 kT5 kT6] in *.

Section ZC.
Context {RCa1 : RunCtx}.

Lemma zc_epi : forall Rb l M MD T (u v0 v1 v2 v3 v4 v5 : Z),
  m_halted MD = None ->
  zget_l Rb l kSP = u ->
  U9_IMG_TOP <= u - 16 -> u + 208 <= 2 ^ 47 ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 152) U9_HARN_RA ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 144) v0 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 136) v1 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 128) v2 ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 120) v3 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 112) v4 ->
  (forall lc,
     zget_l Rb lc kSP = u + 160 ->
     zget_l Rb lc kS0 = v0 -> zget_l Rb lc kS1 = v1 -> zget_l Rb lc kS2 = v2 ->
     zget_l Rb lc kS3 = v3 -> zget_l Rb lc kS4 = v4 -> zget_l Rb lc kS5 = zget_l Rb l kS5 ->
     zget_l Rb lc kGP = zget_l Rb l kGP -> zget_l Rb lc kTP = zget_l Rb l kTP ->
     zget_l Rb lc kS6 = zget_l Rb l kS6 -> zget_l Rb lc kS7 = zget_l Rb l kS7 -> zget_l Rb lc kS8 = zget_l Rb l kS8 ->
     zget_l Rb lc kS9 = zget_l Rb l kS9 -> zget_l Rb lc kS10 = zget_l Rb l kS10 -> zget_l Rb lc kS11 = zget_l Rb l kS11 ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) U9_HARN_RA (zupd Rb lc) M MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_EPI_T (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T u v0 v1 v2 v3 v4 v5 Hh Lsp Hc1 Hc2 H152 H144 H136 H128 H120 H112 K.
  zkeys. unfold U9_IMG_TOP, U9_HARN_RA, L_EPI_T in *. pose proof two64_eq as TW64.
  zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd.   (* ld ra; ld s0 .. s4 *)
  zstep Rfd.                          (* addi sp,sp,160 *)
  zret Rfd.
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd _ ?lc) _ _) _ => apply (K lc) end; zreg.
Qed.

Lemma zsetreg_lemma : forall segs pc Rb k (e v : Z) rest M MD T, v = e ->
  realizes segs (zcfg segs pc (zupd Rb ((k, v) :: rest)) M MD) T ->
  realizes segs (zcfg segs pc (zupd Rb ((k, e) :: rest)) M MD) T.
Proof. intros. subst. assumption. Qed.
Ltac zsetreg v tac := eapply (zsetreg_lemma _ _ _ _ _ v); [tac|].

(* inflateEnd's tail from the zfree return (U9_ZC), back in uncompress2_z at RA2: the err in s0 (inflateEnd
   restores it) is mapped (Z_STREAM_END -> Z_OK, Z_NEED_DICT -> Z_DATA_ERROR, Z_BUF_ERROR with len + avail_in = 0 ->
   Z_DATA_ERROR), then the epilogue. Every branch reaches the epilogue; the return value is not stated. *)
Lemma zc_cps : forall Rb l M MD T (u v0 v1 v2 v3 v4 v5 s16 s3v : Z),
  m_halted MD = None ->
  zget_l Rb l kSP = u + (-16) -> zget_l Rb l kS0 = u ->
  zget_l Rb l kS3 = s3v -> 0 <= s16 < two64 -> 0 <= s3v < two64 ->
  U9_IMG_TOP <= u - 16 -> u + 208 <= 2 ^ 47 ->
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (u + (-16)) 224 ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + (-8)) U9_RA2 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + (-16)) s16 ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 152) U9_HARN_RA ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 144) v0 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 136) v1 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 128) v2 ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 120) v3 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 112) v4 ->
  (forall lc M',
     mpost (run_segments R_segs rc_inp rc_sp rc_mb) M M' (u + 56) (u + 64) 0 0 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (u + 56) 0 ->
     zget_l Rb lc kSP = u + 160 ->
     zget_l Rb lc kS0 = v0 -> zget_l Rb lc kS1 = v1 -> zget_l Rb lc kS2 = v2 ->
     zget_l Rb lc kS3 = v3 -> zget_l Rb lc kS4 = v4 -> zget_l Rb lc kS5 = zget_l Rb l kS5 ->
     zget_l Rb lc kGP = zget_l Rb l kGP -> zget_l Rb lc kTP = zget_l Rb l kTP ->
     zget_l Rb lc kS6 = zget_l Rb l kS6 -> zget_l Rb lc kS7 = zget_l Rb l kS7 -> zget_l Rb lc kS8 = zget_l Rb l kS8 ->
     zget_l Rb lc kS9 = zget_l Rb l kS9 -> zget_l Rb lc kS10 = zget_l Rb l kS10 -> zget_l Rb lc kS11 = zget_l Rb l kS11 ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) U9_HARN_RA (zupd Rb lc) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) U9_ZC (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T u v0 v1 v2 v3 v4 v5 s16 s3v Hh Lsp Ls0 Ls3 Rs16 Rs3 Hc1 Hc2
         WR H8 H16 H152 H144 H136 H128 H120 H112 K.
  zkeys. unfold U9_IMG_TOP, U9_HARN_RA, U9_RA2, U9_ZC, L_EPI_T in *. pose proof two64_eq as TW64.
  pose proof (mpost_refl (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 56) (u + 64) 0 0 : framed (fun X => mpost (run_segments R_segs rc_inp rc_sp rc_mb) M X (u + 56) (u + 64) 0 0) M) as HAG.
  pose proof (mpost_stable (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 56) (u + 64) 0 0 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HST.
  zstep Rfd.                          (* 17ce0 li a0,0 *)
  zstep Rfd.                          (* 17ce4 sd zero,56(s0) *)
  lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mc _) _ =>
  assert (EPI : forall lc, zget_l Rb lc 3 = u ->
     zget_l Rb lc 4 = zget_l Rb l 4 -> zget_l Rb lc 5 = zget_l Rb l 5 -> zget_l Rb lc 22 = zget_l Rb l 22 ->
     zget_l Rb lc 23 = zget_l Rb l 23 -> zget_l Rb lc 24 = zget_l Rb l 24 -> zget_l Rb lc 25 = zget_l Rb l 25 ->
     zget_l Rb lc 26 = zget_l Rb l 26 -> zget_l Rb lc 27 = zget_l Rb l 27 -> zget_l Rb lc 28 = zget_l Rb l 28 ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_EPI_T (zupd Rb lc) Mc MD) T) end.
  { intros lc Gsp G4 G5 G22 G23 G24 G25 G26 G27 G28.
    eapply (zc_epi Rb lc _ MD T u v0 v1 v2 v3 v4 v5 Hh Gsp Hc1 Hc2 H152 H144 H136 H128 H120 H112).
    intros lc2 Q3 Q9 Q10 Q19 Q20 Q21 Q22 Q4 Q5 Q23 Q24 Q25 Q26 Q27 Q28.
    lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mq _) _ => apply (K lc2 Mq) end;
      first [ exact HAG | assumption | etransitivity; eassumption ]. }
  zstep Rfd.                          (* 17ce8 ld ra,8(sp) *)
  zstep Rfd.                          (* 17cec ld s0,0(sp) *)
  zstep Rfd.                          (* 17cf0 addi sp,sp,16 *)
  zret Rfd.                           (* 17cf4 ret: RA2 *)
  Local Ltac to_epi EPI := lazymatch goal with |- realizes _ (zcfg _ _ (zupd _ ?lc) _ _) _ => apply (EPI lc) end; zreg.
  zstep Rfd.                          (* 14ebc li a1,1 *)
  destruct (Z.eq_dec s16 1) as [E1|N1]; [zbr Rfd true | zbr Rfd false].   (* beq s0,a1: Z_STREAM_END *)
  { zstep Rfd. to_epi EPI. }          (* li a0,0 *)
  zstep Rfd. zstep Rfd.               (* mv a0,s0; li a1,2 *)
  destruct (Z.eq_dec s16 2) as [E2|N2]; [zbr Rfd true | zbr Rfd false].   (* beq s0,a1: Z_NEED_DICT *)
  { zstep Rfd. zstep Rfd. to_epi EPI. }   (* li a0,-3; j *)
  zstep Rfd. zstep Rfd.               (* xori a1,a0,-5; or a1,a1,s3 *)
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd _ ((_, ?e) :: _)) _ _) _ => destruct (Z.eq_dec (e mod 18446744073709551616) 0) as [Ez|Ez] end; [zbr Rfd false | zbr Rfd true].
  2: { to_epi EPI. }
  zstep Rfd. zstep Rfd. to_epi EPI.   (* li a0,-3; j *)
Qed.
End ZC.


Definition MD0 : Model := mkModel [] (mkVmMaps [] [] (Z_to_bv 64 0) (Z_to_bv 64 0) 0) IEof [] None None None.
Lemma MD0_halted : m_halted MD0 = None.
Proof. reflexivity. Qed.

Theorem zc_t {RCa1 : RunCtx}  : zc_stmt_U9.
Proof.
  unfold zc_stmt_U9.
  intros regs mem u v0 v1 v2 v3 v4 v5 Hsp Hs0 Hal Hceil Htop ST R8 R152 R144 R136 R128 R120 R112.
  pose proof Hceil as Hc'. unfold U9_IMG_TOP in Hc'.
  set (Rb := zlift regs).
  assert (Gk : forall r : reg, bv_eqb r 0%bv = false -> zget_l Rb [] (bv_key r) = bv_unsigned (getr regs r)).
  { intros r Hr. cbv [zget_l alookup]. subst Rb. rewrite zget_zlift, (getr_reg_get regs r Hr). reflexivity. }
  assert (Lsp : zget_l Rb [] kSP = u + (-16)).
  { change kSP with (bv_key (2%bv : reg)). rewrite Gk by reflexivity. rewrite Hsp.
    change (Z_to_bv 64 (u - 16)) with (w64 (u - 16)). rewrite w64_unsigned, mod_small_u64 by lia. lia. }
  assert (Ls0 : zget_l Rb [] kS0 = u).
  { change kS0 with (bv_key (8%bv : reg)). rewrite Gk by reflexivity. rewrite Hs0.
    change (Z_to_bv 64 (u)) with (w64 (u)). rewrite w64_unsigned, mod_small_u64 by lia. lia. }
  pose proof (u64_range (getr regs 19)) as Rs3.
  pose proof (mem_wr_of_store_ok _ _ _ _ ST) as WR. rewrite Z2Nat.id in WR by lia.
  change (mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) mem (u - 16) 224) in WR.
  destruct (mem_wr_u64_exists_R mem (u + (-16)) ltac:(eapply mem_wr_sub; [exact WR | lia | lia])) as (s16 & H16 & Rs16).
  set (Q := fun c : config => exists lc M',
    c = zcfg (run_segments R_segs rc_inp rc_sp rc_mb) U9_HARN_RA (zupd Rb lc) M' MD0
    /\ mpost (run_segments R_segs rc_inp rc_sp rc_mb) mem M' (u + 56) (u + 64) 0 0
    /\ zget_l Rb lc kSP = u + 160
    /\ zget_l Rb lc kS0 = bv_unsigned v0 /\ zget_l Rb lc kS1 = bv_unsigned v1 /\ zget_l Rb lc kS2 = bv_unsigned v2
    /\ zget_l Rb lc kS3 = bv_unsigned v3 /\ zget_l Rb lc kS4 = bv_unsigned v4 /\ zget_l Rb lc kS5 = zget_l Rb [] kS5
    /\ zget_l Rb lc kGP = zget_l Rb [] kGP /\ zget_l Rb lc kTP = zget_l Rb [] kTP
    /\ zget_l Rb lc kS6 = zget_l Rb [] kS6 /\ zget_l Rb lc kS7 = zget_l Rb [] kS7 /\ zget_l Rb lc kS8 = zget_l Rb [] kS8
    /\ zget_l Rb lc kS9 = zget_l Rb [] kS9 /\ zget_l Rb lc kS10 = zget_l Rb [] kS10 /\ zget_l Rb lc kS11 = zget_l Rb [] kS11).
  assert (HR : realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) U9_ZC (zupd Rb []) mem MD0) Q).
  { eapply (zc_cps Rb [] mem MD0 Q u (bv_unsigned v0) (bv_unsigned v1) (bv_unsigned v2) (bv_unsigned v3)
              (bv_unsigned v4) (bv_unsigned v5) s16 (bv_unsigned (getr regs 19)) MD0_halted Lsp Ls0).
    - change kS3 with (bv_key (19%bv : reg)). apply Gk. reflexivity.
    - exact Rs16.
    - exact Rs3.
    - exact Hceil.
    - exact Htop.
    - exact WR.
    - exact R8.
    - exact H16.
    - exact R152. - exact R144. - exact R136. - exact R128. - exact R120. - exact R112.
    - intros lc M' HP HM Q3 Q9 Q10 Q19 Q20 Q21 Q22 Q4 Q5 Q23 Q24 Q25 Q26 Q27 Q28.
      apply rz_now. subst Q. cbv beta. exists lc, M'.
      repeat (split; [first [reflexivity | assumption] |]). assumption. }
  dand HR as (ms' & RUN & HQ). subst Q. cbv beta in HQ. cbn [cfg_ms cfg_model zcfg] in RUN, HQ.
  dand HQ as (lc & M' & E & HP & Q3 & Q9 & Q10 & Q19 & Q20 & Q21 & Q22 & Q4 & Q5 & Q23 & Q24 & Q25 & Q26 & Q27 & Q28).
  unfold zcfg in E. injection E as E1. subst ms'.
  exists (zden (zupd Rb lc)), M'.
  assert (GET : forall (r : reg) k v, bv_eqb r 0%bv = false -> bv_key r = k -> zget_l Rb lc k = v ->
                getr (zden (zupd Rb lc)) r = w64 v).
  { intros r k v Hr Hk Hv. rewrite (getr_zupd Rb lc r Hr), Hk, Hv. reflexivity. }
  assert (KEEP : forall (r0 : reg) k, bv_eqb r0 0%bv = false -> bv_key r0 = k -> zget_l Rb lc k = zget_l Rb [] k ->
            getr (zden (zupd Rb lc)) r0 = getr regs r0).
  { intros r0 k Hr0 Hk HQk. rewrite (GET r0 k _ Hr0 Hk HQk). rewrite <- Hk, (Gk r0 Hr0). apply w64_of_word. }
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]].
  - unfold zst in RUN. cbn [zupd] in RUN. subst Rb. rewrite zden_zlift in RUN. exact RUN.
  - replace 8 with (u + 64 - (u + 56)) by lia.
    apply (frame_mod_of_mpost (run_segments R_segs rc_inp rc_sp rc_mb)); [lia | lia | exact HP |].
    pose proof (msteps_mem_grows (run_segments R_segs rc_inp rc_sp rc_mb) _ _ RUN) as G. unfold zst in G. cbn [ms_mem] in G. exact G.
  - rewrite (GET 2%bv kSP (u + 160) eq_refl eq_refl Q3). reflexivity.
  - rewrite (GET 8%bv kS0 _ eq_refl eq_refl Q9). apply w64_of_word.
  - rewrite (GET 9%bv kS1 _ eq_refl eq_refl Q10). apply w64_of_word.
  - rewrite (GET 18%bv kS2 _ eq_refl eq_refl Q19). apply w64_of_word.
  - rewrite (GET 19%bv kS3 _ eq_refl eq_refl Q20). apply w64_of_word.
  - rewrite (GET 20%bv kS4 _ eq_refl eq_refl Q21). apply w64_of_word.
  - eapply KEEP; [reflexivity | reflexivity | exact Q22].
  - intros r Hr. unfold S_ENTRY in Hr. cbn [app] in Hr.
    repeat (destruct Hr as [<- | Hr];
      [ eapply KEEP; [ reflexivity | reflexivity
                     | first [ exact Q4 | exact Q5 | exact Q23 | exact Q24 | exact Q25 | exact Q26 | exact Q27 | exact Q28 ] ] |]).
    destruct Hr.
Qed.
End T_ZC.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U Require T_Tok.

Module T_ZB.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U.TBase OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U.T_Entry.T_Loop OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U.T_U2C.T_Ret OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U.T_Entry OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U.T_U2Cw.T_Uw OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U.T_U2C.T_LeaveA OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U.T_U2C.T_Leave OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U.T_U2C.T_Inflate OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U.T_U2A OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U.T_U2C.T_U2B OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U.T_U2C T_ZA OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U.T_Tok.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

Lemma sinv_rewin : forall u p q n gp tp s5 s6 s7 s8 s9 s10 s11 zc w cin0 cout0 W0 ra st lf cf wh wn,
  sinv (cxc u p q n gp tp s5 s6 s7 s8 s9 s10 s11 zc 0 cin0 cout0 W0 ra) st lf cf ->
  w <> 0 -> 0 <= wh -> wh <= WIN_SIZE -> 0 <= wn -> wn < WIN_SIZE -> (wh < WIN_SIZE -> wn = wh) ->
  sinv (cxc u p q n gp tp s5 s6 s7 s8 s9 s10 s11 zc w cin0 cout0 W0 ra) (set_win st wh wn) lf cf.
Proof.
  intros u p q n gp tp s5 s6 s7 s8 s9 s10 s11 zc w cin0 cout0 W0 ra st lf cf wh wn (R & W & P & Mo) Hw H1 H2 H3 H4 H5.
  destruct st; unfold sinv, set_win, RNG, WIN, PROG, MODE, Wm, tables_live, ctable_live, cxc in *; cbn -[Z.add Z.mul Z.sub Z.pow] in *.
  split; [| split; [| split; [exact P | exact Mo]]].
  - destr_conj R. split_conj; try assumption; lia_std.
  - split; [intros E; exfalso; exact (Hw E) | intros _; split_conj; assumption].
Qed.

Lemma wok0 : forall p q n zc, DATA_LO + DATA_LEN <= zc -> wok p q n zc 0.
Proof.
  intros p q n zc Hz. unfold wok, ZSEP. cbv [WIN_SIZE]. cbv [DATA_LO DATA_LEN] in Hz.
  split_conj; try lia_std; try (left; reflexivity). reflexivity.
Qed.

Section ZB.
Context {RCa1 : RunCtx}.
Variables (u p q n gp tp s5 s6 s7 s8 s9 s10 s11 : Z) (fin : Z -> Z) (MD : Model) (T : TSet).
Variable zc : Z.
Hypothesis Hh : m_halted MD = None.
Hypothesis Hfin : forall i, 0 <= i < n -> 0 <= fin i < 256.
Hypothesis Hu0 : zc + FRA <= u. Hypothesis Hzimg : DATA_LO + DATA_LEN <= zc. Hypothesis Hu1 : u + 208 <= 140737488355328. Hypothesis Hua : u mod 16 = 0.
Hypothesis Hp0 : 0 < p. Hypothesis Hp1 : p + STATE_SIZE <= zc. Hypothesis Hpa : p mod 16 = 0.
Hypothesis Hq1 : 1 <= q. Hypothesis Hn0 : 0 <= n. Hypothesis Hn1 : n < 67108864. Hypothesis Hqn : q + n <= zc.
Hypothesis Spq : ZSEP (p + STATE_SIZE <= q \/ q + n <= p).
Hypothesis Spob : ZSEP (p + STATE_SIZE <= BUF \/ BUF + 262144 <= p).
Hypothesis Sobq : ZSEP (BUF + 262144 <= q \/ q + n <= BUF).
Hypothesis Sprom : ZSEP (p + STATE_SIZE <= ROM_LO_ALL \/ ROMHI_T <= p).
Hypothesis Rgp : 0 <= gp < two64. Hypothesis Rtp : 0 <= tp < two64.
Hypothesis Rs5 : 0 <= s5 < two64. Hypothesis Rs6 : 0 <= s6 < two64. Hypothesis Rs7 : 0 <= s7 < two64. Hypothesis Rs8 : 0 <= s8 < two64.
Hypothesis Rs9 : 0 <= s9 < two64. Hypothesis Rs10 : 0 <= s10 < two64. Hypothesis Rs11 : 0 <= s11 < two64.
Hypothesis MEMCPY : memcpy_spec_t.
Hypothesis ADLER : adler32_spec_t.
Hypothesis A_HEAD : arm_stmt L_HEAD HEAD.
Hypothesis A_DICTID : arm_stmt L_DICTID DICTID.
Hypothesis A_DICT : arm_stmt L_DICT DICT.
Hypothesis A_TYPE : arm_stmt L_TYPE TYPE.
Hypothesis A_TYPEDO : arm_stmt L_TYPEDO TYPEDO.
Hypothesis A_STORED : arm_stmt L_STORED STORED.
Hypothesis A_COPY_ : arm_stmt L_COPY_ COPY_.
Hypothesis A_COPY : arm_stmt L_COPY COPY.
Hypothesis A_TABLE : arm_stmt L_TABLE TABLE.
Hypothesis A_LENLENS : arm_stmt L_LENLENS LENLENS.
Hypothesis A_CODELENS : arm_stmt L_CODELENS CODELENS.
Hypothesis A_LEN_ : arm_stmt L_LEN_ LEN_.
Hypothesis A_LEN : arm_stmt L_LEN LEN.
Hypothesis A_LENEXT : arm_stmt L_LENEXT LENEXT.
Hypothesis A_DIST : arm_stmt L_DIST DIST.
Hypothesis A_DISTEXT : arm_stmt L_DISTEXT DISTEXT.
Hypothesis A_MATCH : arm_stmt L_MATCH MATCH.
Hypothesis A_LIT : arm_stmt L_LIT LIT.
Hypothesis A_CHECK : arm_stmt_ob L_CHECK CHECK.
Hypothesis A_LENGTH : arm_stmt L_LENGTH LENGTH.
Variable w : Z.
Hypothesis Hw : wok p q n zc w.
Variables (site : bool) (cin0 cout0 W0 s4u s5u rvu : Z) (st : ist) (lf cf : Z -> Z).
Hypothesis Hcin0 : 0 <= cin0 <= n.
Hypothesis Hcout0 : 0 <= cout0 <= 262144.
Hypothesis SI : sinv (cxc u p q n gp tp s5 s6 s7 s8 s9 s10 s11 zc 0 cin0 cout0 W0 (ra_site site)) st lf cf.
Hypothesis Hcc : cout0 < t_cout st.

Local Ltac open_zb :=
  zkeysb; unfold L_UW_RET, L_RET, L_ZB, T_ZE1, T_ZE2, RA2 in *;
  cbv [STATE_SIZE FRA WIN_SIZE ROM_LO_ALL A_ZCALLOC A_ZCFREE BUF DATA_LO DATA_LEN] in *;
  pose proof two64_eq as TW64.

Theorem zb_cps : forall Rb l M,
  zget_l Rb l kSP = u + -320 -> zget_l Rb l kA0 = w ->
  zget_l Rb l kS0 = BUF + t_cout st -> zget_l Rb l kS1 = t_out st - (262144 - t_cout st) ->
  zget_l Rb l kS2 = 1 -> zget_l Rb l kS3 = p -> zget_l Rb l kS5 = s4u -> zget_l Rb l kS6 = s5u ->
  zget_l Rb l kS9 = t_hold st -> zget_l Rb l kS7 = n - t_cin st -> zget_l Rb l kS10 = q + t_cin st ->
  zget_l Rb l kS11 = rvu -> zget_l Rb l kS4 = t_out st - (262144 - t_cout st) ->
  zget_l Rb l kGP = gp -> zget_l Rb l kTP = tp ->
  rom_ok M -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -1024) 1232 -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M p STATE_SIZE ->
  (w <> 0 -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M w WIN_SIZE) ->
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M q n fin ->
  tok_mem (cxc u p q n gp tp s5 s6 s7 s8 s9 s10 s11 zc 0 cin0 cout0 W0 (ra_site site)) st s4u s5u lf cf M ->
  KZE2 u p gp tp s5 s6 s7 s8 s9 s10 s11 MD T M w ->
  KZE1 u p gp tp s5 s6 s7 s8 s9 s10 s11 MD T M w ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_ZB (zupd Rb l) M MD) T.
Proof.
  intros Rb l M Lsp La0 Ls0 Ls1 Ls2 Ls3 Ls4 Ls5 Ls6 Ls8 Ls9 Ls10 Ls11 Lgp Ltp ROM Wstk Wp Ww Hin TM HZE2 HZE1.
  pose proof Hw as Hw'. dand Hw' as (W1 & W2 & W3 & W4 & W5 & W6 & W7).
  pose proof SI as SI'. dand SI' as (RNG_ & _ & _ & _).
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  icx_cbn.
  assert (RF : 0 <= cin /\ cin <= n /\ 0 <= cout /\ cout <= 262144 /\ 262144 - cout <= out /\ out <= 262144 /\ out - (262144 - cout) <= cout).
  { clear -RNG_. unfold RNG, cxc in RNG_. icx_cbn. destr_conj RNG_. split_conj; assumption. }
  clear RNG_. dand RF as (Rci0 & Rci1 & Rco0 & Rco1 & Rou0 & Rou1 & Rou2).
  dand TM as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & FRM & CST & HK & SAT & STRM & SLO & SBK & Hlens & Hcodes).
  unfold cxc in *. icx_cbn.
  pose proof CST as CST'. unfold i_cst in CST'. icx_cbn. unfold wsz in CST'. icx_cbn. cbn [Z.eqb] in CST'.
  dand CST' as (C64 & C88 & Cp0 & Cp16 & Cp48 & Cp56 & Cp60 & Cp72 & Cp7144).
  dand (out_arr_exists M) as (fo & HOB & Hfo). cbv [BUF_N] in HOB.
  open_zb.
  assert (T1' : mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -256 + -8) 96768) by (replace (u + -256 + -8) with (u + -264) by lia_std; exact T1).
  assert (T2' : mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -256 + -16) p) by (replace (u + -256 + -16) with (u + -272) by lia_std; exact T2).
  assert (T3' : mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -256 + -24) (213360 + cout)) by (replace (u + -256 + -24) with (u + -280) by lia_std; exact T3).
  assert (T4' : mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -256 + -32) (u)) by (replace (u + -256 + -32) with (u + -288) by lia_std; exact T4).
  assert (T5' : mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -256 + -40) bits) by (replace (u + -256 + -40) with (u + -296) by lia_std; exact T5).
  assert (T6' : mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -256 + -48) (out - (262144 - cout))) by (replace (u + -256 + -48) with (u + -304) by lia_std; exact T6).
  assert (T7' : mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -256 + -56) s4u) by (replace (u + -256 + -56) with (u + -312) by lia_std; exact T7).
  clear T1 T2 T3 T4 T5 T6 T7.
  eapply (uw_resume_t MEMCPY Rb l M MD T p 213360 262144 w cout (out - (262144 - cout)) (u + -256) 96768
            p (213360 + cout) (u) bits (out - (262144 - cout)) s4u zc fo Hh).
  all: lazymatch goal with
       | |- forall R' M', w = 0 -> _ => idtac
       | |- forall R' M' whave' wnext', _ => idtac
       | |- ZSEP _ => first [ assumption | unfold ZSEP; lia_std ]
       | |- mem_u64 _ _ _ _ => assumption
       | |- mem_u32 _ _ _ _ => assumption
       | |- mem_arr _ _ _ _ _ _ => exact HOB
       | |- mem_wr _ _ _ _ => first [ assumption | eapply mem_wr_sub; [exact Wstk | lia_std | lia_std] ]
       | |- _ -> mem_wr _ _ _ _ => exact Ww
       | |- forall i, _ -> _ => intros i _; apply Hfo
       | |- _ => first [ zreg | assumption | reflexivity | lia_std
                       | match goal with |- ?G => idtac "UWSIDE" G end ]
       end.
  -
    intros R' M' Wz. intros. zimps. zkeys.
    clear SAT STRM Hlens Hcodes HOB Hfo CST Cp60 Cp72 T1' T2' T3' T4' T5' T6' T7'.
    pose proof (ctx_ok_cxc u p q n gp tp s5 s6 s7 s8 s9 s10 s11 zc Hu0 Hzimg Hu1 Hua Hp0 Hp1 Hpa Hq1 Hn0 Hn1 Hqn Spq Spob Sobq Sprom
                  Rgp Rtp Rs5 Rs6 Rs7 Rs8 Rs9 Rs10 Rs11 0 cin0 cout0 W0 (ra_site site) (wok0 p q n zc Hzimg) Hcin0 Hcout0
                  ltac:(destruct site; [left | right]; reflexivity)) as CX0.
    pose proof CX0 as CXo. unfold cxc in CXo. dand CXo as (_ & _ & SEP).
    match goal with HP : mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M M' _ |- _ =>
      pose proof HP as HPw; zreattachL HP end.
    clear SEP.
    pose proof (mpostL_stable (run_segments R_segs rc_inp rc_sp rc_mb) M [(u + -1024, 1024); (u, 112); (p, 7176); (213360, 262144)] ltac:(ranges_ok_tac)) as HST.
    assert (HAG : framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M X [(u + -1024, 1024); (u, 112); (p, 7176); (213360, 262144)]) M').
    { eapply (framed_mpostL_trans _ _ _ _ _ _ (mpostL_refl (run_segments R_segs rc_inp rc_sp rc_mb) M _) HPw).
      intros x Hx; eapply ranges_within_outside; [| exact Hx]; ranges_within_tac. }
    clear HPw.
    pose proof FRM as FRM'. unfold i_frame in FRM'. icx_cbn.
    dand FRM' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Q136 & _ & _ & _ & _ & Q80 & _).
    rewrite Wz in *.
    zstep Rfd.
    zstep Rfd.
    zbr Rfd false.
    zstep Rfd. zlit.
    tstep1 Rfd.
    zstep Rfd.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?R9 ?Mx _) _ =>
      eapply (ret_t _ R9 [] Mx MD T (-4) CX0 Hh) end.
    + unfold s_regs_ret, cxc, Kra; icx_cbn; zkeys; cbn [Pos.eqb]; split_conj; zreg.
    + exact FRM.
    + intros R9 HB.
      lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mx _) _ =>
        eapply (u2_krx u p q n gp tp s5 s6 s7 s8 s9 s10 s11 fin MD T M zc Hh Hu0 Hzimg Hu1 Hua Hp0 Hp1 Hpa 0 (wok0 p q n zc Hzimg) HZE2 HZE1
                  site cin0 cout0 W0 M (mpostL_refl (run_segments R_segs rc_inp rc_sp rc_mb) M (fp_u2 u p 0)) R9 Mx (-4) 16210) end.
      * cbv. discriminate.
      * exact HB.
      * unfold s_std, i_cst, wsz, cxc; icx_cbn; cbn [Z.eqb]; cbv [BUF BUF_N]; split_conj; try assumption.
        all: first [ apply buf_writable | intros i Hi; exfalso; lia_std | match goal with |- ?G => idtac "STDSIDE" G end ].
      * unfold cxc; icx_cbn. assumption.
      * unfold reach; cbv [HEAD DICTID MEM]; lia_std.
      * unfold fp_call, fp_loop, wsz, cxc; icx_cbn; cbv [FRA ZS_OFF ZS_SIZE STATE_SIZE BUF]; cbn [Z.eqb app].
        eapply (framed_mpostL_trans _ _ _ _ _ _ (mpostL_refl (run_segments R_segs rc_inp rc_sp rc_mb) M _) HAG).
        intros x Hx; eapply ranges_within_outside; [| exact Hx]; ranges_within_tac.
  -
    intros R' M' whave' wnext' Wnz. intros. zimps. zkeys.
    specialize (Ww Wnz).
    pose proof SAT as SAT'. destruct SAT' as [Hmode SREST']. unfold st_rest, cxc in SREST'. icx_cbn. destr_conj SREST'. clear SAT.
    unfold cxc in Hmode; icx_cbn.
    clear Cp60 Cp72 CST HOB Hfo T1' T2' T3' T4' T5' T6' T7'.
    repeat match goal with
           | H : mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 76) _ |- _ => clear H
           | H : mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 80) _ |- _ => clear H
           end.
    pose proof (ctx_ok_cxc u p q n gp tp s5 s6 s7 s8 s9 s10 s11 zc Hu0 Hzimg Hu1 Hua Hp0 Hp1 Hpa Hq1 Hn0 Hn1 Hqn Spq Spob Sobq Sprom
                  Rgp Rtp Rs5 Rs6 Rs7 Rs8 Rs9 Rs10 Rs11 w cin0 cout0 W0 (ra_site site) Hw Hcin0 Hcout0
                  ltac:(destruct site; [left | right]; reflexivity)) as CX1.
    pose proof CX1 as CXo. unfold cxc in CXo. dand CXo as (_ & _ & SEP).
    lazymatch goal with HP : mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M M' ?rs |- _ =>
      pose proof HP as HPw; unfold uw_res_fp in HP; cbv [WIN_SIZE] in HP;
      lazymatch type of HP with mpostL _ _ _ ?rs' =>
        apply (mem_arr_magreeL (run_segments R_segs rc_inp rc_sp rc_mb) 1 M M' rs' q n fin (proj1 HP)) in Hin;
        [| pose proof Spq as D1; pose proof W5 as D2; unfold ZSEP in D1, D2; clear SEP;
           zconj_norm; repeat split; first [ exact I | lia_std ] ]
      end;
      zreattachL HP end.
    clear SEP.
    assert (HZW : KZW u p q n gp tp s5 s6 s7 s8 s9 s10 s11 fin MD T M zc w) by (unfold KZW; intros; exfalso; lia_std).
    assert (OBLOW1 : c_ob (cxc u p q n gp tp s5 s6 s7 s8 s9 s10 s11 zc w cin0 cout0 W0 (ra_site site))
                     + c_osz (cxc u p q n gp tp s5 s6 s7 s8 s9 s10 s11 zc w cin0 cout0 W0 (ra_site site))
                     <= c_u (cxc u p q n gp tp s5 s6 s7 s8 s9 s10 s11 zc w cin0 cout0 W0 (ra_site site)) - FRA).
    { unfold cxc; icx_cbn; cbv [BUF FRA]; lia_std. }
    pose proof (pcall_all u p q n gp tp s5 s6 s7 s8 s9 s10 s11 fin MD T M zc Hh Hfin Hu0 Hzimg Hu1 Hua Hp0 Hp1 Hpa Hq1 Hn0 Hn1 Hqn
                  Spq Spob Sobq Sprom Rgp Rtp Rs5 Rs6 Rs7 Rs8 Rs9 Rs10 Rs11 MEMCPY ADLER
                  A_HEAD A_DICTID A_DICT A_TYPE A_TYPEDO A_STORED A_COPY_ A_COPY A_TABLE A_LENLENS A_CODELENS
                  A_LEN_ A_LEN A_LENEXT A_DIST A_DISTEXT A_MATCH A_LIT A_CHECK A_LENGTH w Hw HZE2 HZE1 HZW) as PC.
    pose proof (u2_krl u p q n gp tp s5 s6 s7 s8 s9 s10 s11 fin MD T M zc Hh Hu0 Hzimg Hu1 Hua Hp0 Hp1 Hpa Hn1 Hqn Spq Spob Sobq w Hw HZE2 HZE1
                  _ (PC _) site cin0 cout0 W0 M Hcin0 Hcout0 (Z.le_refl _) (mpostL_refl (run_segments R_segs rc_inp rc_sp rc_mb) M (fp_u2 u p w))) as HKRL.
    pose proof (u2_krx u p q n gp tp s5 s6 s7 s8 s9 s10 s11 fin MD T M zc Hh Hu0 Hzimg Hu1 Hua Hp0 Hp1 Hpa w Hw HZE2 HZE1
                  site cin0 cout0 W0 M (mpostL_refl (run_segments R_segs rc_inp rc_sp rc_mb) M (fp_u2 u p w))) as HKRX.
    lazymatch goal with |- realizes _ (zcfg _ _ ?R9 ?Mx _) _ =>
      eapply (leave_uwret_t _ fin MD T M CX1 Hh OBLOW1 HKRL HKRX R9 [] Mx
                (set_win (IST mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) whave' wnext')
                rvu 0 lf cf) end.
    all: first [ eapply sinv_rewin; [exact SI | exact Wnz | assumption ..]
               | unfold cxc; icx_cbn; zreg
               | unfold set_win, cxc; icx_cbn; zreg
               | left; reflexivity
               | unfold s_std, i_cst, wsz, cxc; icx_cbn; rewrite (proj2 (Z.eqb_neq w 0) Wnz); cbv [BUF BUF_N WIN_SIZE]; split_conj;
                 first [ assumption | apply buf_writable | match goal with |- ?G => idtac "STDSIDE1" G end ]
               | unfold st_at, st_rest, set_win, cxc; icx_cbn; split_conj; assumption
               | unfold strm_at, set_win, cxc; icx_cbn; unfold strm_at, cxc in STRM; icx_cbn; exact STRM
               | unfold s_lo, set_win, cxc; icx_cbn; unfold s_lo, cxc in SLO; icx_cbn; exact SLO
               | unfold s_bk, set_win, cxc; icx_cbn; unfold s_bk, cxc in SBK; icx_cbn; exact SBK
               | assumption
               | unfold fp_call, fp_loop, wsz, cxc; icx_cbn; rewrite (proj2 (Z.eqb_neq w 0) Wnz); cbv [FRA ZS_OFF ZS_SIZE STATE_SIZE WIN_SIZE BUF]; cbn [app];
                 eapply (framed_mpostL_trans _ _ _ _ _ _ (mpostL_refl (run_segments R_segs rc_inp rc_sp rc_mb) M _) HPw);
                 intros x Hx; eapply ranges_within_outside; [| exact Hx]; unfold uw_res_fp; cbv [WIN_SIZE]; ranges_within_tac
               | match goal with |- ?G => idtac "LVSIDE" G end ].
Qed.
End ZB.
End T_ZB.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Frame Hoare AllocSim.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit Require Import U9LibStmt.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.IK Require Import MstepsGrows.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U Require Import TBase. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U Require T_Entry. Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U.T_Entry.T_Loop. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U Require T_U2C. Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U.T_U2C.T_Ret. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U Require Import T_Entry. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U Require T_U2C. Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U.T_U2Cw.T_Uw. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U Require T_U2C. Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U.T_U2C.T_LeaveA. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U Require T_U2C. Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U.T_U2C.T_Leave. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U Require T_U2C. Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U.T_U2C.T_Inflate. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U Require Import T_U2A. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U Require T_U2C. Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U.T_U2C.T_U2B. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U Require Import T_U2C. Import T_ZA. Import T_ZC. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U Require Import T_Tok. Import T_ZB.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

Lemma zl_get : forall regs (r : reg), bv_eqb r 0%bv = false ->
  zget_l (zlift regs) [] (bv_key r) = bv_unsigned (getr regs r).
Proof. intros regs r Hr. cbv [zget_l alookup]. rewrite zget_zlift, (getr_reg_get regs r Hr). reflexivity. Qed.

Lemma zl_get_lit : forall regs (r : reg) k z, bv_eqb r 0%bv = false -> bv_key r = k ->
  getr regs r = Z_to_bv 64 z -> 0 <= z < two64 -> zget_l (zlift regs) [] k = z.
Proof.
  intros regs r k z Hr <- H Hz. rewrite (zl_get regs r Hr), H.
  change (Z_to_bv 64 z) with (w64 z). rewrite w64_unsigned, mod_small_u64 by exact Hz. reflexivity.
Qed.

Lemma zd_get : forall R (r : reg) k v, bv_eqb r 0%bv = false -> bv_key r = k -> zget R k = v ->
  getr (zden R) r = w64 v.
Proof. intros R r k v Hr <- <-. apply getr_zkey. exact Hr. Qed.
Lemma zd_get_u : forall R (r : reg) k v, bv_eqb r 0%bv = false -> bv_key r = k -> zget R k = v -> 0 <= v < two64 ->
  bv_unsigned (getr (zden R) r) = v.
Proof. intros R r k v Hr Hk Hv Rv. rewrite (zd_get R r k v Hr Hk Hv), w64_unsigned. apply mod_small_u64. exact Rv. Qed.

Lemma mem_u64_modv {RCa1 : RunCtx}  : forall M a v, mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M a v -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M a (v mod two64).
Proof. intros M a v H. unfold mem_u64 in *. rewrite Z_to_le_bytes_mod by (cbn; lia_std). exact H. Qed.

Lemma hold_u64 : forall hold bits, 0 <= bits -> bits <= 40 -> 0 <= hold -> hold < 2 ^ bits -> 0 <= hold < two64.
Proof.
  intros hold bits B0 B1 H0 H1. pose proof (Z.pow_le_mono_r 2 bits 40 ltac:(lia_std) B1) as P.
  change (2 ^ 40) with 1099511627776 in P. rewrite two64_eq. split; [exact H0|]. change (2 ^ 64) with 18446744073709551616. lia_std.
Qed.

Lemma frame_mod_WA {RCa1 : RunCtx}  : forall mem mem' u p,
  0 <= u + -1024 -> u + 208 <= two64 -> 0 < p -> p + STATE_SIZE <= two64 ->
  mpostL (run_segments R_segs rc_inp rc_sp rc_mb) mem mem' (fp_u2 u p 0) -> mem_grows mem mem' -> frame_mod mem mem' (WA_U9 u p).
Proof.
  intros mem mem' u p Hu0 Hu1 Hp0 Hp1 HP HG. pose proof two64_eq as TW64.
  eapply frame_mod_weaken; [| eapply (frame_mod_of_mpostL (run_segments R_segs rc_inp rc_sp rc_mb) mem mem' (fp_u2 u p 0)); [| exact HP | exact HG]].
  - intros a Ho. unfold WA_U9 in Ho. cbn [outside wranges fp_u2 Z.eqb] in *.
    dand Ho as (O1 & O2 & O3 & O4 & O5 & _). repeat split; try assumption.
    unfold in_rng. lia_std.
  - unfold fp_u2. cbn [ranges_lt]. cbv [STATE_SIZE BUF] in *. lia_std.
Qed.
Lemma frame_mod_WAw {RCa1 : RunCtx}  : forall mem mem' u p (ww : word),
  0 <= u + -1024 -> u + 208 <= two64 -> 0 < p -> p + STATE_SIZE <= two64 -> bv_unsigned ww <> 0 -> bv_unsigned ww + WIN_SIZE <= two64 ->
  mpostL (run_segments R_segs rc_inp rc_sp rc_mb) mem mem' (fp_u2 u p (bv_unsigned ww)) -> mem_grows mem mem' -> frame_mod mem mem' (WA_U9 u p ++ [(ww, U9_WIN_N)]).
Proof.
  intros mem mem' u p ww Hu0 Hu1 Hp0 Hp1 Hw0 Hw1 HP HG. pose proof two64_eq as TW64. pose proof (u64_range ww) as Rw.
  eapply frame_mod_weaken; [| eapply (frame_mod_of_mpostL (run_segments R_segs rc_inp rc_sp rc_mb) mem mem' (fp_u2 u p (bv_unsigned ww))); [| exact HP | exact HG]].
  - intros a Ho. unfold WA_U9 in Ho. cbn [outside wranges fp_u2 app] in *.
    dand Ho as (O1 & O2 & O3 & O4 & O5 & O6 & _). rewrite (proj2 (Z.eqb_neq _ 0) Hw0).
    repeat split; try assumption. rewrite Z_to_bv_bv_unsigned. exact O6.
  - unfold fp_u2. cbn [ranges_lt]. cbv [STATE_SIZE BUF] in *. lia_std.
Qed.

Section CONTRACT.
Context {RCa1 : RunCtx}.
Hypothesis A_TABLE : arm_stmt L_TABLE TABLE.
Hypothesis A_LENLENS : arm_stmt L_LENLENS LENLENS.
Hypothesis A_CODELENS : arm_stmt L_CODELENS CODELENS.

Hypothesis A_HEAD : arm_stmt L_HEAD HEAD.
Hypothesis A_DICTID : arm_stmt L_DICTID DICTID.
Hypothesis A_DICT : arm_stmt L_DICT DICT.
Hypothesis A_TYPE : arm_stmt L_TYPE TYPE.
Hypothesis A_TYPEDO : arm_stmt L_TYPEDO TYPEDO.
Hypothesis A_STORED : arm_stmt L_STORED STORED.
Hypothesis A_COPY_ : arm_stmt L_COPY_ COPY_.
Hypothesis A_COPY : arm_stmt L_COPY COPY.
Hypothesis A_LEN_ : arm_stmt L_LEN_ LEN_.
Hypothesis A_LEN : arm_stmt L_LEN LEN.
Hypothesis A_LENEXT : arm_stmt L_LENEXT LENEXT.
Hypothesis A_DIST : arm_stmt L_DIST DIST.
Hypothesis A_DISTEXT : arm_stmt L_DISTEXT DISTEXT.
Hypothesis A_MATCH : arm_stmt L_MATCH MATCH.
Hypothesis A_LIT : arm_stmt L_LIT LIT.
Hypothesis A_CHECK : arm_stmt_ob L_CHECK CHECK.
Hypothesis A_LENGTH : arm_stmt L_LENGTH LENGTH.

Local Ltac open_layout LAY := let Hu0 := ident:(Hu0) in let Hu1 := ident:(Hu1) in let Hzimg := ident:(Hzimg) in let Hp1 := ident:(Hp1) in let Spob := ident:(Spob) in let Hqn := ident:(Hqn) in let Sobq := ident:(Sobq) in let Spq := ident:(Spq) in let ROMH := ident:(ROMH) in let STK := ident:(STK) in let STP := ident:(STP) in let Sprom := ident:(Sprom) in let Sqrom := ident:(Sqrom) in (dand LAY as (Hua & Hu0 & Hu1 & Hzimg & Hpa & Hp0 & Hp1 & Spob & Hn & Hq1 & Hqn & Sobq & Spq & RD & ROMH & STK & STP & Sprom & Sqrom);
  cbv [U9_FRA U9_INFL_N U9_BUF U9_BUF_N U9_RO_LO U9_RO_HI U9_IMG_TOP] in Hu0, Hu1, Hzimg, Hp1, Spob, Hqn, Sobq, Spq, ROMH, STK, STP, Sprom, Sqrom).

Theorem za_s : za_stmt_U9 zwtok_U9.
Proof.
  unfold za_stmt_U9. intros regs mem u pw qw n zc Hsp Hs2 Hs1 Ha0 Hs3 Hs4 LAY F32 F24 F16 F8 S8 S16 S72 S80 S88.
  set (p := bv_unsigned pw) in *. set (q := bv_unsigned qw) in *.
  assert (Ep : bv_unsigned pw = p) by reflexivity. assert (Eq : bv_unsigned qw = q) by reflexivity. clearbody p q.
  pose proof (u64_range pw) as Rp. pose proof (u64_range qw) as Rq. rewrite Ep in Rp. rewrite Eq in Rq.
  open_layout LAY. pose proof two64_eq as TW64.
  set (Rb := zlift regs).
  assert (Lsp : zget_l Rb [] kSP = u + -32).
  { subst Rb. rewrite (zl_get_lit regs 2%bv kSP (u - 32) eq_refl eq_refl Hsp); lia_std. }
  assert (Ls2 : zget_l Rb [] kS2 = u).
  { subst Rb. apply (zl_get_lit regs 18%bv kS2 (u) eq_refl eq_refl Hs2). lia_std. }
  assert (Ls1 : zget_l Rb [] kS1 = 7176).
  { subst Rb. apply (zl_get_lit regs 9%bv kS1 7176 eq_refl eq_refl Hs1). lia_std. }
  assert (La0 : zget_l Rb [] kA0 = p).
  { subst Rb. change kA0 with (bv_key (10%bv : reg)). rewrite (zl_get regs 10%bv eq_refl), Ha0. exact Ep. }
  assert (Ls3 : zget_l Rb [] kS3 = n).
  { subst Rb. apply (zl_get_lit regs 19%bv kS3 n eq_refl eq_refl Hs3). lia_std. }
  assert (Ls4 : zget_l Rb [] kS4 = 262144).
  { subst Rb. apply (zl_get_lit regs 20%bv kS4 262144 eq_refl eq_refl Hs4). lia_std. }
  set (gp := zget_l Rb [] kGP). set (tp := zget_l Rb [] kTP).
  set (s5 := zget_l Rb [] kS5). set (s6 := zget_l Rb [] kS6). set (s7 := zget_l Rb [] kS7). set (s8 := zget_l Rb [] kS8).
  set (s9 := zget_l Rb [] kS9). set (s10 := zget_l Rb [] kS10). set (s11 := zget_l Rb [] kS11).
  assert (RRG : forall (r : reg), bv_eqb r 0%bv = false -> 0 <= zget_l Rb [] (bv_key r) < two64).
  { intros r Hr. subst Rb. rewrite (zl_get regs r Hr). rewrite two64_eq. apply u64_range. }
  pose proof (RRG 3%bv eq_refl : 0 <= gp < two64) as Rgp. pose proof (RRG 4%bv eq_refl : 0 <= tp < two64) as Rtp.
  pose proof (RRG 21%bv eq_refl : 0 <= s5 < two64) as Rs5. pose proof (RRG 22%bv eq_refl : 0 <= s6 < two64) as Rs6. pose proof (RRG 23%bv eq_refl : 0 <= s7 < two64) as Rs7.
  pose proof (RRG 24%bv eq_refl : 0 <= s8 < two64) as Rs8. pose proof (RRG 25%bv eq_refl : 0 <= s9 < two64) as Rs9.
  pose proof (RRG 26%bv eq_refl : 0 <= s10 < two64) as Rs10. pose proof (RRG 27%bv eq_refl : 0 <= s11 < two64) as Rs11.
  clear RRG.
  pose proof (mem_wr_of_store_ok _ _ _ _ STK) as Wstk. rewrite Z2Nat.id in Wstk by lia_std.
  change (mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) mem (u - 1024) 1232) in Wstk. replace (u - 1024) with (u + -1024) in Wstk by lia_std.
  pose proof (mem_wr_of_store_ok _ _ _ _ STP) as Wp. rewrite Z2Nat.id in Wp by lia_std.
  change (mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) mem p 7176) in Wp.
  pose proof (rom_ok_of_hyp mem ROMH) as ROM.
  destruct (mem_arr_of_readable (run_segments R_segs rc_inp rc_sp rc_mb) mem q n ltac:(lia_std) ltac:(lia_std) ltac:(lia_std) RD) as (fin & Hin & Hfin).
  set (Q := fun c : config => exists (R : tree Z) (M' : word -> option byte),
    (c = zcfg (run_segments R_segs rc_inp rc_sp rc_mb) T_ZE2 (zupd R []) M' MD0 /\
     zget R kA3 = A_ZCFREE /\ zget R kA1 = p /\ zget R kA0 = 0 /\ zget R kS0 = u /\ zget R kSP = u + -16 /\
     zget R kGP = gp /\ zget R kTP = tp /\
     zget R kS5 = s5 /\ zget R kS6 = s6 /\ zget R kS7 = s7 /\ zget R kS8 = s8 /\ zget R kS9 = s9 /\ zget R kS10 = s10 /\ zget R kS11 = s11 /\
     mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (u + -8) RA2 /\ mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (u + 56) p /\ mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (u + 72) A_ZCFREE /\ mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (u + 80) 0 /\
     mpostL (run_segments R_segs rc_inp rc_sp rc_mb) mem M' (fp_u2 u p 0))
    \/
    (c = zcfg (run_segments R_segs rc_inp rc_sp rc_mb) T_ZW (zupd R []) M' MD0 /\
     zget R kA3 = A_ZCALLOC /\ zget R kA0 = 0 /\ zget R kA1 = WIN_SIZE /\ zget R kA2 = 1 /\ zget R kSP = u + -320 /\
     zget R kGP = gp /\ zget R kTP = tp /\
     zwtok_U9 u p q n zc (sregs regs S_ENTRY5) (sregs (zden R) S_ALL) M' /\
     mpostL (run_segments R_segs rc_inp rc_sp rc_mb) mem M' (fp_u2 u p 0))).
  assert (HR : realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_ZA (zupd Rb []) mem MD0) Q).
  { eapply (za_cps u p q n gp tp s5 s6 s7 s8 s9 s10 s11 fin MD0 Q zc MD0_halted Hfin);
      try first [ exact Lsp | exact Ls2 | exact Ls1 | exact La0 | exact Ls3 | exact Ls4 | reflexivity | assumption
                | exact memcpy_ok_t | exact adler32_ok_t
                | exact F32 | exact F24 | exact F16 | exact F8 | rewrite <- Eq; exact S8 | exact S16 | exact S72 | exact S80 | exact S88
                | unfold ZSEP; cbv [STATE_SIZE ROM_LO_ALL ROMHI_T BUF]; lia_std
                | cbv [FRA STATE_SIZE DATA_LO DATA_LEN]; lia_std ].
    -
      intros R M'. intros. apply rz_now. subst Q. cbv beta. exists R, M'. left.
      repeat (split; [first [reflexivity | assumption] |]). assumption.
    -
      intros R M' cin0 cout0 W0 ra st rv v4 v5 lf cf. cbv zeta. intros Hra Hcin0 Hcout0 SI Hcc Hmd.
      intros GA3 GA0 GA1 GA2 GS0 GS1 GS2 GS3 GS4 GS5 GSP GGP GTP GS6 GS7 GS9 GS10 GS11 U264 U272 U280 U288 U296 U304 U312 STD SAT STRM SLO SBK Hlens Hcodes Hw0 HP.
      apply rz_now. subst Q. cbv beta. exists R, M'. right.
      split; [reflexivity|]. do 7 (split; [assumption|]). split; [| exact HP].
      pose proof SI as SI'. dand SI' as (RNG_ & _ & _ & _). unfold RNG, cxc in RNG_. icx_cbn.
      destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
      icx_cbn. destr_conj RNG_.
      cbv [BUF] in GS0.
      pose proof (hold_u64 hold bits ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)) as Rhold.
      exists s5, s6, s7, s8, s9, s10, s11, cin0, cout0, W0, ra,
             (bv_unsigned (getr (zden R) 21)), (bv_unsigned (getr (zden R) 22)), (bv_unsigned (getr (zden R) 24)),
             (bv_unsigned (getr (zden R) 27)),
             (IST mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext), lf, cf.
      split; [| split; [| split]].
      + subst s5 s6 s7 s8 s9 s10 s11 Rb. unfold sregs, S_ENTRY5, S_ENTRY. cbn [map app].
        rewrite <- (zl_get regs 21%bv eq_refl), <- (zl_get regs 22%bv eq_refl), <- (zl_get regs 23%bv eq_refl), <- (zl_get regs 24%bv eq_refl),
                <- (zl_get regs 25%bv eq_refl), <- (zl_get regs 26%bv eq_refl), <- (zl_get regs 27%bv eq_refl).
        reflexivity.
      + unfold sregs, S_ALL, tok_regs. cbn [map]. icx_cbn. cbv [BUF STATE_SIZE] in *.
        rewrite (zd_get_u R 8 kS0 _ eq_refl eq_refl GS0) by lia_std.
        rewrite (zd_get_u R 9 kS1 _ eq_refl eq_refl GS1) by lia_std.
        rewrite (zd_get_u R 18 kS2 _ eq_refl eq_refl GS2) by lia_std.
        rewrite (zd_get_u R 19 kS3 _ eq_refl eq_refl GS3) by lia_std.
        rewrite (zd_get_u R 20 kS4 _ eq_refl eq_refl GS4) by lia_std.
        rewrite (zd_get_u R 23 kS7 _ eq_refl eq_refl GS7) by lia_std.
        rewrite (zd_get_u R 25 kS9 _ eq_refl eq_refl GS9) by exact Rhold.
        rewrite (zd_get_u R 26 kS10 _ eq_refl eq_refl GS10) by lia_std.
        reflexivity.
      + unfold tok_pure. pose proof (u64_range (getr (zden R) 21)). pose proof (u64_range (getr (zden R) 22)).
        pose proof (u64_range (getr (zden R) 24)). pose proof (u64_range (getr (zden R) 27)).
        rewrite <- TW64 in *.
        split_conj; try assumption; try (icx_cbn; assumption); try (cbv [FRA STATE_SIZE]; lia_std).
      + unfold tok_mem, cxw. icx_cbn. clear ROM Wstk Wp Hin. open_std STD. split_conj; try assumption.
        all: first [ exact FRM | exact CST | exact HK | exact SAT | exact STRM | exact SLO | exact SBK
                   | rewrite (zd_get R 20%bv kS4 _ eq_refl eq_refl GS4), w64_unsigned; apply mem_u64_modv; exact U304
                   | rewrite (zd_get R 21%bv kS5 _ eq_refl eq_refl GS5), w64_unsigned; apply mem_u64_modv; exact U312
                   | match goal with |- ?G => idtac "TOKSIDE" G end ]. }
  dand HR as (ms' & RUN & HQ). subst Q. cbv beta in HQ. cbn [cfg_ms cfg_model zcfg] in RUN, HQ.
  unfold zst in RUN. cbn [zupd] in RUN. subst Rb. rewrite zden_zlift in RUN.
  pose proof (msteps_mem_grows (run_segments R_segs rc_inp rc_sp rc_mb) _ _ RUN) as G. cbn [ms_mem] in G.
  assert (KEPT : forall (R : tree Z) (r : reg) k, bv_eqb r 0%bv = false -> bv_key r = k ->
            zget R k = zget_l (zlift regs) [] k -> getr (zden R) r = getr regs r).
  { intros R r k Hr Hk Hv. rewrite (zd_get R r k _ Hr Hk Hv), <- Hk, (zl_get regs r Hr). apply w64_of_word. }
  assert (SE : forall R : tree Z, zget R kS5 = s5 -> zget R kS6 = s6 -> zget R kS7 = s7 -> zget R kS8 = s8 -> zget R kS9 = s9 ->
            zget R kS10 = s10 -> zget R kS11 = s11 -> sregs (zden R) S_ENTRY5 = sregs regs S_ENTRY5).
  { intros R E5 E6 E7 E8 E9 E10 E11. unfold sregs, S_ENTRY5, S_ENTRY. cbn [map app].
    rewrite (KEPT R 21%bv kS5 eq_refl eq_refl E5), (KEPT R 22%bv kS6 eq_refl eq_refl E6), (KEPT R 23%bv kS7 eq_refl eq_refl E7), (KEPT R 24%bv kS8 eq_refl eq_refl E8),
            (KEPT R 25%bv kS9 eq_refl eq_refl E9), (KEPT R 26%bv kS10 eq_refl eq_refl E10), (KEPT R 27%bv kS11 eq_refl eq_refl E11).
    reflexivity. }
  destruct HQ as (R & M' & [(E & GA4 & GA1 & GA0 & GS0 & GSP & GGP & GTP & G5 & G6 & G7 & G8 & G9 & G10 & G11 & C8 & C64 & C80 & C88 & HP)
                           |(E & GA3 & GA0 & GA1 & GA2 & GSP & GGP & GTP & TOK & HP)]);
    unfold zcfg, zst in E; injection E as E1; subst ms'; cbn [ms_mem] in G; cbn [zupd].
  - exists (zden R), M', T_ZE2. split; [exact RUN | split].
    + apply frame_mod_WA; try assumption; cbv [STATE_SIZE]; lia_std.
    + left. split; [reflexivity | split].
      * unfold end_regs_U9. split_conj.
        -- exact (zd_get R 13%bv kA3 _ eq_refl eq_refl GA4).
        -- exact (zd_get R 11%bv kA1 _ eq_refl eq_refl GA1).
        -- exact (zd_get R 10%bv kA0 _ eq_refl eq_refl GA0).
        -- exact (zd_get R 8%bv kS0 _ eq_refl eq_refl GS0).
        -- exact (zd_get R 2%bv kSP _ eq_refl eq_refl GSP).
        -- exact (KEPT R 3%bv kGP eq_refl eq_refl GGP).
        -- exact (KEPT R 4%bv kTP eq_refl eq_refl GTP).
        -- apply SE; assumption.
      * unfold end_cells_U9. split_conj; [exact C8 | exact C64 | exact C80 | exact C88].
  - exists (zden R), M', T_ZW. split; [exact RUN | split].
    + apply frame_mod_WA; try assumption; cbv [STATE_SIZE]; lia_std.
    + right. split; [reflexivity |]. split_conj.
      * exact (zd_get R 13%bv kA3 _ eq_refl eq_refl GA3).
      * exact (zd_get R 10%bv kA0 _ eq_refl eq_refl GA0).
      * exact (zd_get R 11%bv kA1 _ eq_refl eq_refl GA1).
      * exact (zd_get R 12%bv kA2 _ eq_refl eq_refl GA2).
      * exact (zd_get R 2%bv kSP _ eq_refl eq_refl GSP).
      * exact (KEPT R 3%bv kGP eq_refl eq_refl GGP).
      * exact (KEPT R 4%bv kTP eq_refl eq_refl GTP).
      * exact TOK.
Qed.

Lemma sregs_S_ALL : forall regs l,
  sregs regs S_ALL = l ->
  l = [bv_unsigned (getr regs 8); bv_unsigned (getr regs 9); bv_unsigned (getr regs 18); bv_unsigned (getr regs 19);
       bv_unsigned (getr regs 20); bv_unsigned (getr regs 21); bv_unsigned (getr regs 22); bv_unsigned (getr regs 23);
       bv_unsigned (getr regs 24); bv_unsigned (getr regs 25); bv_unsigned (getr regs 26); bv_unsigned (getr regs 27)].
Proof. intros regs l <-. reflexivity. Qed.

Local Ltac open_token TOK := let PURE := ident:(PURE) in (dand TOK as (s5 & s6 & s7 & s8 & s9 & s10 & s11 & cin0 & cout0 & W0 & ra & s4u & s5u & s7u & rvu & st & lf & cf & EsE & EsW & PURE & TM);
  unfold tok_pure in PURE;
  dand PURE as (Hra & Hcin0 & Hcout0 & Rs5 & Rs6 & Rs7 & Rs8 & Rs9 & Rs10 & Rs11 & Rs4u & Rs5u & Rs7u & Rrvu & SI & Hcc & Hmd & Lu0 & Lu1 & Lp0 & Lp1)).

Theorem zb_s : zb_stmt_U9 zwtok_U9.
Proof.
  unfold zb_stmt_U9. intros regs mem u pw qw ww n zc sE sW Hsp Ha0 HsW TOK LAY Hwa Hw0 Hw1 Swb Swp Swq Swi STW.
  set (p := bv_unsigned pw) in *. set (q := bv_unsigned qw) in *. set (w := bv_unsigned ww) in *.
  assert (Ep : bv_unsigned pw = p) by reflexivity. assert (Eq : bv_unsigned qw = q) by reflexivity. assert (Ew : bv_unsigned ww = w) by reflexivity.
  clearbody p q w.
  pose proof (u64_range pw) as Rp. pose proof (u64_range qw) as Rq. pose proof (u64_range ww) as Rw.
  rewrite Ep in Rp. rewrite Eq in Rq. rewrite Ew in Rw.
  open_layout LAY. cbv [U9_WIN_N U9_BUF U9_BUF_N U9_INFL_N U9_IMG_TOP] in Hw1, Swb, Swp, Swq, Swi, STW. pose proof two64_eq as TW64.
  open_token TOK.
  pose proof (sregs_S_ALL regs sW HsW) as EW. rewrite EsW in EW. unfold tok_regs in EW.
  injection EW as W0_ W1_ W2_ W3_ W4_ W5_ W6_ W7_ W8_ W9_ W10_ W11_.
  set (Rb := zlift regs).
  assert (Lsp : zget_l Rb [] kSP = u + -320).
  { subst Rb. rewrite (zl_get_lit regs 2%bv kSP (u - 320) eq_refl eq_refl Hsp); lia_std. }
  assert (La0 : zget_l Rb [] kA0 = w).
  { subst Rb. change kA0 with (bv_key (10%bv : reg)). rewrite (zl_get regs 10%bv eq_refl), Ha0. exact Ew. }
  assert (GL : forall (r : reg) k v, bv_eqb r 0%bv = false -> bv_key r = k -> bv_unsigned (getr regs r) = v -> zget_l Rb [] k = v).
  { intros r k v Hr <- Hv. subst Rb. rewrite (zl_get regs r Hr). exact Hv. }
  pose proof (GL 8%bv kS0 _ eq_refl eq_refl (eq_sym W0_)) as Ls0.
  pose proof (GL 9%bv kS1 _ eq_refl eq_refl (eq_sym W1_)) as Ls1.
  pose proof (GL 18%bv kS2 _ eq_refl eq_refl (eq_sym W2_)) as Ls2.
  pose proof (GL 19%bv kS3 _ eq_refl eq_refl (eq_sym W3_)) as Ls3.
  pose proof (GL 20%bv kS4 _ eq_refl eq_refl (eq_sym W4_)) as Ls4.
  pose proof (GL 21%bv kS5 _ eq_refl eq_refl (eq_sym W5_)) as Ls5.
  pose proof (GL 22%bv kS6 _ eq_refl eq_refl (eq_sym W6_)) as Ls6.
  pose proof (GL 23%bv kS7 _ eq_refl eq_refl (eq_sym W7_)) as Ls7.
  pose proof (GL 25%bv kS9 _ eq_refl eq_refl (eq_sym W9_)) as Ls9.
  pose proof (GL 26%bv kS10 _ eq_refl eq_refl (eq_sym W10_)) as Ls10.
  pose proof (GL 27%bv kS11 _ eq_refl eq_refl (eq_sym W11_)) as Ls11.
  set (gp := zget_l Rb [] kGP). set (tp := zget_l Rb [] kTP).
  assert (RRG : forall (r : reg), bv_eqb r 0%bv = false -> 0 <= zget_l Rb [] (bv_key r) < two64).
  { intros r Hr. subst Rb. rewrite (zl_get regs r Hr). rewrite two64_eq. apply u64_range. }
  pose proof (RRG 3%bv eq_refl : 0 <= gp < two64) as Rgp. pose proof (RRG 4%bv eq_refl : 0 <= tp < two64) as Rtp. clear RRG.
  pose proof (mem_wr_of_store_ok _ _ _ _ STK) as Wstk. rewrite Z2Nat.id in Wstk by lia_std.
  change (mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) mem (u - 1024) 1232) in Wstk. replace (u - 1024) with (u + -1024) in Wstk by lia_std.
  pose proof (mem_wr_of_store_ok _ _ _ _ STP) as Wp. rewrite Z2Nat.id in Wp by lia_std.
  change (mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) mem p 7176) in Wp.
  rewrite <- (Z_to_bv_bv_unsigned 64 ww), Ew in STW.
  pose proof (mem_wr_of_store_ok _ _ _ _ STW) as Ww. rewrite Z2Nat.id in Ww by lia_std.
  change (mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) mem w 32768) in Ww.
  pose proof (rom_ok_of_hyp mem ROMH) as ROM.
  destruct (mem_arr_of_readable (run_segments R_segs rc_inp rc_sp rc_mb) mem q n ltac:(lia_std) ltac:(lia_std) ltac:(lia_std) RD) as (fin & Hin & Hfin).
  assert (Hwok : wok p q n zc w).
  { unfold wok, ZSEP. cbv [WIN_SIZE STATE_SIZE BUF ROM_LO_ALL ROMHI_T]. split_conj; try lia_std. }
  assert (Hsite : exists site : bool, ra = ra_site site).
  { destruct Hra as [-> | ->]; [exists true | exists false]; reflexivity. }
  dand Hsite as (site & Esite). subst ra.
  assert (Ku0 : zc + FRA <= u) by (cbv [FRA]; lia_std).
  assert (Kzimg : DATA_LO + DATA_LEN <= zc) by (cbv [DATA_LO DATA_LEN]; lia_std).
  assert (Ku1 : u + 208 <= 140737488355328) by lia_std.
  assert (Kp1 : p + STATE_SIZE <= zc) by (cbv [STATE_SIZE]; lia_std).
  assert (Kn0 : 0 <= n) by lia_std. assert (Kn1 : n < 67108864) by lia_std.
  assert (Kqn : q + n <= zc) by lia_std.
  assert (Kpq : ZSEP (p + STATE_SIZE <= q \/ q + n <= p)) by (unfold ZSEP; cbv [STATE_SIZE]; lia_std).
  assert (Kpob : ZSEP (p + STATE_SIZE <= BUF \/ BUF + 262144 <= p)) by (unfold ZSEP; cbv [STATE_SIZE BUF]; lia_std).
  assert (Kobq : ZSEP (BUF + 262144 <= q \/ q + n <= BUF)) by (unfold ZSEP; cbv [BUF]; lia_std).
  assert (Kprom : ZSEP (p + STATE_SIZE <= ROM_LO_ALL \/ ROMHI_T <= p)) by (unfold ZSEP; cbv [STATE_SIZE ROM_LO_ALL ROMHI_T]; lia_std).
  set (Q := fun c : config => exists (R : tree Z) (M' : word -> option byte),
    c = zcfg (run_segments R_segs rc_inp rc_sp rc_mb) T_ZE1 (zupd R []) M' MD0 /\
    zget R kA3 = A_ZCFREE /\ zget R kA1 = w /\ zget R kA0 = 0 /\ zget R kS0 = u /\ zget R kSP = u + -16 /\
    zget R kGP = gp /\ zget R kTP = tp /\
    zget R kS5 = s5 /\ zget R kS6 = s6 /\ zget R kS7 = s7 /\ zget R kS8 = s8 /\ zget R kS9 = s9 /\ zget R kS10 = s10 /\ zget R kS11 = s11 /\
    mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (u + -8) RA2 /\ mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (u + 56) p /\ mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (u + 72) A_ZCFREE /\ mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (u + 80) 0 /\
    mpostL (run_segments R_segs rc_inp rc_sp rc_mb) mem M' (fp_u2 u p w)).
  assert (HR : realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_ZB (zupd Rb []) mem MD0) Q).
  { eapply (zb_cps u p q n gp tp s5 s6 s7 s8 s9 s10 s11 fin MD0 Q zc MD0_halted Hfin
              Ku0 Kzimg Ku1 Hua Hp0 Kp1 Hpa Hq1 Kn0 Kn1 Kqn Kpq Kpob Kobq Kprom Rgp Rtp Rs5 Rs6 Rs7 Rs8 Rs9 Rs10 Rs11 memcpy_ok_t adler32_ok_t
              A_HEAD A_DICTID A_DICT A_TYPE A_TYPEDO A_STORED A_COPY_ A_COPY A_TABLE A_LENLENS A_CODELENS
              A_LEN_ A_LEN A_LENEXT A_DIST A_DISTEXT A_MATCH A_LIT A_CHECK A_LENGTH
              w Hwok site cin0 cout0 W0 s4u s5u rvu st lf cf Hcin0 Hcout0 SI Hcc Rb [] mem
              Lsp La0 Ls0 Ls1 Ls2 Ls3 Ls5 Ls6 Ls9 Ls7 Ls10 Ls11 Ls4 eq_refl eq_refl ROM Wstk Wp ltac:(intros _; exact Ww) Hin TM).
    -
      intros R M'. intros. exfalso. lia_std.
    -
      intros R M'. intros. apply rz_now. subst Q. cbv beta. exists R, M'.
      repeat (split; [first [reflexivity | assumption] |]). assumption. }
  dand HR as (ms' & RUN & HQ). subst Q. cbv beta in HQ. cbn [cfg_ms cfg_model zcfg] in RUN, HQ.
  unfold zst in RUN. cbn [zupd] in RUN. subst Rb. rewrite zden_zlift in RUN.
  pose proof (msteps_mem_grows (run_segments R_segs rc_inp rc_sp rc_mb) _ _ RUN) as G. cbn [ms_mem] in G.
  dand HQ as (R & M' & E & GA4 & GA1 & GA0 & GS0 & GSP & GGP & GTP & G5 & G6 & G7 & G8 & G9 & G10 & G11 & C8 & C64 & C80 & C88 & HP).
  unfold zcfg, zst in E; injection E as E1; subst ms'; cbn [ms_mem] in G; cbn [zupd].
  exists (zden R), M'. split; [exact RUN | split; [| split]].
  - apply frame_mod_WAw; rewrite ?Ew; try assumption; cbv [STATE_SIZE WIN_SIZE]; first [lia | lia_std].
  - unfold end_regs_U9. split_conj.
    + exact (zd_get R 13%bv kA3 _ eq_refl eq_refl GA4).
    + exact (zd_get R 11%bv kA1 _ eq_refl eq_refl GA1).
    + exact (zd_get R 10%bv kA0 _ eq_refl eq_refl GA0).
    + exact (zd_get R 8%bv kS0 _ eq_refl eq_refl GS0).
    + exact (zd_get R 2%bv kSP _ eq_refl eq_refl GSP).
    + rewrite (zd_get R 3%bv kGP _ eq_refl eq_refl GGP). subst gp. rewrite (zl_get regs 3%bv eq_refl). apply w64_of_word.
    + rewrite (zd_get R 4%bv kTP _ eq_refl eq_refl GTP). subst tp. rewrite (zl_get regs 4%bv eq_refl). apply w64_of_word.
    + rewrite EsE. unfold sregs, S_ENTRY5, S_ENTRY. cbn [map app]. rewrite (zd_get_u R 21 kS5 _ eq_refl eq_refl G5) by exact Rs5.
      rewrite (zd_get_u R 22 kS6 _ eq_refl eq_refl G6) by exact Rs6. rewrite (zd_get_u R 23 kS7 _ eq_refl eq_refl G7) by exact Rs7.
      rewrite (zd_get_u R 24 kS8 _ eq_refl eq_refl G8) by exact Rs8. rewrite (zd_get_u R 25 kS9 _ eq_refl eq_refl G9) by exact Rs9.
      rewrite (zd_get_u R 26 kS10 _ eq_refl eq_refl G10) by exact Rs10. rewrite (zd_get_u R 27 kS11 _ eq_refl eq_refl G11) by exact Rs11.
      reflexivity.
  - unfold end_cells_U9. split_conj; [exact C8 | exact C64 | exact C80 | exact C88].
Qed.

Theorem zb0_s : zb0_stmt_U9 zwtok_U9.
Proof.
  unfold zb0_stmt_U9. intros regs mem u pw qw n zc sE sW Hsp Ha0 HsW TOK LAY.
  set (p := bv_unsigned pw) in *. set (q := bv_unsigned qw) in *.
  assert (Ep : bv_unsigned pw = p) by reflexivity. assert (Eq : bv_unsigned qw = q) by reflexivity.
  clearbody p q.
  pose proof (u64_range pw) as Rp. pose proof (u64_range qw) as Rq. rewrite Ep in Rp. rewrite Eq in Rq.
  open_layout LAY. pose proof two64_eq as TW64.
  open_token TOK.
  pose proof (sregs_S_ALL regs sW HsW) as EW. rewrite EsW in EW. unfold tok_regs in EW.
  injection EW as W0_ W1_ W2_ W3_ W4_ W5_ W6_ W7_ W8_ W9_ W10_ W11_.
  set (Rb := zlift regs).
  assert (Lsp : zget_l Rb [] kSP = u + -320).
  { subst Rb. rewrite (zl_get_lit regs 2%bv kSP (u - 320) eq_refl eq_refl Hsp); lia_std. }
  assert (La0 : zget_l Rb [] kA0 = 0).
  { subst Rb. apply (zl_get_lit regs 10%bv kA0 0 eq_refl eq_refl Ha0). lia_std. }
  assert (GL : forall (r : reg) k v, bv_eqb r 0%bv = false -> bv_key r = k -> bv_unsigned (getr regs r) = v -> zget_l Rb [] k = v).
  { intros r k v Hr <- Hv. subst Rb. rewrite (zl_get regs r Hr). exact Hv. }
  pose proof (GL 8%bv kS0 _ eq_refl eq_refl (eq_sym W0_)) as Ls0.
  pose proof (GL 9%bv kS1 _ eq_refl eq_refl (eq_sym W1_)) as Ls1.
  pose proof (GL 18%bv kS2 _ eq_refl eq_refl (eq_sym W2_)) as Ls2.
  pose proof (GL 19%bv kS3 _ eq_refl eq_refl (eq_sym W3_)) as Ls3.
  pose proof (GL 20%bv kS4 _ eq_refl eq_refl (eq_sym W4_)) as Ls4.
  pose proof (GL 21%bv kS5 _ eq_refl eq_refl (eq_sym W5_)) as Ls5.
  pose proof (GL 22%bv kS6 _ eq_refl eq_refl (eq_sym W6_)) as Ls6.
  pose proof (GL 23%bv kS7 _ eq_refl eq_refl (eq_sym W7_)) as Ls7.
  pose proof (GL 25%bv kS9 _ eq_refl eq_refl (eq_sym W9_)) as Ls9.
  pose proof (GL 26%bv kS10 _ eq_refl eq_refl (eq_sym W10_)) as Ls10.
  pose proof (GL 27%bv kS11 _ eq_refl eq_refl (eq_sym W11_)) as Ls11.
  set (gp := zget_l Rb [] kGP). set (tp := zget_l Rb [] kTP).
  assert (RRG : forall (r : reg), bv_eqb r 0%bv = false -> 0 <= zget_l Rb [] (bv_key r) < two64).
  { intros r Hr. subst Rb. rewrite (zl_get regs r Hr). rewrite two64_eq. apply u64_range. }
  pose proof (RRG 3%bv eq_refl : 0 <= gp < two64) as Rgp. pose proof (RRG 4%bv eq_refl : 0 <= tp < two64) as Rtp. clear RRG.
  pose proof (mem_wr_of_store_ok _ _ _ _ STK) as Wstk. rewrite Z2Nat.id in Wstk by lia_std.
  change (mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) mem (u - 1024) 1232) in Wstk. replace (u - 1024) with (u + -1024) in Wstk by lia_std.
  pose proof (mem_wr_of_store_ok _ _ _ _ STP) as Wp. rewrite Z2Nat.id in Wp by lia_std.
  change (mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) mem p 7176) in Wp.
  pose proof (rom_ok_of_hyp mem ROMH) as ROM.
  destruct (mem_arr_of_readable (run_segments R_segs rc_inp rc_sp rc_mb) mem q n ltac:(lia_std) ltac:(lia_std) ltac:(lia_std) RD) as (fin & Hin & Hfin).
  assert (Hsite : exists site : bool, ra = ra_site site).
  { destruct Hra as [-> | ->]; [exists true | exists false]; reflexivity. }
  dand Hsite as (site & Esite). subst ra.
  assert (Ku0 : zc + FRA <= u) by (cbv [FRA]; lia_std).
  assert (Kzimg : DATA_LO + DATA_LEN <= zc) by (cbv [DATA_LO DATA_LEN]; lia_std).
  assert (Ku1 : u + 208 <= 140737488355328) by lia_std.
  assert (Kp1 : p + STATE_SIZE <= zc) by (cbv [STATE_SIZE]; lia_std).
  assert (Kn0 : 0 <= n) by lia_std. assert (Kn1 : n < 67108864) by lia_std.
  assert (Kqn : q + n <= zc) by lia_std.
  assert (Kpq : ZSEP (p + STATE_SIZE <= q \/ q + n <= p)) by (unfold ZSEP; cbv [STATE_SIZE]; lia_std).
  assert (Kpob : ZSEP (p + STATE_SIZE <= BUF \/ BUF + 262144 <= p)) by (unfold ZSEP; cbv [STATE_SIZE BUF]; lia_std).
  assert (Kobq : ZSEP (BUF + 262144 <= q \/ q + n <= BUF)) by (unfold ZSEP; cbv [BUF]; lia_std).
  assert (Kprom : ZSEP (p + STATE_SIZE <= ROM_LO_ALL \/ ROMHI_T <= p)) by (unfold ZSEP; cbv [STATE_SIZE ROM_LO_ALL ROMHI_T]; lia_std).
  set (Q := fun c : config => exists (R : tree Z) (M' : word -> option byte),
    c = zcfg (run_segments R_segs rc_inp rc_sp rc_mb) T_ZE2 (zupd R []) M' MD0 /\
    zget R kA3 = A_ZCFREE /\ zget R kA1 = p /\ zget R kA0 = 0 /\ zget R kS0 = u /\ zget R kSP = u + -16 /\
    zget R kGP = gp /\ zget R kTP = tp /\
    zget R kS5 = s5 /\ zget R kS6 = s6 /\ zget R kS7 = s7 /\ zget R kS8 = s8 /\ zget R kS9 = s9 /\ zget R kS10 = s10 /\ zget R kS11 = s11 /\
    mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (u + -8) RA2 /\ mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (u + 56) p /\ mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (u + 72) A_ZCFREE /\ mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (u + 80) 0 /\
    mpostL (run_segments R_segs rc_inp rc_sp rc_mb) mem M' (fp_u2 u p 0)).
  assert (HR : realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_ZB (zupd Rb []) mem MD0) Q).
  { eapply (zb_cps u p q n gp tp s5 s6 s7 s8 s9 s10 s11 fin MD0 Q zc MD0_halted Hfin
              Ku0 Kzimg Ku1 Hua Hp0 Kp1 Hpa Hq1 Kn0 Kn1 Kqn Kpq Kpob Kobq Kprom Rgp Rtp Rs5 Rs6 Rs7 Rs8 Rs9 Rs10 Rs11 memcpy_ok_t adler32_ok_t
              A_HEAD A_DICTID A_DICT A_TYPE A_TYPEDO A_STORED A_COPY_ A_COPY A_TABLE A_LENLENS A_CODELENS
              A_LEN_ A_LEN A_LENEXT A_DIST A_DISTEXT A_MATCH A_LIT A_CHECK A_LENGTH
              0 (wok0 p q n zc Kzimg) site cin0 cout0 W0 s4u s5u rvu st lf cf Hcin0 Hcout0 SI Hcc Rb [] mem
              Lsp La0 Ls0 Ls1 Ls2 Ls3 Ls5 Ls6 Ls9 Ls7 Ls10 Ls11 Ls4 eq_refl eq_refl ROM Wstk Wp ltac:(intros C; exfalso; exact (C eq_refl)) Hin TM).
    -
      intros R M'. intros. apply rz_now. subst Q. cbv beta. exists R, M'.
      repeat (split; [first [reflexivity | assumption] |]). assumption.
    -
      intros R M'. intros. exfalso. match goal with H : 0 <> 0 |- _ => exact (H eq_refl) end. }
  dand HR as (ms' & RUN & HQ). subst Q. cbv beta in HQ. cbn [cfg_ms cfg_model zcfg] in RUN, HQ.
  unfold zst in RUN. cbn [zupd] in RUN. subst Rb. rewrite zden_zlift in RUN.
  pose proof (msteps_mem_grows (run_segments R_segs rc_inp rc_sp rc_mb) _ _ RUN) as G. cbn [ms_mem] in G.
  dand HQ as (R & M' & E & GA4 & GA1 & GA0 & GS0 & GSP & GGP & GTP & G5 & G6 & G7 & G8 & G9 & G10 & G11 & C8 & C64 & C80 & C88 & HP).
  unfold zcfg, zst in E; injection E as E1; subst ms'; cbn [ms_mem] in G; cbn [zupd].
  exists (zden R), M'. split; [exact RUN | split; [| split]].
  - apply frame_mod_WA; try assumption; cbv [STATE_SIZE]; lia_std.
  - unfold end_regs_U9. split_conj.
    + exact (zd_get R 13%bv kA3 _ eq_refl eq_refl GA4).
    + exact (zd_get R 11%bv kA1 _ eq_refl eq_refl GA1).
    + exact (zd_get R 10%bv kA0 _ eq_refl eq_refl GA0).
    + exact (zd_get R 8%bv kS0 _ eq_refl eq_refl GS0).
    + exact (zd_get R 2%bv kSP _ eq_refl eq_refl GSP).
    + rewrite (zd_get R 3%bv kGP _ eq_refl eq_refl GGP). subst gp. rewrite (zl_get regs 3%bv eq_refl). apply w64_of_word.
    + rewrite (zd_get R 4%bv kTP _ eq_refl eq_refl GTP). subst tp. rewrite (zl_get regs 4%bv eq_refl). apply w64_of_word.
    + rewrite EsE. unfold sregs, S_ENTRY5, S_ENTRY. cbn [map app]. rewrite (zd_get_u R 21 kS5 _ eq_refl eq_refl G5) by exact Rs5.
      rewrite (zd_get_u R 22 kS6 _ eq_refl eq_refl G6) by exact Rs6. rewrite (zd_get_u R 23 kS7 _ eq_refl eq_refl G7) by exact Rs7.
      rewrite (zd_get_u R 24 kS8 _ eq_refl eq_refl G8) by exact Rs8. rewrite (zd_get_u R 25 kS9 _ eq_refl eq_refl G9) by exact Rs9.
      rewrite (zd_get_u R 26 kS10 _ eq_refl eq_refl G10) by exact Rs10. rewrite (zd_get_u R 27 kS11 _ eq_refl eq_refl G11) by exact Rs11.
      reflexivity.
  - unfold end_cells_U9. split_conj; [exact C8 | exact C64 | exact C80 | exact C88].
Qed.

Definition contract_U9 : zlib_u2_contract_U9 :=
  ZU2C_U9 zwtok_U9 zw_local za_s zb_s zb0_s zc_t.

End CONTRACT.
