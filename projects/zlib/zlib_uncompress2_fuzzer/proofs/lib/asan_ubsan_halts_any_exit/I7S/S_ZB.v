(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.IK Require IConj.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.IK.IConj.
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel Require ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit Require PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.I7S Require SBase S_Entry S_U2C.

From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.I7S Require S_ZBA. Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.I7S.S_ZBA.

Module S_ZA.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.I7S.SBase OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.I7S.S_Entry.S_Loop OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.I7S.S_U2C.S_Ret OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.I7S.S_Entry OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.I7S.S_U2Cw.S_Uw OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.I7S.S_U2C.S_LeaveA OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.I7S.S_U2C.S_Leave OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.I7S.S_U2C.S_Inflate S_U2A OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.I7S.S_U2C.S_U2B OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.I7S.S_U2C.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec.FPState}.

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

Lemma mem_wr_arrk_exists : forall k M base n,
  0 < k <= 8 -> 0 <= n -> 0 <= base -> base + k * n <= two64 ->
  mem_wr R_segs M base (k * n) ->
  exists f, mem_arr k R_segs M base n f /\ (forall i, 0 <= f i < 2 ^ (8 * k)).
Proof.
  intros k M base n Hk Hn Hb Hbn W.
  destruct (mem_wr_readable R_segs wr_rd_R M base (k * n) W ltac:(lia)) as (bs & Hbs & Hlen).
  exists (le_cell k bs). split.
  - apply (mem_arr_of_bytes R_segs k M base n bs Hbs); lia.
  - intros i. apply le_cell_range. exact Hk.
Qed.

Section ZA.
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
Hypothesis Sprom : ZSEP (p + STATE_SIZE <= ROM_LO_ALL \/ ROMHI_S <= p).
Hypothesis Rgp : 0 <= gp < two64. Hypothesis Rtp : 0 <= tp < two64.
Hypothesis Rs5 : 0 <= s5 < two64. Hypothesis Rs6 : 0 <= s6 < two64. Hypothesis Rs7 : 0 <= s7 < two64. Hypothesis Rs8 : 0 <= s8 < two64.
Hypothesis Rs9 : 0 <= s9 < two64. Hypothesis Rs10 : 0 <= s10 < two64. Hypothesis Rs11 : 0 <= s11 < two64.
Hypothesis MEMCPY : memcpy_spec_s.
Hypothesis ADLER : adler32_spec_s.
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
  zget_l Rb l kSP = u + -32 -> zget_l Rb l kS1 = u -> zget_l Rb l kA0 = p ->
  zget_l Rb l kS3 = n -> zget_l Rb l kS4 = 262144 -> zget_l Rb l kS5 = s5 ->
  zget_l Rb l kGP = gp -> zget_l Rb l kTP = tp ->
  zget_l Rb l kS6 = s6 -> zget_l Rb l kS7 = s7 -> zget_l Rb l kS8 = s8 -> zget_l Rb l kS9 = s9 ->
  zget_l Rb l kS10 = s10 -> zget_l Rb l kS11 = s11 ->
  rom_ok M -> mem_wr R_segs M (u + -1024) 1232 -> mem_wr R_segs M p STATE_SIZE ->
  mem_arr 1 R_segs M q n fin ->
  mem_u64 R_segs M (u + -32) BUF -> mem_u64 R_segs M (u + -24) (u + 168) -> mem_u64 R_segs M (u + -16) (u + 176) ->
  mem_u64 R_segs M (u + -8) RA_II ->
  mem_u64 R_segs M (u) q -> mem_u32 R_segs M (u + 8) 0 ->
  mem_u64 R_segs M (u + 64) A_ZCALLOC -> mem_u64 R_segs M (u + 72) A_ZCFREE -> mem_u64 R_segs M (u + 80) 0 ->
  KZE2 u p gp tp s5 s6 s7 s8 s9 s10 s11 MD T M 0 ->
  KZW u p q n gp tp s5 s6 s7 s8 s9 s10 s11 fin MD T M zc 0 ->
  realizes R_segs (zcfg R_segs L_ZA (zupd Rb l) M MD) T.
Proof.
  intros Rb l M Lsp Ls1 La0 Ls3 Ls4 Ls5 Lgp Ltp Ls6 Ls7 Ls8 Ls9 Ls10 Ls11
         ROM Wstk Wp Hin Fm32 Fm24 Fm16 Fm8 S8 S16 S72 S80 S88 HZE2 HZW.
  pose proof two64_eq as TW64.
  assert (Hwph : wok p q n zc 0).
  { unfold wok, ZSEP. cbv [WIN_SIZE ]. pose proof Hzimg as Hz'. cbv [DATA_LO DATA_LEN] in Hz'. split_conj; try lia_std; try (left; reflexivity). reflexivity. }
  eapply (za_prefix_s Rb l M MD T u p q n zc gp tp s5 s6 s7 s8 s9 s10 s11 fin Hh); try eassumption.
  intros R' M' vlen vofs vext vlb vdb vnc vnl vnd vsh.
  intros Gsp Gs0 Gs1 Gs2 Gs3 Gs4 Gs5 Ggp Gtp Gs6 Gs7 Gs8 Gs9 Gs10 Gs11
         ROM' Wstk' Wp' Hin' T8 T16 T32 T40 T64 T72 T80 T88
         P0 P8 P12 P16 P24 P48 P56 P60 P64 P68 P72 P80 P88 P92 P96 P100 P104 P112 P120 P124 P128 P132 P136 P140 P144 P7144
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
            | match goal with H : mem_u64 R_segs ?My ?a ?v |- mem_u64 R_segs ?My ?a ?v' => replace v' with v by lia_std; exact H
                            | H : mem_u32 R_segs ?My ?a ?v |- mem_u32 R_segs ?My ?a ?v' => replace v' with v by lia_std; exact H end
            | match goal with |- ?G => idtac "EMSIDE" G end ].
  - eapply (framed_mpostL_trans _ _ _ _ _ _ (mpostL_refl R_segs M (fp_u2 u p 0)) HP).
    intros x Hx; eapply ranges_within_outside; [| exact Hx]; unfold fp_u2; cbv [STATE_SIZE WIN_SIZE]; cbn [Z.eqb]; ranges_within_tac.
Qed.
End ZA.
End FXG.
End S_ZA.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit Require Frame Hoare.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit Require RefMemcpyLib FuzzMem S7MemcpyBase S7Memcpy S7AdlerBase S7AdlerIface S7Adler.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit Require S7LibStmt.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel Require Inftrees InftreesCoverage ItableModel.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.I7S Require Base.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.IK Require ZTac ZMem ZCall ZCallL ZArr ZArr4 IDefs ISpecs ITac.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.I7S Require S_It0 S_It3.

From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.I7S Require S_ZBI. Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.I7S.S_ZBI.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.I7S Require S_It4 S_It5 S_It6.

From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel Require InflateInvTab.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.IK Require ZStep.

From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.I7S Require S_ZBF. Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.I7S.S_ZBF.







Module S_Tok.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.ShapeAlg OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.Frame OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.Hoare.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.RefMemcpyLib OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.FuzzMem OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.S7MemcpyBase OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.S7Memcpy OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.S7AdlerBase OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.S7AdlerIface OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.S7Adler.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.S7LibStmt.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.I7S.SBase OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.I7S.S_U2C.S_LeaveA S_U2A OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.I7S.S_U2C.S_U2B OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.I7S.S_U2C S_It7 S_Fast1 S_Fast7.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec.FPState}.


Lemma w64_lit : forall z (w : word), bv_unsigned w = z -> w64 z = w.
Proof. intros z w <-. apply w64_of_word. Qed.

Lemma msteps_memcpy_S7 : msteps_memcpy R_segs A_MEMCPY.
Proof.
  intros mem0 dst src n bs rom Hn Hlen Hsrc Hdst Hdisj Hnws Hnwd regs ret Hret H1 H10 H11 H12.
  unfold A_MEMCPY. rewrite (w64_lit 131460 (0x20184%bv : word)) by reflexivity.
  apply (ref_memcpy mem0 dst src n bs rom); try assumption.
  constructor; assumption.
Qed.
Theorem memcpy_ok : memcpy_spec_s.
Proof. unfold memcpy_spec_s. apply memcpy_glue. apply msteps_memcpy_S7. Qed.

Lemma img_ok_of_rom_ok : forall m, rom_ok m -> img_ok m.
Proof.
  intros m H. apply (img_ok_of_range m ROM_LO ROM_HI).
  - apply rom_hyp_of_okG; [cbv [ROM_LO]; lia_std | rewrite two64_eq; cbv [ROM_HI]; lia_std | exact H].
  - cbv [ROM_LO RO_LO]. lia_std.
  - cbv [ROM_HI RO_HI]. lia_std.
Qed.
Lemma msteps_adler32_S7 : msteps_adler32 R_segs A_ADLER32 FR_AD rom_ok.
Proof.
  intros regs m rom retw usp a adr v len. unfold A_ADLER32, FR_AD. rewrite (w64_lit 95732 (0x175f4%bv : word)) by reflexivity.
  intros. eapply (s7_adler32 regs m rom retw usp a adr v len); try eassumption. apply img_ok_of_rom_ok. assumption.
Qed.
Theorem adler32_ok : adler32_spec_s.
Proof. unfold adler32_spec_s. apply adler32_glue; [cbv [FR_AD]; lia_std | apply msteps_adler32_S7]. Qed.

Lemma msteps_adler32_null_S7 : msteps_adler32_null0 R_segs A_ADLER32.
Proof.
  intros regs m rom retw. unfold A_ADLER32. rewrite (w64_lit 95732 (0x175f4%bv : word)) by reflexivity.
  exact (s7_adler32_null regs m rom retw).
Qed.
Theorem adler32_null_ok : adler32_null_spec_s.
Proof. unfold adler32_null_spec_s. apply adler32_null0_glue. apply msteps_adler32_null_S7. Qed.

Theorem itable_ok : itable_spec_s.
Proof. exact itable_s. Qed.
Theorem ifast_ok : ifast_spec_s.
Proof. exact ifast_s. Qed.

Section Local.
Variable P : word -> Prop.
Variables M M' : mem.
Hypothesis AG : forall x, P x -> M' x = M x.

Lemma mem_is_local : forall a bs,
  (forall x : word, a <= bv_unsigned x < a + Z.of_nat (length bs) -> P x) ->
  0 <= a -> a + Z.of_nat (length bs) <= two64 ->
  mem_is R_segs M a bs -> mem_is R_segs M' a bs.
Proof.
  intros a bs HP Ha Hn H. unfold mem_is in *.
  destruct bs as [|b bs']; [exact H|].
  assert (Ha' : bv_unsigned (w64 a) = a).
  { rewrite w64_unsigned, mod_small_u64; [reflexivity|]. cbn [length] in Hn. lia_std. }
  rewrite (rdn_ext R_segs (length (b :: bs')) M' M (w64 a)); [exact H | |].
  - rewrite Ha'. rewrite <- two64_eq. exact Hn.
  - intros x Hx. apply AG. apply HP. rewrite Ha' in Hx. exact Hx.
Qed.

Lemma mem_u64_local : forall a v,
  (forall x : word, a <= bv_unsigned x < a + 8 -> P x) -> 0 <= a -> a + 8 <= two64 ->
  mem_u64 R_segs M a v -> mem_u64 R_segs M' a v.
Proof.
  intros a v HP Ha Hn H. unfold mem_u64 in *.
  apply (mem_is_local a (Z_to_le_bytes 8 v)); rewrite ?length_Z_to_le_bytes; first [exact HP | exact Ha | exact Hn | exact H].
Qed.
Lemma mem_u32_local : forall a v,
  (forall x : word, a <= bv_unsigned x < a + 4 -> P x) -> 0 <= a -> a + 4 <= two64 ->
  mem_u32 R_segs M a v -> mem_u32 R_segs M' a v.
Proof.
  intros a v HP Ha Hn H. unfold mem_u32 in *.
  apply (mem_is_local a (Z_to_le_bytes 4 v)); rewrite ?length_Z_to_le_bytes; first [exact HP | exact Ha | exact Hn | exact H].
Qed.
Lemma mem_arr_local : forall k base n f,
  (forall x : word, base <= bv_unsigned x < base + k * n -> P x) ->
  mem_arr k R_segs M base n f -> mem_arr k R_segs M' base n f.
Proof.
  intros k base n f HP (A & B & C & D & H). split; [exact A | split; [exact B | split; [exact C | split; [exact D |]]]].
  intros i Hi. eapply mem_is_local; [ | nia | rewrite length_Z_to_le_bytes; nia | apply H; exact Hi].
  intros x Hx. apply HP. rewrite length_Z_to_le_bytes in Hx. nia.
Qed.

Lemma i_frame_local : forall cx,
  (forall x : word, c_u cx + -224 <= bv_unsigned x < c_u cx -> P x) ->
  0 <= c_u cx + -1024 -> c_u cx + 208 <= two64 ->
  i_frame cx M -> i_frame cx M'.
Proof.
  intros cx HP Hu1 Hu2 H. unfold i_frame in *.
  dand H as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20 & A21 & A22 & A23 & A24 & A25).
  repeat split; (eapply mem_u64_local; [ | | | eassumption]; [intros x Hx; apply HP; lia_std | lia_std | lia_std]).
Qed.
Lemma i_hooks_local : forall cx,
  (forall x : word, c_u cx + 64 <= bv_unsigned x < c_u cx + 80 -> P x) ->
  0 <= c_u cx -> c_u cx + 208 <= two64 ->
  i_hooks cx M -> i_hooks cx M'.
Proof.
  intros cx HP Hu1 Hu2 [A B].
  split; (eapply mem_u64_local; [ | | | eassumption]; [intros x Hx; apply HP; lia_std | lia_std | lia_std]).
Qed.
Lemma i_cst_local : forall cx,
  (forall x : word, (c_u cx + 56 <= bv_unsigned x < c_u cx + 88) \/ (c_p cx <= bv_unsigned x < c_p cx + 7164) -> P x) ->
  0 <= c_u cx -> c_u cx + 208 <= two64 -> 0 <= c_p cx -> c_p cx + STATE_SIZE <= two64 ->
  i_cst R_segs cx M -> i_cst R_segs cx M'.
Proof.
  intros cx HP Hu1 Hu2 Hp1 Hp2 H. unfold i_cst, STATE_SIZE in *.
  dand H as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
  repeat split; ((eapply mem_u64_local || eapply mem_u32_local); [ | | | eassumption]; [intros x Hx; apply HP; lia_std | lia_std | lia_std]).
Qed.
Lemma st_at_local : forall cx st,
  (forall x : word, c_p cx + 8 <= bv_unsigned x < c_p cx + 168 -> P x) ->
  0 <= c_p cx -> c_p cx + STATE_SIZE <= two64 ->
  st_at R_segs cx st M -> st_at R_segs cx st M'.
Proof.
  intros cx st HP Hp1 Hp2 H. unfold st_at, st_rest, STATE_SIZE in *.
  dand H as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17).
  repeat split; ((eapply mem_u64_local || eapply mem_u32_local); [ | | | eassumption]; [intros x Hx; apply HP; lia_std | lia_std | lia_std]).
Qed.
Lemma strm_at_local : forall cx st,
  (forall x : word, (c_u cx <= bv_unsigned x < c_u cx + 36) \/ (c_p cx + 96 <= bv_unsigned x < c_p cx + 108) -> P x) ->
  0 <= c_u cx -> c_u cx + 208 <= two64 -> 0 <= c_p cx -> c_p cx + STATE_SIZE <= two64 ->
  strm_at R_segs cx st M -> strm_at R_segs cx st M'.
Proof.
  intros cx st HP Hu1 Hu2 Hp1 Hp2 H. unfold strm_at, STATE_SIZE in *.
  dand H as (A1 & A2 & A3 & A4 & A5 & A6).
  repeat split; ((eapply mem_u64_local || eapply mem_u32_local); [ | | | eassumption]; [intros x Hx; apply HP; lia_std | lia_std | lia_std]).
Qed.
End Local.

Definition cxw (u p q n s5 s6 s7 s8 s9 s10 s11 zc cin0 cout0 W0 ra : Z) : ictx :=
  cxc u p q n 0 0 s5 s6 s7 s8 s9 s10 s11 zc 0 cin0 cout0 W0 ra.

Definition tok_mem (cx : ictx) (st : ist) (rv : Z) (lf cf : Z -> Z) (M : mem) : Prop :=
  mem_u64 R_segs M (c_u cx + -232) L_UW_RET /\ mem_u64 R_segs M (c_u cx + -240) (c_p cx) /\
  mem_u64 R_segs M (c_u cx + -248) rv /\ mem_u64 R_segs M (c_u cx + -256) (c_n cx - t_cin st) /\
  mem_u64 R_segs M (c_u cx + -264) (c_osz cx - t_cout st) /\ mem_u64 R_segs M (c_u cx + -272) (t_out st - (c_osz cx - t_cout st)) /\
  i_frame cx M /\ i_cst R_segs cx M /\ i_hooks cx M /\
  st_at R_segs cx st M /\ strm_at R_segs cx st M /\
  mem_arr 2 R_segs M (c_p cx + 168) N_LENS lf /\ mem_arr 4 R_segs M (c_p cx + 1384) N_CODES cf.

Definition tok_pure (u p q n s5 s6 s7 s8 s9 s10 s11 zc cin0 cout0 W0 ra s11v : Z) (st : ist) (lf cf : Z -> Z) : Prop :=
  (ra = RA_C1 \/ ra = RA_C2) /\ 0 <= cin0 <= n /\ 0 <= cout0 <= 262144 /\
  0 <= s5 < two64 /\ 0 <= s6 < two64 /\ 0 <= s7 < two64 /\ 0 <= s8 < two64 /\ 0 <= s9 < two64 /\ 0 <= s10 < two64 /\ 0 <= s11 < two64 /\
  0 <= s11v < two64 /\
  sinv (cxw u p q n s5 s6 s7 s8 s9 s10 s11 zc cin0 cout0 W0 ra) st lf cf /\ cout0 < t_cout st /\ t_mode st <= DONE /\
  zc + FRA <= u /\ u + 208 <= 140737488355328 /\ 0 < p /\ p + STATE_SIZE <= zc.

Definition tok_regs (p q n cin0 s11v : Z) (st : ist) : list Z :=
  [BUF + t_cout st; t_out st - (262144 - t_cout st); 1; p; t_out st - (262144 - t_cout st); n - cin0;
   262144 - t_cout st; t_hold st; t_bits st; t_out st; s11v; q + t_cin st].

Definition zwtok_S7 : ZWINV := fun u p q n zc sE sW M =>
  exists (s5 s6 s7 s8 s9 s10 s11 cin0 cout0 W0 ra rv s11v : Z) (st : ist) (lf cf : Z -> Z),
    sE = [s5; s6; s7; s8; s9; s10; s11] /\ sW = tok_regs p q n cin0 s11v st /\
    tok_pure u p q n s5 s6 s7 s8 s9 s10 s11 zc cin0 cout0 W0 ra s11v st lf cf /\
    tok_mem (cxw u p q n s5 s6 s7 s8 s9 s10 s11 zc cin0 cout0 W0 ra) st rv lf cf M.

Theorem zw_local : zw_local_stmt_S7 zwtok_S7.
Proof.
  intros u p q n zc sE sW M M' AG H.
  dand H as (s5 & s6 & s7 & s8 & s9 & s10 & s11 & cin0 & cout0 & W0 & ra & rv & s11v & st & lf & cf & EsE & EsW & PURE & TM).
  exists s5, s6, s7, s8, s9, s10, s11, cin0, cout0, W0, ra, rv, s11v, st, lf, cf.
  split; [exact EsE | split; [exact EsW | split; [exact PURE |]]].
  pose proof two64_eq as TW64.
  assert (HL : zc + FRA <= u /\ u + 208 <= 140737488355328 /\ 0 < p /\ p + STATE_SIZE <= zc).
  { unfold tok_pure in PURE. destr_conj PURE. split_conj; assumption. }
  clear PURE EsE EsW. cbv [FRA STATE_SIZE] in HL. dand HL as (Hu0 & Hu1 & Hp0 & Hp1).
  unfold tok_mem, cxw, cxc in *. icx_cbn.
  dand TM as (T1 & T2 & T3 & T4 & T5 & T6 & FRM & CST & HK & SAT & STRM & Hlens & Hcodes).
  unfold in_fpw_S7, S7_ZWD, S7_INFL_N, S7_BUF, S7_BUF_N in AG.
  split_conj.
  all: first [ eapply (mem_u64_local _ M M' AG); [ | | | eassumption]; [intros x Hx; lia_std | lia_std | lia_std]
             | eapply (i_frame_local _ M M' AG); [ | | | eassumption]; icx_cbn; [intros x Hx; lia_std | lia_std | lia_std]
             | eapply (i_hooks_local _ M M' AG); [ | | | eassumption]; icx_cbn; [intros x Hx; lia_std | lia_std | lia_std]
             | eapply (i_cst_local _ M M' AG); [ | | | | | eassumption]; icx_cbn; cbv [STATE_SIZE]; [intros x Hx; lia_std | lia_std | lia_std | lia_std | lia_std]
             | eapply (st_at_local _ M M' AG); [ | | | eassumption]; icx_cbn; cbv [STATE_SIZE]; [intros x Hx; lia_std | lia_std | lia_std]
             | eapply (strm_at_local _ M M' AG); [ | | | | | eassumption]; icx_cbn; cbv [STATE_SIZE BUF]; [intros x Hx; lia_std | lia_std | lia_std | lia_std | lia_std]
             | eapply (mem_arr_local _ M M' AG); [ | eassumption]; cbv [N_LENS N_CODES]; intros x Hx; lia_std
             | match goal with |- ?G => idtac "LOCSIDE" G end ].
Qed.
End FXG.
End S_Tok.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.I7S Require Import SBase. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.I7S Require S_Entry. Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.I7S.S_Entry.S_Loop. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.I7S Require S_U2C. Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.I7S.S_U2C.S_Ret. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.I7S Require Import S_Entry. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.I7S Require S_U2C. Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.I7S.S_U2Cw.S_Uw. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.I7S Require S_U2C. Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.I7S.S_U2C.S_LeaveA. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.I7S Require S_U2C. Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.I7S.S_U2C.S_Leave. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.I7S Require S_U2C. Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.I7S.S_U2C.S_Inflate. Import S_U2A. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.I7S Require S_U2C. Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.I7S.S_U2C.S_U2B. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.I7S Require Import S_U2C. Import S_ZA. Import S_Tok.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.PropExec.FPState}.

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
Hypothesis Sprom : ZSEP (p + STATE_SIZE <= ROM_LO_ALL \/ ROMHI_S <= p).
Hypothesis Rgp : 0 <= gp < two64. Hypothesis Rtp : 0 <= tp < two64.
Hypothesis Rs5 : 0 <= s5 < two64. Hypothesis Rs6 : 0 <= s6 < two64. Hypothesis Rs7 : 0 <= s7 < two64. Hypothesis Rs8 : 0 <= s8 < two64.
Hypothesis Rs9 : 0 <= s9 < two64. Hypothesis Rs10 : 0 <= s10 < two64. Hypothesis Rs11 : 0 <= s11 < two64.
Hypothesis MEMCPY : memcpy_spec_s.
Hypothesis ADLER : adler32_spec_s.
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
Variables (site : bool) (cin0 cout0 W0 rv : Z) (st : ist) (lf cf : Z -> Z).
Hypothesis Hcin0 : 0 <= cin0 <= n.
Hypothesis Hcout0 : 0 <= cout0 <= 262144.
Hypothesis SI : sinv (cxc u p q n gp tp s5 s6 s7 s8 s9 s10 s11 zc 0 cin0 cout0 W0 (ra_site site)) st lf cf.
Hypothesis Hcc : cout0 < t_cout st.

Local Ltac open_zb :=
  zkeysb; unfold L_UW_RET, L_RET, L_ZB, T_ZE1, T_ZE2, RA2 in *;
  cbv [STATE_SIZE FRA WIN_SIZE ROM_LO_ALL A_ZCALLOC A_ZCFREE BUF DATA_LO DATA_LEN] in *;
  pose proof two64_eq as TW64.

Theorem zb_cps : forall Rb l M,
  zget_l Rb l kSP = u + -272 -> zget_l Rb l kA0 = w ->
  zget_l Rb l kS0 = BUF + t_cout st -> zget_l Rb l kS1 = t_out st - (262144 - t_cout st) ->
  zget_l Rb l kS2 = 1 -> zget_l Rb l kS3 = p -> zget_l Rb l kS4 = t_out st - (262144 - t_cout st) ->
  zget_l Rb l kS5 = n - cin0 -> zget_l Rb l kS6 = 262144 - t_cout st -> zget_l Rb l kS7 = t_hold st ->
  zget_l Rb l kS8 = t_bits st -> zget_l Rb l kS9 = t_out st -> zget_l Rb l kS11 = q + t_cin st ->
  zget_l Rb l kGP = gp -> zget_l Rb l kTP = tp ->
  rom_ok M -> mem_wr R_segs M (u + -1024) 1232 -> mem_wr R_segs M p STATE_SIZE ->
  (w <> 0 -> mem_wr R_segs M w WIN_SIZE) ->
  mem_arr 1 R_segs M q n fin ->
  tok_mem (cxc u p q n gp tp s5 s6 s7 s8 s9 s10 s11 zc 0 cin0 cout0 W0 (ra_site site)) st rv lf cf M ->
  KZE2 u p gp tp s5 s6 s7 s8 s9 s10 s11 MD T M w ->
  KZE1 u p gp tp s5 s6 s7 s8 s9 s10 s11 MD T M w ->
  realizes R_segs (zcfg R_segs L_ZB (zupd Rb l) M MD) T.
Proof.
  intros Rb l M Lsp La0 Ls0 Ls1 Ls2 Ls3 Ls4 Ls5 Ls6 Ls7 Ls8 Ls9 Ls10 Lgp Ltp ROM Wstk Wp Ww Hin TM HZE2 HZE1.
  pose proof Hw as Hw'. dand Hw' as (W1 & W2 & W3 & W4 & W5 & W6 & W7).
  pose proof SI as SI'. dand SI' as (RNG_ & _ & _ & _).
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  icx_cbn.
  assert (RF : 0 <= cin /\ cin <= n /\ 0 <= cout /\ cout <= 262144 /\ 262144 - cout <= out /\ out <= 262144 /\ out - (262144 - cout) <= cout).
  { clear -RNG_. unfold RNG, cxc in RNG_. icx_cbn. destr_conj RNG_. split_conj; assumption. }
  clear RNG_. dand RF as (Rci0 & Rci1 & Rco0 & Rco1 & Rou0 & Rou1 & Rou2).
  dand TM as (T1 & T2 & T3 & T4 & T5 & T6 & FRM & CST & HK & SAT & STRM & Hlens & Hcodes).
  unfold cxc in *. icx_cbn.
  pose proof CST as CST'. unfold i_cst in CST'. icx_cbn. unfold wsz in CST'. icx_cbn. cbn [Z.eqb] in CST'.
  dand CST' as (C64 & C88 & Cp0 & Cp16 & Cp48 & Cp56 & Cp60 & Cp72 & Cp7144).
  dand (out_arr_exists M) as (fo & HOB & Hfo). cbv [BUF_N] in HOB.
  open_zb.
  assert (T1' : mem_u64 R_segs M (u + -224 + -8) 93932) by (replace (u + -224 + -8) with (u + -232) by lia_std; exact T1).
  assert (T2' : mem_u64 R_segs M (u + -224 + -16) p) by (replace (u + -224 + -16) with (u + -240) by lia_std; exact T2).
  assert (T3' : mem_u64 R_segs M (u + -224 + -24) rv) by (replace (u + -224 + -24) with (u + -248) by lia_std; exact T3).
  assert (T4' : mem_u64 R_segs M (u + -224 + -32) (n - cin)) by (replace (u + -224 + -32) with (u + -256) by lia_std; exact T4).
  assert (T5' : mem_u64 R_segs M (u + -224 + -40) (262144 - cout)) by (replace (u + -224 + -40) with (u + -264) by lia_std; exact T5).
  assert (T6' : mem_u64 R_segs M (u + -224 + -48) (out - (262144 - cout))) by (replace (u + -224 + -48) with (u + -272) by lia_std; exact T6).
  clear T1 T2 T3 T4 T5 T6.
  eapply (uw_resume_s MEMCPY Rb l M MD T p 208560 262144 w cout (out - (262144 - cout)) (u + -224) 93932
            p rv (n - cin) (262144 - cout) (out - (262144 - cout)) zc fo Hh).
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
    clear SAT STRM Hlens Hcodes HOB Hfo CST Cp60 Cp72 T1' T2' T3' T4' T5' T6'.
    pose proof (ctx_ok_cxc u p q n gp tp s5 s6 s7 s8 s9 s10 s11 zc Hu0 Hzimg Hu1 Hua Hp0 Hp1 Hpa Hq1 Hn0 Hn1 Hqn Spq Spob Sobq Sprom
                  Rgp Rtp Rs5 Rs6 Rs7 Rs8 Rs9 Rs10 Rs11 0 cin0 cout0 W0 (ra_site site) (wok0 p q n zc Hzimg) Hcin0 Hcout0
                  ltac:(destruct site; [left | right]; reflexivity)) as CX0.
    pose proof CX0 as CXo. unfold cxc in CXo. dand CXo as (_ & _ & SEP).
    match goal with HP : mpostL R_segs M M' _ |- _ =>
      pose proof HP as HPw; zreattachL HP end.
    clear SEP.
    pose proof (mpostL_stable R_segs M [(u + -1024, 1024); (u, 112); (p, 7176); (208560, 262144)] ltac:(ranges_ok_tac)) as HST.
    assert (HAG : framed (fun X => mpostL R_segs M X [(u + -1024, 1024); (u, 112); (p, 7176); (208560, 262144)]) M').
    { eapply (framed_mpostL_trans _ _ _ _ _ _ (mpostL_refl R_segs M _) HPw).
      intros x Hx; eapply ranges_within_outside; [| exact Hx]; ranges_within_tac. }
    clear HPw.
    pose proof FRM as FRM'. unfold i_frame in FRM'. icx_cbn.
    dand FRM' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Q104 & _ & _ & Q72 & _).
    rewrite Wz in *.
    zstep Rfd.
    zstep Rfd.
    zbr Rfd false.
    zstep Rfd.
    zstep Rfd.
    tstep1 Rfd.
    zstep Rfd.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?R9 ?Mx _) _ =>
      eapply (ret_s _ R9 [] Mx MD T (-4) CX0 Hh) end.
    + unfold s_regs_ret, cxc, Kra; icx_cbn; zkeys; cbn [Pos.eqb]; split_conj; zreg.
    + exact FRM.
    + intros R9 HB.
      lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mx _) _ =>
        eapply (u2_krx u p q n gp tp s5 s6 s7 s8 s9 s10 s11 fin MD T M zc Hh Hu0 Hzimg Hu1 Hp0 Hp1 0 (wok0 p q n zc Hzimg) HZE2 HZE1
                  site cin0 cout0 W0 M (mpostL_refl R_segs M (fp_u2 u p 0)) R9 Mx (-4) 16210) end.
      * cbv. discriminate.
      * exact HB.
      * unfold s_std, i_cst, wsz, cxc; icx_cbn; cbn [Z.eqb]; cbv [BUF BUF_N]; split_conj; try assumption.
        all: first [ apply buf_writable | intros i Hi; exfalso; lia_std | match goal with |- ?G => idtac "STDSIDE" G end ].
      * unfold cxc; icx_cbn. assumption.
      * unfold reach; cbv [HEAD DICTID MEM]; lia_std.
      * unfold fp_call, fp_loop, wsz, cxc; icx_cbn; cbv [FRA ZS_OFF ZS_SIZE STATE_SIZE BUF]; cbn [Z.eqb app].
        eapply (framed_mpostL_trans _ _ _ _ _ _ (mpostL_refl R_segs M _) HAG).
        intros x Hx; eapply ranges_within_outside; [| exact Hx]; ranges_within_tac.
  -
    intros R' M' whave' wnext' Wnz. intros. zimps. zkeys.
    specialize (Ww Wnz).
    pose proof SAT as SAT'. destruct SAT' as [Hmode SREST']. unfold st_rest, cxc in SREST'. icx_cbn. destr_conj SREST'. clear SAT.
    unfold cxc in Hmode; icx_cbn.
    clear Cp60 Cp72 CST HOB Hfo T1' T2' T3' T4' T5' T6'.
    repeat match goal with
           | H : mem_u32 R_segs M (p + 76) _ |- _ => clear H
           | H : mem_u32 R_segs M (p + 80) _ |- _ => clear H
           end.
    pose proof (ctx_ok_cxc u p q n gp tp s5 s6 s7 s8 s9 s10 s11 zc Hu0 Hzimg Hu1 Hua Hp0 Hp1 Hpa Hq1 Hn0 Hn1 Hqn Spq Spob Sobq Sprom
                  Rgp Rtp Rs5 Rs6 Rs7 Rs8 Rs9 Rs10 Rs11 w cin0 cout0 W0 (ra_site site) Hw Hcin0 Hcout0
                  ltac:(destruct site; [left | right]; reflexivity)) as CX1.
    pose proof CX1 as CXo. unfold cxc in CXo. dand CXo as (_ & _ & SEP).
    lazymatch goal with HP : mpostL R_segs M M' ?rs |- _ =>
      pose proof HP as HPw; unfold uw_res_fp in HP; cbv [WIN_SIZE] in HP;
      lazymatch type of HP with mpostL _ _ _ ?rs' =>
        apply (mem_arr_magreeL R_segs 1 M M' rs' q n fin (proj1 HP)) in Hin;
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
    pose proof (u2_krl u p q n gp tp s5 s6 s7 s8 s9 s10 s11 fin MD T M zc Hh Hu0 Hzimg Hu1 Hp0 Hp1 Hn1 Hqn Spq Spob Sobq w Hw HZE2 HZE1
                  _ (PC _) site cin0 cout0 W0 M Hcin0 Hcout0 (Z.le_refl _) (mpostL_refl R_segs M (fp_u2 u p w))) as HKRL.
    pose proof (u2_krx u p q n gp tp s5 s6 s7 s8 s9 s10 s11 fin MD T M zc Hh Hu0 Hzimg Hu1 Hp0 Hp1 w Hw HZE2 HZE1
                  site cin0 cout0 W0 M (mpostL_refl R_segs M (fp_u2 u p w))) as HKRX.
    lazymatch goal with |- realizes _ (zcfg _ _ ?R9 ?Mx _) _ =>
      eapply (leave_uwret_s _ fin MD T M CX1 Hh OBLOW1 HKRL HKRX R9 [] Mx
                (set_win (IST mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext) whave' wnext')
                rv 0 lf cf) end.
    all: first [ eapply sinv_rewin; [exact SI | exact Wnz | assumption ..]
               | unfold cxc; icx_cbn; zreg
               | unfold set_win, cxc; icx_cbn; zreg
               | left; reflexivity
               | unfold s_std, i_cst, wsz, cxc; icx_cbn; rewrite (proj2 (Z.eqb_neq w 0) Wnz); cbv [BUF BUF_N WIN_SIZE]; split_conj;
                 first [ assumption | apply buf_writable | match goal with |- ?G => idtac "STDSIDE1" G end ]
               | unfold st_at, st_rest, set_win, cxc; icx_cbn; split_conj; assumption
               | unfold strm_at, set_win, cxc; icx_cbn; unfold strm_at, cxc in STRM; icx_cbn; exact STRM
               | assumption
               | unfold fp_call, fp_loop, wsz, cxc; icx_cbn; rewrite (proj2 (Z.eqb_neq w 0) Wnz); cbv [FRA ZS_OFF ZS_SIZE STATE_SIZE WIN_SIZE BUF]; cbn [app];
                 eapply (framed_mpostL_trans _ _ _ _ _ _ (mpostL_refl R_segs M _) HPw);
                 intros x Hx; eapply ranges_within_outside; [| exact Hx]; unfold uw_res_fp; cbv [WIN_SIZE]; ranges_within_tac
               | match goal with |- ?G => idtac "LVSIDE" G end ].
Qed.
End ZB.
End FXG.
