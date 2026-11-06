(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr Nodes Decode FP.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top Require Import TrzNodes TrzStdio.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim StdioBase Stdio Driver.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import AImages ExecA LazyModel NodesA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import NodesCfg RunCeiling.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanSizeClass AsanLayout.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import B_base B_iface BI_shadow BI_region_is_poisoned BI_iface.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BX_atexit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition A_RSTAGE : Z := 0x5d0c10.
Definition A_RSTAGE_LEN : Z := 65536.

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section Stmts.
Variable segs : list Segment.
Variable C : adrv_consts.
Variable APS : Type.
Variable AHK : APS -> list ablock -> list fblock -> mem -> Model -> Prop.
Variable SO : APS -> stdout_st.
Variable aalloc_same : APS -> APS -> Prop.
#[local] Notation wz := (fun z : Z => Z_to_bv 64 z).
#[local] Notation usp sp := (bv_unsigned sp).
#[local] Notation ST m lo sp := (stk segs m lo (bv_unsigned sp)).

(* [comment removed for export] *)
Definition rstage_iv (iv : Z * Z) : Prop := A_RSTAGE <= fst iv /\ snd iv <= A_RSTAGE + A_RSTAGE_LEN.
Definition AHK_frame_rstage_stmt : Prop :=
  forall s LB LF m m' mo W,
    AHK s LB LF m mo -> munch W m m' -> wmono segs m m' ->
    Forall (fun iv => aclient_write_ok C LB iv \/ rstage_iv iv \/ iv = (c_errno C, c_errno C + 4)) W ->
    AHK s LB LF m' mo.

(* [comment removed for export] *)
Definition aread_static_rz_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo mo1 : Model) (s : APS) (LB : list ablock) (LF : list fblock)
         (fd buf count lo : Z) (junk : list byte) (ans : read_ans) (K : TSet),
  K [] ->
  AHK s LB LF m mo ->
  A_RSTAGE <= buf -> buf + count <= A_RSTAGE + A_RSTAGE_LEN -> 0 < count <= 65536 -> 3 <= fd < 2^32 ->
  rw_cells segs m buf [CB (Z.to_nat count) junk] ->
  read_out fd buf count mo = Some (ans, mo1) ->
  ST m lo sp -> alloc_ceiling <= lo -> lo <= usp sp - AICP_STACK -> tp = wz (c_tp C) -> frm0 fc ->
  a0 = wz fd -> a1 = wz buf -> a2 = wz count ->
  (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (mo' : Model) (s' : APS) (res : Z),
     ST m' lo sp ->
     match ans with
     | RdErr e => res = 2^64 - 1 /\ munch [(lo, usp sp); (buf, buf + count); (c_errno C, c_errno C + 4)] m m'
     | RdData bs => res = Z.of_nat (length bs) /\ bytes_at segs m' buf bs /\ munch [(lo, usp sp); (buf, buf + count); (c_errno C, c_errno C + 4)] m m'
     end ->
     wmono segs m m' -> frm0 fc' ->
     AHK s' LB LF m' mo' -> aalloc_same s s' -> SO s' = SO s -> m_fs mo' = m_fs mo -> m_fds mo' = m_fds mo1 -> magree mo1 mo' ->
     realizes_cfg acfg segs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz res) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (ret_pc ra) fc' None m' (seg_rom segs)) mo') K) ->
  realizes_cfg acfg segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz (c_wrap_read C)) fc None m (seg_rom segs)) mo) K.

(* [comment removed for export] *)
Definition amemcpy_static_rz_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : APS) (LB : list ablock) (LF : list fblock)
         (dst src n lo : Z) (bs junk : list byte) (bd : ablock) (K : TSet),
  K [] ->
  AHK s LB LF m mo ->
  In bd LB -> ab_addr bd <= dst -> dst + n <= ab_addr bd + ab_size bd ->
  A_RSTAGE <= src -> src + n <= A_RSTAGE + A_RSTAGE_LEN -> 0 < n < 2^26 ->
  bytes_at segs m src bs -> Z.of_nat (length bs) = n -> rw_cells segs m dst [CB (Z.to_nat n) junk] ->
  ST m lo sp -> alloc_ceiling <= lo -> lo <= usp sp - AICP_STACK -> tp = wz (c_tp C) -> frm0 fc ->
  a0 = wz dst -> a1 = wz src -> a2 = wz n ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (mo' : Model) (s' : APS),
     ST m' lo sp -> rw_cells segs m' dst [CB (Z.to_nat n) bs] ->
     munch [(lo, usp sp); (dst, dst + n)] m m' -> wmono segs m m' -> frm0 fc' ->
     AHK s' LB LF m' mo' -> aalloc_same s s' -> SO s' = SO s -> m_fs mo' = m_fs mo -> m_fds mo' = m_fds mo -> magree mo mo' ->
     realizes_cfg acfg segs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (ret_pc ra) fc' None m' (seg_rom segs)) mo') K) ->
  realizes_cfg acfg segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz (c_wrap_memcpy C)) fc None m (seg_rom segs)) mo) K.
(* [comment removed for export] *)
Definition AHK_libc_head_stmt : Prop :=
  forall s LB LF m mo, AHK s LB LF m mo ->
    exists (cdt thr sec : byte) (tm1 : word), rw_cells segs m AXLIBC [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1].

(* [comment removed for export] *)
Definition aexit_atx_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : APS) (LB : list ablock) (LF : list fblock)
         (code lo : Z),
  AHK s LB LF m mo -> atx_ok_on segs m -> 0 <= code < 2^32 -> zlength (so_buf (SO s)) <= STDOUT_BUFSIZ ->
  ST m lo sp -> alloc_ceiling <= lo -> lo <= usp sp - AEXIT_STACK -> usp sp < 2^47 -> tp = wz (c_tp C) -> frm0 fc -> a0 = wz code ->
  realizes_cfg acfg segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz (c_exit C)) fc None m (seg_rom segs)) mo)
            (ShapeAlg.t_emit (Wz 1 (fst (exit_flush_pure (SO s)))) (t_exit (bv_and (wz code) (wz 255)) (m_fs mo))).
End Stmts.

(* [comment removed for export] *)
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
Lemma img_shadow_facts : forall A n, 0x10000 <= A -> 1 <= n -> A + n <= 0x603000 ->
     range_in_mem C_SB A n
  /\ C_SB + 0x2000 <= shw_lo C_SB A /\ shw_hi C_SB A n <= C_SB + 0xc0608
  /\ (forall Y M, app_mem Y M -> 0 <= M -> 0x603000 <= Y -> shw_hi C_SB A n <= Y \/ Y + M <= shw_lo C_SB A)
  /\ A + n < 2^47 /\ 0 < A.
Proof.
  intros A n HA Hn HAN. aceil.
  pose proof (shw_geom C_SB A n ltac:(unfold C_SB; lia) ltac:(lia) Hn) as G; cbv zeta in G.
  rewrite !Z.shiftr_div_pow2 in G by lia. change (2^3) with 8 in G.
  unfold range_in_mem, A_HIGHEND_VAL, C_SB in *.
  split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; [Z.div_mod_to_equations; lia|].
  split; [| lia].
  intros Y M AY HM HY. unfold app_mem in AY. rewrite kLowAppEnd_val, kHighMemBeg_val in AY. Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
Record a_drv_iface5x (segs : list Segment) (C : adrv_consts) (D : adrv_params) : Prop := mkADrvIface5x {
  adx_frame_rstage : AHK_frame_rstage_stmt segs C (p_APS D) (p_AHK D);
  adx_read_s       : aread_static_rz_stmt segs C (p_APS D) (p_AHK D) (p_SO D) (p_aalloc_same D);
  adx_memcpy_s     : amemcpy_static_rz_stmt segs C (p_APS D) (p_AHK D) (p_SO D) (p_aalloc_same D);
  adx_exit         : aexit_atx_stmt segs C (p_APS D) (p_AHK D) (p_SO D);
  adx_libc_head    : AHK_libc_head_stmt segs (p_APS D) (p_AHK D)
}.
End RC__1.
