(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr Nodes Decode FP.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top Require Import TrzNodes TrzStdio.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim StdioBase Stdio Driver.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import Printf_model.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import AImages ExecA LazyModel NodesA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import NodesCfg.          (* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Export B_alloc_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition adiag_pieces (d : diag_msg) : list (list Z) :=
  match d with
  | DUsage s => pieces_usage s | DCannotOpen s => pieces_cannot_open s | DReadError s => pieces_read_error s
  | DTooBig => pieces_too_big | DOom => pieces_oom | DShortHdr => pieces_short_hdr | DCfgOverrun => pieces_cfg_overrun
  end.


From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section Stmts.
Variable segs : list Segment.          (* [comment removed for export] *)
Variable C : adrv_consts.
Variable FM : adrv_fmts.

(* [comment removed for export] *)
Variable APS : Type.                                                   (* [comment removed for export] *)
Variable AHK : APS -> list ablock -> list fblock -> mem -> Model -> Prop.
Variable SO : APS -> stdout_st.                                        (* [comment removed for export] *)
(* [comment removed for export] *)
Variable aS : APS -> word -> Prop.
Variable aN : APS -> nat.
Variable aEB : APS -> Z.
(* [comment removed for export] *)
Variable amalloc_rel : Z -> APS -> Model -> option Z -> APS -> Model -> Prop.
Variable afree_rel : Z -> APS -> Model -> APS -> Model -> Prop.
Variable ayfuzz_rel : APS -> Model -> APS -> Model -> Prop.            (* [comment removed for export] *)
Variable aalloc_same : APS -> APS -> Prop.                              (* [comment removed for export] *)
Variable arealloc_rel : Z -> Z -> APS -> Model -> option Z -> APS -> Model -> Prop.   (* [comment removed for export] *)
Variable acredit : APS -> Z.                                            (* [comment removed for export] *)
Variable acharge : Z -> Z.                                              (* [comment removed for export] *)
Variable arefund : Z -> Z.                                              (* [comment removed for export] *)
(* [comment removed for export] *)
Variable uanchor : mem -> Z (* [comment removed for export] *) -> word (* [comment removed for export] *) -> word (* [comment removed for export] *) -> Prop.
Variable URA : list Z.      (* [comment removed for export] *)
Variable AHEAD : nat -> list (Z * Z) -> list aevent -> APS -> Model -> Prop.   (* [comment removed for export] *)

#[local] Notation usp sp := (bv_unsigned sp).
#[local] Notation ST m lo sp := (stk segs m lo (bv_unsigned sp)).

#[local] Notation wz := (fun z : Z => Z_to_bv 64 z).
#[local] Notation adrv_static := (B_base.adrv_static C).
#[local] Notation aclient_addr := (B_base.aclient_addr C).
#[local] Notation ablock_range := (B_base.ablock_range C).
#[local] Notation aheap_pres := (B_alloc_iface.aheap_pres segs C).
#[local] Notation nbig := (B_alloc_iface.nbig).

(* [comment removed for export] *)
Definition adrv_acc (LB : list ablock) (x : acc) : Prop :=
  let a := bv_unsigned (fst x) in let k := Z.of_nat (snd x) in
  (alloc_ceiling <= a /\ a + k <= 2^64)
  \/ (c_img_lo C <= a /\ a + k <= c_img_hi C)
  \/ (exists b, In b LB /\ ab_addr b <= a /\ a + k <= ab_addr b + ab_size b).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition AHK_kip_stmt : Prop :=
  forall s LB LF m mo, AHK s LB LF m mo ->
    m_halted mo = None /\ minvA mo /\ LI (aS s) (aN s) (aEB s) mo
    /\ (forall x, adrv_acc LB x -> acc_ok (m_vm_lazy mo) (aS s) x)
    /\ (forall mo', magree mo mo' -> LI (aS s) (aN s) (aEB s) mo' -> AHK s LB LF m mo').
Definition AHK_mem_inv_stmt : Prop :=
  forall s LB LF m mo, AHK s LB LF m mo -> mem_inv segs m.
Definition AHK_perm_stmt : Prop :=
  forall s LB LB' LF m mo, AHK s LB LF m mo -> Permutation LB LB' -> AHK s LB' LF m mo.
(* [comment removed for export] *)
Definition aclient_write_ok (LB : list ablock) (iv : Z * Z) : Prop :=
  alloc_ceiling <= fst iv
  \/ (exists b, In b LB /\ ab_addr b <= fst iv /\ snd iv <= ab_addr b + ab_size b)
  \/ (c_initialized C <= fst iv /\ snd iv <= c_initialized C + 8)
  \/ (c_initialized C + 0x20990 <= fst iv /\ snd iv <= c_initialized C + 0x20990 + 544).
Definition AHK_frame_stmt : Prop :=
  forall s LB LF m m' mo W,
    AHK s LB LF m mo -> munch W m m' -> wmono segs m m' -> Forall (aclient_write_ok LB) W -> AHK s LB LF m' mo.
(* [comment removed for export] *)
Definition AHK_vmsame_stmt : Prop :=
  forall s LB LF m mo mo', AHK s LB LF m mo -> vm_same mo mo' -> minvA mo' -> m_halted mo' = None -> m_fs mo' = m_fs mo ->
    AHK s LB LF m mo'.
Definition AHK_blocks_stmt : Prop :=
  forall s LB LF m mo, AHK s LB LF m mo ->
    (forall b, In b LB -> ablock_range (ab_addr b) (ab_size b))
    /\ (forall b1 b2, In b1 LB -> In b2 LB -> ab_addr b1 <> ab_addr b2 ->
          ab_addr b1 + ab_size b1 <= ab_addr b2 \/ ab_addr b2 + ab_size b2 <= ab_addr b1)
    /\ List.NoDup (map ab_addr LB).
(* [comment removed for export] *)
Definition AHK_so_stmt : Prop :=
  forall s LB LF m mo, AHK s LB LF m mo -> zlength (so_buf (SO s)) <= STDOUT_BUFSIZ.
(* [comment removed for export] *)
Definition uanchor_triv_stmt : Prop :=
  forall m SP ra s0, bv_unsigned s0 < alloc_ceiling -> In (bv_unsigned ra) URA -> uanchor m SP ra s0.
(* [comment removed for export] *)
Definition uanchor_step_stmt : Prop :=
  forall m SP ra s0 ra' s0', In (bv_unsigned ra) URA -> SP + 16 <= bv_unsigned s0 < 2^47 ->
    rw_cells segs m (bv_unsigned s0 - 16) [C8 s0'; C8 ra'] -> uanchor m (bv_unsigned s0) ra' s0' -> uanchor m SP ra s0.
Definition uanchor_frame_stmt : Prop :=
  forall m m' SP ra s0, (forall a, SP <= a < 2^47 -> m' (wa a) = m (wa a)) -> uanchor m SP ra s0 -> uanchor m' SP ra s0.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition amemcpy_icp_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : APS) (LB : list ablock) (LF : list fblock)
         (dst src n lo : Z) (bs junk : list byte) (bd bsr : ablock) (K : TSet),
  K [] ->
  AHK s LB LF m mo ->
  In bd LB -> ab_addr bd <= dst -> dst + n <= ab_addr bd + ab_size bd ->
  In bsr LB -> ab_addr bsr <= src -> src + n <= ab_addr bsr + ab_size bsr ->
  (dst + n <= src \/ src + n <= dst) -> 0 < n < 2^26 ->
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
Definition aread_rz_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo mo1 : Model) (s : APS) (LB : list ablock) (LF : list fblock)
         (fd buf count lo : Z) (junk : list byte) (b : ablock) (ans : read_ans) (K : TSet),
  K [] ->
  AHK s LB LF m mo ->
  In b LB -> ab_addr b <= buf -> buf + count <= ab_addr b + ab_size b -> 0 < count <= 65536 -> 3 <= fd < 2^32 ->
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
Definition aopen_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : APS) (LB : list ablock) (LF : list fblock)
         (pa lo : Z) (path : list byte) (KA KB : TSet),
  KA [] -> KB [] ->
  AHK s LB LF m mo ->
  bytes_at segs m pa (path ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) path -> usp sp <= pa -> pa + Z.of_nat (length path) + 1 <= 2^47 ->
  path_has_slash path = false ->   (* [comment removed for export] *)
  fd_lookup (m_fds mo) (alloc_fd (m_fds mo)) = None -> 3 <= bv_unsigned (alloc_fd (m_fds mo)) <= 4096 ->
  ST m lo sp -> alloc_ceiling <= lo -> lo <= usp sp - 160 -> tp = wz (c_tp C) ->
  a0 = wz pa -> a1 = wz 0 (* [comment removed for export] *) ->
  (* [comment removed for export] *)
  (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (mo' : Model) (s' : APS) (e : Z),
     (open_classify path mo = OcErrno e \/ (exists ent, open_classify path mo = OcMay ent /\ In e openat_errnos)) ->
     ST m' lo sp -> munch [(lo, usp sp); (c_errno C, c_errno C + 4)] m m' -> wmono segs m m' ->
     AHK s' LB LF m' mo' -> aalloc_same s s' -> SO s' = SO s ->
     m_fs mo' = m_fs mo -> m_fds mo' = m_fds mo -> magree mo mo' ->
     realizes_cfg acfg segs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz (2^64 - 1)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom segs)) mo') KA) ->
  (* [comment removed for export] *)
  (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (mo' : Model) (s' : APS) (ent : FdEntry),
     open_classify path mo = OcMay ent ->
     let fd := alloc_fd (m_fds mo) in
     ST m' lo sp -> munch [(lo, usp sp); (c_errno C, c_errno C + 4)] m m' -> wmono segs m m' ->
     AHK s' LB LF m' mo' -> aalloc_same s s' -> SO s' = SO s ->
     m_fs mo' = m_fs mo -> m_fds mo' = fd_insert (m_fds mo) fd ent -> magree (with_fds (fd_insert (m_fds mo) fd ent) mo) mo' ->
     realizes_cfg acfg segs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 fd a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom segs)) mo') KB) ->
  realizes_cfg acfg segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz (c_open C)) fc None m (seg_rom segs)) mo)
            (match open_classify path mo with OcErrno _ => KA | _ => t_alt2 KA KB end).

Definition aclose_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : APS) (LB : list ablock) (LF : list fblock)
         (fd lo : Z) (K : TSet),
  K [] -> AHK s LB LF m mo -> 3 <= fd < 2^32 ->
  ST m lo sp -> alloc_ceiling <= lo -> lo <= usp sp - 160 -> tp = wz (c_tp C) -> a0 = wz fd ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (mo' : Model) (s' : APS),
     ST m' lo sp -> munch [(lo, usp sp); (c_errno C, c_errno C + 4)] m m' -> wmono segs m m' ->
     AHK s' LB LF m' mo' -> aalloc_same s s' -> SO s' = SO s ->
     m_fs mo' = m_fs mo -> m_fds mo' = m_fds (snd (close_out fd mo)) -> magree (snd (close_out fd mo)) mo' ->
     realizes_cfg acfg segs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom segs)) mo') K) ->
  realizes_cfg acfg segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz (c_close C)) fc None m (seg_rom segs)) mo) K.

(* [comment removed for export] *)
Definition afwrite_diag_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : APS) (LB : list ablock) (LF : list fblock)
         (sa lo : Z) (zs : list Z) (K : TSet),
  K [] -> AHK s LB LF m mo ->
  bytes_at segs m sa (zb zs) -> Forall (fun c => 0 <= c < 256) zs -> 0 < zlength zs < 4096 -> c_img_lo C <= sa ->
  sa + zlength zs <= 0x21060 (* [comment removed for export] *) ->
  ST m lo sp -> alloc_ceiling <= lo -> lo <= usp sp - AICP_STACK -> usp sp < 2^47 -> tp = wz (c_tp C) -> frm0 fc ->
  a0 = wz sa -> a1 = wz (zlength zs) -> a2 = wz 1 -> a3 = wz (c_stderr_F C) ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (mo' : Model) (s' : APS),
     ST m' lo sp -> munch [(lo, usp sp); (c_stderr_F C, c_stderr_F C + 232)] m m' -> wmono segs m m' -> frm0 fc' ->
     AHK s' LB LF m' mo' -> aalloc_same s s' -> SO s' = SO s -> m_fs mo' = m_fs mo -> m_fds mo' = m_fds mo -> magree mo mo' ->
     realizes_cfg acfg segs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (ret_pc ra) fc' None m' (seg_rom segs)) mo') K) ->
  realizes_cfg acfg segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz (c_wrap_fwrite C)) fc None m (seg_rom segs)) mo) (ShapeAlg.t_emit (Wz 2 zs) K).

(* [comment removed for export] *)
Definition adiag_args (d : diag_msg) (m : mem) (fmtp argw : word) (lo SP : Z) : Prop :=
  match d with
  | DUsage zs | DCannotOpen zs | DReadError zs =>
      fmtp = wz (match d with DUsage _ => f_usage FM | DCannotOpen _ => f_cannot_open FM | _ => f_read_error FM end)
      /\ (exists slack : list byte,        (* [comment removed for export] *)
             bytes_at segs m (bv_unsigned argw) (zb zs ++ Z_to_bv 8 0 :: slack)
             /\ (- (bv_unsigned argw + zlength zs + 1)) mod 8 <= zlength slack)
      /\ Forall (fun c => 0 < c < 256) zs /\ zlength zs < 2^20
      /\ SP <= bv_unsigned argw /\ bv_unsigned argw + zlength zs + 16 <= 2^47   (* [comment removed for export] *)
  | DTooBig => fmtp = wz (f_too_big FM) /\ bv_unsigned argw mod 2^32 = 67108864
  | _ => False
  end.
Definition afprintf_diag_stmt : Prop :=
  forall (d : diag_msg) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : APS) (LB : list ablock) (LF : list fblock)
         (lo : Z) (K : TSet),
  K [] -> AHK s LB LF m mo ->
  adiag_args d m a1 a2 lo (usp sp) ->
  ST m lo sp -> alloc_ceiling <= lo -> lo <= usp sp - AICP_STACK -> usp sp < 2^47 -> tp = wz (c_tp C) -> frm0 fc ->
  a0 = wz (c_stderr_F C) ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (mo' : Model) (s' : APS),
     ST m' lo sp -> munch [(lo, usp sp); (c_stderr_F C, c_stderr_F C + 232)] m m' -> wmono segs m m' -> frm0 fc' ->
     AHK s' LB LF m' mo' -> aalloc_same s s' -> SO s' = SO s -> m_fs mo' = m_fs mo -> m_fds mo' = m_fds mo -> magree mo mo' ->
     realizes_cfg acfg segs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (ret_pc ra) fc' None m' (seg_rom segs)) mo') K) ->
  realizes_cfg acfg segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz (c_wrap_fprintf C)) fc None m (seg_rom segs)) mo)
            (ShapeAlg.t_emit (Wz 2 (concat (adiag_pieces d))) K).

(* [comment removed for export] *)
Definition aprintf_rz_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : APS) (LB : list ablock) (LF : list fblock)
         (ap lo : Z) (v1 : word) (K : TSet),
  K [] -> AHK s LB LF m mo ->
  rw_cells segs m ap [C8 v1] -> bv_unsigned v1 mod 2^32 = 0 -> usp sp <= ap -> ap + 56 < 2^47 -> ap mod 8 = 0 ->
  zlength (so_buf (SO s)) <= STDOUT_BUFSIZ ->
  ST m lo sp -> alloc_ceiling <= lo -> lo <= usp sp - AICP_STACK -> usp sp < 2^47 -> tp = wz (c_tp C) -> frm0 fc ->
  a0 = wz (f_emit FM) -> a1 = wz ap ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (mo' : Model) (s' : APS),
     ST m' lo sp -> munch [(lo, usp sp); (c_stdout_F C, c_stdout_F C + 232); (c_stdout_buf C, c_stdout_buf C + 1024)] m m' -> wmono segs m m' -> frm0 fc' ->
     AHK s' LB LF m' mo' -> aalloc_same s s' -> SO s' = snd (vprintf_pure (SO s) (pieces_emit_d 0)) -> m_fs mo' = m_fs mo -> m_fds mo' = m_fds mo -> magree mo mo' ->
     realizes_cfg acfg segs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (ret_pc ra) fc' None m' (seg_rom segs)) mo') K) ->
  realizes_cfg acfg segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz (c_wrap_vprintf C)) fc None m (seg_rom segs)) mo)
            (ShapeAlg.t_emit (Wz 1 (fst (vprintf_pure (SO s) (pieces_emit_d 0)))) K).

(* [comment removed for export] *)
Definition aexit_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : APS) (LB : list ablock) (LF : list fblock)
         (code lo : Z),
  AHK s LB LF m mo -> 0 <= code < 2^32 -> zlength (so_buf (SO s)) <= STDOUT_BUFSIZ ->
  ST m lo sp -> alloc_ceiling <= lo -> lo <= usp sp - AEXIT_STACK -> usp sp < 2^47 -> tp = wz (c_tp C) -> frm0 fc -> a0 = wz code ->
  realizes_cfg acfg segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz (c_exit C)) fc None m (seg_rom segs)) mo)
            (ShapeAlg.t_emit (Wz 1 (fst (exit_flush_pure (SO s)))) (t_exit (bv_and (wz code) (wz 255)) (m_fs mo))).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ayfuzz_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : APS) (LB : list ablock)
         (T n lo : Z) (txt : list byte) (K : TSet),
  K [] -> AHK s LB [] m mo ->
  bytes_at segs m T txt -> Z.of_nat (length txt) = n -> 0 <= n < 2^26 ->
  ((exists b, In b LB /\ ab_addr b <= T /\ T + n <= ab_addr b + ab_size b) \/ (n = 0 /\ T = c_empty C)) ->
  nbig LB <= 7900 ->
  ST m lo sp -> alloc_ceiling <= lo -> lo <= usp sp - AYFUZZ_STACK -> usp sp mod 16 = 0 -> usp sp < 2^47 ->
  tp = wz (c_tp C) -> gp = wz 0x10800 -> uanchor m (usp sp) ra s0 -> frm0 fc ->
  a0 = wz T -> a1 = wz n -> ycost n <= acredit s ->
  (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (mo' : Model) (s' : APS),
     ST m' lo sp -> aheap_pres LB [] (usp sp) m m' -> (* [comment removed for export] *) frm0 fc' -> SO s' = SO s ->
     AHK s' LB [] m' mo' -> ayfuzz_rel s mo s' mo' -> m_fs mo' = m_fs mo -> m_fds mo' = m_fds mo -> acredit s - ycost n <= acredit s' ->
     realizes_cfg acfg segs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (ret_pc ra) fc' None m' (seg_rom segs)) mo') K) ->
  realizes_cfg acfg segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz (c_yfuzz C)) fc None m (seg_rom segs)) mo) K.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Variable AT_MAIN : mem -> Model -> Prop.
Variable aps_init : mem -> Model -> APS.
Definition AHK_init_stmt : Prop :=
  forall m mo, AT_MAIN m mo ->
    AHK (aps_init m mo) [] [] m mo /\ SO (aps_init m mo) = stdout_init /\ AHEAD 40%nat [] [] (aps_init m mo) mo /\ acredit (aps_init m mo) = ACREDIT0.

End Stmts.

(* [comment removed for export] *)
Record adrv_params : Type := mkADrvParams {
  p_APS : Type;
  p_AHK : p_APS -> list ablock -> list fblock -> mem -> Model -> Prop;
  p_SO : p_APS -> stdout_st;
  p_aS : p_APS -> word -> Prop;  p_aN : p_APS -> nat;  p_aEB : p_APS -> Z;
  p_amalloc_rel : Z -> p_APS -> Model -> option Z -> p_APS -> Model -> Prop;
  p_afree_rel : Z -> p_APS -> Model -> p_APS -> Model -> Prop;
  p_ayfuzz_rel : p_APS -> Model -> p_APS -> Model -> Prop;
  p_aalloc_same : p_APS -> p_APS -> Prop;
  p_arealloc_rel : Z -> Z -> p_APS -> Model -> option Z -> p_APS -> Model -> Prop;
  p_acredit : p_APS -> Z;
  p_acharge : Z -> Z;
  p_arefund : Z -> Z;
  p_uanchor : mem -> Z -> word -> word -> Prop;
  p_URA : list Z;
  p_AHEAD : nat -> list (Z * Z) -> list aevent -> p_APS -> Model -> Prop
}.

Record a_drv_iface (segs : list Segment) (C : adrv_consts) (FM : adrv_fmts) (D : adrv_params) : Prop := mkADrvIface {
  adi_kip      : AHK_kip_stmt C (p_APS D) (p_AHK D) (p_aS D) (p_aN D) (p_aEB D);
  adi_mem_inv  : AHK_mem_inv_stmt segs (p_APS D) (p_AHK D);
  adi_perm     : AHK_perm_stmt (p_APS D) (p_AHK D);
  adi_frame    : AHK_frame_stmt segs C (p_APS D) (p_AHK D);
  adi_vmsame   : AHK_vmsame_stmt (p_APS D) (p_AHK D);
  adi_blocks   : AHK_blocks_stmt C (p_APS D) (p_AHK D);
  adi_so       : AHK_so_stmt (p_APS D) (p_AHK D) (p_SO D);
  adi_charge   : acharge_bound_stmt (p_acharge D) (p_arefund D);
  adi_asame_refl : aalloc_same_refl_stmt (p_APS D) (p_aalloc_same D);
  adi_uras     : forall z, In z (c_uras C) -> In z (p_URA D);
  adi_uanchor  : uanchor_triv_stmt (p_uanchor D) (p_URA D);
  adi_uanchor_step : uanchor_step_stmt segs (p_uanchor D) (p_URA D);
  adi_uanchor_frame : uanchor_frame_stmt (p_uanchor D);
  adi_free     : afree_rz_stmt segs C (p_APS D) (p_AHK D) (p_SO D) (p_afree_rel D) (p_acredit D) (p_arefund D) (p_uanchor D);
  adi_malloc   : amalloc_rz_stmt segs C (p_APS D) (p_AHK D) (p_SO D) (p_amalloc_rel D) (p_acredit D) (p_acharge D) (p_uanchor D);
  adi_realloc  : arealloc_rz_stmt segs C (p_APS D) (p_AHK D) (p_SO D) (p_arealloc_rel D) (p_acredit D) (p_acharge D) (p_arefund D) (p_uanchor D);
  adi_realloc0 : arealloc_null_rz_stmt segs C (p_APS D) (p_AHK D) (p_SO D) (p_arealloc_rel D) (p_acredit D) (p_acharge D) (p_uanchor D);
  adi_memcpy   : amemcpy_icp_stmt segs C (p_APS D) (p_AHK D) (p_SO D) (p_aalloc_same D);
  adi_read     : aread_rz_stmt segs C (p_APS D) (p_AHK D) (p_SO D) (p_aalloc_same D);
  adi_open     : aopen_stmt segs C (p_APS D) (p_AHK D) (p_SO D) (p_aalloc_same D);
  adi_close    : aclose_stmt segs C (p_APS D) (p_AHK D) (p_SO D) (p_aalloc_same D);
  adi_fwrite   : afwrite_diag_stmt segs C (p_APS D) (p_AHK D) (p_SO D) (p_aalloc_same D);
  adi_fprintf  : afprintf_diag_stmt segs C FM (p_APS D) (p_AHK D) (p_SO D) (p_aalloc_same D);
  adi_printf   : aprintf_rz_stmt segs C FM (p_APS D) (p_AHK D) (p_SO D) (p_aalloc_same D);
  adi_yfuzz    : ayfuzz_stmt segs C (p_APS D) (p_AHK D) (p_SO D) (p_ayfuzz_rel D) (p_acredit D) (p_uanchor D);
  adi_hd_malloc : ahead_malloc_stmt (p_APS D) (p_amalloc_rel D) (p_AHEAD D);
  adi_hd_free  : ahead_free_stmt (p_APS D) (p_afree_rel D) (p_AHEAD D);
  adi_hd_free0 : ahead_free0_stmt (p_APS D) (p_afree_rel D) (p_AHEAD D);
  adi_hd_perm  : ahead_perm_stmt (p_APS D) (p_AHEAD D);
  adi_hd_weaken : ahead_weaken_stmt (p_APS D) (p_AHEAD D);
  adi_hd_yfuzz : ahead_yfuzz_stmt (p_APS D) (p_ayfuzz_rel D) (p_AHEAD D);
  adi_hd_magree : ahead_magree_stmt (p_APS D) (p_AHEAD D);
  adi_hd_vmsame : ahead_vmsame_stmt (p_APS D) (p_AHEAD D);
  adi_hd_aps   : ahead_aps_stmt (p_APS D) (p_aalloc_same D) (p_AHEAD D);
  adi_hd_cmalloc : ahead_credit_malloc_stmt (p_APS D) (p_acredit D) (p_acharge D) (p_AHEAD D);
  adi_hd_cfree : ahead_credit_free_stmt (p_APS D) (p_acredit D) (p_AHEAD D);
  adi_hd_reserve : ahead_reserve_stmt (p_APS D) (p_acredit D) (p_AHEAD D);
  adi_hd_cyfuzz : ahead_credit_yfuzz_stmt (p_APS D) (p_acredit D) (p_AHEAD D)
}.
(* [comment removed for export] *)
End RC__1.
