(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr SysStep Exec CellsX TacX.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_Rep ECH_LibState
     ECH_C1_stmt ECH_C3_stmt ECH_C6_stmt.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
From Stdlib Require Import Sorting.Permutation.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
Definition MEMINIT_STACK : Z := FR_mem_new + FR_mem_init + Z.max CZALLOC_STACK BUFNEW_STACK.
Definition BIONEW_STACK (ph : ctxphase) : Z := FR_BIO_new + FR_BIO_new_ex + Z.max CZALLOC_STACK (Z.max (CNEWEX_STACK ph) MEMINIT_STACK).
Definition NEWMEMBUF_STACK (ph : ctxphase) : Z := FR_BIO_new_mem_buf + BIONEW_STACK ph.
Definition MEMREAD_STACK : Z := FR_mem_read + BIOACC_STACK.                       (* [comment removed for export] *)
Definition MEMCTRL_STACK : Z := FR_mem_ctrl.
Definition BIOCTRL_STACK : Z := FR_BIO_ctrl + MEMCTRL_STACK.
Definition BIOEOF_STACK : Z := FR_BIO_eof + BIOCTRL_STACK.
Definition BREADCONV_STACK : Z := FR_bread_conv + Z.max MEMREAD_STACK BIOCTRL_STACK.
Definition READINTERN_STACK : Z := FR_bio_read_intern + Z.max BREADCONV_STACK BIOEOF_STACK.
Definition BIOREADEX_STACK : Z := FR_BIO_set_data + READINTERN_STACK.               (* [comment removed for export] *)
Definition BIOREAD_STACK : Z := FR_BIO_read + READINTERN_STACK.
Definition MEMFREE_STACK : Z := FR_mem_free + Z.max (FR_mem_buf_free + BUFFREE_STACK) CFREE_STACK.
Definition BIOFREE_STACK : Z := FR_BIO_free + FR_BIO_free_int + Z.max MEMFREE_STACK (Z.max CFREEEX_STACK CFREE_STACK).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition MEMBIO_below (a : Z) (R : membio) (lo : Z) : Prop :=
  a + BIO_SIZE <= lo /\ mb_bb R + BIOBUFMEM_SIZE <= lo /\ mb_bm R + BUFMEM_SIZE <= lo /\ mb_rp R + BUFMEM_SIZE <= lo.
(* [comment removed for export] *)
Definition memrd_out (a : Z) (R : membio) (out outl lo sp : Z) : Prop :=
     (out + outl <= lo \/ sp <= out) /\ 0 < out /\ out + outl <= 2^64        (* [comment removed for export] *)
  /\ Forall (fun b => out + outl <= blk_addr b \/ blk_addr b + blk_size b <= out) (blocks_MEMBIO a R)
  /\ (mb_buf R + mb_len R <= out \/ out + outl <= mb_buf R)
  /\ (out + outl <= A_mem_buf_method + O_METH_BREAD \/ A_mem_buf_method + O_METH_BREAD + 64 <= out).   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition mb_take (R : membio) (ds : list byte) (n : Z) : list byte := firstn (Z.to_nat n) (skipn (Z.to_nat (mb_pos R)) ds).
Definition mb_avail (R : membio) : Z := mb_len R - mb_pos R.
Definition mb_rdn (R : membio) (outl : Z) : Z := Z.min outl (mb_avail R).
Definition mb_after_read (R : membio) (n : Z) : membio := mb_advance R n (Z.land (mb_flags R) (Z.lnot BIO_FLAGS_RETRY_MASK)).
(* [comment removed for export] *)
Definition mb_after_bread (R : membio) (n : Z) : membio :=
  mkMB (mb_buf R) (mb_len R) (mb_pos R + n) (Z.land (mb_flags R) (Z.lnot BIO_FLAGS_RETRY_MASK)) (mb_numf R) (mb_nread R)
       (mb_next R) (mb_prev R) (mb_bb R) (mb_bm R) (mb_rp R) (mb_id R) (mb_bbid R) (mb_bmid R) (mb_rpid R).
Definition mem_ctrl_rv (R : membio) (cmd : Z) : Z := if cmd =? BIO_CTRL_EOF then (if mb_avail R =? 0 then 1 else 0) else 0.

Section W.
  Variable H : hsr.

  (* [comment removed for export] *)
  Definition memrd_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (LB : list block) (rv : Z) (a : Z) (R' : membio) (ds : list byte)
      (out : Z) (data : list byte) (outl : Z) (rb : option (Z * Z)) (W : list (Z * Z)) (lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' junk',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ munch ((lo, bv_unsigned sp) :: W) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
      /\ MEMBIO LB m' a R' /\ bytes_at rsegs m' (mb_buf R') ds
      /\ rw_cells rsegs m' out [CB (length data) data; CB (Z.to_nat outl - length data) junk']
      /\ match rb with None => True | Some (rbp, v) => rw_cells rsegs m' rbp [C8 (wz v)] end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition memread_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list block) (a out outl lo : Z) (R : membio) (ds junk : list byte),
      a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 out -> a2 = Z_to_bv 64 outl -> 0 < outl < 2^31 ->
      MEMBIO LB m a R -> MEMBIO_below a R lo -> MEMBIO_sep a R -> bytes_at rsegs m (mb_buf R) ds -> Z.of_nat (length ds) = mb_len R ->
      rw_cells rsegs m out [CB (Z.to_nat outl) junk] -> memrd_out a R out outl lo (bv_unsigned sp) ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - MEMREAD_STACK -> mem_inv rsegs m -> bv_unsigned ra mod 2 = 0 ->
      evt rsegs (memrd_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB (mb_rdn R outl) a (mb_after_bread R (mb_rdn R outl)) ds
                   out (mb_take R ds (mb_rdn R outl)) outl None ((out, out + outl) :: MEMBIO_foot a R) lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_mem_read) fc None m (seg_rom rsegs)).

  (* [comment removed for export] *)
  Definition memctrl_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (LB : list block) (rv a : Z) (R : membio) (lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ munch [(lo, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
      /\ MEMBIO LB m' a R.
  Definition memctrl_stmt_at (entry stack : Z) (needs_meth : bool) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list block) (a cmd larg parg lo : Z) (R : membio),
      a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 cmd -> a2 = Z_to_bv 64 larg -> a3 = Z_to_bv 64 parg ->
      (cmd = BIO_CTRL_EOF \/ cmd = BIO_CTRL_PUSH) -> 0 <= larg < 2^63 -> 0 <= parg < 2^64 ->
      MEMBIO LB m a R -> MEMBIO_below a R lo -> MEMBIO_sep a R -> (needs_meth = true -> METH_mem m) ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - stack -> mem_inv rsegs m -> bv_unsigned ra mod 2 = 0 ->
      evt rsegs (memctrl_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB (mem_ctrl_rv R cmd) a R lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 entry) fc None m (seg_rom rsegs)).
  Definition memctrl_stmt : Prop := memctrl_stmt_at P_mem_ctrl MEMCTRL_STACK false.
  Definition bioctrl_mem_stmt : Prop := memctrl_stmt_at P_BIO_ctrl BIOCTRL_STACK true.

  (* [comment removed for export] *)
  Definition bioeof_mem_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list block) (a lo : Z) (R : membio),
      a0 = Z_to_bv 64 a -> MEMBIO LB m a R -> MEMBIO_below a R lo -> MEMBIO_sep a R -> METH_mem m ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - BIOEOF_STACK -> mem_inv rsegs m -> bv_unsigned ra mod 2 = 0 ->
      evt rsegs (memctrl_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB (mem_ctrl_rv R BIO_CTRL_EOF) a R lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_BIO_eof) fc None m (seg_rom rsegs)).

  (* [comment removed for export] *)
  Definition rd_ok (n : Z) : Z := if 0 <? n then 1 else 0.
  Definition breadconv_mem_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list block) (a out outl rbp rbv lo : Z) (R : membio) (ds junk : list byte),
      a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 out -> a2 = Z_to_bv 64 outl -> a3 = Z_to_bv 64 rbp -> 0 < outl < 2^31 ->
      MEMBIO LB m a R -> MEMBIO_below a R lo -> MEMBIO_sep a R -> METH_mem m -> bytes_at rsegs m (mb_buf R) ds -> Z.of_nat (length ds) = mb_len R ->
      rw_cells rsegs m out [CB (Z.to_nat outl) junk] -> memrd_out a R out outl lo (bv_unsigned sp) ->
      rw_cells rsegs m rbp [C8 (wz rbv)] -> memrd_out a R rbp 8 lo (bv_unsigned sp) -> (rbp + 8 <= out \/ out + outl <= rbp) ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - BREADCONV_STACK -> mem_inv rsegs m -> bv_unsigned ra mod 2 = 0 ->
      evt rsegs (memrd_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB (rd_ok (mb_rdn R outl)) a
                   (mb_after_bread R (mb_rdn R outl)) ds out (mb_take R ds (mb_rdn R outl)) outl (Some (rbp, mb_rdn R outl))
                   ((out, out + outl) :: (rbp, rbp + 8) :: MEMBIO_foot a R) lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_bread_conv) fc None m (seg_rom rsegs)).

  (* [comment removed for export] *)
  Definition readintern_mem_stmt_at (entry stack : Z) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list block) (a out outl rbp rbv lo : Z) (R : membio) (ds junk : list byte),
      a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 out -> a2 = Z_to_bv 64 outl -> a3 = Z_to_bv 64 rbp -> 0 < outl < 2^31 ->
      MEMBIO LB m a R -> MEMBIO_below a R lo -> MEMBIO_sep a R -> METH_mem m -> bytes_at rsegs m (mb_buf R) ds -> Z.of_nat (length ds) = mb_len R ->
      rw_cells rsegs m out [CB (Z.to_nat outl) junk] -> memrd_out a R out outl lo (bv_unsigned sp) ->
      rw_cells rsegs m rbp [C8 (wz rbv)] -> memrd_out a R rbp 8 lo (bv_unsigned sp) -> (rbp + 8 <= out \/ out + outl <= rbp) ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - stack -> mem_inv rsegs m -> bv_unsigned ra mod 2 = 0 ->
      evt rsegs (memrd_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB (rd_ok (mb_rdn R outl)) a
                   (mb_after_read R (mb_rdn R outl)) ds out (mb_take R ds (mb_rdn R outl)) outl (Some (rbp, mb_rdn R outl))
                   ((out, out + outl) :: (rbp, rbp + 8) :: MEMBIO_foot a R) lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 entry) fc None m (seg_rom rsegs)).
  Definition readintern_mem_stmt : Prop := readintern_mem_stmt_at P_bio_read_intern READINTERN_STACK.
  Definition bioreadex_mem_stmt : Prop := readintern_mem_stmt_at P_BIO_read_ex BIOREADEX_STACK.

  (* [comment removed for export] *)
  Definition bioread_mem_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list block) (a out outl lo : Z) (R : membio) (ds junk : list byte),
      a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 out -> a2 = Z_to_bv 64 outl -> 0 < outl < 2^31 ->
      MEMBIO LB m a R -> MEMBIO_below a R lo -> MEMBIO_sep a R -> METH_mem m -> bytes_at rsegs m (mb_buf R) ds -> Z.of_nat (length ds) = mb_len R ->
      rw_cells rsegs m out [CB (Z.to_nat outl) junk] -> memrd_out a R out outl lo (bv_unsigned sp) ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - BIOREAD_STACK -> mem_inv rsegs m -> bv_unsigned ra mod 2 = 0 ->
      evt rsegs (memrd_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB (mb_rdn R outl) a
                   (mb_after_read R (mb_rdn R outl)) ds out (mb_take R ds (mb_rdn R outl)) outl None
                   ((out, out + outl) :: MEMBIO_foot a R) lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_BIO_read) fc None m (seg_rom rsegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition newmembuf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : PState) (LB : list block) (ph : ctxphase) (buf len lo B : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun k => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : PState) (LBN : list block) (x : ctxinfo) (a : Z) (R : membio),
      let LB' := blocks_MEMBIO a R ++ LBN ++ LB in
      cfg_ms k = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ hs_KREL H s' (cfg_model k) /\ hs_MPRES H mo (cfg_model k)
      /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\ rw_cells rsegs m' (errno_addr tp) [C4 errv'] /\ hs_rauxv_ok H m' B
      /\ hs_RHEAP H s' LB' m' /\ ctxph_delta ph LBN x /\ CTXPH LB' m' (CtxReady x) /\ (ph = CtxFresh -> CTX_keys m')
      /\ MEMBIO LB' m' a R /\ mb_buf R = buf /\ mb_len R = len /\ mb_pos R = 0 /\ mb_nread R = 0 /\ mb_next R = 0 /\ mb_prev R = 0 /\ 0 < a /\ MEMBIO_apart a R
      /\ MEMFLAG m' 1 /\ IMPL_mem m' /\ GOT_mem m' /\ METH_mem m' /\ relro_lib m'
      /\ xpres LB (bv_unsigned sp) (memflag_foot ++ ctxph_foot ph) m m'.   (* [comment removed for export] *)
  Definition newmembuf_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState) (LB : list block) (ph : ctxphase)
           (buf len v lo B : Z) (errv : word),
      a0 = Z_to_bv 64 buf -> a1 = Z_to_bv 64 len -> 0 < buf -> buf + len <= hceil -> 0 <= len < 2^31 ->
      hs_RHEAP H s LB m -> hs_KREL H s mo ->
      lb_bytes LB + ctxph_bytes ph + MEMBIO_BYTES <= hs_LIVE_MAX H -> Z.of_nat (length LB) + ctxph_cnt ph + 4 <= hs_LIVE_CNT_MAX H ->
      lb_big LB + ctxph_big ph <= hs_LIVE_BIG_MAX H ->
      hs_rauxv_ok H m B -> bv_unsigned sp <= B -> bv_unsigned sp mod 16 = 0 ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - NEWMEMBUF_STACK ph ->
      rw_cells rsegs m (errno_addr tp) [C4 errv] -> mem_inv rsegs m -> tp = Z_to_bv 64 RATP ->
      MEMFLAG m v -> IMPL_mem m -> GOT_mem m -> METH_mem m -> relro_lib m -> CTXPH LB m ph -> bv_unsigned ra mod 2 = 0 ->
      hs_SR H (newmembuf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB ph buf len lo B m mo)
        (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_BIO_new_mem_buf) fc None m (seg_rom rsegs)) mo).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition biofree_mem_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : PState) (LB : list block) (a : Z) (R : membio) (lo B : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun k => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : PState) (LBr : list block),
      cfg_ms k = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ hs_KREL H s' (cfg_model k) /\ hs_MPRES H mo (cfg_model k)
      /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\ rw_cells rsegs m' (errno_addr tp) [C4 errv'] /\ hs_rauxv_ok H m' B
      /\ hs_RHEAP H s' LBr m' /\ Permutation LB (blocks_MEMBIO a R ++ LBr)
      /\ IMPL_mem m' /\ GOT_mem m' /\ METH_mem m'
      /\ xpres LBr (bv_unsigned sp) [] m m'.
  Definition biofree_mem_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState) (LB : list block) (x : ctxinfo)
           (a lo B : Z) (R : membio) (errv : word),
      a0 = Z_to_bv 64 a -> MEMBIO LB m a R -> MEMBIO_apart a R -> CTXPH LB m (CtxReady x) ->
      hs_RHEAP H s LB m -> hs_KREL H s mo ->
      hs_rauxv_ok H m B -> bv_unsigned sp <= B ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - BIOFREE_STACK ->
      rw_cells rsegs m (errno_addr tp) [C4 errv] -> mem_inv rsegs m -> tp = Z_to_bv 64 RATP ->
      IMPL_mem m -> GOT_mem m -> METH_mem m -> bv_unsigned ra mod 2 = 0 ->
      hs_SR H (biofree_mem_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB a R lo B m mo)
        (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_BIO_free) fc None m (seg_rom rsegs)) mo).
  (* [comment removed for export] *)

  Definition C7_stmts : Prop :=
    memread_stmt /\ memctrl_stmt /\ bioctrl_mem_stmt /\ bioeof_mem_stmt /\ breadconv_mem_stmt
    /\ readintern_mem_stmt /\ bioreadex_mem_stmt /\ bioread_mem_stmt /\ newmembuf_stmt /\ biofree_mem_stmt.
End W.
End HCW.
