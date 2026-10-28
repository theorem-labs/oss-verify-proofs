(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr SysStep Exec CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsStack0 ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface ECH_AKit ECH_AStmt_C1 ECH_AStmt_C3 ECH_AStmt_C6.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From Stdlib Require Import Sorting.Permutation.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
Definition MEMREAD_STACK : Z := FR_mem_read + AINTRIN_STACK.                      (* [comment removed for export] *)
Definition MEMCTRL_STACK : Z := FR_mem_ctrl.
Definition BIOCTRL_STACK : Z := FR_BIO_ctrl + MEMCTRL_STACK.
Definition BIOEOF_STACK : Z := FR_BIO_eof + BIOCTRL_STACK.
Definition BREADCONV_STACK : Z := FR_bread_conv + Z.max MEMREAD_STACK BIOCTRL_STACK.
Definition READINTERN_STACK : Z := FR_bio_read_intern + Z.max BREADCONV_STACK BIOEOF_STACK.
Definition BIOREADEX_STACK : Z := FR_BIO_set_data + READINTERN_STACK.               (* [comment removed for export] *)
Definition BIOREAD_STACK : Z := FR_BIO_read + 16 + Z.max AFS_STACK READINTERN_STACK.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition MEMINIT_STACK : Z := FR_mem_init + Z.max CZALLOC_STACK (Z.max BUFNEW_STACK AINTRIN_STACK).
Definition BIONEW_STACK (ph : ctxphase) : Z := FR_BIO_new_ex + Z.max CZALLOC_STACK (Z.max (CNEWEX_STACK ph) MEMINIT_STACK).
Definition NEWMEMBUF_STACK (ph : ctxphase) : Z := FR_BIO_new_mem_buf + Z.max (BIONEW_STACK ph) AINTRIN_STACK.
Definition MEMFREE_STACK : Z := FR_mem_free + Z.max (FR_mem_buf_free + BUFFREE_STACK) CFREE_STACK.
Definition BIOFREEINT_STACK : Z := FR_BIO_free_int + Z.max MEMFREE_STACK (Z.max CFREEEX_STACK CFREE_STACK).
Definition BIOFREE_STACK : Z := FR_BIO_free + BIOFREEINT_STACK.
(* [comment removed for export] *)
Definition R_BIO_new_mem_buf_BIO_new : Z := 0x4170e4.          Definition R_BIO_new_mem_buf_asan_memcpy : Z := 0x4171a0.
Definition R_BIO_new_ex_CRYPTO_zalloc : Z := 0x236c64.          Definition R_BIO_new_ex_CRYPTO_new_ex_data : Z := 0x236cf0.
Definition R_BIO_new_ex_create : Z := 0x236d24.
Definition R_mem_init_CRYPTO_zalloc : Z := 0x418608.            Definition R_mem_init_BUF_MEM_new : Z := 0x41861c.
Definition R_mem_init_CRYPTO_zalloc_2 : Z := 0x418654.          Definition R_mem_init_asan_memcpy : Z := 0x418688.
Definition R_BIO_free_BIO_free_int : Z := 0x236e68.             Definition R_BIO_free_int_destroy : Z := 0x236fb8.
Definition R_BIO_free_int_CRYPTO_free_ex_data : Z := 0x236fc8.  Definition R_BIO_free_int_CRYPTO_free : Z := 0x236fdc.
Definition R_mem_free_mem_buf_free : Z := 0x418174.             Definition R_mem_free_CRYPTO_free : Z := 0x4181b0.
Definition R_mem_free_CRYPTO_free_2 : Z := 0x4181c4.            Definition R_mem_buf_free_BUF_MEM_free : Z := 0x3f0c34.
(* [comment removed for export] *)
Definition PF_meminit : list (Z * list Z) :=
  pf_shift R_mem_init_CRYPTO_zalloc PF_czalloc ++ pf_shift R_mem_init_BUF_MEM_new PF_bufnew ++ pf_shift R_mem_init_CRYPTO_zalloc_2 PF_czalloc.
Definition PF_bionewex (ph : ctxphase) : list (Z * list Z) :=
  pf_shift R_BIO_new_ex_CRYPTO_zalloc PF_czalloc ++ pf_shift R_BIO_new_ex_CRYPTO_new_ex_data (PF_ctx ph) ++ pf_shift R_BIO_new_ex_create PF_meminit.
Definition PF_newmembuf (ph : ctxphase) : list (Z * list Z) := pf_shift R_BIO_new_mem_buf_BIO_new (PF_bionewex ph).
Definition PF_memfree : list (Z * list Z) :=
  pf_shift R_mem_free_mem_buf_free PF_buffree
  ++ pf_shift R_mem_free_CRYPTO_free PF_cfree ++ pf_shift R_mem_free_CRYPTO_free_2 PF_cfree.
Definition PF_biofreeint : list (Z * list Z) := pf_shift R_BIO_free_int_destroy PF_memfree ++ pf_shift R_BIO_free_int_CRYPTO_free PF_cfree.
Definition PF_biofree : list (Z * list Z) := pf_shift R_BIO_free_BIO_free_int PF_biofreeint.

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
Definition MEMBIO_shad (m : mem) (a : Z) (R : membio) : Prop :=
  addressable m a BIO_SIZE /\ addressable m (mb_bb R) BIOBUFMEM_SIZE /\ addressable m (mb_bm R) BUFMEM_SIZE /\ addressable m (mb_rp R) BUFMEM_SIZE.
Definition PAYLOAD_shad (m : mem) (R : membio) : Prop :=
  accessible m (mb_buf R) (mb_len R) /\ shvis m (mb_buf R) (mb_buf R + mb_len R) /\ in_app_mem (mb_buf R) (mb_buf R + mb_len R).
Definition OUT_shad (m : mem) (out outl : Z) : Prop :=
  accessible m out outl /\ shvis m out (out + outl) /\ in_app_mem out (out + outl) /\ aconst_ok (out, out + outl).
(* [comment removed for export] *)
Definition RB_shad (m : mem) (rbp : Z) : Prop :=
  accessible m rbp 8 /\ in_app_mem rbp (rbp + 8) /\ aconst_ok (rbp, rbp + 8).
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
  Variable H : asr.

  (* [comment removed for export] *)
  Definition memrd_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (LB : list block) (rv : Z) (a : Z) (R' : membio) (ds : list byte)
      (out : Z) (data : list byte) (outl : Z) (rb : option (Z * Z)) (W : list (Z * Z)) (lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' junk',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch ((lo, bv_unsigned sp) :: W) m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ ACONST m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ MEMBIO H LB m' a R' /\ bytes_at asegs m' (mb_buf R') ds
      /\ rw_cells asegs m' out [CB (length data) data; CB (Z.to_nat outl - length data) junk']
      /\ match rb with None => True | Some (rbp, v) => rw_cells asegs m' rbp [C8 (wz v)] end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition memread_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list block) (a out outl lo : Z) (R : membio) (ds junk : list byte),
      a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 out -> a2 = Z_to_bv 64 outl -> 0 < outl < 2^31 ->
      MEMBIO H LB m a R -> MEMBIO_below a R lo -> MEMBIO_sep a R -> bytes_at asegs m (mb_buf R) ds -> Z.of_nat (length ds) = mb_len R ->
      rw_cells asegs m out [CB (Z.to_nat outl) junk] -> memrd_out a R out outl lo (bv_unsigned sp) ->
      MEMBIO_shad m a R -> PAYLOAD_shad m R -> OUT_shad m out outl -> ACONST m ->                       (* [comment removed for export] *)
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - MEMREAD_STACK -> mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
      evt asegs (memrd_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB (mb_rdn R outl) a (mb_after_bread R (mb_rdn R outl)) ds
                   out (mb_take R ds (mb_rdn R outl)) outl None ((out, out + outl) :: MEMBIO_foot a R) lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_mem_read) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition memctrl_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (LB : list block) (rv a : Z) (R : membio) (lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(lo, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ ACONST m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ MEMBIO H LB m' a R.
  Definition memctrl_stmt_at (entry stack : Z) (needs_meth : bool) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list block) (a cmd larg parg lo : Z) (R : membio),
      a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 cmd -> a2 = Z_to_bv 64 larg -> a3 = Z_to_bv 64 parg ->
      (cmd = BIO_CTRL_EOF \/ cmd = BIO_CTRL_PUSH) -> 0 <= larg < 2^63 -> 0 <= parg < 2^64 ->
      MEMBIO H LB m a R -> MEMBIO_below a R lo -> MEMBIO_sep a R -> (needs_meth = true -> METH_mem m) ->
      MEMBIO_shad m a R -> ACONST m ->                                                                   (* [comment removed for export] *)
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - stack -> mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
      evt asegs (memctrl_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB (mem_ctrl_rv R cmd) a R lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).
  Definition memctrl_stmt : Prop := memctrl_stmt_at P_mem_ctrl MEMCTRL_STACK false.
  Definition bioctrl_mem_stmt : Prop := memctrl_stmt_at P_BIO_ctrl BIOCTRL_STACK true.

  (* [comment removed for export] *)
  Definition bioeof_mem_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list block) (a lo : Z) (R : membio),
      a0 = Z_to_bv 64 a -> MEMBIO H LB m a R -> MEMBIO_below a R lo -> MEMBIO_sep a R -> METH_mem m ->
      MEMBIO_shad m a R -> ACONST m ->                                                                   (* [comment removed for export] *)
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - BIOEOF_STACK -> mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
      evt asegs (memctrl_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB (mem_ctrl_rv R BIO_CTRL_EOF) a R lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_BIO_eof) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition rd_ok (n : Z) : Z := if 0 <? n then 1 else 0.
  Definition breadconv_mem_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list block) (a out outl rbp rbv lo : Z) (R : membio) (ds junk : list byte),
      a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 out -> a2 = Z_to_bv 64 outl -> a3 = Z_to_bv 64 rbp -> 0 < outl < 2^31 ->
      MEMBIO H LB m a R -> MEMBIO_below a R lo -> MEMBIO_sep a R -> METH_mem m -> bytes_at asegs m (mb_buf R) ds -> Z.of_nat (length ds) = mb_len R ->
      rw_cells asegs m out [CB (Z.to_nat outl) junk] -> memrd_out a R out outl lo (bv_unsigned sp) -> rbp mod 8 = 0 ->
      rw_cells asegs m rbp [C8 (wz rbv)] -> memrd_out a R rbp 8 lo (bv_unsigned sp) -> (rbp + 8 <= out \/ out + outl <= rbp) ->
      MEMBIO_shad m a R -> PAYLOAD_shad m R -> OUT_shad m out outl -> RB_shad m rbp -> ACONST m ->                   (* [comment removed for export] *)
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - BREADCONV_STACK -> mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
      evt asegs (memrd_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB (rd_ok (mb_rdn R outl)) a
                   (mb_after_bread R (mb_rdn R outl)) ds out (mb_take R ds (mb_rdn R outl)) outl (Some (rbp, mb_rdn R outl))
                   ((out, out + outl) :: (rbp, rbp + 8) :: MEMBIO_foot a R) lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_bread_conv) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition readintern_mem_stmt_at (entry stack : Z) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list block) (a out outl rbp rbv lo : Z) (R : membio) (ds junk : list byte),
      a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 out -> a2 = Z_to_bv 64 outl -> a3 = Z_to_bv 64 rbp -> 0 < outl < 2^31 ->
      MEMBIO H LB m a R -> MEMBIO_below a R lo -> MEMBIO_sep a R -> METH_mem m -> bytes_at asegs m (mb_buf R) ds -> Z.of_nat (length ds) = mb_len R ->
      rw_cells asegs m out [CB (Z.to_nat outl) junk] -> memrd_out a R out outl lo (bv_unsigned sp) -> rbp mod 8 = 0 ->
      rw_cells asegs m rbp [C8 (wz rbv)] -> memrd_out a R rbp 8 lo (bv_unsigned sp) -> (rbp + 8 <= out \/ out + outl <= rbp) ->
      MEMBIO_shad m a R -> PAYLOAD_shad m R -> OUT_shad m out outl -> RB_shad m rbp -> ACONST m ->                   (* [comment removed for export] *)
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - stack -> mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
      evt asegs (memrd_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB (rd_ok (mb_rdn R outl)) a
                   (mb_after_read R (mb_rdn R outl)) ds out (mb_take R ds (mb_rdn R outl)) outl (Some (rbp, mb_rdn R outl))
                   ((out, out + outl) :: (rbp, rbp + 8) :: MEMBIO_foot a R) lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).
  Definition readintern_mem_stmt : Prop := readintern_mem_stmt_at P_bio_read_intern READINTERN_STACK.
  Definition bioreadex_mem_stmt : Prop := readintern_mem_stmt_at P_BIO_read_ex BIOREADEX_STACK.

  (* [comment removed for export] *)
  Definition bioread_mem_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list block) (LF : list fframe) (a out outl lo : Z) (R : membio) (ds junk : list byte),
      a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 out -> a2 = Z_to_bv 64 outl -> 0 < outl < 2^31 ->
      MEMBIO H LB m a R -> MEMBIO_below a R lo -> MEMBIO_sep a R -> METH_mem m -> bytes_at asegs m (mb_buf R) ds -> Z.of_nat (length ds) = mb_len R ->
      rw_cells asegs m out [CB (Z.to_nat outl) junk] -> memrd_out a R out outl lo (bv_unsigned sp) ->
      MEMBIO_shad m a R -> PAYLOAD_shad m R -> OUT_shad m out outl -> ACONST m ->                       (* [comment removed for export] *)
      as_RFS H LF m -> (length LF < AFS_MAXLIVE)%nat -> tp = Z_to_bv 64 ATP -> athr_cells m ->         (* [comment removed for export] *)
      afs_write_ok H LF (out, out + outl) -> AIMG_TOP <= out -> fsobj H LF (mb_buf R) (mb_len R) ->                 (* [comment removed for export] *)
      bv_unsigned sp mod 16 = 0 ->                                                                      (* [comment removed for export] *)
      arelro_lib m ->                                                                                   (* [comment removed for export] *)
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - BIOREAD_STACK -> mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
      evt asegs (fun ms' => exists (XS : list (Z * Z)), Forall (fs_scratch H LF) XS /\
                   memrd_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB (mb_rdn R outl) a
                     (mb_after_read R (mb_rdn R outl)) ds out (mb_take R ds (mb_rdn R outl)) outl None
                     (XS ++ (out, out + outl) :: MEMBIO_foot a R) lo m ms' /\ as_RFS H LF (ms_mem ms') /\ arelro_lib (ms_mem ms'))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_BIO_read) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition NEWMEMBUF_COST (ph : ctxphase) : Z :=
    as_Cm H BIO_SIZE + ctxph_cost H ph + as_Cf H 0 + as_Cm H BIOBUFMEM_SIZE + as_Cm H BUFMEM_SIZE + as_Cm H BUFMEM_SIZE.
  Definition newmembuf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (LF : list fframe) (ph : ctxphase) (buf len lo B : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun k => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H) (LBN LB' : list block) (x : ctxinfo) (a : Z) (R : membio) (XS : list (Z * Z)),
      as_VIS H s' (cfg_ms k) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ Permutation LB' (blocks_MEMBIO a R ++ LBN ++ LB)             (* [comment removed for export] *)
      /\ as_MPRES H mo (cfg_model k) /\ c3_frame H sp tp s' LB' lo B errv' m' k /\ METH_mem m'
      /\ ctxph_delta ph LBN x /\ Forall (fun b => addressable m' (blk_addr b) (blk_size b)) LBN
      /\ CTXPH LB' m' (CtxReady x) /\ (ph = CtxFresh -> CTX_keys m')
      /\ MEMBIO H LB' m' a R /\ mb_buf R = buf /\ mb_len R = len /\ mb_pos R = 0 /\ mb_nread R = 0 /\ mb_next R = 0 /\ mb_prev R = 0 /\ 0 < a
      /\ MEMBIO_apart a R /\ MEMBIO_shad m' a R                                                       (* [comment removed for export] *)
      /\ Forall (fs_scratch H LF) XS /\ as_RFS H LF m'
      /\ xpres H LB (bv_unsigned sp) (memflag_foot ++ ctxph_foot ph ++ XS) m m'
      /\ as_AL H s' >= as_AL H s - NEWMEMBUF_COST ph.
  Definition newmembuf_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model) (s : as_St H) (LB : list block) (LF : list fframe) (ph : ctxphase)
           (buf len lo B : Z) (errv : word) (CH : list (Z * Z)),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 P_BIO_new_mem_buf) fc None m (seg_rom asegs) ->
      a0 = Z_to_bv 64 buf -> a1 = Z_to_bv 64 len -> 0 < buf -> buf + len <= aceil -> 0 <= len < 2^31 ->
      as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
      lb_bytes LB + ctxph_bytes ph + MEMBIO_BYTES <= as_LIVE_MAX H -> Z.of_nat (length LB) + ctxph_cnt ph + 4 <= as_LIVE_CNT_MAX H ->
      as_rauxv_ok H m B -> bv_unsigned sp <= B -> bv_unsigned sp mod 16 = 0 ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - NEWMEMBUF_STACK ph -> ctxph_sh0 ph m lo sp ->   (* [comment removed for export] *)
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP -> ACONST m ->
      MEMFLAG m 1 -> IMPL_mem m -> GOT_mem m -> METH_mem m -> arelro_lib m -> CTXPH LB m ph ->
      (* [comment removed for export] *)
      as_RFS H LF m -> (length LF + ctxph_frames ph <= AFS_MAXLIVE)%nat ->
      as_chain H m (bv_unsigned s0) CH -> (forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp') ->
      pf_ok (as_TR H) (PF_newmembuf ph) (bv_unsigned ra) CH -> ctxph_closed_ok H ph -> NEWMEMBUF_COST ph <= as_AL H s ->   (* [comment removed for export] *)
      bv_unsigned ra mod 2 = 0 ->
      as_SR H (newmembuf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF ph buf len lo B m mo) (mkCfg msF mo).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition BIOFREE_COST : Z := as_Cf H BUFMEM_SIZE + as_Cf H BUFMEM_SIZE + as_Cf H BIOBUFMEM_SIZE + as_Cf H 0 + as_Cf H BIO_SIZE.
  Definition biofreeint_mem_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (LF : list fframe) (x : ctxinfo) (a : Z) (R : membio) (rbp shi lo B : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun k => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H) (LBr : list block) (XS : list (Z * Z)),
      as_VIS H s' (cfg_ms k) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ as_MPRES H mo (cfg_model k)
      /\ as_AKREL H s' k /\ mem_inv asegs m' /\ ACONST m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
      /\ as_RHEAP H s' LBr m' /\ Permutation LB (blocks_MEMBIO a R ++ LBr)
      /\ MEMFLAG m' 1 /\ IMPL_mem m' /\ GOT_mem m' /\ METH_mem m' /\ arelro_lib m' /\ CTXPH LBr m' (CtxReady x)
      /\ rw_cells asegs m' rbp [C4 (wz 0)] /\ stack0 m' lo shi
      /\ Forall (fs_scratch H LF) XS /\ as_RFS H LF m'
      /\ xpres H LBr (bv_unsigned sp) ((rbp, rbp + 4) :: mutex_foot (blk_addr (cx_exlock x)) ++ XS) m m'
      /\ as_AL H s' >= as_AL H s - BIOFREE_COST.
  Definition biofreeint_mem_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model) (s : as_St H) (LB : list block) (LF : list fframe) (x : ctxinfo)
           (a rbp shi lo B : Z) (R : membio) (errv jv : word) (CH : list (Z * Z)),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 P_BIO_free_int) fc None m (seg_rom asegs) ->
      a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 rbp -> rw_cells asegs m rbp [C4 jv] -> bv_unsigned sp <= rbp -> rbp + 8 <= shi -> shi <= B -> rbp mod 4 = 0 ->
      stack0 m lo shi ->                                                                     (* [comment removed for export] *)
      MEMBIO H LB m a R -> MEMBIO_apart a R -> MEMBIO_shad m a R -> CTXPH LB m (CtxReady x) ->
      as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
      as_rauxv_ok H m B -> bv_unsigned sp <= B -> bv_unsigned sp mod 16 = 0 ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - BIOFREEINT_STACK ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP -> ACONST m ->
      MEMFLAG m 1 -> IMPL_mem m -> GOT_mem m -> METH_mem m -> arelro_lib m ->
      (* [comment removed for export] *)
      as_RFS H LF m -> (length LF < AFS_MAXLIVE)%nat ->
      as_chain H m (bv_unsigned s0) CH -> (forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp') ->
      (forall fp' ra', In (fp', ra') CH -> rbp + 4 <= fp' - 16 \/ fp' <= rbp) ->                 (* [comment removed for export] *)
      pf_ok (as_TR H) PF_biofreeint (bv_unsigned ra) CH -> BIOFREE_COST <= as_AL H s ->
      bv_unsigned ra mod 2 = 0 ->
      as_SR H (biofreeint_mem_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF x a R rbp shi lo B m mo) (mkCfg msF mo).

  Definition biofree_mem_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (LF : list fframe) (x : ctxinfo) (a : Z) (R : membio) (lo B : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun k => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H) (LBr : list block) (XS : list (Z * Z)),
      as_VIS H s' (cfg_ms k) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ as_MPRES H mo (cfg_model k)
      /\ as_AKREL H s' k /\ mem_inv asegs m' /\ ACONST m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
      /\ as_RHEAP H s' LBr m' /\ Permutation LB (blocks_MEMBIO a R ++ LBr)
      /\ MEMFLAG m' 1 /\ IMPL_mem m' /\ GOT_mem m' /\ METH_mem m' /\ arelro_lib m' /\ CTXPH LBr m' (CtxReady x)
      /\ stack0 m' lo (bv_unsigned sp)
      /\ Forall (fs_scratch H LF) XS /\ as_RFS H LF m'
      /\ xpres H LBr (bv_unsigned sp) (mutex_foot (blk_addr (cx_exlock x)) ++ XS) m m'
      /\ as_AL H s' >= as_AL H s - BIOFREE_COST.
  Definition biofree_mem_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model) (s : as_St H) (LB : list block) (LF : list fframe) (x : ctxinfo)
           (a lo B : Z) (R : membio) (errv : word) (CH : list (Z * Z)),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 P_BIO_free) fc None m (seg_rom asegs) ->
      a0 = Z_to_bv 64 a -> stack0 m lo (bv_unsigned sp) ->                                  (* [comment removed for export] *)
      MEMBIO H LB m a R -> MEMBIO_apart a R -> MEMBIO_shad m a R -> CTXPH LB m (CtxReady x) ->
      as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
      as_rauxv_ok H m B -> bv_unsigned sp <= B -> bv_unsigned sp mod 16 = 0 ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - BIOFREE_STACK ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP -> ACONST m ->
      MEMFLAG m 1 -> IMPL_mem m -> GOT_mem m -> METH_mem m -> arelro_lib m ->
      (* [comment removed for export] *)
      as_RFS H LF m -> (length LF < AFS_MAXLIVE)%nat ->
      as_chain H m (bv_unsigned s0) CH -> (forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp') ->
      pf_ok (as_TR H) PF_biofree (bv_unsigned ra) CH -> BIOFREE_COST <= as_AL H s ->
      bv_unsigned ra mod 2 = 0 ->
      as_SR H (biofree_mem_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF x a R lo B m mo) (mkCfg msF mo).

  Definition C7_stmts : Prop :=
    memread_stmt /\ memctrl_stmt /\ bioctrl_mem_stmt /\ bioeof_mem_stmt /\ breadconv_mem_stmt
    /\ readintern_mem_stmt /\ bioreadex_mem_stmt /\ bioread_mem_stmt /\ newmembuf_stmt /\ biofreeint_mem_stmt /\ biofree_mem_stmt.
End W.
End HCW.
