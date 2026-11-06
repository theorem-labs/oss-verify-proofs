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
     ECH_C1_stmt ECH_C5_stmt.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
From Stdlib Require Import Sorting.Permutation.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section HCW.
  Context {HCEIL : HeapCeil}.

Definition VPMNEW_STACK : Z := FR_X509_VERIFY_PARAM_new + CZALLOC_STACK.
Definition XBUFFREE_STACK : Z := FR_buffer_free + CFREE_STACK.
Definition VPMFREE_STACK : Z := FR_X509_VERIFY_PARAM_free + Z.max (SKPOPFREE_STACK XBUFFREE_STACK) CFREE_STACK.
Definition CTYPE_STACK : Z := FR_ossl_ctype_check.
Definition HNPART_STACK : Z := FR_validate_hostname_part + CTYPE_STACK.
Definition VSN_STACK : Z := FR_validate_string_name.                 (* [comment removed for export] *)
Definition ADDSTR_STACK : Z := FR_add_string_to_buffer_stack + Z.max CSTRNDUP_STACK (Z.max SKNEW_STACK (SKPUSH_STACK)).
Definition ADD1HOST_STACK : Z := FR_X509_VERIFY_PARAM_add1_host + Z.max HNPART_STACK ADDSTR_STACK.
(* [comment removed for export] *)
Definition ADD1HOST_BYTES : Z := 16 + 264 + SK_SIZE + 32.
Definition CTYPE_MASK_alnum : Z := 7.     (* [comment removed for export] *)

Section W.
  Variable H : hsr.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition vpmnew_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : PState) (LB : list block) (lo B : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun c => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (A : Z) (p : bptr) (s' : PState),
      cfg_ms c = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ hs_KREL H s' (cfg_model c) /\ hs_MPRES H mo (cfg_model c)
      /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\ rw_cells rsegs m' (errno_addr tp) [C4 errv'] /\ hs_rauxv_ok H m' B
      /\ xpres LB (bv_unsigned sp) memflag_foot m m'
      /\ rblock_range A VPM_SIZE /\ hs_RHEAP H s' ((p, A, VPM_SIZE) :: LB) m'
      /\ VPMobj ((p, A, VPM_SIZE) :: LB) m' A (vpm_empty p)
      /\ MEMFLAG m' 1 /\ IMPL_mem m' /\ GOT_mem m'.
  Definition vpmnew_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState) (LB : list block) (v lo B : Z) (errv : word),
      hs_RHEAP H s LB m -> hs_KREL H s mo ->
      lb_bytes LB + VPM_SIZE <= hs_LIVE_MAX H -> Z.of_nat (length LB) + 1 <= hs_LIVE_CNT_MAX H -> lb_big LB <= hs_LIVE_BIG_MAX H ->
      hs_rauxv_ok H m B -> bv_unsigned sp <= B ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - VPMNEW_STACK ->
      rw_cells rsegs m (errno_addr tp) [C4 errv] -> mem_inv rsegs m -> tp = Z_to_bv 64 RATP ->
      MEMFLAG m v -> IMPL_mem m -> GOT_mem m -> bv_unsigned ra mod 2 = 0 ->
      hs_SR H (vpmnew_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB lo B m mo)
        (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_X509_VERIFY_PARAM_new) fc None m (seg_rom rsegs)) mo).

  (* [comment removed for export] *)
  Definition vpmfree_stmt : Prop := efree_stmt_at H vpmrep VPMobj blocks_VPM GOT_x509vpm P_X509_VERIFY_PARAM_free VPMFREE_STACK.
  Definition xbuffree_stmt : Prop := efree_stmt_at H xbufrep XBUFobj blocks_XBUF GOT_x509vpm P_buffer_free XBUFFREE_STACK.
  Definition popfree_hosts_stmt : Prop := skpopfree_stmt_gen H xbufrep XBUFobj blocks_XBUF GOT_x509vpm P_buffer_free XBUFFREE_STACK.
  Definition XBUFobj_frame : Prop := EP_frame xbufrep XBUFobj blocks_XBUF.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition ctype_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (rv lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ munch [(lo, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp).
  Definition ctype_alnum_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (c lo : Z),
      a0 = Z_to_bv 64 c -> a1 = Z_to_bv 64 CTYPE_MASK_alnum -> 0 <= c < 256 ->
      stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - CTYPE_STACK -> mem_inv rsegs m -> bv_unsigned ra mod 2 = 0 ->
      evt rsegs (ctype_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (if is_alnumZ c then 1 else 0) lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_ossl_ctype_check) fc None m (seg_rom rsegs)).

  (* [comment removed for export] *)
  Definition hnpart_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (name lo : Z) (ns rest : list byte),
      a0 = Z_to_bv 64 name -> a1 = Z_to_bv 64 (zlength ns) -> a2 = Z_to_bv 64 2 ->
      bytes_at rsegs m name (ns ++ rest) -> (name + zlength ns + zlength rest <= lo \/ bv_unsigned sp <= name) ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - HNPART_STACK -> mem_inv rsegs m -> bv_unsigned ra mod 2 = 0 ->
      evt rsegs (ctype_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (if hostname_ok ns then 1 else 0) lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_validate_hostname_part) fc None m (seg_rom rsegs)).

  (* [comment removed for export] *)
  Definition vsn_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (name lenp lo : Z) (ns rest : list byte),
      a0 = Z_to_bv 64 name -> a1 = Z_to_bv 64 lenp -> 0 < name ->      (* [comment removed for export] *)
      bytes_at rsegs m name (ns ++ Z_to_bv 8 0 :: rest) -> ~ In (Z_to_bv 8 0) ns -> 1 <= zlength ns ->
      (name + zlength ns + 1 + zlength rest <= lo \/ bv_unsigned sp <= name) ->
      rw_cells rsegs m lenp [C8 (wz (zlength ns))] -> (lenp + 8 <= lo \/ bv_unsigned sp <= lenp) ->
      (lenp + 8 <= name \/ name + zlength ns + 1 + zlength rest <= lenp) ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - VSN_STACK -> mem_inv rsegs m -> bv_unsigned ra mod 2 = 0 ->
      evt rsegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
                   ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                            F (ret_pc ra) fc None m' (seg_rom rsegs)
                   /\ munch [(lo, bv_unsigned sp); (lenp, lenp + 8)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
                   /\ rw_cells rsegs m' lenp [C8 (wz (zlength ns))])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_validate_string_name) fc None m (seg_rom rsegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition add1host_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : PState) (LB : list block) (a : Z) (V : vpmrep) (ns : list byte) (lo B : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun c => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : PState) (V' : vpmrep) (NB : list block),
      cfg_ms c = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (if hostname_ok ns then 1 else 0)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ hs_KREL H s' (cfg_model c) /\ hs_MPRES H mo (cfg_model c)
      /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\ rw_cells rsegs m' (errno_addr tp) [C4 errv'] /\ hs_rauxv_ok H m' B
      /\ xpres LB (bv_unsigned sp) (memflag_foot ++ [(a, a + VPM_SIZE)]) m m'
      /\ hs_RHEAP H s' (NB ++ LB) m' /\ VPMobj (NB ++ LB) m' a V' /\ vp_id V' = vp_id V
      /\ Permutation (blocks_VPM a V') ((vp_id V, a, VPM_SIZE) :: NB)
      /\ (hostname_ok ns = false -> NB = [] /\ V' = V)
      /\ (hostname_ok ns = true -> exists K X, vp_hosts_o V' = Some (K, [X]) /\ xb_len X = zlength ns)
      /\ Z.of_nat (length NB) <= 4 /\ lb_bytes NB <= ADD1HOST_BYTES /\ lb_big NB = 0
      /\ MEMFLAG m' 1 /\ IMPL_mem m' /\ GOT_mem m'.
  Definition add1host_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState) (LB : list block)
           (a name lo B : Z) (V : vpmrep) (pn : bptr) (ns slack : list byte) (errv : word),
      a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 name -> a2 = Z_to_bv 64 0 ->
      VPMobj LB m a V -> vp_hosts V = 0 -> vp_hosts_o V = None -> a + VPM_SIZE <= lo ->
      In (pn, name, zlength ns + 1) LB -> bytes_at rsegs m name (ns ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) ns ->
      1 <= zlength ns <= 255 -> (- (name + zlength ns + 1)) mod 8 <= zlength slack ->
      hs_RHEAP H s LB m -> hs_KREL H s mo ->
      lb_bytes LB + ADD1HOST_BYTES <= hs_LIVE_MAX H -> Z.of_nat (length LB) + 4 <= hs_LIVE_CNT_MAX H -> lb_big LB <= hs_LIVE_BIG_MAX H ->
      hs_rauxv_ok H m B -> bv_unsigned sp <= B ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - ADD1HOST_STACK ->
      rw_cells rsegs m (errno_addr tp) [C4 errv] -> mem_inv rsegs m -> tp = Z_to_bv 64 RATP ->
      MEMFLAG m 1 -> IMPL_mem m -> GOT_mem m -> bv_unsigned ra mod 2 = 0 ->      (* [comment removed for export] *)
      hs_SR H (add1host_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB a V ns lo B m mo)
        (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_X509_VERIFY_PARAM_add1_host) fc None m (seg_rom rsegs)) mo).
  (* [comment removed for export] *)

  Definition C12_stmts : Prop :=
    vpmnew_stmt /\ vpmfree_stmt /\ xbuffree_stmt /\ popfree_hosts_stmt /\ XBUFobj_frame
    /\ ctype_alnum_stmt /\ hnpart_stmt /\ vsn_stmt /\ add1host_stmt.
End W.
End HCW.
