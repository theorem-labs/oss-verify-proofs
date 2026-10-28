(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr SysStep Exec CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsStack0 ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface ECH_AStmt_C1 ECH_AStmt_C5 ECH_AStmt_C13.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From Stdlib Require Import Sorting.Permutation.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section HCW.
  Context {HCEIL : HeapCeil}.

Definition VPMNEW_STACK : Z := FR_X509_VERIFY_PARAM_new + CZALLOC_STACK.
Definition XBUFFREE_STACK : Z := FR_buffer_free + CFREE_STACK.
Definition VPMFREE_STACK : Z := FR_X509_VERIFY_PARAM_free + 32 + Z.max (SKPOPFREE_STACK XBUFFREE_STACK) CFREE_STACK.
Definition CTYPE_STACK : Z := FR_ossl_ctype_check.
Definition HNPART_STACK : Z := FR_validate_hostname_part + CTYPE_STACK.
Definition VSN_STACK : Z := FR_validate_string_name.                 (* [comment removed for export] *)
Definition ADDSTR_STACK : Z := FR_add_string_to_buffer_stack + Z.max CSTRNDUP_STACK (Z.max SKNEW_STACK (SKPUSH_STACK)).
Definition ADD1HOST_STACK : Z := FR_X509_VERIFY_PARAM_add1_host + Z.max (Z.max HNPART_STACK (VSN_STACK + AINTRIN_STACK)) ADDSTR_STACK.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition ADD1HOST_BYTES : Z := 16 + 264 + SK_SIZE + 32.
Definition CTYPE_MASK_alnum : Z := 7.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition R_X509_VERIFY_PARAM_new_CRYPTO_zalloc : Z := 0x432314.
Definition R_X509_VERIFY_PARAM_free_sk_pop_free : Z := 0x432428.      (* [comment removed for export] *)
Definition R_X509_VERIFY_PARAM_free_sk_pop_free_2 : Z := 0x432430.    (* [comment removed for export] *)
Definition R_X509_VERIFY_PARAM_free_sk_pop_free_3 : Z := 0x432438.    (* [comment removed for export] *)
Definition R_X509_VERIFY_PARAM_free_sk_pop_free_4 : Z := 0x432440.    (* [comment removed for export] *)
Definition R_X509_VERIFY_PARAM_free_sk_pop_free_5 : Z := 0x432448.    (* [comment removed for export] *)
Definition R_X509_VERIFY_PARAM_free_CRYPTO_free : Z := 0x432478.      (* [comment removed for export] *)
Definition R_X509_VERIFY_PARAM_free_helper_sk_pop_free : Z := 0x432530.
Definition R_buffer_free_CRYPTO_free : Z := 0x432bbc.
Definition R_X509_VERIFY_PARAM_add1_host_strlen : Z := 0x4325c0.
Definition R_X509_VERIFY_PARAM_add1_host_validate_string_name : Z := 0x4325d4.
Definition R_X509_VERIFY_PARAM_add1_host_validate_hostname_part : Z := 0x432634.
Definition R_X509_VERIFY_PARAM_add1_host_add_string_to_buffer_stack : Z := 0x432620.
Definition R_add_string_to_buffer_stack_CRYPTO_zalloc : Z := 0x432968.
Definition R_add_string_to_buffer_stack_CRYPTO_strndup : Z := 0x43298c.
Definition R_add_string_to_buffer_stack_OPENSSL_sk_new : Z := 0x432a54.
Definition R_add_string_to_buffer_stack_OPENSSL_sk_push : Z := 0x432aac.

(* [comment removed for export] *)
Definition PF_vpmnew : list (Z * list Z) := pf_shift R_X509_VERIFY_PARAM_new_CRYPTO_zalloc PF_czalloc.
Definition PF_xbuffree : list (Z * list Z) := pf_shift R_buffer_free_CRYPTO_free PF_cfree ++ PF_cfree.
Definition PF_vpmfree : list (Z * list Z) :=
  pf_shift R_X509_VERIFY_PARAM_free_sk_pop_free_2 (pf_shift R_X509_VERIFY_PARAM_free_helper_sk_pop_free (PF_skpopfree PF_xbuffree))
  ++ pf_shift R_X509_VERIFY_PARAM_free_CRYPTO_free PF_cfree ++ PF_cfree.
Definition PF_addstr : list (Z * list Z) :=
  pf_shift R_add_string_to_buffer_stack_CRYPTO_zalloc PF_czalloc ++ pf_shift R_add_string_to_buffer_stack_CRYPTO_strndup PF_cstrndup
  ++ pf_shift R_add_string_to_buffer_stack_OPENSSL_sk_new PF_sknew ++ pf_shift R_add_string_to_buffer_stack_OPENSSL_sk_push PF_skpush.
Definition PF_add1host : list (Z * list Z) := pf_shift R_X509_VERIFY_PARAM_add1_host_add_string_to_buffer_stack PF_addstr.      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition XBUF_shad (m : mem) (a : Z) (X : xbufrep) : Prop :=
  a + XBUF_SIZE <= AAPP_HI /\ addressable m a XBUF_SIZE
  /\ xb_data X + (xb_len X + 1) <= AAPP_HI /\ addressable m (xb_data X) (xb_len X + 1)
  /\ exists bs, rw_cells asegs m (xb_data X) [CB (Z.to_nat (xb_len X + 1)) bs].
Definition HOSTS_shad (m : mem) (P : Z) (xs : option (skrep * list xbufrep)) : Prop :=
  match xs with
  | None => True
  | Some (K, bs) => SKX_shad m P K /\ Forall2 (fun p X => XBUF_shad m p X) (sk_elems K) bs
  end.
Definition VPM_shad (m : mem) (a : Z) (V : vpmrep) : Prop :=
  a + VPM_SIZE <= AAPP_HI /\ addressable m a VPM_SIZE /\ HOSTS_shad m (vp_hosts V) (vp_hosts_o V).

Section W.
  Variable H : asr.

  (* [comment removed for export] *)
  Definition as_slack_law : Prop :=
    forall s LB m p A n, as_RHEAP H s LB m -> In (p, A, n) LB -> wr_at asegs m (A + n) ((- (A + n)) mod 8).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition vpmnew_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (lo B : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun c => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (A : Z) (p : bptr) (s' : as_St H),
      as_VIS H s' (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ as_AKREL H s' c /\ as_MPRES H mo (cfg_model c)
      /\ mem_inv asegs m' /\ ACONST m' /\ stk asegs m' lo (bv_unsigned sp) /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
      /\ xpres H LB (bv_unsigned sp) memflag_foot m m'
      /\ ablock_range H A VPM_SIZE /\ as_RHEAP H s' ((p, A, VPM_SIZE) :: LB) m'
      /\ VPMobj ((p, A, VPM_SIZE) :: LB) m' A (vpm_empty p) /\ VPM_shad m' A (vpm_empty p)
      /\ MEMFLAG m' 1 /\ IMPL_mem m' /\ GOT_mem m'
      /\ as_AL H s' >= as_AL H s - as_Cm H VPM_SIZE.
  Definition vpmnew_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model) (s : as_St H) (LB : list block) (v lo B : Z) (errv : word) (CH : list (Z * Z)),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 P_X509_VERIFY_PARAM_new) fc None m (seg_rom asegs) ->
      as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
      lb_bytes LB + VPM_SIZE <= as_LIVE_MAX H -> Z.of_nat (length LB) + 1 <= as_LIVE_CNT_MAX H ->
      as_rauxv_ok H m B -> bv_unsigned sp <= B ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - VPMNEW_STACK ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
      bv_unsigned sp mod 16 = 0 -> ACONST m ->
      as_chain H m (bv_unsigned s0) CH -> (forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp') -> pf_ok (as_TR H) PF_vpmnew (bv_unsigned ra) CH ->
      as_Cm H VPM_SIZE <= as_AL H s ->
      MEMFLAG m v -> IMPL_mem m -> GOT_mem m -> bv_unsigned ra mod 2 = 0 ->
      as_SR H (vpmnew_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB lo B m mo) (mkCfg msF mo).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition xbuf_cost (X : xbufrep) : Z := as_Cf H (Z.max (xb_len X + 1) 0) + as_Cf H XBUF_SIZE.
  Definition hosts_cost (xs : option (skrep * list xbufrep)) : Z :=
    match xs with
    | None => 0
    | Some (K, bs) => ecost_sum xbufrep xbuf_cost bs + as_Cf H (Z.max (8 * sk_cap K) 0) + as_Cf H SK_SIZE
    end.
  Definition vpm_cost (V : vpmrep) : Z := hosts_cost (vp_hosts_o V) + as_Cf H 0 + as_Cf H VPM_SIZE.   (* [comment removed for export] *)
  Definition vpmfree_stmt : Prop := efree_stmt_at H vpmrep VPMobj blocks_VPM GOT_x509vpm PF_vpmfree vpm_cost VPM_shad P_X509_VERIFY_PARAM_free VPMFREE_STACK.
  Definition xbuffree_stmt : Prop := efree_stmt_at H xbufrep XBUFobj blocks_XBUF GOT_x509vpm PF_xbuffree xbuf_cost XBUF_shad P_buffer_free XBUFFREE_STACK.
  Definition popfree_hosts_stmt : Prop := skpopfree_stmt_gen H xbufrep XBUFobj blocks_XBUF GOT_x509vpm PF_xbuffree xbuf_cost XBUF_shad P_buffer_free XBUFFREE_STACK.
  Definition XBUFobj_frame : Prop := EP_frame H xbufrep XBUFobj blocks_XBUF.
  Definition XBUF_shad_frame : Prop := eshad_frame H xbufrep blocks_XBUF XBUF_shad.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition ctype_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (rv lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(lo, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ ACONST m' /\ stk asegs m' lo (bv_unsigned sp).
  Definition ctype_alnum_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (c lo : Z),
      a0 = Z_to_bv 64 c -> a1 = Z_to_bv 64 CTYPE_MASK_alnum -> 0 <= c < 256 ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - CTYPE_STACK -> mem_inv asegs m -> ACONST m -> bv_unsigned ra mod 2 = 0 ->   (* [comment removed for export] *)
      evt asegs (ctype_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (if is_alnumZ c then 1 else 0) lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_ossl_ctype_check) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition hnpart_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (name lo : Z) (ns rest : list byte),
      a0 = Z_to_bv 64 name -> a1 = Z_to_bv 64 (zlength ns) -> a2 = Z_to_bv 64 2 ->
      bytes_at asegs m name (ns ++ rest) -> (name + zlength ns + zlength rest <= lo \/ bv_unsigned sp <= name) ->
      accessible m name (zlength ns) -> (name + zlength ns <= ALOWSH_LO \/ AHI_LO <= name) ->    (* [comment removed for export] *)
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - HNPART_STACK -> mem_inv asegs m -> ACONST m -> bv_unsigned ra mod 2 = 0 ->
      evt asegs (ctype_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (if hostname_ok ns then 1 else 0) lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_validate_hostname_part) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition vsn_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (name lenp lo hi0 : Z) (ns rest : list byte),
      a0 = Z_to_bv 64 name -> a1 = Z_to_bv 64 lenp -> 0 < name ->      (* [comment removed for export] *)
      bytes_at asegs m name (ns ++ Z_to_bv 8 0 :: rest) -> ~ In (Z_to_bv 8 0) ns -> 1 <= zlength ns < 2^40 ->     (* [comment removed for export] *)
      (name + zlength ns + 1 + zlength rest <= lo \/ bv_unsigned sp <= name) ->
      lenp mod 8 = 0 -> rw_cells asegs m lenp [C8 (wz (zlength ns))] -> (lenp + 8 <= lo \/ bv_unsigned sp <= lenp) ->
      (lenp + 8 <= name \/ name + zlength ns + 1 + zlength rest <= lenp) ->
      accessible m name (zlength ns + 1) -> shvis m name (name + zlength ns + 1) -> in_app_mem name (name + zlength ns + 1) ->   (* [comment removed for export] *)
      (name + zlength ns + 1 <= ALOWSH_LO \/ AHI_LO <= name) ->
      stack0 m lo hi0 -> lenp + 8 <= hi0 -> lo <= lenp ->                                                                       (* [comment removed for export] *)
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - (VSN_STACK + AINTRIN_STACK) -> mem_inv asegs m -> ACONST m -> bv_unsigned ra mod 2 = 0 ->
      evt asegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
                   ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                            F (ret_pc ra) fc None m' (seg_rom asegs)
                   /\ munch [(lo, bv_unsigned sp); (lenp, lenp + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ ACONST m' /\ stk asegs m' lo (bv_unsigned sp)
                   /\ rw_cells asegs m' lenp [C8 (wz (zlength ns))] /\ stack0 m' lo hi0)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_validate_string_name) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition ADD1HOST_COST : Z := as_Cm H XBUF_SIZE + as_Cm H 256 + as_Cm H SK_SIZE + as_Cm H 32 + 3 * as_Cf H 0.   (* [comment removed for export] *)
  Definition add1host_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (a : Z) (V : vpmrep) (ns : list byte) (lo B : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun c => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H) (V' : vpmrep) (NB : list block),
      as_VIS H s' (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (if hostname_ok ns then 1 else 0)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ as_AKREL H s' c /\ as_MPRES H mo (cfg_model c)
      /\ mem_inv asegs m' /\ ACONST m' /\ stk asegs m' lo (bv_unsigned sp) /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
      /\ xpres H LB (bv_unsigned sp) (memflag_foot ++ [(a, a + VPM_SIZE)]) m m'
      /\ as_RHEAP H s' (NB ++ LB) m' /\ VPMobj (NB ++ LB) m' a V' /\ vp_id V' = vp_id V
      /\ Permutation (blocks_VPM a V') ((vp_id V, a, VPM_SIZE) :: NB)
      /\ (hostname_ok ns = false -> NB = [] /\ V' = V)
      /\ (hostname_ok ns = true -> exists K X, vp_hosts_o V' = Some (K, [X]) /\ xb_len X = zlength ns)
      /\ Z.of_nat (length NB) <= 4 /\ lb_bytes NB <= ADD1HOST_BYTES
      /\ VPM_shad m' a V' /\ stack0 m' lo (bv_unsigned sp)
      /\ MEMFLAG m' 1 /\ IMPL_mem m' /\ GOT_mem m'
      /\ as_AL H s' >= as_AL H s - ADD1HOST_COST.
  Definition add1host_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model) (s : as_St H) (LB : list block)
           (a name lo B : Z) (V : vpmrep) (pn : bptr) (ns slack : list byte) (errv : word) (CH : list (Z * Z)),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 P_X509_VERIFY_PARAM_add1_host) fc None m (seg_rom asegs) ->
      a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 name -> a2 = Z_to_bv 64 0 ->
      VPMobj LB m a V -> vp_hosts V = 0 -> vp_hosts_o V = None -> a + VPM_SIZE <= lo ->
      In (pn, name, zlength ns + 1) LB -> bytes_at asegs m name (ns ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) ns ->
      1 <= zlength ns <= 255 -> (- (name + zlength ns + 1)) mod 8 <= zlength slack ->
      VPM_shad m a V -> accessible m name (zlength ns + 1) ->                                   (* [comment removed for export] *)
      as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
      lb_bytes LB + ADD1HOST_BYTES <= as_LIVE_MAX H -> Z.of_nat (length LB) + 4 <= as_LIVE_CNT_MAX H ->
      as_rauxv_ok H m B -> bv_unsigned sp <= B ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - ADD1HOST_STACK -> stack0 m lo (bv_unsigned sp) ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
      bv_unsigned sp mod 16 = 0 -> ACONST m ->
      as_chain H m (bv_unsigned s0) CH -> (forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp') -> pf_ok (as_TR H) PF_add1host (bv_unsigned ra) CH ->
      ADD1HOST_COST <= as_AL H s ->
      MEMFLAG m 1 -> IMPL_mem m -> GOT_mem m -> bv_unsigned ra mod 2 = 0 ->      (* [comment removed for export] *)
      as_SR H (add1host_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB a V ns lo B m mo) (mkCfg msF mo).
  (* [comment removed for export] *)

  Definition C12_stmts : Prop :=
    vpmnew_stmt /\ vpmfree_stmt /\ xbuffree_stmt /\ popfree_hosts_stmt /\ XBUFobj_frame /\ XBUF_shad_frame
    /\ ctype_alnum_stmt /\ hnpart_stmt /\ vsn_stmt /\ add1host_stmt.
End W.
End HCW.
