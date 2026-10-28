(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr SysStep Exec CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface ECH_AStmt_C1.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import ECH_B64.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section HCW.
  Context {HCEIL : HeapCeil}.

Definition ENCCTX_SIZE : Z := 92.
Definition O_ENC_DATA : Z := 4.  Definition O_ENC_LINE : Z := 84.  Definition O_ENC_FLAGS : Z := 88.
Definition ENCNEW_STACK : Z := FR_EVP_ENCODE_CTX_new + CZALLOC_STACK.
Definition ENCFREE_STACK : Z := FR_EVP_ENCODE_CTX_free + CFREE_STACK.
Definition DECINIT_STACK : Z := FR_EVP_DecodeInit.
Definition DECBLOCK_STACK : Z := FR_evp_decodeblock_int.
Definition DECUPDATE_STACK : Z := FR_EVP_DecodeUpdate + DECBLOCK_STACK.
Definition DECFINAL_STACK : Z := FR_EVP_DecodeFinal + DECBLOCK_STACK.

(* [comment removed for export] *)
Definition b64_saved (c : Z) : Prop := 0 <= c < 128 /\ b64_base64 (a2b c) = true /\ a2b c <> B64_ERROR /\ a2b c <> B64_EOF.
Definition du_inv (d : list Z) : Prop := Forall b64_saved d /\ (length d < 64)%nat.
Definition ENCCTX_foot (a : Z) : list (Z * Z) := [(a, a + ENCCTX_SIZE)].
(* [comment removed for export] *)
Definition B64TAB (m : mem) : Prop := bytes_at asegs m A_data_ascii2bin (map (Z_to_bv 8) data_ascii2bin).
(* [comment removed for export] *)
Definition PF_encnew : list (Z * list Z) := PF_czalloc.
Definition PF_encfree : list (Z * list Z) := PF_cfree.

Section W.
  Variable H : asr.

(* [comment removed for export] *)
Definition ENCCTX (LB : list block) (m : mem) (a : Z) (d : list Z) (p : bptr) : Prop :=
  exists (raw : list byte) (line : Z),
       length raw = 80%nat /\ map bv_unsigned (firstn (length d) raw) = d
    /\ rw_cells asegs m a [C4 (wz (zlength d)); CB 80 raw; C4 (wz line); C4 (wz 0)]
    /\ 0 <= line < 2^32 /\ In (p, a, ENCCTX_SIZE) LB /\ ablock_range H a ENCCTX_SIZE /\ du_inv d.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition encnew_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (lo B : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun c => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (A : Z) (p : bptr) (s' : as_St H),
      as_VIS H s' (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ as_AKREL H s' c /\ as_MPRES H mo (cfg_model c)
      /\ mem_inv asegs m' /\ ACONST m' /\ stk asegs m' lo (bv_unsigned sp) /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
      /\ xpres H LB (bv_unsigned sp) memflag_foot m m'
      /\ as_RHEAP H s' ((p, A, ENCCTX_SIZE) :: LB) m'
      /\ ENCCTX ((p, A, ENCCTX_SIZE) :: LB) m' A [] p /\ addressable m' A ENCCTX_SIZE
      /\ MEMFLAG m' 1 /\ IMPL_mem m' /\ GOT_mem m'
      /\ as_AL H s' >= as_AL H s - as_Cm H ENCCTX_SIZE.
  Definition encnew_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model) (s : as_St H) (LB : list block) (v lo B : Z) (errv : word) (CH : list (Z * Z)),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 P_EVP_ENCODE_CTX_new) fc None m (seg_rom asegs) ->
      as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
      lb_bytes LB + ENCCTX_SIZE <= as_LIVE_MAX H -> Z.of_nat (length LB) + 1 <= as_LIVE_CNT_MAX H ->
      as_rauxv_ok H m B -> bv_unsigned sp <= B ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - ENCNEW_STACK ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
      bv_unsigned sp mod 16 = 0 -> ACONST m ->
      as_chain H m (bv_unsigned s0) CH -> (forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp') -> pf_ok (as_TR H) PF_encnew (bv_unsigned ra) CH ->
      as_Cm H ENCCTX_SIZE <= as_AL H s ->
      MEMFLAG m v -> IMPL_mem m -> GOT_mem m -> bv_unsigned ra mod 2 = 0 ->
      as_SR H (encnew_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB lo B m mo) (mkCfg msF mo).

  (* [comment removed for export] *)
  Definition encfree_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (p : bptr) (lo B : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun c => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H),
      as_VIS H s' (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ as_AKREL H s' c /\ as_MPRES H mo (cfg_model c)
      /\ mem_inv asegs m' /\ ACONST m' /\ stk asegs m' lo (bv_unsigned sp) /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
      /\ xpres H (as_lb_remove H p LB) (bv_unsigned sp) [] m m'
      /\ as_RHEAP H s' (as_lb_remove H p LB) m' /\ IMPL_mem m' /\ GOT_mem m'
      /\ as_AL H s' >= as_AL H s - as_Cf H ENCCTX_SIZE.
  Definition encfree_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model) (s : as_St H) (LB : list block) (p : bptr) (a lo B : Z) (d : list Z) (errv : word) (CH : list (Z * Z)),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 P_EVP_ENCODE_CTX_free) fc None m (seg_rom asegs) ->
      a0 = Z_to_bv 64 a -> ENCCTX LB m a d p -> addressable m a ENCCTX_SIZE ->
      as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
      as_rauxv_ok H m B -> bv_unsigned sp <= B ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - ENCFREE_STACK ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
      bv_unsigned sp mod 16 = 0 -> ACONST m ->
      as_chain H m (bv_unsigned s0) CH -> (forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp') -> pf_ok (as_TR H) PF_encfree (bv_unsigned ra) CH ->
      as_Cf H ENCCTX_SIZE <= as_AL H s ->
      IMPL_mem m -> GOT_mem m -> bv_unsigned ra mod 2 = 0 ->
      as_SR H (encfree_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p lo B m mo) (mkCfg msF mo).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition c8_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (LB : list block) (rv a : Z) (d' : list Z) (p : bptr) (W : list (Z * Z)) (X : mem -> Prop) (lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ a0 = Z_to_bv 64 rv
      /\ munch ((lo, bv_unsigned sp) :: W) m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ ACONST m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ ENCCTX LB m' a d' p /\ X m'.

  (* [comment removed for export] *)
  Definition decinit_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list block) (p : bptr) (a lo : Z) (old : list byte),
      a0 = Z_to_bv 64 a -> rw_cells asegs m a [CB 92 old] -> In (p, a, ENCCTX_SIZE) LB -> ablock_range H a ENCCTX_SIZE -> a + ENCCTX_SIZE <= lo ->
      accessible m a ENCCTX_SIZE -> ACONST m ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - DECINIT_STACK -> mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
      evt asegs (c8_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB (a + 88) a [] p (ENCCTX_foot a) (fun _ => True) lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_EVP_DecodeInit) fc None m (seg_rom asegs)).
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition du_outcap (d : list Z) (inl : Z) : Z := 3 * ((zlength d + inl) / 4).
  Definition decupdate_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list block) (p : bptr) (a out outlp inp_a inl outsz ov lo : Z)
           (d : list Z) (inp : list byte) (junk : list byte),
      a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 out -> a2 = Z_to_bv 64 outlp -> a3 = Z_to_bv 64 inp_a -> a4 = Z_to_bv 64 inl ->
      0 <= inl < 2^20 -> Z.of_nat (length inp) = inl ->
      ENCCTX LB m a d p -> B64TAB m ->
      bytes_at asegs m inp_a inp -> rw_cells asegs m out [CB (Z.to_nat outsz) junk] -> du_outcap d inl <= outsz -> 0 < out ->
      0 < inp_a -> inp_a + inl < 2^64 -> out + outsz < 2^64 ->   (* [comment removed for export] *)
      rw_cells asegs m outlp [C4 (wz ov)] ->
      accessible m a ENCCTX_SIZE -> accessible m out outsz -> accessible m outlp 4 -> accessible m inp_a inl -> ACONST m ->
      (aapp out outsz \/ bv_unsigned sp <= out) -> (aapp outlp 4 \/ bv_unsigned sp <= outlp) -> (aapp inp_a inl \/ bv_unsigned sp <= inp_a) ->   (* [comment removed for export] *)
      outlp mod 4 = 0 ->   (* [comment removed for export] *)
      (* [comment removed for export] *)
      a + ENCCTX_SIZE <= lo -> (out + outsz <= lo \/ bv_unsigned sp <= out) -> (outlp + 4 <= lo \/ bv_unsigned sp <= outlp) ->
      (inp_a + inl <= lo \/ bv_unsigned sp <= inp_a) ->
      (out + outsz <= a \/ a + ENCCTX_SIZE <= out) -> (outlp + 4 <= a \/ a + ENCCTX_SIZE <= outlp) -> (outlp + 4 <= out \/ out + outsz <= outlp) ->
      (inp_a + inl <= out \/ out + outsz <= inp_a) -> (inp_a + inl <= a \/ a + ENCCTX_SIZE <= inp_a) -> (inp_a + inl <= outlp \/ outlp + 4 <= inp_a) ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - DECUPDATE_STACK -> mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
      let r := decode_update d (map bv_unsigned inp) in
      evt asegs (c8_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB (dr_rv r) a (dr_d r) p
                   [(out, out + outsz); (outlp, outlp + 4); (a, a + ENCCTX_SIZE)]
                   (fun m' => exists junk', rw_cells asegs m' out [CB (length (dr_out r)) (map (Z_to_bv 8) (dr_out r)); CB (Z.to_nat outsz - length (dr_out r)) junk']
                                         /\ rw_cells asegs m' outlp [C4 (wz (zlength (dr_out r)))]
                                         /\ bytes_at asegs m' inp_a inp /\ B64TAB m'
                                         /\ (length (dr_out r) <= Z.to_nat outsz)%nat) lo m)      (* [comment removed for export] *)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_EVP_DecodeUpdate) fc None m (seg_rom asegs)).
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition decfinal_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list block) (p : bptr) (a outlp ov lo : Z) (d : list Z),
      a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 0 -> a2 = Z_to_bv 64 outlp ->
      ENCCTX LB m a d p -> B64TAB m -> (length d = 0%nat \/ Nat.modulo (length d) 4 <> 0%nat) ->
      rw_cells asegs m outlp [C4 (wz ov)] -> (outlp + 4 <= lo \/ bv_unsigned sp <= outlp) -> (outlp + 4 <= a \/ a + ENCCTX_SIZE <= outlp) ->
      accessible m a ENCCTX_SIZE -> accessible m outlp 4 -> ACONST m -> (aapp outlp 4 \/ bv_unsigned sp <= outlp) -> outlp mod 4 = 0 ->
      a + ENCCTX_SIZE <= lo ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - DECFINAL_STACK -> mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
      evt asegs (c8_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB (decode_final_rv d) a d p
                   [(outlp, outlp + 4)] (fun m' => rw_cells asegs m' outlp [C4 (wz 0)] /\ B64TAB m') lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_EVP_DecodeFinal) fc None m (seg_rom asegs)).

  Definition C8_stmts : Prop := encnew_stmt /\ encfree_stmt /\ decinit_stmt /\ decupdate_stmt /\ decfinal_stmt.
End W.
End HCW.
