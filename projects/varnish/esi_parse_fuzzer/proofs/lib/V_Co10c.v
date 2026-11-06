(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Img0 Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutP0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutP0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition vep_error_entry : Z := 0x1b0b0.
Definition vep_emit_len_entry : Z := 0x1c0fc.
Definition vep_emit_common_entry : Z := 0x1bfc0.
Definition vep_mark_common_entry : Z := 0x1aeac.
Definition WS_Init_entry : Z := 0x187e4.
Definition WS_Alloc_entry : Z := 0x18c18.
Definition WS_Rollback_entry : Z := 0x19e58.
Definition VEP_Init_entry : Z := 0x1bb40.
Definition VEP_Parse_entry : Z := 0x19efc.
Definition VEP_Finish_entry : Z := 0x1bde4.
Definition vep_do_comment_entry : Z := 0x1b9b8.
Definition vep_do_remove_entry : Z := 0x1b8b4.
Definition vep_do_include_entry : Z := 0x1b0ec.

Definition VEPERR_STACK : Z := 48.                 (* [comment removed for export] *)
Definition EMITLEN_STACK : Z := 32 + (48 + (48 + REALLOC_STACK)).   (* [comment removed for export] *)
Definition EMITC_STACK : Z := 48 + EMITLEN_STACK.
Definition MARK_STACK : Z := 48 + EMITC_STACK.
Definition WSINIT_STACK : Z := 96.
Definition WSALLOC_STACK : Z := 32 + 64 + CALLOC_STACK.
Definition WSROLLBACK_STACK : Z := 48 + 32 + FREE_STACK.
Definition VEPINIT_STACK : Z := 64 + WSALLOC_STACK.
Definition VEPFIN_STACK : Z := 32 + MARK_STACK.
Definition DOINCL_STACK : Z := 112 + (64 + 64 + (48 + REALLOC_STACK)).   (* [comment removed for export] *)
Definition PARSE_STACK : Z := 176 + DOINCL_STACK.

From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_HKit.
(* [comment removed for export] *)
Ltac hnorm_consts_in H ::=
  unfold PARSE_STACK, DOINCL_STACK, VEPFIN_STACK, VEPINIT_STACK, WSROLLBACK_STACK, WSALLOC_STACK, MARK_STACK, EMITC_STACK,
         EMITLEN_STACK, VEPERR_STACK, WSINIT_STACK, REALLOC_STACK, CALLOC_STACK, MALLOC_STACK, FREE_STACK in H.
Ltac unfold_stacks :=
  unfold PARSE_STACK, DOINCL_STACK, VEPFIN_STACK, VEPINIT_STACK, WSROLLBACK_STACK, WSALLOC_STACK, MARK_STACK, EMITC_STACK,
         EMITLEN_STACK, VEPERR_STACK, WSINIT_STACK, REALLOC_STACK, CALLOC_STACK, MALLOC_STACK, FREE_STACK in *.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition vkeep (v v' : vep) (ch : list vf) : Prop := forall f, ~ In f ch -> v' f = v f.

(* [comment removed for export] *)
Definition vep_cnt (v : vep) (n : Z) : Prop :=
  0 <= v Fo_pending /\ 0 <= v Fcb_x /\ v Fcb_x + v Fo_pending = n /\
  0 <= v Fo_total <= v Fo_last /\ v Fo_last <= v Fcb_x /\
  v Fo_wait = v Fcb_x - v Fo_last /\ v Fo_crc = v Fo_wait.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition vsb_room (vv : vsb_rec) (N : Z) : Prop :=
  vb_size vv <= vb_len vv + 4096 /\ vb_len vv <= 7 * N.

(* [comment removed for export] *)
Definition NMAX : Z := 2^26.

Section C.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutP0}.

  (* [comment removed for export] *)
  Definition vep_base (H : henv) (VEP : Z) (v : vep) : Prop :=
    v Fvc = h_vc H /\ v Fcb = vi_cb VI0 /\ v Fcb_priv = VEP + 56 /\ v Fdogzip = 0 /\ v Furl = vi_url VI0.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition vep_error_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (H : henv) (lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ munch [(bv_unsigned sp - VEPERR_STACK, bv_unsigned sp); (h_vsc H + 1304, h_vsc H + 1320)] m m'
      /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ henv_ok LayoutP0 VI0 H m' /\ stk rsegs m' lo (bv_unsigned sp).

  Definition vep_error_stmt : Prop :=
    forall (VEP : Z) (v : vep) (tag : list byte) (q : vep_pads) (H : henv) (lo : Z),
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem),
      a0 = Z_to_bv 64 VEP ->
      rw_cells rsegs m VEP (vep_cells v tag q) -> length tag = 8%nat -> vep_pads_wf q ->
      v Fvc = h_vc H -> henv_ok LayoutP0 VI0 H m -> henv_geom H -> img_ok0 m ->
      4096 <= VEP -> VEP mod 8 = 0 -> VEP + 312 <= alloc_ceiling ->
      stk rsegs m lo (bv_unsigned sp) -> lo + VEPERR_STACK <= bv_unsigned sp -> alloc_ceiling <= lo ->
      bv_unsigned sp <= h_sp H ->
      mem_inv rsegs m ->
      evt rsegs (vep_error_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc H lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 vep_error_entry) fc None m (seg_rom rsegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition vep_emit_len_stmt : Prop :=
    forall (VEP : Z) (v : vep) (tag : list byte) (q : vep_pads) (vv : vsb_rec) (l c8 c16 c64 : Z) (lo : Z),
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (m : mem) (md : Model) (A : AS) (T : TSet),
      ainv A m md -> mem_inv rsegs m ->
      a0 = Z_to_bv 64 VEP -> a1 = Z_to_bv 64 l -> a2 = Z_to_bv 64 c8 -> a3 = Z_to_bv 64 c16 -> a4 = Z_to_bv 64 c64 ->
      1 <= l < 2^62 -> 0 <= c8 < 256 -> 0 <= c16 < 256 -> 0 <= c64 < 256 ->
      vep_obj LayoutP0 A m VEP v tag q -> vsb_obj LayoutP0 A m (v Fvsb) vv false -> VEP <> v Fvsb -> VEP <> vb_buf vv ->
      vb_size vv + 9 <= EXT_MAX ->
      a_livebytes A + vsb_extendsize (vb_size vv + 9) <= LIVE_MAX -> a_nlive A + 1 <= NLIVE_MAX ->   (* [comment removed for export] *)
      tp = al_tp LayoutP0 -> bv_unsigned sp mod 16 = 0 -> bv_unsigned ra mod 2 = 0 ->
      stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + EMITLEN_STACK <= bv_unsigned sp ->
      bv_unsigned sp + 64 <= 2^47 ->
      (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model) (vv' : vsb_rec),
          ainv A' m' md' -> mem_inv rsegs m' -> md_frame md md' ->
          stk rsegs m' lo (bv_unsigned sp) ->
          vep_obj LayoutP0 A' m' VEP v tag q ->
          vsb_obj LayoutP0 A' m' (v Fvsb) vv' false ->
          vb_len vv <= vb_len vv' <= vb_len vv + Z.min 9 (2 + l) ->
          vb_size vv <= vb_size vv' <= Z.max (vb_size vv) (vb_len vv' + 4096) ->
          (vb_buf vv' = vb_buf vv \/ (a_live A (vb_buf vv') = None /\ a_live A' (vb_buf vv) = None)) ->
          (forall p, p <> vb_buf vv -> p <> vb_buf vv' -> a_live A' p = a_live A p) ->
          a_livebytes A' = a_livebytes A + vb_size vv' - vb_size vv -> a_nlive A' = a_nlive A ->   (* [comment removed for export] *)
          cframe LayoutP0 (owned A) (owned A') (bv_unsigned sp) EMITLEN_STACK
                 (fun a => blk (vb_buf vv) (vb_size vv) a \/ (v Fvsb <= a < v Fvsb + 40))
                 (blk (vb_buf vv') (vb_size vv')) m m' ->
          realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                     bvmap_empty (ret_pc ra) (Z_to_bv 32 0) None m' (seg_rom rsegs)) md') T) ->
      realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 bvmap_empty (Z_to_bv 64 vep_emit_len_entry) (Z_to_bv 32 0) None m (seg_rom rsegs)) md) T.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition vep_emit_common_stmt : Prop :=
    forall (VEP : Z) (v : vep) (tag : list byte) (q : vep_pads) (vv : vsb_rec) (l mark : Z) (lo : Z),
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (m : mem) (md : Model) (A : AS) (T : TSet),
      ainv A m md -> mem_inv rsegs m ->
      a0 = Z_to_bv 64 VEP -> a1 = Z_to_bv 64 l -> a2 = Z_to_bv 64 mark ->
      0 <= l -> v Fo_total + l < 2^62 -> 0 <= v Fo_total -> bool01 mark ->
      vep_obj LayoutP0 A m VEP v tag q -> v Fdogzip = 0 -> vsb_obj LayoutP0 A m (v Fvsb) vv false -> VEP <> v Fvsb -> VEP <> vb_buf vv ->
      vb_size vv + 9 <= EXT_MAX ->
      a_livebytes A + vsb_extendsize (vb_size vv + 9) <= LIVE_MAX -> a_nlive A + 1 <= NLIVE_MAX ->   (* [comment removed for export] *)
      tp = al_tp LayoutP0 -> bv_unsigned sp mod 16 = 0 -> bv_unsigned ra mod 2 = 0 ->
      stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + EMITC_STACK <= bv_unsigned sp ->
      bv_unsigned sp + 64 <= 2^47 ->
      (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model)
              (v' : vep) (vv' : vsb_rec),
          ainv A' m' md' -> mem_inv rsegs m' -> md_frame md md' ->
          stk rsegs m' lo (bv_unsigned sp) ->
          vep_obj LayoutP0 A' m' VEP v' tag q ->
          (   (l = 0 /\ v' = v /\ vv' = vv)
           \/ (1 <= l /\ exists c, v' = fupd (fupd (fupd v Fcrc c) Fo_crc 0) Fo_total (v Fo_total + l))) ->
          vsb_obj LayoutP0 A' m' (v Fvsb) vv' false ->
          vb_len vv <= vb_len vv' <= vb_len vv + Z.min 9 (2 + l) ->
          vb_size vv <= vb_size vv' <= Z.max (vb_size vv) (vb_len vv' + 4096) ->
          (vb_buf vv' = vb_buf vv \/ (a_live A (vb_buf vv') = None /\ a_live A' (vb_buf vv) = None)) ->
          (forall p, p <> vb_buf vv -> p <> vb_buf vv' -> a_live A' p = a_live A p) ->
          a_livebytes A' = a_livebytes A + vb_size vv' - vb_size vv -> a_nlive A' = a_nlive A ->   (* [comment removed for export] *)
          cframe LayoutP0 (owned A) (owned A') (bv_unsigned sp) EMITC_STACK
                 (fun a => blk VEP 312 a \/ blk (vb_buf vv) (vb_size vv) a \/ (v Fvsb <= a < v Fvsb + 40))
                 (blk (vb_buf vv') (vb_size vv')) m m' ->
          realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                     bvmap_empty (ret_pc ra) (Z_to_bv 32 0) None m' (seg_rom rsegs)) md') T) ->
      realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 bvmap_empty (Z_to_bv 64 vep_emit_common_entry) (Z_to_bv 32 0) None m (seg_rom rsegs)) md) T.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition MARK_FIELDS : list vf :=
    [Fcrc; Fcrcp; Fo_crc; Fo_wait; Fo_pending; Fo_last; Fo_total; Fver_p; Flast_mark; Fcb_x].

  Definition vep_mark_common_stmt : Prop :=
    forall (VEP : Z) (v : vep) (tag : list byte) (q : vep_pads) (vv : vsb_rec) (H : henv) (p mark n : Z) (seg : list byte) (lo : Z),
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (m : mem) (md : Model) (A : AS) (T : TSet),
      ainv A m md -> mem_inv rsegs m ->
      a0 = Z_to_bv 64 VEP -> a1 = Z_to_bv 64 p -> a2 = Z_to_bv 64 mark -> bool01 mark ->
      vep_obj LayoutP0 A m VEP v tag q -> vep_base H VEP v -> henv_ok LayoutP0 VI0 H m -> henv_geom H -> img_ok0 m ->
      bool01 (v Flast_mark) -> vep_cnt v n -> 0 <= n -> n + (p - v Fver_p) < NMAX ->
      vsb_obj LayoutP0 A m (v Fvsb) vv false -> VEP <> v Fvsb -> VEP <> vb_buf vv -> vb_size vv + 9 <= EXT_MAX ->
      a_livebytes A + vsb_extendsize (vb_size vv + 9) <= LIVE_MAX -> a_nlive A + 1 <= NLIVE_MAX ->   (* [comment removed for export] *)
      (* [comment removed for export] *)
      bytes_at rsegs m (v Fver_p) seg -> Z.of_nat (length seg) = p - v Fver_p -> 4096 <= v Fver_p -> p <= alloc_ceiling ->
      (* [comment removed for export] *)
      ((v Fver_p = vi_empty VI0 /\ seg = []) \/
       (exists d k, a_live A d = Some k /\ 0 < k /\ d <= v Fver_p /\ p <= d + k /\ d <> VEP /\ d <> v Fvsb /\ d <> vb_buf vv)) ->
      tp = al_tp LayoutP0 -> bv_unsigned sp mod 16 = 0 -> bv_unsigned ra mod 2 = 0 ->
      stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + MARK_STACK <= bv_unsigned sp ->
      bv_unsigned sp <= h_sp H ->
      (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model)
              (v' : vep) (vv' : vsb_rec),
          ainv A' m' md' -> mem_inv rsegs m' -> md_frame md md' ->
          stk rsegs m' lo (bv_unsigned sp) ->
          vep_obj LayoutP0 A' m' VEP v' tag q -> vkeep v v' MARK_FIELDS ->
          v' Fver_p = p -> v' Flast_mark = mark -> v' Fo_pending = 0 -> vep_cnt v' (n + (p - v Fver_p)) ->
          0 <= v' Fcrc < 2^64 -> 0 <= v' Fcrcp < 2^64 ->
          vsb_obj LayoutP0 A' m' (v Fvsb) vv' false ->
          vb_len vv <= vb_len vv' <= vb_len vv + 3 * (v' Fo_last - v Fo_last) ->
          vb_size vv <= vb_size vv' <= Z.max (vb_size vv) (vb_len vv' + 4096) ->
          (vb_buf vv' = vb_buf vv \/ (a_live A (vb_buf vv') = None /\ a_live A' (vb_buf vv) = None)) ->
          (forall r, r <> vb_buf vv -> r <> vb_buf vv' -> a_live A' r = a_live A r) ->
          a_livebytes A' = a_livebytes A + vb_size vv' - vb_size vv -> a_nlive A' = a_nlive A ->   (* [comment removed for export] *)
          henv_ok LayoutP0 VI0 H m' -> bytes_at rsegs m' (v Fver_p) seg ->
          cframe LayoutP0 (owned A) (owned A') (bv_unsigned sp) MARK_STACK
                 (fun a => blk VEP 312 a \/ blk (vb_buf vv) (vb_size vv) a \/ (v Fvsb <= a < v Fvsb + 40))
                 (blk (vb_buf vv') (vb_size vv')) m m' ->
          realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                     bvmap_empty (ret_pc ra) (Z_to_bv 32 0) None m' (seg_rom rsegs)) md') T) ->
      realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 bvmap_empty (Z_to_bv 64 vep_mark_common_entry) (Z_to_bv 32 0) None m (seg_rom rsegs)) md) T.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition WS_Init_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (H : henv) (lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ munch [(bv_unsigned sp - WSINIT_STACK, bv_unsigned sp); (h_ws H, h_ws H + 40); (h_wsbuf H, h_wsbuf H + 32)] m m'
      /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
      /\ ws0_obj LayoutP0 H m' /\ glob_ok LayoutP0 VI0 H m'.

  Definition WS_Init_stmt : Prop :=
    forall (H : henv) (junk40 junk32 : list byte) (lo : Z),
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem),
      a0 = Z_to_bv 64 (h_ws H) -> a1 = Z_to_bv 64 0x10577 -> a2 = Z_to_bv 64 (h_wsbuf H) -> a3 = Z_to_bv 64 1024 ->
      rw_cells rsegs m (h_ws H) [CB 40 junk40] -> rw_cells rsegs m (h_wsbuf H) [CB 32 junk32] ->
      glob_ok LayoutP0 VI0 H m -> henv_geom H -> img_ok0 m ->
      bv_unsigned sp = h_sp H ->
      stk rsegs m lo (bv_unsigned sp) -> lo + WSINIT_STACK <= bv_unsigned sp -> alloc_ceiling <= lo ->
      mem_inv rsegs m ->
      evt rsegs (WS_Init_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc H lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 WS_Init_entry) fc None m (seg_rom rsegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition WS_Alloc_stmt : Prop :=
    forall (H : henv) (lo : Z),
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (m : mem) (md : Model) (A : AS) (T : TSet),
      ainv A m md -> mem_inv rsegs m -> (exists r k, a_live A r = Some k) ->
      a0 = Z_to_bv 64 (h_ws H) -> a1 = Z_to_bv 64 312 ->
      ws0_obj LayoutP0 H m -> glob_ok LayoutP0 VI0 H m -> henv_geom H -> img_ok0 m ->
      a_livebytes A + 352 <= LIVE_MAX -> a_nlive A + 2 <= NLIVE_MAX ->   (* [comment removed for export] *)
      tp = al_tp LayoutP0 -> bv_unsigned sp mod 16 = 0 -> bv_unsigned ra mod 2 = 0 ->
      stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + WSALLOC_STACK <= bv_unsigned sp ->
      bv_unsigned sp <= h_sp H ->
      (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (r : Z) (A' : AS) (m' : mem) (md' : Model),
          ainv A' m' md' -> mem_inv rsegs m' -> md_frame md md' ->
          stk rsegs m' lo (bv_unsigned sp) -> glob_ok LayoutP0 VI0 H m' ->
          (* [comment removed for export] *)
              (exists wa junk, r <> 0 /\ ws1_obj LayoutP0 H A' m' wa r /\ rw_cells rsegs m' r [CB 312 junk] /\
               a_live A wa = None /\ a_live A r = None /\
               (forall p, p <> wa -> p <> r -> a_live A' p = a_live A p) /\
               a_livebytes A' = a_livebytes A + 352 /\ a_nlive A' = a_nlive A + 2 /\
               cframe LayoutP0 (owned A) (owned A') (bv_unsigned sp) WSALLOC_STACK
                      (fun a => h_ws H <= a < h_ws H + 40 \/ h_wsbuf H <= a < h_wsbuf H + 32)
                      (fun a => blk wa 40 a \/ blk r 312 a) m m') ->
          realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                     bvmap_empty (ret_pc ra) (Z_to_bv 32 0) None m' (seg_rom rsegs)) md') T) ->
      realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 bvmap_empty (Z_to_bv 64 WS_Alloc_entry) (Z_to_bv 32 0) None m (seg_rom rsegs)) md) T.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition WS_Rollback_stmt : Prop :=
    forall (H : henv) (E : option (Z * Z)) (lo : Z),
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (m : mem) (md : Model) (A : AS) (T : TSet),
      ainv A m md -> mem_inv rsegs m ->
      a0 = Z_to_bv 64 (h_ws H) -> a1 = Z_to_bv 64 0 ->
      match E with None => ws0_obj LayoutP0 H m | Some (wa, vep) => ws1_obj LayoutP0 H A m wa vep end ->
      glob_ok LayoutP0 VI0 H m -> henv_geom H -> img_ok0 m ->
      tp = al_tp LayoutP0 -> bv_unsigned sp mod 16 = 0 -> bv_unsigned ra mod 2 = 0 ->
      stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + WSROLLBACK_STACK <= bv_unsigned sp ->
      bv_unsigned sp <= h_sp H ->
      (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model),
          ainv A' m' md' -> mem_inv rsegs m' -> md_frame md md' ->
          stk rsegs m' lo (bv_unsigned sp) -> glob_ok LayoutP0 VI0 H m' -> ws0_obj LayoutP0 H m' ->
          match E with
          | None => (forall p, a_live A' p = a_live A p) /\ a_livebytes A' = a_livebytes A /\ a_nlive A' = a_nlive A
          | Some (wa, vep) => a_live A' wa = None /\ a_live A' vep = None /\
                              (forall p, p <> wa -> p <> vep -> a_live A' p = a_live A p) /\
                              a_livebytes A' = a_livebytes A - 352 /\ a_nlive A' = a_nlive A - 2
          end ->
          cframe LayoutP0 (owned A) (owned A') (bv_unsigned sp) WSROLLBACK_STACK
                 (fun a => h_ws H <= a < h_ws H + 40 \/ h_wsbuf H <= a < h_wsbuf H + 32 \/
                           match E with None => False | Some (wa, vep) => blk wa 40 a \/ blk vep 312 a end)
                 nowhere m m' ->
          realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                     bvmap_empty (ret_pc ra) (Z_to_bv 32 0) None m' (seg_rom rsegs)) md') T) ->
      realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 bvmap_empty (Z_to_bv 64 WS_Rollback_entry) (Z_to_bv 32 0) None m (seg_rom rsegs)) md) T.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition vep_init_map (H : henv) (VEP S flags : Z) : vep :=
    fun f => match f with
             | Fflags => flags | Fvsb => S | Furl => vi_url VI0 | Fvc => h_vc H | Fcb => vi_cb VI0
             | Fcb_priv => VEP + 56 | Fstate => vi_st VI0 S_Start | Fstartup => 1 | _ => 0 end.

  Definition VEP_Init_stmt : Prop :=
    forall (H : henv) (flags : Z) (lo : Z),
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (m : mem) (md : Model) (A : AS) (T : TSet),
      ainv A m md -> mem_inv rsegs m -> (exists r k, a_live A r = Some k) ->
      a0 = Z_to_bv 64 (h_vc H) -> a1 = Z_to_bv 64 (h_req H) -> a2 = Z_to_bv 64 0 -> a3 = Z_to_bv 64 0 -> a4 = Z_to_bv 64 flags ->
      0 <= flags < 16 ->
      ws0_obj LayoutP0 H m -> henv_ok LayoutP0 VI0 H m -> henv_geom H -> img_ok0 m ->
      a_livebytes A + 408 <= LIVE_MAX -> a_nlive A + 4 <= NLIVE_MAX ->   (* [comment removed for export] *)
      tp = al_tp LayoutP0 -> bv_unsigned sp mod 16 = 0 -> bv_unsigned ra mod 2 = 0 ->
      stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + VEPINIT_STACK <= bv_unsigned sp ->
      bv_unsigned sp = h_sp H ->
      (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (r : Z) (A' : AS) (m' : mem) (md' : Model),
          ainv A' m' md' -> mem_inv rsegs m' -> md_frame md md' ->
          stk rsegs m' lo (bv_unsigned sp) -> henv_ok LayoutP0 VI0 H m' -> img_ok0 m' ->
          (* [comment removed for export] *)
              (exists wa tag q b, r <> 0 /\ ws1_obj LayoutP0 H A' m' wa r /\
               (exists S, vep_obj LayoutP0 A' m' r (vep_init_map H r S flags) tag q /\ S <> 0 /\
                          vsb_obj LayoutP0 A' m' S (vsb_fresh b) false /\
                          a_live A S = None /\ a_live A b = None /\ S <> r /\ b <> r /\ S <> wa /\ b <> wa /\
                          a_live A wa = None /\ a_live A r = None /\
                          (forall p, p <> wa -> p <> r -> p <> S -> p <> b -> a_live A' p = a_live A p) /\
                          a_livebytes A' = a_livebytes A + 408 /\ a_nlive A' = a_nlive A + 4 /\
                          cframe LayoutP0 (owned A) (owned A') (bv_unsigned sp) VEPINIT_STACK
                                 (fun a => h_ws H <= a < h_ws H + 40 \/ h_wsbuf H <= a < h_wsbuf H + 32)
                                 (fun a => blk wa 40 a \/ blk r 312 a \/ blk S 40 a \/ blk b 16 a) m m')) ->
          realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                     bvmap_empty (ret_pc ra) (Z_to_bv 32 0) None m' (seg_rom rsegs)) md') T) ->
      realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 bvmap_empty (Z_to_bv 64 VEP_Init_entry) (Z_to_bv 32 0) None m (seg_rom rsegs)) md) T.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition vsb_blocks (S : Z) (x : vsb_rec) (a : Z) : Prop := blk S 40 a \/ blk (vb_buf x) (vb_size x) a.
  Definition vsb_apart (S : Z) (x : vsb_rec) (others : list Z) : Prop :=
    forall y, In y others -> S <> y /\ vb_buf x <> y.

  (* [comment removed for export] *)
  Definition world_len (vv : vsb_rec) (va : option vsb_rec) (vi : option (vsb_rec * bool)) : Z :=
    vb_len vv + match va with None => 0 | Some x => vb_len x end + match vi with None => 0 | Some (x, _) => vb_len x end.
  Definition world_room (vv : vsb_rec) (va : option vsb_rec) (vi : option (vsb_rec * bool)) (N : Z) : Prop :=
    vb_size vv <= vb_len vv + 4096 /\ world_len vv va vi <= 7 * N.
  (* [comment removed for export] *)
  Definition PARSE_LIVE (N : Z) : Z := 24 * N + 32768.
  (* [comment removed for export] *)
  Definition PARSE_NLIVE : Z := 5.
  (* [comment removed for export] *)
  Definition world_nlive (va : option vsb_rec) (vi : option (vsb_rec * bool)) : Z :=
    match va with None => 0 | Some _ => 2 end + match vi with None => 0 | Some _ => 2 end.
  Lemma world_nlive_nonneg : forall va vi, 0 <= world_nlive va vi <= 4.
  Proof. intros [x|] [[y b]|]; unfold world_nlive; lia. Qed.
  (* [comment removed for export] *)
  Definition FIN_LIVE (N : Z) : Z := 20 * N + 16384.
  (* [comment removed for export] *)
  Definition world_bytes (vv : vsb_rec) (va : option vsb_rec) (vi : option (vsb_rec * bool)) : Z :=
    40 + vb_size vv
    + match va with None => 0 | Some x => 40 + vb_size x end
    + match vi with None => 0 | Some (x, _) => 40 + vb_size x end.

  Definition parsed_world (H : henv) (A : AS) (m : mem) (VEP : Z) (v : vep) (tag : list byte) (q : vep_pads)
             (vv : vsb_rec) (va : option vsb_rec) (vi : option (vsb_rec * bool)) (wa n N : Z) : Prop :=
       vep_obj LayoutP0 A m VEP v tag q /\ vep_base H VEP v
    /\ (exists st, v Fstate = vi_st VI0 st) /\ bool01 (v Flast_mark) /\ bool01 (v Fesi_found)
    /\ vep_cnt v n /\ 0 <= n <= N /\ N < NMAX /\ 4096 <= v Fver_p <= alloc_ceiling
    /\ vsb_obj LayoutP0 A m (v Fvsb) vv false /\ world_room vv va vi N /\ vsb_apart (v Fvsb) vv [VEP; wa]
    /\ match va with
       | None => v Fattr_vsb = 0
       | Some x => vsb_obj LayoutP0 A m (v Fattr_vsb) x false /\ vb_size x + 9 <= EXT_MAX /\ vb_size x <= vb_len x + 4096 /\
                   vsb_apart (v Fattr_vsb) x [VEP; wa; v Fvsb; vb_buf vv]
       end
    /\ match vi with
       | None => v Finclude_src = 0
       | Some (x, fi) => vsb_obj LayoutP0 A m (v Finclude_src) x fi /\ vb_size x <= vb_len x + 4096 /\
                   vsb_apart (v Finclude_src) x [VEP; wa; v Fvsb; vb_buf vv] /\
                   match va with None => True | Some y => vsb_apart (v Finclude_src) x [v Fattr_vsb; vb_buf y] end
       end.

  (* [comment removed for export] *)
  Definition parse_changed (H : henv) (VEP S b : Z) (a : Z) : Prop :=
    blk VEP 312 a \/ blk S 40 a \/ blk b 16 a \/ (h_vsc H + 1304 <= a < h_vsc H + 1320).
  Definition finish_changed (H : henv) (VEP : Z) (v : vep) (vv : vsb_rec) (va : option vsb_rec)
             (vi : option (vsb_rec * bool)) (a : Z) : Prop :=
    blk VEP 312 a \/ vsb_blocks (v Fvsb) vv a
    \/ match va with None => False | Some x => vsb_blocks (v Fattr_vsb) x a end
    \/ match vi with None => False | Some (x, _) => vsb_blocks (v Finclude_src) x a end
    \/ (h_vsc H + 1304 <= a < h_vsc H + 1320).
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition parse_blocks (v : vep) (vv : vsb_rec) (va : option vsb_rec) (vi : option (vsb_rec * bool)) (x : Z) : Prop :=
    x = vb_buf vv
    \/ match va with None => False | Some y => x = v Fattr_vsb \/ x = vb_buf y end
    \/ match vi with None => False | Some (y, _) => x = v Finclude_src \/ x = vb_buf y end.
  Definition parse_new (v : vep) (vv : vsb_rec) (va : option vsb_rec) (vi : option (vsb_rec * bool)) (a : Z) : Prop :=
    blk (vb_buf vv) (vb_size vv) a
    \/ match va with None => False | Some x => vsb_blocks (v Fattr_vsb) x a end
    \/ match vi with None => False | Some (x, _) => vsb_blocks (v Finclude_src) x a end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition VEP_Parse_stmt : Prop :=
    forall (H : henv) (VEP S b flags wa DATA : Z) (inp : list byte) (tag : list byte) (q : vep_pads) (lo : Z),
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (m : mem) (md : Model) (A : AS) (T : TSet),
      ainv A m md -> mem_inv rsegs m ->
      a0 = Z_to_bv 64 VEP -> a1 = Z_to_bv 64 DATA -> a2 = Z_to_bv 64 (Z.of_nat (length inp)) ->
      0 <= flags < 16 ->
      vep_obj LayoutP0 A m VEP (vep_init_map H VEP S flags) tag q -> S <> 0 ->
      vsb_obj LayoutP0 A m S (vsb_fresh b) false ->
      ws1_obj LayoutP0 H A m wa VEP -> data_obj LayoutP0 A m DATA inp ->
      henv_ok LayoutP0 VI0 H m -> henv_geom H -> img_ok0 m ->
      VEP <> S -> VEP <> b -> wa <> S -> wa <> b -> DATA <> VEP -> DATA <> S -> DATA <> b -> DATA <> wa ->
      a_livebytes A + PARSE_LIVE (Z.of_nat (length inp)) <= LIVE_MAX -> a_nlive A + PARSE_NLIVE <= NLIVE_MAX ->   (* [comment removed for export] *)
      tp = al_tp LayoutP0 -> bv_unsigned sp mod 16 = 0 -> bv_unsigned ra mod 2 = 0 ->
      stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + PARSE_STACK <= bv_unsigned sp ->
      bv_unsigned sp = h_sp H ->
      (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model)
              (v' : vep) (tag' : list byte) (q' : vep_pads) (vv' : vsb_rec) (va : option vsb_rec)
              (vi : option (vsb_rec * bool)) (n : Z),
          ainv A' m' md' -> mem_inv rsegs m' -> md_frame md md' ->
          stk rsegs m' lo (bv_unsigned sp) -> henv_ok LayoutP0 VI0 H m' -> img_ok0 m' ->
          parsed_world H A' m' VEP v' tag' q' vv' va vi wa n (Z.of_nat (length inp)) -> v' Fvsb = S ->
          DATA <= v' Fver_p <= DATA + Z.of_nat (length inp) ->
          ws1_obj LayoutP0 H A' m' wa VEP -> data_obj LayoutP0 A' m' DATA inp ->
          (* [comment removed for export] *)
          (forall p k, a_live A p = Some k -> p <> b -> a_live A' p = Some k) ->
          (forall x, parse_blocks v' vv' va vi x -> x = b \/ a_live A x = None) ->
          a_livebytes A' = a_livebytes A - 56 + world_bytes vv' va vi -> a_nlive A' = a_nlive A + world_nlive va vi ->   (* [comment removed for export] *)
          cframe LayoutP0 (owned A) (owned A') (bv_unsigned sp) PARSE_STACK (parse_changed H VEP S b)
                 (parse_new v' vv' va vi) m m' ->
          realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                     bvmap_empty (ret_pc ra) (Z_to_bv 32 0) None m' (seg_rom rsegs)) md') T) ->
      realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 bvmap_empty (Z_to_bv 64 VEP_Parse_entry) (Z_to_bv 32 0) None m (seg_rom rsegs)) md) T.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition VEP_Finish_stmt : Prop :=
    forall (H : henv) (VEP wa n N DATA : Z) (v : vep) (tag : list byte) (q : vep_pads) (vv : vsb_rec) (va : option vsb_rec) (vi : option (vsb_rec * bool)) (lo : Z),
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (m : mem) (md : Model) (A : AS) (T : TSet),
      ainv A m md -> mem_inv rsegs m ->
      a0 = Z_to_bv 64 VEP ->
      parsed_world H A m VEP v tag q vv va vi wa n N ->
      ws1_obj LayoutP0 H A m wa VEP -> henv_ok LayoutP0 VI0 H m -> henv_geom H -> img_ok0 m ->
      (* [comment removed for export] *)
      a_live A DATA = Some N -> 0 < N -> DATA <= v Fver_p <= DATA + N -> DATA <> VEP -> DATA <> v Fvsb ->
      ~ parse_blocks v vv va vi DATA ->
      a_livebytes A + FIN_LIVE N <= LIVE_MAX -> a_nlive A + 1 <= NLIVE_MAX ->   (* [comment removed for export] *)
      tp = al_tp LayoutP0 -> bv_unsigned sp mod 16 = 0 -> bv_unsigned ra mod 2 = 0 ->
      stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + VEPFIN_STACK <= bv_unsigned sp ->
      bv_unsigned sp = h_sp H ->
      (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (r : Z) (A' : AS) (m' : mem) (md' : Model)
              (v' : vep) (vr : vsb_rec),
          ainv A' m' md' -> mem_inv rsegs m' -> md_frame md md' ->
          stk rsegs m' lo (bv_unsigned sp) -> henv_ok LayoutP0 VI0 H m' -> img_ok0 m' ->
          vep_obj LayoutP0 A' m' VEP v' tag q -> ws1_obj LayoutP0 H A' m' wa VEP ->
          (r = 0 \/ (r <> 0 /\ r = v Fvsb /\ vsb_obj LayoutP0 A' m' r vr true /\ vsb_apart r vr [VEP; wa] /\
                     (parse_blocks v vv va vi (vb_buf vr) \/ a_live A (vb_buf vr) = None))) ->
          (* [comment removed for export] *)
          (forall p k, a_live A p = Some k -> p <> v Fvsb -> ~ parse_blocks v vv va vi p -> a_live A' p = Some k) ->
          (* [comment removed for export] *)
          a_livebytes A' = a_livebytes A - world_bytes vv va vi + (if Z.eqb r 0 then 0 else 40 + vb_size vr) ->
          a_nlive A' = a_nlive A - world_nlive va vi - (if Z.eqb r 0 then 2 else 0) ->
          cframe LayoutP0 (owned A) (owned A') (bv_unsigned sp) VEPFIN_STACK (finish_changed H VEP v vv va vi)
                 (fun a => r <> 0 /\ vsb_blocks r vr a) m m' ->
          realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                     bvmap_empty (ret_pc ra) (Z_to_bv 32 0) None m' (seg_rom rsegs)) md') T) ->
      realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 bvmap_empty (Z_to_bv 64 VEP_Finish_entry) (Z_to_bv 32 0) None m (seg_rom rsegs)) md) T.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition vep_do_comment_stmt : Prop :=
    forall (VEP : Z) (v : vep) (tag : list byte) (q : vep_pads) (H : henv) (lo : Z),
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem),
      a0 = Z_to_bv 64 VEP -> a1 = Z_to_bv 64 1 ->
      rw_cells rsegs m VEP (vep_cells v tag q) -> length tag = 8%nat -> vep_pads_wf q -> bool01 (v Femptytag) ->
      v Fvc = h_vc H -> henv_ok LayoutP0 VI0 H m -> henv_geom H -> img_ok0 m ->
      4096 <= VEP -> VEP mod 8 = 0 -> VEP + 312 <= alloc_ceiling ->
      stk rsegs m lo (bv_unsigned sp) -> lo + VEPERR_STACK <= bv_unsigned sp -> alloc_ceiling <= lo ->
      bv_unsigned sp <= h_sp H ->
      mem_inv rsegs m ->
      evt rsegs (vep_error_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc H lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 vep_do_comment_entry) fc None m (seg_rom rsegs)).

  (* [comment removed for export] *)
  Definition vep_do_remove_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (H : henv) (VEP : Z) (v : vep) (tag : list byte) (q : vep_pads) (lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' rm,
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ munch [(bv_unsigned sp - VEPERR_STACK, bv_unsigned sp); (h_vsc H + 1304, h_vsc H + 1320); (VEP + 92, VEP + 96)] m m'
      /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ henv_ok LayoutP0 VI0 H m' /\ stk rsegs m' lo (bv_unsigned sp)
      /\ bool01 rm /\ rw_cells rsegs m' VEP (vep_cells (fupd v Fremove rm) tag q).

  Definition vep_do_remove_stmt : Prop :=
    forall (VEP : Z) (v : vep) (tag : list byte) (q : vep_pads) (H : henv) (lo : Z),
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem),
      a0 = Z_to_bv 64 VEP -> a1 = Z_to_bv 64 1 ->
      rw_cells rsegs m VEP (vep_cells v tag q) -> length tag = 8%nat -> vep_pads_wf q ->
      bool01 (v Femptytag) -> bool01 (v Fendtag) -> bool01 (v Fremove) ->
      v Fvc = h_vc H -> henv_ok LayoutP0 VI0 H m -> henv_geom H -> img_ok0 m ->
      4096 <= VEP -> VEP mod 8 = 0 -> VEP + 312 <= alloc_ceiling -> off_image LayoutP0 VEP 312 ->
      stk rsegs m lo (bv_unsigned sp) -> lo + VEPERR_STACK <= bv_unsigned sp -> alloc_ceiling <= lo ->
      bv_unsigned sp <= h_sp H ->
      mem_inv rsegs m ->
      evt rsegs (vep_do_remove_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc H VEP v tag q lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 vep_do_remove_entry) fc None m (seg_rom rsegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition vep_do_include_attr_stmt : Prop :=
    forall (VEP : Z) (v : vep) (tag : list byte) (q : vep_pads) (ya : vsb_rec) (vi : option vsb_rec) (H : henv) (lo : Z),
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (m : mem) (md : Model) (A : AS) (T : TSet),
      ainv A m md -> mem_inv rsegs m ->
      a0 = Z_to_bv 64 VEP -> a1 = Z_to_bv 64 0 ->
      vep_obj LayoutP0 A m VEP v tag q -> vep_base H VEP v -> henv_ok LayoutP0 VI0 H m -> henv_geom H -> img_ok0 m ->
      (v Fmatch_hit = vi_tbl_attr_include VI0 \/ v Fmatch_hit = vi_tbl_attr_include VI0 + 16) -> bool01 (v Finclude_continue) ->
      v Fattr_vsb <> 0 -> vsb_obj LayoutP0 A m (v Fattr_vsb) ya true -> vb_error ya = 0 ->
      v Fattr_vsb <> VEP -> vb_buf ya <> VEP ->
      match vi with
      | None => v Finclude_src = 0
      | Some yi => v Finclude_src <> 0 /\ vsb_obj LayoutP0 A m (v Finclude_src) yi true /\ vb_error yi = 0 /\
                   v Finclude_src <> VEP /\ vb_buf yi <> VEP /\ v Finclude_src <> v Fattr_vsb /\ v Finclude_src <> vb_buf ya /\
                   vb_buf yi <> v Fattr_vsb /\ vb_buf yi <> vb_buf ya
      end ->
      tp = al_tp LayoutP0 -> bv_unsigned sp mod 16 = 0 -> bv_unsigned ra mod 2 = 0 ->
      stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + DOINCL_STACK <= bv_unsigned sp ->
      bv_unsigned sp <= h_sp H ->
      (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model)
              (v' : vep) (vi' : option vsb_rec),
          ainv A' m' md' -> mem_inv rsegs m' -> md_frame md md' ->
          stk rsegs m' lo (bv_unsigned sp) -> henv_ok LayoutP0 VI0 H m' ->
          vep_obj LayoutP0 A' m' VEP v' tag q ->
          (  (* [comment removed for export] *) (vi = None /\ v' = fupd (fupd v Finclude_src (v Fattr_vsb)) Fattr_vsb 0 /\ vi' = Some ya /\
                        (forall r, a_live A' r = a_live A r) /\ a_livebytes A' = a_livebytes A /\ a_nlive A' = a_nlive A)
          \/ (* [comment removed for export] *) (vi <> None /\ v' = fupd (fupd (fupd v Fstate (vi_st VI0 S_TagError)) Fattr_vsb 0) Finclude_src 0 /\ vi' = None /\
                        a_live A' (v Fattr_vsb) = None /\ a_live A' (vb_buf ya) = None /\
                        (match vi with Some yi => a_live A' (v Finclude_src) = None /\ a_live A' (vb_buf yi) = None /\
                                                  a_livebytes A' = a_livebytes A - 80 - vb_size ya - vb_size yi /\ a_nlive A' = a_nlive A - 4
                                     | None => False end) /\
                        (forall r, r <> v Fattr_vsb -> r <> vb_buf ya -> r <> v Finclude_src ->
                                   r <> match vi with Some yi => vb_buf yi | None => 0 end -> a_live A' r = a_live A r))
          \/ (* [comment removed for export] *) (vi = None /\ v' = fupd (fupd v Fstate (vi_st VI0 S_TagError)) Fattr_vsb 0 /\ vi' = None /\
                        a_live A' (v Fattr_vsb) = None /\ a_live A' (vb_buf ya) = None /\
                        a_livebytes A' = a_livebytes A - 40 - vb_size ya /\ a_nlive A' = a_nlive A - 2 /\
                        (forall r, r <> v Fattr_vsb -> r <> vb_buf ya -> a_live A' r = a_live A r))
          \/ (* [comment removed for export] *) (exists ic, bool01 ic /\ v' = fupd (fupd v Finclude_continue ic) Fattr_vsb 0 /\ vi' = vi /\
                        a_live A' (v Fattr_vsb) = None /\ a_live A' (vb_buf ya) = None /\
                        a_livebytes A' = a_livebytes A - 40 - vb_size ya /\ a_nlive A' = a_nlive A - 2 /\
                        (forall r, r <> v Fattr_vsb -> r <> vb_buf ya -> a_live A' r = a_live A r))) ->
          match vi' with
          | None => v' Finclude_src = 0
          | Some yi => v' Finclude_src <> 0 /\ vsb_obj LayoutP0 A' m' (v' Finclude_src) yi true /\ vb_error yi = 0
          end ->
          cframe LayoutP0 (owned A) (owned A') (bv_unsigned sp) DOINCL_STACK
                 (fun a => blk VEP 312 a \/ vsb_blocks (v Fattr_vsb) ya a
                           \/ match vi with Some yi => vsb_blocks (v Finclude_src) yi a | None => False end
                           \/ (h_vsc H + 1304 <= a < h_vsc H + 1320))
                 nowhere m m' ->
          realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                     bvmap_empty (ret_pc ra) (Z_to_bv 32 0) None m' (seg_rom rsegs)) md') T) ->
      realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 bvmap_empty (Z_to_bv 64 vep_do_include_entry) (Z_to_bv 32 0) None m (seg_rom rsegs)) md) T.

  (* [comment removed for export] *)
  Definition vep_do_include_tag_stmt : Prop :=
    forall (VEP : Z) (v : vep) (tag : list byte) (q : vep_pads) (vv : vsb_rec) (vi : option vsb_rec) (H : henv) (lo : Z),
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (m : mem) (md : Model) (A : AS) (T : TSet),
      ainv A m md -> mem_inv rsegs m ->
      a0 = Z_to_bv 64 VEP -> a1 = Z_to_bv 64 1 ->
      vep_obj LayoutP0 A m VEP v tag q -> vep_base H VEP v -> henv_ok LayoutP0 VI0 H m -> henv_geom H -> img_ok0 m ->
      0 <= v Fflags < 16 -> bool01 (v Femptytag) -> bool01 (v Finclude_continue) -> v Flast_mark = 1 -> v Fattr_vsb = 0 ->
      vsb_obj LayoutP0 A m (v Fvsb) vv false -> VEP <> v Fvsb -> VEP <> vb_buf vv ->
      vb_size vv <= vb_len vv + 4096 ->
      vb_len vv + match vi with Some yi => vb_len yi | None => 0 end + 8 <= 2^29 ->
      (* [comment removed for export] *)
      a_livebytes A + vb_size vv + vb_len vv + 2 * match vi with Some yi => vb_len yi | None => 0 end + 12304 <= LIVE_MAX ->
      a_nlive A + 1 <= NLIVE_MAX ->
      match vi with
      | None => v Finclude_src = 0
      | Some yi => v Finclude_src <> 0 /\ vsb_obj LayoutP0 A m (v Finclude_src) yi true /\ vb_error yi = 0 /\
                   v Finclude_src <> VEP /\ vb_buf yi <> VEP /\ v Finclude_src <> v Fvsb /\ v Finclude_src <> vb_buf vv /\
                   vb_buf yi <> v Fvsb /\ vb_buf yi <> vb_buf vv
      end ->
      tp = al_tp LayoutP0 -> bv_unsigned sp mod 16 = 0 -> bv_unsigned ra mod 2 = 0 ->
      stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + DOINCL_STACK <= bv_unsigned sp ->
      bv_unsigned sp <= h_sp H ->
      (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model)
              (v' : vep) (vv' : vsb_rec),
          ainv A' m' md' -> mem_inv rsegs m' -> md_frame md md' ->
          stk rsegs m' lo (bv_unsigned sp) -> henv_ok LayoutP0 VI0 H m' ->
          vep_obj LayoutP0 A' m' VEP v' tag q -> vkeep v v' [Fstate; Finclude_src; Finclude_continue] ->
          (v' Fstate = v Fstate \/ v' Fstate = vi_st VI0 S_TagError) -> bool01 (v' Finclude_continue) -> v' Finclude_src = 0 ->
          vsb_obj LayoutP0 A' m' (v Fvsb) vv' false ->
          vb_len vv <= vb_len vv' <= vb_len vv + match vi with Some yi => vb_len yi + 8 | None => 0 end ->
          vb_size vv <= vb_size vv' <= Z.max (vb_size vv) (vb_len vv' + 4096) ->
          (vb_buf vv' = vb_buf vv \/ (a_live A (vb_buf vv') = None /\ a_live A' (vb_buf vv) = None)) ->
          match vi with
          | None => (forall r, a_live A' r = a_live A r) /\ a_livebytes A' = a_livebytes A /\ a_nlive A' = a_nlive A
          | Some yi => a_live A' (v Finclude_src) = None /\ a_live A' (vb_buf yi) = None /\
                       (forall r, r <> vb_buf vv -> r <> vb_buf vv' -> r <> v Finclude_src -> r <> vb_buf yi -> a_live A' r = a_live A r) /\
                       a_livebytes A' = a_livebytes A + (vb_size vv' - vb_size vv) - 40 - vb_size yi /\ a_nlive A' = a_nlive A - 2
          end ->
          cframe LayoutP0 (owned A) (owned A') (bv_unsigned sp) DOINCL_STACK
                 (fun a => blk VEP 312 a \/ blk (vb_buf vv) (vb_size vv) a \/ (v Fvsb <= a < v Fvsb + 40)
                           \/ match vi with Some yi => vsb_blocks (v Finclude_src) yi a | None => False end
                           \/ (h_vsc H + 1304 <= a < h_vsc H + 1320))
                 (blk (vb_buf vv') (vb_size vv')) m m' ->
          realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                     bvmap_empty (ret_pc ra) (Z_to_bv 32 0) None m' (seg_rom rsegs)) md') T) ->
      realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 bvmap_empty (Z_to_bv 64 vep_do_include_entry) (Z_to_bv 32 0) None m (seg_rom rsegs)) md) T.

End C.

(* [comment removed for export] *)
Section PW.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutP0}.

  Lemma vsb_blocks_bound : forall A m md S x fin a,
    ainv A m md -> vsb_obj LayoutP0 A m S x fin -> vsb_blocks S x a -> 4096 <= a < alloc_ceiling.
  Proof.
    intros A m md S x fin a AI0 VO X.
    (first [ pose proof ((vsb_obj_geom LayoutP0 A m md S x fin AI0 VO)) as dR_1; dand8 dR_1 as _ S1 S2 _ _ B1 B2 _ | pose proof (vsb_obj_geom LayoutP0 A m md S x fin AI0 VO) as (_ & S1 & S2 & _ & _ & B1 & B2 & _) ]).
    unfold vsb_blocks, blk in X. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma parsed_world_room : forall H A m VEP v tag q vv va vi wa n N,
    parsed_world H A m VEP v tag q vv va vi wa n N -> vsb_room vv N /\ world_bytes vv va vi <= 7 * N + 12408.
  Proof.
    intros H A m VEP v tag q vv va vi wa n N PW.
    (first [ dand14 PW as _ _ _ _ _ _ _ _ _ VO WR _ VA VI | destruct PW as (_ & _ & _ & _ & _ & _ & _ & _ & _ & VO & WR & _ & VA & VI) ]).
    destruct WR as [SZ WL]. unfold world_len in WL. unfold vsb_room, world_bytes.
    pose proof (proj1 (proj2 VO)) as IV. unfold vsb_inv in IV.
    destruct va as [x|]; [destruct VA as (VOa & _ & SZa & _); pose proof (proj1 (proj2 VOa)) as IVa; unfold vsb_inv in IVa|];
    (destruct vi as [[y fi]|]; [destruct VI as (VOi & SZi & _); pose proof (proj1 (proj2 VOi)) as IVi; unfold vsb_inv in IVi|]);
    lia.
  Qed.

  Lemma parse_new_bound : forall H A m VEP v tag q vv va vi wa n N md a,
    ainv A m md -> parsed_world H A m VEP v tag q vv va vi wa n N -> parse_new v vv va vi a ->
    4096 <= a < alloc_ceiling.
  Proof.
    intros H A m VEP v tag q vv va vi wa n N md a AI0 PW X.
    (first [ dand14 PW as _ _ _ _ _ _ _ _ _ VO _ _ VA VI | destruct PW as (_ & _ & _ & _ & _ & _ & _ & _ & _ & VO & _ & _ & VA & VI) ]).
    destruct X as [X|[X|X]].
    - (first [ pose proof ((vsb_obj_geom LayoutP0 A m md _ _ _ AI0 VO)) as dR_3; dand8 dR_3 as _ _ _ _ _ B1 B2 _ | pose proof (vsb_obj_geom LayoutP0 A m md _ _ _ AI0 VO) as (_ & _ & _ & _ & _ & B1 & B2 & _) ]). unfold blk in X. lia.
    - destruct va as [x|]; [|destruct X]. destruct VA as (VO2 & _). eapply vsb_blocks_bound; [exact AI0| exact VO2| exact X].
    - destruct vi as [[x fi]|]; [|destruct X]. destruct VI as (VO3 & _). eapply vsb_blocks_bound; [exact AI0| exact VO3| exact X].
  Qed.

  Lemma finish_changed_cases : forall H VEP v vv va vi a,
    finish_changed H VEP v vv va vi a ->
    blk VEP 312 a \/ blk (v Fvsb) 40 a \/ parse_new v vv va vi a \/ (h_vsc H + 1304 <= a < h_vsc H + 1320).
  Proof.
    intros H VEP v vv va vi a X. unfold finish_changed, parse_new, vsb_blocks in *. tauto.
  Qed.

  Lemma finish_changed_bound : forall H A m VEP v tag q vv va vi wa n N md a,
    ainv A m md -> parsed_world H A m VEP v tag q vv va vi wa n N -> finish_changed H VEP v vv va vi a ->
    (h_vsc H + 1304 <= a < h_vsc H + 1320) \/ 4096 <= a < alloc_ceiling.
  Proof.
    intros H A m VEP v tag q vv va vi wa n N md a AI0 PW X.
    destruct (finish_changed_cases H VEP v vv va vi a X) as [Y|[Y|[Y|Y]]]; [| | right; eapply parse_new_bound; eauto | left; exact Y].
    - destruct PW as (VO & _). destruct VO as (LV & _). destruct (live_geom LayoutP0 A m md _ _ AI0 LV) as (_ & _ & ? & ? & _). unfold blk in Y. lia.
    - (first [ dand11 PW as _ _ _ _ _ _ _ _ _ VO _ | destruct PW as (_ & _ & _ & _ & _ & _ & _ & _ & _ & VO & _) ]).
      pose proof (vsb_obj_geom LayoutP0 A m md _ _ _ AI0 VO) as (_ & ? & ? & _). unfold blk in Y. lia.
  Qed.
End PW.
