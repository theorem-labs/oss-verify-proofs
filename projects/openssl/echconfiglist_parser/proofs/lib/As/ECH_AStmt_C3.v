(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr SysStep Exec CellsX TacX.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsStack0 ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface ECH_AStmt_C0 ECH_AStmt_C1 ECH_AStmt_C2.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
Definition CTXINIT_CNT : Z := 160.
Definition CTXINIT_BYTES : Z := 2^16.
Definition CTXINIT_STACK : Z := 1024 + AREALLOC_STACK.
Definition GETDEFCTX_STACK : Z := FR_get_default_context + CGETLOCAL_STACK.                 (* [comment removed for export] *)
Definition ctxph_cnt (ph : ctxphase) : Z := match ph with CtxFresh => CTXINIT_CNT | CtxReady _ => 0 end.
Definition ctxph_bytes (ph : ctxphase) : Z := match ph with CtxFresh => CTXINIT_BYTES | CtxReady _ => 0 end.
Definition ctxph_stack (ph : ctxphase) : Z := match ph with CtxFresh => FR_get_default_context + CTXINIT_STACK | CtxReady _ => GETDEFCTX_STACK end.
(* [comment removed for export] *)
Definition ctxph_foot (ph : ctxphase) : list (Z * Z) := match ph with CtxFresh => CTX_X ++ AERRNO_X | CtxReady _ => [] end.
Lemma Forall_ctxph_foot : forall (P : Z * Z -> Prop) ph, Forall P (CTX_X ++ AERRNO_X) -> Forall P (ctxph_foot ph).
Proof. intros P [|x] HF; [exact HF| apply Forall_nil]. Qed.
Lemma rin_ivs_ctxph_foot : forall ph a, rin_ivs (ctxph_foot ph) a -> rin_ivs (CTX_X ++ AERRNO_X) a.
Proof. intros [|x] a Ha; [exact Ha| destruct Ha]. Qed.
(* [comment removed for export] *)
Lemma CTX_X_AERRNO_range : Forall (fun iv : Z * Z => 0x5b1000 <= fst iv /\ snd iv <= AIMG_TOP) (CTX_X ++ AERRNO_X).
Proof.
  unfold CTX_X, AERRNO_X, ATP, A_destructor_key, A_defctx_inited, A_defctx, A_defctx_tlkey, A_defctx_tlkey_once, A_defctx_tlkey_ret, A_defctx_once, A_defctx_once_ret,
    A_base_inited, A_in_init_config_key, A_base_once, A_base_ret, A_optsdone_lock, A_init_lock, A_td_cancelbuf, A_keys, A_next_key, A_key_lock, AIMG_TOP.
  cbn [app]. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil.
Qed.
Lemma ctxph_foot_rangeX : forall ph, Forall (fun iv : Z * Z => 0x5b1000 <= fst iv /\ snd iv <= AIMG_TOP) (ctxph_foot ph).
Proof. intros ph. apply Forall_ctxph_foot. apply CTX_X_AERRNO_range. Qed.
(* [comment removed for export] *)
Definition ctxph_delta (ph : ctxphase) (LBN : list block) (x : ctxinfo) : Prop :=
  match ph with
  | CtxReady x0 => x = x0 /\ LBN = []
  | CtxFresh => Z.of_nat (length LBN) <= CTXINIT_CNT /\ lb_bytes LBN <= CTXINIT_BYTES
               /\ In (cx_exlock x) LBN /\ (exists po pi, In (po, cx_olock x, 40) LBN /\ In (pi, cx_ilock x, 40) LBN)
  end.
(* [comment removed for export] *)
Definition ctxph_frames (ph : ctxphase) : nat := match ph with CtxFresh => 4%nat | CtxReady _ => 1%nat end.
Definition gdf_frames (ph : ctxphase) : nat := match ph with CtxFresh => 3%nat | CtxReady _ => 0%nat end.
Lemma gdf_frames_lt : forall ph, (gdf_frames ph < ctxph_frames ph)%nat.
Proof. intros [|x]; cbn; lia. Qed.
(* [comment removed for export] *)
Definition ctxph_sh0 {HCEIL : HeapCeil} (ph : ctxphase) (m : mem) (lo : Z) (sp : word) : Prop :=
  match ph with CtxFresh => stack0 m lo (bv_unsigned sp) | CtxReady _ => True end.
Definition GETGLOBAL_STACK (ph : ctxphase) : Z := FR_ossl_lib_ctx_get_ex_data_global + ctxph_stack ph.
Definition GETANDLOCK_STACK : Z := FR_get_and_lock + CRWLOCK_STACK.
(* [comment removed for export] *)
Definition NEWEX_INNER : Z := Z.max (Z.max GETANDLOCK_STACK CUNLOCK_STACK) (Z.max CFREE_STACK AFS_STACK).
Definition CNEWEX_STACK (ph : ctxphase) : Z := FR_CRYPTO_new_ex_data + FR_ossl_crypto_new_ex_data_ex + 16 + Z.max (GETGLOBAL_STACK ph) NEWEX_INNER.
Definition CNEWEX_READY_STACK : Z := FR_CRYPTO_new_ex_data + FR_ossl_crypto_new_ex_data_ex + 16 + Z.max (FR_ossl_lib_ctx_get_ex_data_global + GETDEFCTX_STACK) NEWEX_INNER.
Definition GETGLOBAL_READY_STACK : Z := FR_ossl_lib_ctx_get_ex_data_global + GETDEFCTX_STACK.
Definition CFREEEX_STACK : Z := FR_CRYPTO_free_ex_data + 16 + Z.max GETGLOBAL_READY_STACK NEWEX_INNER.
Definition CRYPTO_EX_INDEX_BIO : Z := 12.
Definition A_defctx_global : Z := A_defctx + 8.      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition PF_ctxinit : list (Z * list Z) := [].
Definition PF_ctx (ph : ctxphase) : list (Z * list Z) := match ph with CtxFresh => PF_ctxinit | CtxReady _ => [] end.
(* [comment removed for export] *)
Definition APC0_MEMALIGN : Z := 0x1c4c70.   (* [comment removed for export] *)
Definition PFC_CTXINIT : list (Z * list Z) := [
    (APC0_MALLOC, [0x1f5850; 0x1f45d0; 0x20e178; 0x1fb974; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x1fa404; 0x218e68; 0x216ed0; 0x216d18; 0x1fba74; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x1fa67c; 0x218e68; 0x216ed0; 0x216d18; 0x1fba74; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x1fa8b8; 0x1fb8fc; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x1fa8b8; 0x201408; 0x1fb91c; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x1fa8b8; 0x203248; 0x1fb928; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x1fa8b8; 0x203248; 0x1fb998; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x1fa8b8; 0x203248; 0x1fb9e4; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x1fa8b8; 0x203248; 0x1fba08; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x1fa8b8; 0x203268; 0x1fb928; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x1fa8b8; 0x203268; 0x1fb998; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x1fa8b8; 0x203268; 0x1fb9e4; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x1fa8b8; 0x203268; 0x1fba08; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x1fa8b8; 0x2032b0; 0x1fb928; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x1fa8b8; 0x2032b0; 0x1fb998; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x1fa8b8; 0x2032b0; 0x1fb9e4; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x1fa8b8; 0x2032b0; 0x1fba08; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x1fa8b8; 0x20a8f0; 0x1fba50; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x1fa8b8; 0x20d0a0; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x1fa8b8; 0x20d0b4; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x1fa8b8; 0x20e198; 0x1fb974; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x1fa8b8; 0x216eac; 0x216d18; 0x1fba74; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x1fa8b8; 0x218ce0; 0x216ed0; 0x216d18; 0x1fba74; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x1fa8b8; 0x260a60; 0x1fba2c; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x1fa8b8; 0x260ad4; 0x1fba2c; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x1fa8b8; 0x359908; 0x1fb950; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x1fa8b8; 0x3fd11c; 0x1fb9c0; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x1fa8b8; 0x4113c8; 0x1fbb10; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x1fbac0; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x1fbae8; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x1fbb38; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x1fbb60; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x1fbbac; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x1fdd30; 0x20a9ac; 0x1fba50; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x1fdd30; 0x20a9ec; 0x1fba50; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x1fdd30; 0x216ef0; 0x216d18; 0x1fba74; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x1fdd30; 0x260a80; 0x1fba2c; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x1fdeec; 0x260a0c; 0x1fba2c; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x1fdeec; 0x519300; 0x1fbbdc; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x1fe058; 0x1fe4bc; 0x20b02c; 0x2095ac; 0x1fbbd0; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x1fe058; 0x1fe4bc; 0x20b02c; 0x2095d8; 0x1fbbd0; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x2031e0; 0x1fb928; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x2031e0; 0x1fb998; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x2031e0; 0x1fb9e4; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x2031e0; 0x1fba08; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x203218; 0x1fb928; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x203218; 0x1fb998; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x203218; 0x1fb9e4; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x203218; 0x1fba08; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x20322c; 0x1fb928; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x20322c; 0x1fb998; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x20322c; 0x1fb9e4; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x20322c; 0x1fba08; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x20a8e4; 0x1fba50; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x20b490; 0x20a91c; 0x1fba50; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x20b490; 0x20a96c; 0x1fba50; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x20b490; 0x3fd14c; 0x1fb9c0; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x20b490; 0x518720; 0x1fba9c; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x20b4b0; 0x20a91c; 0x1fba50; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x20b4b0; 0x20a96c; 0x1fba50; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x20b4b0; 0x3fd14c; 0x1fb9c0; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x20b4b0; 0x518720; 0x1fba9c; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x20e14c; 0x1fb974; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x216ea0; 0x216d18; 0x1fba74; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x218c80; 0x216ed0; 0x216d18; 0x1fba74; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x218dbc; 0x216ed0; 0x216d18; 0x1fba74; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x2609f8; 0x1fba2c; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x3598f8; 0x1fb950; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x4113b8; 0x1fbb10; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x41c4b8; 0x1fbb88; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x41cc40; 0x41c4c4; 0x1fbb88; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x1f58c4; 0x41ce0c; 0x41c4e4; 0x1fbb88; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x20aea8; 0x2095ac; 0x1fbbd0; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x20aea8; 0x2095d8; 0x1fbbd0; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x20aea8; 0x2095f0; 0x1fbbd0; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x20bc78; 0x20b044; 0x2095ac; 0x1fbbd0; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x20bc78; 0x20b044; 0x2095d8; 0x1fbbd0; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x20bc78; 0x20b044; 0x2095f0; 0x1fbbd0; 0x1fc024; 0x533f94]);
    (APC0_MALLOC, [0x1f5850; 0x3fd10c; 0x1fb9c0; 0x1fc024; 0x533f94]);
    (APC0_REALLOC, [0x1f5c74; 0x1fe180; 0x1fe4bc; 0x20b02c; 0x2095ac; 0x1fbbd0; 0x1fc024; 0x533f94]);
    (APC0_MEMALIGN, [0x1f5ab0; 0x219100; 0x218dec; 0x216ed0; 0x216d18; 0x1fba74; 0x1fc024; 0x533f94]) ].

Section W.
  Variable H : asr.

  (* [comment removed for export] *)
  Definition CTXINIT_COST : Z := as_Cm H CTXINIT_BYTES + as_Cf H CTXINIT_BYTES.
  Definition ctxph_cost (ph : ctxphase) : Z := match ph with CtxFresh => CTXINIT_COST | CtxReady _ => 0 end.
  (* [comment removed for export] *)
  Definition ctxph_closed_ok (ph : ctxphase) : Prop :=
    match ph with CtxFresh => Forall (fun r : Z * list Z => trace_ok (as_TR H) (fst r) (snd r)) PFC_CTXINIT | CtxReady _ => True end.

  (* [comment removed for export] *)
  Definition ainblk (LB : list block) (A n : Z) : Prop := exists b, In b LB /\ blk_addr b <= A /\ A + n <= blk_addr b + blk_size b.

  (* [comment removed for export] *)
  Definition c3_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (rv : Z) (W : list (Z * Z)) (X : mem -> Prop) (lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ a0 = Z_to_bv 64 rv
      /\ munch ((lo, bv_unsigned sp) :: W) m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ ACONST m' /\ stk asegs m' lo (bv_unsigned sp) /\ X m'.

  (* [comment removed for export] *)
  Definition c3_frame (sp tp : word) (s' : as_St H) (LB' : list block) (lo B : Z) (errv' : word) (m' : mem) (c : config) : Prop :=
       as_AKREL H s' c /\ mem_inv asegs m' /\ ACONST m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B /\ as_RHEAP H s' LB' m'
    /\ MEMFLAG m' 1 /\ IMPL_mem m' /\ GOT_mem m' /\ arelro_lib m'.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition getdefctx_ready_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (x : ctxinfo) (lo : Z),
      tp = Z_to_bv 64 ATP -> CTX_statics m x -> ACONST m ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - GETDEFCTX_STACK -> mem_inv asegs m ->
      bv_unsigned ra mod 2 = 0 ->
      evt asegs (c3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A_defctx [] (fun m' => CTX_statics m' x) lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_get_default_context) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Definition getdefctx_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (LF : list fframe) (ph : ctxphase) (rv lo B : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun k => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H) (LBN : list block) (x : ctxinfo) (XS : list (Z * Z)),
      as_VIS H s' (cfg_ms k) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ as_MPRES H mo (cfg_model k) /\ c3_frame sp tp s' (LBN ++ LB) lo B errv' m' k
      /\ ctxph_delta ph LBN x /\ Forall (fun b => addressable m' (blk_addr b) (blk_size b)) LBN
      /\ CTXPH (LBN ++ LB) m' (CtxReady x) /\ (ph = CtxFresh -> CTX_keys m')
      /\ Forall (fs_scratch H LF) XS /\ as_RFS H LF m'
      /\ xpres H LB (bv_unsigned sp) (ctxph_foot ph ++ XS) m m'
      /\ as_AL H s' >= as_AL H s - ctxph_cost ph.
  (* [comment removed for export] *)
  Definition getdefctx_stmt_for (entry rv : Z) (stack : ctxphase -> Z) (ph : ctxphase) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model) (s : as_St H) (LB : list block) (LF : list fframe)
           (lo B : Z) (errv : word) (CH : list (Z * Z)),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 entry) fc None m (seg_rom asegs) ->
      a0 = Z_to_bv 64 0 ->
      as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
      lb_bytes LB + ctxph_bytes ph <= as_LIVE_MAX H -> Z.of_nat (length LB) + ctxph_cnt ph <= as_LIVE_CNT_MAX H ->
      as_rauxv_ok H m B -> bv_unsigned sp <= B -> bv_unsigned sp mod 16 = 0 ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - stack ph -> ctxph_sh0 ph m lo sp ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP -> ACONST m ->
      MEMFLAG m 1 -> IMPL_mem m -> GOT_mem m -> arelro_lib m -> CTXPH LB m ph ->
      (* [comment removed for export] *)
      as_RFS H LF m -> (length LF + gdf_frames ph <= AFS_MAXLIVE)%nat ->
      as_chain H m (bv_unsigned s0) CH -> (forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp') ->
      pf_ok (as_TR H) (PF_ctx ph) (bv_unsigned ra) CH -> ctxph_closed_ok ph -> ctxph_cost ph <= as_AL H s ->
      bv_unsigned ra mod 2 = 0 ->
      as_SR H (getdefctx_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF ph rv lo B m mo) (mkCfg msF mo).
  Definition getdefctx_stmt_at (entry rv : Z) (stack : ctxphase -> Z) : Prop := forall ph, getdefctx_stmt_for entry rv stack ph.
  Definition getdefctx_fresh_stmt : Prop := getdefctx_stmt_for P_get_default_context A_defctx ctxph_stack CtxFresh.
  (* [comment removed for export] *)
  Definition getdefctx_stmt : Prop := getdefctx_stmt_at P_get_default_context A_defctx ctxph_stack.
  Definition getglobal_stmt : Prop := getdefctx_stmt_at P_ossl_lib_ctx_get_ex_data_global A_defctx_global GETGLOBAL_STACK.
  Definition getglobal_ready_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (x : ctxinfo) (lo : Z),
      a0 = Z_to_bv 64 0 -> tp = Z_to_bv 64 ATP -> CTX_statics m x -> ACONST m ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - GETGLOBAL_READY_STACK -> mem_inv asegs m ->
      bv_unsigned ra mod 2 = 0 ->
      evt asegs (c3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A_defctx_global [] (fun m' => CTX_statics m' x) lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_ossl_lib_ctx_get_ex_data_global) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition getandlock_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list block) (x : ctxinfo) (rd lo : Z),
      let b := cx_exlock x in
      a0 = Z_to_bv 64 A_defctx_global -> a1 = Z_to_bv 64 CRYPTO_EX_INDEX_BIO -> a2 = Z_to_bv 64 rd -> 0 <= rd < 2 ->
      CTX_statics m x -> EXLOCK LB m b -> aapp (blk_addr b) MUTEX_SIZE -> ACONST m ->     (* [comment removed for export] *)
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - GETANDLOCK_STACK -> mem_inv asegs m ->
      bv_unsigned ra mod 2 = 0 ->
      evt asegs (c3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A_defctx_exmeth_bio (mutex_foot (blk_addr b))
                   (fun m' => CTX_statics m' x /\ MUTEX m' (blk_addr b) MUTEX_HELD) lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_get_and_lock) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition exdata_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (rv : word -> Prop) (s : as_St H) (LB : list block) (LF : list fframe) (x : ctxinfo) (ad lo B : Z) (errv : word) (m : mem) (mo : Model) : config -> Prop :=
    fun k => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (s' : as_St H) (XS : list (Z * Z)),
      as_VIS H s' (cfg_ms k) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ rv a0 /\ as_MPRES H mo (cfg_model k) /\ c3_frame sp tp s' LB lo B errv m' k
      /\ CTX_statics m' x /\ EXLOCK LB m' (cx_exlock x) /\ rw_cells asegs m' ad [C8 (wz 0); C8 (wz 0)]
      /\ Forall (fs_scratch H LF) XS /\ as_RFS H LF m'
      /\ xpres H LB (bv_unsigned sp) ((ad, ad + 16) :: mutex_foot (blk_addr (cx_exlock x)) ++ XS) m m'
      /\ as_AL H s' >= as_AL H s - as_Cf H 0.
  Definition exdata_stmt_at (entry stack : Z) (rv : word -> Prop) (c0ok : Z -> Z -> Prop) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model) (s : as_St H) (LB : list block) (LF : list fframe)
           (x : ctxinfo) (obj ad c0 k0 lo B : Z) (errv : word) (CH : list (Z * Z)),
      let b := cx_exlock x in
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 entry) fc None m (seg_rom asegs) ->
      a0 = Z_to_bv 64 CRYPTO_EX_INDEX_BIO -> a1 = Z_to_bv 64 obj -> a2 = Z_to_bv 64 ad -> c0ok c0 k0 ->
      rw_cells asegs m ad [C8 (wz c0); C8 (wz k0)] -> ad + 16 <= lo -> ad mod 8 = 0 ->
      accessible m ad 16 -> ainblk LB ad 16 ->                                              (* [comment removed for export] *)
      CTX_statics m x -> EXLOCK LB m b -> (ad + 16 <= blk_addr b \/ blk_addr b + MUTEX_SIZE <= ad) ->
      as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->                                   (* [comment removed for export] *)
      as_rauxv_ok H m B -> bv_unsigned sp <= B -> bv_unsigned sp mod 16 = 0 ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - stack ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP -> ACONST m ->
      MEMFLAG m 1 -> IMPL_mem m -> GOT_mem m -> arelro_lib m ->
      as_RFS H LF m -> (length LF < AFS_MAXLIVE)%nat ->                                       (* [comment removed for export] *)
      as_chain H m (bv_unsigned s0) CH -> (forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp') -> as_Cf H 0 <= as_AL H s ->   (* [comment removed for export] *)
      bv_unsigned ra mod 2 = 0 ->
      as_SR H (exdata_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc rv s LB LF x ad lo B errv m mo) (mkCfg msF mo).
  Definition cnewex_ready_stmt : Prop := exdata_stmt_at P_CRYPTO_new_ex_data CNEWEX_READY_STACK (fun a0 => a0 = Z_to_bv 64 1) (fun _ _ => True).

  (* [comment removed for export] *)
  Definition cnewex_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (LF : list fframe) (ph : ctxphase) (ad lo B : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun k => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H) (LBN : list block) (x : ctxinfo) (XS : list (Z * Z)),
      as_VIS H s' (cfg_ms k) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ as_MPRES H mo (cfg_model k) /\ c3_frame sp tp s' (LBN ++ LB) lo B errv' m' k
      /\ ctxph_delta ph LBN x /\ Forall (fun b => addressable m' (blk_addr b) (blk_size b)) LBN
      /\ CTXPH (LBN ++ LB) m' (CtxReady x) /\ (ph = CtxFresh -> CTX_keys m')
      /\ rw_cells asegs m' ad [C8 (wz 0); C8 (wz 0)]
      /\ Forall (fs_scratch H LF) XS /\ as_RFS H LF m'
      /\ xpres H LB (bv_unsigned sp) ((ad, ad + 16) :: ctxph_foot ph ++ XS) m m'
      /\ as_AL H s' >= as_AL H s - (ctxph_cost ph + as_Cf H 0).
  Definition cnewex_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model) (s : as_St H) (LB : list block) (LF : list fframe) (ph : ctxphase)
           (obj ad c0 k0 lo B : Z) (errv : word) (CH : list (Z * Z)),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 P_CRYPTO_new_ex_data) fc None m (seg_rom asegs) ->
      a0 = Z_to_bv 64 CRYPTO_EX_INDEX_BIO -> a1 = Z_to_bv 64 obj -> a2 = Z_to_bv 64 ad ->
      rw_cells asegs m ad [C8 (wz c0); C8 (wz k0)] -> xclient_range H LB (bv_unsigned sp) CTX_X ad 16 -> ad mod 8 = 0 -> ad + 16 <= B ->
      accessible m ad 16 -> ainblk LB ad 16 ->                                              (* [comment removed for export] *)
      (forall x, ph = CtxReady x -> ad + 16 <= blk_addr (cx_exlock x) \/ blk_addr (cx_exlock x) + MUTEX_SIZE <= ad) ->
      as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
      lb_bytes LB + ctxph_bytes ph <= as_LIVE_MAX H -> Z.of_nat (length LB) + ctxph_cnt ph <= as_LIVE_CNT_MAX H ->
      as_rauxv_ok H m B -> bv_unsigned sp <= B -> bv_unsigned sp mod 16 = 0 ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - CNEWEX_STACK ph -> ctxph_sh0 ph m lo sp ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP -> ACONST m ->
      MEMFLAG m 1 -> IMPL_mem m -> GOT_mem m -> arelro_lib m -> CTXPH LB m ph ->
      (* [comment removed for export] *)
      as_RFS H LF m -> (length LF + ctxph_frames ph <= AFS_MAXLIVE)%nat ->
      as_chain H m (bv_unsigned s0) CH -> (forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp') ->
      pf_ok (as_TR H) (PF_ctx ph) (bv_unsigned ra) CH -> ctxph_closed_ok ph -> ctxph_cost ph + as_Cf H 0 <= as_AL H s ->
      bv_unsigned ra mod 2 = 0 ->
      as_SR H (cnewex_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF ph ad lo B m mo) (mkCfg msF mo).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition cfreeex_stmt : Prop := exdata_stmt_at P_CRYPTO_free_ex_data CFREEEX_STACK (fun _ => True) (fun c0 k0 => c0 = 0 /\ k0 = 0).   (* [comment removed for export] *)

  Definition C3_stmts : Prop :=
    getdefctx_ready_stmt /\ getdefctx_stmt /\ getglobal_ready_stmt /\ getglobal_stmt /\ getandlock_stmt
    /\ cnewex_ready_stmt /\ cnewex_stmt /\ cfreeex_stmt.
End W.
End HCW.
