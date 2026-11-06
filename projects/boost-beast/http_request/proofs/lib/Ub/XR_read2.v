(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib Require Ref0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX Exec.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ref Require Import XE_kit.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ub Require Import USegs RMalloc_iface_stmt HeapSR_iface CXXRep CXXLib CXXHeap XRep XE_assign XE_idioms XPRep XPRep2 XFuzz_stmt XP_srkit XF_rep XF_insert4 XP_ftab_rep XP_field XM_rep XM_rep2 XP_req_stmt XP_isl3 XF_lookup XP_wrap XP_body XUbsan XP_pst XP_dtor XP_dtor2 XP_ipf XP_ipf3 XP_put XP_put3
     XA_leaves XL_mutex XB_flat XB_flat2 XB_flat3 XS_readsome XS_ctor XR_stmt XR_read XR_readB.
From OSSVerify.Proofs.boost_beast.http_request.lib.RB Require Import RBMem RBShape DList.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prelim Prog.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac cbn_ps := cbn [ps_c ps_S ps_L ps_ns ps_ls ps_em ps_h ps_u ps_es ps_insz ps_g ps_rdi ps_LBn ps_st ps_errv].
Local Ltac cbn_ps_all := cbn [ps_c ps_S ps_L ps_ns ps_ls ps_em ps_h ps_u ps_es ps_insz ps_g ps_rdi ps_LBn ps_st ps_errv] in *.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition CAPMAX (N : Z) : Z := 2 * N + 65536.

(* [comment removed for export] *)
Record rsw := mkW { w_d : pst ; w_PB : list block ; w_FBB : list block ; w_FB : fbv ; w_fds : list byte ;
                    w_Fs : fbv ; w_sds : list byte ; w_nr : Z }.

(* [comment removed for export] *)
Record rsc := mkC { c_P : Z ; c_N : Z ; c_lo : Z ; c_B : Z ; c_stb : Z ; c_implb : Z ; c_A : Z ; c_LBin : list block ;
                    c_pad7 : list byte ; c_pad2 : list byte ; c_j13 : list byte ; c_j32a : list byte ; c_j8a : list byte ;
                    c_j32b : list byte ; c_j8b : list byte ; c_mb : byte ; c_m0 : mem ; c_mo0 : Model ;
                    c_gp : word ; c_tp : word ; c_s8 : word ; c_s9 : word ; c_s10 : word ; c_s11 : word ; c_F : bvmap 5 word ; c_fc : bv 32 }.

Ltac cbn_w := cbn [w_d w_PB w_FBB w_FB w_fds w_Fs w_sds w_nr c_P c_N c_lo c_B c_stb c_implb c_A c_LBin c_pad7 c_pad2 c_j13 c_j32a c_j8a c_j32b c_j8b c_mb c_m0 c_mo0 c_gp c_tp c_s8 c_s9 c_s10 c_s11 c_F c_fc
                   ps_c ps_S ps_L ps_ns ps_ls ps_em ps_h ps_u ps_es ps_insz ps_g ps_rdi ps_LBn ps_st ps_errv].
Ltac cbn_w_all := cbn [w_d w_PB w_FBB w_FB w_fds w_Fs w_sds w_nr c_P c_N c_lo c_B c_stb c_implb c_A c_LBin c_pad7 c_pad2 c_j13 c_j32a c_j8a c_j32b c_j8b c_mb c_m0 c_mo0 c_gp c_tp c_s8 c_s9 c_s10 c_s11 c_F c_fc
                   ps_c ps_S ps_L ps_ns ps_ls ps_em ps_h ps_u ps_es ps_insz ps_g ps_rdi ps_LBn ps_st ps_errv] in *.

Definition fbb_ok (FB : fbv) (FBB : list block) : Prop :=
  (FB = FB_empty /\ FBB = []) \/ (FB <> FB_empty /\ exists pf, FBB = [(pf, fb_begin FB, fb_cap FB)]).

(* [comment removed for export] *)
Definition wM (N : Z) (w : rsw) : Z := zlength (w_sds w) * (N + 1) + zlength (w_fds w).

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
Definition PutUw (P : Z) (mb : byte) (d : pst) (m : mem) : Prop :=
  FieldsC m (P + 80) (ps_S d) (ps_L d) (ps_ns d) (ps_ls d) (ps_em d)
  /\ rw_cells usegs m (P + O_PR_HDR) (HdrCells (ps_h d)) /\ rw_cells usegs m (P + O_PR_USED) [C1 (b8 (ps_u d))]
  /\ MBuf m (P + 168) (ps_es d) (ps_insz d) /\ rw_cells usegs m (P + 232) [C8 (wz (P + 168))]
  /\ rw_cells usegs m (P + 242) [C1 mb] /\ rw_cells usegs m (P + 288) [C8 (wz 0)] /\ rw_cells usegs m (P + 336) [C8 (wz 0)]
  /\ PfTab m /\ FTInit m /\ XStatics m.

Lemma PutU_of : forall P p0 bs mb d m, PutUw P mb d m -> bytes_at usegs m p0 bs -> PutU P p0 bs mb d m.
Proof. intros P p0 bs mb d m (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11) W. exact (conj A1 (conj A2 (conj A3 (conj A4 (conj A5 (conj A6 (conj A7 (conj A8 (conj W (conj A9 (conj A10 A11))))))))))). Qed.
Lemma PutU_split : forall P p0 bs mb d m, PutU P p0 bs mb d m -> PutUw P mb d m /\ bytes_at usegs m p0 bs.
Proof. intros P p0 bs mb d m (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12). exact (conj (conj A1 (conj A2 (conj A3 (conj A4 (conj A5 (conj A6 (conj A7 (conj A8 (conj A10 (conj A11 A12)))))))))) A9). Qed.

(* [comment removed for export] *)
Definition rs_static (C : rsc) : Prop :=
  0 <= c_P C /\ c_P C + 512 <= c_B C /\ c_B C <= 2^64 /\ c_P C mod 16 = 0 /\ hceil <= c_lo C /\ 0xb8000 <= c_lo C /\ c_lo C + SRO_STACK <= c_P C
  /\ 0 <= c_N C <= 2^26
  /\ (exists p7, In (p7, c_stb C, SZ_SPCI_STATE) (c_LBin C)) /\ rblock_range (c_stb C) SZ_SPCI_STATE
  /\ (1 <= c_N C -> exists p9, In (p9, c_A C, c_N C) (c_LBin C))
  /\ c_tp C = Z_to_bv 64 RATP
  /\ bv_unsigned (c_mb C) <= 1.                                             (* [comment removed for export] *)

Section SR.
  Variable H : hsr.
  Hypothesis HH : heap_sr_hyps H.

(* [comment removed for export] *)
Definition RWm (C : rsc) (w : rsw) (E : ecv) (m : mem) : Prop :=
  let P := c_P C in let d := w_d w in let LB := ps_LBn d ++ c_LBin C in
     rw_cells usegs m P (ParserCoreCells (ps_c d) (c_pad7 C) (c_pad2 C))
  /\ PutUw P (c_mb C) d m
  /\ rw_cells usegs m (P + 240) [C1 (ps_rdi d)] /\ rw_cells usegs m (P + 243) [CB 13 (c_j13 C)]
  /\ rw_cells usegs m (P + 256) [CB 32 (c_j32a C)] /\ rw_cells usegs m (P + 296) [CB 8 (c_j8a C)]
  /\ rw_cells usegs m (P + 304) [CB 32 (c_j32b C)] /\ rw_cells usegs m (P + 344) [CB 8 (c_j8b C)]
  /\ HttpCat m (ps_g d) /\ (FieldTabZero m \/ FT m) /\ MiscVt48 m
  /\ FlatBuf LB m (P + 416) (w_FB w) (w_fds w) /\ rw_cells usegs m (P + 464) (ErrCodeCells E)
  /\ rw_cells usegs m (P + 360) (BasicStreamCells (c_stb C))
  /\ StateBlock LB m (c_stb C) (P + 392) (c_implb C) (mkST (mkSPC VP_SPCI_STATE 1 1 1) 0 (w_Fs w) STREAM_EOF (w_nr w) (c_N C - zlength (w_sds w))) (w_sds w)
  /\ hs_RHEAP H (ps_st d) LB m /\ rw_cells usegs m RERRNO [C4 (ps_errv d)] /\ hs_rauxv_ok H m (c_B C) /\ mem_inv usegs m.

(* [comment removed for export] *)
Definition RWp (C : rsc) (w : rsw) : Prop :=
  let P := c_P C in let N := c_N C in let LBin := c_LBin C in
  let d := w_d w in let LB := ps_LBn d ++ LBin in let c := ps_c d in let h := ps_h d in let es := ps_es d in let FB := w_FB w in
     pcore_ok c
  /\ FieldsOwn LB (ps_em d) /\ MBufOwn LB es /\ HdrOwnP LB h /\ elems_heap (ps_em d)
  /\ (forall x s, In (x, s) es -> 0 < x /\ x + 24 + s <= hceil /\ (x + 24 + s <= 0x10000 \/ 0xb8000 <= x))
  /\ (forall e x s, e ∈ ps_L d -> In (x, s) es -> e + 48 <= x \/ x + 24 + s <= e)
  /\ (pc_state c <= 1 -> hdr_empty h /\ ps_u d = 0) /\ 0 <= ps_u d <= 1
  /\ mb_cap es <= 3 * ps_insz d + 512 /\ Z.of_nat (length es) <= KB /\ 0 <= ps_insz d
  /\ (pc_state c = 3 \/ pc_state c = 4 \/ pc_state c = 9 -> 1 <= pc_len c)
  /\ hdr_disj (ps_L d) es h /\ (pc_state c < 10 -> pc_hlim c <= 8192) /\ pc_skip c < 2^62
  /\ lbn_ownedP (ps_L d) h es (w_PB w) /\ Permutation (ps_LBn d) (w_PB w ++ w_FBB w) /\ fbb_ok FB (w_FBB w)
  /\ (forall e, e ∈ ps_L d -> blk_fresh LBin P e 48)
  /\ (forall x s, In (x, s) es -> forall a k, rclient_range LBin P a k -> 0 <= k -> a + k <= x \/ x + 24 + s <= a)
  /\ (hv_tl h <> 0 -> blk_fresh LBin P (hv_tp h) (hv_tl h)) /\ (hv_ml h <> 0 -> blk_fresh LBin P (hv_mp h) (hv_ml h))
  /\ (FB <> FB_empty -> blk_fresh LBin P (fb_begin FB) (fb_cap FB))
  /\ (FB <> FB_empty -> forall e, e ∈ ps_L d -> e + 48 <= fb_begin FB \/ fb_end FB <= e)
  /\ (FB <> FB_empty -> forall x s, In (x, s) es -> x + 24 + s <= fb_begin FB \/ fb_end FB <= x)
  /\ (FB <> FB_empty -> hv_tl h <> 0 -> hv_tp h + hv_tl h <= fb_begin FB \/ fb_end FB <= hv_tp h)
  /\ (FB <> FB_empty -> hv_ml h <> 0 -> hv_mp h + hv_ml h <= fb_begin FB \/ fb_end FB <= hv_mp h)
  /\ ((N = 0 /\ w_Fs w = FB_empty) \/ (1 <= N /\ fb_begin (w_Fs w) = c_A C /\ fb_end (w_Fs w) = c_A C + N /\ (c_A C + N <= c_stb C \/ c_stb C + SZ_SPCI_STATE <= c_A C)))
  /\ zlength (w_fds w) + zlength (w_sds w) <= N /\ 0 <= w_nr w /\ fb_cap FB <= CAPMAX N
  /\ lb_bytes LB + 17 * pc_hlim c + body_res es (ps_insz d) (zlength (w_fds w) + zlength (w_sds w))
       + (if pc_state c <=? 9 then 34 else 0) + (2 * CAPMAX N - lb_bytes (w_FBB w)) <= hs_LIVE_MAX H
  /\ 4 * Z.of_nat (length LB) + pc_hlim c + 4 * (KB - Z.of_nat (length es))
       + (if pc_state c <=? 1 then 8 else 0) + (if pc_state c <=? 9 then 2 else 0) + 4 * (2 - Z.of_nat (length (w_FBB w))) <= 4 * hs_LIVE_CNT_MAX H
  /\ ps_insz d + (zlength (w_fds w) + zlength (w_sds w)) <= 2^28.

(* [comment removed for export] *)
Definition rs_frames (m : mem) (sp : word) (j8 : list byte) (t1c t2c : list cell) (s7v s6v s5v s4v s3v s2v s1v s0v ra : word) (fr0 : list word) : Prop :=
  rs_frame m sp j8 t1c t2c /\ rw_cells usegs m (bv_unsigned sp + -72) (map C8 (rs_sv s7v s6v s5v s4v s3v s2v s1v s0v ra))
  /\ rw_cells usegs m (bv_unsigned sp) (map C8 fr0) /\ length fr0 = 8%nat.

(* [comment removed for export] *)
Definition rs_core (C : rsc) (sp : word) (s7v s6v s5v s4v s3v s2v s1v s0v ra : word) (fr0 : list word) (w : rsw) (E : ecv) (tot : Z) (m : mem)
    (j8 : list byte) (t1c t2c : list cell) : Prop :=
  RWm C w E m /\ RWp C w /\ stk usegs m (c_lo C) (bv_unsigned sp + -128)
  /\ rs_frames m sp j8 t1c t2c s7v s6v s5v s4v s3v s2v s1v s0v ra fr0
  /\ xpres (c_LBin C) (c_P C) (sro_X (c_P C) (c_stb C)) (c_m0 C) m
  /\ 0 <= tot /\ tot + zlength (w_fds w) + zlength (w_sds w) <= c_N C
  /\ w_nr w <= c_N C - zlength (w_sds w).

(* [comment removed for export] *)
Definition rs_at_put (C : rsc) (sp : word) (s7v s6v s5v s4v s3v s2v s1v s0v ra : word) (fr0 : list word) (M0 : Z) (w : rsw) (cf : config) : Prop :=
  exists (t0 t1 t2 a4 a5 a6 a7 s5x s6x s7x t3 t4 t5 t6 : word) (m : mem) (E : ecv) (tot : Z) (j8 : list byte) (t1c t2c : list cell),
    cfg_ms cf = rs_ms P_BP_PUT (wz RS_PUTRET) sp (c_gp C) (c_tp C) t0 t1 t2 tot (c_P C) (wz (c_P C)) (wz (fb_in (w_FB w))) (wz (fb_size (w_FB w))) (wz (c_P C + O_H_EC))
                      a4 a5 a6 a7 s5x s6x s7x (c_s8 C) (c_s9 C) (c_s10 C) (c_s11 C) t3 t4 t5 t6 (c_F C) (c_fc C) m
    /\ 1 <= fb_size (w_FB w) /\ pc_state (ps_c (w_d w)) <> 11
    /\ hs_KREL H (ps_st (w_d w)) (cfg_model cf) /\ hs_MPRES H (c_mo0 C) (cfg_model cf)
    /\ rs_core C sp s7v s6v s5v s4v s3v s2v s1v s0v ra fr0 w E tot m j8 t1c t2c
    /\ wM (c_N C) w <= M0.

(* [comment removed for export] *)
Definition rs_at_doread (C : rsc) (sp : word) (s7v s6v s5v s4v s3v s2v s1v s0v ra : word) (fr0 : list word) (M0 : Z) (w : rsw) (cf : config) : Prop :=
  exists (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5x s6x s7x t3 t4 t5 t6 : word) (m : mem) (E : ecv) (tot : Z) (j8 : list byte) (t1c t2c : list cell),
    cfg_ms cf = rs_ms RS_DOREAD rax sp (c_gp C) (c_tp C) t0 t1 t2 tot (c_P C) a0 a1 a2 a3 a4 a5 a6 a7 s5x s6x s7x (c_s8 C) (c_s9 C) (c_s10 C) (c_s11 C) t3 t4 t5 t6 (c_F C) (c_fc C) m
    /\ pc_state (ps_c (w_d w)) <> 11
    /\ hs_KREL H (ps_st (w_d w)) (cfg_model cf) /\ hs_MPRES H (c_mo0 C) (cfg_model cf)
    /\ rs_core C sp s7v s6v s5v s4v s3v s2v s1v s0v ra fr0 w E tot m j8 t1c t2c
    /\ wM (c_N C) w <= M0.

(* [comment removed for export] *)
Definition rs_done (C : rsc) (sp : word) (s7v s6v s5v s4v s3v s2v s1v s0v ra : word) (fr0 : list word) (M0 : Z) (cf : config) : Prop :=
  exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) (w : rsw) (E : ecv) (tot : Z),
    cfg_ms cf = MS (mkR ra sp (c_gp C) (c_tp C) t0 t1 t2 s0v s1v (wz tot) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v (c_s8 C) (c_s9 C) (c_s10 C) (c_s11 C) t3 t4 t5 t6)
                   (c_F C) (ret_pc ra) (c_fc C) None m (seg_rom usegs)
    /\ hs_KREL H (ps_st (w_d w)) (cfg_model cf) /\ hs_MPRES H (c_mo0 C) (cfg_model cf)
    /\ RWm C w E m /\ RWp C w /\ stk usegs m (c_lo C) (bv_unsigned sp)
    /\ rw_cells usegs m (bv_unsigned sp) (map C8 fr0)
    /\ xpres (c_LBin C) (c_P C) (sro_X (c_P C) (c_stb C)) (c_m0 C) m
    /\ 0 <= tot /\ tot + zlength (w_fds w) + zlength (w_sds w) <= c_N C
    /\ ec_ok E /\ (E = EC_clear \/ http_fail E)
    /\ wM (c_N C) w <= M0
    /\ (E = EC_clear -> pc_state (ps_c (w_d w)) <> 11 -> wM (c_N C) w < M0 /\ w_nr w <= c_N C - zlength (w_sds w)).


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pst_call (d : pst) : pst :=
  mkPST (ps_c d) (ps_S d) (ps_L d) (ps_ns d) (ps_ls d) (ps_em d) (ps_h d) (ps_u d) (ps_es d) (ps_insz d) (ps_g d) (ps_rdi d) [] (ps_st d) (ps_errv d).
Definition pst_ret (d'' : pst) (LBn : list block) (g : bool) : pst :=
  mkPST (ps_c d'') (ps_S d'') (ps_L d'') (ps_ns d'') (ps_ls d'') (ps_em d'') (ps_h d'') (ps_u d'') (ps_es d'') (ps_insz d'') g (ps_rdi d'')
        (ps_LBn d'' ++ LBn) (ps_st d'') (ps_errv d'').

(* [comment removed for export] *)
Definition put_MX (C : rsc) (w : rsw) : Z := hs_LIVE_MAX H - (2 * CAPMAX (c_N C) - lb_bytes (w_FBB w)).
Definition put_CX (C : rsc) (w : rsw) : Z := hs_LIVE_CNT_MAX H - (2 - Z.of_nat (length (w_FBB w))).

(* [comment removed for export] *)
Definition w_after_put (w : rsw) (d'' : pst) (g : bool) (k : Z) : rsw :=
  mkW (pst_ret d'' (ps_LBn (w_d w)) g) (ps_LBn d'' ++ w_PB w) (w_FBB w) (fb_consume (w_FB w) k) (skipn (Z.to_nat k) (w_fds w)) (w_Fs w) (w_sds w) (w_nr w).

Lemma blk_fresh_weaken : forall LB LB' SP SP' A n,
  blk_fresh LB SP A n -> SP <= SP' -> (forall b, In b LB' -> In b LB) -> blk_fresh LB' SP' A n.
Proof.
  intros LB LB' SP SP' A n F HS HL a k RR Hk. apply F; [| exact Hk].
  eapply rclient_range_weaken; [exact RR | exact HS | exact HL].
Qed.

Lemma fbb_ok_facts : forall FB FBB, fbb_ok FB FBB ->
  lb_bytes FBB = fb_cap FB /\ 0 <= Z.of_nat (length FBB) <= 1
  /\ (FB <> FB_empty -> forall LB, (forall b, In b FBB -> In b LB) -> exists pf, In (pf, fb_begin FB, fb_cap FB) LB).
Proof.
  intros FB FBB [[-> ->] | (NE & pf & ->)]; cbn.
  - split; [reflexivity|]. split; [lia|]. intros K; exfalso; exact (K eq_refl).
  - unfold lb_bytes, blk_size. cbn [fold_right snd]. split; [lia|]. split; [change (Z.of_nat 1) with 1; lia|]. intros _ LB HL. exists pf. apply HL. left; reflexivity.
Qed.

Lemma fb_consume_shape : forall FB k, fb_begin (fb_consume FB k) = fb_begin FB /\ fb_end (fb_consume FB k) = fb_end FB
  /\ fb_cap (fb_consume FB k) = fb_cap FB /\ fb_last (fb_consume FB k) = fb_last FB.
Proof. intros FB k. unfold fb_consume, fb_cap. destruct (k <? fb_size FB); cbn; repeat split; reflexivity. Qed.

Lemma fbv_eq_dec : forall a b : fbv, {a = b} + {a <> b}.
Proof. intros a b. decide equality; apply Z.eq_dec. Qed.

Lemma fb_consume_empty : forall FB k, 0 <= k -> (FB <> FB_empty -> 0 < fb_begin FB) -> (fb_consume FB k = FB_empty <-> FB = FB_empty).
Proof.
  intros FB k K0 POS. split.
  - intros E. destruct (fbv_eq_dec FB FB_empty) as [EQ | NE]; [exact EQ|]. exfalso.
    pose proof (POS NE). pose proof (fb_consume_shape FB k) as (B & _). rewrite E in B. cbn in B. lia.
  - intros ->. unfold fb_consume, fb_size, FB_empty. cbn. replace (k <? 0 - 0) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Lemma fbb_ok_consume : forall FB FBB k, 0 <= k -> (FB <> FB_empty -> 0 < fb_begin FB) -> fbb_ok FB FBB -> fbb_ok (fb_consume FB k) FBB.
Proof.
  intros FB FBB k K0 POS OK. pose proof (fb_consume_shape FB k) as (B & E & CP & _).
  destruct OK as [[-> ->] | (NE & pf & ->)].
  - left. split; [| reflexivity]. apply (proj2 (fb_consume_empty FB_empty k K0 ltac:(intros K; exfalso; exact (K eq_refl)))). reflexivity.
  - right. split; [intros K; apply NE; exact (proj1 (fb_consume_empty FB k K0 POS) K)|]. exists pf. rewrite B, CP. reflexivity.
Qed.

Lemma zlength_skipn : forall {A} (k : nat) (l : list A), (k <= length l)%nat -> zlength (skipn k l) = zlength l - Z.of_nat k.
Proof. intros A k l Hk. unfold zlength. rewrite length_skipn. lia. Qed.

(* [comment removed for export] *)
Lemma RWp_put_pre : forall C w (spw : word),
  rs_static C -> RWp C w ->
  w_FB w <> FB_empty -> fb_begin (w_FB w) <= fb_in (w_FB w) -> fb_out (w_FB w) <= fb_end (w_FB w) -> zlength (w_fds w) = fb_size (w_FB w) ->
  bv_unsigned spw <= c_P C ->
  let d := w_d w in let LB0 := ps_LBn d ++ c_LBin C in
  PutL spw (c_P C) (fb_in (w_FB w)) (w_fds w) LB0 (ps_L d) (ps_es d) (ps_h d) (pst_call d)
  /\ PutB LB0 (fb_in (w_FB w)) (zlength (w_fds w) + zlength (w_sds w)) (put_MX C w) (put_CX C w) (pst_call d) (fb_in (w_FB w))
  /\ put_MX C w <= hs_LIVE_MAX H /\ put_CX C w <= hs_LIVE_CNT_MAX H.
Proof.
  intros C w spw STC RP NE BI OE SZ SPW. cbv zeta.
  destruct C as [P N lo B stb implb A LBin pad7 pad2 j13 j32a j8a j32b j8b mb m0 mo0 gp tp s8w s9w s10 s11 F fc].
  destruct w as [d PB FBB FB fds Fs sds nr]. destruct d as [c S L ns ls em h u es insz g rdi LBn st errv]. unfold pst_call, RWp, rs_static in *. cbn_w_all.
  destruct STC as (P0 & PB0 & BHI & AL16 & CEIL & IMG & LO & NR26 & INS & RBS & INA & TP & MB1).
  destruct RP as (PCOK & OWN & MOWN & HOWN & EH & ESH & DFB & HST & U01 & CAP & LES & INZ & LEN1 & HDJ & HL8 & SK62
                  & AOWN & PERM & FOK & FRL & FRB & FRT & FRM & FRF & DJL & DJB & DJT & DJM & STRM & SZS & NR & CPM & BY & CN & IZ).
  destruct (fbb_ok_facts _ _ FOK) as (FBBb & FBBn & FBBin). unfold fb_size, fb_cap in *.
  unfold CAPMAX in *. pose proof SZ as SZ'. unfold zlength in SZ'.
  split; [| split; [| unfold put_MX, put_CX, CAPMAX; cbn_w; split; lia]].
  - unfold PutL. cbn_ps. cbn [app].
    split; [exact PCOK|]. split; [exact OWN|]. split; [exact MOWN|]. split; [exact HOWN|]. split; [exact EH|]. split; [exact ESH|].
    split; [intros e He; left; exact He|]. split; [intros x s IN; left; exact IN|].
    split. { intros e He. destruct (DJL NE e He); lia. }
    split. { intros x s IN. destruct (DJB NE x s IN); lia. }
    split; [exact DFB|]. split; [exact HST|]. split; [exact U01|]. split; [exact CAP|]. split; [exact LES|]. split; [exact INZ|].
    split; [exact LEN1|]. split; [exact HDJ|]. split; [left; reflexivity|]. split; [exact HL8|]. split; [exact SK62|].
    split; [intros b []|]. split; [intros e He; exact He | intros x s IN; exact IN].
  - unfold PutB, put_MX, put_CX, CAPMAX in *. cbn_w. cbn [app length]. rewrite Z.sub_diag, Z.sub_0_r.
    split; [| split; [| exact IZ]].
    + clear - BY FBBb FBBn CPM. lia.
    + clear - CN FBBn. lia.
Qed.

(* [comment removed for export] *)
Lemma RWp_put_post : forall C w (spw : word) (d'' : pst) (q : Z) (g : bool),
  rs_static C -> RWp C w ->
  (w_FB w <> FB_empty -> 0 < fb_begin (w_FB w)) -> fb_begin (w_FB w) <= fb_in (w_FB w) -> fb_out (w_FB w) <= fb_end (w_FB w) ->
  zlength (w_fds w) = fb_size (w_FB w) ->
  bv_unsigned spw <= c_P C ->
  let d := w_d w in let LB0 := ps_LBn d ++ c_LBin C in let p0 := fb_in (w_FB w) in
  PutL spw (c_P C) p0 (w_fds w) LB0 (ps_L d) (ps_es d) (ps_h d) d'' ->
  PutB LB0 p0 (zlength (w_fds w) + zlength (w_sds w)) (put_MX C w) (put_CX C w) d'' q ->
  p0 <= q <= p0 + zlength (w_fds w) ->
  RWp C (w_after_put w d'' g (q - p0)).
Proof.
  intros C w spw d'' q g' STC RP POS BI OE SZ SPW. cbv zeta. intros L B QR.
  destruct C as [P N lo B0 stb implb A LBin pad7 pad2 j13 j32a j8a j32b j8b mb m0 mo0 gp tp s8w s9w s10 s11 F fc].
  destruct w as [d PB1 FBB FB fds Fs sds nr]. destruct d as [c S L1 ns ls em h u es insz g rdi LBn st errv].
  destruct d'' as [c2 S2 L2 ns2 ls2 em2 h2 u2 es2 insz2 g2 rdi2 LBn2 st2 errv2]. unfold w_after_put, pst_ret, RWp, rs_static in *. cbn_w_all.
  destruct STC as (P0 & PB & BHI & AL16 & CEIL & IMG & LO & NR26 & INS & RBS & INA & TP & MB1).
  destruct RP as (PCOK & OWN & MOWN & HOWN & EH & ESH & DFB & HST & U01 & CAP & LES & INZ & LEN1 & HDJ & HL8 & SK62
                  & AOWN & PERM & FOK & FRL & FRB & FRT & FRM & FRF & DJL & DJB & DJT & DJM & STRM & SZS & NRK & CPM & BY & CN & IZ).
  destruct L as (PCOK2 & OWN2 & MOWN2 & HOWN2 & EH2 & ESH2 & NEW2 & NEWB2 & WINL2 & WINB2 & DFB2 & HST2 & U012 & CAP2 & LES2 & INZ2 & LEN12 & HDJ2 & HNEW2 & HL82 & SK622 & AOWN2 & LS2 & ESS2).
  destruct B as (B1 & B2 & B3). unfold PutL, PutB in *. cbn_w_all.
  destruct (fbb_ok_facts _ _ FOK) as (FBBb & FBBn & FBBin).
  pose proof (fb_consume_shape FB (q - fb_in FB)) as (CB_ & CE & CCP & CL). unfold fb_size, fb_cap in *.
  assert (ZSK : zlength (skipn (Z.to_nat (q - fb_in FB)) fds) = zlength fds - (q - fb_in FB)).
  { rewrite zlength_skipn; [lia|]. unfold zlength in SZ, QR. lia. }
  assert (SUB : forall b, In b LBin -> In b (LBn ++ LBin)) by (intros b Hb; apply in_or_app; right; exact Hb).
  assert (FW : forall A0 n0, blk_fresh (LBn ++ LBin) (bv_unsigned spw) A0 n0 -> blk_fresh LBin P A0 n0).
  { intros A0 n0 F0. eapply blk_fresh_weaken; [exact F0 | exact SPW | exact SUB]. }
  (* [comment removed for export] *)
  assert (FBLK : FB <> FB_empty -> forall A0 n0, blk_fresh (LBn ++ LBin) (bv_unsigned spw) A0 n0 -> 0 <= n0 -> A0 + n0 <= fb_begin FB \/ fb_end FB <= A0).
  { intros NE A0 n0 F0 Hn.
    destruct (FBBin NE (LBn ++ LBin)) as [pf INf].
    { intros b Hb. apply in_or_app. left. eapply Permutation_in; [apply Permutation_sym; exact PERM|]. apply in_or_app. right. exact Hb. }
    pose proof (fbb_ok_facts FB FBB FOK) as _.
    destruct (F0 (fb_begin FB) (fb_end FB - fb_begin FB) ltac:(right; right; exists (pf, fb_begin FB, fb_end FB - fb_begin FB); split; [exact INf | cbn; lia]) ltac:(lia)); lia. }
  rewrite <- !app_assoc.
  split; [exact PCOK2|]. split; [exact OWN2|]. split; [exact MOWN2|]. split; [exact HOWN2|]. split; [exact EH2|]. split; [exact ESH2|]. split; [exact DFB2|].
  split; [exact HST2|]. split; [exact U012|]. split; [exact CAP2|]. split; [exact LES2|]. split; [exact INZ2|]. split; [exact LEN12|]. split; [exact HDJ2|].
  split; [exact HL82|]. split; [exact SK622|].
  split.
  { (* [comment removed for export] *)
    intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb | Hb]; [exact (AOWN2 b Hb)|].
    destruct (AOWN b Hb) as [[K1 K2] | [K | [K | K]]].
    - left. split; [apply LS2; exact K1 | exact K2].
    - right; left. destruct HNEW2 as [-> | [HE _]]; [exact K|]. exfalso. destruct K as [K _]. destruct HE as (_ & ML & _). lia.
    - right; right; left. destruct HNEW2 as [-> | [HE _]]; [exact K|]. exfalso. destruct K as [K _]. destruct HE as (_ & _ & _ & TL & _). lia.
    - right; right; right. destruct K as [s [IN EQ]]. exists s. split; [apply ESS2; exact IN | exact EQ]. }
  split. { apply Permutation_app_head. exact PERM. }
  split. { apply fbb_ok_consume; [lia | exact POS | exact FOK]. }
  split. { intros e He. destruct (NEW2 e He) as [old | fresh]; [exact (FRL e old) | exact (FW _ _ fresh)]. }
  split. { intros x s IN. destruct (NEWB2 x s IN) as [old | fresh]; [exact (FRB x s old) |].
           intros a k RR Hk. apply fresh; [| exact Hk]. eapply rclient_range_weaken; [exact RR | exact SPW | exact SUB]. }
  split. { intros TL. destruct HNEW2 as [-> | (HE & FT2 & FM2)]; [exact (FRT TL) | exact (FW _ _ (FT2 TL))]. }
  split. { intros ML. destruct HNEW2 as [-> | (HE & FT2 & FM2)]; [exact (FRM ML) | exact (FW _ _ (FM2 ML))]. }
  split. { rewrite CCP, CB_. intros NE. apply FRF. intros K. apply NE. apply (proj2 (fb_consume_empty FB (q - fb_in FB) ltac:(lia) POS)). exact K. }
  assert (NE' : fb_consume FB (q - fb_in FB) <> FB_empty -> FB <> FB_empty).
  { intros NE K. apply NE. apply (proj2 (fb_consume_empty FB (q - fb_in FB) ltac:(lia) POS)). exact K. }
  rewrite CB_, CE.
  split. { intros NE e He. destruct (NEW2 e He) as [old | fresh]; [exact (DJL (NE' NE) e old) | exact (FBLK (NE' NE) _ _ fresh ltac:(lia))]. }
  split. { intros NE x s IN. destruct (NEWB2 x s IN) as [old | fresh]; [exact (DJB (NE' NE) x s old) |].
           destruct (FBBin (NE' NE) (LBn ++ LBin)) as [pf INf].
           { intros b Hb. apply in_or_app. left. eapply Permutation_in; [apply Permutation_sym; exact PERM|]. apply in_or_app. right. exact Hb. }
           destruct (fresh (fb_begin FB) (fb_end FB - fb_begin FB) ltac:(right; right; exists (pf, fb_begin FB, fb_end FB - fb_begin FB); split; [exact INf | cbn; lia]) ltac:(lia)); lia. }
  split. { intros NE TL. destruct HNEW2 as [-> | (HE & FT2 & FM2)]; [exact (DJT (NE' NE) TL) |].
           destruct HOWN2 as (_ & _ & _ & TLR). exact (FBLK (NE' NE) _ _ (FT2 TL) ltac:(lia)). }
  split. { intros NE ML. destruct HNEW2 as [-> | (HE & FT2 & FM2)]; [exact (DJM (NE' NE) ML) |].
           destruct HOWN2 as (_ & _ & MLR & _). exact (FBLK (NE' NE) _ _ (FM2 ML) ltac:(lia)). }
  split; [exact STRM|].
  rewrite ZSK, ?CCP.
  split; [clear - SZS QR; lia|]. split; [exact NRK|]. split; [exact CPM|].
  unfold put_MX, put_CX, CAPMAX in *. cbn_w_all. rewrite <- ?app_assoc in B1, B2.
  set (s34 := if pc_state c2 <=? 9 then 34 else 0) in *. set (s8 := if pc_state c2 <=? 1 then 8 else 0) in *. set (s2 := if pc_state c2 <=? 9 then 2 else 0) in *.
  split; [clear - B1 QR SZ; replace (zlength fds - (q - fb_in FB) + zlength sds) with (zlength fds + zlength sds - (q - fb_in FB)) by lia; lia|].
  split; [clear - B2; lia|].
  clear - B3 QR SZ. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma StateBlock_LB_mono : forall LB LB' m b ioc implb S ds,
  StateBlock LB m b ioc implb S ds -> (forall x, In x LB -> In x LB') -> StateBlock LB' m b ioc implb S ds.
Proof.
  intros LB LB' m b ioc implb S ds (p & j7 & j16 & j4 & IN & RB & CH & OK & EV & CE & CW & PM & FB & REST) HL.
  exists p, j7, j16, j4. split; [apply HL; exact IN|]. split; [exact RB|]. split; [exact CH|]. split; [exact OK|]. split; [exact EV|].
  split; [exact CE|]. split; [exact CW|]. split; [exact PM|]. split; [eapply FlatBuf_LB_mono; [exact FB | exact HL] | exact REST].
Qed.
Scheme kc__1 := Elimination for Corelib.Init.Logic.and Sort Prop.
Scheme kc__2 := Elimination for Corelib.Init.Logic.or Sort Prop.
Scheme kc__3 := Elimination for Corelib.Init.Logic.ex Sort Prop.

(* [comment removed for export] *)
Lemma FlatBuf_consume : forall LB m m' a FB ds k,
  FlatBuf LB m a FB ds -> 0 <= k <= fb_size FB ->
  rw_cells usegs m' a (FlatBufCells (fb_consume FB k)) ->
  (FB <> FB_empty -> exists pre junk,
      rw_cells usegs m' (fb_begin FB) [CB (Z.to_nat (fb_in FB - fb_begin FB)) pre; CB (length ds) ds; CB (Z.to_nat (fb_end FB - fb_out FB)) junk]) ->
  FlatBuf LB m' a (fb_consume FB k) (skipn (Z.to_nat k) ds).
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Init.Datatypes.list); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.RMalloc_iface_stmt.block); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.RMalloc_iface_stmt.mem); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Datatypes.option); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.fbv); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.FlatBuf); constr:(HCEIL); constr:(@kc__1); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Step.rw_cells); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.USegs.usegs); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.FlatBufCells); constr:(@Corelib.Init.Logic.and); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.fb_ok); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Prelim.zlength); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.fb_size); constr:(@Corelib.Init.Logic.not); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.FB_empty); constr:(@Corelib.Init.Logic.ex); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.fb_begin); constr:(@Corelib.Init.Datatypes.cons); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.cell); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.CB); constr:(@Stdlib.ZArith.BinInt.Z.to_nat); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.fb_in); constr:(@Corelib.Init.Datatypes.length); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.fb_end); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.fb_out); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XB_flat.fb_consume); constr:(@Corelib.Lists.ListDef.skipn); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XR_read2.HCW.SR.fb_consume_shape); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.fb_cap); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.fb_last); constr:(@kc__2); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Prog.bptr); constr:(@Stdlib.Lists.List.In); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Init.Datatypes.pair); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.RMalloc_iface_stmt.rblock_range); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Corelib.Init.Logic.or); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@kc__3); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapCeil.hceil); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Corelib.Init.Logic.conj); constr:(@Stdlib.ZArith.BinInt.Z.of_nat); constr:(@Corelib.Init.Logic.or_introl); constr:(@Corelib.Init.Logic.eq_sym); constr:(@Stdlib.ZArith.BinInt.Z.ltb); constr:(@Corelib.Init.Datatypes.false); constr:(@Stdlib.ZArith.BinInt.Z.ltb_ge); constr:(@Stdlib.ZArith.Znat.Nat2Z.is_nonneg); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.micromega.EnvRing.PEsub); constr:(@Corelib.Init.Logic.eq_ind); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ub.XRep.mkFB); constr:(@Corelib.Init.Logic.or_intror); constr:(@Corelib.Init.Logic.ex_intro); constr:(@Stdlib.ZArith.BinInt.Z.ltb_spec); constr:(@Corelib.Init.Datatypes.BoolSpec); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Corelib.Init.Datatypes.nat); constr:(@Corelib.Init.Nat.sub); constr:(@Stdlib.micromega.ZifyClasses.rew_iff_rev); constr:(@Stdlib.ZArith.BinInt.Z.max); constr:(@Stdlib.micromega.ZifyClasses.mkrel); constr:(@Corelib.Init.Logic.iff_refl); constr:(@Stdlib.micromega.ZifyClasses.mkapp); constr:(@Stdlib.micromega.ZifyClasses.mkapp2); constr:(@Stdlib.Arith.PeanoNat.Nat.sub); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_sub_max); constr:(@Stdlib.micromega.ZifyInst.of_nat_to_nat_eq); constr:(@Stdlib.ZArith.BinInt.Z.max_spec); constr:(@Stdlib.micromega.RingMicromega.PsatzMulC); constr:(@Stdlib.micromega.EnvRing.Pc); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Stdlib.micromega.Tauto.OR); constr:(@Stdlib.Lists.List.length_skipn); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.cells_at); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.wr_at); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.cells_size); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.cells_wf); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Mem.bytes_at); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Cells.cells_bytes); constr:(@Corelib.Init.Logic.True); constr:(@Corelib.Init.Datatypes.app); constr:(@Corelib.Lists.ListDef.firstn); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Ref.XE_kit.rw_cells_reshape); constr:(@Corelib.Init.Nat.add); constr:(@Corelib.Init.Nat.min); constr:(@Stdlib.ZArith.BinInt.Z.min); constr:(@Corelib.Init.Logic.iff_sym); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_iff); constr:(@Stdlib.Arith.PeanoNat.Nat.add); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_add); constr:(@Stdlib.Arith.PeanoNat.Nat.min); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_min); constr:(@Stdlib.micromega.ZifyClasses.rew_iff); constr:(@Stdlib.ZArith.BinInt.Z.min_spec); constr:(@Corelib.Init.Logic.I); constr:(@Stdlib.Lists.List.length_firstn); constr:(@Stdlib.Lists.List.length_app); constr:(@Stdlib.Lists.List.firstn_skipn); constr:(@Stdlib.Lists.List.app_assoc); constr:(@Stdlib.Lists.List.skipn_all2); constr:(@Corelib.Init.Peano.le); constr:(@Stdlib.ZArith.Znat.Nat2Z.inj_le); constr:(@kc__3 ((@Corelib.Init.Datatypes.list) ((@stdpp.bitvector.definitions.bv) ((@Corelib.Numbers.BinNums.Npos) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) ((@Corelib.Numbers.BinNums.xO) (@Corelib.Numbers.BinNums.xH)))))))); constr:(@kc__3 (@OSSVerify.Proofs.boost_beast.http_request.lib.Spec.Prog.bptr))|] [|@junk; @pre; @p; @CL; @CCP; @CE; @CB_; @BLK'; @C'; @K; @BLK; @SZ; @C; @FB; @__ff; @__varmap; @__wit; @__arith; @H0; @__x1; @__x2; @__x3; @__x4; @__x5; @_H; @R1; @S2; @S1; @CP; @R; @IN; @x; @SH; @y; @__p1; @cstr; @b; @z; @__x6; @__p2; @__p3; @__p4; @b0; @n; @m; @z2; @H2; @z1; @H1; @__x7; @E; @__x8; @__x9; @__x10; @__p5; @z8; @H8; @z7; @H7; @z6; @H6; @z5; @H5; @z4; @H4; @cstr1; @cstr0; @L0; @l; @__x11; @L3; @L2; @L1; @WR; @BA; @WF; @B; @e; @NE0; @NE; @OK; @k; @ds; @a; @m'; @LB|] "#Pp#y%[$($Y$Z$X$D##$:#$%/$_$.$S#)#y#($6%,$+$)#%#*%.$K#&#'#+$^$t#.#-#,#0#K$c#F#E#A#G#D#f#J#L#O#N%F#1#5#C#H#/#4#B#6#I#2#=#M#Q#P#T#U#W#Y$s%:#g#k$3#3#7#R#X#?#Z$n%3%;#9#>#S$r$x#e#m#V$l#]#^%5$<$*#8#:$z#\%9%1#a#i%J#;#<#[%&%E#d#c#h$}%+%-#_%$%6#n#t#x$&$g%0%B%A%C%L$j#v%Y#r#|$B#@$R$i$h%%$2%D#`#j%O%P%S#p#q#s%W$$$#$M$d$J$v%?%@#b%H%K#l#u#o%U%I%[$C#}$'$G$T$U$W$]$`$e$f$a$k$q$y$u%#%4%7%8%=%<%N%M%Q%R%T#w%V%X%\%Z#~$0$9$=$;%($@$A$7$\$[$8$>$?$P$-$I$V$E$H%'$o$%%2$m$N$Q%G$b$,$F$O$4$L$|$5$p$w%)$/$1${%*%>$~U%/%$j%%0&$N&%1%%2%#|$%3&%4$%5$%6%%7'%8*%9$%:$%;%%<%%='%>$%?*%@%%A$%B%%C+%D$%E%%F'%G'%H%#>$%I&$C%%J%%K(%L&%M&%N$%O&%P&%Q$%R%%S%$J)%T%%U$%V&%W)%X$%Y*%Z(UT7T[;T,;#;#;#;#;#UTI#UTJ#UTI(UTJ#UT\#k##&#UT7%ZSmS$OQS*S&JOS*4MOS+#PS$S'S*VSV*S&GS*&C$#&S%S*RJ#0O1O'#$)#(#J24Q(#Q+O,O'$#)#(#HUT8I%I$#%I*#%I-#4MS12#j#$=#->#j#%?#-@#k##8##;##?##A#$GS&GS+$S&##%#7QS*O#4MS'O#&S%ORJ#0S11S1'#$)#(#J2s#6S,(#S,+S1,S1'$#)#(#H%I#s#$%I)#%I,#4MS/1#j#$s#>#-s#?#j#%s#@#-s#A#k##7#7S'Q)QEs#H#OZSmS$S/S1S,%#k##'#k##?#k##s###j##s#(#PS$S,S+VSVs#OS*&C#s#)&S%S+RJ#0S'1S''#$)#(#J2s#XO(#O+S',S''$#)#(#H%I#s#F%I)#%I,#4MS01#j#$s#`#-s#a#j#%s#b#-s#c#k##7##:##=#OQ4MS,O#PS$S0OVSVs#mQGO&C$#4MSDs#As#3j#$s#n#-s#o#j#%s#p#-s#q#k##s#G##)##-#PS$S/S'VSVs#yOGS'&C$#&S%S'RJ#0S01S0'#$)#(#J2s$'S1(#S1+S0,S0'$#)#(#H%I#s#q%I)#%I,#4MS21#j#$s$/#-s$0#j#%s$1#-s$2#k##7##:##>#$GOGS,$O##%#7S1S'O#4MS/S0#&S%S0RJ#0S21S2'#$)#(#J2s$GSD(#SD+S2,S2'$#)#(#H%I#s$5%I)#%I,#4MSI1#j#$s$O#-s$P#j#%s$Q#-s$R#k##7#7S/S1)S1Es$Y#S0ZSmS$SIS2SD%#k##'#k##?#k##s###j##s#(#VSVs$_S'&C#s#(&S%S,RJ#0S/1S/'#$)#(#J2s$hS0(#S0+S/,S/'$#)#(#H%I#s$V%I)#%I,#4MS@1#j#$s$p#-s$q#j#%s$r#-s$s#k##7##:#PS$S2S1VSVs$zS1GS0&C$#4MSWs#=s#/j#$s${#-s$|#j#%s$}#-s$~#k##s#C##)#VSVs%(S0GS/&C$#&S%S/RJ#0S@1S@'#$)#(#J2s%2S2(#S2+S@,S@'$#)#(#H%I#s$|%I)#%I,#4MSE1#j#$s%:#-s%;#j#%s%<#-s%=#k##7##:#$GS0GSD$S0##%#7S2S/O#4MSIS@#&S%S@RJ#0SE1SE'#$)#(#J2s%QSW(#SW+SE,SE'$#)#(#H%I#s%?%I)#%I,#4MSG1#j#$s%Y#-s%Z#j#%s%[#-s%\#k##7#7SIS2)S2Es%c#S@ZSmS$SGSESW%#k##'#k##?#k##s###j##s#(#&S%SDRJ#0SI1SI'#$)#(#J2s%pS@(#S@+SI,SI'$#)#(#H%I#s%^%I)#%I,#4MSA1#j#$s%x#-s%y#j#%s%z#-s%{#k##7#VSVs&$SDGS2&C$#4MSXs#9s#+j#$s&%#-s&&#j#%s&'#-s&(#k##s#?#$GS2GSI$S2##%#7SWS@O#4MSASE#&S%SERJ#0SX1SX'#$)#(#J2s&;SG(#SG+SX,SX'$#)#(#H%I#s&)%I)#%I,#4MS`1#j#$s&C#-s&D#j#%s&E#-s&F#k##7#VT]SASW7SASW0#0SA&C$#+&+SA&C$#8)8SA&C$#5,5SA&C$##&##*##.#7SGSE0#0SG&C$#+&+SG&C$#8)8SG&C$#5,5SG&C$##&##*##.#7SXSA)SAEs&n#SGZSmS$SwS`Sn%#j##'#+'&C#s#78)8SX&C$#5,5SX&C$##&##*#7SnSG0#0Sn&C$#7S`SX+#+S`&C$#8&8S`&C$#5)5S`&C$##&##*#7SoSn+#+So&C$#8&8So&C$#5)5So&C$##&##*#7SwS`)S`Es'=#SoZSmS$S[SJSx%#j##'#8'8Sw&C$#5*5Sw&C$##&#7SxSo+#+Sx&C$#7SJSw8#8SJ&C$#5&5SJ&C$##&#7SaSx8#8Sa&C$#5&5Sa&C$##&#7S[SJ)SJEs']#SaZSmS$SBS7T9%#j##'#5'5S[&C$#7T9Sa8#8T9&C$#7S7S[5#5S7&C$#&S%SFRVTKS)CVTK#C0SB>S)CH#8SB>'C$#H'#S8FS$'%3G&1SB$*#,SB$%##%#5SB$&#+SB$%##%##(##.##0##2#j#&S)#-S)#?<#$G:##*j##%#&S%SBROH4MSCS5#VSVs(0S6GJ&C$#&S%S&RJ#0Q1Q'#$)#(#J2s(:SH(#SH+Q,Q'$#)#(#H%I#s((%I)#%I,#4MSK1#j#$s(B#-s(C#j#%s(D#-s(E#k##7#$GS5$S5s(B#$#7S+S8O#4MS3S;#&S%QRJ#0S,1S,'#$)#(#J2s(WS<(#S<+S,,S,'$#)#(#H%I#s(E%I)#%I,#4MS=1#j#$s(_#-s(`#j#%s(a#-s(b#k##7#7OSH0#&C#s(\7S'S;+#&C#s'p7S,S38#8S,&C$#7S1S<5#5S1&C$#$Gs'U$s'Vs'U$s'Vs'O#$#5S0$s'R#$$s'T#$##'##+#k#'-#k#(2#k#)7#k#*;#k#+?#k#,s#7#k#-s#;#k#.s#?#k#/s#W#k#0s#[#j#1S%#OR4MS8S6#VSVs)0S9GR&C$#&S%RRJ#0R1R'#$)#(#J2s):SC(#SC+R,R'$#)#(#H%I#s)(%I)#%I,#4MS<1#j#$s)B#-s)C#j#%s)D#-s)E#k##7#$GS6$S6<#$#7RS5O#4MS;SH#2s)PS3(#S3%I#3%I<#4MS>A#j#$s)R#-s)S#j#%s)T#-s)U#k##s#'#7RSC0#&C#s#)7RSH+#&C#s#%7RS;8#8R&C$#7RS35#5R&C$#UT8NUT7NUT^CUT_CUT`CVTaCG.C#S-#/%FDDE#L6&FDDE##6'FDDE##6(FDDE%#VTb)ECS4TLVTcHS&&S4#TLm$%#WTdCGJXTeHS&$#l#2*)#l#332#l#465#$GG#######%#l#5'#H$Gs#O$s#Ps#O$s#Ps#I#$#$s#KB$s##s#M#$##&##*#m#,#j#'s#'#j#(s#,#j#)s#1#j#*s#5#j#+s#9#j#,s#D#j#-s#H#j#.s#L#j#/s#d#j#0s#h#dT:S%Rs#k#S9HSaSGSASESWSIS/S'S*S&j#6s$l#U#Hj##s%0#0S9>S)CH#8S9>s%3C$#Hs%3#SCFS$'%3G&1S9$*#,S9$%##%#5S9$&#+S9$%##%##(##.##0##2#j#&S)#-S)#0S6>S)CH#8S6>s%JC$#Hs%J#SHFS$'%3G&1S6$*#,S6$%##%#5S6$&#+S6$%##%##(##.##0##2#j#&S)#-S)#$G9##)j##%#0S5>S)CH#8S5>s%dC$#Hs%d#S;FS$'%3G&1S5$*#,S5$%##%#5S5$&#+S5$%##%##(##.##0##2#j#&S)#U#H0S8>S)CH#8S8>s%{C$#Hs%{#S3FS$'%3G&1S8$*#,S8$%##%#5S8$&#+S8$%##%##(##.##0##2#0SC>S)CJ#8SC>s&4C$#Hs&4#S<FS$'%3G&1SC$*#,SC$%##%#5SC$&#+SC$%##%##(##.##0##2#0SH$G#1SH$%#,SH$%##%#5SH$&#+SH$%##%##(##.#j##1#8SHFS$2#3G$##(#%#0S;>S)CS*#8S;>s&]C$#Hs&]#S>0S38S3FS$$#3G$1S3$'#,S3$%##%#5S3$&#+S3$%##%##(##.##0#0S<8S<FS$$#3G$1S<$'#,S<$%##%#5S<$&#+S<$%##%##(##.##0#0SK$G#1SK$%#,SK$%##%#5SK$&#+SK$%##%##(##.#j##1#8SK3G###'0S>8S>FS$$#8S=3G#0S=1S=$$#,S=$%##%#5S=$&#+S=$%##%##(##/#8SM3G#0SM1SM$$#,SM$%##%#5SM$&#+SM$%##%##(##/#0SL$G#1SL$%#,SL$%##%#5SL$&#+SL$%##%##(##.#j##1#8SY3G#0Sb1Sb$$#,Sb$%##%#5Sb$&#+Sb$%##%##(#0SN1SN$$#,SN$%##%#5SN$&#+SN$%##%##(#0SO$G#1SO$%#,SO$%##%#5SO$&#+SO$%##%##(##.#j##1#0Sg1Sg$$#,Sg$%##%#,SP5SP$$#+SP$%##%#0SZ3G#UT;s-VVT<%#&C#G8SZ$G#B)$UTfS$$$#;s-\;#;#;#;#;#;#;#;#;#UT;#;T,;#;#;#;#;#;#;#;#;#;#;#;#;#;#;#UT;#USh3USh#USh#;#;#;#;#;#;#;#;#;#;#;#;#;#;#;#UT;#$s#46UShs.4USh#;#;#;#;#;#;#;#;#;#;#;#;#;#;#;#UT;#$6s#N?6##s#G##s#K##s#N##s#R#0SQ$G#1SQ$%#,SQ$%##%#5SQ$&#+SQ$%##%##(##.#j##1#VT<1s#a&C#G8SQ$G#B5$$#s#`$$s#D$s#28?$##&##)##,#0S\3G#0SyVT<#s#p&C#G8Sy$G#B'$$#s#o$$s#S$s#A*?$##&##)##,#VS]CS+=C#S&s'cVS]CQ=C#S*s'e=C%J#UShT,KC#KCs.}.C$S-#/s'iFDDE#LUShs/%KC#.C'S-#/s'mFDDE#L6s'nFDDE'#UTgDKCT,KCs/,.C$S-#/s'sFDDE#L.C%S-0/s'uFDDE#L6s'vFDDE%#.Cs'vSc)/s'xFDDE#L.Cs'xS-+/s'zFDDE#L6s'{FDDE'/6s'|FDDE$#:s'}FDDE'0#:s'~FDDE*1#:s(#FDDE32#l#2#s'ys'sl#3?s(&#l#4s(*s()#j#7C#j#8C#j#9C#j#:C#j#;C#$S&S*$S*S+#$#$JS&##&3GS&$GS*$S+Q#)#$QO$OS'#$##&##)#k##+#k##-#k##0#k#7C#k#8C#k#9C#k#:C#k#;C#+Si5Si,Si1Si0Si\H'&%$#QOS&l#5?)#j#<s#H#j#=s#V#V#JHj##s#Z#j##s$j#Ds$ks#xs#h#S1j#>s$n#j#?s$u#V#JHj##s%$#j##s%7#Ds%8s%3s%##Hj#6s%?#j#@s%L#V#JHj##s%R#j##s%m#Ds%ns%bs%R#Hj#6s%q#j#As&%#V#JHj##s&*#j##s&K#Ds&Ls&?s&/#Hj#6s&P#j#Bs&b#V#JHj##s&i#j##s'2#Ds'3s'$s&p#Hj#6s'9#j#&S)#V#JHj##s'Q#j#CS)#YT-S)s'ns'j#Hj#6s()#U#Hj##s*W#ZTMs*qs*Xs*Ts(C#Sn0SF$G#1SF$%#,SF$%##%#5SF$&#+SF$%##%##(##.#7SBS7O#4MS6S9#PS$S8%)S7Es06#SFVSVs07#G)&C$#&S%+RJ#7S5S90#1$'#$)#(#J)S9Es0C#S62s0D#(#$+,,-'$#)#(#H%I#s02%I)#%I.#4MSC3#j#$s0L#-s0M#j#%s0N#-s0O#k##:##=##s###?s++s(`7S9SFPS$SC#j##%#&S%S9R4MSHS8s+/2s0\S5@#,J1J'$#&C&#2s0bS;(#S;%I#s+%%Is+.#4MS>s+3#j#$s0d#-s0e#j#%s0f#-s0g#k##s+9#$GS8,S*1S*'$#$S8##'#7S+SCO#4MS<S3#2s0uSK(#SK%I#s*w%Is+$#4MSMs+)#j#$s0w#-s0x#j#%s0y#-s0z#k##s+/#7OS;0#&C#s0t7S'S3+#&C#s0,7S,S<8#&C#s*v7S1SK5#&C#s*u7S/S=PS$SO#k#Ds*m#k#'&#k#(*#k#).#k#*2#k#+6#k#,A#k#-s#%#k#.s#,#k#/s#7#k#0s#>#j#1S%#4MSCS5s*m2s1>S6@#'s*as*h&C$#%Is+es*_%Is*h#4MSKs*m#j#$s1B#-s1C#j#%s1D#-s1E#k##s*s#$S5,#s+_#7RS8O#4MS3S;#%Is+Us*l%Is*u#4MS=s*z#j#$s1O#-s1P#j#%s1Q#-s1R#k##s+$#0s*X&C#s+%+s*W&C#s*|8s*U&C#s*X7RS<5#&C#s*W7RS>&S%#R7RS=0#>S)CH#8%>s,XC$#Hs,X#SOFS$'%3G&1*$*#,,$%##%#5/$&#+1$%##%##(##.##0##2#j#&S)#-S)#'GGLS>#LJH&S4#Sdk###s%C$HJLS&J&S4#Sdk##%##'#LS*S&&S4#Sdk##s%K#j##&#j##$Hj##-#VThJHD/+&$#j#EC#j#CC#k#EC.k#CC#2s24SMUSp#@$$G#VS]CJQs++FDDES*6s+,FDDEs%l#ICs+,s+,.C#S-s%x/s+/FDDE#L:s+0FDDE&s%{#l#2#s+*s+$l#3*s+3#l#4s+7s+6#j#7C#j#FP#$GH##J$s#*Jk##$#k#7C#k#FP#$SLs#hWH#SLS0l#5+%#l#G:8#WHS=s#2#l#6@>#XTNS4s#3Sd#&S4Sds#4BGSMTG#GGGTGGGGGnS4#$##S%H#%#$##&S%#$j#HS4#CS%&LS=s#=ZT#S4Sd%$#Hl#6-,#,*1+'$#LS>#0.B&S>50+1T&%*$#T'''%$nS4#$##S%)#%#$##&S%#5m#/#m##s#fWTis#gs#O#j#Ds+?#j#'s#k#j#(s#o#j#)s#r#j#*s#u#j#+s#x#j#,s$%#j#-s$)#j#.s$,#j#/s$5#j#0s$:#eT:S%Rs$<#S6HS[SXSGSASESWSDS,S+S*S&j#6s${#U#Hj##s-N#-S)s*TPS$S;s%Aj##$#j#&S)s*AU#H>S)CHs*B>s-rC#s*AHs-r#S<##s*2>S)CJs*1>s-vC#s*#Hs-v#SK##s)}7S;SCPS$S>#j##%#FS$s*$s)~3Gs*#1S;$s*'#,S;$%##%#5S;$&#+S;$%##%##(##.##0#>S)CS*s*.>s.0C#s*.Hs.0#S=FS$s)ks)\##s)[7S>S<PS$SY#j##%#3Gs)]1S>$s)`#,S>$%##%#5S>$&#+S>$%##%##(##.#FS$s)fs)h8SL3G###s)A7SYSMPS$Sg#j##%#0SY1SY$$#,SY$%##%#5SY$&#+SY$%##%##(#8Sb3G#7SgSNPS$S\#j##s),#5Sg$s)(#+Sg$%##%#0SP1SP$$#$$s),#$#,SZ5SZ$$#+SZ$%##%#7SQSP&S%#R7S\SZ0#>S)CH#8%>s.rC$#Hs.r#SjFS$'%3G&1*$*#,,$%##%#5/$&#+1$%##%##(##.##0##2#j#&S)#-S)#>S)CSAH>s/+C#8Hs/+#SjFS$H:$H6##4##/#:##'##)#j#IC#>S)CSAs(B>s/6C#HHs/6#SjFS$s(EH3GH$s(GB##@##;#&##(##*#j#IC#8S\>s/BC/#Hs/B#SjFS$s(Q%3G&$s#)H#s#)##/##&##(##*#j#IC#$s#3H+S\$H##%##8##/##1##3#j#IC#>S)CSEs(~>s/WC#s(nHs/W#SiFS$s)%s(p3Gs(q1s#M$s)(#,s#O$%##%#$%s)%##s)##%##+##-#GSQVT=SP#3SP$$%SPLSP&WSz%$#GS\LSZ#GSy3SQ#$$SQBs(-SyTs(-#s(/s(0s(1Ts(.s(.s(.s(1s(2nS4#$##S%J#%#$##1#$s(1#,%$%##%#$%s(8$s(9s(:#$##&#GSq3S\#2s51SqUSp#@$$G#RT$R#R#R#R#NC#NC%NCT$*C$#*C&#9#S#%N#s.6VS]CO=Cs)2S&#=C#Js)0Qs.6FDDES,Qs.7FDDES16s.8FDDEs)##Qs.9FDDES06s.:FDDE$#6s.;FDDE'#.Cs.;S-s)4/s.=FDDE#LICs)5s)+.Cs)7S-#/s.@FDDE#L6s.AFDDE&#;s);KC#.Cs)7S-#/s.EFDDE#L6s.FFDDEs)7#WT%Cs)4s)?.Cs)6S-#/s.IFDDE#L.C%S-s)A/s.KFDDE#L6s.LFDDE%#6s.MFDDE#):s.NFDDE*s)=#:s.OFDDE0s)>#:s.PFDDE7s)?#l#2#s.Js.Dl#3?s.S#l#4s##s.V#j#7C#j#8C#j#9C#j#:C#j#;C#j#JC#j#FP#j#KP#j#LP##s&JS'##S,#O#'S+S&$S*##s)2#BS+Q$S*#$$O#$#$S'S,#s)4##%#k##s)5#k##+#k##/#k#7C#k#8C#k#9C#k#:C#k#;C#k#JC#k#FP#k#KP#k#LP#,T&5T&$$#+T&$%##%#1T&$#)0T&$G#`H'%#)+,Si&$S[S=Ol#5s#'.#l#Gs#`s#^#$s)?s#q$s#rs)B#$#$s)Ds)E##s#k#%#m#)#1s#w$s)G#,s#y$%##%#$%s)N##s#t#%#m#+#j#6s#s#U#H$s#vS\NCs#oNCs#q*C#s#l*C%#*Cs#o#*Cs#q#9#S#%N#s/E=Cs/DS&s*>=Cs*AS*s#n=C$J#UShs*>KC#.Cs/FS-#/s/HFDDE#L.Cs*7S-s*</s/JFDDE#L6s/KFDDE#s#r.Cs#gS-s*9/s/MFDDE#L6s/NFDDE#s#s6s/OFDDE&#6s/PFDDEs#x#ICs#ls*D.C.S(#/s/SFDDE#LQs/TFDDES/6s/UFDDE#s*>.Cs*DS-s*D/s/WFDDE#L6s/XFDDE##6s/YFDDE#s*A:s/ZFDDE's*I#:s/[FDDE*s*J#:s/\FDDE.s*K#:s/]FDDE7s*L#l#2#s/Ws/Ql#3=s/`#l#4As/c#j#7C#j#8C#j#9C#j#:C#j#;C#j#JC#j#FP#j#KP#j#LP#j#MP#$GQ$JS+##S,$QS&##S1#%##S'#'OQ&CS'##SDs*C$S+S+####s*Fs*D#$#k##'#k##)#k##,#k##3#k#7C#k#8C#k#9C#k#:C#k#;C#k#JC#k#FP#k#KP#k#LP#k#MP#2s79Sj@#bHs#os#ms#js#h#s#qs#ks#ns#ps#iJS[SLOl#5B&#l#Gs$is$g#$s*Hs*H###$s*Js*M##s$s#%#m#(#1s$~$s*O#,s%$$%##%#$%s*V##s$|#%#m#+#j#6s#d#U#HnSz%s%1s%0%#H##s%#J#%$##s#g$###l#Ns%4S4#l#Hs%;s%7#m##s%@XSRs%Is%AQ#XSRs%Ks%AS1#XSRs%Ms%AS2#5s&:MCs+js%R$#So+s&<MCs+js%]$#S[8s&>MCs+ds%k$#Sw0s&@MCs+ws%y$#SBXT'S)s&*SE#WTjs&Bs&*#j#>s&E#j#?s&L#V#JHj##s&S#j##s--#Ds-.s-)s&Z#Hj#6s-6#j#@s&_#V#JHj##s&c#j##s&t#Ds&us-Ws&q#Hj#6s-e#j#As&y#V#JHj##s&|#j##s'2#Ds'3s./s'/#Hj#6s.B#j#Bs'6#V#JHj##s';#j##s'O#Ds'Ps.ns'L#Hj#6s'T#j#&S)#V#JHj##s'[#j#CS)#YT-S)s/Ws'_#Hj#6s/q#U#Hj##s0.#ZTMs2Vs0/s**s'f#S`2s8&SFVT.#s*P@HGs*0&C$#j#OK#'s2os2qVT=S7#3S7$$%S7LS7&WSz%$#'s0Is0KLSF#'s04s063SB#$$SB)S6VT.s*:#@#Bs/gS6Ts/o#s/fs/cs/aTs/ps/ps/ps/ds/bnS4#$##S%J#%#$##,#1$'$#&C*#'s0(s0*3S9#'s/o,&C.#<GS6's*H#<G#&C#'UT>Cj#CCH&CJHUTk#j#EC#j#CC#CCs#*j#CK#'JH<G#j#PC#j#OC#CCs*W<GHj#CC#CCS6`SkCKCCSl1S.$SrS6S6#fT(KKKCCCTlS.S.S.(Tms*]s*\'s#&7#`SkKCCCS.S.33-s#&6#CC;`S^CC6561s#'8$<<#USps*a$Gs*aVSSGS53GS5<GS5&C#S5#%#$S5G&C&G#$#?&#<GS8@s33'#HVSSG#3G$<G%&C#&#%#$(G&C&G#$#?&#@s*r'#J<G#Rs&BNC#*Cs%5s&A*C$#9#S#R'NC#UTnT,VToC#NCs&OWS_C$#*Cs%=#*Cs%?#*Cs&M#*C*#9#S#*Cs%C(*Cs&Q#*C3#9#S#*Cs&U49#S#WS_C0s&V*C0s&V*C$#*Cs&Z#9#S#WS_C5s&\*C4s&[*Cs&]#*C%#9#S#WS_C:A*Cs%S'*Cs&b#*C%#9#S#*Cs#&.9#S#%N#s2:%N&#%N,#%N2#%N8#%N;#%N@#%Ns#,#=Cs2@Os&i=Cs-=S&#=C#Js-;;s%ZKC#ICs-6#.Cs-2S(#/s2EFDDE#L6s2FFDDEs&n#.C&S-s2F/s2HFDDE#L.Cs-7S(s2H/s2JFDDE#L6s2KFDDE%#Ss2LFDDE(#.C-S(s-D/s2NFDDE#L6s2OFDDEs&v#.Cs-GS-s2O/s2QFDDE#L.C2S(s2Q/s2SFDDE#L6s2TFDDE%#Ss2UFDDE(#ICs-Cs-N.Cs-NSc#/s2XFDDE#L.Cs2XS-s-P/s2ZFDDE#L6s2[FDDE#s'$.Cs-OS((/s2]FDDE#LWT%Cs-Vs-UICs-L#.Cs-NS(#/s2aFDDE#L:s2bFDDE's-Q#:s2cFDDE*s-R#:s2dFDDE.s-S#:s2eFDDE2s-T#:s2fFDDE<s-U#l#2#s2`s2Zl#3s#*s2i#l#4s#.s2l#j#7C#j#8C#j#9C#j#:C#j#;C#j#JC#j#FP#j#KP#j#LP#'S+Q&CH##O#$%G&CHG#$#?&#&COS+#S,#$S+G&COG#$#?&#'S*S+3Q##s8YS/'QO&CS,#BS'S,'O#&CQ#k##&#k##)#k##+#k##.#k##5#k#7C#k#8C#k#9C#k#:C#k#;C#k#JC#k#FP#k#KP#k#LP#'s0os0q$S3#3GS3@s4R'#S*3G#bH'&#S*%S3s0ws0uJS&S+OSJS[l#5s#-*#l#Qs$6C#l#Rs$Bs$:#l#Ss$FC#l#Ts$Ps$H#l#Gs$Ss$R#XSss$ns$js$U#,s$y1s$z'$#&Cs$~#m#'#j#6s$v#U#H$s$yS9's26s26&Cs%(#&Cs$v$CC%`S^CCs$vs$us$vs$qs%+s$xs$d&&#*Cs$-s()9#S#*Cs$4s(+9#S#*Cs(/$9#S#WS_Cs$Fs'#*Cs'#s$8*C$#*Cs(3#9#S#*Cs(6$9#S#*Cs$T/9#S#%N#s3h%N&#%N)#%N/#%N2#%N5#VS]CS'=Cs3mO#=Cs.jS&#=C#Js.hICs.fs$..Cs3nSc#/s3pFDDE#L.Cs._S(%/s3rFDDE#L6s3sFDDE%#6s3tFDDEs(?s$,Ss3uFDDE$#.Cs$6S(s(5/s3wFDDE#L6s3xFDDEs(A#.Cs(8S-s3x/s3zFDDE#L6s3{FDDE#s$*Ss3|FDDE&#ICs.ts.p.C#S-s(=/s4#FDDE#L.Cs.xS(%/s4%FDDE#LICs.os.o.Cs.qS(#/s4(FDDE#L:s4)FDDE&s.t#:s4*FDDE)s.u#:s4+FDDE-s.v#:s4,FDDE5s.w#l#2#s4&s3|l#3?s4/#l#4s#$s42#j#7C#j#8C#j#9C#j#:C#j#;C#j#JC#j#UC#j#FP#j#KP#'S&O3G#&CH$#$##S's$$?$#&CS'O#S1#$OG&CS'G#$#?&#$s#|S''OS'&CQ#'QQ&CS+#k##%#k##(#k##*#k##1#k#7C#k#8C#k#9C#k#:C#k#;C#k#JC#k#UC#k#FP#k#KP#$s#wGaHs#z#S*S3s23s21s#ys25JS&S+OS[l#5s##%#l#Qs%NC#l#Rs%Zs%R#l#Ss%^C#l#Ts%hs%`#l#Gs%ks%j#XSss#ls#ks#i#,s&41s&5'$#&Cs&:#m#'#j#6s#t#U#HnSz%s&Bs&A%#H##s&6J#%$##s#w$###l#Ns&ES4#l#Hs&Ls&H#@s&S&C#s.Cm#%#2s;{s.GWTOs;|s.ISFMKs&Xs&T%$#m##s.G7HS9&S%#Rj#1S%#LSBs,fUSps-G$Gs-G's3?s3A$S5#WH#S5Snl#5s,Gs,A#l#G('#WHS9s,n#l#6s,\s,Z#XTNS4,Sd#&S4Sd-BGS6TG#GGGnS4#$##S%H#%###s,>&S%#s,?j#HS4#LS9s,wZT#S4Sd$s,>#Hl#6+*#LSBs,:Bs,<SBTs,:#s,>s,8s,7nS4#$##S%%#%###s,6&S%#s,Hm#(#7RSB&S%#Rm#%#MS%R@#S6HUJ#j#Vs.I#Js.Jm#$#USWH's3vs3})#(#J(s.NS5's3ss3x)#(#H%I#s<7%I'#%I)#4MSHs4+#j#$s<Q#-s<R#j#%s<S#-s<T#'s3ps3w)#(#J2s<[S8(#S8's3ns3s)#(#H%I#s<G%I'#%I*#4MS;s4&#j#$s<a#-s<b#j#%s<c#-s<d#7SHS80#1$'#$)#(#J)S8Es<o#SC2s<p#(#$+,,-'$#)#(#H%I#s<^%I)#%I.#4MS33#j#$s<x#-s<y#j#%s<z#-s<{#j##:#'s4,s4.)#(#J's4(s4-)#(#H%I#s<m%Is6N#%I(#4MS3s47#j#$s=+#-s=,#j#%s=-#U#H's,`s4()#(#J's,\s,a)#(#H%I#s<{%Is7\#%I(#4MS<s41#j#$s=9#-s=:#'s4+s4/)#(#S&'s4's4,)#(#H%I#s=+%Is/@#%I(#4MSKs48#j#$s=E#-s=F#7SKS30#1$'#$)#(#J)S3Es=Q#S<2s=R#(#$+,,-'$#)#(#H%I#s=@%I)#%I.#4MS=3#j#$s=Z#-s=[#j#%s=\#-s=]#j##:#'s4>s4B)#(#S*'s4:s4?)#(#H%I#s=O%Is6v#%I(#4MS>s4K#j#$s=i#U#H's4;s4=)#(#S+'s47s4<)#(#H%I#s=[%Is7{#%I(#4MS=s4F#'s-4s45)#(#Q's-0s-5)#(#J%I#s=e%Is/g#%I(#4MSMs4>#'s49s4:)#(#O2s>)S>(#S>'s47s4<)#(#S&%I#s=q%I'#%I*#XTPMSLs4E#UT/$@#XT0MSLs4H##&#0s->1s-?'#$)#(#J)SMEs><#SL2s>=#(#$+s-G,s-H'$#)#(#H%I#s>+%I)#%I.#4MSN3#j#$s>E#-s>F#j#%s>G#-s>H#j##9#'s4Qs4R)#(#S'2s>PS=(#S='s4Os4T)#(#S*%I#s><%I'#%I*#UT/#@#XT0MSYs4_#'s4Qs4S)#(#S,(s/,SM's4Ns4S)#(#S+%I#s>I%I'#%I)#XTPMSbs4]#'s-js-k)#(#S12s>iSL(#SL's-hs-m)#(#Q%I#s>U%I'#%I*#UT1#US{$XT?MSNs-x##%#'s4[s4\)#(#S02s>xSY(#SY's4Ys4^)#(#O%I#s>d%I'#%I*#UT/#@#XT0MSOs4i#0s-z1s-{'#$)#(#J)SNEs?-#SO2s?.#(#$+s.',s.('$#)#(#H%I#s>x%I)#%I.#4MSZ3#j#$s?6#-s?7#j#%s?8#-s?9#k##9#j##s#(#US{>XT?MSOs5'#'s4ws4x)#(#S/2s?DSb(#Sb's4us4z)#(#S'%I#s?0%I'#%I*#UT1#'s4vs4x)#(#SD2s?PSN(#SN's4ts4y)#(#S,%I#s?<%I'#%I*#US{#XT?MSPs5(#'s4us4v)#(#S22s?]SO(#SO's.Qs4x)#(#S1%I#s?I%I'#%I*#UT/#@#XT0MSZs5'#'s.Vs.W)#&Ks<X#2s?kSg&K##'s5$s5')#&Ks=e###S?#'##*#'s.Ms.T)#(#J)SZEs?w#SQ2s?x#(#$'s.Ms.R)#(#H%I#s?d%I'#%I,#4MSqs.a#j#$s?~#-s@##j#%s@$#-s@%#j##5#2s@*SP&K##2s@,S/'s.ps.s)#&K%###S?#(#'s4Js4L)#&Ks=A#2s@5SQ&K##,S\'s.:#)#&Ks=f###S?#(#2s@=S\&K##+Sy,Sy'$#)#&Ks=1###S?#)#7SjSq0#1$'#$)#(#J)SqEs@M#Si2s@N#(#$+,,-'$#)#(#H%I#s@<%I)#%I.#4MT@3#j#$s@V#-s@W#j#%s@X#-s@Y#j##:#2s@^SI+Sq,Sq'$#)#&K'###S?&Ks.6s.62s@fSE+Sj,Sj'$#)#&K'###S?2s@mSA's-Es-H)#&K%###S?7TQT@0#1$'#$)#(#J)T@Es@y#St2s@z#(#$+,,-'$#)#(#H%I#s@h%I)#%I.#4MS|3#j#$sA&#-sA'#j#%sA(#-sA)#j##:#2sA.SX+St,St'$#)#&K'#,S}1S}'$#VT=St#3St$$%StLSt&WSz%$#,S|1S|'$#LTQ#,Se1Se'$#3S}#$$S}0Su1SuB#ST,Su5Su+SuT(&%$#T)))%$nS4#$##S%S*#%#$##0#1$'#$)#(#J)STEsAT#S~2sAU#(#$+,,-'$#)#(#H%I#sAC%I)#%I.#4MSU3#j#$sA]#-sA^#j#%sA_#-sA`#,S:1S:'$#3S|#'s##s#%)#(#J's##s#%)#(#H%I#sAU%I;#%I(#4MSUs#.#j#$sAo#-sAp#j#%sAq#)SeWTRsAv#S:AsAwS7#0S~1S~B#S:'#%)#)S:WTRsA~#STAsB#SF#(&#EsB%&ST2sB&#(#$+S~,S~'$#)#(#H%I#sAp%I)#%I-#4MTA6#j#$sB.#0ST1ST'#$)#(#S72sB7S:(#S:+ST,ST'$#)#(#SJ%I#sB%%I)#%I,#B0Se'#2)#(#s#+EsBEs#.S:2sBF#(#$%I#,%I'#2sBJS72sBKs#3VSv$#&KHs#/&Ks#*s#*2sBOSa&K#s#'##S?#&##(#j#OK#VTSs#>@VSvs-2H&K#s#9##(j#OK#VT.s#%s#C2sB[STVTSs#=#VSvs-9#&K#s#@&KHH##1#%#j#OK#VSv;0&K#s##&K--2sBfSJ&K#s#-##S?#&#@B<GSe@s#7VT2$#B&#<Gs#/&C$#UT>K@J&C#s-M&KJHVTpJHWTq%$#j#EK#j#CK#CC1CCSe`SkCKCCSls-2S.s-%SrSeSe#CC2fT(KKKCCCTrS.S.S.T2Tss#f4$s#H3#fT(KKKCCCTBS.S.S.T3TCs#66's#+3#CCs#?`SkCKCCSls-7S.s-*Srs#@s#@#`S^KC2S.s-9+@5%s#@4#@><Gs#J&C$#CC%Us-0s#MCCs#N`SkCKCCSls-?S.s-2Srs#Os#O#`S^KC:S.s-A3s#%)&s#O%#XTDs#%(#Q&Ks#2s#2@s#3&C##CC$`S^KC@S.s-G9s#6%#s#6%#XTD'%#S02sC5SB's$Ns$O)#&K%#@&<G&&C$#CC%Us-C)CC*`SkCKCCSls-RS.s-ESr++#`S^KCs#-S.s-Ts#&-)&+%#XTD+(#SI2sCBS9USp#@$$G#USps#Z$Gs#;2sCHSUUSp#@$$G#1SfB#SU0Sf'$#VSSG#3G$<G%&C#&#%#$(G&C&G#$#?&#1T)B#TT0T)'$#<G#VSSGSf3GSf<GSf&C#Sf#%#$SfG&C&G#$#?&#<GT)2sChTE@#VTtH#3H$VT2H%&C#H#%#$(H&C&)#$#?&#2sCsTF@#VT2J#1TG0TG'$#VSSG#3G$<G%&C#&#%#$(G&C&G#$#?&#1T*0T*'$#<G#+TU,TU'$#VSSG#3G$<G%&C#&#%#$(G&C&G#$#?&#+T4,T4'$#<G#Rs-vR#R#R#NC#NC'*Cs1cs-v*C$#*C&#9#S#R)NC#WS_Cs.##NC-WS_Cs.%#*Cs-os-h*Cs..#*C%#*C(#9#S#*Cs1qs.)*C2#*C4#9#S#R0NC#*Cs.8s-w*C/#*C2#*C&#9#S#NC@*Cs.9s0p*C$#9#S#WS_Cs.:AWS_Cs.;A*C#s,M*C:#*C&#*C?#9#S#*Cs.)s.5*Cs#(#*CA#*Cs#+#9#S#*C2s.H*Cs#'#9#S#9-S#*Cs25s23*Cs.3#*Cs#2#*Cs#+#*Cs#5#9#S#*Cs.Rs1,*Cs#1#9#S#*C?9*Cs#1#*C=#9#S#*Cs2Bs12*Cs.@#*Cs#?#*Cs#8#*Cs#B#9#S#%Ns#?s=v%Ns#@#%Ns#A#%Ns#B#%Ns#5#%Ns#6#%Ns#7#%Ns#8#%Ns#.#%Ns#/#%N@#%N;#%N/#%N6#%Ns#-#%N<#%N@#%Ns#'#%Ns#)#%Ns#*#%Ns#.#%Ns#4#%Ns#<#%Ns#=#%Ns#I#%Ns#N#%Ns#D#%Ns#L#%Ns#[#%Ns#\#%Ns#S#%Ns#^#VS]CS1=C#S0s>9=C#Os>:=Cs97S&#VS]CS,=C#Qs>=VS]CS0=C#S0s>?=C#S's>@=C&S*#=C)J#KCs:%ICs2]#.Cs>BSc#/s>DFDDE#L;s:)KC#.C#S('/s>HFDDE#L6s>IFDDE'#.C*S-s>I/s>KFDDE#L.C(S(s>K/s>MFDDE#L6s>NFDDE%#Ss>OFDDE(#Qs>PFDDESDKCs:4.Cs9?S(#/s>SFDDE#L6s>TFDDE&#.Cs9LS-&/s>VFDDE#L.Cs9DS(s9N/s>XFDDE#L6s>YFDDE%#Ss>ZFDDE(#.Cs>ZScs1s/s>\FDDE#L.C.S(s1u/s>^FDDE#L6s>_FDDE%#.Cs1xS-s>_/s>aFDDE#L.C3S(s>a/s>cFDDE#L6s>dFDDE%#Ss>eFDDE(#WT%Cs3%s1~IC#s#(.Cs>gSc#/s>iFDDE#L.Cs9bS(%/s>kFDDE#L6s>lFDDE%#.C(S-s>l/s>nFDDE#L.Cs9gS(s>n/s>pFDDE#L6s>qFDDE%#Ss>rFDDE(#.Cs9aS(s#//s>tFDDE#LICs9hs34.Cs22Sc#/s>wFDDE#LQs>xFDDES2.Cs#:S-s38/s>zFDDE#LQs>{FDDES@6s>|FDDE$#Qs>}FDDESI6s>~FDDE$#6s?#FDDE)#Qs?$FDDESW6s?%FDDEs2;#.Cs9yS(//s?'FDDE#LWT%Cs9rs9q.C#S(s9}/s?*FDDE#L:s?+FDDE&s9v#:s?,FDDE)s9w#:s?-FDDE,s9x#:s?.FDDE5s9y#:s?/FDDE9s9z#:s?0FDDE<s9{#:s?1FDDEs#*s9|#:s?2FDDEs#6s9}#:s?3FDDEs#Bs9~#l#2#s?-s?'l#3s#Ss?6#l#4s#_s?9#j#7C#j#8C#j#9C#j#:C#j#;C#j#JC#j#UC#j#WC#j#XC#j#YC#j#FP#j#KP#j#LP#j#MP#j#ZP#'QS'3G#&CS,$#$#$&G&CS,G#$#?&#&CS&S0#S/#$S+S0&CS&S+#$#?&#3GS,&CS/S,#$#$S,G&CS/G#$#?&#BS,S1'#S03G#&CQ$#$#$&G&CQG#$#?&#&CS+SD'S1S03S/#$S2S/##SA##SG#SE##sCNSn'SDS2&CS/#BS1S0&C#S/k##%#k##(#k##*#k##/#k##2#k##4#k##>#k##s#&#k##s#-#k#7C#k#8C#k#9C#k#:C#k#;C#k#JC#k#UC#k#WC#k#XC#k#YC#k#FP#k#KP#k#LP#k#MP#k#ZP#,T+1T+'$#$T4#5T+$'#+T+$%##%#$*+0T+$G#2sGFTu@#3S'#@s+/i#;H/*)'$S'S*(T412%S1Q#S+OS,S0S@SESZS~TAl#5s#V4#l#[s%qC#l#\s%~s%v#l#]s&'C#l#^s&4s&,#l#_s&9C#l#`s&Es&=#l#as&IC#l#bs&Ss&K#l#cs&UC#l#ds&cs&[#l#es&ks&i#l#fs&os&n#l#Gs&ss&q#l#gs&vs&|#l#gs'(s'+#l#gs'/s'5#XSss'Vs'Js'9#CKs'a`S^KCs'KS.s1rs'Ds'Vs':s'7s($s'9s'4+Sf,Sf'$#VSSG#3G$<G%&C#&#%#$(G&C&G#$#?&#+T),T)'$#<G#1TV0TV'$#VSSG#3G$<G%&C#&#%#$(G&C&G#$#?&#1TE0TE'$#<G#9s1HS#%N#s@vVS]CS&=C#Js@v.Cs;cS(s;b/s@vFDDE#L:s@wFDDE#s;f#l#2#s@qs@kl#3's@z#l#4*s@}#j#7C#j#8C#&CHJ&CJS&k##$#k#7C#k#8C#@sAXWHS*#S0l#5*%#l#a7C#l#bs#$<#l#cs#)C#l#ds#6s#.#l#es'Ps'N#l#fs'Ts'S#l#Gs'Xs'V#l#gs'[s'a#l#gs'is'l#l#gs'ps'v#XSss(8s'ws#A#XSRs(9S?#TWXSRs(<s(9s#D#XSRs(>s(9s#F#WTOsHEs).S:MKs(Js(B$s(^#WTvsHGs)0S:MKs(Qs(M$s([#2sHIs)0WTHsHJS7s)2MKs(]s(U%$#UT1s(am#$#UT8sHNAsHOSJ#AsHPs(i#AsHQs)9#AsHRS7#AsHSSa'AsHTST#AsHUSF#&sHSH#j#hsHT#AsHXs)@s(qAsHY#,AsHZSFH&sHX#(j#hsHY#AsH]H,AsH^SF#&sH\#,j#hsH]#AsHaS:4AsHbS7#CsH`#WTwsHds)MS:MsHbS:'$/#XT5sHfs)Ns)#9MsHd0-$8#AsHhs)O:XT5sHiS7s)Q;ZT#sHg:5%$#US{s)$US{s).&sHj$#m#&#\TXMSus)?s)1s)(Sxs#$#XT'sHms)ASJ#XT'sHns)[s)X#0s*)1s**'#$)#(#J+s*.,s*/'$#)#(#H%I#sHc%Is*)#%I*#4MSU/#j#$sH}#-sH~#j#%sI##-sI$#m#5#j#6s)|#U#H$s*#S|'s*Es*E)#(#J's*Cs*H)#(#H%I#sHu%Is*;#%I(#4MSUs*N#j#$sI3#-sI4#j#%sI5#'s){s){)#(#s#K's)rs)~)#(#H%I#sI&%Is)w#%I(#4MTAs*(#j#$sI@#AsIDS:SJAsIES7#'s)rs)r)#(#s#X's)ns)u)#(#(%I#sI3%Is)d#%I(#&KT$7AsIPSTSaAsIQSF#2sIR#&K#8##S?#s)T##)#j#OK#2sIX6VSvs)m#VT.s)]s*;&K##&KHA##S?#%##2#j#OK#VSvs*,s)Y&Ks)js#'##S?#+##8#j#OK#&KT$BVSvs)|)&K#A##S?#s)d#<Gs#(&CG#CCGCCs#+`SkCKCCSls4'S.s3vSrs#,s#,#`S^KCs)^S.s4)s)WT$G%s#,'#'s)&s)&VSSG#3G$<G%&C#&#%#$(G&C&G#$#?&#'s)#s)#<G#+TF,TF'$#VSSG#3G$<G%&C#&#%#$(G&C&G#$#?&#+T6,T6'$#<G#=CsC&S&s$k=CsC'J#ICs6>s6>.CsC&Sc#/sC(FDDE#LQsC)FDDES+6sC*FDDE$#QsC+FDDEQ6sC,FDDE#s3@SsC-FDDE%#.CsC-S(s=x/sC/FDDE#L:sC0FDDE%s={#l#2#sC*sC$l#3/sC3#l#4s${sC6#j#7C#j#8C#j#FP#j#KP#'JJ3G###S&#S*s2~?$#&CGJk##$#k#7C#k#8C#k#FP#k#KP#'s),s),$#G&CQ$YH$#s)/QOl#52'#l#_s#'C#l#`s#4s#,#l#as%8C#l#bs%Es%=#l#cs#;C#l#ds#Fs#>#l#es)qs)o#l#fs)us)t#l#Gs)ys)w#l#gs)|s*&#l#gs*.s*1#l#gs*5s*;#XSss#Ys#Ss#O#Bs*Us*?Bs*X#<Gs#z&C$#fT(KKKCCCTBS.S.S.T3TCs+2s*Ys*Is*_s*Cs*@fT(KKKCCCTBS.S.S.T3TCs*|s*\s*Ms#e'#CCs#~`SkCKCCSls4}S.s4pSrs$#s$##`S^KCs*XS.s5#s*Qs#a)%s$#(#'s%ks)|VSSG#3G$<G%&C#&#%#$(G&C&G#$#?&#'s%is)y<G#*Cs72s2l*Cs8@#*Cs8B#*Cs4_#*Cs(|#*Cs)&#*Cs)9#*Cs)<#9#S#*Cs4Fs2|*Cs4a#*Cs)F#*Cs)>#*Cs)A#9#S#WS_Cs4ds)0*Cs4Rs4Q*Cs4N#*Cs)M#*C&#*Cs)G#*Cs)2#*Cs)K#9#S#*Cs)T59#S#*Cs8Z<*Cs4w#*Cs)8#*Cs)>#*Cs)Z#9#S#*Cs)=/*Cs)V#9#S#*Cs7Ts4w*Cs7V#*Cs4|#*Cs)G#*Cs)c#9#S#9+S#*Cs8js4p*Cs5+#*Cs)H#*Cs)N#*Cs)j#9#S#*Cs8os4v*Cs8q#*Cs52#*Cs)O#*Cs)U#*Cs)q#9#S#9s#$S#*Cs8ws50*Cs54#*Cs)[#*Cs)b#9#S#%N#sDO%N$#%N*#%N,#%N4#%N;#%N=#%N>#%N?#%N@#%Ns#'#%Ns#+#%Ns#2#%Ns#5#%Ns#?#%Ns#F#=Cs(}S/sD]=C#S+sD^=C#S&s9,VS]CS/=C#S'sDa=C#QsDb=Cs))S/s)-=C$S*#=C(J#UShs?XKC#IC#s?Y.CsDfSc#/sDhFDDE#LKCsK}.C#S(&/sDkFDDE#L6sDlFDDE&#.C)S-sDl/sDnFDDE#L.C(S(sDn/sDpFDDE#L6sDqFDDE%#SsDrFDDE(#UShsL,KC#.C#S(s)5/sDvFDDE#L6sDwFDDEs)5#.C&S(sDw/sDyFDDE#L6sDzFDDEs)1#SsD{FDDE&#IC9s)=.Cs?tS(#/sD~FDDE#L6sE#FDDEs(e#.C&S-sE#/sE%FDDE#L.Cs?yS(sE%/sE'FDDE#L6sE(FDDE%#SsE)FDDE(#.CsE)S-s?s/sE+FDDE#L.Cs?vS(6/sE-FDDE#L.Cs@&S(s##/sE/FDDE#L6sE0FDDEs(ps(mUShs8JKC#.Cs@&S-#/sE4FDDE#L.C%S-s#./sE6FDDE#L6sE7FDDE%#6sE8FDDE*#6sE9FDDEs(x#.Cs@'S(s)#/sE;FDDE#LWT%Cs@*s9S.C#S(s@4/sE>FDDE#L:sE?FDDE&s@.#:sE@FDDE)s@/#:sEAFDDE4s@0#:sEBFDDE7s@1#:sECFDDE:s@2#:sEDFDDE=s@3#:sEEFDDEs#(s@4#:sEFFDDEs#2s@5#l#2#sE@sE:l#3s#CsEI#l#4s#MsEL#j#7C#j#8C#j#9C#j#:C#j#;C#j#JC#j#UC#j#WC#j#XC#j#YC#j#iC#j#FP#j#KP#j#LP#'S'S+3G#&CS1$#$#$&G&CS1G#$#?&#3Gs3x&CS/s3y#$#$s3{G##s(j?%#'S1S,&CQ##S2#$%G##s(g?%#$GS+&CS+S@&CS'S@$SDS/##SG$S0S@$S@S2#$##&##SA#'S/SD&CS,#BS,s(h&C#S/k##%#k##(#k##0#k##2#k##4#k##6#k##=#k##s#$#k#7C#k#8C#k#9C#k#:C#k#;C#k#JC#k#UC#k#WC#k#XC#k#YC#k#iC#k#FP#k#KP#k#LP#,T*$s+{#$Gs+{+T*'#s+}3G#5T*2sMITG@#@s2$i#9H+*'S*J&)s,'s,(,Qs74$#S&S+OS'S0SDSNS:l#5s#F.#l#_s%{C#l#`s&,s&$#l#as(0C#l#bs(=s(5#l#cs%9C#l#ds%Ds%<#l#es,is,g#l#fs,ms,l#l#Gs,qs,o#l#gs,ts,z#l#gs-&s-)#l#gs--s-3#XSss&Os%Rs%M#XSRs&PS?#TWXSRs-Us&Ps(]#XSRs&Ts&Ps%Y#WTHsM^S:SJMKs&\s&W$s&e#2sM`s&yWTHsMaS7s&{MKs&gs&`%$#MKs-gs&j#s-{s'|UT1s&tm#$#AsMfs&ss'vAsMgH#&sMe#s'qj#hsMf#AsMjs'(s'zAsMkS7#XT5sMlS:SJs'|ZT#sMjs'js'os'h%#AsMns'+s'~XT5sMoS7s'-s(#ZT#sMm's'w%$#AsMqs(%%&sMo#s'nm#%#VTYs.?s.]$s-gs-h`S^KCTYS.TZTxs.As-hs-Xs._s-is-YVSSGSU3GSU<GSU&C#SU#%#$SUG&C&G#$#?&#<GTT9s5tS#%N#sFx%Ns5t#QsFvFDDES'.CsAdS(sAj/sFxFDDE#L6sFyFDDE%#.CsAmS-sFy/sF{FDDE#L.CsAiS(sF{/sF}FDDE#L6sF~FDDE%#SsG#FDDE(#ICsAxsAw.C#S-sAt/sG&FDDE#L.CsAqS(%/sG(FDDE#L:sG)FDDE#sAtsAp:sG*FDDE&sAu#:sG+FDDE*sAv#l#2#sG%sF{l#3sB'sG.#l#47sG1#j#7C#j#8C#j#9C#j#:C#j#;C#j#FP#&CJS+#Q#&CJG#s6v#?%#$s6tQ&CS&s7&k###sAmk##%#k##'#k#7C#k#8C#k#9C#k#:C#k#;C#k#FP#3GT6]H#T6s-0s#pQs#hOS2S:l#55%#l#_s''C#l#`s'4s',#l#as)8C#l#bs)Es)=#l#cs#8C#l#ds#Bs#:#l#es-qs-o#l#fs-us-t#l#Gs-ys-w#l#gs-|s.&#l#gs..s.1#l#gs.5s.;#XSss#Ls#Ks#J#XTysNcs/LS:#MsNas(ts#Ys#Os.}#US{s'u&sNc#s(Xm#%#\TXMSus/8s/*s'xSxs#a#XT'sNfs((s(&#XT'sNgs(4s(z#0s/}1s/~'#$)#(#J+s0&,s0''$#)#(#H%I#sN\%Is/~#%I*#4MSU/#j#$sNv#-sNw#j#%sNx#-sNy#m#5#j#6s(U#U#HnSz%s0?s0>%#H##s/{J#%$##s(X$###l#Ns0DS4#l#Hs0Ms0I#7SeS}0#1$'#$)#(#J)S}EsO.#S|2sO/#(#$+,,-'$#)#(#H%I#sNy%I)#%I.#4MST3#j#$sO7#-sO8#j#%sO9#-sO:#m#:#j#<S?#j#js0k#V#JHj##S?#j##s11#Ds12S?s0u#Hj#6s17#j#ks1?#V#JHj##s1B#j##s1i#Ds1js1ds1K#Hj#6s1m#j#ls1v#V#JHj##s1{#j##s2C#Ds2Ds2=s2)#S&j#ms2H#j#ns2W#j#os2e#V#JHj##s2s#j##s3C#Ds3Ds3Bs2w#Hj#6s3Q#V#JHj##s3^#j##s4,#Ds4-s4*s3n#Hl#6Hs4:#j#ps4E#j#$sO\#V#JHj##s4R#j#CsO_#YT-sO`s4ys4`#Hj#6s5)#j#%sOb#V#JHj##s58#j#CsOe#YT-sOfs5as5H#Hl#qs6$s5q#l#rs6&s6'#j#ssB3#XSRsB6sAxs6M#XSRsB<sAxs:K#XSRsB>sAxSI#l#DsBPsBB#j#'sJe#j#(sJj#V#JHj##sJp#j##sJ}#DsJ~sJ{sJu#Hj#6sK'#j#)sK0#V#JHj##sK6#j##sKK#DsKLsKEsK?#Hj#6sKQ#j#*sK^#V#JHj##sKd#j##sL$#DsL%sKvsKp#Hl#6sL:sL*#j#+sL<#j#,sLT#j#-sLX#j#.sL]#j#/sLd#V#JHj##sLi#j##sMc#DsMdsMMsM&#Hj#6sMh#j#tsMs#V#JHj##sMv#j##sNw#DsNxsN]sN6#Hj#6sNz#j#0sO+#V#JHj##sO/#j##sP5#DsP6sOtsOM#Hj#6sP9#j#uC#j#vsP<#j#1S%#j#wC#j#xsP@#j#PTz#j#ysPN##"). Qed.

(* [comment removed for export] *)
Lemma xpres_put_sro : forall (C : rsc) (w : rsw) (SPp E : Z) m m',
  let P := c_P C in let d := w_d w in
  xpres (ps_LBn d ++ c_LBin C) SPp (put_X P E (ps_L d) (ps_es d)) m m' ->
  RWp C w -> rs_static C -> SPp <= P -> E = P + 464 ->
  (forall e, e ∈ ps_L d -> 0 < e /\ e + 48 <= hceil /\ (e + 48 <= 0x10000 \/ 0xb8000 <= e)) ->
  xpres (c_LBin C) P (sro_X P (c_stb C)) m m'.
Proof.
  intros C w SPp E m m'. cbv zeta. intros XP RP STC HS -> EL.
  destruct C as [P N lo B0 stb implb A LBin pad7 pad2 j13 j32a j8a j32b j8b mb m0 mo0 gp tp s8w s9w s10 s11 F fc].
  destruct w as [d PB1 FBB FB fds Fs sds nr]. destruct d as [c S L1 ns ls em h u es insz g rdi LBn st errv]. unfold RWp, rs_static in *. cbn_w_all.
  destruct STC as (P0 & PB & BHI & AL16 & CEIL & IMG & LO & NR26 & INS & RBS & INA & TP & MB1).
  destruct RP as (PCOK & OWN & MOWN & HOWN & EH & ESH & DFB & HST & U01 & CAP & LES & INZ & LEN1 & HDJ & HL8 & SK62
                  & AOWN & PERM & FOK & FRL & FRB & REST).
  assert (LOP : lo + 400 <= P) by (clear - LO; unfold SRO_STACK in LO; lia).
  eapply xpres_restrict; [exact XP|]. intros a Ha [RC NX]. split.
  - destruct RC as [K|[K|(b & Hb & K)]]; [left; lia | right; left; exact K | right; right; exists b; split; [apply in_or_app; right; exact Hb | exact K]].
  - pose proof XH_consts as (X1 & X2 & X3 & X4 & X5).
    unfold put_X, sro_X in *. unfold G_HTTP_CAT, G_FIELD_TABLE, XH_LO, XH_HI, SZ_SPCI_STATE in *. cbn in NX.
    intros IN. cbn in IN. rewrite rin_ivs_app in IN.
    destruct IN as [K|[K|[K|[K|[K|K]]]]]; try (apply NX; clear - K; lia).
    + (* [comment removed for export] *)
      apply rin_ivs_elemsW in K. destruct K as (e & INe & Ke).
      pose proof (proj2 (list_elem_of_In _ _) INe) as INe'.
      destruct (EL e INe') as (E1 & E2 & E3).
      destruct RC as [R|[R|(b & Hb & R1 & R2)]]; [clear - R E2 CEIL LOP Ke; lia | clear - R E3 Ke; unfold RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK in R; lia |].
      destruct (FRL e INe' (blk_addr b) (blk_size b) ltac:(right; right; exists b; split; [exact Hb | lia]) ltac:(lia)); lia.
    + (* [comment removed for export] *)
      apply mb_elemsW_In in K. destruct K as (x & s & INx & Kx).
      destruct (ESH x s INx) as (E1 & E2 & E3).
      destruct RC as [R|[R|(b & Hb & R1 & R2)]]; [clear - R E2 CEIL LOP Kx; lia | clear - R E3 Kx; unfold RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RVMLOCK in R; lia |].
      destruct (FRB x s INx (blk_addr b) (blk_size b) ltac:(right; right; exists b; split; [exact Hb | lia]) ltac:(lia)); lia.
Qed.
End SR.
End HCW.
