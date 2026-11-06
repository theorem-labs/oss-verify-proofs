(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require TP_0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX Exec.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import ASegs AsShadow AsConst AsIface AsIface5 AsIface7 AsIface8 AsCXXHeap AsWalk AsStack0 AXPres AXKit AXRep AXRep2 AXPRep AXPRep2
     AXRep_fields AXRep_mbuf AXImgKit X8Kit X8SRKit X8_P_ftab_rep X8_F_insert2 X8_F_insert4 X8_state1_stmt X8_state2_stmt X8_mbuf_stmt X8_pst
     X8_put_stmt X8_cobj X8_S_place X8_stream_stmt X8_stream_stmt4.
From OSSVerify.Proofs.boost_beast.http_request.lib.RB Require Import RBMem RBShape DList.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prelim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition HREAD_STACK : Z := 208 + BPUT_STACK.

(* [comment removed for export] *)
Definition CAPMAX (N : Z) : Z := 2 * N + 65536.

(* [comment removed for export] *)
Definition hread_X (P E fb stb : Z) (L0 : list Z) (es0 : list mbe) : list (Z * Z) :=
  (fb, fb + 40) :: (stb, stb + SZ_SPCI_STATE) :: put_X P E L0 es0.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record rsw := mkW { w_d : pst ; w_PB : list block ; w_FBB : list block ; w_FB : fbv ; w_fds : list byte ;
                    w_Fs : fbv ; w_sds : list byte ; w_nr : Z }.

(* [comment removed for export] *)
Record rsc := mkC { c_bs : Z ; c_fb : Z ; c_P : Z ; c_E : Z ; c_ioc : Z ; c_N : Z ; c_lo : Z ; c_B : Z ; c_shi : Z ; c_SP : Z ;
                    c_stb : Z ; c_implb : Z ; c_A : Z ; c_LBin : list block ; c_LF : list fframe ;
                    c_pad7 : list byte ; c_pad2 : list byte ; c_j13 : list byte ; c_j32a : list byte ; c_j8a : list byte ;
                    c_j32b : list byte ; c_j8b : list byte ; c_mb : byte ; c_m0 : mem ; c_mo0 : Model ;
                    c_gp : word ; c_tp : word ; c_F : bvmap 5 word ; c_fc : bv 32 ;
                    c_MX : Z ; c_CX : Z }.     (* [comment removed for export] *)

Ltac cbn_w := cbn [w_d w_PB w_FBB w_FB w_fds w_Fs w_sds w_nr c_bs c_fb c_P c_E c_ioc c_N c_lo c_B c_shi c_SP c_stb c_implb c_A c_LBin c_LF
                   c_pad7 c_pad2 c_j13 c_j32a c_j8a c_j32b c_j8b c_mb c_m0 c_mo0 c_gp c_tp c_F c_fc c_MX c_CX
                   ps_c ps_S ps_L ps_ns ps_ls ps_em ps_h ps_u ps_es ps_insz ps_g ps_rdi ps_LBn ps_A].
Ltac cbn_w_all := cbn [w_d w_PB w_FBB w_FB w_fds w_Fs w_sds w_nr c_bs c_fb c_P c_E c_ioc c_N c_lo c_B c_shi c_SP c_stb c_implb c_A c_LBin c_LF
                   c_pad7 c_pad2 c_j13 c_j32a c_j8a c_j32b c_j8b c_mb c_m0 c_mo0 c_gp c_tp c_F c_fc c_MX c_CX
                   ps_c ps_S ps_L ps_ns ps_ls ps_em ps_h ps_u ps_es ps_insz ps_g ps_rdi ps_LBn ps_A] in *.

Definition fbb_ok (FB : fbv) (FBB : list block) : Prop :=
  (FB = FB_empty /\ FBB = []) \/ (FB <> FB_empty /\ exists pf, FBB = [(pf, fb_begin FB, fb_cap FB)]).

(* [comment removed for export] *)
Definition wM (N : Z) (w : rsw) : Z := zlength (w_sds w) * (N + 1) + zlength (w_fds w).

Section HCW.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

(* [comment removed for export] *)
Definition PutUw (P : Z) (mb : byte) (d : pst) (m : mem) : Prop :=
  AFieldsC m (P + 80) (ps_S d) (ps_L d) (ps_ns d) (ps_ls d) (ps_em d)
  /\ rw_cells asegs m (P + O_PR_HDR) (HdrCells (ps_h d)) /\ rw_cells asegs m (P + O_PR_USED) [C1 (b8 (ps_u d))]
  /\ AMBuf m (P + 168) (ps_es d) (ps_insz d) /\ rw_cells asegs m (P + 232) [C8 (wz (P + 168))]
  /\ rw_cells asegs m (P + O_PR_MERGE) [C1 mb] /\ rw_cells asegs m (P + 288) [C8 (wz 0)] /\ rw_cells asegs m (P + 336) [C8 (wz 0)]
  /\ APfTab m /\ FTInit m /\ AXStatics2 m.

Lemma PutU_of : forall P p0 bs mb d m, PutUw P mb d m -> bytes_at asegs m p0 bs -> PutU P p0 bs mb d m.
Proof. intros P p0 bs mb d m (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11) W. exact (conj A1 (conj A2 (conj A3 (conj A4 (conj A5 (conj A6 (conj A7 (conj A8 (conj W (conj A9 (conj A10 A11))))))))))). Qed.
Lemma PutU_split : forall P p0 bs mb d m, PutU P p0 bs mb d m -> PutUw P mb d m /\ bytes_at asegs m p0 bs.
Proof. intros P p0 bs mb d m (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12). exact (conj (conj A1 (conj A2 (conj A3 (conj A4 (conj A5 (conj A6 (conj A7 (conj A8 (conj A10 (conj A11 A12)))))))))) A9). Qed.

(* [comment removed for export] *)
Definition rs_static (C : rsc) : Prop :=
  let bs := c_bs C in let fb := c_fb C in let P := c_P C in let E := c_E C in
     aobj [] (c_LF C) P 352 /\ aobj [] (c_LF C) E 24        (* [comment removed for export] *)
  /\ P mod 8 = 0 /\ E mod 8 = 0 /\ bs mod 8 = 0 /\ fb mod 8 = 0
  /\ (P + 352 <= E \/ E + 24 <= P) /\ (bs + 32 <= fb \/ fb + 48 <= bs)
  /\ aceil <= c_lo C
  /\ 0 <= c_N C < 2^26 /\ 0 <= c_ioc C < 2^64
  /\ (exists p7, In (p7, c_stb C, SZ_SPCI_STATE) (c_LBin C)) /\ rblock_range (c_stb C) SZ_SPCI_STATE
  /\ (1 <= c_N C -> exists p9, In (p9, c_A C, c_N C) (c_LBin C))
  /\ (1 <= c_N C -> c_A C + c_N C <= c_stb C \/ c_stb C + SZ_SPCI_STATE <= c_A C)
  /\ (length (c_LF C) + 4 < AFS_MAXLIVE)%nat /\ (length (c_LF C) + 1 < AFS7_MAXLIVE)%nat
  /\ c_tp C = Z_to_bv 64 ATP
  /\ c_MX C <= as_LIVE_MAX H /\ c_CX C <= as_LIVE_CNT_MAX H.

(* [comment removed for export] *)
Definition rs_placed (C : rsc) (SP : Z) : Prop :=
     sobj SP (c_shi C) (c_bs C) 32 /\ sobj SP (c_shi C) (c_fb C) 48               (* [comment removed for export] *)
  /\ c_lo C + HREAD_STACK <= SP /\ SP mod 16 = 0 /\ SP <= c_shi C /\ SP <= c_B C /\ SP <= c_SP C
  /\ SP + 128 <= c_bs C /\ SP + 128 <= c_fb C.                                       (* [comment removed for export] *)

(* [comment removed for export] *)
Definition RWm (C : rsc) (w : rsw) (s : as_St H) (errv : word) (E : ecv) (m : mem) : Prop :=
  let P := c_P C in let d := w_d w in let LB := ps_LBn d ++ c_LBin C in
     rw_cells asegs m P (ParserCoreCells (ps_c d) (c_pad7 C) (c_pad2 C))
  /\ PutUw P (c_mb C) d m /\ HdrOwnA LB m (ps_h d)
  /\ rw_cells asegs m (P + 240) [C1 (ps_rdi d)] /\ rw_cells asegs m (P + 243) [CB 13 (c_j13 C)]
  /\ rw_cells asegs m (P + 256) [CB 32 (c_j32a C)] /\ rw_cells asegs m (P + 296) [CB 8 (c_j8a C)]
  /\ rw_cells asegs m (P + 304) [CB 32 (c_j32b C)] /\ rw_cells asegs m (P + 344) [CB 8 (c_j8b C)]
  /\ AHttpCat m (ps_g d) /\ (AFieldTabZero m \/ FT m) /\ AMiscVt48 m
  /\ AFlatBuf LB m (c_fb C) (w_FB w) (w_fds w) /\ rw_cells asegs m (c_E C) (ErrCodeCells E)
  /\ rw_cells asegs m (c_bs C) (BasicStreamCells (c_stb C))
  /\ AStateBlock LB m (c_stb C) (c_ioc C) (c_implb C)
       (mkST (mkSPC AVP_SPCI_STATE 1 1 1) 0 (w_Fs w) STREAM_EOF (w_nr w) (c_N C - zlength (w_sds w))) (w_sds w)
  /\ as_RHEAP H s LB m /\ rw_cells asegs m (errno_addr (c_tp C)) [C4 errv] /\ as_rauxv_ok H m (c_B C) /\ mem_inv asegs m
  (* [comment removed for export] *)
  /\ as_RFS H (c_LF C) m /\ ACONST m /\ stack0 m (c_lo C) (c_shi C) /\ athr_cells m
  /\ accessible m P PARSER_SIZE /\ accessible m (c_E C) 24 /\ shvis m (c_E C) (c_E C + 24)
  /\ accessible m (c_bs C) 32 /\ accessible m (c_fb C) 48
  /\ (1 <= c_N C -> shvis m (c_A C) (c_A C + c_N C)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FBU : Z := 2048 + AWILDB.
Definition PHI2MAX (N : Z) : Z := 29 * FBU + 4 * CAPMAX N + 4096 + AWILDB.
Definition fb_res2 (N D : Z) : Z := (29 - Z.log2 D) * FBU + 4 * (CAPMAX N - D).
Definition fb_res (N C : Z) : Z :=
  if C =? 0 then 512 + (512 * FBU + PHI2MAX N)
  else if C <=? 1024 then (1024 - C) * FBU + PHI2MAX N
  else fb_res2 N (C - 1024).
(* [comment removed for export] *)
Definition fb_wild_res (C : Z) : Z := if C <=? 1024 then (1024 - C) + 30 else 29 - Z.log2 (C - 1024).
Definition K_WILD_CALL : Z := 576.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition RWp (C : rsc) (MA : Z) (w : rsw) : Prop :=
  let P := c_P C in let E := c_E C in let N := c_N C in let LBin := c_LBin C in let SP := c_SP C in
  let d := w_d w in let LB := ps_LBn d ++ LBin in let c := ps_c d in let h := ps_h d in let es := ps_es d in let FB := w_FB w in
  let R := zlength (w_fds w) + zlength (w_sds w) in
     pcore_ok c
  /\ AFieldsOwn LB (ps_em d) /\ AMBufOwn LB es
  /\ (forall e d', (ps_em d) !! e = Some d' -> forall x s, In (x, s) es -> e + esize d' <= x \/ x + mb_block_size s <= e)
  /\ (pc_state c <= 1 -> hdr_empty h /\ ps_u d = 0) /\ 0 <= ps_u d <= 1
  /\ mb_cap es <= 3 * ps_insz d + 512 /\ Z.of_nat (length es) <= KB /\ 0 <= ps_insz d
  /\ (pc_state c = 3 \/ pc_state c = 4 \/ pc_state c = 9 -> 1 <= pc_len c)
  /\ hdr_disj (ps_L d) es h /\ (pc_state c < 10 -> pc_hlim c <= 8192) /\ pc_skip c < 2^62
  /\ lbn_ownedP (ps_L d) h es (w_PB w) /\ Permutation (ps_LBn d) (w_PB w ++ w_FBB w) /\ fbb_ok FB (w_FBB w)
  (* [comment removed for export] *)
  /\ (forall e, e ∈ ps_L d -> blk_fresh H LBin SP e 48)
  /\ (forall x s, In (x, s) es -> blk_fresh H LBin SP x (24 + s))
  /\ (hv_tl h <> 0 -> blk_fresh H LBin SP (hv_tp h) (hv_tl h)) /\ (hv_ml h <> 0 -> blk_fresh H LBin SP (hv_mp h) (hv_ml h))
  /\ (FB <> FB_empty -> blk_fresh H LBin SP (fb_begin FB) (fb_cap FB))
  (* [comment removed for export] *)
  /\ (FB <> FB_empty -> forall e, e ∈ ps_L d -> e + 48 <= fb_begin FB \/ fb_end FB <= e)
  /\ (FB <> FB_empty -> forall x s, In (x, s) es -> x + 24 + s <= fb_begin FB \/ fb_end FB <= x)
  /\ (FB <> FB_empty -> hv_tl h <> 0 -> hv_tp h + hv_tl h <= fb_begin FB \/ fb_end FB <= hv_tp h)
  /\ (FB <> FB_empty -> hv_ml h <> 0 -> hv_mp h + hv_ml h <= fb_begin FB \/ fb_end FB <= hv_mp h)
  /\ ps_off d P PARSER_SIZE /\ ps_off d E 24
  (* [comment removed for export] *)
  /\ ((N = 0 /\ w_Fs w = FB_empty) \/ (1 <= N /\ fb_begin (w_Fs w) = c_A C /\ fb_end (w_Fs w) = c_A C + N))
  /\ zlength (w_fds w) + zlength (w_sds w) <= N /\ 0 <= w_nr w /\ fb_cap FB <= CAPMAX N
  (* [comment removed for export] *)
  /\ lb_bytes LB + 17 * pc_hlim c + body_res es (ps_insz d) R
       + (if pc_state c <=? 9 then 34 else 0) + (2 * CAPMAX N - lb_bytes (w_FBB w)) <= c_MX C
  /\ 4 * Z.of_nat (length LB) + pc_hlim c + 4 * (KB - Z.of_nat (length es))
       + (if pc_state c <=? 1 then 8 else 0) + (if pc_state c <=? 9 then 2 else 0) + 4 * (2 - Z.of_nat (length (w_FBB w))) <= 4 * c_CX C
  /\ ps_insz d + R <= 2^26
  /\ 0 <= ps_A d
  /\ ps_A d + 17 * pc_hlim c + body_res es (ps_insz d) R + (if pc_state c <=? 9 then 34 else 0) + fb_res N (fb_cap FB) <= MA.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rs_done (C : rsc) (MA MR : Z) (sp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v ra : word) (fr : list cell) (M0 : Z)
    (cf : config) : Prop :=
  exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) (w : rsw) (s : as_St H) (errv : word) (E : ecv) (tot : Z)
         (XS : list (Z * Z)),
    as_VIS H s (cfg_ms cf) = MS (mkR ra sp (c_gp C) (c_tp C) t0 t1 t2 s0v s1v (wz tot) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3 t4 t5 t6)
                              (c_F C) (ret_pc ra) (c_fc C) None m (seg_rom asegs)
    /\ as_AKREL H s cf /\ as_MPRES H (c_mo0 C) (cfg_model cf)
    /\ RWm C w s errv E m /\ RWp C MA w /\ al_ok H s (ps_A (w_d w)) MA MR
    /\ stk asegs m (c_lo C) (bv_unsigned sp)
    /\ rw_cells asegs m (bv_unsigned sp) fr
    /\ Forall (fs_scratch H (c_LF C)) XS
    /\ xpres H (c_LBin C) (c_SP C) (hread_X (c_P C) (c_E C) (c_fb C) (c_stb C) [] [] ++ XS) (c_m0 C) m
    /\ 0 <= tot /\ tot + zlength (w_fds w) + zlength (w_sds w) <= c_N C
    /\ ec_ok E /\ (E = EC_clear \/ http_fail E)
    /\ wM (c_N C) w <= M0
    /\ (E = EC_clear -> pc_state (ps_c (w_d w)) <> 11 -> wM (c_N C) w < M0 /\ w_nr w <= c_N C - zlength (w_sds w)).

Definition hread_stmt (MA MR : Z) : Prop :=
  forall (C : rsc) (ra sp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (msF : machine_state) (m : mem) (mo : Model) (fr : list cell) (w : rsw) (s : as_St H) (errv : word) (E : ecv) (XS : list (Z * Z)),
    as_VIS H s msF = MS (mkR ra sp (c_gp C) (c_tp C) t0 t1 t2 s0 s1 (wz (c_bs C)) (wz (c_fb C)) (wz (c_P C)) (wz (c_E C)) a4 a5 a6 a7
                             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        (c_F C) (Z_to_bv 64 P_A_HTTP_READ_SOME) (c_fc C) None m (seg_rom asegs) ->
    rs_static C -> rs_placed C (bv_unsigned sp) ->
    pc_state (ps_c (w_d w)) <> 11 ->
    RWm C w s errv E m -> RWp C MA w -> al_ok H s (ps_A (w_d w)) MA MR ->
    stk asegs m (c_lo C) (bv_unsigned sp) -> rw_cells asegs m (bv_unsigned sp) fr -> Z.of_nat (cells_size fr) = 128 ->
    Forall (fs_scratch H (c_LF C)) XS ->
    xpres H (c_LBin C) (c_SP C) (hread_X (c_P C) (c_E C) (c_fb C) (c_stb C) [] [] ++ XS) (c_m0 C) m ->
    w_nr w <= c_N C - zlength (w_sds w) ->
    as_AKREL H s (mkCfg msF mo) -> as_MPRES H (c_mo0 C) mo ->
    bv_unsigned ra mod 2 = 0 ->
    as_SR H (rs_done C MA MR sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra fr (wM (c_N C) w)) (mkCfg msF mo).

End HCW.
