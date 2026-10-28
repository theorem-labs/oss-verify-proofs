(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image ZBridge Arr.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition huf_reg_post (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPV DST dcap RLO RHI lo fr : Z) (extra : list (Z * Z)) (m : fmem) (Q : fmem -> Z -> Prop) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' r,
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch ((DST, DST + dcap) :: extra ++ [(SPV - fr, SPV)]) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo SPV /\ stk usegs m' RLO RHI
    /\ (r = dcap \/ zd_is_error r = true) /\ 0 <= r < 2^64 /\ Q m' r.

(* [comment removed for export] *)
Definition huf_reg_pre (m : fmem) (SPV lo fr RLO RHI DST dcap SRC n : Z) (src : list byte) : Prop :=
  mem_inv usegs m /\
  stk usegs m lo SPV /\ 4096 <= lo /\ lo <= SPV - fr /\ SPV < 2^47 /\
  stk usegs m RLO RHI /\ RLO <= DST /\ DST + dcap <= RHI /\ 4096 <= DST /\ 0 <= dcap < 2^32 /\ RHI < 2^47 /\
  bytes_at usegs m SRC src /\ zlen src = n /\ 4096 <= SRC /\ n < 2^32 /\ SRC + n < 2^47 /\
  (RHI <= lo \/ SPV <= RLO) /\ (SRC + n <= lo \/ SPV <= SRC) /\ (RHI <= SRC \/ SRC + n <= RLO) /\ SPV mod 16 = 0.

Lemma huf_using_reg : forall ENTRY fr, 0 <= fr -> huf_using_stmt_at ENTRY fr ->
  forall (ra gp tp t0 t1 t2 s0 s1 flags a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SPV DST dcap SRC n DT lo RLO RHI : Z) (src dtb : list byte),
  huf_reg_pre m SPV lo fr RLO RHI DST dcap SRC n src ->
  bytes_at usegs m DT dtb -> zlen dtb = HUF_DTABLE_BYTES -> 4096 <= DT -> DT + HUF_DTABLE_BYTES < 2^47 -> DT mod 4 = 0 ->
  (DT + HUF_DTABLE_BYTES <= lo \/ SPV <= DT) -> (RHI <= DT \/ DT + HUF_DTABLE_BYTES <= RLO) -> huf_tbl_ok dtb ->
  evt usegs (huf_reg_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap RLO RHI lo fr [] m huf_noQ)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DST) (Z_to_bv 64 dcap) (Z_to_bv 64 SRC) (Z_to_bv 64 n)
               (Z_to_bv 64 DT) flags a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ENTRY) fc None m (seg_rom usegs)).
Proof.
  intros ENTRY fr FR0 H. intros until dtb.
  intros (MI & STK & LO0 & LOS & SPH & REG & RL & RH & DL & DC & RHH & SRCB & SLEN & SRCL & NR & SRCH & RSTK & SSTK & RSRC & SP16) DTB DTL DT0 DTH DTA DTSTK RDT TOK.
  destruct (stk_split usegs m RLO DST RHI REG ltac:(lia)) as [Ra R2]. destruct (stk_split usegs m DST (DST + dcap) RHI R2 ltac:(lia)) as [Rm Rb].
  eapply evt_mono.
  - eapply (H ra gp tp t0 t1 t2 s0 s1 flags a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SPV DST dcap SRC n DT lo src dtb).
    + unfold huf_dec_pre. repeat (split; [first [assumption | lia]|]). lia.
    + unfold huf_dt_pre. repeat (split; [first [assumption | lia]|]). lia.
    + exact TOK.
  - intros ms' (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & r & -> & MU & WM & MI' & STK' & Rm' & RES & RNG & QQ).
    unfold huf_reg_post. do 14 eexists. exists m', r.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact STK'|].
    split; [|split; [exact RES | split; [exact RNG | exact QQ]]].
    cbn [app] in MU.
    assert (Ra' : stk usegs m' RLO DST) by (eapply stk_transport_disjoint; [exact Ra | exact MU | exact WM | cbn [disjoint_from]; repeat split; lia]).
    assert (Rb' : stk usegs m' (DST + dcap) RHI) by (eapply stk_transport_disjoint; [exact Rb | exact MU | exact WM | cbn [disjoint_from]; repeat split; lia]).
    eapply stk_merge; [eapply stk_merge; [exact Ra' | exact Rm' | lia] | exact Rb' | lia].
Qed.

Lemma huf_wksp_reg : forall ENTRY fr, 0 <= fr -> huf_wksp_stmt_at ENTRY fr ->
  forall (ra gp tp t0 t1 t2 s0 s1 flags s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SPV DST dcap SRC n DT WK wksz lo RLO RHI : Z) (src dtb : list byte),
  huf_reg_pre m SPV lo fr RLO RHI DST dcap SRC n src ->
  u8arr usegs m DT dtb -> huf_hdr_ok dtb -> 4096 <= DT -> DT + HUF_DTABLE_BYTES < 2^47 -> DT mod 4 = 0 ->
  stk usegs m WK (WK + wksz) -> 4096 <= WK -> 0 <= wksz < 2^32 -> WK + wksz < 2^47 -> WK mod 4 = 0 ->
  (DT + HUF_DTABLE_BYTES <= lo \/ SPV <= DT) -> (WK + wksz <= lo \/ SPV <= WK) ->
  (RHI <= DT \/ DT + HUF_DTABLE_BYTES <= RLO) -> (RHI <= WK \/ WK + wksz <= RLO) ->
  (DT + HUF_DTABLE_BYTES <= WK \/ WK + wksz <= DT) ->
  (DT + HUF_DTABLE_BYTES <= SRC \/ SRC + n <= DT) -> (WK + wksz <= SRC \/ SRC + n <= WK) ->
  evt usegs (huf_reg_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap RLO RHI lo fr
               [(DT, DT + HUF_DTABLE_BYTES); (WK, WK + wksz)] m
               (fun m' r => huf_built DT m' r /\ stk usegs m' WK (WK + wksz)))
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DT) (Z_to_bv 64 DST) (Z_to_bv 64 dcap) (Z_to_bv 64 SRC)
               (Z_to_bv 64 n) (Z_to_bv 64 WK) (Z_to_bv 64 wksz) flags s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ENTRY) fc None m (seg_rom usegs)).
Proof.
  intros ENTRY fr FR0 H. intros until dtb.
  intros (MI & STK & LO0 & LOS & SPH & REG & RL & RH & DL & DC & RHH & SRCB & SLEN & SRCL & NR & SRCH & RSTK & SSTK & RSRC & SP16)
         DTU HOK DT0 DTH DTA WKS WK0 WKZ WKH WKA DTSTK WKSTK RDT RWK DTWK DTSRC WKSRC.
  destruct (stk_split usegs m RLO DST RHI REG ltac:(lia)) as [Ra R2]. destruct (stk_split usegs m DST (DST + dcap) RHI R2 ltac:(lia)) as [Rm Rb].
  eapply evt_mono.
  - eapply (H ra gp tp t0 t1 t2 s0 s1 flags s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SPV DST dcap SRC n DT WK wksz lo src dtb);
      try assumption; try lia.
    unfold huf_dec_pre. repeat (split; [first [assumption | lia]|]). lia.
  - intros ms' (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & r & -> & MU & WM & MI' & STK' & Rm' & RES & RNG & QQ).
    unfold huf_reg_post. do 14 eexists. exists m', r.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact STK'|].
    split; [|split; [exact RES | split; [exact RNG | exact QQ]]].
    cbn [app] in MU.
    assert (Ra' : stk usegs m' RLO DST) by (eapply stk_transport_disjoint; [exact Ra | exact MU | exact WM | cbn [disjoint_from]; repeat split; lia]).
    assert (Rb' : stk usegs m' (DST + dcap) RHI) by (eapply stk_transport_disjoint; [exact Rb | exact MU | exact WM | cbn [disjoint_from]; repeat split; lia]).
    eapply stk_merge; [eapply stk_merge; [exact Ra' | exact Rm' | lia] | exact Rb' | lia].
Qed.
