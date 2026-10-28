(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem huf_1x1_wksp_proof : huf_rdx1_stmt -> huf_1x1_stmt -> huf_1x1_wksp_stmt.
Proof.
  intros RDX1 H1X1.
  unfold huf_1x1_wksp_stmt, huf_wksp_stmt_at, PHUF_1X1_WKSP, HUF_1X1W_STACK, HUF_TBL_STACK.
  unfold huf_rdx1_stmt, huf_rd_stmt_at, PHUF_RDX1, HUF_TBL_STACK in RDX1.
  unfold huf_1x1_stmt, huf_int_stmt_at, PHUF_1X1, HUF_1X_STACK in H1X1.
  intros until dtb.
  intros (MI & STK & LO0 & LO & SPB & OUT & D0 & D1 & D2 & SRCB & SL & S0 & S1 & S2 & OS1 & OS2 & DJ1 & SP16)
         UT HDR T0 T1 TA WKS W0 W1 W2 WA OSD OSW DJD DJW DJTW DJTS DJWS.
  unfold HUF_DTABLE_BYTES in *.
  assert (MU : munch [(DST, DST + dcap); (DT, DT + 16388); (WK, WK + wksz); (SPV - 1072, SPV)] m m) by apply munch_refl.
  assert (WM : wmono usegs m m) by apply wmono_refl.
  pose proof HDR as (DL & _). unfold HUF_DTABLE_BYTES in DL.
  carve_frame 48%nat STK.
  kx_autoLx [] 40%nat
    [KZRange SPV 4096 (2^47); KZWr (SPV - 48) 48; KZRange DT 4096 (2^47); KZRange SRC 4096 (2^47); KZRange n 0 (2^32);
     KZRange WK 4096 (2^47); KZRange wksz 0 (2^32); KZRange DST 4096 (2^47); KZRange dcap 0 (2^32);
     KZDisj (SPV - 48) 48 DT 16388; KZDisj (SPV - 48) 48 SRC n; KZDisj (SPV - 48) 48 WK wksz; KZDisj (SPV - 48) 48 DST dcap]
    (@nil (Z * Z)).
  kx_mem.
  eapply evt_cut; [eapply RDX1 | unfold huf_rd_post, HUF_DTABLE_BYTES, HUF_TBL_STACK; post_call usegs m0].
  all: try eassumption; try lia.
  rename x14 into r. rename x15 into dtb'. rename x13 into m1.
  kx_autoLx [0x20814] 40%nat
    [KZRange SPV 4096 (2^47); KZRange r 0 (2^64 - 1); KZRange n 0 (2^32); KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47)] [(SPV - 48, 48)].
  all: lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x207f4) _ _ _ _) => kx_trap_fast | _ => idtac end.
  1: zstep.
  1: release_frame FR PC SPV.
  1: apply evt_done; unfold huf_dec_post; repeat (lazymatch goal with |- ex _ => eexists end).
  1: (split; [reflexivity|]); (split; [exact MU|]); (split; [exact WM|]); (split; [exact KXMI|]); (split; [exact PC|]); (split; [exact OUT|]).
  1: assert (ER : zd_is_error r = true) by (unfold zd_is_error, ZE_maxCode; apply Z.ltb_lt; lia).
  1: split; [right; exact ER | split; [lia | split; [exists dtb'; split; [exact PC1 | split; [exact PC2 | intro NE; rewrite ER in NE; discriminate NE]] | exact PC0]]].
  1: zstep.
  1: release_frame FR PC SPV.
  1: apply evt_done; unfold huf_dec_post; repeat (lazymatch goal with |- ex _ => eexists end).
  1: (split; [reflexivity|]); (split; [exact MU|]); (split; [exact WM|]); (split; [exact KXMI|]); (split; [exact PC|]); (split; [exact OUT|]).
  1: split; [right; vm_compute; reflexivity | split; [lia | split; [exists dtb'; split; [exact PC1 | split; [exact PC2 | intro NE; vm_compute in NE; discriminate NE]] | exact PC0]]].
  release_frame FR PC SPV.
  assert (NE : zd_is_error r = false) by (unfold zd_is_error, ZE_maxCode; apply Z.ltb_ge; lia).
  destruct (POST NE) as ((_ & ty & tl & TY & TLB & TLR & _ & NB) & ty' & TY' & TYZ).
  rewrite TY in TY'. injection TY' as <-.
  assert (TY0 : bv_unsigned ty = 0) by (destruct (Z.eq_dec (bv_unsigned ty) 0) as [Z0|NZ]; [exact Z0 | apply TYZ in NZ; discriminate NZ]).
  rewrite TY0 in NB. change (negb (0 =? 0)) with false in NB.
  assert (SRC' : bytes_at usegs m1 (r + SRC) (skipn (Z.to_nat r) src)).
  { pose proof SRCB as SB. rewrite <- (firstn_skipn (Z.to_nat r) src) in SB. apply bytes_at_app in SB as [_ SB].
    rewrite length_firstn, Nat.min_l in SB by lia. rewrite Z2Nat.id in SB by lia. replace (r + SRC) with (SRC + r) by lia. exact SB. }
  assert (SL' : zlen (skipn (Z.to_nat r) src) = -1 * r + n) by (rewrite length_skipn; lia).
  eapply evt_mono.
  { eapply (H1X1 ra gp tp x x0 x1 s0 s1 x6 x7 x8 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x9 x10 x11 x12 F fc m1 SPV DST dcap (r + SRC) (-1 * r + n) DT tl lo
                  (skipn (Z.to_nat r) src) dtb').
    - unfold huf_dec_pre. repeat (split; [first [assumption | lia]|]); first [assumption | lia].
    - unfold huf_dt_pre, HUF_DTABLE_BYTES. destruct PC1 as [PB _]. destruct PC2 as [PL _]. unfold HUF_DTABLE_BYTES in PL.
      repeat (split; [first [assumption | lia]|]); first [assumption | lia].
    - exact TLB.
    - exact TLR.
    - intro X; discriminate X.
    - exact NB. }
  intros ms' PO. unfold huf_dec_post in *.
  destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & m2 & r2 & E & MU2 & WM2 & MI2 & STK2 & OUT2 & R2 & RG2 & _).
  exists y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, m2, r2.
  split; [exact E|].
  split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU2]. unfold sub_fp; cbn [outside app]; intros; lia. }
  split; [eapply wmono_trans; eassumption|].
  split; [exact MI2|]. split; [exact STK2|]. split; [exact OUT2|]. split; [exact R2|]. split; [exact RG2|].
  split.
  - exists dtb'. split; [|split; [exact PC2 | intros _; exact (proj1 (POST NE))]].
    destruct PC2 as [PL _]. unfold HUF_DTABLE_BYTES in PL.
    eapply (u8arr_transport usegs _ m1 m2 DT dtb' PC1 MU2 WM2). cbn [disjoint_from app]. rewrite PL. lia.
  - eapply (stk_transport_disjoint usegs _ m1 m2 WK (WK + wksz) PC0 MU2 WM2). cbn [disjoint_from app]. lia.
Qed.

(* [comment removed for export] *)
Ltac wk_after_call FRSZ WTOT TAILPC HINT x2 r dtb' m1 src FR PC PC0 PC1 PC2 POST MU WM OUT SRCB :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 TAILPC) _ _ _ _) =>
      lazymatch goal with
      | |- evt _ (huf_dec_post ?ra ?gp ?tp ?s0 ?s1 ?s2 ?s3 ?s4 ?s5 ?s6 ?s7 ?s8 ?s9 ?s10 ?s11 ?F ?fc ?SPV ?DST ?dcap ?lo _ _ ?m _)
               (MS (mkR _ _ _ _ ?x5 ?x6 ?x7 _ _ _ _ (Z_to_bv 64 (r + ?SRC)) (Z_to_bv 64 (-1 * r + ?n)) (Z_to_bv 64 ?DT) ?x15 ?x16 ?x17
                        _ _ _ _ _ _ _ _ _ _ ?x28 ?x29 ?x30 ?x31) _ _ _ _ _ _) =>
          release_frame FR PC SPV;
          let NE := fresh "NE" in
          assert (NE : zd_is_error r = false) by (unfold zd_is_error, ZE_maxCode; apply Z.ltb_ge; lia);
          let ty := fresh "ty" in let tl := fresh "tl" in let TY := fresh "TY" in let TLB := fresh "TLB" in let TLR := fresh "TLR" in
          let X2 := fresh "X2" in let NB := fresh "NB" in let ty' := fresh "ty'" in let TY' := fresh "TY'" in let TYZ := fresh "TYZ" in
          destruct (POST NE) as ((_ & ty & tl & TY & TLB & TLR & X2 & NB) & ty' & TY' & TYZ);
          rewrite TY in TY'; injection TY' as <-;
          let SRC' := fresh "SRC'" in let SL' := fresh "SL'" in
          assert (SRC' : bytes_at usegs m1 (r + SRC) (skipn (Z.to_nat r) src))
            by (let SB := fresh "SB" in pose proof SRCB as SB; rewrite <- (firstn_skipn (Z.to_nat r) src) in SB;
                apply bytes_at_app in SB as [_ SB]; rewrite length_firstn, Nat.min_l in SB by lia; rewrite Z2Nat.id in SB by lia;
                replace (r + SRC) with (SRC + r) by lia; exact SB);
          assert (SL' : zlen (skipn (Z.to_nat r) src) = -1 * r + n) by (rewrite length_skipn; lia);
          eapply evt_mono;
          [ eapply (HINT ra gp tp x5 x6 x7 s0 s1 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 F fc m1 SPV DST dcap
                         (r + SRC) (-1 * r + n) DT tl lo (skipn (Z.to_nat r) src) dtb');
            [ unfold huf_dec_pre; repeat (split; [first [assumption | lia]|]); first [assumption | lia]
            | unfold huf_dt_pre, HUF_DTABLE_BYTES; destruct PC1 as [? _]; destruct PC2 as [? _]; unfold HUF_DTABLE_BYTES in *;
              repeat (split; [first [assumption | lia]|]); first [assumption | lia]
            | exact TLB | exact TLR
            | lazymatch x2 with
              | true => intros _; apply X2; apply (proj2 TYZ); reflexivity
              | false => let X := fresh "X" in intro X; discriminate X
              end
            | lazymatch x2 with
              | true => assert (TZ : (bv_unsigned ty =? 0) = false) by (apply Z.eqb_neq; apply (proj2 TYZ); reflexivity);
                        rewrite TZ in NB; exact NB
              | false => assert (TZ : bv_unsigned ty = 0)
                           by (destruct (Z.eq_dec (bv_unsigned ty) 0) as [Z0|NZ]; [exact Z0 | apply TYZ in NZ; discriminate NZ]);
                         rewrite TZ in NB; exact NB
              end ]
          | let ms' := fresh "ms'" in let PO := fresh "PO" in
            intros ms' PO; unfold huf_dec_post in *;
            destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & m2 & r2 & E & MU2 & WM2 & MI2 & STK2 & OUT2 & R2 & RG2 & _);
            exists y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, m2, r2;
            split; [exact E|];
            split; [eapply munch_trans; [exact MU|]; eapply munch_weaken; [|exact MU2]; unfold sub_fp, HUF_4X_STACK; cbn [outside app]; intros; lia|];
            split; [eapply wmono_trans; eassumption|];
            split; [exact MI2|]; split; [exact STK2|]; split; [exact OUT2|]; split; [exact R2|]; split; [exact RG2|];
            split;
            [ exists dtb'; split; [|split; [exact PC2 | intros _; exact (proj1 (POST NE))]];
              destruct PC2 as [PL _]; unfold HUF_DTABLE_BYTES in PL;
              eapply (u8arr_transport usegs _ m1 m2 DT dtb' PC1 MU2 WM2); unfold HUF_4X_STACK; cbn [disjoint_from app]; rewrite PL; lia
            | eapply (stk_transport_disjoint usegs _ m1 m2 _ _ PC0 MU2 WM2); unfold HUF_4X_STACK; cbn [disjoint_from app]; lia ] ]
      end
  | |- evt _ (huf_dec_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?SPV _ _ _ _ _ _ _) _ =>
      zstep; release_frame FR PC SPV;
      apply evt_done; unfold huf_dec_post; repeat (lazymatch goal with |- ex _ => eexists end);
      (split; [reflexivity|]); (split; [exact MU|]); (split; [exact WM|]); (split; [assumption|]); (split; [exact PC|]); (split; [exact OUT|]);
      first [ (* [comment removed for export] *)
              split; [right; vm_compute; reflexivity
                     | split; [lia | split; [exists dtb'; split; [exact PC1 | split; [exact PC2 | let NE := fresh "NE" in intro NE; vm_compute in NE; discriminate NE]] | exact PC0]]]
            | (* [comment removed for export] *)
              let ER := fresh "ER" in
              assert (ER : zd_is_error r = true) by (unfold zd_is_error, ZE_maxCode; apply Z.ltb_lt; lia);
              split; [right; exact ER
                     | split; [lia | split; [exists dtb'; split; [exact PC1 | split; [exact PC2 | let NE := fresh "NE" in intro NE; rewrite ER in NE; discriminate NE]] | exact PC0]]] ]
  end.

(* [comment removed for export] *)
Ltac wk_arm RDX TAILPC HINT x2 FRSZ WTOT lo WK src FR MU WM OUT SRCB :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
      (eapply evt_cut; [eapply RDX | unfold huf_rd_post, HUF_DTABLE_BYTES, HUF_TBL_STACK; post_call segs mm]); try eassumption; try lia
  end;
  lazymatch goal with
  | PC : stk usegs ?m1 lo _, PC0 : stk usegs ?m1 WK _, PC1 : u8arr usegs ?m1 _ ?dtb', PC2 : huf_hdr_ok ?dtb',
    PC3 : 0 <= ?r < 2^64, POST : zd_is_error ?r = false -> _ |- _ =>
      lazymatch goal with
      | |- evt _ (huf_dec_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?SPV _ _ _ _ _ _ _) _ =>
          lazymatch type of SRCB with bytes_at _ _ ?S ?sb => lazymatch goal with SLx : zlen sb = ?nn |- _ =>
          kx_autoLx [TAILPC] 40%nat [KZRange SPV 4096 (2^47); KZRange r 0 (2^64 - 1); KZRange S 4096 (2^47); KZRange nn 0 (2^32);
                                     KZRange (S + nn) 4096 (2^47)] [(SPV - FRSZ, FRSZ)] end end;
          lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x255f8) _ _ _ _) => kx_trap_fast | _ => idtac end;
          wk_after_call FRSZ WTOT TAILPC HINT x2 r dtb' m1 src FR PC PC0 PC1 PC2 POST MU WM OUT SRCB
      end
  end.

Theorem huf_4x_wksp_proof : huf_rdx1_stmt -> huf_rdx2_stmt -> huf_4x1_stmt -> huf_4x2_stmt -> huf_4x_wksp_stmt.
Proof.
  intros RDX1 RDX2 H4X1 H4X2.
  unfold huf_4x_wksp_stmt, huf_wksp_stmt_at, PHUF_4X_WKSP, HUF_4XW_STACK, HUF_TBL_STACK.
  unfold huf_rdx1_stmt, huf_rdx2_stmt, huf_rd_stmt_at, PHUF_RDX1, PHUF_RDX2, HUF_TBL_STACK in RDX1, RDX2.
  unfold huf_4x1_stmt, huf_4x2_stmt, huf_int_stmt_at, PHUF_4X1, PHUF_4X2, HUF_4X_STACK in H4X1, H4X2.
  intros until dtb.
  intros (MI & STK & LO0 & LO & SPB & OUT & D0 & D1 & D2 & SRCB & SL & S0 & S1 & S2 & OS1 & OS2 & DJ1 & SP16)
         UT HDR T0 T1 TA WKS W0 W1 W2 WA OSD OSW DJD DJW DJTW DJTS DJWS.
  unfold HUF_DTABLE_BYTES in *.
  assert (MU : munch [(DST, DST + dcap); (DT, DT + 16388); (WK, WK + wksz); (SPV - 1088, SPV)] m m) by apply munch_refl.
  assert (WM : wmono usegs m m) by apply wmono_refl.
  pose proof HDR as (DL & _). unfold HUF_DTABLE_BYTES in DL.
  carve_frame 64%nat STK.
  (* [comment removed for export] *)
  assert (CONT : forall mm Q (jk : list byte) (x6 x7 : word),
     mem_inv usegs mm -> munch [(DST, DST + dcap); (DT, DT + 16388); (WK, WK + wksz); (SPV - 1088, SPV)] m mm -> wmono usegs m mm ->
     rw_cells usegs mm (SPV + -64) [CB 8 jk; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
     stk usegs mm lo (SPV + -64) -> stk usegs mm DST (DST + dcap) -> bytes_at usegs mm SRC src ->
     u8arr usegs mm DT dtb -> stk usegs mm WK (WK + wksz) -> 0 <= Q <= 15 ->
     evt usegs (huf_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo (64 + 1024)
                  [(DT, DT + 16388); (WK, WK + wksz)] m (fun m' r => huf_built DT m' r /\ stk usegs m' WK (WK + wksz)))
       (MS (mkR ra (Z_to_bv 64 (SPV + -64)) gp tp (Z_to_bv 64 Q) x6 x7 s0 s1 (Z_to_bv 64 DT) (Z_to_bv 64 DST) (Z_to_bv 64 dcap)
                (Z_to_bv 64 SRC) (Z_to_bv 64 n) (Z_to_bv 64 WK) (Z_to_bv 64 wksz) flags s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x25474) fc None mm (seg_rom usegs))).
  { clear MI STK OUT SRCB UT WKS MU WM FR junk.
    intros mm Q jk x6 x7 MI MU WM FR STK OUT SRCB UT WKS HQ.
    kx_autoLx [] 60%nat
      [KZRange Q 0 15; KZRange SPV 4096 (2^47); KZRange DT 4096 (2^47); KZRange SRC 4096 (2^47); KZRange n 0 (2^32);
      KZRange WK 4096 (2^47); KZRange wksz 0 (2^32); KZRange DST 4096 (2^47); KZRange dcap 0 (2^32); KZImg 0x10000 0x14000]
      [(0x11110, 256)].
    all: lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x255f8) _ _ _ _) => kx_trap_fast | _ => idtac end.
    - Time wk_arm RDX1 0x22194 H4X1 false 64 1088 lo WK src FR MU WM OUT SRCB.
    - Time wk_arm RDX2 0x20d94 H4X2 true 64 1088 lo WK src FR MU WM OUT SRCB. }
  kx_autoLx [0x25474; 0x25458] 80%nat
    [KZRange SPV 4096 (2^47); KZWr (SPV - 64) 64; KZRange DT 4096 (2^47); KZRange SRC 4096 (2^47); KZRange n 0 (2^32);
     KZRange WK 4096 (2^47); KZRange wksz 0 (2^32); KZRange DST 4096 (2^47); KZRange dcap 0 (2^32);
     KZDisj (SPV - 64) 64 DT 16388; KZDisj (SPV - 64) 64 SRC n; KZDisj (SPV - 64) 64 WK wksz; KZDisj (SPV - 64) 64 DST dcap;
    KZImg 0x10000 0x14000]
    (@nil (Z * Z)).
  all: lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x255f8) _ _ _ _) => kx_trap_fast | _ => idtac end.
  all: lazymatch goal with
       | |- evt _ _ (MS _ _ (Z_to_bv 64 0x25474) _ _ _ _) => kx_mem; eapply CONT; try eassumption; lia
       | |- evt _ _ (MS _ _ (Z_to_bv 64 0x25458) _ _ _ _) => idtac
       | _ => kx_mem; wk_after_call 64 1088 0 H4X1 false 0 dtb m src FR STK WKS UT HDR I MU WM OUT SRCB
       end.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
    lazymatch goal with
    | KXA : atoms_ok ?zs ?E |- context [bv_unsigned (edenot ?E (EMd M_DIVU ?a ?b))] =>
        let nz := kx_len zs in let ua := kx_uz E zs nz a in let ub := kx_uz E zs nz b in
        assert (HD : bv_unsigned (edenot E (EMd M_DIVU a b)) = ua / ub)
          by (change (edenot E (EMd M_DIVU a b)) with (mul_div M_DIVU (edenot E a) (edenot E b)); rewrite u_divu64;
              [ rewrite (uz_sound zs E a KXA), (uz_sound zs E b KXA); reflexivity
              | rewrite (uz_sound zs E b KXA); change (0 < ub); kx_lia ])
    end.
    rewrite HD. rewrite (Z.mod_small (16 * n) (2^64)), (Z.mod_small dcap (2^64)) by lia.
    assert (DQ : 0 <= 16 * n / dcap <= 15)
      by (split; [apply Z.div_pos; lia | apply Z.lt_succ_r; apply Z.div_lt_upper_bound; lia]).
    set (dq := 16 * n / dcap) in *.
    kx_autoLx [0x25474] 20%nat
      [KZRange dq 0 15; KZRange SPV 4096 (2^47); KZRange DT 4096 (2^47); KZRange SRC 4096 (2^47); KZRange n 0 (2^32);
       KZRange WK 4096 (2^47); KZRange wksz 0 (2^32); KZRange DST 4096 (2^47); KZRange dcap 0 (2^32)]
      (@nil (Z * Z)).
    all: lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x255f8) _ _ _ _) => kx_trap_fast | _ => idtac end.
    all: kx_mem; eapply CONT; try eassumption; clear - DQ; lia.
Qed.
