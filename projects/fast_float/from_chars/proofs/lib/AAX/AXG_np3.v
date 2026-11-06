(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require Import AxAsan AXG_put AXG_put2 AXG_np AXG_np2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require Import AXG_npscp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXF_np0z.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXF_np0z.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.

Definition KCALLEE : list nat := [1; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.

Lemma grows_wb : forall m m' a bs, mem_grows m m' -> mem_grows m (wbytes m' a bs).
Proof. intros m m' a bs H. eapply mem_grows_trans; [exact H | apply wbytes_grows]. Qed.
Ltac growsc := repeat apply grows_wb; apply mem_grows_refl.
Lemma addneg : forall x p, x + Zneg p = x - Zpos p.
Proof. reflexivity. Qed.
Lemma stk_ok_grows : forall m m' sp K, mem_grows m m' -> stk_ok SEGS m sp K -> stk_ok SEGS m' sp K.
Proof. intros m m' sp K G H a n H1 H2. apply (store_ok_mono SEGS n m m' _ G). apply H; assumption. Qed.
Ltac rgz := replace (Z_to_bv 5 (Z.of_nat 2)) with (@BV 5 2 I) in * by (apply bv_eq; reflexivity).
Ltac kcin Hk := clear - Hk; cbn [KCALLEE In] in Hk; repeat (destruct Hk as [<-|Hk]; [cbn [In]; memb|]); destruct Hk.

Section NP.
Context {fx : FPState}.
Variable rom : word -> option byte.
Variables (m : word -> option byte) (regs : bvmap 5 word) (CA ND c SB sz nc newc j SP : Z).
Hypothesis Hc : c = (ND + 31) / 32.
Hypothesis I : INV_C m CA SB c sz nc newc j.
Hypothesis Hj : j + 1 + nc <= newc.
Hypothesis HND : 33 <= ND <= 512.
Hypothesis H2 : getr regs 2 = wa SP.
Hypothesis HSP : 2^46 + 4096 <= SP <= 2^47 /\ SP mod 16 = 0.
Hypothesis HSTK : stk_ok SEGS m (wa SP) 2048.
Hypothesis H10 : getr regs 10 = wa 923480.
Hypothesis H11 : getr regs 11 = wa CA.
Hypothesis H12 : getr regs 12 = wa ND.
Hypothesis H13 : getr regs 13 = wa 8.
Hypothesis HCA : ((4304 <= CA /\ CA + 3888 <= 65536) \/ 6529232 <= CA) /\ CA mod 16 = 0 /\ CA + 2592 <= SP - 2048.
Hypothesis HSB : 4194304 <= SB /\ SB mod 4096 = 0 /\ SB + 137438953472 + 4096 <= SP - 2048.
Hypothesis HSEP : CA + 2592 <= SB \/ SB + 137438953472 + 4096 <= CA.
Hypothesis HIMG : forall i, 65536 <= i < 143360 -> m (Z_to_bv 64 i) = None.

#[using="ND Hc I Hj HND H2 HSP HSTK H10 H11 H12 H13 HCA HSB HSEP"] Lemma np_pop : 1 <= cnt_of nc j ->
  exists R m', msteps SEGS (mkst regs (wa 0x43ce8) m rom) (mkst R (wa 0x43f08) m' rom) /\
    getr R (Z_to_bv 5 (Z.of_nat 2)) = wa SP /\
    (forall k, In k KCALLEE -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))) /\
    getr R 10 = wa (SB + c * 4294967296 + j * sz) /\
    INV_C m' CA SB c sz nc newc (j + 1) /\
    (forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP) -> ~ owned_C CA SB c x -> m' (wa x) = m (wa x)) /\ mem_grows m m'.
Proof. LiaFast.lf_pins (fun (ND Hc I Hj HND H2 HSP HSTK H10 H11 H12 H13 HCA HSB HSEP : LiaFast.U) => LiaFast.u0).
  intros Hcnt.
  pose proof I as I0. destruct I0 as [Igeo ISB IRIB Icnt Imc Isz Ich Imu Inf Ina Ifa Ist Iwrec Iwri Iwst].
  pose proof (cnt_of_range nc j ltac:(slia) ltac:(slia)) as Hcr.
  set (cnt := cnt_of nc j) in *.
  destruct Ist as (st & Hst & Rst).
  assert (HC5 : Z.shiftr ((ND + 31) mod 2^64) 5 = c) by (rewrite Hc; apply c_of_nd; exact HND).
  pose proof (c_of_nd_range ND HND) as Hcr5. rewrite <- Hc in Hcr5.
  assert (Hsz16 : sz = 16 * (sz / 16)) by (pose proof (Z.div_mod sz 16 ltac:(lia)); slia).
  set (cp := j * (sz / 16)).
  assert (Hcp : 0 <= cp <= 16384).
  { unfold cp. assert (0 <= sz / 16) by (apply Z.div_pos; slia). destruct Igeo as (_ & _ & _ & _ & Hj1 & _ & Hns & _). nia. }
  assert (HSPa : bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 2))) = SP) by (rgz; rewrite H2, u_wa_small by slia; reflexivity).
  assert (P : AXF_np0z.np0_pre regs m CA ND cnt sz cp SB st).
  { constructor; try assumption; try slia.
    - rewrite H2. apply (stk_ok_shrink m (wa SP) 2048 1024); [slia | exact HSTK].
    - rewrite HC5, Z.add_0_r. exact Icnt.
    - intros d k Hd Hk. rewrite HC5, Z.add_0_r. apply Iwrec; slia.
    - rewrite HC5. exact Isz.
    - rewrite HC5, chp_off by slia. replace (CA + (80 * c + 4 * (cnt - 1)) + 16) with (CA + 80 * c + 16 + 4 * (cnt - 1)) by ring.
      pose proof (Ich (cnt - 1) ltac:(slia)) as R7. replace ((j + cnt - 1 - (cnt - 1)) * (sz / 16)) with cp in R7 by (unfold cp; ring). exact R7.
    - intros d k Hd Hk. replace (CA + 2576 + d) with (CA + 2560 + (16 + d)) by ring. apply Iwst; slia. }
  destruct (AXF_np0z.np0_pnp0p regs m rom CA ND cnt sz cp SB st P
              (sc_np0p_p regs m SP CA ND SB HSPa HND ltac:(unfold ca_place; slia) cnt sz cp st ltac:(slia)))
    as (R & Hms & A10 & A11 & A12 & A13 & A14 & A15 & KK).
  set (m' := AXF_np0z.np0_mem_pnp0p m regs CA ND cnt sz cp SB st) in *.
  assert (EM : m' = wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
             (wa (SP - 8)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1)))))))
             (wa (SP - 16)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8)))))))
             (wa (SP - 24)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9)))))))
             (wa (SP - 32)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18)))))))
             (wa (SP - 40)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19)))))))
             (wa (SP - 48)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20)))))))
             (wa (CA + 80 * c)) (word_to_le_bytes 4 (wa (cnt - 1))))
             (wa (CA + 2576)) (word_to_le_bytes 8 (wa (sz + st)))).
  { unfold m', AXF_np0z.np0_mem_pnp0p. rewrite HSPa, HC5, Z.add_0_r, ext_Z_lo32_small by slia. rewrite ?addneg. reflexivity. }
  clearbody m'. subst m'.
  assert (FRM : forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP) -> ~ (CA + 80 * c <= x < CA + 80 * c + 4) -> ~ (CA + 2576 <= x < CA + 2584) ->
            wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
             (wa (SP - 8)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1)))))))
             (wa (SP - 16)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8)))))))
             (wa (SP - 24)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9)))))))
             (wa (SP - 32)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18)))))))
             (wa (SP - 40)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19)))))))
             (wa (SP - 48)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20)))))))
             (wa (CA + 80 * c)) (word_to_le_bytes 4 (wa (cnt - 1))))
             (wa (CA + 2576)) (word_to_le_bytes 8 (wa (sz + st))) (wa x) = m (wa x)).
  { intros x Hx F1 F2 F3. repeat (rewrite wb_other by first [exact Hx | (lenq; slia) | slia]). reflexivity. }
  eexists R, _. split; [exact Hms|].
  split; [rewrite (KK 2%nat ltac:(cbn; tauto)); rgz; exact H2|].
  split; [intros k Hk; apply KK; kcin Hk|].
  split.
  { rewrite A10, HC5, ext_Z_u32 by slia. f_equal. unfold cp. rewrite Hsz16 at 2. ring. }
  assert (G : mem_grows m (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
             (wa (SP - 8)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1)))))))
             (wa (SP - 16)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8)))))))
             (wa (SP - 24)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9)))))))
             (wa (SP - 32)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18)))))))
             (wa (SP - 40)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19)))))))
             (wa (SP - 48)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20)))))))
             (wa (CA + 80 * c)) (word_to_le_bytes 4 (wa (cnt - 1))))
             (wa (CA + 2576)) (word_to_le_bytes 8 (wa (sz + st))))) by growsc.
  split.
  { apply (inv_pop m _ CA SB c sz nc newc j SP I Hj ltac:(slia) ltac:(slia) HSEP G Hcnt FRM).
    - apply wb_rd_other; [slia | lenq; slia | slia | lenq; slia | lenq; slia |]. apply wb_rd_hit; lenq; slia.
    - exists ((sz + st) mod 2^64). split; [apply Z.mod_pos_bound; lia|]. unfold rd.
      rewrite (wa_eqm ((sz + st) mod 2^64) (sz + st)) by (apply Z.mod_mod; lia). apply (wb_rd_hit _ _ 8 (sz + st)); lenq; slia. }
  split; [intros x Hx F1 F2; apply FRM; [exact Hx | exact F1 | unfold owned_C in F2; slia | unfold owned_C in F2; slia] | exact G].
Qed.

End NP.
