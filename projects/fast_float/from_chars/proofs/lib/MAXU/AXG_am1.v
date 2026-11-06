(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3 SeqExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr MallocWfMeta.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGeom OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng MngRepr MngHeap MngWb MngWk MngGeoX MngLt MngSurgery MngExc MngNtfPre MngGM MngCtx2.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AxBits MngZ MngNtfM MngNtfS MngMWP MngMW0 MngMW1.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_eez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_mt1z.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_eez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_eez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_eez.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AxBits OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngZ OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngNtfM OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngNtfS OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngMWP OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngMW0 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngMW1 OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_eez.AXF_mt0z OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_mt1z OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_eez.AXF_mt2z OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_eez.AXF_mtez OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_eez.AXF_mtedz.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma set_init_done_same : forall s, st_init_done s = true -> set_init_done true s = s.
Proof. intros [] H. cbn in H. subst. reflexivity. Qed.

(* [comment removed for export] *)
Definition s_take (s : astate) : astate :=
  upd_meta (st_avail_meta s) MRaw
    (set_avail_meta (padd (st_avail_meta s) META_SIZE) (set_avail_meta_count (st_avail_meta_count s - 1) s)).

Lemma alloc_meta_take : forall s, st_init_done s = true -> st_free_meta_head s = None -> 0 < st_avail_meta_count s ->
  alloc_meta s = IRet (Some (st_avail_meta s), s_take s).
Proof.
  intros s Hi Hf Hc. unfold alloc_meta. cbn. rewrite set_init_done_same by exact Hi. rewrite Hf. cbn.
  replace (0 <? st_avail_meta_count s) with true by (symmetry; apply Z.ltb_lt; exact Hc). cbn. reflexivity.
Qed.

Ltac side := cbn [length word_to_le_bytes Z_to_le_bytes]; (rewrite ?u_wa_small by lia); lia.
Ltac memb := first [ AxSymRun3.memb_refl | repeat first [ (left; reflexivity) | right ] ].      (* [comment removed for export] *)
Ltac litr2 H := match type of H with getr _ ?r = _ => match goal with |- getr _ ?r0 = _ => replace r0 with r by (apply bv_eq; reflexivity) end end; rewrite H.

(* [comment removed for export] *)
Lemma kp_lit : forall (R regs : bvmap 5 word) (l : list nat),
  (forall k, In k l -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))) ->
  forall k r, In k l -> Z_to_bv 5 (Z.of_nat k) = r -> getr R r = getr regs r.
Proof. intros R regs l K k r Hk <-. exact (K k Hk). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record am_frame (R : bvmap 5 word) (m : word -> option byte) (sp0 can ra s0 s1 s2 s3 s4 : Z) : Prop := {
  mf_R2 : getr R 2 = wa (sp0 + -64) ; mf_R18 : getr R 18 = wa 621568 ; mf_R19 : getr R 19 = wa 621712 ;
  mf_Rsp : 2^20 <= sp0 <= 2^47 ; mf_Asp : sp0 mod 16 = 0 ; mf_Rcan : 0 <= can <= 2^64-1 ;
  mf_Rra : 0 <= ra <= 2^64-1 ; mf_Rs0 : 0 <= s0 <= 2^64-1 ; mf_Rs1 : 0 <= s1 <= 2^64-1 ; mf_Rs2 : 0 <= s2 <= 2^64-1 ;
  mf_Rs3 : 0 <= s3 <= 2^64-1 ; mf_Rs4 : 0 <= s4 <= 2^64-1 ;
  mf_Mra : rdn SEGS m (wa (sp0 + -8)) 8 = Some (word_to_le_bytes 8 (wa ra)) ;
  mf_Ms0 : rdn SEGS m (wa (sp0 + -16)) 8 = Some (word_to_le_bytes 8 (wa s0)) ;
  mf_Ms1 : rdn SEGS m (wa (sp0 + -24)) 8 = Some (word_to_le_bytes 8 (wa s1)) ;
  mf_Ms2 : rdn SEGS m (wa (sp0 + -32)) 8 = Some (word_to_le_bytes 8 (wa s2)) ;
  mf_Ms3 : rdn SEGS m (wa (sp0 + -40)) 8 = Some (word_to_le_bytes 8 (wa s3)) ;
  mf_Ms4 : rdn SEGS m (wa (sp0 + -48)) 8 = Some (word_to_le_bytes 8 (wa s4)) ;
  mf_Mcan : rdn SEGS m (wa (sp0 + -56)) 8 = Some (word_to_le_bytes 8 (wa can)) ;
  mf_Mgd : rdn SEGS m (wa (0 + 621568)) 8 = Some (word_to_le_bytes 8 (wa can))
}.

Lemma am_frame_mem : forall R m m' sp0 can ra s0 s1 s2 s3 s4, am_frame R m sp0 can ra s0 s1 s2 s3 s4 ->
  (forall x, sp0 - 56 <= x < sp0 -> m' (wa x) = m (wa x)) -> (forall x, 621568 <= x < 621576 -> m' (wa x) = m (wa x)) ->
  am_frame R m' sp0 can ra s0 s1 s2 s3 s4.
Proof.
  intros R m m' sp0 can ra s0 s1 s2 s3 s4 F H1 H2. destruct F.
  constructor; try assumption.
  all: rewrite (rdn_frame_n m m'); first [assumption | (cbn [Z.of_nat Pos.of_succ_nat]; lia) | (intros x Hx; cbn [Z.of_nat Pos.of_succ_nat] in Hx; first [apply H1 | apply H2]; lia)].
Qed.

Lemma am_frame_regs : forall R R' m sp0 can ra s0 s1 s2 s3 s4, am_frame R m sp0 can ra s0 s1 s2 s3 s4 ->
  getr R' 2 = getr R 2 -> getr R' 18 = getr R 18 -> getr R' 19 = getr R 19 -> am_frame R' m sp0 can ra s0 s1 s2 s3 s4.
Proof. intros R R' m sp0 can ra s0 s1 s2 s3 s4 F E2 E18 E19. destruct F. constructor; try assumption; congruence. Qed.

Section AM1.
Context {fx : FPState}.

Definition am_mem0 (m : word -> option byte) (regs : bvmap 5 word) (sp0 can : Z) : word -> option byte :=
  mt0_mem_pmt0 m regs can sp0.

#[using="Type"] Theorem seg_amp : forall L s m regs rom sp0 K,
  NC L [] [] s m sp0 K -> getr regs 2 = wa sp0 ->
  exists R can, msteps SEGS (mkst regs (wa 0x53a60) m rom) (mkst R (wa 0x53a94) (am_mem0 m regs sp0 can) rom) /\
    am_frame R (am_mem0 m regs sp0 can) sp0 can (bv_unsigned (getr regs 1)) (bv_unsigned (getr regs 8)) (bv_unsigned (getr regs 9))
      (bv_unsigned (getr regs 18)) (bv_unsigned (getr regs 19)) (bv_unsigned (getr regs 20)) /\
    (forall k, In k [1; 3; 4; 5; 6; 7; 8; 9; 12; 13; 14; 15; 16; 17; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat ->
       getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))) /\
    (forall x, 0 <= x < 2^64 -> ~ (sp0 - 56 <= x < sp0) -> am_mem0 m regs sp0 can (wa x) = m (wa x)) /\
    mem_grows m (am_mem0 m regs sp0 can).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L s m regs rom sp0 K N R2.
  pose proof N as [HR HEX HZU HK Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HC HMP HMD].
  destruct Henv as (Mgot & Mtab & (can & Rcan & Mcan)).
  assert (P : mt0_pre regs m can sp0).
  { constructor; try assumption; try lia.
    all: try (apply (stk_ok_mono' m (wa sp0) K 1024); [exact HSTK | lia]).
    all: try (rewrite Z.add_0_l; assumption). }
  destruct (mt0_pmt0 regs m rom can sp0 P ltac:(constructor)) as (R & Hms & Q2 & Q10 & Q11 & Q18 & Q19 & Qk).
  exists R, can. split; [exact Hms|].
  pose proof (u64_range (getr regs 1)) as W1. pose proof (u64_range (getr regs 8)) as W8. pose proof (u64_range (getr regs 9)) as W9.
  pose proof (u64_range (getr regs 18)) as W18. pose proof (u64_range (getr regs 19)) as W19. pose proof (u64_range (getr regs 20)) as W20.
  assert (MOUT : forall x, 0 <= x < 2^64 -> ~ (sp0 - 56 <= x < sp0) -> am_mem0 m regs sp0 can (wa x) = m (wa x)).
  { intros x Hx Hn. unfold am_mem0, mt0_mem_pmt0. do 7 (rewrite MngWb.wbytes_out by side). reflexivity. }
  split.
  - constructor; try assumption; try lia.
    all: try (apply u64_range).
    all: try (rewrite (rdn_frame_n m); [exact Mcan | lia | lia | intros x Hx; apply MOUT; lia]).
    all: unfold am_mem0, mt0_mem_pmt0.
    all: repeat (rewrite rdn_wbytes_disjoint; [| side | side]).
    all: first [ (apply rdn_wbytes_hit8; side) | (rewrite wa_u; apply rdn_wbytes_hit8; side) ].
  - split; [exact Qk|]. split; [exact MOUT|].
    unfold am_mem0, mt0_mem_pmt0. repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma nc_ctx_rd : forall L s m sp0 K c, NC L [] [] s m sp0 K -> In c (ctx_cells s) -> (forall z, mc_val c <> VLo5 z) -> (mc_w c <= 8)%nat ->
  rdn SEGS m (wa (loc_addr L (mc_loc c))) (mc_w c) = Some (word_to_le_bytes (mc_w c) (wa (sval_num L (mc_val c)))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L s m sp0 K c N Hc Hv Hw. pose proof N as [HR HEX _ _ _ _ _ _ _ _ _ _ _ _].
  exact (rx_front_rd L s m [] HR (EXC_ok_of_z [] s [] (proj1 (nc_ks _ _ _ _ _ _ _ N)) HEX) c (ctx_in_front s c Hc) Hv Hw).
Qed.

#[using="Type"] Lemma nc_ctx_wr : forall L s m sp0 K c, NC L [] [] s m sp0 K -> In c (ctx_cells s) -> (forall z, mc_val c <> VLo5 z) ->
  forall d k, 0 <= d -> d + Z.of_nat k <= Z.of_nat (mc_w c) -> store_ok SEGS m (wa (loc_addr L (mc_loc c) + d)) k = true.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L s m sp0 K c N Hc Hv. pose proof N as [HR HEX _ _ _ _ _ _ _ _ _ _ _ _].
  exact (rx_front_wr L s m [] HR (EXC_ok_of_z [] s [] (proj1 (nc_ks _ _ _ _ _ _ _ N)) HEX) c (ctx_in_front s c Hc) Hv).
Qed.

Ltac in_ctx13 := unfold ctx_cells; apply in_app_iff; left; cbn [In]; repeat first [ (left; reflexivity) | right ].

#[using="Type"] Lemma nc_init_rd : forall L s m sp0 K, NC L [] [] s m sp0 K -> st_init_done s = true ->
  rdn SEGS m (wa 621728) 4 = Some (word_to_le_bytes 4 (wa 1)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L s m sp0 K N Hi. pose proof (nc_ctx _ _ _ _ _ _ _ N) as Hctx.
  pose proof (nc_ctx_rd L s m sp0 K (MCell (LCtx CTX_init_done) 4 (VZ (if st_init_done s then 1 else 0))) N ltac:(in_ctx13)
                ltac:(intros z E; discriminate) ltac:(cbn; lia)) as H.
  cbn [mc_loc mc_w mc_val loc_addr sval_num] in H. rewrite Hctx, Hi in H. exact H.
Qed.

#[using="Type"] Lemma nc_amc_rd : forall L s m sp0 K, NC L [] [] s m sp0 K ->
  rdn SEGS m (wa 621752) 8 = Some (word_to_le_bytes 8 (wa (st_avail_meta_count s))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L s m sp0 K N. pose proof (nc_ctx _ _ _ _ _ _ _ N) as Hctx.
  pose proof (nc_ctx_rd L s m sp0 K (MCell (LCtx CTX_avail_meta_count) 8 (VZ (st_avail_meta_count s))) N ltac:(in_ctx13)
                ltac:(intros z E; discriminate) ltac:(cbn; lia)) as H.
  cbn [mc_loc mc_w mc_val loc_addr sval_num] in H. rewrite Hctx in H. exact H.
Qed.

#[using="Type"] Lemma nc_am_rd : forall L s m sp0 K, NC L [] [] s m sp0 K -> st_areas s <> [] ->
  rdn SEGS m (wa 621744) 8 = Some (word_to_le_bytes 8 (wa (loc_addr L (LMem (st_avail_meta s))))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L s m sp0 K N Hne. pose proof (nc_ctx _ _ _ _ _ _ _ N) as Hctx.
  pose proof (nc_ctx_rd L s m sp0 K (MCell (LCtx CTX_avail_meta) 8
      (match st_areas s with [] => VZ 0 | _ => VP (st_avail_meta s) end)) N ltac:(in_ctx13)
                ltac:(intros z E; destruct (st_areas s); discriminate) ltac:(cbn; lia)) as H.
  cbn [mc_loc mc_w mc_val loc_addr] in H. rewrite Hctx in H. destruct (st_areas s) as [|a t]; [exfalso; exact (Hne eq_refl)|]. exact H.
Qed.

#[using="Type"] Lemma nc_ctx_holds : forall L s m sp0 K c, NC L [] [] s m sp0 K -> In c (ctx_cells s) -> cell_holds L (bview SEGS m) c.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L s m sp0 K c N Hc. pose proof N as [HR HEX _ _ _ _ _ _ _ _ _ _ _ _].
  exact (rx_front_holds L s m [] HR (EXC_ok_of_z [] s [] (proj1 (nc_ks _ _ _ _ _ _ _ N)) HEX) c (ctx_in_front s c Hc)).
Qed.

#[using="Type"] Lemma nc_am_wr : forall L s m sp0 K d k, NC L [] [] s m sp0 K -> 0 <= d -> d + Z.of_nat k <= 16 ->
  store_ok SEGS m (wa (621744 + d)) k = true.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L s m sp0 K d k N Hd Hk. pose proof (nc_ctx _ _ _ _ _ _ _ N) as Hctx.
  apply (store_ok_of_bytes SEGS m 621744 16); [|exact Hd | exact Hk].
  intros j Hj. destruct (Z_lt_le_dec j 8) as [D|D].
  - pose proof (holds_wview SEGS L m (MCell (LCtx CTX_avail_meta) 8 (match st_areas s with [] => VZ 0 | _ => VP (st_avail_meta s) end)) j
      (nc_ctx_holds L s m sp0 K (MCell (LCtx CTX_avail_meta) 8 (match st_areas s with [] => VZ 0 | _ => VP (st_avail_meta s) end)) N ltac:(in_ctx13))
      ltac:(intros z E; destruct (st_areas s); discriminate) ltac:(cbn; lia)) as W.
    cbn [mc_loc loc_addr] in W. rewrite Hctx in W. exact W.
  - pose proof (holds_wview SEGS L m (MCell (LCtx CTX_avail_meta_count) 8 (VZ (st_avail_meta_count s))) (j - 8)
      (nc_ctx_holds L s m sp0 K (MCell (LCtx CTX_avail_meta_count) 8 (VZ (st_avail_meta_count s))) N ltac:(in_ctx13))
      ltac:(intros z E; discriminate) ltac:(cbn; lia)) as W.
    cbn [mc_loc loc_addr] in W. rewrite Hctx in W. unfold CTX_avail_meta_count in W. replace (621744 + j) with (0x97c98 + 32 + (j - 8)) by ring. exact W.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition am_take_mem (m : word -> option byte) (am cnt : Z) : word -> option byte :=
  wbytes (wbytes m (wa (0 + 621744)) (word_to_le_bytes 8 (wa (am + 40)))) (wa (0 + 621752)) (word_to_le_bytes 8 (wa (cnt + -1))).

#[using="Type"] Theorem seg_amt : forall L s m R rom sp0 K spf can ra s0 s1 s2 s3 s4,
  am_frame R m spf can ra s0 s1 s2 s3 s4 -> NC L [] [] s m sp0 K ->
  st_init_done s = true -> st_free_meta_head s = None -> 0 < st_avail_meta_count s <= 101 -> st_areas s <> [] ->
  0 <= loc_addr L (LMem (st_avail_meta s)) <= 2^63-1 ->
  rdn SEGS m (wa 621648) 8 = Some (word_to_le_bytes 8 (wa 4096)) ->
  exists R', msteps SEGS (mkst R (wa 0x53a94) m rom)
                (mkst R' (wa 0x53cd4) (am_take_mem m (loc_addr L (LMem (st_avail_meta s))) (st_avail_meta_count s)) rom) /\
    getr R' 10 = wa (loc_addr L (LMem (st_avail_meta s))) /\
    am_frame R' (am_take_mem m (loc_addr L (LMem (st_avail_meta s))) (st_avail_meta_count s)) spf can ra s0 s1 s2 s3 s4 /\
    (forall k, In k [1; 3; 4; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L s m R rom sp0 K spf can ra s0 s1 s2 s3 s4 F N Hi Hf Hc Hne Ram Mpg.
  set (am := loc_addr L (LMem (st_avail_meta s))) in *. set (cnt := st_avail_meta_count s) in *.
  assert (P1 : mt1_pre R m 0).
  { constructor; [exact (mf_R19 _ _ _ _ _ _ _ _ _ _ F) | lia | | |].
    - rewrite Z.add_0_l. exact (nc_init_rd L s m sp0 K N Hi).
    - exact Mpg.
    - pose proof (nc_ctx_rd L s m sp0 K (MCell (LCtx CTX_free_meta_head) 8 (optr (st_free_meta_head s))) N ltac:(in_ctx13)
        ltac:(intros z E; cbn [mc_val optr] in E; destruct (st_free_meta_head s); discriminate) ltac:(cbn; lia)) as H.
      cbn [mc_loc mc_w mc_val loc_addr] in H. rewrite (nc_ctx _ _ _ _ _ _ _ N), sval_optr, Hf in H. exact H. }
  destruct (mt1_pmt1 R m rom 0 P1 ltac:(constructor)) as (R1 & Hms1 & A8 & A10 & A11 & A19 & Ak1).
  change (mt1_mem_pmt1 m R 0) with m in Hms1.
  assert (P2 : mt2_pre R1 m cnt am).
  { constructor; [exact A19 | lia | lia | | |].
    - rewrite Z.add_0_l. exact (nc_amc_rd L s m sp0 K N).
    - rewrite Z.add_0_l. exact (nc_am_rd L s m sp0 K N Hne).
    - intros d k Hd Hk. rewrite Z.add_0_l. exact (nc_am_wr L s m sp0 K d k N Hd Hk). }
  destruct (mt2_pmt2t R1 m rom cnt am P2) as (R2 & Hms2 & B10 & B11 & B12 & B19 & Bk2).
  { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_eez.AXF_mt2.RES_pmt2t fst snd]. repeat (first [apply Forall_nil | apply Forall_cons]). apply sc_br_z. rewrite br_eq_z.
    cbn [zeval edenot]. rewrite (zatom R1 (VALS_mt2 cnt am) 32 cnt eq_refl eq_refl) by lia.
    change (0 mod 2^64) with 0. apply Z.eqb_neq. rewrite Z.mod_small by lia. lia. }
  change (mt2_mem_pmt2t m R1 cnt am) with (am_take_mem m am cnt) in Hms2.
  exists R2. split; [exact (msteps_trans SEGS _ _ _ Hms1 Hms2)|]. split; [exact B10|].
  assert (KK : forall k, In k [1; 2; 3; 4; 18; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R2 (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))).
  { intros k Hk. rewrite (Bk2 k ltac:(clear - Hk; cbn [In] in *; repeat (destruct Hk as [<-|Hk]; [memb|]); destruct Hk)),
                         (Ak1 k ltac:(clear - Hk; cbn [In] in *; repeat (destruct Hk as [<-|Hk]; [memb|]); destruct Hk)). reflexivity. }
  split.
  - apply (am_frame_mem R2 m); [| intros x Hx; unfold am_take_mem; rewrite !MngWb.wbytes_out by (pose proof (mf_Rsp _ _ _ _ _ _ _ _ _ _ F); side); reflexivity
                                 | intros x Hx; unfold am_take_mem; rewrite !MngWb.wbytes_out by side; reflexivity].
    apply (am_frame_regs R R2 m spf can ra s0 s1 s2 s3 s4 F).
    + exact (kp_lit R2 R _ KK 2%nat (Z_to_bv 5 2) ltac:(cbn [In]; memb) ltac:(apply bv_eq; reflexivity)).
    + exact (kp_lit R2 R _ KK 18%nat (Z_to_bv 5 18) ltac:(cbn [In]; memb) ltac:(apply bv_eq; reflexivity)).
    + rewrite B19. exact (eq_sym (mf_R19 _ _ _ _ _ _ _ _ _ _ F)).
  - intros k Hk. apply KK. clear - Hk. cbn [In] in *. repeat (destruct Hk as [<-|Hk]; [memb|]); destruct Hk.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition am_ep_mem (m : word -> option byte) (mt : Z) : word -> option byte :=
  wbytes (wbytes m (wa (mt + 8)) (word_to_le_bytes 8 (wa 0))) (wa (mt + 0)) (word_to_le_bytes 8 (wa 0)).

#[using="Type"] Lemma am_ep_mem_out : forall m mt x, 0 <= mt -> mt + 16 <= 2^64 -> 0 <= x < 2^64 -> ~ (mt <= x < mt + 16) ->
  am_ep_mem m mt (wa x) = m (wa x).
Proof. LiaFast.lf_pins LiaFast.u0. intros m mt x H1 H2 Hx Hn. unfold am_ep_mem. rewrite !MngWb.wbytes_out by side. reflexivity. Qed.

#[using="Type"] Lemma am_ep_mem_8 : forall m mt x, 0 <= mt -> mt + 16 <= 2^64 -> 0 <= x < 2^64 -> mt + 8 <= x < mt + 16 ->
  am_ep_mem m mt (wa x) = wbytes m (wa (mt + 8)) (word_to_le_bytes 8 (wa 0)) (wa x).
Proof. LiaFast.lf_pins LiaFast.u0. intros m mt x H1 H2 Hx Hn. unfold am_ep_mem. rewrite MngWb.wbytes_out by side. reflexivity. Qed.

#[using="Type"] Lemma am_take_mem_out : forall m am cnt x, 0 <= x < 2^64 -> ~ (621744 <= x < 621760) -> am_take_mem m am cnt (wa x) = m (wa x).
Proof. LiaFast.lf_pins LiaFast.u0. intros m am cnt x Hx Hn. unfold am_take_mem. rewrite !MngWb.wbytes_out by side. reflexivity. Qed.

#[using="Type"] Lemma am_take_mem_lo : forall m am cnt x, 621744 <= x < 621752 ->
  am_take_mem m am cnt (wa x) = wbytes m (wa (0 + 621744)) (word_to_le_bytes 8 (wa (am + 40))) (wa x).
Proof. LiaFast.lf_pins LiaFast.u0. intros m am cnt x Hx. unfold am_take_mem. rewrite MngWb.wbytes_out by side. reflexivity. Qed.

#[using="Type"] Theorem seg_ame : forall R m rom spf can ra s0 s1 s2 s3 s4 mt,
  am_frame R m spf can ra s0 s1 s2 s3 s4 -> getr R 10 = wa mt -> 1 <= mt <= 2^63-1 -> mt mod 8 = 0 ->
  (forall d k, 0 <= d -> d + Z.of_nat k <= 16 -> store_ok SEGS m (wa (mt + 0 + d)) k = true) ->
  (mt + 16 <= spf - 56 \/ spf <= mt) -> (mt + 16 <= 621568 \/ 621576 <= mt) -> (ra = 0x542a0 \/ ra = 0x53ec4) ->
  exists R', msteps SEGS (mkst R (wa 0x53cd4) m rom) (mkst R' (wa ra) (am_ep_mem m mt) rom) /\
    getr R' 1 = wa ra /\ getr R' 2 = wa spf /\ getr R' 8 = wa s0 /\ getr R' 9 = wa s1 /\ getr R' 10 = wa mt /\
    getr R' 18 = wa s2 /\ getr R' 19 = wa s3 /\ getr R' 20 = wa s4 /\
    (forall k, In k [3; 4; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros R m rom spf can ra s0 s1 s2 s3 s4 mt F R10 Rmt Amt W D1 D2 Hra.
  destruct F as [R2 R18 R19 Rsp Asp Rcan Rra Rs0 Rs1 Rs2 Rs3 Rs4 Mra Ms0 Ms1 Ms2 Ms3 Ms4 Mcan Mgd].
  destruct Hra as [-> | ->].
  - assert (P : mte_pre R m mt can spf s0 s1 s2 s3 s4) by (constructor; try assumption; lia).
    destruct (mte_pmte R m rom mt can spf s0 s1 s2 s3 s4 P) as (R' & Hms & Q1 & Q2 & Q8 & Q9 & Q10 & _ & _ & Q18 & Q19 & Q20 & Qk).
    { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_eez.AXF_mte.RES_pmte fst snd]. constructor. }
    change (mte_mem_pmte m R mt can spf s0 s1 s2 s3 s4) with (am_ep_mem m mt) in Hms.
    exists R'. split; [exact Hms|]. do 8 (split; [assumption|]). intros k Hk. apply Qk. clear - Hk. cbn [In] in *. intuition lia.
  - assert (P : mted_pre R m mt can spf s0 s1 s2 s3 s4) by (constructor; try assumption; lia).
    destruct (mted_pmted R m rom mt can spf s0 s1 s2 s3 s4 P) as (R' & Hms & Q1 & Q2 & Q8 & Q9 & Q10 & _ & _ & Q18 & Q19 & Q20 & Qk).
    { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_eez.AXF_mted.RES_pmted fst snd]. constructor. }
    change (mted_mem_pmted m R mt can spf s0 s1 s2 s3 s4) with (am_ep_mem m mt) in Hms.
    exists R'. split; [exact Hms|]. do 8 (split; [assumption|]). intros k Hk. apply Qk. clear - Hk. cbn [In] in *. intuition lia.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition am_cell (v : sptr) : mcell := MCell (LCtx CTX_avail_meta) 8 (VP v).
Definition amc_cell (v : Z) : mcell := MCell (LCtx CTX_avail_meta_count) 8 (VZ v).

#[using="Type"] Lemma take_cov : forall s, ~ In (st_avail_meta s) (keys s) -> st_areas s <> [] ->
  forall c, In c (image (s_take s)) ->
    In c (image s) \/ c = am_cell (padd (st_avail_meta s) META_SIZE) \/ c = amc_cell (st_avail_meta_count s - 1).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros s Hk Hne c Hc. unfold image in Hc |- *. apply in_app_iff in Hc as [Hc|Hc]; [|apply in_app_iff in Hc as [Hc|Hc]].
  - unfold s_take, upd_meta in Hc. unfold ctx_cells in Hc. cbn [st_init_done st_mmap_counter st_free_meta_head st_areas st_avail_meta st_avail_meta_count
      st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_seq st_brk st_active st_usage
      st_unmap_seq st_bounces set_metas set_avail_meta set_avail_meta_count] in Hc.
    apply in_app_iff in Hc as [Hc|Hc]; [|left; apply in_app_iff; left; unfold ctx_cells; apply in_app_iff; right; exact Hc].
    destruct (st_areas s) as [|a t] eqn:Ea; [exfalso; exact (Hne eq_refl)|].
    cbn [In] in Hc.
    repeat (destruct Hc as [<-|Hc]; [first [ (right; left; reflexivity) | (right; right; reflexivity)
                                         | (left; apply in_app_iff; left; unfold ctx_cells; apply in_app_iff; left; rewrite Ea; cbn [In]; repeat first [ (left; reflexivity) | right ]) ] |]).
    destruct Hc.
  - left. apply in_app_iff. right. apply in_app_iff. left. unfold s_take, upd_meta in Hc. cbn [st_areas set_metas set_avail_meta set_avail_meta_count] in Hc.
    rewrite (areas_cells_ext s _ _) in Hc; [exact Hc|].
    intros q. cbn [st_metas set_metas set_avail_meta set_avail_meta_count]. destruct (sptr_eq_dec q (st_avail_meta s)) as [->|Hq].
    + rewrite mlookup_mupdate_same. destruct (mlookup (st_metas s) (st_avail_meta s)) as [x|] eqn:E; [|reflexivity].
      exfalso. apply Hk. unfold keys. exact (mlookup_In_keys _ _ _ E).
    + rewrite mlookup_mupdate_other by exact Hq. reflexivity.
  - left. apply in_app_iff. right. apply in_app_iff. right. unfold s_take in Hc. rewrite used_metas_raw_new in Hc.
    + exact Hc.
    + unfold keys. cbn [st_metas set_avail_meta set_avail_meta_count]. exact Hk.
Qed.


#[using="Type"] Lemma take_rev : forall s, ~ In (st_avail_meta s) (keys s) -> st_areas s <> [] ->
  forall c, In c (image s) ->
    In c (image (s_take s)) \/ mc_loc c = LCtx CTX_avail_meta /\ mc_w c = 8%nat \/ mc_loc c = LCtx CTX_avail_meta_count /\ mc_w c = 8%nat.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros s Hk Hne c Hc. unfold image in Hc |- *. apply in_app_iff in Hc as [Hc|Hc]; [|apply in_app_iff in Hc as [Hc|Hc]].
  - unfold ctx_cells in Hc. apply in_app_iff in Hc as [Hc|Hc]; [|left; apply in_app_iff; left; unfold ctx_cells; apply in_app_iff; right; exact Hc].
    cbn [In] in Hc.
    repeat (destruct Hc as [<-|Hc]; [first [ (right; left; split; reflexivity) | (right; right; split; reflexivity)
                                         | (left; apply in_app_iff; left; unfold ctx_cells, s_take, upd_meta; apply in_app_iff; left;
                                            cbn [st_init_done st_mmap_counter st_free_meta_head st_areas st_avail_meta st_avail_meta_count
                                              st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_seq st_brk
                                              set_metas set_avail_meta set_avail_meta_count In]; repeat first [ (left; reflexivity) | right ]) ] |]).
    destruct Hc.
  - left. apply in_app_iff. right. apply in_app_iff. left. unfold s_take, upd_meta. cbn [st_areas set_metas set_avail_meta set_avail_meta_count].
    rewrite (areas_cells_ext s _ _); [exact Hc|].
    intros q. cbn [st_metas set_metas set_avail_meta set_avail_meta_count]. destruct (sptr_eq_dec q (st_avail_meta s)) as [->|Hq].
    + rewrite mlookup_mupdate_same. destruct (mlookup (st_metas s) (st_avail_meta s)) as [x|] eqn:E; [|reflexivity].
      exfalso. apply Hk. unfold keys. exact (mlookup_In_keys _ _ _ E).
    + rewrite mlookup_mupdate_other by exact Hq. reflexivity.
  - left. apply in_app_iff. right. apply in_app_iff. right. unfold s_take. rewrite used_metas_raw_new; [exact Hc|].
    unfold keys. cbn [st_metas set_avail_meta set_avail_meta_count]. exact Hk.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma in_image_front : forall s c, In c (ctx_cells s ++ areas_cells s (st_areas s)) -> In c (image s).
Proof. LiaFast.lf_pins LiaFast.u0. intros s c H. rewrite image_parts, app_assoc. apply in_app_iff. left. exact H. Qed.

#[using="Type"] Theorem am_take : forall HTOP X R U L s m regs rom sp0 K ra,
  CUT HTOP X R U L s m sp0 K -> getr regs 2 = wa sp0 -> getr regs 1 = wa ra -> (ra = 0x542a0 \/ ra = 0x53ec4) ->
  st_init_done s = true -> st_free_meta_head s = None -> 0 < st_avail_meta_count s ->
  rdn SEGS m (wa 621648) 8 = Some (word_to_le_bytes 8 (wa 4096)) ->
  exists R' m', msteps SEGS (mkst regs (wa 0x53a60) m rom) (mkst R' (wa ra) m' rom) /\
    getr R' 10 = wa (loc_addr L (LMem (st_avail_meta s))) /\
    (forall k, In k [1;2;3;4;8;9;18;19;20;21;22;23;24;25;26;27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))) /\
    CUT HTOP (st_avail_meta s :: X) R U L (s_take s) m' sp0 K /\ GROW sp0 K L s m L (s_take s) m' /\ mem_grows m m'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros HTOP X R U L s m regs rom sp0 K ra C R2 R1 Hra Hi Hf Hc Mpg.
  pose proof C as [HI HX N HG HD HT HTB].
  pose proof N as [HR HEX HZU HK Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HC HMP HMD].
  pose proof (inv_keys HI) as (Knd & Kpl & Kemp & Kav & Krange).
  assert (Hne : st_areas s <> []) by (intros E; pose proof (Kemp E); lia).
  set (mt := st_avail_meta s) in *. set (cnt := st_avail_meta_count s) in *. set (am := loc_addr L (LMem mt)) in *.
  (* [comment removed for export] *)
  set (la := last (st_areas s) (SP 0%nat 0)) in *.
  assert (Hla : In la (st_areas s)) by (apply MngLt.last_In_l; exact Hne).
  destruct (area_range HTOP X R U s L la HI HG Hla) as (r & rg & Epr & Hr & Hl & _ & B1 & B2 & B3 & B4).
  destruct (HG r rg Hr Hl) as (G1 & G2 & G3 & G4). unfold ranges_disjoint in G4. cbn [fst snd] in G4.
  assert (Eam : am = loc_addr L (LMem la) + 24 + 40 * (101 - cnt)).
  { assert (Emt : mt = padd la (AREA_HDR + META_SIZE * (METAS_PER_AREA - cnt))) by exact (Kav Hne).
    unfold am. rewrite Emt. rewrite !loc_addr_LMem, prid_padd, poff_padd. unfold AREA_HDR, META_SIZE, METAS_PER_AREA. ring. }
  assert (Aam : am mod 8 = 0).
  { rewrite Eam. rewrite loc_addr_LMem in *. rewrite Epr in *. apply Z.mod_divide in G2; [|unfold PGSZ; lia]. apply Z.mod_divide in B4; [|unfold PGSZ; lia].
    destruct G2 as (k1 & E1). destruct B4 as (k2 & E2). rewrite E1, E2. unfold PGSZ.
    replace (k1 * 4096 + k2 * 4096 + 24 + 40 * (101 - cnt)) with ((k1 * 512 + k2 * 512 + 3 + 5 * (101 - cnt)) * 8) by ring. apply Z.mod_mul. lia. }
  assert (Ram : (am + 40 <= 0x10000 \/ 0x99000 <= am) /\ am + 40 <= HTOP /\ 4096 <= am).
  { rewrite Eam. clear - B1 B2 G1 G3 G4 Hc Krange. unfold PGSZ, METAS_PER_AREA in *. lia. }
  (* [comment removed for export] *)
  destruct (seg_amp L s m regs rom sp0 K N R2) as (R1' & can & Hms1 & F1 & K1 & MOUT1 & GR1).
  set (m1 := am_mem0 m regs sp0 can) in *.
  assert (N1 : NC L [] [] s m1 sp0 K) by (apply (NC_stackw L s m m1 sp0 K N GR1); intros x Hx Hn; apply MOUT1; [exact Hx | lia]).
  assert (Mpg1 : rdn SEGS m1 (wa 621648) 8 = Some (word_to_le_bytes 8 (wa 4096))).
  { rewrite (rdn_frame_n m m1 621648 8) by (first [lia | (intros x Hx; cbn in Hx; apply MOUT1; lia)]). exact Mpg. }
  (* [comment removed for export] *)
  assert (Hc' : 0 < st_avail_meta_count s <= 101) by (clear - Hc Krange; unfold METAS_PER_AREA in *; lia).
  assert (Ram' : 0 <= am <= 2^63-1) by (clear - Ram HTB; lia).
  destruct (seg_amt L s m1 R1' rom sp0 K sp0 can _ _ _ _ _ _ F1 N1 Hi Hf Hc' Hne Ram' Mpg1) as (R2' & Hms2 & B10 & F2 & K2).
  fold mt am cnt in Hms2, B10, F2.
  set (m2 := am_take_mem m1 am cnt) in *.
  assert (G2' : mem_grows m1 m2) by (unfold m2, am_take_mem; exact (mem_grows_trans _ _ _ (wbytes_grows _ _ _) (wbytes_grows _ _ _))).
  (* [comment removed for export] *)
  assert (W16 : forall d k, 0 <= d -> d + Z.of_nat k <= 16 -> store_ok SEGS m2 (wa (am + 0 + d)) k = true).
  { intros d k Hd Hk. apply (store_ok_mono SEGS k m m2); [exact (mem_grows_trans _ _ _ GR1 G2')|].
    replace (am + 0 + d) with (am + d) by ring. apply (store_ok_of_bytes SEGS m am 16); [|exact Hd | exact Hk].
    intros j Hj. assert (Hfp : In (LMem la, PGSZ) (footprint s)) by (right; apply in_app_iff; left; apply in_map_iff; exists la; auto).
    pose proof (proj1 (Forall_forall _ _) (proj2 (proj2 (proj2 HR))) _ Hfp (am + j) ltac:(cbn [fst snd]; rewrite Eam; unfold PGSZ; lia)) as H.
    unfold bview in H. destruct ((0 <=? am + j) && (am + j <? 2^64)); [|exfalso; exact (H eq_refl)].
    destruct (wview SEGS m (wa (am + j))); [discriminate | exfalso; exact (H eq_refl)]. }
  assert (Era : bv_unsigned (getr regs 1) = ra) by (rewrite R1; apply u_wa_small; clear - Hra; lia).
  assert (Hra' : bv_unsigned (getr regs 1) = 0x542a0 \/ bv_unsigned (getr regs 1) = 0x53ec4) by (rewrite Era; exact Hra).
  assert (D1 : am + 16 <= sp0 - 56 \/ sp0 <= am) by (clear - Ram HT HK1; lia).
  assert (D2 : am + 16 <= 621568 \/ 621576 <= am) by (clear - Ram; lia).
  destruct (seg_ame R2' m2 rom sp0 can _ _ _ _ _ _ am F2 B10 ltac:(clear - Ram HTB; lia) Aam W16 D1 D2 Hra')
    as (R3 & Hms3 & C1 & C2 & C8 & C9 & C10 & C18 & C19 & C20 & K3).
  set (m3 := am_ep_mem m2 am) in *.
  assert (GR3 : mem_grows m2 m3) by (unfold m3, am_ep_mem; exact (mem_grows_trans _ _ _ (wbytes_grows _ _ _) (wbytes_grows _ _ _))).
  rewrite Era in Hms3. exists R3, m3. split; [exact (msteps_trans SEGS _ _ _ Hms1 (msteps_trans SEGS _ _ _ Hms2 Hms3))|]. split; [exact C10|].
  split.
  { intros k Hk. cbn [In] in Hk.
    assert (KK : forall k, In k [3;4;21;22;23;24;25;26;27]%nat -> getr R3 (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
    { intros k' Hk'. rewrite (K3 k' Hk'), (K2 k' ltac:(clear - Hk'; cbn [In] in *; repeat (destruct Hk' as [<-|Hk']; [memb|]); destruct Hk')),
                              (K1 k' ltac:(clear - Hk'; cbn [In] in *; repeat (destruct Hk' as [<-|Hk']; [memb|]); destruct Hk')). reflexivity. }
    destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]]].
    - litr2 C1. apply wa_u.
    - litr2 C2. rewrite <- R2. reflexivity.
    - apply KK. cbn [In]. repeat first [ (left; reflexivity) | right ].
    - apply KK. cbn [In]. repeat first [ (left; reflexivity) | right ].
    - litr2 C8. apply wa_u.
    - litr2 C9. apply wa_u.
    - litr2 C18. apply wa_u.
    - litr2 C19. apply wa_u.
    - litr2 C20. apply wa_u.
    - apply KK. cbn [In]. repeat first [ (left; reflexivity) | right ].
    - apply KK. cbn [In]. repeat first [ (left; reflexivity) | right ].
    - apply KK. cbn [In]. repeat first [ (left; reflexivity) | right ].
    - apply KK. cbn [In]. repeat first [ (left; reflexivity) | right ].
    - apply KK. cbn [In]. repeat first [ (left; reflexivity) | right ].
    - apply KK. cbn [In]. repeat first [ (left; reflexivity) | right ].
    - apply KK. cbn [In]. repeat first [ (left; reflexivity) | right ]. }
  (* [comment removed for export] *)
  destruct (take_slot_Inv X R U s HI Hc) as (Hfresh & NX & HI2 & EU2). fold mt in Hfresh, NX, HI2, EU2.
  change (upd_meta mt MRaw (set_avail_meta (padd mt META_SIZE) (set_avail_meta_count (cnt - 1) s))) with (s_take s) in HI2.
  assert (HX2 : XNM (mt :: X) (s_take s)).
  { intros x [<-|Hx]; [left; unfold s_take; apply MT_upd_same|].
    assert (Hxk : x <> mt) by (intros ->; destruct (HX mt Hx) as [E|E]; apply Hfresh; exact (MT_Some_In_keys s mt _ E)).
    unfold s_take. rewrite MT_upd_other by exact Hxk. exact (HX x Hx). }
  set (Cnew := [am_cell (padd mt META_SIZE); amc_cell (cnt - 1); MCell (LMem (padd mt META_prev)) 8 (VZ 0); MCell (LMem (padd mt META_next)) 8 (VZ 0)]).
  assert (MTt : MT (s_take s) mt = Some MRaw) by (unfold s_take; apply MT_upd_same).
  assert (KSt : KS (s_take s)) by exact (KS_of_Inv _ _ _ _ HI2).
  assert (LPm : forall d, loc_addr L (LMem (padd mt d)) = am + d) by (intros d; unfold am; rewrite !loc_addr_LMem, prid_padd, poff_padd; ring).
  assert (MOUT3 : forall x, 0 <= x < 2^64 -> ~ (sp0 - 56 <= x < sp0) -> ~ (621744 <= x < 621760) -> ~ (am <= x < am + 16) -> m3 (wa x) = m (wa x)).
  { intros x Hx H1 H2 H3. unfold m3. rewrite am_ep_mem_out by (clear - Ram HTB Hx H3; lia). unfold m2. rewrite am_take_mem_out by (clear - Hx H2; lia).
    apply MOUT1; assumption. }
  assert (MG : mem_grows m m3) by exact (mem_grows_trans _ _ _ GR1 (mem_grows_trans _ _ _ G2' GR3)).
  cut (CUT HTOP (mt :: X) R U L (s_take s) m3 sp0 K /\ GROW sp0 K L s m L (s_take s) m3);
    [intros (CC & GG); split; [exact CC | split; [exact GG | exact MG]]|].
  apply (silent_step HTOP X R U (mt :: X) R U L s (s_take s) m m3 sp0 K Cnew C HI2 HX2 eq_refl).
  - intros fpr Hfpr. left. exact Hfpr.
  - intros c Hcn. destruct (take_cov s Hfresh Hne c Hcn) as [H|[H|H]]; [left; exact H | right; subst c; cbn [In]; memb | right; subst c; cbn [In]; memb].
  - intros c Hcn. cbn [In] in Hcn. destruct Hcn as [<-|[<-|[<-|[<-|[]]]]].
    + apply ctx_in_image. unfold ctx_cells, s_take, upd_meta. apply in_app_iff. left.
      cbn [st_init_done st_mmap_counter st_free_meta_head st_areas st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift
           st_area_head st_area_tail st_avail_meta_areas st_seq st_brk set_metas set_avail_meta set_avail_meta_count].
      destruct (st_areas s) as [|a t]; [exfalso; exact (Hne eq_refl)|]. cbn [In]. repeat first [ (left; reflexivity) | right ].
    + apply ctx_in_image. unfold ctx_cells, s_take, upd_meta. apply in_app_iff. left.
      cbn [st_init_done st_mmap_counter st_free_meta_head st_areas st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift
           st_area_head st_area_tail st_avail_meta_areas st_seq st_brk set_metas set_avail_meta set_avail_meta_count In].
      repeat first [ (left; reflexivity) | right ].
    + apply in_image_front. apply (msc_in_front (s_take s) mt MRaw _ KSt MTt). cbn [meta_slot_cells In]. memb.
    + apply in_image_front. apply (msc_in_front (s_take s) mt MRaw _ KSt MTt). cbn [meta_slot_cells In]. memb.
  - intros c Hcn. destruct (take_rev s Hfresh Hne c Hcn) as [H|[(El & Ew)|(El & Ew)]]; [left; exact H| |].
    + right. exists (am_cell (padd mt META_SIZE)). split; [cbn [In]; memb|]. unfold cell_range. rewrite El, Ew. reflexivity.
    + right. exists (amc_cell (cnt - 1)). split; [cbn [In]; memb|]. unfold cell_range. rewrite El, Ew. reflexivity.
  - apply Forall_forall. intros c Hcn. cbn [In] in Hcn. destruct Hcn as [<-|[<-|[<-|[<-|[]]]]].
    + unfold am_cell. apply (cell_holds_frame L (bview SEGS (wbytes m1 (wa (0 + 621744)) (word_to_le_bytes 8 (wa (am + 40))))) (bview SEGS m3)); [cbn [mc_w]; lia | |].
      * replace (0 + 621744) with (loc_addr L (mc_loc (MCell (LCtx CTX_avail_meta) 8 (VP (padd mt META_SIZE))))) by (cbn; rewrite Hctx; reflexivity).
        apply holds_wb; [intros z E; discriminate | cbn [mc_w]; lia | cbn [mc_loc loc_addr]; rewrite Hctx; unfold CTX_avail_meta; lia
                        | cbn [mc_loc mc_w loc_addr Z.of_nat Pos.of_succ_nat]; rewrite Hctx; unfold CTX_avail_meta; lia |].
        cbn [mc_val sval_num mc_w]. rewrite LPm. reflexivity.
      * intros a Ha. unfold in_rng, cell_range in Ha. cbn [mc_loc mc_w loc_addr fst snd] in Ha. rewrite Hctx in Ha. apply MngWb.bview_ext.
        unfold CTX_avail_meta in Ha. unfold m3. rewrite am_ep_mem_out by (clear - Ram HTB Ha; lia). unfold m2. rewrite am_take_mem_lo by (clear - Ha; lia). reflexivity.
    + unfold amc_cell. apply (cell_holds_frame L (bview SEGS m2) (bview SEGS m3)); [cbn [mc_w]; lia | |].
      * unfold m2, am_take_mem.
        replace (0 + 621752) with (loc_addr L (mc_loc (MCell (LCtx CTX_avail_meta_count) 8 (VZ (cnt - 1))))) by (cbn; rewrite Hctx; reflexivity).
        apply holds_wb; [intros z E; discriminate | cbn [mc_w]; lia | cbn [mc_loc loc_addr]; rewrite Hctx; unfold CTX_avail_meta_count; lia
                        | cbn [mc_loc mc_w loc_addr Z.of_nat Pos.of_succ_nat]; rewrite Hctx; unfold CTX_avail_meta_count; lia |].
        cbn [mc_val sval_num mc_w]. f_equal. all: lia.
      * intros a Ha. unfold in_rng, cell_range in Ha. cbn [mc_loc mc_w loc_addr fst snd] in Ha. rewrite Hctx in Ha. apply MngWb.bview_ext.
        unfold CTX_avail_meta_count in Ha. unfold m3. rewrite am_ep_mem_out by (clear - Ram HTB Ha; lia). reflexivity.
    + unfold m3, am_ep_mem. replace (am + 0) with (loc_addr L (mc_loc (MCell (LMem (padd mt META_prev)) 8 (VZ 0)))) by (cbn [mc_loc]; rewrite LPm; reflexivity).
      apply holds_wb; [intros z E; discriminate | cbn [mc_w]; lia | cbn [mc_loc]; rewrite LPm; unfold META_prev; clear - Ram HTB; lia
                      | cbn [mc_loc mc_w Z.of_nat Pos.of_succ_nat]; rewrite LPm; unfold META_prev; clear - Ram HTB; lia | reflexivity].
    + apply (cell_holds_frame L (bview SEGS (wbytes m2 (wa (am + 8)) (word_to_le_bytes 8 (wa 0)))) (bview SEGS m3)); [cbn [mc_w]; lia | |].
      * replace (am + 8) with (loc_addr L (mc_loc (MCell (LMem (padd mt META_next)) 8 (VZ 0)))) by (cbn [mc_loc]; rewrite LPm; reflexivity).
        apply holds_wb; [intros z E; discriminate | cbn [mc_w]; lia | cbn [mc_loc]; rewrite LPm; unfold META_next; clear - Ram HTB; lia
                      | cbn [mc_loc mc_w Z.of_nat Pos.of_succ_nat]; rewrite LPm; unfold META_next; clear - Ram HTB; lia | reflexivity].
      * intros a Ha. unfold in_rng, cell_range in Ha. cbn [mc_loc mc_w fst snd] in Ha. rewrite LPm in Ha. apply MngWb.bview_ext.
        unfold m3. rewrite am_ep_mem_8 by (clear - Ram HTB Ha; unfold META_next in Ha; lia). reflexivity.
  - exact MG.
  - intros x Hx Hne'.
    assert (CASES : (sp0 - K <= x < sp0) \/ (621744 <= x < 621752) \/ (621752 <= x < 621760) \/ (am <= x < am + 8) \/ (am + 8 <= x < am + 16)).
    { destruct (range_dec x (sp0 - 56) 56) as [XA|XA]; [left; clear - XA HK1; lia|].
      destruct (range_dec x 621744 16) as [XB|XB]; [destruct (Z_lt_ge_dec x 621752); [right; left; lia | right; right; left; lia]|].
      destruct (range_dec x am 16) as [XC|XC]; [destruct (Z_lt_ge_dec x (am + 8)); [right; right; right; left; lia | right; right; right; right; lia]|].
      exfalso. apply Hne'. apply MOUT3; [exact Hx | replace sp0 with (sp0 - 56 + 56) at 2 by ring; exact XA | exact XB | exact XC]. }
    destruct CASES as [A|[B|[B|[B|B]]]]; [left; exact A|right..].
    + exists (am_cell (padd mt META_SIZE)). split; [cbn [In]; memb|]. unfold in_rng, cell_range, am_cell, amc_cell. cbn [mc_loc mc_w loc_addr fst snd]. rewrite Hctx. unfold CTX_avail_meta. clear - B. lia.
    + exists (amc_cell (cnt - 1)). split; [cbn [In]; memb|]. unfold in_rng, cell_range, am_cell, amc_cell. cbn [mc_loc mc_w loc_addr fst snd]. rewrite Hctx. unfold CTX_avail_meta_count. clear - B. lia.
    + exists (MCell (LMem (padd mt META_prev)) 8 (VZ 0)). split; [cbn [In]; memb|]. unfold in_rng, cell_range. cbn [mc_loc mc_w fst snd]. rewrite LPm. unfold META_prev. clear - B. lia.
    + exists (MCell (LMem (padd mt META_next)) 8 (VZ 0)). split; [cbn [In]; memb|]. unfold in_rng, cell_range. cbn [mc_loc mc_w fst snd]. rewrite LPm. unfold META_next. clear - B. lia.
Qed.


(* [comment removed for export] *)
#[using="Type"] Lemma am_regs : forall (regs R1 R2 R3 : bvmap 5 word) sp0,
  getr regs 2 = wa sp0 ->
  (forall k, In k [1; 3; 4; 5; 6; 7; 8; 9; 12; 13; 14; 15; 16; 17; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat ->
     getr R1 (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))) ->
  (forall k, In k [1; 3; 4; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R2 (Z_to_bv 5 (Z.of_nat k)) = getr R1 (Z_to_bv 5 (Z.of_nat k))) ->
  (forall k, In k [3; 4; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R3 (Z_to_bv 5 (Z.of_nat k)) = getr R2 (Z_to_bv 5 (Z.of_nat k))) ->
  getr R3 1 = wa (bv_unsigned (getr regs 1)) -> getr R3 2 = wa sp0 -> getr R3 8 = wa (bv_unsigned (getr regs 8)) ->
  getr R3 9 = wa (bv_unsigned (getr regs 9)) -> getr R3 18 = wa (bv_unsigned (getr regs 18)) ->
  getr R3 19 = wa (bv_unsigned (getr regs 19)) -> getr R3 20 = wa (bv_unsigned (getr regs 20)) ->
  forall k, In k [1;2;3;4;8;9;18;19;20;21;22;23;24;25;26;27]%nat -> getr R3 (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs R1 R2 R3 sp0 R2e K1 K2 K3 C1 C2 C8 C9 C18 C19 C20 k Hk'.
  assert (KK : forall k, In k [3;4;21;22;23;24;25;26;27]%nat -> getr R3 (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
  { intros k' Hk2. rewrite (K3 k' Hk2), (K2 k' ltac:(clear - Hk2; cbn [In] in *; repeat (destruct Hk2 as [<-|Hk2]; [memb|]); destruct Hk2)),
                            (K1 k' ltac:(clear - Hk2; cbn [In] in *; repeat (destruct Hk2 as [<-|Hk2]; [memb|]); destruct Hk2)). reflexivity. }
  cbn [In] in Hk'.
  destruct Hk' as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]]].
  - litr2 C1. apply wa_u.
  - litr2 C2. rewrite <- R2e. reflexivity.
  - apply KK. cbn [In]. memb.
  - apply KK. cbn [In]. memb.
  - litr2 C8. apply wa_u.
  - litr2 C9. apply wa_u.
  - litr2 C18. apply wa_u.
  - litr2 C19. apply wa_u.
  - litr2 C20. apply wa_u.
  - apply KK. cbn [In]. memb.
  - apply KK. cbn [In]. memb.
  - apply KK. cbn [In]. memb.
  - apply KK. cbn [In]. memb.
  - apply KK. cbn [In]. memb.
  - apply KK. cbn [In]. memb.
  - apply KK. cbn [In]. memb.
Qed.

End AM1.
