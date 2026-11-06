(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3 SeqExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr MallocWfMeta.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocLemmasRing OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGeom OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AxMng AxBits MngZ MngRepr MngHeap MngImage MngWb MngWk MngGeoX MngLt MngSurgery MngExc MngNtfPre MngNtfC MngNtfM MngNtfS MngGM MngCtx2.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngHeap.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngMW0 MngMW1.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_eez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_eez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_eez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_eez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_eez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_eez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_eez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_eez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_eez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXG_am1 AXG_am3 AXG_am4.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxMng OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxBits OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngZ OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngRepr OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngHeap OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngImage OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngWb OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngWk OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngGeoX OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngLt OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngSurgery OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngExc OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfPre OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfC OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfM OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfS OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngGM OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngCtx2 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngHeap.MngMWP OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngMW0 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngMW1 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_mt1z OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_mt2z OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_mt3oz OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_mt8bz OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_mpwz OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_mprz OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_mt9z OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_mt10z OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_mt100z OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_am1 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_am3 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_am4.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma nth_of_nth_error' : forall {A} (l : list A) r y d, nth_error l r = Some y -> nth r l d = y.
Proof. intros A l. induction l as [|h t IH]; intros [|r] y d H; cbn in H; try discriminate; [injection H as <-; reflexivity | exact (IH r y d H)]. Qed.

Definition rw_page (rg : region) (o : Z) : region := mkRegion (rg_kind rg) (rg_len rg) (rg_rw rg ++ [o]) (rg_live rg).

Definition s_res1 (s : astate) (r : nat) (rg : region) (o : Z) : astate := set_regions (lupd (st_regions s) r (rw_page rg o)) s.

Lemma alloc_meta_openres : forall s r o rg, st_init_done s = true -> st_free_meta_head s = None -> st_avail_meta_count s = 0 ->
  0 < st_avail_meta_area_count s -> st_avail_meta_areas s = SP r o -> region_of s r = Some rg ->
  exists K, alloc_meta s = IAsk (KMprotect (SP r o)) s K /\
    K 1 = IRet (Some (padd (SP r o) AREA_HDR), s_opn (SP r o) (s_res1 s r rg o)).
Proof.
  intros s r o rg Hi Hf Hc Hac Hp Hr. eexists. split.
  - unfold alloc_meta. cbn. rewrite set_init_done_same by exact Hi. rewrite Hf. cbn. rewrite Hc. cbn.
    replace (st_avail_meta_area_count s =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn.
    replace (st_avail_meta_area_count s =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn.
    rewrite Hp. reflexivity.
  - cbn. unfold region_of in Hr. rewrite (nth_of_nth_error' _ _ _ _ Hr). cbn [prid poff].
    unfold s_opn, s_take, open_st, s_res1, rw_page. cbn. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac klist H := first [ AxSymRun3.klist_refl H | (cbn [In] in H |- *; repeat (destruct H as [<-|H]; [first [solve [memb] | (exfalso; congruence)] |]); destruct H) ].      (* [comment removed for export] *)
Ltac regk KK k := match goal with |- getr _ ?r0 = _ => replace r0 with (Z_to_bv 5 (Z.of_nat k)) by (apply bv_eq; reflexivity) end;
  rewrite (KK k ltac:(cbn [In]; solve [memb])).
Ltac in_ctx13 := unfold ctx_cells; apply in_app_iff; left; cbn [In]; repeat first [ (left; reflexivity) | right ].

Section AM5.
Context {fx : FPState}.

#[using="Type"] Theorem seg_amq : forall HTOP X R U L s m Rg rom sp0 K spf can ra s0 s1 s2 s3 s4,
  am_frame Rg m spf can ra s0 s1 s2 s3 s4 -> CUT HTOP X R U L s m sp0 K ->
  st_init_done s = true -> st_free_meta_head s = None -> st_avail_meta_count s = 0 ->
  rdn SEGS m (wa 614032) 8 = Some (word_to_le_bytes 8 (wa 4096)) ->
  exists R', msteps SEGS (mkst Rg (wa 0x51cdc) m rom) (mkst R' (wa 0x51db0) m rom) /\ getr R' 8 = wa 4096 /\
    am_frame R' m spf can ra s0 s1 s2 s3 s4 /\
    (forall k, In k [1; 3; 4; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr Rg (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros HTOP X R U L s m Rg rom sp0 K spf can ra s0 s1 s2 s3 s4 F C Hi Hf Hc Mpg.
  pose proof C as [HI HX N HG HD HT HTB].
  pose proof (nc_ctx _ _ _ _ _ _ _ N) as Hctx.
  assert (P1 : mt1_pre Rg m 0).
  { constructor; [exact (mf_R19 _ _ _ _ _ _ _ _ _ _ F) | lia | | |].
    - rewrite Z.add_0_l. exact (nc_init_rd L s m sp0 K N Hi).
    - exact Mpg.
    - pose proof (nc_ctx_rd L s m sp0 K (MCell (LCtx CTX_free_meta_head) 8 (optr (st_free_meta_head s))) N ltac:(in_ctx13)
        ltac:(intros z E; cbn [mc_val optr] in E; destruct (st_free_meta_head s); discriminate) ltac:(cbn; lia)) as H.
      cbn [mc_loc mc_w mc_val loc_addr] in H. rewrite Hctx, sval_optr, Hf in H. exact H. }
  destruct (mt1_pmt1 Rg m rom 0 P1 ltac:(constructor)) as (R1 & Hms1 & A8 & A10 & A11 & A19 & Ak1).
  change (mt1_mem_pmt1 m Rg 0) with m in Hms1.
  set (am := sval_num L (match st_areas s with [] => VZ 0 | _ => VP (st_avail_meta s) end)).
  pose proof (nc_ctx_rd L s m sp0 K (MCell (LCtx CTX_avail_meta) 8 (match st_areas s with [] => VZ 0 | _ => VP (st_avail_meta s) end)) N ltac:(in_ctx13)
      ltac:(intros z E; destruct (st_areas s); discriminate) ltac:(cbn; lia)) as Mam.
  cbn [mc_loc mc_w mc_val loc_addr] in Mam. rewrite Hctx in Mam. fold am in Mam.
  assert (Ram2 : 0 <= am <= 2^63-1).
  { unfold am. destruct (st_areas s) as [|a t] eqn:Ea; [cbn; lia|]. cbn [sval_num].
    pose proof (inv_keys HI) as (_ & _ & _ & Kav & _).
    assert (Hne : st_areas s <> []) by (rewrite Ea; discriminate).
    rewrite (Kav Hne). set (la := last (st_areas s) (SP 0%nat 0)).
    assert (Hla : In la (st_areas s)) by (apply MngLt.last_In_l; exact Hne).
    destruct (area_range HTOP X R U s L la HI HG Hla) as (r & rg & _ & Hr & Hl & _ & B1 & B2 & _).
    destruct (HG r rg Hr Hl) as (G1 & _ & G3 & _).
    rewrite !loc_addr_LMem, prid_padd, poff_padd. rewrite loc_addr_LMem in B1, B2. rewrite Hc.
    unfold AREA_HDR, META_SIZE, METAS_PER_AREA, PGSZ in *. clear - B1 B2 G1 G3 HTB. lia. }
  assert (P2 : mt2_pre R1 m 0 am).
  { constructor; [exact A19 | lia | exact Ram2 | | |].
    - rewrite Z.add_0_l. rewrite <- Hc. exact (nc_amc_rd L s m sp0 K N).
    - rewrite Z.add_0_l. exact Mam.
    - intros d k Hd Hk. rewrite Z.add_0_l. exact (nc_am_wr L s m sp0 K d k N Hd Hk). }
  destruct (mt2_pmt2z R1 m rom 0 am P2) as (R2 & Hms2 & B11 & B19 & Bk2).
  { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_mt2.RES_pmt2z fst snd]. repeat (first [apply Forall_nil | apply Forall_cons]). apply sc_br_z. rewrite br_eq_z.
    cbn [zeval edenot]. rewrite (zatom R1 (VALS_mt2 0 am) 32 0 eq_refl eq_refl) by lia. reflexivity. }
  change (mt2_mem_pmt2z m R1 0 am) with m in Hms2.
  exists R2. split; [exact (msteps_trans SEGS _ _ _ Hms1 Hms2)|]. split; [match goal with |- getr _ ?r0 = _ => replace r0 with (Z_to_bv 5 (Z.of_nat 8)) by (apply bv_eq; reflexivity) end;
           rewrite (Bk2 8%nat ltac:(cbn [In]; memb)); litr2 A8; reflexivity|].
  assert (KK : forall k, In k [1; 2; 3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R2 (Z_to_bv 5 (Z.of_nat k)) = getr Rg (Z_to_bv 5 (Z.of_nat k))).
  { intros k Hk'. destruct (decide (k = 19%nat)) as [->|Hn19].
    - litr2 B19. exact (eq_sym (mf_R19 _ _ _ _ _ _ _ _ _ _ F)).
    - rewrite (Bk2 k ltac:(clear - Hk' Hn19; klist Hk')). apply Ak1. clear - Hk' Hn19. klist Hk'. }
  split.
  - apply (am_frame_regs Rg R2 m spf can ra s0 s1 s2 s3 s4 F).
    + exact (kp_lit R2 Rg _ KK 2%nat (Z_to_bv 5 2) ltac:(cbn [In]; memb) ltac:(apply bv_eq; reflexivity)).
    + exact (kp_lit R2 Rg _ KK 18%nat (Z_to_bv 5 18) ltac:(cbn [In]; memb) ltac:(apply bv_eq; reflexivity)).
    + exact (kp_lit R2 Rg _ KK 19%nat (Z_to_bv 5 19) ltac:(cbn [In]; memb) ltac:(apply bv_eq; reflexivity)).
  - intros k Hk'. apply KK. clear - Hk'. klist Hk'.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition mpw_store (m : word -> option byte) (sp0 : Z) : word -> option byte :=
  wbytes m (wa (sp0 + -64 + -8)) (word_to_le_bytes 8 (wa 335712)).

(* [comment removed for export] *)
#[using="Type"] Theorem seg_amr0 : forall R m rom sp0 can ra s0 s1 s2 s3 s4 ac ar,
  am_frame R m sp0 can ra s0 s1 s2 s3 s4 -> getr R 8 = wa 4096 ->
  1 <= ac <= 2^60 -> rdn SEGS m (wa (0 + 614144)) 8 = Some (word_to_le_bytes 8 (wa ac)) ->
  4096 <= ar <= 2^47 -> ar mod 4096 = 0 -> rdn SEGS m (wa (0 + 614176)) 8 = Some (word_to_le_bytes 8 (wa ar)) ->
  exists R', msteps SEGS (mkst R (wa 0x51db0) m rom) (mkst R' (wa 0x53414) m rom) /\
    getr R' 1 = wa 335712 /\ getr R' 9 = wa ar /\ getr R' 10 = wa ar /\ getr R' 11 = wa 4096 /\ getr R' 12 = wa 3 /\
    am_frame R' m sp0 can ra s0 s1 s2 s3 s4 /\
    (forall k, In k [3; 4; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros R m rom sp0 can ra s0 s1 s2 s3 s4 ac ar F R8 Rac Mac Rar Aar Mar.
  assert (P1 : mt3o_pre R m ac ar) by (constructor; [exact R8 | exact (mf_R19 _ _ _ _ _ _ _ _ _ _ F) | exact Rac | lia | exact Mac | exact Mar]).
  destruct (mt3o_pmt3oo R m rom ac ar P1 ltac:(constructor)) as (R1 & Hms1 & A8 & A9 & A10 & A19 & Ak1).
  change (mt3o_mem_pmt3oo m R ac ar) with m in Hms1.
  assert (P2 : mt8b_pre R1 m ar) by (constructor; [exact A8 | exact A9 | exact Rar | exact Aar]).
  destruct (mt8b_pmt8b R1 m rom ar P2 ltac:(constructor)) as (R2 & Hms2 & B1 & B8 & B9 & B10 & B11 & B12 & Bk2).
  change (mt8b_mem_pmt8b m R1 ar) with m in Hms2.
  exists R2. split; [exact (msteps_trans SEGS _ _ _ Hms1 Hms2)|].
  split; [exact B1|]. split; [exact B9|]. split; [exact B10|]. split; [exact B11|]. split; [exact B12|].
  assert (KK : forall k, In k [2; 3; 4; 18; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R2 (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))).
  { intros k Hk'. rewrite (Bk2 k ltac:(clear - Hk'; klist Hk')), (Ak1 k ltac:(clear - Hk'; klist Hk')). reflexivity. }
  split.
  - apply (am_frame_regs R R2 m sp0 can ra s0 s1 s2 s3 s4 F).
    + exact (kp_lit R2 R _ KK 2%nat (Z_to_bv 5 2) ltac:(cbn [In]; memb) ltac:(apply bv_eq; reflexivity)).
    + exact (kp_lit R2 R _ KK 18%nat (Z_to_bv 5 18) ltac:(cbn [In]; memb) ltac:(apply bv_eq; reflexivity)).
    + regk Bk2 19%nat. litr2 A19. exact (eq_sym (mf_R19 _ _ _ _ _ _ _ _ _ _ F)).
  - intros k Hk'. apply KK. clear - Hk'. klist Hk'.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem seg_mpw : forall Rf R m rom sp0 can ra s0 s1 s2 s3 s4 ar,
  am_frame Rf m sp0 can ra s0 s1 s2 s3 s4 -> getr R 2 = wa (sp0 + -64) ->
  getr R 1 = wa 335712 -> getr R 10 = wa ar -> getr R 11 = wa 4096 -> getr R 12 = wa 3 ->
  4096 <= ar <= 2^47 -> ar mod 4096 = 0 ->
  stk_ok SEGS m (wa (sp0 + -64)) 1024 -> rdn SEGS m (wa (0 + 614032)) 8 = Some (word_to_le_bytes 8 (wa 4096)) -> 2^20 + 1024 <= sp0 ->
  exists R', msteps SEGS (mkst R (wa 0x53414) m rom) (mkst R' (wa 0x53444) (mpw_store m sp0) rom) /\
    getr R' 17 = wa 226 /\ getr R' 10 = wa ar /\ getr R' 11 = wa 4096 /\ getr R' 12 = wa 3 /\ getr R' 2 = wa (sp0 + -64 + -16) /\
    (forall k, In k [1; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros Rf R m rom sp0 can ra s0 s1 s2 s3 s4 ar F R2sp R1 R10 R11 R12 Rar Aar STK Mpg Hsp.
  pose proof (mf_Rsp _ _ _ _ _ _ _ _ _ _ F) as Rsp. pose proof (mf_Asp _ _ _ _ _ _ _ _ _ _ F) as Asp.
  assert (P3 : mpw_pre R m (sp0 + -64) ar).
  { constructor; [exact R2sp | exact R10 | exact R11 | exact R12 | exact STK | lia | exact Rar | | exact Aar | exact Mpg | lia].
    replace (sp0 + -64) with ((sp0 - 64) + 0) by ring. rewrite Z.add_0_r. clear - Asp. apply Z.mod_divide in Asp; [|lia].
    destruct Asp as (k & ->). replace (k * 16 - 64) with ((k - 4) * 16) by ring. apply Z.mod_mul. lia. }
  destruct (mpw_pmpw R m rom (sp0 + -64) ar P3 ltac:(constructor)) as (R3 & Hms3 & C2 & C10 & C11 & C12 & C13 & C14 & C17 & Ck3).
  change (mpw_mem_pmpw m R (sp0 + -64) ar) with (wbytes m (wa (sp0 + -64 + -8)) (word_to_le_bytes 8 (wa (bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 1))))))) in Hms3.
  replace (wbytes m (wa (sp0 + -64 + -8)) (word_to_le_bytes 8 (wa (bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 1)))))))
    with (mpw_store m sp0) in Hms3.
  2: { unfold mpw_store. replace (getr R (Z_to_bv 5 (Z.of_nat 1))) with (wa 335712) by (symmetry; litr2 R1; reflexivity).
       rewrite u_wa_small by lia. reflexivity. }
  exists R3. split; [exact Hms3|].
  split; [exact C17|]. split; [exact C10|]. split; [exact C11|]. split; [exact C12|]. split; [exact C2|].
  intros k Hk'. apply Ck3. clear - Hk'. klist Hk'.
Qed.

#[using="Type"] Theorem seg_ams : forall Rf R m rom sp0 can ra s0 s1 s2 s3 s4,
  am_frame Rf m sp0 can ra s0 s1 s2 s3 s4 ->
  getr R 2 = wa (sp0 + -64 + -16) -> getr R 10 = wa 0 -> getr R 18 = wa 613952 -> getr R 19 = wa 614096 ->
  rdn SEGS m (wa (sp0 + -64 + -8)) 8 = Some (word_to_le_bytes 8 (wa 335712)) -> 2^20 + 1024 <= sp0 ->
  exists R', msteps SEGS (mkst R (wa 0x53448) m rom) (mkst R' (wa 0x51ec0) m rom) /\ am_frame R' m sp0 can ra s0 s1 s2 s3 s4 /\
    (forall k, In k [3; 4; 8; 9; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros Rf R m rom sp0 can ra s0 s1 s2 s3 s4 F R2 R10 R18 R19 Mra Hsp.
  pose proof (mf_Asp _ _ _ _ _ _ _ _ _ _ F) as Asp. pose proof (mf_Rsp _ _ _ _ _ _ _ _ _ _ F) as Rsp.
  assert (P1 : mpr_pre R m (sp0 + -64)).
  { constructor; [exact R2 | exact R10 | lia | | exact Mra].
    clear - Asp. apply Z.mod_divide in Asp; [|lia]. destruct Asp as (k & ->). replace (k * 16 + -64) with ((k - 4) * 16) by ring. apply Z.mod_mul. lia. }
  destruct (mpr_pmpr R m rom (sp0 + -64) P1 ltac:(constructor)) as (R1 & Hms1 & A1 & A2 & A10 & A11 & Ak1).
  change (mpr_mem_pmpr m R (sp0 + -64)) with m in Hms1.
  assert (P2 : mt9_pre R1 m 0) by (constructor; [exact A10 | lia]).
  destruct (mt9_pmt9 R1 m rom 0 P2 ltac:(constructor)) as (R2' & Hms2 & B10 & Bk2).
  change (mt9_mem_pmt9 m R1 0) with m in Hms2.
  exists R2'. split; [exact (msteps_trans SEGS _ _ _ Hms1 Hms2)|].
  split.
  - apply (am_frame_regs Rf R2' m sp0 can ra s0 s1 s2 s3 s4 F).
    + regk Bk2 2%nat. litr2 A2. exact (eq_sym (mf_R2 _ _ _ _ _ _ _ _ _ _ F)).
    + regk Bk2 18%nat. regk Ak1 18%nat. litr2 R18. exact (eq_sym (mf_R18 _ _ _ _ _ _ _ _ _ _ F)).
    + regk Bk2 19%nat. regk Ak1 19%nat. litr2 R19. exact (eq_sym (mf_R19 _ _ _ _ _ _ _ _ _ _ F)).
  - intros k Hk'. rewrite (Bk2 k ltac:(clear - Hk'; klist Hk')), (Ak1 k ltac:(clear - Hk'; klist Hk')). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma ecall_52f24 : exists w, fetch_word SEGS (wa 0x53444) = Some w /\ is_ecall w = true.
Proof. LiaFast.lf_pins LiaFast.u0. eexists. split; [vm_compute; reflexivity | vm_compute; reflexivity]. Qed.

#[using="Type"] Lemma add4_52f24 : bv_add (wa 0x53444) (w64 4) = wa 0x53448.
Proof. LiaFast.lf_pins LiaFast.u0. apply bv_eq. reflexivity. Qed.

#[using="Type"] Lemma kout_mprotect : forall FORB HTOP L s p eff ans L', koutcome FORB HTOP L s (KMprotect p) eff ans L' ->
  eff = mkEffect (w64 0) [] [(w64 (loc_addr L (LMem p)), w64 PGSZ)] /\ ans = 1 /\ L' = L.
Proof. LiaFast.lf_pins LiaFast.u0. intros FORB HTOP L s p eff ans L' H. inversion H; subst. auto. Qed.

#[using="Type"] Lemma getr_u : forall (R : bvmap 5 word) r v, getr R r = wa v -> 0 <= v < 2^64 -> bv_unsigned (getr R r) = v mod 2^64.
Proof. LiaFast.lf_pins LiaFast.u0. intros R r v H Hv. rewrite H, u_wa_small by exact Hv. rewrite Z.mod_small by exact Hv. reflexivity. Qed.

(* [comment removed for export] *)
Definition am_qpost (HTOP : Z) (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z) (L0 : layout) (s0 : astate) (m0 : word -> option byte)
    (regs0 : bvmap 5 word) (sp0 K ra : Z) : @wpost (option sptr * astate) :=
  fun L' r R' pc m' => exists mt s', r = (Some mt, s') /\ pc = wa ra /\ getr R' 10 = wa (loc_addr L' (LMem mt)) /\
    (forall k, In k [1;2;3;4;8;9;18;19;20;21;22;23;24;25;26;27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr regs0 (Z_to_bv 5 (Z.of_nat k))) /\
    CUT HTOP (mt :: X) R U L' s' m' sp0 K /\ GROW sp0 K L0 s0 m0 L' s' m'.

End AM5.
