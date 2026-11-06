(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3 SeqExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMain.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGeom OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AxMng AxBits MngZ MngRepr MngHeap MngWb MngFree MngFree5 AXF_p4z.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_pd5z.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_tfz MngFreeMem AXG_ffstep.

Module MngFreeGeo.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMain.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGeom OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng MngRepr MngImage MngHeap MngWb MngFree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Lemma free_cells_geom : forall L s g am i fr spz,
  WF s -> layout_ok L s -> In (g, am, i, fr) (frames s) ->
  (forall rg, In rg (footprint s) -> loc_addr L (fst rg) + snd rg <= spz - 1024) ->
  5 <= loc_addr L (LMem (frame_ptr am i fr)) <= spz - 1024 /\
  1 <= loc_addr L (LMem g) + 28 /\ loc_addr L (LMem g) + 40 <= spz - 1024 /\
  (loc_addr L (LMem (frame_ptr am i fr)) <= loc_addr L (LMem g) + 28 \/ loc_addr L (LMem g) + 32 <= loc_addr L (LMem (frame_ptr am i fr)) - 3).
Proof.
  intros L s g am i fr spz HW HL HF HFP.
  pose proof (get_meta_ok s g am i fr HW HF) as GM. cbn zeta in GM.
  destruct GM as (Ch4 & Ch3 & Ch16 & Cgm & Cmem & Cav & Cfr & Cbits & _).
  assert (FP : forall c, In c (image s) -> 1 <= loc_addr L (mc_loc c) /\ loc_addr L (mc_loc c) + Z.of_nat (mc_w c) <= spz - 1024).
  { intros c Hc. destruct (image_in_footprint s L c HW HL Hc) as (rg & Hrg & Hincl).
    pose proof (proj2 (proj2 (proj2 HL)) rg Hrg) as R. pose proof (HFP rg Hrg) as S.
    unfold range_incl, cell_range, crange in *. cbn [fst snd] in *. lia. }
  pose proof (FP _ Ch4) as F4. pose proof (FP _ Ch16) as F16. pose proof (FP _ Cfr) as FF. pose proof (FP _ Cbits) as FB.
  cbn [mc_loc mc_w] in F4, F16, FF, FB. rewrite !loc_padd in F4, F16, FF, FB. unfold META_freed, META_bits in FF, FB.
  assert (D3F : ranges_disjoint (cell_range L (MCell (LMem (padd (frame_ptr am i fr) (-3))) 1 (VZ (hdr_byte3 am i fr))))
                                (cell_range L (MCell (LMem (padd g META_freed)) 4 (VZ (am_freed am))))).
  { apply (image_pair_disjoint s L); [exact HW | exact HL | exact Ch3 | exact Cfr | intro E; injection E; intros; discriminate]. }
  assert (D16F : ranges_disjoint (cell_range L (MCell (LMem (padd (frame_ptr am i fr) (-2))) 2 (VZ (hdr_off16 am i fr))))
                                 (cell_range L (MCell (LMem (padd g META_freed)) 4 (VZ (am_freed am))))).
  { apply (image_pair_disjoint s L); [exact HW | exact HL | exact Ch16 | exact Cfr | intro E; injection E; intros; discriminate]. }
  unfold ranges_disjoint, cell_range in D3F, D16F. cbn [mc_loc mc_w fst snd] in D3F, D16F. rewrite !loc_padd in D3F, D16F.
  unfold META_freed in D3F, D16F. cbn [Z.of_nat Pos.of_succ_nat] in *. lia.
Qed.

End MngFreeGeo.

From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_pd5z.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_pd5z.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_pd5z.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_pd5z.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_pd5z.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_pd5z.

Module MngFreeM.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGeom OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AxMng AxBits MngZ MngRepr MngHeap MngFree MngFree5 MngGM.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_pd5z.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_pd5z.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_pd5z.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_pd5z.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_pd5z.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_pd5z.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxMng OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxBits OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngZ OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngRepr OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngHeap OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngFree OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngFree5 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngGM OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_pd5z.AXF_p4mz OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_pd5z.AXF_p5mz OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_pd5z.AXF_pd4z OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_pd5z OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_pd5z.AXF_pe4z OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_pd5z.AXF_pe5z.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Record free_gen4 (regs : bvmap 5 word) (m : word -> option byte) (h3 off16 G avail freed W secret sz B : Z) : Prop := {
  fg_HP : getr regs 10 = wa (16 * off16 + B + 16) ;
  fg_Rsp : 2^20 <= bv_unsigned (getr regs 2) <= 2^47 ;
  fg_Asp : bv_unsigned (getr regs 2) mod 16 = 0 ;
  fg_HSTK : stk_ok SEGS m (getr regs 2) 1024 ;
  fg_RB : 1 <= B <= 2^63-1 ;
  fg_AB : B mod 16 = 0 ;
  fg_Roff : 0 <= off16 <= 65535 ;
  fg_RPB : 1 <= 16 * off16 + B <= 2^63-1 ;
  fg_Rh3 : 0 <= h3 <= 159 ;
  fg_RG : 1 <= G <= 2^63-1 ;
  fg_Rav : 0 <= avail <= 2^32 - 1 ;
  fg_Rfr : 0 <= freed <= 2^32 - 1 ;
  fg_RW : 0 <= W <= 2^64 - 1 ;
  fg_Rsz : 1 <= sz <= 2^59 ;
  fg_Rsec : 0 <= secret <= 2^64 - 1 ;
  fg_REND : 1 <= 16 * sz + (B + 16 * sz * Z.land h3 31) <= 2^63-1 ;
  fg_RENDR : 1 <= 16 * sz + (B + (-1 * Z.shiftr h3 5 + 16 * sz * Z.land h3 31)) <= 2^63-1 ;
  fg_Mh4 : rdn SEGS m (wa (16 * off16 + B + 12)) 1 = Some (word_to_le_bytes 1 (wa 0)) ;
  fg_Mh3 : rdn SEGS m (wa (16 * off16 + B + 13)) 1 = Some (word_to_le_bytes 1 (wa h3)) ;
  fg_Moff : rdn SEGS m (wa (16 * off16 + B + 14)) 2 = Some (word_to_le_bytes 2 (wa off16)) ;
  fg_Mmeta : rdn SEGS m (wa (B + 0)) 8 = Some (word_to_le_bytes 8 (wa G)) ;
  fg_Mmem : rdn SEGS m (wa (G + 16)) 8 = Some (word_to_le_bytes 8 (wa B)) ;
  fg_Mav : rdn SEGS m (wa (G + 24)) 4 = Some (word_to_le_bytes 4 (wa avail)) ;
  fg_Mfr : rdn SEGS m (wa (G + 28)) 4 = Some (word_to_le_bytes 4 (wa freed)) ;
  fg_MW : rdn SEGS m (wa (G + 32)) 8 = Some (word_to_le_bytes 8 (wa W)) ;
  fg_Marea : rdn SEGS m (wa (4096 * (G / 4096) + 0)) 8 = Some (word_to_le_bytes 8 (wa secret)) ;
  fg_Mctx : rdn SEGS m (wa (0 + 614104)) 8 = Some (word_to_le_bytes 8 (wa secret)) ;
  fg_Mnl : rdn SEGS m (wa (0 + 613987)) 1 = Some (word_to_le_bytes 1 (wa 0)) ;
  fg_Mend : rdn SEGS m (wa (16 * sz + (B + 16 * sz * Z.land h3 31) + 12)) 1 = Some (word_to_le_bytes 1 (wa 0)) ;
  fg_Mendr : rdn SEGS m (wa (16 * sz + (B + (-1 * Z.shiftr h3 5 + 16 * sz * Z.land h3 31)) + 12)) 1 = Some (word_to_le_bytes 1 (wa 0)) ;
  fg_Whdr : (forall d k, 0 <= d -> d + Z.of_nat k <= 4 -> store_ok SEGS m (wa (16 * off16 + B + 12 + d)) k = true) ;
  fg_Wmeta : (forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (G + 24 + d)) k = true) ;
  fg_D1 : 16 * sz + (B + 16 * sz * Z.land h3 31) + 12 + 1 <= bv_unsigned (getr regs 2) + -1024 ;
  fg_D2 : 16 * sz + (B + (-1 * Z.shiftr h3 5 + 16 * sz * Z.land h3 31)) + 12 + 1 <= bv_unsigned (getr regs 2) + -1024 ;
  fg_D3 : 16 * off16 + B + 12 + 4 <= bv_unsigned (getr regs 2) + -1024 ;
  fg_D4 : B + 0 + 8 <= bv_unsigned (getr regs 2) + -1024 ;
  fg_D5 : G + 0 + 40 <= bv_unsigned (getr regs 2) + -1024 ;
  fg_D6 : 4096 * (G / 4096) + 0 + 8 <= bv_unsigned (getr regs 2) + -1024 ;
  fg_D7 : (G + 0 + 40 <= 16 * off16 + B + 12 \/ 16 * off16 + B + 12 + 4 <= G + 0) ;
  fg_D8 : (0 + 613987 + 1 <= 16 * off16 + B + 12 \/ 16 * off16 + B + 12 + 4 <= 0 + 613987) ;
  fg_A1 : Z.land h3 31 <= Z.land W 31 ;
  fg_A2 : Z.testbit avail (Z.land h3 31) = false ;
  fg_A3 : Z.testbit freed (Z.land h3 31) = false ;
  fg_A5 : Z.shiftr h3 5 <= -16 * off16 + (16 * sz + 16 * sz * Z.land h3 31) + -4 ;
  fg_HIMG : 16 * off16 + B + 16 <= 0x10000 \/ 0x97000 <= 16 * off16 + B + 12 ;
  fg_GIMG : G + 40 <= 0x10000 \/ 0x97000 <= G ;
  fg_AG : G mod 8 = 0
}.

Theorem free_gen4_of_model : forall L s (regs : bvmap 5 word) (m : word -> option byte) g am i fr,
  WF s -> repr L s (bview SEGS m) -> markers_hold L s (bview SEGS m) ->
  In (g, am, i, fr) (frames s) -> fr_kind fr = FUser -> rsv_code am fr < 5 ->
  ly_ctx L = 0x95ed8 ->
  getr regs 10 = wa (loc_addr L (LMem (frame_ptr am i fr))) ->
  rdn SEGS m (wa 613987) 1 = Some (word_to_le_bytes 1 (wa 0)) ->
  2^20 <= bv_unsigned (getr regs 2) <= 2^47 -> bv_unsigned (getr regs 2) mod 16 = 0 -> stk_ok SEGS m (getr regs 2) 1024 ->
  (forall rg, In rg (footprint s) -> loc_addr L (fst rg) + snd rg <= bv_unsigned (getr regs 2) - 1024) ->
  (forall rg, In rg (footprint s) -> fst rg <> LCtx 0 -> ranges_disjoint (crange L rg) (0x10000, 0x87000)) ->
  free_gen4 regs m (hdr_byte3 am i fr) (hdr_off16 am i fr) (loc_addr L (LMem g)) (am_avail am) (am_freed am) (meta_bits am)
           (ly_sec L mod 2^64) (stride_of am / 16) (loc_addr L (LMem (am_mem am))).
Proof.
  intros L s regs m g am i fr HW HR HM HF Hk Hrc Hctx HP Hnl Rsp Asp HSTK HFP HAP.
  pose proof (get_meta_ok s g am i fr HW HF) as GM. cbn zeta in GM.
  destruct GM as (Ch4 & Ch3 & Ch16 & Cgm & Cmem & Cav & Cfr & Cbits & Geo & (a & k & Ha & Hk0 & Hga & Carea & Csec) & Hland & Hasrt & _).
  destruct (in_frames_inv s g am i fr HF) as (Hu & Hi & Hfri).
  apply (used_metas_usedX s g am HW) in Hu as Hux.
  pose proof (inv_groups HW g am Hux) as (Gm & Gml & Gsl & Gcl & Gmp & Gns).
  pose proof (Gsl i Hi) as (S1 & S2 & S3). rewrite Hfri in S3. destruct S3 as (Hal & _ & FOK & Hhdr).
  destruct FOK as (Fn & Foff & Ffit & F16 & _).
  destruct Gm as (Mlast & Maidx & Mlen & Mav0 & Mfr0 & Mdisj & Mabove & _ & _).
  destruct (masks_range_inv [] None U0 s g am HW Hux) as (_ & _ & _ & Rsc63 & Rml0).
  set (p := frame_ptr am i fr) in *.
  set (B := loc_addr L (LMem (am_mem am))).
  set (G := loc_addr L (LMem g)).
  set (h3 := hdr_byte3 am i fr) in *.
  set (off16 := hdr_off16 am i fr) in *.
  set (sz := stride_of am / 16).
  assert (Hstr1 : stride_of am = 16 * sz /\ 1 <= sz).
  { unfold sz, stride_of. destruct Gcl as [(C63 & CL0 & CML & _) | (Csc & _)].
    - rewrite CL0. replace ((0 =? 0) && negb (am_maplen am =? 0)) with true by (destruct (Z.eqb_spec (am_maplen am) 0); [lia | reflexivity]).
      replace (am_maplen am * 4096 - UNIT) with ((am_maplen am * 256 - 1) * 16) by (unfold UNIT; ring). rewrite Z.div_mul by lia. split; [ring | lia].
    - destruct ((am_last am =? 0) && negb (am_maplen am =? 0)) eqn:E.
      + apply andb_prop in E as [_ E]. apply negb_true_iff, Z.eqb_neq in E.
        replace (am_maplen am * 4096 - UNIT) with ((am_maplen am * 256 - 1) * 16) by (unfold UNIT; ring). rewrite Z.div_mul by lia. split; [ring | lia].
      + unfold class_size, UNIT. rewrite (Z.mul_comm 16), Z.div_mul by lia. pose proof (size_classes_range _ Csc). split; [ring | lia]. }
  destruct Hstr1 as (Hstr & Rsz1).
  assert (PADDR : loc_addr L (LMem p) = 16 * off16 + B + 16).
  { pose proof (f_equal (fun q => loc_addr L (LMem q)) Geo) as E. cbn beta in E. rewrite loc_padd in E.
    unfold B. rewrite <- E. unfold UNIT. ring. }
  destruct HR as (HL & HC & HFM).
  pose proof HL as (Lctx & Lal & Ldisj & Lrng).
  (* [comment removed for export] *)
  destruct (used_group_region [] None U0 s g am HW Hux) as (rgG & HrG & HkG & HlG & Ho0 & Hext & _).
  assert (FG : In (LMem (SP (prid (am_mem am)) 0), rg_len rgG) (footprint s)) by (apply footprint_region_In; assumption).
  pose proof (Lrng _ FG) as RgG. cbn [crange fst snd loc_addr] in RgG.
  pose proof (HFP _ FG) as SpG. cbn [fst snd loc_addr] in SpG.
  assert (EB : B = ly_reg L (prid (am_mem am)) + poff (am_mem am)) by (unfold B; destruct (am_mem am); reflexivity).
  (* [comment removed for export] *)
  pose proof (inv_areas HW) as (AND & AOK & _).
  destruct (AOK a Ha) as (ra & oa & rga & Ea & Oal & Opg & Hra & Hla & Hofit & Hkind).
  assert (FA : In (LMem a, PGSZ) (footprint s)) by (unfold footprint; right; apply in_app_iff; left; apply (in_map (fun a0 => (LMem a0, PGSZ))); exact Ha).
  pose proof (Lrng _ FA) as RgA. cbn [crange fst snd] in RgA.
  pose proof (HFP _ FA) as SpA. cbn [fst snd] in SpA.
  pose proof (Lal ra rga Hra Hla) as Aal.
  assert (EG : G = loc_addr L (LMem a) + 24 + 40 * k) by (unfold G; rewrite Hga, loc_padd; unfold AREA_HDR, META_SIZE; ring).
  assert (EA : loc_addr L (LMem a) = ly_reg L ra + oa) by (rewrite Ea; reflexivity).
  assert (HAG : 4096 * (G / 4096) = loc_addr L (LMem a)).
  { rewrite EG, EA. unfold PGSZ in *. clear - Oal Aal Hk0. unfold METAS_PER_AREA in Hk0.
    assert (E : (ly_reg L ra + oa) = 4096 * ((ly_reg L ra + oa) / 4096)).
    { pose proof (Z.div_mod (ly_reg L ra + oa) 4096 ltac:(lia)) as D. rewrite Zplus_mod, Aal, Oal in D. cbn in D. lia. }
    rewrite E. replace (4096 * ((ly_reg L ra + oa) / 4096) + 24 + 40 * k) with ((24 + 40 * k) + ((ly_reg L ra + oa) / 4096) * 4096) by ring.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. ring. }
  idtac "T0". Time assert (Hpr : forall x, 0 <= x -> (forall j, 32 <= j -> Z.testbit x j = false) -> 0 <= x <= 2^32 - 1).
  { idtac "HPR". time (intros x Hx Hb; split; [exact Hx|]).  assert (x < 2^32); [|lia].
    rewrite <- (Z.mod_small x (2^32)) at 1; [apply Z.mod_pos_bound; lia|]. split; [exact Hx|].
    destruct (Z.eq_dec x 0) as [->|Hnz]; [lia|]. apply Z.log2_lt_cancel. rewrite Z.log2_pow2 by lia.
    destruct (Z.lt_ge_cases (Z.log2 x) 32) as [Hl|Hg]; [exact Hl|]. exfalso.
    pose proof (Z.bit_log2 x ltac:(lia)) as Hbit. rewrite Hb in Hbit by lia. discriminate. }
  assert (Rav : 0 <= am_avail am <= 2^32 - 1).
  { idtac "RAV". Time (apply Hpr; [exact Mav0|]; intros j Hj; apply (proj1 (Mabove j ltac:(clear - Mlast Hj; lia)))). }
  assert (Rfr : 0 <= am_freed am <= 2^32 - 1).
  { Time (apply Hpr; [exact Mfr0|]; intros j Hj; apply (proj2 (Mabove j ltac:(clear - Mlast Hj; lia)))). }
  (* [comment removed for export] *)
  assert (Hrsv0 : 0 <= frame_rsv am fr) by (clear - Ffit; unfold frame_rsv, UNIT, IB in *; lia).
  assert (Hrceq : rsv_code am fr = frame_rsv am fr).
  { clear - Hrc Hrsv0. unfold rsv_code, frame_rsv in *. destruct (5 <=? _) eqn:E; [apply Z.leb_le in E; lia | reflexivity]. }
  assert (Eh3 : h3 = i + 32 * rsv_code am fr) by (unfold h3, hdr_byte3; rewrite Hk; reflexivity).
  assert (Eoff : off16 = sz * i + fr_off fr).
  { unfold off16, hdr_off16. rewrite Hstr. unfold UNIT. replace (16 * sz * i) with ((sz * i) * 16) by ring.
    rewrite Z.div_mul by lia. reflexivity. }
  assert (Hext' : poff (am_mem am) + 16 + 16 * sz * am_last am + 16 * sz <= rg_len rgG).
  { clear - Hext Hstr. unfold group_extent, UNIT, IB in Hext. rewrite Hstr in Hext. lia. }
  assert (Rsz : 1 <= sz <= 2^59).
  { split; [exact Rsz1|]. assert (0 <= sz * am_last am) by (apply Z.mul_nonneg_nonneg; lia).
    clear - Rsz1 Hext' RgG Mlast H Ho0. lia. }
  assert (Hsi : 0 <= sz * i <= sz * am_last am) by (clear - Rsz Hi; split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg_l; lia]).
  assert (Ho16 : 0 <= fr_off fr /\ 16 * fr_off fr + fr_n fr <= 16 * sz - 4) by (clear - Foff Ffit Hstr; unfold UNIT, IB in *; rewrite Hstr in Ffit; lia).
  assert (Hfoff : fr_off fr < sz) by (clear - Ho16 Fn; lia).
  assert (Eshr : Z.shiftr h3 5 = rsv_code am fr).
  { rewrite Eh3. rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32.
    replace (i + 32 * rsv_code am fr) with (i + rsv_code am fr * 32) by ring. rewrite Z.div_add by lia.
    rewrite Z.div_small by (clear - Hi Mlast; lia). ring. }
  assert (Hsp64 : bv_unsigned (getr regs 2) < 2^64) by (clear - Rsp; lia).
  (* [comment removed for export] *)
  constructor.
  - rewrite HP, PADDR. reflexivity.
  - exact Rsp.
  - exact Asp.
  - exact HSTK.
  - rewrite EB. clear - RgG Ho0 Hext' Hsi Rsz. lia.
  - rewrite EB. pose proof (used_group_aligned [] None U0 s HW 64%nat g am Hux ltac:(clear - Rsc63; lia)) as Al16.
    pose proof (Lal _ _ HrG HlG) as AlR. clear - Al16 AlR. unfold PGSZ in *.
    rewrite Zplus_mod, Al16. replace (ly_reg L (prid (am_mem am))) with (4096 * (ly_reg L (prid (am_mem am)) / 4096)) at 1
      by (pose proof (Z.div_mod (ly_reg L (prid (am_mem am))) 4096 ltac:(lia)); lia).
    replace (4096 * (ly_reg L (prid (am_mem am)) / 4096)) with ((256 * (ly_reg L (prid (am_mem am)) / 4096)) * 16) by ring.
    rewrite Z_mod_mult. reflexivity.
  - clear - F16 Eoff Rsz Hsi Ho16. lia.
  - rewrite EB, Eoff. clear - RgG Ho0 Hext' Hsi Rsz Ho16 Hfoff Hi. nia.
  - rewrite Eh3. clear - Hrc Hrceq Hrsv0 Hi Mlast. lia.
  - rewrite EG. clear - RgA Hk0. unfold METAS_PER_AREA, PGSZ in *. lia.
  - exact Rav.
  - exact Rfr.
  - exact (meta_bits_range_inv [] None U0 s g am L HW Hux HL).
  - exact Rsz.
  - pose proof (Z.mod_pos_bound (ly_sec L) (2^64) ltac:(lia)). clear - H. lia.
  - rewrite Hland, EB. clear - RgG Ho0 Hext' Hsi Rsz. lia.
  - rewrite Hland, Eshr, EB. clear - RgG Ho0 Hext' Hsi Rsz Hrc Hrceq Hrsv0. lia.
  - cellrd HC Ch4 Hr. fold p in Hr. rewrite PADDR in Hr. rdn_by Hr.
  - cellrd HC Ch3 Hr. fold p in Hr. rewrite PADDR in Hr. rdn_by Hr.
  - cellrd HC Ch16 Hr. fold p in Hr. rewrite PADDR in Hr. rdn_by Hr.
  - cellrd HC Cgm Hr. fold B G in Hr. rdn_by Hr.
  - cellrd HC Cmem Hr. fold B G in Hr. unfold META_mem in Hr. rdn_by Hr.
  - cellrd HC Cav Hr. fold G in Hr. unfold META_avail in Hr. rdn_by Hr.
  - cellrd HC Cfr Hr. fold G in Hr. unfold META_freed in Hr. rdn_by Hr.
  - cellrd HC Cbits Hr. fold G in Hr. unfold META_bits in Hr. rdn_by Hr.
  - cellrd HC Carea Hr. rewrite <- HAG in Hr. replace (4096 * (G / 4096) + 0) with (4096 * (G / 4096)) by ring.
    rewrite Hr. f_equal. apply le_wa_eqm; [|apply Nat.leb_le; reflexivity]. change (8 * Z.of_nat 8) with 64. rewrite Z.mod_mod by lia. reflexivity.
  - cellrd HC Csec Hr. cbn [loc_addr] in Hr. rewrite Hctx in Hr. unfold CTX_secret in Hr.
    replace (0 + 614104) with (0x95ed8 + 0) by reflexivity.
    rewrite Hr. f_equal. apply le_wa_eqm; [|apply Nat.leb_le; reflexivity]. change (8 * Z.of_nat 8) with 64. rewrite Z.mod_mod by lia. reflexivity.
  - exact Hnl.
  - assert (Cend : In (MCell (LMem (slot_end am i)) 1 (VZ 0)) (markers s)) by (apply (In_markers s g am i fr _ HF Hk); apply in_eq).
    cellrd HM Cend Hr. unfold slot_end, slot_start in Hr. rewrite !loc_padd, Hstr in Hr. fold B in Hr. unfold UNIT, IB in Hr.
    rewrite Hland. rdn_by Hr.
  - rewrite Hland, Eshr, Hrceq.
    destruct (Z.ltb_spec 0 (frame_rsv am fr)) as [Hpos|Hzr].
    + assert (Cr : In (MCell (LMem (padd (slot_end am i) (- frame_rsv am fr))) 1 (VZ 0)) (markers s)).
      { apply (In_markers s g am i fr _ HF Hk). unfold marker_cells. apply in_cons. apply in_or_app. left.
        replace (0 <? frame_rsv am fr) with true by (symmetry; apply Z.ltb_lt; exact Hpos). apply in_eq. }
      cellrd HM Cr Hr. unfold slot_end, slot_start in Hr. rewrite !loc_padd, Hstr in Hr. fold B in Hr. unfold UNIT, IB in Hr.
      rdn_by Hr.
    + assert (Cend : In (MCell (LMem (slot_end am i)) 1 (VZ 0)) (markers s)) by (apply (In_markers s g am i fr _ HF Hk); apply in_eq).
      cellrd HM Cend Hr. unfold slot_end, slot_start in Hr. rewrite !loc_padd, Hstr in Hr. fold B in Hr. unfold UNIT, IB in Hr.
      replace (frame_rsv am fr) with 0 by (clear - Hzr Hrsv0; lia). rdn_by Hr.
  - (* [comment removed for export] *)
    apply (store_ok_of_bytes SEGS m (16 * off16 + B + 12) 4). intros j Hj.
    pose proof (proj1 (Forall_forall _ _) HC _ Ch4) as K4. pose proof (proj1 (Forall_forall _ _) HC _ Ch3) as K3.
    pose proof (proj1 (Forall_forall _ _) HC _ Ch16) as K16.
    assert (E4 : loc_addr L (mc_loc (MCell (LMem (padd p (-4))) 1 (VZ 0))) = 16 * off16 + B + 12) by (cbn [mc_loc]; rewrite loc_padd; fold p; rewrite PADDR; ring).
    assert (E3 : loc_addr L (mc_loc (MCell (LMem (padd p (-3))) 1 (VZ h3))) = 16 * off16 + B + 13) by (cbn [mc_loc]; rewrite loc_padd; fold p; rewrite PADDR; ring).
    assert (E16 : loc_addr L (mc_loc (MCell (LMem (padd p (-2))) 2 (VZ off16))) = 16 * off16 + B + 14) by (cbn [mc_loc]; rewrite loc_padd; fold p; rewrite PADDR; ring).
    assert (Hj' : j = 0 \/ j = 1 \/ j = 2 \/ j = 3) by (clear - Hj; lia).
    destruct Hj' as [ -> | [ -> | [ -> | -> ] ] ].
    + pose proof (holds_wview SEGS L m _ 0 K4 ltac:(intros z Hz0; discriminate) ltac:(cbn; lia)) as W. rewrite E4 in W. exact W.
    + pose proof (holds_wview SEGS L m _ 0 K3 ltac:(intros z Hz0; discriminate) ltac:(cbn; lia)) as W. rewrite E3 in W.
      replace (16 * off16 + B + 12 + 1) with (16 * off16 + B + 13 + 0) by ring. exact W.
    + pose proof (holds_wview SEGS L m _ 0 K16 ltac:(intros z Hz0; discriminate) ltac:(cbn; lia)) as W. rewrite E16 in W.
      replace (16 * off16 + B + 12 + 2) with (16 * off16 + B + 14 + 0) by ring. exact W.
    + pose proof (holds_wview SEGS L m _ 1 K16 ltac:(intros z Hz0; discriminate) ltac:(cbn; lia)) as W. rewrite E16 in W.
      replace (16 * off16 + B + 12 + 3) with (16 * off16 + B + 14 + 1) by ring. exact W.
  - (* [comment removed for export] *)
    apply (store_ok_of_bytes SEGS m (G + 24) 8). intros j Hj.
    pose proof (proj1 (Forall_forall _ _) HC _ Cav) as Ka. pose proof (proj1 (Forall_forall _ _) HC _ Cfr) as Kf.
    assert (Ea' : loc_addr L (mc_loc (MCell (LMem (padd g META_avail)) 4 (VZ (am_avail am)))) = G + 24) by (cbn [mc_loc]; rewrite loc_padd; reflexivity).
    assert (Ef' : loc_addr L (mc_loc (MCell (LMem (padd g META_freed)) 4 (VZ (am_freed am)))) = G + 28) by (cbn [mc_loc]; rewrite loc_padd; reflexivity).
    destruct (Z.ltb_spec j 4) as [Hl|Hg].
    + pose proof (holds_wview SEGS L m _ j Ka ltac:(intros z Hz0; discriminate) ltac:(cbn; clear - Hj Hl; lia)) as W. rewrite Ea' in W. exact W.
    + pose proof (holds_wview SEGS L m _ (j - 4) Kf ltac:(intros z Hz0; discriminate) ltac:(cbn; clear - Hj Hg; lia)) as W. rewrite Ef' in W.
      replace (G + 24 + j) with (G + 28 + (j - 4)) by ring. exact W.
  - rewrite Hland, EB. clear - SpG Ho0 Hext' Hsi Rsz. lia.
  - rewrite Hland, Eshr, Hrceq, EB. clear - SpG Ho0 Hext' Hsi Rsz Hrsv0. lia.
  - rewrite EB, Eoff. clear - SpG Ho0 Hext' Hsi Rsz Ho16 Hfoff. nia.
  - rewrite EB. clear - SpG Ho0 Hext' Hsi Rsz. lia.
  - rewrite EG. clear - SpA Hk0. unfold METAS_PER_AREA, PGSZ in *. lia.
  - rewrite HAG. clear - SpA. unfold PGSZ in *. lia.
  - assert (Hne : (LMem a, PGSZ) <> (LMem (SP (prid (am_mem am)) 0), rg_len rgG)).
    { rewrite Ea. intro E. injection E as E1 E2. clear - E2 Opg. unfold PGSZ in *. lia. }
    destruct (pairwise_map_In _ (crange L) _ _ _ Ldisj FA FG Hne) as [D|D];
      unfold ranges_disjoint in D; cbn [crange fst snd] in D; change (loc_addr L (LMem (SP (prid (am_mem am)) 0))) with (ly_reg L (prid (am_mem am)) + 0) in D.
    + rewrite EG, EB, Eoff. clear - D Ho0 Hext' Hsi Rsz Ho16 Hfoff Hk0. unfold METAS_PER_AREA, PGSZ in *. nia.
    + rewrite EG, EB, Eoff. clear - D Ho0 Hext' Hsi Rsz Ho16 Hfoff Hk0. unfold METAS_PER_AREA, PGSZ in *. nia.
  - pose proof (HAP _ FG ltac:(discriminate)) as D. unfold ranges_disjoint in D. cbn [crange fst snd loc_addr] in D.
    rewrite EB, Eoff. clear - D Ho0 Hext' Hsi Rsz Ho16 Hfoff. nia.
  - assert (EW : Z.land (meta_bits am) 31 = am_last am).
    { unfold meta_bits. replace (am_last am + 32 + 64 * am_sc am + 4096 * am_maplen am) with (am_last am + 32 * (1 + 2 * am_sc am + 128 * am_maplen am)) by ring.
      apply land31; clear - Mlast Rsc63 Rml0; lia. }
    rewrite Hland, EW. exact (proj2 Hi).
  - unfold allocated in Hal. apply negb_true_iff in Hal. rewrite Z.lor_spec in Hal. apply orb_false_iff in Hal.
    rewrite Hland. exact (proj1 Hal).
  - unfold allocated in Hal. apply negb_true_iff in Hal. rewrite Z.lor_spec in Hal. apply orb_false_iff in Hal.
    rewrite Hland. exact (proj2 Hal).
  - rewrite Eshr, Hrceq, Hland, Eoff. unfold frame_rsv. rewrite Hstr. clear - Ho16 Fn. unfold UNIT, IB. lia.
  - pose proof (HAP _ FG ltac:(discriminate)) as D. unfold ranges_disjoint in D. cbn [crange fst snd loc_addr] in D.
    rewrite EB, Eoff. clear - D Ho0 Hext' Hsi Rsz Ho16 Hfoff. nia.
  - pose proof (HAP _ FA ltac:(discriminate)) as D. unfold ranges_disjoint in D. cbn [crange fst snd] in D.
    rewrite EG. clear - D Hk0. unfold METAS_PER_AREA, PGSZ in *. lia.
  - rewrite EG, EA. clear - Oal Aal. unfold PGSZ in *. rewrite Zplus_mod, (Zplus_mod (ly_reg L ra + oa) 24), (Zplus_mod (ly_reg L ra) oa).
    replace (ly_reg L ra mod 8) with 0. 2:{ pose proof (Z.div_mod (ly_reg L ra) 4096 ltac:(lia)) as E. rewrite Aal in E. rewrite E.
      replace (4096 * (ly_reg L ra / 4096) + 0) with ((512 * (ly_reg L ra / 4096)) * 8) by ring. rewrite Z_mod_mult. reflexivity. }
    replace (oa mod 8) with 0. 2:{ pose proof (Z.div_mod oa 4096 ltac:(lia)) as E. rewrite Oal in E. rewrite E.
      replace (4096 * (oa / 4096) + 0) with ((512 * (oa / 4096)) * 8) by ring. rewrite Z_mod_mult. reflexivity. }
    replace (40 * k) with (k * 8 * 5) by ring. rewrite Z.mul_comm, Z.mul_assoc, Z_mod_mult. cbn. reflexivity.
Qed.

Record free_gen5 (regs : bvmap 5 word) (m : word -> option byte) (h3 off16 G avail freed W secret sz B rsv : Z) : Prop := {
  g5_HP : getr regs 10 = wa (16 * off16 + B + 16) ;
  g5_Rsp : 2^20 <= bv_unsigned (getr regs 2) <= 2^47 ;
  g5_Asp : bv_unsigned (getr regs 2) mod 16 = 0 ;
  g5_HSTK : stk_ok SEGS m (getr regs 2) 1024 ;
  g5_RB : 1 <= B <= 2^63-1 ;
  g5_AB : B mod 16 = 0 ;
  g5_Roff : 0 <= off16 <= 65535 ;
  g5_RPB : 1 <= 16 * off16 + B <= 2^63-1 ;
  g5_Rh3 : 160 <= h3 <= 191 ;
  g5_RG : 1 <= G <= 2^63-1 ;
  g5_Rav : 0 <= avail <= 2^32 - 1 ;
  g5_Rfr : 0 <= freed <= 2^32 - 1 ;
  g5_RW : 0 <= W <= 2^64 - 1 ;
  g5_Rsz : 1 <= sz <= 2^59 ;
  g5_Rsec : 0 <= secret <= 2^64 - 1 ;
  g5_REND : 1 <= 16 * sz + (B + 16 * sz * Z.land h3 31) <= 2^63-1 ;
  g5_RENDR : 1 <= 16 * sz + (B + (16 * sz * Z.land h3 31 + -1 * rsv)) <= 2^63-1 ;
  g5_Mh4 : rdn SEGS m (wa (16 * off16 + B + 12)) 1 = Some (word_to_le_bytes 1 (wa 0)) ;
  g5_Mh3 : rdn SEGS m (wa (16 * off16 + B + 13)) 1 = Some (word_to_le_bytes 1 (wa h3)) ;
  g5_Moff : rdn SEGS m (wa (16 * off16 + B + 14)) 2 = Some (word_to_le_bytes 2 (wa off16)) ;
  g5_Mmeta : rdn SEGS m (wa (B + 0)) 8 = Some (word_to_le_bytes 8 (wa G)) ;
  g5_Mmem : rdn SEGS m (wa (G + 16)) 8 = Some (word_to_le_bytes 8 (wa B)) ;
  g5_Mav : rdn SEGS m (wa (G + 24)) 4 = Some (word_to_le_bytes 4 (wa avail)) ;
  g5_Mfr : rdn SEGS m (wa (G + 28)) 4 = Some (word_to_le_bytes 4 (wa freed)) ;
  g5_MW : rdn SEGS m (wa (G + 32)) 8 = Some (word_to_le_bytes 8 (wa W)) ;
  g5_Marea : rdn SEGS m (wa (4096 * (G / 4096) + 0)) 8 = Some (word_to_le_bytes 8 (wa secret)) ;
  g5_Mctx : rdn SEGS m (wa (0 + 614104)) 8 = Some (word_to_le_bytes 8 (wa secret)) ;
  g5_Mnl : rdn SEGS m (wa (0 + 613987)) 1 = Some (word_to_le_bytes 1 (wa 0)) ;
  g5_Mend : rdn SEGS m (wa (16 * sz + (B + 16 * sz * Z.land h3 31) + 12)) 1 = Some (word_to_le_bytes 1 (wa 0)) ;
  g5_Mendr : rdn SEGS m (wa (16 * sz + (B + (16 * sz * Z.land h3 31 + -1 * rsv)) + 12)) 1 = Some (word_to_le_bytes 1 (wa 0)) ;
  g5_Whdr : (forall d k, 0 <= d -> d + Z.of_nat k <= 4 -> store_ok SEGS m (wa (16 * off16 + B + 12 + d)) k = true) ;
  g5_Wmeta : (forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (G + 24 + d)) k = true) ;
  g5_D1 : 16 * sz + (B + 16 * sz * Z.land h3 31) + 12 + 1 <= bv_unsigned (getr regs 2) + -1024 ;
  g5_D2 : 16 * sz + (B + (16 * sz * Z.land h3 31 + -1 * rsv)) + 12 + 1 <= bv_unsigned (getr regs 2) + -1024 ;
  g5_D3 : 16 * off16 + B + 12 + 4 <= bv_unsigned (getr regs 2) + -1024 ;
  g5_D4 : B + 0 + 8 <= bv_unsigned (getr regs 2) + -1024 ;
  g5_D5 : G + 0 + 40 <= bv_unsigned (getr regs 2) + -1024 ;
  g5_D6 : 4096 * (G / 4096) + 0 + 8 <= bv_unsigned (getr regs 2) + -1024 ;
  g5_D7 : (G + 0 + 40 <= 16 * off16 + B + 12 \/ 16 * off16 + B + 12 + 4 <= G + 0) ;
  g5_D8 : (0 + 613987 + 1 <= 16 * off16 + B + 12 \/ 16 * off16 + B + 12 + 4 <= 0 + 613987) ;
  g5_A1 : Z.land h3 31 <= Z.land W 31 ;
  g5_A2 : Z.testbit avail (Z.land h3 31) = false ;
  g5_A3 : Z.testbit freed (Z.land h3 31) = false ;
  g5_A5 : rsv <= -16 * off16 + (16 * sz + 16 * sz * Z.land h3 31) + -4 ;
  g5_HIMG : 16 * off16 + B + 16 <= 0x10000 \/ 0x97000 <= 16 * off16 + B + 12 ;
  g5_GIMG : G + 40 <= 0x10000 \/ 0x97000 <= G ;
  g5_AG : G mod 8 = 0 ;
  g5_Rrsv : 5 <= rsv <= 2^32 - 1 ;
  g5_Mrsv : rdn SEGS m (wa (16 * sz + (B + 16 * sz * Z.land h3 31) + 8)) 4 = Some (word_to_le_bytes 4 (wa rsv)) ;
  g5_Mend5 : rdn SEGS m (wa (16 * sz + (B + 16 * sz * Z.land h3 31) + 7)) 1 = Some (word_to_le_bytes 1 (wa 0))
}.

Theorem free_gen5_of_model : forall L s (regs : bvmap 5 word) (m : word -> option byte) g am i fr,
  WF s -> repr L s (bview SEGS m) -> markers_hold L s (bview SEGS m) ->
  In (g, am, i, fr) (frames s) -> fr_kind fr = FUser -> 5 <= frame_rsv am fr ->
  ly_ctx L = 0x95ed8 ->
  getr regs 10 = wa (loc_addr L (LMem (frame_ptr am i fr))) ->
  rdn SEGS m (wa 613987) 1 = Some (word_to_le_bytes 1 (wa 0)) ->
  2^20 <= bv_unsigned (getr regs 2) <= 2^47 -> bv_unsigned (getr regs 2) mod 16 = 0 -> stk_ok SEGS m (getr regs 2) 1024 ->
  (forall rg, In rg (footprint s) -> loc_addr L (fst rg) + snd rg <= bv_unsigned (getr regs 2) - 1024) ->
  (forall rg, In rg (footprint s) -> fst rg <> LCtx 0 -> ranges_disjoint (crange L rg) (0x10000, 0x87000)) ->
  free_gen5 regs m (hdr_byte3 am i fr) (hdr_off16 am i fr) (loc_addr L (LMem g)) (am_avail am) (am_freed am) (meta_bits am)
           (ly_sec L mod 2^64) (stride_of am / 16) (loc_addr L (LMem (am_mem am))) (frame_rsv am fr).
Proof.
  intros L s regs m g am i fr HW HR HM HF Hk Hrc Hctx HP Hnl Rsp Asp HSTK HFP HAP.
  pose proof (get_meta_ok s g am i fr HW HF) as GM. cbn zeta in GM.
  destruct GM as (Ch4 & Ch3 & Ch16 & Cgm & Cmem & Cav & Cfr & Cbits & Geo & (a & k & Ha & Hk0 & Hga & Carea & Csec) & Hland & Hasrt & _).
  destruct (in_frames_inv s g am i fr HF) as (Hu & Hi & Hfri).
  apply (used_metas_usedX s g am HW) in Hu as Hux.
  pose proof (inv_groups HW g am Hux) as (Gm & Gml & Gsl & Gcl & Gmp & Gns).
  pose proof (Gsl i Hi) as (S1 & S2 & S3). rewrite Hfri in S3. destruct S3 as (Hal & _ & FOK & Hhdr).
  destruct FOK as (Fn & Foff & Ffit & F16 & _).
  destruct Gm as (Mlast & Maidx & Mlen & Mav0 & Mfr0 & Mdisj & Mabove & _ & _).
  destruct (masks_range_inv [] None U0 s g am HW Hux) as (_ & _ & _ & Rsc63 & Rml0).
  set (p := frame_ptr am i fr) in *.
  set (B := loc_addr L (LMem (am_mem am))).
  set (G := loc_addr L (LMem g)).
  set (h3 := hdr_byte3 am i fr) in *.
  set (off16 := hdr_off16 am i fr) in *.
  set (sz := stride_of am / 16).
  assert (Hstr1 : stride_of am = 16 * sz /\ 1 <= sz).
  { unfold sz, stride_of. destruct Gcl as [(C63 & CL0 & CML & _) | (Csc & _)].
    - rewrite CL0. replace ((0 =? 0) && negb (am_maplen am =? 0)) with true by (destruct (Z.eqb_spec (am_maplen am) 0); [lia | reflexivity]).
      replace (am_maplen am * 4096 - UNIT) with ((am_maplen am * 256 - 1) * 16) by (unfold UNIT; ring). rewrite Z.div_mul by lia. split; [ring | lia].
    - destruct ((am_last am =? 0) && negb (am_maplen am =? 0)) eqn:E.
      + apply andb_prop in E as [_ E]. apply negb_true_iff, Z.eqb_neq in E.
        replace (am_maplen am * 4096 - UNIT) with ((am_maplen am * 256 - 1) * 16) by (unfold UNIT; ring). rewrite Z.div_mul by lia. split; [ring | lia].
      + unfold class_size, UNIT. rewrite (Z.mul_comm 16), Z.div_mul by lia. pose proof (size_classes_range _ Csc). split; [ring | lia]. }
  destruct Hstr1 as (Hstr & Rsz1).
  assert (PADDR : loc_addr L (LMem p) = 16 * off16 + B + 16).
  { pose proof (f_equal (fun q => loc_addr L (LMem q)) Geo) as E. cbn beta in E. rewrite loc_padd in E.
    unfold B. rewrite <- E. unfold UNIT. ring. }
  destruct HR as (HL & HC & HFM).
  pose proof HL as (Lctx & Lal & Ldisj & Lrng).
  (* [comment removed for export] *)
  destruct (used_group_region [] None U0 s g am HW Hux) as (rgG & HrG & HkG & HlG & Ho0 & Hext & _).
  assert (FG : In (LMem (SP (prid (am_mem am)) 0), rg_len rgG) (footprint s)) by (apply footprint_region_In; assumption).
  pose proof (Lrng _ FG) as RgG. cbn [crange fst snd loc_addr] in RgG.
  pose proof (HFP _ FG) as SpG. cbn [fst snd loc_addr] in SpG.
  assert (EB : B = ly_reg L (prid (am_mem am)) + poff (am_mem am)) by (unfold B; destruct (am_mem am); reflexivity).
  (* [comment removed for export] *)
  pose proof (inv_areas HW) as (AND & AOK & _).
  destruct (AOK a Ha) as (ra & oa & rga & Ea & Oal & Opg & Hra & Hla & Hofit & Hkind).
  assert (FA : In (LMem a, PGSZ) (footprint s)) by (unfold footprint; right; apply in_app_iff; left; apply (in_map (fun a0 => (LMem a0, PGSZ))); exact Ha).
  pose proof (Lrng _ FA) as RgA. cbn [crange fst snd] in RgA.
  pose proof (HFP _ FA) as SpA. cbn [fst snd] in SpA.
  pose proof (Lal ra rga Hra Hla) as Aal.
  assert (EG : G = loc_addr L (LMem a) + 24 + 40 * k) by (unfold G; rewrite Hga, loc_padd; unfold AREA_HDR, META_SIZE; ring).
  assert (EA : loc_addr L (LMem a) = ly_reg L ra + oa) by (rewrite Ea; reflexivity).
  assert (HAG : 4096 * (G / 4096) = loc_addr L (LMem a)).
  { rewrite EG, EA. unfold PGSZ in *. clear - Oal Aal Hk0. unfold METAS_PER_AREA in Hk0.
    assert (E : (ly_reg L ra + oa) = 4096 * ((ly_reg L ra + oa) / 4096)).
    { pose proof (Z.div_mod (ly_reg L ra + oa) 4096 ltac:(lia)) as D. rewrite Zplus_mod, Aal, Oal in D. cbn in D. lia. }
    rewrite E. replace (4096 * ((ly_reg L ra + oa) / 4096) + 24 + 40 * k) with ((24 + 40 * k) + ((ly_reg L ra + oa) / 4096) * 4096) by ring.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. ring. }
  idtac "T0". Time assert (Hpr : forall x, 0 <= x -> (forall j, 32 <= j -> Z.testbit x j = false) -> 0 <= x <= 2^32 - 1).
  { idtac "HPR". time (intros x Hx Hb; split; [exact Hx|]).  assert (x < 2^32); [|lia].
    rewrite <- (Z.mod_small x (2^32)) at 1; [apply Z.mod_pos_bound; lia|]. split; [exact Hx|].
    destruct (Z.eq_dec x 0) as [->|Hnz]; [lia|]. apply Z.log2_lt_cancel. rewrite Z.log2_pow2 by lia.
    destruct (Z.lt_ge_cases (Z.log2 x) 32) as [Hl|Hg]; [exact Hl|]. exfalso.
    pose proof (Z.bit_log2 x ltac:(lia)) as Hbit. rewrite Hb in Hbit by lia. discriminate. }
  assert (Rav : 0 <= am_avail am <= 2^32 - 1).
  { idtac "RAV". Time (apply Hpr; [exact Mav0|]; intros j Hj; apply (proj1 (Mabove j ltac:(clear - Mlast Hj; lia)))). }
  assert (Rfr : 0 <= am_freed am <= 2^32 - 1).
  { Time (apply Hpr; [exact Mfr0|]; intros j Hj; apply (proj2 (Mabove j ltac:(clear - Mlast Hj; lia)))). }
  (* [comment removed for export] *)
  assert (Hrsv0 : 0 <= frame_rsv am fr) by (clear - Ffit; unfold frame_rsv, UNIT, IB in *; lia).
  assert (Hrceq : rsv_code am fr = 5).
  { clear - Hrc. unfold rsv_code. unfold frame_rsv in Hrc. destruct (5 <=? _) eqn:E; [reflexivity | apply Z.leb_gt in E; lia]. }
  assert (Eh3 : h3 = i + 32 * rsv_code am fr) by (unfold h3, hdr_byte3; rewrite Hk; reflexivity).
  assert (Eoff : off16 = sz * i + fr_off fr).
  { unfold off16, hdr_off16. rewrite Hstr. unfold UNIT. replace (16 * sz * i) with ((sz * i) * 16) by ring.
    rewrite Z.div_mul by lia. reflexivity. }
  assert (Hext' : poff (am_mem am) + 16 + 16 * sz * am_last am + 16 * sz <= rg_len rgG).
  { clear - Hext Hstr. unfold group_extent, UNIT, IB in Hext. rewrite Hstr in Hext. lia. }
  assert (Rsz : 1 <= sz <= 2^59).
  { split; [exact Rsz1|]. assert (0 <= sz * am_last am) by (apply Z.mul_nonneg_nonneg; lia).
    clear - Rsz1 Hext' RgG Mlast H Ho0. lia. }
  assert (Hsi : 0 <= sz * i <= sz * am_last am) by (clear - Rsz Hi; split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg_l; lia]).
  assert (Ho16 : 0 <= fr_off fr /\ 16 * fr_off fr + fr_n fr <= 16 * sz - 4) by (clear - Foff Ffit Hstr; unfold UNIT, IB in *; rewrite Hstr in Ffit; lia).
  assert (Hfoff : fr_off fr < sz) by (clear - Ho16 Fn; lia).
  assert (Eshr : Z.shiftr h3 5 = rsv_code am fr).
  { rewrite Eh3. rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32.
    replace (i + 32 * rsv_code am fr) with (i + rsv_code am fr * 32) by ring. rewrite Z.div_add by lia.
    rewrite Z.div_small by (clear - Hi Mlast; lia). ring. }
  assert (Hsp64 : bv_unsigned (getr regs 2) < 2^64) by (clear - Rsp; lia).
  (* [comment removed for export] *)
  constructor.
  - rewrite HP, PADDR. reflexivity.
  - exact Rsp.
  - exact Asp.
  - exact HSTK.
  - rewrite EB. clear - RgG Ho0 Hext' Hsi Rsz. lia.
  - rewrite EB. pose proof (used_group_aligned [] None U0 s HW 64%nat g am Hux ltac:(clear - Rsc63; lia)) as Al16.
    pose proof (Lal _ _ HrG HlG) as AlR. clear - Al16 AlR. unfold PGSZ in *.
    rewrite Zplus_mod, Al16. replace (ly_reg L (prid (am_mem am))) with (4096 * (ly_reg L (prid (am_mem am)) / 4096)) at 1
      by (pose proof (Z.div_mod (ly_reg L (prid (am_mem am))) 4096 ltac:(lia)); lia).
    replace (4096 * (ly_reg L (prid (am_mem am)) / 4096)) with ((256 * (ly_reg L (prid (am_mem am)) / 4096)) * 16) by ring.
    rewrite Z_mod_mult. reflexivity.
  - clear - F16 Eoff Rsz Hsi Ho16. lia.
  - rewrite EB, Eoff. clear - RgG Ho0 Hext' Hsi Rsz Ho16 Hfoff Hi. nia.
  - rewrite Eh3, Hrceq. clear - Hi Mlast. lia.
  - rewrite EG. clear - RgA Hk0. unfold METAS_PER_AREA, PGSZ in *. lia.
  - exact Rav.
  - exact Rfr.
  - exact (meta_bits_range_inv [] None U0 s g am L HW Hux HL).
  - exact Rsz.
  - pose proof (Z.mod_pos_bound (ly_sec L) (2^64) ltac:(lia)). clear - H. lia.
  - rewrite Hland, EB. clear - RgG Ho0 Hext' Hsi Rsz. lia.
  - rewrite Hland, EB. assert (frame_rsv am fr <= 16 * sz) by (unfold frame_rsv; rewrite Hstr; clear - Fn Ho16; unfold UNIT, IB in *; lia).
    clear - RgG Ho0 Hext' Hsi Rsz Hrc H. lia.
  - cellrd HC Ch4 Hr. fold p in Hr. rewrite PADDR in Hr. rdn_by Hr.
  - cellrd HC Ch3 Hr. fold p in Hr. rewrite PADDR in Hr. rdn_by Hr.
  - cellrd HC Ch16 Hr. fold p in Hr. rewrite PADDR in Hr. rdn_by Hr.
  - cellrd HC Cgm Hr. fold B G in Hr. rdn_by Hr.
  - cellrd HC Cmem Hr. fold B G in Hr. unfold META_mem in Hr. rdn_by Hr.
  - cellrd HC Cav Hr. fold G in Hr. unfold META_avail in Hr. rdn_by Hr.
  - cellrd HC Cfr Hr. fold G in Hr. unfold META_freed in Hr. rdn_by Hr.
  - cellrd HC Cbits Hr. fold G in Hr. unfold META_bits in Hr. rdn_by Hr.
  - cellrd HC Carea Hr. rewrite <- HAG in Hr. replace (4096 * (G / 4096) + 0) with (4096 * (G / 4096)) by ring.
    rewrite Hr. f_equal. apply le_wa_eqm; [|apply Nat.leb_le; reflexivity]. change (8 * Z.of_nat 8) with 64. rewrite Z.mod_mod by lia. reflexivity.
  - cellrd HC Csec Hr. cbn [loc_addr] in Hr. rewrite Hctx in Hr. unfold CTX_secret in Hr.
    replace (0 + 614104) with (0x95ed8 + 0) by reflexivity.
    rewrite Hr. f_equal. apply le_wa_eqm; [|apply Nat.leb_le; reflexivity]. change (8 * Z.of_nat 8) with 64. rewrite Z.mod_mod by lia. reflexivity.
  - exact Hnl.
  - assert (Cend : In (MCell (LMem (slot_end am i)) 1 (VZ 0)) (markers s)) by (apply (In_markers s g am i fr _ HF Hk); apply in_eq).
    cellrd HM Cend Hr. unfold slot_end, slot_start in Hr. rewrite !loc_padd, Hstr in Hr. fold B in Hr. unfold UNIT, IB in Hr.
    rewrite Hland. rdn_by Hr.
  - rewrite Hland.
    assert (Cr : In (MCell (LMem (padd (slot_end am i) (- frame_rsv am fr))) 1 (VZ 0)) (markers s)).
    { apply (In_markers s g am i fr _ HF Hk). unfold marker_cells. apply in_cons. apply in_or_app. left.
      replace (0 <? frame_rsv am fr) with true by (symmetry; apply Z.ltb_lt; clear - Hrc; lia). apply in_eq. }
    cellrd HM Cr Hr. unfold slot_end, slot_start in Hr. rewrite !loc_padd, Hstr in Hr. fold B in Hr. unfold UNIT, IB in Hr.
    rdn_by Hr.
  - (* [comment removed for export] *)
    apply (store_ok_of_bytes SEGS m (16 * off16 + B + 12) 4). intros j Hj.
    pose proof (proj1 (Forall_forall _ _) HC _ Ch4) as K4. pose proof (proj1 (Forall_forall _ _) HC _ Ch3) as K3.
    pose proof (proj1 (Forall_forall _ _) HC _ Ch16) as K16.
    assert (E4 : loc_addr L (mc_loc (MCell (LMem (padd p (-4))) 1 (VZ 0))) = 16 * off16 + B + 12) by (cbn [mc_loc]; rewrite loc_padd; fold p; rewrite PADDR; ring).
    assert (E3 : loc_addr L (mc_loc (MCell (LMem (padd p (-3))) 1 (VZ h3))) = 16 * off16 + B + 13) by (cbn [mc_loc]; rewrite loc_padd; fold p; rewrite PADDR; ring).
    assert (E16 : loc_addr L (mc_loc (MCell (LMem (padd p (-2))) 2 (VZ off16))) = 16 * off16 + B + 14) by (cbn [mc_loc]; rewrite loc_padd; fold p; rewrite PADDR; ring).
    assert (Hj' : j = 0 \/ j = 1 \/ j = 2 \/ j = 3) by (clear - Hj; lia).
    destruct Hj' as [ -> | [ -> | [ -> | -> ] ] ].
    + pose proof (holds_wview SEGS L m _ 0 K4 ltac:(intros z Hz0; discriminate) ltac:(cbn; lia)) as W. rewrite E4 in W. exact W.
    + pose proof (holds_wview SEGS L m _ 0 K3 ltac:(intros z Hz0; discriminate) ltac:(cbn; lia)) as W. rewrite E3 in W.
      replace (16 * off16 + B + 12 + 1) with (16 * off16 + B + 13 + 0) by ring. exact W.
    + pose proof (holds_wview SEGS L m _ 0 K16 ltac:(intros z Hz0; discriminate) ltac:(cbn; lia)) as W. rewrite E16 in W.
      replace (16 * off16 + B + 12 + 2) with (16 * off16 + B + 14 + 0) by ring. exact W.
    + pose proof (holds_wview SEGS L m _ 1 K16 ltac:(intros z Hz0; discriminate) ltac:(cbn; lia)) as W. rewrite E16 in W.
      replace (16 * off16 + B + 12 + 3) with (16 * off16 + B + 14 + 1) by ring. exact W.
  - (* [comment removed for export] *)
    apply (store_ok_of_bytes SEGS m (G + 24) 8). intros j Hj.
    pose proof (proj1 (Forall_forall _ _) HC _ Cav) as Ka. pose proof (proj1 (Forall_forall _ _) HC _ Cfr) as Kf.
    assert (Ea' : loc_addr L (mc_loc (MCell (LMem (padd g META_avail)) 4 (VZ (am_avail am)))) = G + 24) by (cbn [mc_loc]; rewrite loc_padd; reflexivity).
    assert (Ef' : loc_addr L (mc_loc (MCell (LMem (padd g META_freed)) 4 (VZ (am_freed am)))) = G + 28) by (cbn [mc_loc]; rewrite loc_padd; reflexivity).
    destruct (Z.ltb_spec j 4) as [Hl|Hg].
    + pose proof (holds_wview SEGS L m _ j Ka ltac:(intros z Hz0; discriminate) ltac:(cbn; clear - Hj Hl; lia)) as W. rewrite Ea' in W. exact W.
    + pose proof (holds_wview SEGS L m _ (j - 4) Kf ltac:(intros z Hz0; discriminate) ltac:(cbn; clear - Hj Hg; lia)) as W. rewrite Ef' in W.
      replace (G + 24 + j) with (G + 28 + (j - 4)) by ring. exact W.
  - rewrite Hland, EB. clear - SpG Ho0 Hext' Hsi Rsz. lia.
  - rewrite Hland, EB. clear - SpG Ho0 Hext' Hsi Rsz Hrc. lia.
  - rewrite EB, Eoff. clear - SpG Ho0 Hext' Hsi Rsz Ho16 Hfoff. nia.
  - rewrite EB. clear - SpG Ho0 Hext' Hsi Rsz. lia.
  - rewrite EG. clear - SpA Hk0. unfold METAS_PER_AREA, PGSZ in *. lia.
  - rewrite HAG. clear - SpA. unfold PGSZ in *. lia.
  - assert (Hne : (LMem a, PGSZ) <> (LMem (SP (prid (am_mem am)) 0), rg_len rgG)).
    { rewrite Ea. intro E. injection E as E1 E2. clear - E2 Opg. unfold PGSZ in *. lia. }
    destruct (pairwise_map_In _ (crange L) _ _ _ Ldisj FA FG Hne) as [D|D];
      unfold ranges_disjoint in D; cbn [crange fst snd] in D; change (loc_addr L (LMem (SP (prid (am_mem am)) 0))) with (ly_reg L (prid (am_mem am)) + 0) in D.
    + rewrite EG, EB, Eoff. clear - D Ho0 Hext' Hsi Rsz Ho16 Hfoff Hk0. unfold METAS_PER_AREA, PGSZ in *. nia.
    + rewrite EG, EB, Eoff. clear - D Ho0 Hext' Hsi Rsz Ho16 Hfoff Hk0. unfold METAS_PER_AREA, PGSZ in *. nia.
  - pose proof (HAP _ FG ltac:(discriminate)) as D. unfold ranges_disjoint in D. cbn [crange fst snd loc_addr] in D.
    rewrite EB, Eoff. clear - D Ho0 Hext' Hsi Rsz Ho16 Hfoff. nia.
  - assert (EW : Z.land (meta_bits am) 31 = am_last am).
    { unfold meta_bits. replace (am_last am + 32 + 64 * am_sc am + 4096 * am_maplen am) with (am_last am + 32 * (1 + 2 * am_sc am + 128 * am_maplen am)) by ring.
      apply land31; clear - Mlast Rsc63 Rml0; lia. }
    rewrite Hland, EW. exact (proj2 Hi).
  - unfold allocated in Hal. apply negb_true_iff in Hal. rewrite Z.lor_spec in Hal. apply orb_false_iff in Hal.
    rewrite Hland. exact (proj1 Hal).
  - unfold allocated in Hal. apply negb_true_iff in Hal. rewrite Z.lor_spec in Hal. apply orb_false_iff in Hal.
    rewrite Hland. exact (proj2 Hal).
  - rewrite Hland, Eoff. unfold frame_rsv. rewrite Hstr. clear - Ho16 Fn. unfold UNIT, IB. lia.
  - pose proof (HAP _ FG ltac:(discriminate)) as D. unfold ranges_disjoint in D. cbn [crange fst snd loc_addr] in D.
    rewrite EB, Eoff. clear - D Ho0 Hext' Hsi Rsz Ho16 Hfoff. nia.
  - pose proof (HAP _ FA ltac:(discriminate)) as D. unfold ranges_disjoint in D. cbn [crange fst snd] in D.
    rewrite EG. clear - D Hk0. unfold METAS_PER_AREA, PGSZ in *. lia.
  - rewrite EG, EA. clear - Oal Aal. unfold PGSZ in *. rewrite Zplus_mod, (Zplus_mod (ly_reg L ra + oa) 24), (Zplus_mod (ly_reg L ra) oa).
    replace (ly_reg L ra mod 8) with 0. 2:{ pose proof (Z.div_mod (ly_reg L ra) 4096 ltac:(lia)) as E. rewrite Aal in E. rewrite E.
      replace (4096 * (ly_reg L ra / 4096) + 0) with ((512 * (ly_reg L ra / 4096)) * 8) by ring. rewrite Z_mod_mult. reflexivity. }
    replace (oa mod 8) with 0. 2:{ pose proof (Z.div_mod oa 4096 ltac:(lia)) as E. rewrite Oal in E. rewrite E.
      replace (4096 * (oa / 4096) + 0) with ((512 * (oa / 4096)) * 8) by ring. rewrite Z_mod_mult. reflexivity. }
    replace (40 * k) with (k * 8 * 5) by ring. rewrite Z.mul_comm, Z.mul_assoc, Z_mod_mult. cbn. reflexivity.
  - (* [comment removed for export] *)
    split; [exact Hrc|].
    destruct Gcl as [(C63 & CL0 & CML & _ & _ & C6) | (Csc & _ & _ & Cspan)].
    + destruct C6 as [CR | (fr' & Hfr' & _ & _ & Hbig)]; [discriminate CR|].
      assert (Ei0 : i = 0) by (clear - Hi CL0; lia). assert (Hfri0 : ss_fr (nth_slot am 0) = Some fr) by (rewrite <- Ei0; exact Hfri).
      rewrite Hfri0 in Hfr'. injection Hfr' as <-.
      assert (Est : stride_of am = am_maplen am * PGSZ - UNIT).
      { unfold stride_of. rewrite CL0. replace ((0 =? 0) && negb (am_maplen am =? 0)) with true by (destruct (Z.eqb_spec (am_maplen am) 0); [lia | reflexivity]).
        unfold PGSZ. reflexivity. }
      unfold frame_rsv. rewrite Est. clear - Hbig Ho16 Fn. unfold UNIT, IB, PGSZ in *. lia.
    + assert (0 <= stride_of am * am_last am) by (rewrite Hstr; apply Z.mul_nonneg_nonneg; clear - Rsz Mlast; lia).
      unfold frame_rsv. clear - Cspan Ho16 Fn H Hstr. unfold UNIT, IB in *. lia.
  - assert (C4 : In (MCell (LMem (padd (slot_end am i) (-4))) 4 (VZ (frame_rsv am fr))) (markers s)).
    { apply (In_markers s g am i fr _ HF Hk). unfold marker_cells. apply in_cons. apply in_or_app. right.
      replace (5 <=? frame_rsv am fr) with true by (symmetry; apply Z.leb_le; exact Hrc). apply in_eq. }
    cellrd HM C4 Hr. unfold slot_end, slot_start in Hr. rewrite !loc_padd, Hstr in Hr. fold B in Hr. unfold UNIT, IB in Hr.
    rewrite Hland. rdn_by Hr.
  - assert (C5 : In (MCell (LMem (padd (slot_end am i) (-5))) 1 (VZ 0)) (markers s)).
    { apply (In_markers s g am i fr _ HF Hk). unfold marker_cells. apply in_cons. apply in_or_app. right.
      replace (5 <=? frame_rsv am fr) with true by (symmetry; apply Z.leb_le; exact Hrc). right. apply in_eq. }
    cellrd HM C5 Hr. unfold slot_end, slot_start in Hr. rewrite !loc_padd, Hstr in Hr. fold B in Hr. unfold UNIT, IB in Hr.
    rewrite Hland. rdn_by Hr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma gm_asserts_facts : forall p base v, get_meta_asserts p base v = true ->
  (gm_sc v < 48 -> znth (gm_sc v) size_classes * Z.land (gm_p3 v) 31 <= gm_off16 v < znth (gm_sc v) size_classes * (Z.land (gm_p3 v) 31 + 1)) /\
  (48 <= gm_sc v -> gm_sc v = 63) /\
  (0 < gm_maplen v -> gm_off16 v <= gm_maplen v * 4096 / 16 - 1).
Proof.
  intros p base v H. unfold get_meta_asserts in H.
  repeat (apply andb_prop in H as [H ?]).
  match goal with H1 : (if gm_sc v <? 48 then _ else _) = true, H2 : implb _ _ = true |- _ => rename H1 into Hc; rename H2 into Hm end.
  split; [|split].
  - intros Hs. replace (gm_sc v <? 48) with true in Hc by (symmetry; apply Z.ltb_lt; exact Hs).
    apply andb_prop in Hc as [C1 C2]. apply Z.leb_le in C1. apply Z.ltb_lt in C2. lia.
  - intros Hs. replace (gm_sc v <? 48) with false in Hc by (symmetry; apply Z.ltb_ge; exact Hs). apply Z.eqb_eq in Hc. exact Hc.
  - intros Hp. replace (0 <? gm_maplen v) with true in Hm by (symmetry; apply Z.ltb_lt; exact Hp). cbn in Hm. apply Z.leb_le in Hm. exact Hm.
Qed.

Lemma meta_bits_fields : forall am, 0 <= am_last am <= 31 -> 0 <= am_sc am <= 63 -> 0 <= am_maplen am ->
  Z.land (meta_bits am) 31 = am_last am /\ SCW (meta_bits am) = am_sc am /\ Z.shiftr (meta_bits am) 12 = am_maplen am.
Proof.
  intros am Hl Hs Hm. unfold meta_bits.
  split; [|split].
  - replace (am_last am + 32 + 64 * am_sc am + 4096 * am_maplen am) with (am_last am + 32 * (1 + 2 * am_sc am + 128 * am_maplen am)) by ring.
    apply land31; lia.
  - rewrite SCW_bits by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^6) with 64.
    replace (am_last am + 32 + 64 * am_sc am + 4096 * am_maplen am) with ((am_last am + 32) + (am_sc am + 64 * am_maplen am) * 64) by ring.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. change 63 with (Z.ones 6). rewrite Z.land_ones by lia.
    rewrite Z.add_0_l, Z.add_mod by lia. replace ((64 * am_maplen am) mod 2^6) with 0 by (change (2^6) with 64; rewrite Z.mul_comm; rewrite Z_mod_mult; reflexivity).
    rewrite Z.add_0_r, !Z.mod_mod by lia. apply Z.mod_small. change (2^6) with 64. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2^12) with 4096.
    replace (am_last am + 32 + 64 * am_sc am + 4096 * am_maplen am) with ((am_last am + 32 + 64 * am_sc am) + am_maplen am * 4096) by ring.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. ring.
Qed.

(* [comment removed for export] *)
Lemma frame_shape : forall s g am i fr, WF s -> In (g, am, i, fr) (frames s) ->
  0 <= am_last am <= 31 /\ 0 <= am_sc am <= 63 /\ 0 <= am_maplen am /\ 0 <= i <= am_last am /\
  ((am_sc am = 63 /\ am_last am = 0 /\ 1 <= am_maplen am) \/ 0 <= am_sc am < 48) /\
  get_meta_asserts (frame_ptr am i fr) (am_mem am) (view_of s g am i fr) = true.
Proof.
  intros s g am i fr HW HF.
  pose proof (get_meta_ok s g am i fr HW HF) as GM. cbn zeta in GM.
  destruct GM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hasrt & _).
  destruct (in_frames_inv s g am i fr HF) as (Hu & Hi & Hfri).
  apply (used_metas_usedX s g am HW) in Hu as Hux.
  destruct (masks_range_inv [] None U0 s g am HW Hux) as (_ & _ & Rl & Rs & Rm).
  pose proof (inv_groups HW g am Hux) as (_ & _ & _ & Gcl & _).
  split; [exact Rl|]. split; [exact Rs|]. split; [exact Rm|]. split; [exact Hi|]. split; [|exact Hasrt].
  destruct Gcl as [(C63 & CL0 & CML & _) | (Csc & _)]; [left; auto | right; exact Csc].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Spec.
Variable L : layout.
Variable s : astate.
Variable regs : bvmap 5 word.
Variable m : word -> option byte.
Variables (g : sptr) (am : ameta) (i : Z) (fr : frame).
Hypothesis HW : WF s.
Hypothesis HR : repr L s (bview SEGS m).
Hypothesis HM : markers_hold L s (bview SEGS m).
Hypothesis HF : In (g, am, i, fr) (frames s).
Hypothesis Hk : fr_kind fr = FUser.
Hypothesis Hctx : ly_ctx L = 0x95ed8.
Hypothesis HP : getr regs 10 = wa (loc_addr L (LMem (frame_ptr am i fr))).
Hypothesis Hnl : rdn SEGS m (wa 613987) 1 = Some (word_to_le_bytes 1 (wa 0)).
Hypothesis Htab : forall sc, 0 <= sc < 48 -> rdn SEGS m (wa (98984 + 2 * sc)) 2 = Some (word_to_le_bytes 2 (wa (znth sc size_classes))).
Hypothesis Rsp : 2^20 <= bv_unsigned (getr regs 2) <= 2^47.
Hypothesis Asp : bv_unsigned (getr regs 2) mod 16 = 0.
Hypothesis HSTK : stk_ok SEGS m (getr regs 2) 1024.
Hypothesis HFP : forall rg, In rg (footprint s) -> loc_addr L (fst rg) + snd rg <= bv_unsigned (getr regs 2) - 1024.
Hypothesis HAP : forall rg, In rg (footprint s) -> fst rg <> LCtx 0 -> ranges_disjoint (crange L rg) (0x10000, 0x87000).

Local Ltac shape := destruct (frame_shape s g am i fr HW HF) as (Rl & Rs & Rm & Ri & Cl & Has);
  destruct (meta_bits_fields am Rl Rs Rm) as (EW31 & ESC & EML);
  destruct (gm_asserts_facts _ _ _ Has) as (GA4 & GA63 & GA6); cbn [view_of gm_sc gm_p3 gm_off16 gm_maplen] in GA4, GA63, GA6;
  pose proof (get_meta_ok s g am i fr HW HF) as GMk; cbn zeta in GMk;
  destruct GMk as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hland & _ & _).

#[using="s HW HR HM HF Hk Hctx HP Hnl Htab Rsp Asp HSTK HFP HAP"] Theorem free_prem_of_model : 0 < am_maplen am -> am_last am <> 0 -> rsv_code am fr < 5 ->
  free_prem regs m (hdr_byte3 am i fr) (hdr_off16 am i fr) (loc_addr L (LMem g)) (am_avail am) (am_freed am) (meta_bits am)
           (ly_sec L mod 2^64) (znth (am_sc am) size_classes) (loc_addr L (LMem (am_mem am))).
Proof. LiaFast.lf_pins (fun (s HW HR HM HF Hk Hctx HP Hnl Htab Rsp Asp HSTK HFP HAP : LiaFast.U) => LiaFast.u0).
  intros Hml Hl0 Hrc. shape.
  assert (Hsc : 0 <= am_sc am < 48) by (destruct Cl as [(_ & E & _)|C]; [exfalso; exact (Hl0 E) | exact C]).
  assert (Estr : stride_of am / 16 = znth (am_sc am) size_classes).
  { unfold stride_of. replace ((am_last am =? 0) && negb (am_maplen am =? 0)) with false by (destruct (Z.eqb_spec (am_last am) 0); [exfalso; exact (Hl0 e) | reflexivity]).
    unfold class_size, UNIT. rewrite Z.mul_comm, Z.div_mul by lia. reflexivity. }
  pose proof (free_gen4_of_model L s regs m g am i fr HW HR HM HF Hk Hrc Hctx HP Hnl Rsp Asp HSTK HFP HAP) as FG. rewrite Estr in FG.
  pose proof (fg_RW _ _ _ _ _ _ _ _ _ _ _ FG) as RW'.
  destruct FG as [fg_HP fg_Rsp fg_Asp fg_HSTK fg_RB fg_AB fg_Roff fg_RPB fg_Rh3 fg_RG fg_Rav fg_Rfr fg_RW fg_Rsz fg_Rsec fg_REND fg_RENDR fg_Mh4 fg_Mh3 fg_Moff fg_Mmeta fg_Mmem fg_Mav fg_Mfr fg_MW fg_Marea fg_Mctx fg_Mnl fg_Mend fg_Mendr fg_Whdr fg_Wmeta fg_D1 fg_D2 fg_D3 fg_D4 fg_D5 fg_D6 fg_D7 fg_D8 fg_A1 fg_A2 fg_A3 fg_A5 fg_HIMG fg_GIMG fg_AG]. pose proof (size_classes_range _ Hsc) as Rsz.
  constructor; try assumption.
  - clear - RW' Hml Rl Rs. unfold meta_bits in *. lia.
  - rewrite ESC. replace (2 * am_sc am + 98984) with (98984 + 2 * am_sc am) by ring. exact (Htab _ Hsc).
  - exact (GA4 ltac:(clear - Hsc; lia)).
  - rewrite EML. pose proof (GA6 Hml) as G6. replace (am_maplen am * 4096 / 16) with (am_maplen am * 256) in G6 by (replace (am_maplen am * 4096) with ((am_maplen am * 256) * 16) by ring; rewrite Z.div_mul by lia; reflexivity). clear - G6 Hml. lia.
  - rewrite EW31. exact Hl0.
  - rewrite ESC. clear - Hsc. lia.
Qed.

Local Ltac rdn_match := match goal with H : rdn SEGS m (wa ?Y) ?n = ?V |- rdn SEGS m (wa ?X) ?n = ?V => replace X with Y by ring; exact H end.

#[using="s HW HR HM HF Hk Hctx HP Hnl Htab Rsp Asp HSTK HFP HAP"] Theorem free_prem5_of_model : 0 < am_maplen am -> am_last am <> 0 -> 5 <= frame_rsv am fr ->
  free_prem5 regs m (hdr_byte3 am i fr) (hdr_off16 am i fr) (loc_addr L (LMem g)) (am_avail am) (am_freed am) (meta_bits am)
           (ly_sec L mod 2^64) (znth (am_sc am) size_classes) (loc_addr L (LMem (am_mem am))) (frame_rsv am fr).
Proof. LiaFast.lf_pins (fun (s HW HR HM HF Hk Hctx HP Hnl Htab Rsp Asp HSTK HFP HAP : LiaFast.U) => LiaFast.u0).
  intros Hml Hl0 Hrc. shape.
  assert (Hsc : 0 <= am_sc am < 48) by (destruct Cl as [(_ & E & _)|C]; [exfalso; exact (Hl0 E) | exact C]).
  assert (Estr : stride_of am / 16 = znth (am_sc am) size_classes).
  { unfold stride_of. replace ((am_last am =? 0) && negb (am_maplen am =? 0)) with false by (destruct (Z.eqb_spec (am_last am) 0); [exfalso; exact (Hl0 e) | reflexivity]).
    unfold class_size, UNIT. rewrite Z.mul_comm, Z.div_mul by lia. reflexivity. }
  pose proof (free_gen5_of_model L s regs m g am i fr HW HR HM HF Hk Hrc Hctx HP Hnl Rsp Asp HSTK HFP HAP) as FG. rewrite Estr in FG.
  pose proof (g5_RW _ _ _ _ _ _ _ _ _ _ _ _ FG) as RW'.
  destruct FG as [g5_HP g5_Rsp g5_Asp g5_HSTK g5_RB g5_AB g5_Roff g5_RPB g5_Rh3 g5_RG g5_Rav g5_Rfr g5_RW g5_Rsz g5_Rsec g5_REND g5_RENDR g5_Mh4 g5_Mh3 g5_Moff g5_Mmeta g5_Mmem g5_Mav g5_Mfr g5_MW g5_Marea g5_Mctx g5_Mnl g5_Mend g5_Mendr g5_Whdr g5_Wmeta g5_D1 g5_D2 g5_D3 g5_D4 g5_D5 g5_D6 g5_D7 g5_D8 g5_A1 g5_A2 g5_A3 g5_A5 g5_HIMG g5_GIMG g5_AG g5_Rrsv g5_Mrsv g5_Mend5]. pose proof (size_classes_range _ Hsc) as Rsz.
  constructor; try assumption.
  - clear - RW' Hml Rl Rs. unfold meta_bits in *. lia.
  - rewrite ESC. replace (2 * am_sc am + 98984) with (98984 + 2 * am_sc am) by ring. exact (Htab _ Hsc).
  - exact (GA4 ltac:(clear - Hsc; lia)).
  - rewrite EML. pose proof (GA6 Hml) as G6. replace (am_maplen am * 4096 / 16) with (am_maplen am * 256) in G6 by (replace (am_maplen am * 4096) with ((am_maplen am * 256) * 16) by ring; rewrite Z.div_mul by lia; reflexivity). clear - G6 Hml. lia.
  - rewrite EW31. exact Hl0.
  - rewrite ESC. clear - Hsc. lia.
Qed.

Local Ltac mapped_prep Hml Hl0 Hland Ri :=
  assert (Estr : stride_of am / 16 = am_maplen am * 256 - 1) by
    (unfold stride_of; replace ((am_last am =? 0) && negb (am_maplen am =? 0)) with true by (rewrite Hl0; destruct (Z.eqb_spec (am_maplen am) 0); [lia | reflexivity]);
     replace (am_maplen am * 4096 - UNIT) with ((am_maplen am * 256 - 1) * 16) by (unfold UNIT; ring); rewrite Z.div_mul by lia; reflexivity);
  assert (I0 : Z.land (hdr_byte3 am i fr) 31 = 0) by (rewrite Hland; clear - Ri Hl0; lia).

#[using="s HW HR HM HF Hk Hctx HP Hnl Htab Rsp Asp HSTK HFP HAP"] Theorem free_prd_of_model : 0 < am_maplen am -> am_last am = 0 -> 0 <= am_sc am < 48 -> rsv_code am fr < 5 ->
  free_prd regs m (hdr_byte3 am i fr) (hdr_off16 am i fr) (loc_addr L (LMem g)) (am_avail am) (am_freed am) (meta_bits am)
           (ly_sec L mod 2^64) (znth (am_sc am) size_classes) (loc_addr L (LMem (am_mem am))).
Proof. LiaFast.lf_pins (fun (s HW HR HM HF Hk Hctx HP Hnl Htab Rsp Asp HSTK HFP HAP : LiaFast.U) => LiaFast.u0).
  intros Hml Hl0 Hsc Hrc. shape. mapped_prep Hml Hl0 Hland Ri.
  pose proof (free_gen4_of_model L s regs m g am i fr HW HR HM HF Hk Hrc Hctx HP Hnl Rsp Asp HSTK HFP HAP) as FG. rewrite Estr in FG.
  pose proof (fg_RW _ _ _ _ _ _ _ _ _ _ _ FG) as RW'.
  destruct FG as [fg_HP fg_Rsp fg_Asp fg_HSTK fg_RB fg_AB fg_Roff fg_RPB fg_Rh3 fg_RG fg_Rav fg_Rfr fg_RW fg_Rsz fg_Rsec fg_REND fg_RENDR fg_Mh4 fg_Mh3 fg_Moff fg_Mmeta fg_Mmem fg_Mav fg_Mfr fg_MW fg_Marea fg_Mctx fg_Mnl fg_Mend fg_Mendr fg_Whdr fg_Wmeta fg_D1 fg_D2 fg_D3 fg_D4 fg_D5 fg_D6 fg_D7 fg_D8 fg_A1 fg_A2 fg_A3 fg_A5 fg_HIMG fg_GIMG fg_AG].
  repeat match goal with H : context [Z.land (hdr_byte3 am i fr) 31] |- _ => tryif (constr_eq H I0) then fail else rewrite I0 in H end. pose proof (size_classes_range _ Hsc) as Rsz.
  constructor; try assumption.
  all: rewrite ?I0, ?EML.
  all: try assumption.
  all: try rdn_match.
  all: try (clear - RW' Hml Rl Rs; unfold meta_bits in *; lia).
  all: try (match goal with H : ?lo <= ?X <= ?hi |- _ <= _ <= _ => clear - H Hml; lia end).
  all: try (match goal with H : _ <= bv_unsigned (getr regs 2) + -1024 |- _ <= bv_unsigned (getr regs 2) + -1024 => clear - H Hml; lia end).
  - clear - fg_D1 fg_Rsp fg_RB Hml. lia.
  - rewrite Z.shiftr_div_pow2 in * by lia. clear - fg_D1 fg_Rsp fg_RB fg_Rh3 Hml. lia.
  - rewrite ESC. replace (2 * am_sc am + 98984) with (98984 + 2 * am_sc am) by ring. exact (Htab _ Hsc).
  - exact (GA4 ltac:(clear - Hsc; lia)).
  - clear - fg_A5 Hml. lia.
  - pose proof (GA6 Hml) as G6. replace (am_maplen am * 4096 / 16) with (am_maplen am * 256) in G6 by (replace (am_maplen am * 4096) with ((am_maplen am * 256) * 16) by ring; rewrite Z.div_mul by lia; reflexivity). clear - G6 Hml. lia.
  - rewrite EW31. exact Hl0.
  - rewrite ESC. clear - Hsc. lia.
Qed.

#[using="s HW HR HM HF Hk Hctx HP Hnl Htab Rsp Asp HSTK HFP HAP"] Theorem free_prd5_of_model : 0 < am_maplen am -> am_last am = 0 -> 0 <= am_sc am < 48 -> 5 <= frame_rsv am fr ->
  free_prd5 regs m (hdr_byte3 am i fr) (hdr_off16 am i fr) (loc_addr L (LMem g)) (am_avail am) (am_freed am) (meta_bits am)
           (ly_sec L mod 2^64) (znth (am_sc am) size_classes) (loc_addr L (LMem (am_mem am))) (frame_rsv am fr).
Proof. LiaFast.lf_pins (fun (s HW HR HM HF Hk Hctx HP Hnl Htab Rsp Asp HSTK HFP HAP : LiaFast.U) => LiaFast.u0).
  intros Hml Hl0 Hsc Hrc. shape. mapped_prep Hml Hl0 Hland Ri.
  pose proof (free_gen5_of_model L s regs m g am i fr HW HR HM HF Hk Hrc Hctx HP Hnl Rsp Asp HSTK HFP HAP) as FG. rewrite Estr in FG.
  pose proof (g5_RW _ _ _ _ _ _ _ _ _ _ _ _ FG) as RW'.
  destruct FG as [g5_HP g5_Rsp g5_Asp g5_HSTK g5_RB g5_AB g5_Roff g5_RPB g5_Rh3 g5_RG g5_Rav g5_Rfr g5_RW g5_Rsz g5_Rsec g5_REND g5_RENDR g5_Mh4 g5_Mh3 g5_Moff g5_Mmeta g5_Mmem g5_Mav g5_Mfr g5_MW g5_Marea g5_Mctx g5_Mnl g5_Mend g5_Mendr g5_Whdr g5_Wmeta g5_D1 g5_D2 g5_D3 g5_D4 g5_D5 g5_D6 g5_D7 g5_D8 g5_A1 g5_A2 g5_A3 g5_A5 g5_HIMG g5_GIMG g5_AG g5_Rrsv g5_Mrsv g5_Mend5].
  repeat match goal with H : context [Z.land (hdr_byte3 am i fr) 31] |- _ => tryif (constr_eq H I0) then fail else rewrite I0 in H end.
  pose proof (size_classes_range _ Hsc) as Rsz.
  constructor; try assumption.
  all: rewrite ?I0, ?EML.
  all: try assumption.
  all: try rdn_match.
  all: try (clear - RW' Hml Rl Rs; unfold meta_bits in *; lia).
  all: try (match goal with H : ?lo <= ?X <= ?hi |- _ <= _ <= _ => clear - H Hml; lia end).
  all: try (match goal with H : _ <= bv_unsigned (getr regs 2) + -1024 |- _ <= bv_unsigned (getr regs 2) + -1024 => clear - H Hml; lia end).
  - clear - g5_D1 g5_Rsp g5_RB Hml. lia.
  - clear - g5_D1 g5_A5 g5_Roff g5_Rsp g5_RB Hml g5_Rrsv. lia.
  - rewrite ESC. replace (2 * am_sc am + 98984) with (98984 + 2 * am_sc am) by ring. exact (Htab _ Hsc).
  - exact (GA4 ltac:(clear - Hsc; lia)).
  - clear - g5_A5 Hml. lia.
  - pose proof (GA6 Hml) as G6. replace (am_maplen am * 4096 / 16) with (am_maplen am * 256) in G6 by (replace (am_maplen am * 4096) with ((am_maplen am * 256) * 16) by ring; rewrite Z.div_mul by lia; reflexivity). clear - G6 Hml. lia.
  - rewrite EW31. exact Hl0.
  - rewrite ESC. clear - Hsc. lia.
Qed.

Local Ltac direct_prep Hsc Cl :=
  assert (Hl0 : am_last am = 0) by (destruct Cl as [(_ & E & _)|C]; [exact E | rewrite Hsc in C; clear - C; lia]);
  assert (Hml : 0 < am_maplen am) by (destruct Cl as [(_ & _ & E)|C]; [clear - E; lia | rewrite Hsc in C; clear - C; lia]).

#[using="s HW HR HM HF Hk Hctx HP Hnl Rsp Asp HSTK HFP HAP"] Theorem free_pre_e_of_model : am_sc am = 63 -> rsv_code am fr < 5 ->
  free_pre_e regs m (hdr_byte3 am i fr) (hdr_off16 am i fr) (loc_addr L (LMem g)) (am_avail am) (am_freed am) (meta_bits am)
           (ly_sec L mod 2^64) 1 (loc_addr L (LMem (am_mem am))).
Proof. LiaFast.lf_pins (fun (s HW HR HM HF Hk Hctx HP Hnl Rsp Asp HSTK HFP HAP : LiaFast.U) => LiaFast.u0).
  intros Hsc Hrc. shape. direct_prep Hsc Cl. mapped_prep Hml Hl0 Hland Ri.
  pose proof (free_gen4_of_model L s regs m g am i fr HW HR HM HF Hk Hrc Hctx HP Hnl Rsp Asp HSTK HFP HAP) as FG. rewrite Estr in FG.
  pose proof (fg_RW _ _ _ _ _ _ _ _ _ _ _ FG) as RW'.
  destruct FG as [fg_HP fg_Rsp fg_Asp fg_HSTK fg_RB fg_AB fg_Roff fg_RPB fg_Rh3 fg_RG fg_Rav fg_Rfr fg_RW fg_Rsz fg_Rsec fg_REND fg_RENDR fg_Mh4 fg_Mh3 fg_Moff fg_Mmeta fg_Mmem fg_Mav fg_Mfr fg_MW fg_Marea fg_Mctx fg_Mnl fg_Mend fg_Mendr fg_Whdr fg_Wmeta fg_D1 fg_D2 fg_D3 fg_D4 fg_D5 fg_D6 fg_D7 fg_D8 fg_A1 fg_A2 fg_A3 fg_A5 fg_HIMG fg_GIMG fg_AG].
  repeat match goal with H : context [Z.land (hdr_byte3 am i fr) 31] |- _ => tryif (constr_eq H I0) then fail else rewrite I0 in H end.
  constructor; try assumption.
  all: rewrite ?I0, ?EML.
  all: try assumption.
  all: try rdn_match.
  all: try (clear - RW' Hml Rl Rs; unfold meta_bits in *; lia).
  all: try (match goal with H : ?lo <= ?X <= ?hi |- _ <= _ <= _ => clear - H Hml; lia end).
  all: try (match goal with H : _ <= bv_unsigned (getr regs 2) + -1024 |- _ <= bv_unsigned (getr regs 2) + -1024 => clear - H Hml; lia end).
  - clear - fg_D1 fg_Rsp fg_RB Hml. lia.
  - rewrite Z.shiftr_div_pow2 in * by lia. clear - fg_D1 fg_Rsp fg_RB fg_Rh3 Hml. lia.
  - clear - fg_A5 Hml. lia.
  - pose proof (GA6 Hml) as G6. replace (am_maplen am * 4096 / 16) with (am_maplen am * 256) in G6 by (replace (am_maplen am * 4096) with ((am_maplen am * 256) * 16) by ring; rewrite Z.div_mul by lia; reflexivity). clear - G6 Hml. lia.
  - rewrite EW31. exact Hl0.
  - rewrite ESC. exact Hsc.
Qed.

#[using="s HW HR HM HF Hk Hctx HP Hnl Rsp Asp HSTK HFP HAP"] Theorem free_pre_e5_of_model : am_sc am = 63 -> 5 <= frame_rsv am fr ->
  free_pre_e5 regs m (hdr_byte3 am i fr) (hdr_off16 am i fr) (loc_addr L (LMem g)) (am_avail am) (am_freed am) (meta_bits am)
           (ly_sec L mod 2^64) 1 (loc_addr L (LMem (am_mem am))) (frame_rsv am fr).
Proof. LiaFast.lf_pins (fun (s HW HR HM HF Hk Hctx HP Hnl Rsp Asp HSTK HFP HAP : LiaFast.U) => LiaFast.u0).
  intros Hsc Hrc. shape. direct_prep Hsc Cl. mapped_prep Hml Hl0 Hland Ri.
  pose proof (free_gen5_of_model L s regs m g am i fr HW HR HM HF Hk Hrc Hctx HP Hnl Rsp Asp HSTK HFP HAP) as FG. rewrite Estr in FG.
  pose proof (g5_RW _ _ _ _ _ _ _ _ _ _ _ _ FG) as RW'.
  destruct FG as [g5_HP g5_Rsp g5_Asp g5_HSTK g5_RB g5_AB g5_Roff g5_RPB g5_Rh3 g5_RG g5_Rav g5_Rfr g5_RW g5_Rsz g5_Rsec g5_REND g5_RENDR g5_Mh4 g5_Mh3 g5_Moff g5_Mmeta g5_Mmem g5_Mav g5_Mfr g5_MW g5_Marea g5_Mctx g5_Mnl g5_Mend g5_Mendr g5_Whdr g5_Wmeta g5_D1 g5_D2 g5_D3 g5_D4 g5_D5 g5_D6 g5_D7 g5_D8 g5_A1 g5_A2 g5_A3 g5_A5 g5_HIMG g5_GIMG g5_AG g5_Rrsv g5_Mrsv g5_Mend5].
  repeat match goal with H : context [Z.land (hdr_byte3 am i fr) 31] |- _ => tryif (constr_eq H I0) then fail else rewrite I0 in H end.
  constructor; try assumption.
  all: rewrite ?I0, ?EML.
  all: try assumption.
  all: try rdn_match.
  all: try (clear - RW' Hml Rl Rs; unfold meta_bits in *; lia).
  all: try (match goal with H : ?lo <= ?X <= ?hi |- _ <= _ <= _ => clear - H Hml; lia end).
  all: try (match goal with H : _ <= bv_unsigned (getr regs 2) + -1024 |- _ <= bv_unsigned (getr regs 2) + -1024 => clear - H Hml; lia end).
  - clear - g5_D1 g5_Rsp g5_RB Hml. lia.
  - clear - g5_D1 g5_A5 g5_Roff g5_Rsp g5_RB Hml g5_Rrsv. lia.
  - clear - g5_A5 Hml. lia.
  - pose proof (GA6 Hml) as G6. replace (am_maplen am * 4096 / 16) with (am_maplen am * 256) in G6 by (replace (am_maplen am * 4096) with ((am_maplen am * 256) * 16) by ring; rewrite Z.div_mul by lia; reflexivity). clear - G6 Hml. lia.
  - rewrite EW31. exact Hl0.
  - rewrite ESC. exact Hsc.
Qed.

End Spec.
End MngFreeM.

Import OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxMng OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxBits OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngZ OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngRepr OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngHeap OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngWb OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngFree OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngFree5 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_p4z OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_pd5z.AXF_p5z OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_tfz OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngFreeMem OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ffstep OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngFreeProA.MngFreeGeo OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_pd5z.AXF_p4mz OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_pd5z.AXF_p5mz OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_pd5z.AXF_pd4z OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_pd5z OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_pd5z.AXF_pe4z OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_pd5z.AXF_pe5z OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngFreeProA.MngFreeM.
Import ListNotations.

Module MngFreePro.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3 SeqExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMain.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGeom OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AxMng AxBits MngRepr MngHeap MngWb MngFree MngFree5 AXF_p4z.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_pd5z.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_tfz MngFreeMem AXG_ffstep.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxMng OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxBits OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngRepr OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngHeap OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngWb OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngFree OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngFree5 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_p4z OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_pd5z.AXF_p5z OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_tfz OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngFreeMem OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_ffstep OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngFreeProA.MngFreeGeo.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)
Lemma p5_tail_pre : forall (regs R : bvmap 5 word) m h3 off16 G avail freed W secret sz B rsv,
  free_pre5 regs m h3 off16 G avail freed W secret sz B rsv ->
  pro_regs R regs G W (Z.land h3 31) (16 * off16 + B + 16) ->
  tail_pre R (p4_mem m regs) G W (Z.land h3 31) (16 * off16 + B + 16)
    (bv_unsigned (getr regs 1)) (bv_unsigned (getr regs 8)) (bv_unsigned (getr regs 9)) (bv_unsigned (getr regs 18))
    (bv_unsigned (getr regs 19)) (bv_unsigned (getr regs 2)).
Proof.
  intros regs R m h3 off16 G avail freed W secret sz B rsv FP (P8 & P9 & P10 & P11 & P2 & _).
  pose proof (f5_Rsp _ _ _ _ _ _ _ _ _ _ _ _ FP) as Rsp. pose proof (f5_RPB _ _ _ _ _ _ _ _ _ _ _ _ FP) as RPB.
  pose proof (f5_Rh3 _ _ _ _ _ _ _ _ _ _ _ _ FP) as Rh3. pose proof (f5_RG _ _ _ _ _ _ _ _ _ _ _ _ FP) as RG.
  pose proof (f5_D3 _ _ _ _ _ _ _ _ _ _ _ _ FP) as D3. pose proof (f5_D5 _ _ _ _ _ _ _ _ _ _ _ _ FP) as D5.
  pose proof (f5_D7 _ _ _ _ _ _ _ _ _ _ _ _ FP) as D7. pose proof (f5_HIMG _ _ _ _ _ _ _ _ _ _ _ _ FP) as HIMG.
  pose proof (f5_GIMG _ _ _ _ _ _ _ _ _ _ _ _ FP) as GIMG. pose proof (f5_Whdr _ _ _ _ _ _ _ _ _ _ _ _ FP) as Whdr.
  pose proof (u64_range (getr regs 2)) as U2.
  constructor.
  - exact P8.
  - exact P9.
  - exact P10.
  - exact P11.
  - rewrite P2. reflexivity.
  - exact Rsp.
  - exact (f5_Asp _ _ _ _ _ _ _ _ _ _ _ _ FP).
  - rewrite wa_u. apply (stk_ok_grows SEGS m). { exact (f5_HSTK _ _ _ _ _ _ _ _ _ _ _ _ FP). } apply p4_mem_grows.
  - exact RG.
  - exact (f5_AG _ _ _ _ _ _ _ _ _ _ _ _ FP).
  - pose proof (f5_RW _ _ _ _ _ _ _ _ _ _ _ _ FP). clear - H. lia.
  - pose proof (land31_bound h3 ltac:(clear - Rh3; lia)). clear - H. lia.
  - clear - RPB D3 Rsp. lia.
  - pose proof (u64_range (getr regs 1)). clear - H. lia.
  - pose proof (u64_range (getr regs 8)). clear - H. lia.
  - pose proof (u64_range (getr regs 9)). clear - H. lia.
  - pose proof (u64_range (getr regs 18)). clear - H. lia.
  - pose proof (u64_range (getr regs 19)). clear - H. lia.
  - rewrite wa_u. apply (p4_rdn_save m regs Rsp 8 (fun R => getr R 1)). left. reflexivity.
  - rewrite wa_u. apply (p4_rdn_save m regs Rsp 16 (fun R => getr R 8)). right. left. reflexivity.
  - rewrite wa_u. apply (p4_rdn_save m regs Rsp 24 (fun R => getr R 9)). right. right. left. reflexivity.
  - rewrite wa_u. apply (p4_rdn_save m regs Rsp 32 (fun R => getr R 18)). right. right. right. left. reflexivity.
  - rewrite wa_u. apply (p4_rdn_save m regs Rsp 40 (fun R => getr R 19)). right. right. right. right. left. reflexivity.
  - intros d k Hd Hk. apply (store_ok_mono SEGS k m); [apply p4_mem_grows|].
    replace (16 * off16 + B + 16 + -3 + d) with (16 * off16 + B + 12 + (1 + d)) by ring. apply Whdr; clear - Hd Hk; lia.
  - clear - D3. lia.
  - clear - D5. lia.
  - clear - HIMG. lia.
  - exact GIMG.
  - clear - D7. lia.
Qed.

(* [comment removed for export] *)
Record free_common (m : word -> option byte) (sp0 G W avail freed idx : Z) : Prop := {
  fc_Rav : 0 <= avail <= 2^32 - 1 ; fc_Rfr : 0 <= freed <= 2^32 - 1 ;
  fc_RG : 1 <= G <= 2^63-1 ; fc_RW : 0 <= W <= 3071 ; fc_D5 : G + 40 <= sp0 - 1024 ;
  fc_Mav : rdn SEGS m (wa (G + 24)) 4 = Some (word_to_le_bytes 4 (wa avail)) ;
  fc_Mfr : rdn SEGS m (wa (G + 28)) 4 = Some (word_to_le_bytes 4 (wa freed)) ;
  fc_MW : rdn SEGS m (wa (G + 32)) 8 = Some (word_to_le_bytes 8 (wa W)) ;
  fc_Wmeta : (forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (G + 24 + d)) k = true) ;
  fc_A2 : Z.testbit avail idx = false ; fc_A3 : Z.testbit freed idx = false
}.

Section Pro.
Context {fx : FPState}.

#[using="Type"] Theorem free_prologue : forall L s (regs : bvmap 5 word) m rom g am i fr,
  Heap0 L s m ->
  In (g, am, i, fr) (frames s) -> fr_kind fr = FUser -> am_maplen am = 0 ->
  ly_ctx L = 0x95ed8 ->
  getr regs 10 = wa (loc_addr L (LMem (frame_ptr am i fr))) ->
  rdn SEGS m (wa 613987) 1 = Some (word_to_le_bytes 1 (wa 0)) ->
  (forall sc, 0 <= sc < 48 -> rdn SEGS m (wa (98984 + 2 * sc)) 2 = Some (word_to_le_bytes 2 (wa (znth sc size_classes)))) ->
  2^20 <= bv_unsigned (getr regs 2) <= 2^47 -> bv_unsigned (getr regs 2) mod 16 = 0 -> stk_ok SEGS m (getr regs 2) 1024 ->
  (forall rg, In rg (footprint s) -> loc_addr L (fst rg) + snd rg <= bv_unsigned (getr regs 2) - 1024) ->
  (forall rg, In rg (footprint s) -> fst rg <> LCtx 0 -> ranges_disjoint (crange L rg) (0x10000, 0x87000)) ->
  exists R1, msteps SEGS (mkst regs (wa 0x511d0) m rom) (mkst R1 (wa 0x516d0) (p4_mem m regs) rom)
    /\ pro_regs R1 regs (loc_addr L (LMem g)) (meta_bits am) i (loc_addr L (LMem (frame_ptr am i fr)))
    /\ tail_pre R1 (p4_mem m regs) (loc_addr L (LMem g)) (meta_bits am) i (loc_addr L (LMem (frame_ptr am i fr)))
         (bv_unsigned (getr regs 1)) (bv_unsigned (getr regs 8)) (bv_unsigned (getr regs 9)) (bv_unsigned (getr regs 18))
         (bv_unsigned (getr regs 19)) (bv_unsigned (getr regs 2))
    /\ free_common m (bv_unsigned (getr regs 2)) (loc_addr L (LMem g)) (meta_bits am) (am_avail am) (am_freed am) i.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L s regs m rom g am i fr (HW & HR & HM) HF Hk Hml Hctx HP Hnl Htab Rsp Asp HSTK HFP HAP.
  pose proof (get_meta_ok s g am i fr HW HF) as GM. cbn zeta in GM.
  destruct GM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hland & _ & _).
  pose proof HR as (HL & _ & _).
  destruct (MngFreeGeo.free_cells_geom L s g am i fr (bv_unsigned (getr regs 2)) HW HL HF HFP) as (Gp & _ & _ & _).
  destruct (Z_lt_le_dec (frame_rsv am fr) 5) as [Hr4|Hr5].
  - assert (Hrc : rsv_code am fr < 5).
    { unfold rsv_code. unfold frame_rsv in Hr4. destruct (5 <=? _) eqn:E; [apply Z.leb_le in E; lia | lia]. }
    pose proof (free_pre_of_model L s regs m g am i fr HW HR HM HF Hk Hml Hrc Hctx HP Hnl Htab Rsp Asp HSTK HFP HAP) as FP.
    assert (EP : loc_addr L (LMem (frame_ptr am i fr)) = 16 * hdr_off16 am i fr + loc_addr L (LMem (am_mem am)) + 16).
    { pose proof (fp_HP _ _ _ _ _ _ _ _ _ _ _ FP) as HP'. rewrite HP in HP'. pose proof (f_equal bv_unsigned HP') as E. rewrite !u_wa in E.
      pose proof (fp_RPB _ _ _ _ _ _ _ _ _ _ _ FP) as R1'.
      rewrite (Z.mod_small (loc_addr L (LMem (frame_ptr am i fr)))) in E by (clear - Gp Rsp; lia).
      rewrite Z.mod_small in E by (clear - R1'; lia). exact E. }
    destruct (p4_arm regs m rom _ _ _ _ _ _ _ _ _ FP) as (R1 & Hms1 & PRO).
    pose proof (p4_tail_pre regs R1 m _ _ _ _ _ _ _ _ _ FP PRO) as TP.
    rewrite Hland, <- EP in PRO, TP.
    exists R1. split; [exact Hms1|]. split; [exact PRO|]. split; [exact TP|].
    constructor.
    + exact (fp_Rav _ _ _ _ _ _ _ _ _ _ _ FP).
    + exact (fp_Rfr _ _ _ _ _ _ _ _ _ _ _ FP).
    + exact (fp_RG _ _ _ _ _ _ _ _ _ _ _ FP).
    + exact (fp_RW _ _ _ _ _ _ _ _ _ _ _ FP).
    + pose proof (fp_D5 _ _ _ _ _ _ _ _ _ _ _ FP). clear - H. lia.
    + exact (fp_Mav _ _ _ _ _ _ _ _ _ _ _ FP).
    + exact (fp_Mfr _ _ _ _ _ _ _ _ _ _ _ FP).
    + exact (fp_MW _ _ _ _ _ _ _ _ _ _ _ FP).
    + exact (fp_Wmeta _ _ _ _ _ _ _ _ _ _ _ FP).
    + rewrite <- Hland. exact (fp_A2 _ _ _ _ _ _ _ _ _ _ _ FP).
    + rewrite <- Hland. exact (fp_A3 _ _ _ _ _ _ _ _ _ _ _ FP).
  - pose proof (free_pre5_of_model L s regs m g am i fr HW HR HM HF Hk Hml Hr5 Hctx HP Hnl Htab Rsp Asp HSTK HFP HAP) as FP.
    assert (EP : loc_addr L (LMem (frame_ptr am i fr)) = 16 * hdr_off16 am i fr + loc_addr L (LMem (am_mem am)) + 16).
    { pose proof (f5_HP _ _ _ _ _ _ _ _ _ _ _ _ FP) as HP'. rewrite HP in HP'. pose proof (f_equal bv_unsigned HP') as E. rewrite !u_wa in E.
      pose proof (f5_RPB _ _ _ _ _ _ _ _ _ _ _ _ FP) as R1'.
      rewrite (Z.mod_small (loc_addr L (LMem (frame_ptr am i fr)))) in E by (clear - Gp Rsp; lia).
      rewrite Z.mod_small in E by (clear - R1'; lia). exact E. }
    destruct (p5_arm regs m rom _ _ _ _ _ _ _ _ _ _ FP) as (R1 & Hms1 & PRO).
    pose proof (p5_tail_pre regs R1 m _ _ _ _ _ _ _ _ _ _ FP PRO) as TP.
    rewrite Hland, <- EP in PRO, TP.
    exists R1. split; [exact Hms1|]. split; [exact PRO|]. split; [exact TP|].
    constructor.
    + exact (f5_Rav _ _ _ _ _ _ _ _ _ _ _ _ FP).
    + exact (f5_Rfr _ _ _ _ _ _ _ _ _ _ _ _ FP).
    + exact (f5_RG _ _ _ _ _ _ _ _ _ _ _ _ FP).
    + exact (f5_RW _ _ _ _ _ _ _ _ _ _ _ _ FP).
    + pose proof (f5_D5 _ _ _ _ _ _ _ _ _ _ _ _ FP). clear - H. lia.
    + exact (f5_Mav _ _ _ _ _ _ _ _ _ _ _ _ FP).
    + exact (f5_Mfr _ _ _ _ _ _ _ _ _ _ _ _ FP).
    + exact (f5_MW _ _ _ _ _ _ _ _ _ _ _ _ FP).
    + exact (f5_Wmeta _ _ _ _ _ _ _ _ _ _ _ _ FP).
    + rewrite <- Hland. exact (f5_A2 _ _ _ _ _ _ _ _ _ _ _ _ FP).
    + rewrite <- Hland. exact (f5_A3 _ _ _ _ _ _ _ _ _ _ _ _ FP).
Qed.
End Pro.

(* [comment removed for export] *)
Lemma free_cells_img : forall L s g am i fr x, WF s -> layout_ok L s -> In (g, am, i, fr) (frames s) ->
  (loc_addr L (LMem (frame_ptr am i fr)) - 3 <= x < loc_addr L (LMem (frame_ptr am i fr))) \/
  (loc_addr L (LMem g) + 28 <= x < loc_addr L (LMem g) + 32) -> exists c, In c (image s) /\ in_rng (cell_range L c) x.
Proof.
  intros L s g am i fr x HW HL HF Hx.
  pose proof (get_meta_ok s g am i fr HW HF) as GM. cbn zeta in GM.
  destruct GM as (_ & Ch3 & Ch16 & _ & _ & _ & Cfr & _).
  destruct Hx as [Hx|Hx].
  - destruct (Z.eq_dec x (loc_addr L (LMem (frame_ptr am i fr)) - 3)) as [->|Hne].
    + eexists; split; [exact Ch3|]. unfold in_rng, cell_range. cbn [fst snd mc_loc mc_w]. rewrite loc_padd. lia.
    + eexists; split; [exact Ch16|]. unfold in_rng, cell_range. cbn [fst snd mc_loc mc_w]. rewrite loc_padd. lia.
  - eexists; split; [exact Cfr|]. unfold in_rng, cell_range. cbn [fst snd mc_loc mc_w]. rewrite loc_padd. unfold META_freed. lia.
Qed.
End MngFreePro.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)
Lemma tail_pre_gen : forall (regs R : bvmap 5 word) m h3 off16 G W B,
  2^20 <= bv_unsigned (getr regs 2) <= 2^47 ->
  bv_unsigned (getr regs 2) mod 16 = 0 ->
  stk_ok SEGS m (getr regs 2) 1024 ->
  1 <= 16 * off16 + B <= 2^63-1 ->
  0 <= h3 ->
  1 <= G <= 2^63-1 ->
  G mod 8 = 0 ->
  0 <= W <= 2^64-1 ->
  16 * off16 + B + 12 + 4 <= bv_unsigned (getr regs 2) + -1024 ->
  G + 0 + 40 <= bv_unsigned (getr regs 2) + -1024 ->
  (G + 0 + 40 <= 16 * off16 + B + 12 \/ 16 * off16 + B + 12 + 4 <= G + 0) ->
  16 * off16 + B + 16 <= 0x10000 \/ 0x97000 <= 16 * off16 + B + 12 ->
  G + 40 <= 0x10000 \/ 0x97000 <= G ->
  (forall d k, 0 <= d -> d + Z.of_nat k <= 4 -> store_ok SEGS m (wa (16 * off16 + B + 12 + d)) k = true) ->
  pro_regs R regs G W (Z.land h3 31) (16 * off16 + B + 16) ->
  tail_pre R (p4_mem m regs) G W (Z.land h3 31) (16 * off16 + B + 16)
    (bv_unsigned (getr regs 1)) (bv_unsigned (getr regs 8)) (bv_unsigned (getr regs 9)) (bv_unsigned (getr regs 18))
    (bv_unsigned (getr regs 19)) (bv_unsigned (getr regs 2)).
Proof.
  intros regs R m h3 off16 G W B Rsp Asp HSTK RPB Rh3 RG AG RW D3 D5 D7 HIMG GIMG Whdr (P8 & P9 & P10 & P11 & P2 & _).
  constructor.
  - exact P8.
  - exact P9.
  - exact P10.
  - exact P11.
  - rewrite P2. reflexivity.
  - exact Rsp.
  - exact Asp.
  - rewrite wa_u. apply (stk_ok_grows SEGS m). { exact HSTK. } apply p4_mem_grows.
  - exact RG.
  - exact AG.
  - exact RW.
  - pose proof (land31_bound h3 Rh3). clear - H. lia.
  - clear - RPB D3 Rsp. lia.
  - pose proof (u64_range (getr regs 1)). clear - H. lia.
  - pose proof (u64_range (getr regs 8)). clear - H. lia.
  - pose proof (u64_range (getr regs 9)). clear - H. lia.
  - pose proof (u64_range (getr regs 18)). clear - H. lia.
  - pose proof (u64_range (getr regs 19)). clear - H. lia.
  - rewrite wa_u. apply (p4_rdn_save m regs Rsp 8 (fun R => getr R 1)). left. reflexivity.
  - rewrite wa_u. apply (p4_rdn_save m regs Rsp 16 (fun R => getr R 8)). right. left. reflexivity.
  - rewrite wa_u. apply (p4_rdn_save m regs Rsp 24 (fun R => getr R 9)). right. right. left. reflexivity.
  - rewrite wa_u. apply (p4_rdn_save m regs Rsp 32 (fun R => getr R 18)). right. right. right. left. reflexivity.
  - rewrite wa_u. apply (p4_rdn_save m regs Rsp 40 (fun R => getr R 19)). right. right. right. right. left. reflexivity.
  - intros d k Hd Hk. apply (store_ok_mono SEGS k m); [apply p4_mem_grows|].
    replace (16 * off16 + B + 16 + -3 + d) with (16 * off16 + B + 12 + (1 + d)) by ring. apply Whdr; clear - Hd Hk; lia.
  - clear - D3. lia.
  - clear - D5. lia.
  - clear - HIMG. lia.
  - exact GIMG.
  - clear - D7. lia.
Qed.

(* [comment removed for export] *)
Record free_commonA (m : word -> option byte) (sp0 G W avail freed idx : Z) : Prop := {
  fa_Rav : 0 <= avail <= 2^32 - 1 ; fa_Rfr : 0 <= freed <= 2^32 - 1 ;
  fa_RG : 1 <= G <= 2^63-1 ; fa_RW : 0 <= W <= 2^64-1 ; fa_D5 : G + 40 <= sp0 - 1024 ;
  fa_Mav : rdn SEGS m (wa (G + 24)) 4 = Some (word_to_le_bytes 4 (wa avail)) ;
  fa_Mfr : rdn SEGS m (wa (G + 28)) 4 = Some (word_to_le_bytes 4 (wa freed)) ;
  fa_MW : rdn SEGS m (wa (G + 32)) 8 = Some (word_to_le_bytes 8 (wa W)) ;
  fa_Wmeta : (forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (G + 24 + d)) k = true) ;
  fa_A2 : Z.testbit avail idx = false ; fa_A3 : Z.testbit freed idx = false
}.

Lemma commonA_of : forall m sp0 G W avail freed h3,
  0 <= avail <= 2^32 - 1 -> 0 <= freed <= 2^32 - 1 -> 1 <= G <= 2^63-1 -> 0 <= W <= 2^64-1 ->
  G + 0 + 40 <= sp0 + -1024 ->
  rdn SEGS m (wa (G + 24)) 4 = Some (word_to_le_bytes 4 (wa avail)) ->
  rdn SEGS m (wa (G + 28)) 4 = Some (word_to_le_bytes 4 (wa freed)) ->
  rdn SEGS m (wa (G + 32)) 8 = Some (word_to_le_bytes 8 (wa W)) ->
  (forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (G + 24 + d)) k = true) ->
  Z.testbit avail (Z.land h3 31) = false -> Z.testbit freed (Z.land h3 31) = false ->
  free_commonA m sp0 G W avail freed (Z.land h3 31).
Proof.
  intros m sp0 G W avail freed h3 Rav Rfr RG RW D5 Mav Mfr MW Wmeta A2 A3.
  constructor; try assumption. clear - D5. lia.
Qed.

(* [comment removed for export] *)
Local Ltac fin L regs m g am i fr Hland Gp Rsp HP R1 Hms1 PRO :=
  lazymatch goal with
  | H : getr _ _ = wa (16 * ?off + ?B + 16), RPB : 1 <= 16 * ?off + ?B <= 2^63-1 |- _ =>
      let EP := fresh "EP" in
      assert (EP : loc_addr L (LMem (frame_ptr am i fr)) = 16 * off + B + 16)
        by (let HP' := fresh in pose proof H as HP'; rewrite HP in HP';
            let E := fresh in pose proof (f_equal bv_unsigned HP') as E; rewrite !u_wa in E;
            rewrite (Z.mod_small (loc_addr L (LMem (frame_ptr am i fr)))) in E by (clear - Gp Rsp; lia);
            rewrite Z.mod_small in E by (clear - RPB; lia); exact E)
  end;
  let TP := fresh "TP" in
  lazymatch goal with
  | RW : ?lw <= meta_bits am <= ?hw, Rh3 : ?lh <= hdr_byte3 am i fr <= ?hh |- _ =>
      pose proof (tail_pre_gen regs R1 m (hdr_byte3 am i fr) (hdr_off16 am i fr) (loc_addr L (LMem g)) (meta_bits am)
                    (loc_addr L (LMem (am_mem am)))
                    ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)
                    ltac:(clear - Rh3; lia) ltac:(assumption) ltac:(assumption) ltac:(clear - RW; lia)
                    ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) PRO) as TP
  end;
  let FC := fresh "FC" in
  lazymatch goal with
  | RW : ?lw <= meta_bits am <= ?hw |- _ =>
      pose proof (commonA_of m (bv_unsigned (getr regs 2)) (loc_addr L (LMem g)) (meta_bits am) (am_avail am) (am_freed am)
                    (hdr_byte3 am i fr)
                    ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(clear - RW; lia)
                    ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)
                    ltac:(assumption) ltac:(assumption)) as FC
  end;
  lazymatch goal with EP : loc_addr _ (LMem (frame_ptr _ _ _)) = _ |- _ => rewrite Hland, <- EP in PRO, TP end;
  rewrite Hland in FC;
  exists R1; split; [exact Hms1|]; split; [exact PRO|]; split; [exact TP|exact FC].

Section Pro.
Context {fx : FPState}.

#[using="Type"] Theorem free_prologue_any : forall L s (regs : bvmap 5 word) m rom g am i fr,
  Heap0 L s m ->
  In (g, am, i, fr) (frames s) -> fr_kind fr = FUser ->
  ly_ctx L = 0x95ed8 ->
  getr regs 10 = wa (loc_addr L (LMem (frame_ptr am i fr))) ->
  rdn SEGS m (wa 613987) 1 = Some (word_to_le_bytes 1 (wa 0)) ->
  (forall sc, 0 <= sc < 48 -> rdn SEGS m (wa (98984 + 2 * sc)) 2 = Some (word_to_le_bytes 2 (wa (znth sc size_classes)))) ->
  2^20 <= bv_unsigned (getr regs 2) <= 2^47 -> bv_unsigned (getr regs 2) mod 16 = 0 -> stk_ok SEGS m (getr regs 2) 1024 ->
  (forall rg, In rg (footprint s) -> loc_addr L (fst rg) + snd rg <= bv_unsigned (getr regs 2) - 1024) ->
  (forall rg, In rg (footprint s) -> fst rg <> LCtx 0 -> ranges_disjoint (crange L rg) (0x10000, 0x87000)) ->
  exists R1, msteps SEGS (mkst regs (wa 0x511d0) m rom) (mkst R1 (wa 0x516d0) (p4_mem m regs) rom)
    /\ pro_regs R1 regs (loc_addr L (LMem g)) (meta_bits am) i (loc_addr L (LMem (frame_ptr am i fr)))
    /\ tail_pre R1 (p4_mem m regs) (loc_addr L (LMem g)) (meta_bits am) i (loc_addr L (LMem (frame_ptr am i fr)))
         (bv_unsigned (getr regs 1)) (bv_unsigned (getr regs 8)) (bv_unsigned (getr regs 9)) (bv_unsigned (getr regs 18))
         (bv_unsigned (getr regs 19)) (bv_unsigned (getr regs 2))
    /\ free_commonA m (bv_unsigned (getr regs 2)) (loc_addr L (LMem g)) (meta_bits am) (am_avail am) (am_freed am) i.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L s regs m rom g am i fr (HW & HR & HM) HF Hk Hctx HP Hnl Htab Rsp Asp HSTK HFP HAP.
  pose proof (get_meta_ok s g am i fr HW HF) as GM. cbn zeta in GM.
  destruct GM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hland & _ & _).
  pose proof HR as (HL & _ & _).
  destruct (MngFreeGeo.free_cells_geom L s g am i fr (bv_unsigned (getr regs 2)) HW HL HF HFP) as (Gp & _ & _ & _).
  destruct (frame_shape s g am i fr HW HF) as (Rl & Rs & Rm & Ri & Cl & Has).
  assert (RC : rsv_code am fr < 5 \/ 5 <= frame_rsv am fr).
  { destruct (Z_lt_le_dec (frame_rsv am fr) 5) as [Hr4|Hr5]; [left|right; exact Hr5].
    unfold rsv_code. unfold frame_rsv in Hr4. destruct (5 <=? _) eqn:E; [apply Z.leb_le in E; lia | lia]. }
  destruct (Z.eq_dec (am_maplen am) 0) as [Hml|Hml].
  - (* [comment removed for export] *)
    destruct RC as [Hrc|Hrc].
    + pose proof (free_pre_of_model L s regs m g am i fr HW HR HM HF Hk Hml Hrc Hctx HP Hnl Htab Rsp Asp HSTK HFP HAP) as FP.
      destruct (p4_arm regs m rom _ _ _ _ _ _ _ _ _ FP) as (R1 & Hms1 & PRO).
      destruct FP. fin L regs m g am i fr Hland Gp Rsp HP R1 Hms1 PRO.
    + pose proof (free_pre5_of_model L s regs m g am i fr HW HR HM HF Hk Hml Hrc Hctx HP Hnl Htab Rsp Asp HSTK HFP HAP) as FP.
      destruct (p5_arm regs m rom _ _ _ _ _ _ _ _ _ _ FP) as (R1 & Hms1 & PRO).
      destruct FP. fin L regs m g am i fr Hland Gp Rsp HP R1 Hms1 PRO.
  - assert (Hml' : 0 < am_maplen am) by (clear - Hml Rm; lia).
    destruct (Z.eq_dec (am_last am) 0) as [Hl0|Hl0].
    + destruct Cl as [(C63 & _ & _)|Csc].
      * (* [comment removed for export] *)
        destruct RC as [Hrc|Hrc].
        -- pose proof (free_pre_e_of_model L s regs m g am i fr HW HR HM HF Hk Hctx HP Hnl Rsp Asp HSTK HFP HAP C63 Hrc) as FP.
           destruct (pe4_arm regs m rom _ _ _ _ _ _ _ _ _ FP) as (R1 & Hms1 & PRO).
           destruct FP. fin L regs m g am i fr Hland Gp Rsp HP R1 Hms1 PRO.
        -- pose proof (free_pre_e5_of_model L s regs m g am i fr HW HR HM HF Hk Hctx HP Hnl Rsp Asp HSTK HFP HAP C63 Hrc) as FP.
           destruct (pe5_arm regs m rom _ _ _ _ _ _ _ _ _ _ FP) as (R1 & Hms1 & PRO).
           destruct FP. fin L regs m g am i fr Hland Gp Rsp HP R1 Hms1 PRO.
      * (* [comment removed for export] *)
        destruct RC as [Hrc|Hrc].
        -- pose proof (free_prd_of_model L s regs m g am i fr HW HR HM HF Hk Hctx HP Hnl Htab Rsp Asp HSTK HFP HAP Hml' Hl0 Csc Hrc) as FP.
           destruct (pd4_arm regs m rom _ _ _ _ _ _ _ _ _ FP) as (R1 & Hms1 & PRO).
           destruct FP. fin L regs m g am i fr Hland Gp Rsp HP R1 Hms1 PRO.
        -- pose proof (free_prd5_of_model L s regs m g am i fr HW HR HM HF Hk Hctx HP Hnl Htab Rsp Asp HSTK HFP HAP Hml' Hl0 Csc Hrc) as FP.
           destruct (pd5_arm regs m rom _ _ _ _ _ _ _ _ _ _ FP) as (R1 & Hms1 & PRO).
           destruct FP. fin L regs m g am i fr Hland Gp Rsp HP R1 Hms1 PRO.
    + (* [comment removed for export] *)
      destruct RC as [Hrc|Hrc].
      * pose proof (free_prem_of_model L s regs m g am i fr HW HR HM HF Hk Hctx HP Hnl Htab Rsp Asp HSTK HFP HAP Hml' Hl0 Hrc) as FP.
        destruct (p4m_arm regs m rom _ _ _ _ _ _ _ _ _ FP) as (R1 & Hms1 & PRO).
        destruct FP. fin L regs m g am i fr Hland Gp Rsp HP R1 Hms1 PRO.
      * pose proof (free_prem5_of_model L s regs m g am i fr HW HR HM HF Hk Hctx HP Hnl Htab Rsp Asp HSTK HFP HAP Hml' Hl0 Hrc) as FP.
        destruct (p5m_arm regs m rom _ _ _ _ _ _ _ _ _ _ FP) as (R1 & Hms1 & PRO).
        destruct FP. fin L regs m g am i fr Hland Gp Rsp HP R1 Hms1 PRO.
Qed.
End Pro.
