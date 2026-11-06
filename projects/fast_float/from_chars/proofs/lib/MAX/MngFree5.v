(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngRepr MngHeap MngFree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.


Record free_pre5 (regs : bvmap 5 word) (m : word -> option byte) (h3 off16 G avail freed W secret sz B rsv : Z) : Prop := {
  f5_HP : getr regs 10 = wa (16 * off16 + B + 16) ;
  f5_Rsp : 2^20 <= bv_unsigned (getr regs 2) <= 2^47 ;
  f5_Asp : bv_unsigned (getr regs 2) mod 16 = 0 ;
  f5_HSTK : stk_ok SEGS m (getr regs 2) 1024 ;
  f5_RB : 1 <= B <= 2^63-1 ;
  f5_AB : B mod 16 = 0 ;
  f5_Roff : 0 <= off16 <= 65535 ;
  f5_RPB : 1 <= 16 * off16 + B <= 2^63-1 ;
  f5_Rh3 : 160 <= h3 <= 191 ;
  f5_RG : 1 <= G <= 2^63-1 ;
  f5_Rav : 0 <= avail <= 2^32 - 1 ;
  f5_Rfr : 0 <= freed <= 2^32 - 1 ;
  f5_RW : 0 <= W <= 3071 ;
  f5_Rsz : 1 <= sz <= 8191 ;
  f5_Rsec : 0 <= secret <= 2^64 - 1 ;
  f5_REND : 1 <= 16 * sz + (B + 16 * sz * Z.land h3 31) <= 2^63-1 ;
  f5_RENDR : 1 <= 16 * sz + (B + (16 * sz * Z.land h3 31 + -1 * rsv)) <= 2^63-1 ;
  f5_Mh4 : rdn SEGS m (wa (16 * off16 + B + 12)) 1 = Some (word_to_le_bytes 1 (wa 0)) ;
  f5_Mh3 : rdn SEGS m (wa (16 * off16 + B + 13)) 1 = Some (word_to_le_bytes 1 (wa h3)) ;
  f5_Moff : rdn SEGS m (wa (16 * off16 + B + 14)) 2 = Some (word_to_le_bytes 2 (wa off16)) ;
  f5_Mmeta : rdn SEGS m (wa (B + 0)) 8 = Some (word_to_le_bytes 8 (wa G)) ;
  f5_Mmem : rdn SEGS m (wa (G + 16)) 8 = Some (word_to_le_bytes 8 (wa B)) ;
  f5_Mav : rdn SEGS m (wa (G + 24)) 4 = Some (word_to_le_bytes 4 (wa avail)) ;
  f5_Mfr : rdn SEGS m (wa (G + 28)) 4 = Some (word_to_le_bytes 4 (wa freed)) ;
  f5_MW : rdn SEGS m (wa (G + 32)) 8 = Some (word_to_le_bytes 8 (wa W)) ;
  f5_Marea : rdn SEGS m (wa (4096 * (G / 4096) + 0)) 8 = Some (word_to_le_bytes 8 (wa secret)) ;
  f5_Mctx : rdn SEGS m (wa (0 + 614104)) 8 = Some (word_to_le_bytes 8 (wa secret)) ;
  f5_Mnl : rdn SEGS m (wa (0 + 613987)) 1 = Some (word_to_le_bytes 1 (wa 0)) ;
  f5_Mtab : rdn SEGS m (wa (2 * Z.shiftr W 6 + 98984)) 2 = Some (word_to_le_bytes 2 (wa sz)) ;
  f5_Mend : rdn SEGS m (wa (16 * sz + (B + 16 * sz * Z.land h3 31) + 12)) 1 = Some (word_to_le_bytes 1 (wa 0)) ;
  f5_Mendr : rdn SEGS m (wa (16 * sz + (B + (16 * sz * Z.land h3 31 + -1 * rsv)) + 12)) 1 = Some (word_to_le_bytes 1 (wa 0)) ;
  f5_Whdr : (forall d k, 0 <= d -> d + Z.of_nat k <= 4 -> store_ok SEGS m (wa (16 * off16 + B + 12 + d)) k = true) ;
  f5_Wmeta : (forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (G + 24 + d)) k = true) ;
  f5_D1 : 16 * sz + (B + 16 * sz * Z.land h3 31) + 12 + 1 <= bv_unsigned (getr regs 2) + -1024 ;
  f5_D2 : 16 * sz + (B + (16 * sz * Z.land h3 31 + -1 * rsv)) + 12 + 1 <= bv_unsigned (getr regs 2) + -1024 ;
  f5_D3 : 16 * off16 + B + 12 + 4 <= bv_unsigned (getr regs 2) + -1024 ;
  f5_D4 : B + 0 + 8 <= bv_unsigned (getr regs 2) + -1024 ;
  f5_D5 : G + 0 + 40 <= bv_unsigned (getr regs 2) + -1024 ;
  f5_D6 : 4096 * (G / 4096) + 0 + 8 <= bv_unsigned (getr regs 2) + -1024 ;
  f5_D7 : (G + 0 + 40 <= 16 * off16 + B + 12 \/ 16 * off16 + B + 12 + 4 <= G + 0) ;
  f5_D8 : (0 + 613987 + 1 <= 16 * off16 + B + 12 \/ 16 * off16 + B + 12 + 4 <= 0 + 613987) ;
  f5_A1 : Z.land h3 31 <= Z.land W 31 ;
  f5_A2 : Z.testbit avail (Z.land h3 31) = false ;
  f5_A3 : Z.testbit freed (Z.land h3 31) = false ;
  f5_A4 : sz * Z.land h3 31 <= off16 < sz * (Z.land h3 31 + 1) ;
  f5_A5 : rsv <= -16 * off16 + (16 * sz + 16 * sz * Z.land h3 31) + -4 ;
  f5_HIMG : 16 * off16 + B + 16 <= 0x10000 \/ 0x97000 <= 16 * off16 + B + 12 ;
  f5_GIMG : G + 40 <= 0x10000 \/ 0x97000 <= G ;
  f5_AG : G mod 8 = 0 ;
  f5_Rrsv : 5 <= rsv <= 2^32 - 1 ;
  f5_Mrsv : rdn SEGS m (wa (16 * sz + (B + 16 * sz * Z.land h3 31) + 8)) 4 = Some (word_to_le_bytes 4 (wa rsv)) ;
  f5_Mend5 : rdn SEGS m (wa (16 * sz + (B + 16 * sz * Z.land h3 31) + 7)) 1 = Some (word_to_le_bytes 1 (wa 0))
}.

Ltac cellrd HC C Hr :=
  pose proof (holds_rdn _ _ _ _ (proj1 (Forall_forall _ _) HC _ C) ltac:(intros z Hz; discriminate) ltac:(cbn [mc_w]; apply Nat.leb_le; reflexivity)) as Hr;
  cbn [mc_loc mc_w mc_val sval_num] in Hr; rewrite ?loc_padd in Hr.

Ltac rdn_by Hr :=
  lazymatch type of Hr with
  | rdn ?s ?mm (wa ?A') ?n = Some (word_to_le_bytes ?n (wa ?V')) =>
      lazymatch goal with
      | |- rdn s mm (wa ?A) n = Some (word_to_le_bytes n (wa ?V)) =>
          replace A with A' by ring; replace V with V' by ring; exact Hr
      end
  end.


Theorem free_pre5_of_model : forall L s (regs : bvmap 5 word) (m : word -> option byte) g am i fr,
  WF s -> repr L s (bview SEGS m) -> markers_hold L s (bview SEGS m) ->
  In (g, am, i, fr) (frames s) -> fr_kind fr = FUser -> am_maplen am = 0 -> 5 <= frame_rsv am fr ->
  ly_ctx L = 0x95ed8 ->
  getr regs 10 = wa (loc_addr L (LMem (frame_ptr am i fr))) ->
  rdn SEGS m (wa 613987) 1 = Some (word_to_le_bytes 1 (wa 0)) ->
  (forall sc, 0 <= sc < 48 -> rdn SEGS m (wa (98984 + 2 * sc)) 2 = Some (word_to_le_bytes 2 (wa (znth sc size_classes)))) ->
  2^20 <= bv_unsigned (getr regs 2) <= 2^47 -> bv_unsigned (getr regs 2) mod 16 = 0 -> stk_ok SEGS m (getr regs 2) 1024 ->
  (forall rg, In rg (footprint s) -> loc_addr L (fst rg) + snd rg <= bv_unsigned (getr regs 2) - 1024) ->
  (forall rg, In rg (footprint s) -> fst rg <> LCtx 0 -> ranges_disjoint (crange L rg) (0x10000, 0x87000)) ->
  free_pre5 regs m (hdr_byte3 am i fr) (hdr_off16 am i fr) (loc_addr L (LMem g)) (am_avail am) (am_freed am) (meta_bits am)
           (ly_sec L mod 2^64) (znth (am_sc am) size_classes) (loc_addr L (LMem (am_mem am))) (frame_rsv am fr).
Proof.
  intros L s regs m g am i fr HW HR HM HF Hk Hml Hrc Hctx HP Hnl Htab Rsp Asp HSTK HFP HAP.
  pose proof (get_meta_ok s g am i fr HW HF) as GM. cbn zeta in GM.
  destruct GM as (Ch4 & Ch3 & Ch16 & Cgm & Cmem & Cav & Cfr & Cbits & Geo & (a & k & Ha & Hk0 & Hga & Carea & Csec) & Hland & Hasrt & _).
  destruct (in_frames_inv s g am i fr HF) as (Hu & Hi & Hfri).
  apply (used_metas_usedX s g am HW) in Hu as Hux.
  pose proof (inv_groups HW g am Hux) as (Gm & Gml & Gsl & Gcl & Gmp & Gns).
  pose proof (Gsl i Hi) as (S1 & S2 & S3). rewrite Hfri in S3. destruct S3 as (Hal & _ & FOK & Hhdr).
  destruct FOK as (Fn & Foff & Ffit & F16 & _).
  destruct Gm as (Mlast & Maidx & Mlen & Mav0 & Mfr0 & Mdisj & Mabove & _ & _).
  destruct Gcl as [(C63 & _) | (Csc & _ & _ & Cspan)].
  { (* [comment removed for export] *) exfalso. destruct (Gns Hml) as (N63 & _). exact (N63 C63). }
  set (p := frame_ptr am i fr) in *.
  set (B := loc_addr L (LMem (am_mem am))).
  set (G := loc_addr L (LMem g)).
  set (h3 := hdr_byte3 am i fr) in *.
  set (off16 := hdr_off16 am i fr) in *.
  set (sz := znth (am_sc am) size_classes).
  assert (Hstr : stride_of am = 16 * sz).
  { unfold stride_of. rewrite Hml. replace ((am_last am =? 0) && negb (0 =? 0)) with false by (destruct (am_last am =? 0); reflexivity).
    unfold class_size, UNIT. reflexivity. }
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
  assert (Hsc : 0 <= am_sc am < 48) by exact Csc.
  pose proof (size_classes_range _ Hsc) as Rsz. fold sz in Rsz.
  assert (Hrsv0 : 0 <= frame_rsv am fr) by (clear - Ffit; unfold frame_rsv, UNIT, IB in *; lia).
  assert (Hrceq : rsv_code am fr = 5).
  { clear - Hrc. unfold rsv_code. unfold frame_rsv in Hrc. destruct (5 <=? _) eqn:E; [reflexivity | apply Z.leb_gt in E; lia]. }
  assert (Eh3 : h3 = i + 32 * rsv_code am fr) by (unfold h3, hdr_byte3; rewrite Hk; reflexivity).
  assert (Eoff : off16 = sz * i + fr_off fr).
  { unfold off16, hdr_off16. rewrite Hstr. unfold UNIT. replace (16 * sz * i) with ((sz * i) * 16) by ring.
    rewrite Z.div_mul by lia. reflexivity. }
  assert (Hsi : 0 <= sz * i <= sz * am_last am) by (clear - Rsz Hi; split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg_l; lia]).
  assert (Hext' : poff (am_mem am) + 16 + 16 * sz * am_last am + 16 * sz <= rg_len rgG).
  { clear - Hext Hstr. unfold group_extent, UNIT, IB in Hext. rewrite Hstr in Hext. lia. }
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
  - rewrite EB. pose proof (used_group_aligned [] None U0 s HW 64%nat g am Hux ltac:(clear - Hsc; lia)) as Al16.
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
  - unfold meta_bits. rewrite Hml. clear - Mlast Hsc. lia.
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
  - pose proof (Htab (am_sc am) Hsc) as Ht. fold sz in Ht.
    assert (Esc : Z.shiftr (meta_bits am) 6 = am_sc am).
    { unfold meta_bits. rewrite Hml. clear - Mlast Hsc. rewrite Z.shiftr_div_pow2 by lia. change (2^6) with 64.
      replace (am_last am + 32 + 64 * am_sc am + 4096 * 0) with ((am_last am + 32) + am_sc am * 64) by ring.
      rewrite Z.div_add by lia. rewrite Z.div_small by lia. ring. }
    rewrite Esc. replace (2 * am_sc am + 98984) with (98984 + 2 * am_sc am) by ring. exact Ht.
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
    { unfold meta_bits. rewrite Hml. replace (am_last am + 32 + 64 * am_sc am + 4096 * 0) with (am_last am + 32 * (1 + 2 * am_sc am)) by ring.
      apply land31; clear - Mlast Hsc; lia. }
    rewrite Hland, EW. exact (proj2 Hi).
  - unfold allocated in Hal. apply negb_true_iff in Hal. rewrite Z.lor_spec in Hal. apply orb_false_iff in Hal.
    rewrite Hland. exact (proj1 Hal).
  - unfold allocated in Hal. apply negb_true_iff in Hal. rewrite Z.lor_spec in Hal. apply orb_false_iff in Hal.
    rewrite Hland. exact (proj2 Hal).
  - rewrite Hland, Eoff. clear - Hfoff Ho16. lia.
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
  - assert (frame_rsv am fr <= 16 * sz) by (unfold frame_rsv; rewrite Hstr; clear - Fn Ho16; unfold UNIT, IB in *; lia). clear - Hrc H Rsz. lia.
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
