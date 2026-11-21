(* reloc-zl14c 40f5cd9c482adb971fb174d8eceb4953 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Bytes InitMem.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed AsanProgDeps.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AsanW Require Import AImg RtCells AProto ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel Require Import Inftrees.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AArr ItAPure InfPure_itab.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.U3A Require Import U2AObj U2AIface U2AGlue InfABase InfAGlueE ItA_base U2AIface_fit2_draft.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import DrvAgree RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [U14] inflate_table's writes at the 1.4 inflate_state offsets (lenbits / distbits 136, next 160,
   lens .. work 808 .. 7160; 1.3.1: 120, 144, 792 .. 7144) *)
Definition IT_WR (S : Z) : list (Z * Z) := [(S + 136, S + 144); (S + 160, S + 168); (S + 808, S + 7160)].

Section CANSEC1. Context {rc : runConstT}.
Section T.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Notation FB0 F := (mkABlock (ABFake 0) F 64).

  (* [comment removed for export] *)
  Lemma u2_img_aheap : forall L RNG st LB m, AHEAP AI L RNG st LB m -> u2_img m.
  Proof.
    intros L RNG st LB m AH. pose proof (AI_relro AI L RNG st LB m AH) as R. unfold u2_img, AGOT_SUAR, AGOT_ZCALLOC, ASUAR, A_ZCALLOC, A_ZCFREE.
    split.
    - eapply rw_cells_recast; [apply (rw_cells_image0 asegs m 0xd01d0 (le8 (Z_to_bv 64 887168)));
        [ intros a Ha; rewrite <- (Z_to_bv_bv_unsigned a); apply R; rewrite length_le8 in Ha; unfold ARELRO_LO, ARELRO_HI; lia
        | vm_compute; reflexivity | lia | rewrite length_le8; lia ]
        | cbn; split; exact I | reflexivity | reflexivity].
    - (* [U14] an earlier development run 2026-11-11: u2_img's second conjunct is True at 1.4 (rt-model-equiv c25: the 1.4 image holds no
         zcalloc / zcfree GOT words; inflateInit2_ loads them pc-relative) *)
      exact I.
  Qed.

  (* [comment removed for export] *)
  Lemma it_tabsh_of_runs : forall m,
    shadow_bytes m 2147469532 2147469539 (fun _ => 0) -> shadow_bytes m 2147469539 2147469540 (fun _ => 6) ->
    shadow_bytes m 2147469544 2147469551 (fun _ => 0) -> shadow_bytes m 2147469551 2147469552 (fun _ => 6) ->
    shadow_bytes m 2147469556 2147469564 (fun _ => 0) -> shadow_bytes m 2147469568 2147469576 (fun _ => 0) -> it_tabsh m.
  Proof.
    intros m A1 A2 B1 B2 C D. unfold it_tabsh, tabsh_f.
    split; [| split; [| split; [exact C| exact D]]].
    - apply (shadow_bytes_app m 2147469532 2147469539); eapply shadow_bytes_ext; [exact A1| | exact A2| ]; intros s Hs; cbv beta;
        destruct (Z.eqb_spec s (2147469532 + 7)); first [reflexivity | lia].
    - apply (shadow_bytes_app m 2147469544 2147469551); eapply shadow_bytes_ext; [exact B1| | exact B2| ]; intros s Hs; cbv beta;
        destruct (Z.eqb_spec s (2147469544 + 7)); first [reflexivity | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma it_rebuild : forall (L : alayout) (RNG : footprint) (stA : astate) (LB LBc : list ablock) (m0 : amem) (payload : list Z)
      (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo fw : Z -> Z)
      (v0 v8 v16 v240 v504 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (saved fk fksh : list cell) (m m' : amem) (isd : bool) (b' nx' : Z) (cf' wf' : Z -> Z),
    inf_ctx cx ly AI RNG LB ->
    inf_vis cx ly st lf cf wf fo payload v0 v8 v16 v240 v504 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3
            havedict dmax check total shold sbits back was pad m ->
    inf_hid cx ly AI L RNG stA LB LBc m0 fw saved fk fksh m ->
    Z.of_nat (length payload) = c_n cx ->
    (* [comment removed for export] *)
    mem_inv asegs m' -> stk asegs m' (l_lo ly) (l_SPA ly) ->
    AHEAP AI L RNG stA LB m' ->
    client_agree AI LB (l_SPA ly) (IT_WR (c_p cx)) m m' ->
    rw_cells asegs m' (c_p cx) (istate_cells (Z_to_bv 64 (l_Zs ly)) (Z_to_bv 64 (t_mode st)) (Z_to_bv 64 (t_last st)) (Z_to_bv 64 5) havedict
                                       (Z_to_bv 64 (t_flags st)) dmax check total (Z_to_bv 64 0) (Z_to_bv 64 15) (Z_to_bv 64 (wsz cx))
                                       (Z_to_bv 64 (t_whave st)) (Z_to_bv 64 (t_wnext st)) (Z_to_bv 64 (c_w cx)) shold sbits
                                       (Z_to_bv 64 (t_length st)) (Z_to_bv 64 (t_offset st)) (Z_to_bv 64 (t_extra st))
                                       (Z_to_bv 64 (cp_addrA (c_p cx) (t_lc st))) (Z_to_bv 64 (cp_addrA (c_p cx) (t_dc st)))
                                       (if isd then Z_to_bv 64 (t_lb st) else Z_to_bv 64 b') (if isd then Z_to_bv 64 b' else Z_to_bv 64 (t_db st))
                                       (Z_to_bv 64 (t_ncode st)) (Z_to_bv 64 (t_nlen st))
                                       (Z_to_bv 64 (t_ndist st)) (Z_to_bv 64 (t_shave st)) (Z_to_bv 64 (c_p cx + 1384 + 4 * nx'))) ->
    f16arr asegs m' (c_p cx + 168) 320 lf -> f16arr asegs m' (c_p cx + 808) 288 wf' -> f32arr asegs m' (c_p cx + 1384) 1444 cf' ->
    inf_vis cx ly (st_itab st isd b' nx') lf cf' wf' fo payload v0 v8 v16 v240 v504 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3
            havedict dmax check total shold sbits back was pad m'
    /\ inf_hid cx ly AI L RNG stA LB LBc m0 fw saved fk fksh m'.
  Proof.
    intros until wf'. intros CTX VIS HID PLEN MI' STK' AH' CAGU SSC' LENS' WORK' CODES'.
    destruct ly as [SP SPA Zs F0 lo].
    destruct CTX as (S16 & SB & (ps & HPS & PAYH) & (Fu & SHOME) & RZ & RSZ & HF0 & F064 & F0B & RS & RSS & OBE & OSZ & OCI & ROB & ROBS & WDC
                     & D1 & NR & D16 & RD & RSD & LOC & LOS & SPAR & SPA32 & SP16 & SPT & RSTK & RI & RISH & RSFU & TABC1 & TABC2 & LBABLK).
    cbn [l_SP l_SPA l_Zs l_F0 l_lo] in *.
    destruct VIS as (FRM & STRM & SSC & LENS & WORK & CODES & TAIL & OUT & PAYB & STK & MI & MNE). cbn [l_SP l_SPA l_Zs l_F0 l_lo] in *.
    destruct HID as (AH & SHZ & SHS & SHO & WIN & UNP & SAVED & SZ1 & FK & SZ2 & FKSH & SZ3 & SUBL & CAG & SHLF & SHDF & SHOR & SHO6
                     & IT1 & IT2 & IT3 & IT4 & IT5 & IT6 & GAP & (obr & OBR) & WFU).
    cbn [l_SP l_SPA l_Zs l_F0 l_lo] in *.
    destruct SHOME as (HFU & ZSE & FU256 & FUB).
    atop_facts. unfold KEND in SPT. unfold A_OUTBUF in OBE.
    pose proof (AI_block AI _ _ _ _ _ ps (c_p cx) 7176 AH' HPS) as (_ & _ & _ & _ & BSHS & _).
    pose proof (ablk_lin _ _ SB) as (SB1 & SB2 & SB3 & SB4). unfold AIMG_HI in SB1.
    pose proof (ablk_lin _ _ FUB) as (FUB1 & FUB2 & FUB3 & FUB4). unfold AIMG_HI in FUB1.
    pose proof (ablk_lin _ _ F0B) as (F0B1 & F0B2 & F0B3 & F0B4). unfold AIMG_HI in F0B1.
    (* [comment removed for export] *)
    assert (DISS : forall b, In b LB -> b <> HB ps (c_p cx) 7176 -> ab_addr b + ab_size b <= c_p cx \/ c_p cx + 7176 <= ab_addr b).
    { intros b Hb NE. pose proof (AI_blocks_disjoint AI _ _ _ _ _ b (HB ps (c_p cx) 7176) AH Hb HPS NE) as X. cbn [ab_addr ab_size] in X. lia. }
    pose proof (DISS _ HFU ltac:(discriminate)) as DSU. pose proof (DISS _ HF0 ltac:(discriminate)) as DSF. cbn [ab_addr ab_size] in DSU, DSF.
    assert (DSD : c_q cx + c_n cx <= c_p cx \/ c_p cx + 7176 <= c_q cx).
    { destruct PAYH as [(pd & HPD & NP & PNE)|(N0 & DE)]; [| lia].
      pose proof (DISS _ HPD ltac:(intros E; inversion E; contradiction)) as X. cbn [ab_addr ab_size] in X. exact X. }
    assert (DSW : c_w cx = 0 \/ (c_w cx + 32768 <= c_p cx \/ c_p cx + 7176 <= c_w cx)).
    { destruct WDC as [W0|(W16 & WB & (pw & HPW) & _)]; [left; exact W0| right].
      destruct (N.eq_dec pw ps) as [E|NE].
      - subst pw. pose proof (hb_same_id _ ps (c_p cx) 7176 (c_w cx) 32768 (AI_hb_ids AI _ _ _ _ _ AH) HPS HPW) as Q. inversion Q.
      - pose proof (DISS _ HPW ltac:(intros Q; inversion Q; contradiction)) as X. cbn [ab_addr ab_size] in X. exact X. }
    pose proof (ablk_disj_band _ _ SB) as BS. unfold KLS in BS.
    destruct OCI as (ivO & OCI1 & OCI2 & OCI3). destruct TABC1 as (ivT1 & T11 & T12 & T13). destruct TABC2 as (ivT2 & T21 & T22 & T23).
    (* [comment removed for export] *)
    set (PU := fun a : Z => aclient_addr CI LB SPA a /\ ~ in_ranges (IT_WR (c_p cx)) a).
    assert (NWR : forall a, (a < c_p cx + 136 \/ c_p cx + 7160 <= a) -> ~ in_ranges (IT_WR (c_p cx)) a).
    { intros a H1 (iv & [E|[E|[E|[]]]] & Hr); subst iv; cbn [fst snd] in Hr; lia. }
    assert (PK : forall a, SPA <= a < SP -> PU a).
    { intros a Ha. split; [left; clear - Ha SPT; lia| apply NWR; clear - Ha SB3 H LOC LOS; lia]. }
    assert (PZ : forall a, Fu <= a < Fu + 256 -> PU a).
    { intros a Ha. split; [right; right; left; exists (mkABlock (ABFake 2) Fu 256); split; [exact HFU| cbn [ab_addr ab_size]; exact Ha]|].
      apply NWR; clear - Ha DSU; lia. }
    assert (PS : forall a, c_p cx + 7160 <= a < c_p cx + 7176 -> PU a).
    { intros a Ha. split; [right; right; left; exists (HB ps (c_p cx) 7176); split; [exact HPS| cbn [ab_addr ab_size]; clear - Ha; lia]|].
      apply NWR; clear - Ha; lia. }
    assert (PO : forall a, c_ob cx <= a < c_ob cx + 262144 -> PU a).
    { intros a Ha. split; [right; left; exists ivO; split; [exact OCI1| clear - Ha OCI2 OCI3; lia]|].
      apply NWR; clear - Ha OBE SB1; lia. }
    assert (PF : forall a, F0 <= a < F0 + 64 -> PU a).
    { intros a Ha. split; [right; right; left; exists (FB0 F0); split; [exact HF0| cbn [ab_addr ab_size]; exact Ha]|].
      apply NWR; clear - Ha DSF; lia. }
    assert (PSHX : forall a' a, 0 <= a' < 2 ^ 47 -> a = shad a' ->
                   ((ATOP <= a' < 2 ^ 47) \/ in_ranges CI a' \/ in_fake LB a') -> PU a).
    { intros a' a R47 -> HC. split; [right; right; right; exists a'; split; [exact HC| reflexivity]|].
      pose proof (shad_in_band a' R47) as SBD. unfold KLS in SBD. apply NWR; clear - SBD BS; lia. }
    assert (PSHF : forall c F n s1 s2, In (mkABlock (ABFake c) F n) LB -> F <= 8 * (s1 - 2147450880) -> 8 * (s2 - 2147450880) <= F + n ->
                   forall a, s1 <= a < s2 -> PU a).
    { intros c F n s1 s2 Hb H1 H2 a Ha.
      pose proof (AI_block_bounds AI _ _ _ _ _ _ AH Hb) as (B1 & B2 & B3). cbn [ab_addr ab_size] in B1, B2, B3. unfold AIMG_HI in B1.
      apply (PSHX (8 * (a - ASHOFF)) a); [unfold ASHOFF; clear - Ha H1 H2 B1 B3 H; lia| symmetry; apply shad_unshad|].
      right. right. exists c, F, n. split; [exact Hb| unfold ASHOFF; clear - Ha H1 H2; lia]. }
    assert (PSHC : forall iv s1 s2, In iv CI -> fst iv <= 8 * (s1 - 2147450880) -> 8 * (s2 - 2147450880) <= snd iv ->
                   forall a, s1 <= a < s2 -> PU a).
    { intros iv s1 s2 Hiv H1 H2 a Ha. pose proof (AI_aci_img AI iv Hiv) as I1. pose proof (AI_aci_lo AI iv Hiv) as I2. unfold AIMG_HI in I1.
      apply (PSHX (8 * (a - ASHOFF)) a); [unfold ASHOFF; clear - Ha H1 H2 I1 I2; lia| symmetry; apply shad_unshad|].
      right. left. exists iv. split; [exact Hiv| unfold ASHOFF; clear - Ha H1 H2; lia]. }
    unfold client_agree in CAGU. fold PU in CAGU.
    clear DSU DSF BS DISS.
    assert (Z8 : Zs mod 8 = 0) by (clear - ZSE FU256; Z.div_mod_to_equations; lia).
    assert (F8 : F0 mod 8 = 0) by (clear - F064; Z.div_mod_to_equations; lia).
    assert (O8 : c_ob cx mod 8 = 0) by (rewrite OBE; reflexivity).
    destruct (shr3_lin8 Zs ltac:(lia) Z8) as (qZ & EQZ & QZ). destruct (shr3_lin8 F0 ltac:(lia) F8) as (qF & EQF & QF).
    destruct (shr3_lin8 (c_ob cx) ltac:(lia) O8) as (qO & EQO & QO).
    (* [comment removed for export] *)
    assert (FRM' := rw_cells_magree asegs PU m m' SPA _ CAGU FRM).
    assert (STRM' := rw_cells_magree asegs PU m m' Zs _ CAGU STRM).
    assert (TAIL' := rw_cells_magree asegs PU m m' (c_p cx + 7160) _ CAGU TAIL).
    assert (SAVED' := rw_cells_magree asegs PU m m' (SP + -104) _ CAGU SAVED).
    assert (FK' := rw_cells_magree asegs PU m m' F0 _ CAGU FK).
    assert (FKSH' := rw_cells_magree asegs PU m m' (Z.shiftr F0 3 + 2147450880) _ CAGU FKSH).
    assert (OBR' := rw_cells_magree asegs PU m m' (c_ob cx + c_osz cx) _ CAGU OBR).
    unfold inf_locals in FRM'. unfold strm_cells in STRM'. unfold itail_cells in TAIL'. rewrite SZ1 in SAVED'. rewrite SZ2 in FK'. rewrite SZ3 in FKSH'.
    cbn [cells_size csize Nat.add] in FRM', STRM', TAIL', OBR'. rewrite Nat.add_0_r, Z2Nat.id in OBR' by (clear - OSZ; lia).
    specialize (FRM' ltac:(intros a Ha; apply PK; clear - Ha SPAR; lia)).
    specialize (STRM' ltac:(intros a Ha; apply PZ; clear - Ha ZSE; lia)).
    specialize (TAIL' ltac:(intros a Ha; apply PS; clear - Ha; lia)).
    specialize (SAVED' ltac:(intros a Ha; apply PK; clear - Ha SPAR; lia)).
    specialize (FK' ltac:(intros a Ha; apply PF; clear - Ha; lia)).
    specialize (FKSH' ltac:(intros a Ha; rewrite EQF in Ha; apply (PSHF 0 F0 64 (qF + 2147450880) (qF + 2147450880 + 8) HF0); [clear - QF; lia| clear - QF; lia| exact Ha])).
    specialize (OBR' ltac:(intros a Ha; apply PO; clear - Ha OSZ; lia)).
    assert (OUT' : f8arr asegs m' (c_ob cx) (Z.to_nat (c_osz cx)) fo).
    { destruct OUT as [HB HW]. split; [eapply bytes_at_magree; [exact CAGU| exact HB|]| eapply wr_at_magree; [exact CAGU| exact HW|]];
        rewrite ?length_map, ?length_seq; intros a Ha; apply PO; clear - Ha OSZ; lia. }
    assert (PAYB' : bytes_at asegs m' (c_q cx) (map (Z_to_bv 8) payload)).
    { destruct PAYH as [(pd & HPD & NP & PNE)|(N0 & DE)].
      - eapply bytes_at_magree; [exact CAGU| exact PAYB|]. rewrite length_map, PLEN. intros a Ha.
        split; [right; right; left; exists (HB pd (c_q cx) (c_n cx)); split; [exact HPD| cbn [ab_addr ab_size]; exact Ha]|].
        apply NWR; clear - Ha DSD; lia.
      - destruct payload as [|c pl]; [| cbn [length] in PLEN; lia]. cbn [map]. split; [lia|]. split; [cbn [length]; lia|]. intros i Hi. cbn [length] in Hi. lia. }
    assert (GAP' : stk asegs m' (SPA + 536) (SP + -104)) by (eapply stk_magree; [exact CAGU| exact GAP|]; intros a Ha; apply PK; clear - Ha SPAR; lia).
    assert (WFU' : wr_at asegs m' (Z.shiftr Zs 3 + 2147450880 - 4) 32).
    { eapply wr_at_magree; [exact CAGU| exact WFU|]. rewrite EQZ. intros a Ha.
      apply (PSHF 2 Fu 256 (qZ + 2147450880 - 4) (qZ + 2147450880 - 4 + 32) HFU); [clear - QZ ZSE; lia| clear - QZ ZSE; lia| exact Ha]. }
    assert (SHZ' : shadow_bytes m' (Z.shiftr Zs 3 + 2147450880) (Z.shiftr Zs 3 + 2147450880 + 14) (fun _ => 0)).
    { eapply shadow_bytes_magree; [exact CAGU| exact SHZ|]. rewrite EQZ. intros a Ha.
      apply (PSHF 2 Fu 256 (qZ + 2147450880) (qZ + 2147450880 + 14) HFU); [clear - QZ ZSE; lia| clear - QZ ZSE; lia| exact Ha]. }
    assert (SHO' : shadow_bytes m' (Z.shiftr (c_ob cx) 3 + 2147450880) (Z.shiftr (c_ob cx) 3 + 2147450880 + 32768) (fun _ => 0)).
    { eapply shadow_bytes_magree; [exact CAGU| exact SHO|]. rewrite EQO. intros a Ha.
      apply (PSHC ivO (qO + 2147450880) (qO + 2147450880 + 32768) OCI1); [clear - QO OCI2; lia| clear - QO OCI3; lia| exact Ha]. }
    assert (TABX : forall q1 q2 f, ((2147468552 <= q1 /\ q2 <= 2147469916) \/ (2147469532 <= q1 /\ q2 <= 2147469576)) ->
                   shadow_bytes m q1 q2 f -> shadow_bytes m' q1 q2 f).
    { intros q1 q2 f HR SB0. eapply shadow_bytes_magree; [exact CAGU| exact SB0|]. intros a Ha.
      destruct HR as [HR|HR]; [apply (PSHC ivT1 q1 q2 T11); [clear - HR T12; lia| clear - HR T13; lia| exact Ha]
                              | apply (PSHC ivT2 q1 q2 T21); [clear - HR T22; lia| clear - HR T23; lia| exact Ha]]. }
    (* [comment removed for export] *)
    assert (SHS' : shadow_bytes m' (Z.shiftr (c_p cx) 3 + 2147450880) (Z.shiftr (c_p cx) 3 + 2147450880 + 897) (fun _ => 0)).
    { change 897 with (7176 / 8). apply ablock_sh0; [exact BSHS| reflexivity| lia| lia| lia]. }
    assert (UNP' : unpoisoned m' (c_q cx) (c_q cx + c_n cx)).
    { destruct PAYH as [(pd & HPD & NP & PNE)|(N0 & DE)].
      - pose proof (AI_block AI _ _ _ _ _ pd (c_q cx) (c_n cx) AH' HPD) as (_ & _ & _ & _ & BSHD & _).
        pose proof (AI_block_bounds AI _ _ _ _ _ _ AH HPD) as (B1 & B2 & B3). cbn [ab_addr ab_size] in B1, B2, B3.
        apply ablock_unpoisoned; [exact BSHD| clear - D16; Z.div_mod_to_equations; lia| clear - D1; lia| clear - NR; lia| clear - B3 H; lia].
      - destruct UNP as (U1 & U2 & _). split; [exact U1|]. split; [exact U2|]. intros G HG. exfalso. clear - HG N0. lia. }
    assert (WIN' : c_w cx <> 0 -> shadow_bytes m' (Z.shiftr (c_w cx) 3 + 2147450880) (Z.shiftr (c_w cx) 3 + 2147450880 + 4096) (fun _ => 0)
                                 /\ f8arr asegs m' (c_w cx) (Z.to_nat 32768) fw).
    { intros WN. destruct (WIN WN) as (_ & [HBy HWr]). destruct WDC as [W0|(W16 & WB & (pw & HPW) & _)]; [contradiction|].
      pose proof (AI_block AI _ _ _ _ _ pw (c_w cx) 32768 AH' HPW) as (_ & _ & _ & _ & BSHW & _).
      pose proof (ablk_lin _ _ WB) as (WB1 & WB2 & WB3 & WB4).
      split; [change 4096 with (32768 / 8); apply ablock_sh0; [exact BSHW| reflexivity| lia| lia| lia]|].
      split; [eapply bytes_at_magree; [exact CAGU| exact HBy|]| eapply wr_at_magree; [exact CAGU| exact HWr|]];
        rewrite ?length_map, ?length_seq; intros a Ha;
        (split; [right; right; left; exists (HB pw (c_w cx) 32768); split; [exact HPW| cbn [ab_addr ab_size]; clear - Ha; lia]|
                 apply NWR; clear - Ha DSW WN; lia]). }
    split.
    { (* [comment removed for export] *)
      unfold inf_vis, st_itab. cbn [l_SP l_SPA l_Zs l_F0 l_lo
        t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext].
      split; [exact FRM'|]. split; [exact STRM'|]. split; [destruct isd; exact SSC'|]. split; [exact LENS'|]. split; [exact WORK'|]. split; [exact CODES'|].
      split; [exact TAIL'|]. split; [exact OUT'|]. split; [exact PAYB'|]. split; [exact STK'|]. split; [exact MI'| exact MNE]. }
    (* [comment removed for export] *)
    unfold inf_hid. cbn [l_SP l_SPA l_Zs l_F0 l_lo].
    split; [exact AH'|]. split; [exact SHZ'|]. split; [exact SHS'|]. split; [exact SHO'|].
    split; [exact WIN'|].
    split; [exact UNP'|]. split; [exact SAVED'|]. split; [exact SZ1|]. split; [exact FK'|]. split; [exact SZ2|]. split; [exact FKSH'|]. split; [exact SZ3|].
    split; [exact SUBL|].
    split.
    { (* [comment removed for export] *)
      unfold client_agree in CAG |- *. unfold inf_WR in CAG |- *. cbn [l_SP l_SPA l_Zs l_F0 l_lo] in CAG |- *.
      eapply magree_trans; [exact CAG|].
      eapply magree_mono; [exact CAGU|]. intros a (HC & HN). unfold PU. split.
      - destruct HC as [X|[X|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
        + left. clear - X SPAR. lia.
        + right; left; exact X.
        + right; right; left. exists b. split; [apply SUBL; exact Hb| exact Hr].
        + right; right; right. exists a'. split; [| reflexivity].
          destruct Ha' as [X|[X|(c & A & k & Hb & Hr)]]; [left; exact X| right; left; exact X| right; right]. exists c, A, k. split; [apply SUBL; exact Hb| exact Hr].
      - intros (iv & [<-|[<-|[<-|[]]]] & Hr); apply HN; cbn [fst snd] in Hr;
          (exists (c_p cx, c_p cx + 7176); split; [right; left; reflexivity| cbn [fst snd]; clear - Hr; lia]). }
    split; [apply TABX; [left; lia| exact SHLF]|]. split; [apply TABX; [left; lia| exact SHDF]|].
    split; [apply TABX; [left; lia| exact SHOR]|]. split; [apply TABX; [left; lia| exact SHO6]|].
    split; [apply TABX; [right; lia| exact IT1]|]. split; [apply TABX; [right; lia| exact IT2]|].
    split; [apply TABX; [right; lia| exact IT3]|]. split; [apply TABX; [right; lia| exact IT4]|].
    split; [apply TABX; [right; lia| exact IT5]|]. split; [apply TABX; [right; lia| exact IT6]|].
    split; [exact GAP'|]. split; [exists obr; exact OBR'| exact WFU'].
  Qed.
  (* [comment removed for export] *)
  Variable rng_fs : alayout -> footprint -> Prop.
  Definition itcall_env (L : alayout) (RNG : footprint) (LB : list ablock) (tp : word) (ly : ilay) : Prop :=
    inflate_table_stmtA AI rng_fs /\ rng_fs L RNG /\ atmost1_c2 LB /\ tp = Z_to_bv 64 ATP
    /\ l_SP ly + 16 < al_top L /\ rng RNG (l_lo ly) (al_top L - l_lo ly).

  (* [comment removed for export] *)
  Lemma inf_itcall : forall (L : alayout) (RNG : footprint) (stA : astate) (LB LBc : list ablock) (m0 : amem) (payload : list Z)
      (POST : machine_state -> Prop) (cx : ictx) (ly : ilay) (st : ist) (lf cf wf fo fw : Z -> Z)
      (v0 v8 v16 v240 v504 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total shold sbits back was pad : word)
      (saved fk fksh : list cell) (m : amem) (isd : bool) (ty : codetype) (lens_ofs codes bits RA : Z) (r : Z * arr * Z * Z * arr)
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (FR : bvmap 5 word) (fc : bv 32),
    itcall_env L RNG LB tp ly ->
    inf_ctx cx ly AI RNG LB ->
    inf_vis cx ly st lf cf wf fo payload v0 v8 v16 v240 v504 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3
            havedict dmax check total shold sbits back was pad m ->
    inf_hid cx ly AI L RNG stA LB LBc m0 fw saved fk fksh m ->
    Z.of_nat (length payload) = c_n cx ->
    bits = (if isd then t_db st else t_lb st) ->
    itc ty lf lens_ofs codes (t_nx st) bits cf wf ->
    r = resA ty lf lens_ofs codes (t_nx st) bits cf wf ->
    ra = Z_to_bv 64 RA -> 0 <= RA < 2 ^ 64 -> RA mod 2 = 0 -> sp = Z_to_bv 64 (l_SPA ly) ->
    a0 = Z_to_bv 64 (cty ty) -> a1 = Z_to_bv 64 (c_p cx + 168 + 2 * lens_ofs) -> a2 = Z_to_bv 64 codes ->
    a3 = Z_to_bv 64 (c_p cx + 160) -> a4 = Z_to_bv 64 (if isd then c_p cx + 140 else c_p cx + 136) -> a5 = Z_to_bv 64 (c_p cx + 808) ->
    (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : amem),
       inf_vis cx ly (st_itab st isd (it_bits r) (it_table r)) lf (arr_get (it_tbl r)) (arr_get (it_work r)) fo payload
               v0 v8 v16 v240 v504 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3
               havedict dmax check total shold sbits back was pad m' ->
       inf_hid cx ly AI L RNG stA LB LBc m0 fw saved fk fksh m' ->
       (it_ret r = 0 \/ it_ret r = 1 \/ it_ret r = -1) ->
       evtF asegs RNG POST
         (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (it_ret r)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             FR (Z_to_bv 64 RA) fc None m' (seg_rom asegs))) ->
    evtF asegs RNG POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 A_ITABLE) fc None m (seg_rom asegs)).
  Proof.
    intros until fc. intros (ITAB & RFS & AM1 & ETP & SPT' & RSTK') CTX VIS HID PLEN EB ITC ER ERA RA1 RA2 ESP E0 E1 E2 E3 E4 E5 K.
    pose proof CTX as CTX0. pose proof VIS as VIS0. pose proof HID as HID0.
    destruct CTX0 as (S16 & SB & (ps & HPS & PAYH) & _ & RZ & RSZ & HF0 & F064 & F0B & RS & RSS & OBE & OSZ & OCI & ROB & ROBS & WDC
                     & D1 & NR & D16 & RD & RSD & LOC & LOS & SPAR & SPA32 & SP16 & SPT & RSTK & RI & RISH & RSFU & TABC1 & TABC2 & LBABLK).
    destruct VIS0 as (FRM & STRM & SSC & LENS & WORK & CODES & TAIL & OUT & PAYB & STK & MI & MNE).
    destruct HID0 as (AH & SHZ & SHS & SHO & WIN & UNP & SAVED & SZ1 & FK & SZ2 & FKSH & SZ3 & SUBL & CAG & SHLF & SHDF & SHOR & SHO6
                     & IT1 & IT2 & IT3 & IT4 & IT5 & IT6 & GAP & OBR & WFU).
    atop_facts. unfold KEND in SPT.
    assert (USP : bv_unsigned sp = l_SPA ly) by (rewrite ESP; apply unsigned_lit; clear - SPAR SPT LOC LOS H; lia).
    eapply evtF_cut.
    { unfold inflate_table_stmtA in ITAB.
      eapply (ITAB L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m stA LB ps (c_p cx) (l_lo ly)
                   ty lf cf wf lens_ofs codes (t_nx st) bits isd);
        [ exact AH | exact AM1 | exact LBABLK | exact HPS | exact TABC2 | exact (it_tabsh_of_runs m IT1 IT2 IT3 IT4 IT5 IT6)
        | exact (u2_img_aheap L RNG stA LB m AH) | exact SSC | rewrite EB; destruct isd; reflexivity | exact LENS | exact WORK | exact CODES | exact ITC
        | exact E0 | exact E1 | exact E2 | exact E3 | exact E4 | exact E5
        | rewrite USP; exact STK | clear - LOC; lia | rewrite USP; unfold ITABLE_STACK; clear - LOS; lia | rewrite USP; clear - SPA32; Z.div_mod_to_equations; lia
        | rewrite USP; clear - SPT' SPAR; lia | exact MI | exact ETP | exact RSTK' | exact RI | exact RISH | exact RFS ]. }
    cbv beta. unfold itable_post. cbv zeta. rewrite <- ER.
    intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MI' & STK' & AH' & CAG' & SSC' & LENS' & WORK' & CODES' & RET).
    rewrite USP in STK', CAG'.
    destruct (it_rebuild L RNG stA LB LBc m0 payload cx ly st lf cf wf fo fw v0 v8 v16 v240 v504 vnext j512 j520 zni zai zti zno zao zto zmsg zopq zdt zadl zres zp1 zp2 zp3
                havedict dmax check total shold sbits back was pad saved fk fksh m m' isd (it_bits r) (it_table r) (arr_get (it_tbl r)) (arr_get (it_work r))
                CTX VIS HID PLEN MI' STK' AH' CAG') as (VIS' & HID'); [ | exact LENS' | exact WORK' | exact CODES' | ].
    { destruct isd; exact SSC'. }
    replace (ret_pc ra) with (Z_to_bv 64 RA) by (rewrite ERA; symmetry; apply ret_pc_even; assumption).
    exact (K t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' VIS' HID' RET).
  Qed.
End T.
End CANSEC1.
