(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import DrvAgree FseWalkKit ZdFrameW ZdWalkKit ZdDctxRep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF KXAsan KXAutoA.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells AProto ABase AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_fkit
     AZ_frame_iface AZ_block_iface AZ_dframe_iface AZ_dctx_iface AZ_libc_iface AZ_libc AZ_kx AZ_globals AZ_globalsR AF_fse_rd_base AF_fse_rd_mem AF_fse_rd_seg AF_fse_rd_asm
     AZ_findfsi_a AZ_findfsi_b.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Import FseWalkKit ZdWalkKit.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac rd_retlit := lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.

Notation zlen l := (Z.of_nat (length l)).
Notation SHB := 2147450880.

Section CANSEC1. Context {rc : runConstT}.

Lemma dd_got_cell : forall m, (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None) -> rw_cells bsegs m 0xc7308 [C8 (Z_to_bv 64 0xcfcf8)].
Proof. intros m R. apply relro_wordA; [exact R| unfold ARELRO_LO; lia| unfold ARELRO_HI; lia| vm_compute; reflexivity]. Qed.
Lemma zero16_c8sA : forall (m : amem) s, rw_cells bsegs m s [CB 16 (repeat (Z_to_bv 8 0) 16)] -> rw_cells bsegs m s [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
Proof. intros m s H. eapply rw_cells_recast; [exact H| cbn; repeat split; exact I| vm_compute; reflexivity| reflexivity]. Qed.

(* [comment removed for export] *)
Lemma h5_split44 : forall ws : list word, length ws = 44%nat ->
  exists w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43,
  ws = [w0; w1; w2; w3; w4; w5; w6; w7; w8; w9; w10; w11; w12; w13; w14; w15; w16; w17; w18; w19; w20; w21; w22; w23; w24; w25; w26; w27; w28; w29; w30; w31; w32; w33; w34; w35; w36; w37; w38; w39; w40; w41; w42; w43].
Proof.
  intros ws L. do 44 (destruct ws as [|? ws]; [discriminate L|]). destruct ws; [| discriminate L]. do 44 eexists. reflexivity.
Qed.

Lemma dd_ahull_wmono : forall RNG m m' X n, ahull RNG m X n -> wmono bsegs m m' -> ahull RNG m' X n.
Proof.
  intros RNG m m' X n (RLO & RHI & H1 & H2 & H3 & H4 & H5 & H6 & W & R) WM. exists RLO, RHI.
  repeat (split; [assumption|]). split; [eapply wr_at_transport; [exact W| exact WM]| exact R].
Qed.
Lemma dd_ahull_sub : forall RNG m X n X' n', ahull RNG m X n -> X <= X' -> X' + n' <= X + n -> ahull RNG m X' n'.
Proof.
  intros RNG m X n X' n' (RLO & RHI & H1 & H2 & H3 & H4 & H5 & H6 & W & R) A B. exists RLO, RHI.
  split; [lia|]. split; [lia|]. repeat (split; [assumption|]). exact R.
Qed.

Section Thm.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variable rng_fs : alayout -> footprint -> Prop.
  Hypothesis DMF : zd_dmf_stmtA AI rng_fs.

  Theorem zd_ddctx_proofA : zd_ddctx_stmtA AI rng_fs.
  Proof.
    intros L RNG st LB ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m SPV lo DCTX DST CAP SRC src size
           DA RD0 RD1 RD8 GOT SB OK N0 NLEN N40 RS0 RS1 DSK RC0 RC40 DNULL DNN DZ RDST ST RLO LO RSP S_DC S_DS S_SR S_GT D_DC D_SR SR_DC GT_DC GT_DS
           AFP TP AZS ARO ARS AIS AHS D8 ARD AHD AID ADST MI -> -> -> -> ->.
    pose proof AFP as (AH & ASH & ART & (KHI & RSTK & RI) & RFS & BOT & SPT & SP16 & RSTKT & LBH).
    pose proof atop_range as ATR.
    pose proof (AI_rtcells AI _ _ _ _ _ AH) as RTC. unfold artcells in RTC. destruct RTC as (_ & _ & _ & _ & SHBc & _).
    pose proof (dd_got_cell m (AI_relro AI _ _ _ _ _ AH)) as G2.
    pose proof (ARD ltac:(lia)) as (DBK & UD0 & RDc1 & RDc2). pose proof (fk_ablk_lits _ _ DBK) as DL. pose proof (ablk_disj_band _ _ DBK) as DBD.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    destruct DA as (llt & mlt & oft & huf & pde & pfx & vst & dend & expd & fp & pcs & dsz & bt & stg & le & fe & xs & ws & jhb & ovd & dcb & dce & trace &
                    PT & H1 & [FPC FPSZ] & H3 & [XSC XSSZ] & [H5C H5L] & H5OK & TX & [OWE OWX]).
    pose proof H5OK as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K_DL & K_DD & K_DU & K9 & K10).
    destruct (h5_split44 ws H5L) as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w18 & w19 & w20 & w21
                                     & w22 & w23 & w24 & w25 & w26 & w27 & w28 & w29 & w30 & w31 & w32 & w33 & w34 & w35 & w36 & w37 & w38 & w39 & w40 & w41 & w42 & w43 & EWS).
    pose proof H5C as H5Co. rewrite EWS in H5C, K_DL, K_DD, K_DU.
    cbv beta iota delta [h5_cells h5_sizes mk_wcells wnth nth H5_ddictLocal H5_ddict H5_dictUses] in H5C, K_DL, K_DD, K_DU.
    unfold wz0 in K_DL, K_DD, K_DU. subst w14 w15 w18.
    (* [comment removed for export] *)
    pose proof (proj1 (rw_cells_app bsegs _ _ [C8 w0; C4 w1; C4 w2; C4 w3; C4 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C4 w12; C4 w13] _) H5C) as [H5A H5B].
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul] in H5B.
    match type of H5B with rw_cells _ _ ?a _ => replace a with (DCTX + 30184) in H5B by (clear; lia) end.
    pose proof (proj1 (rw_cells_app bsegs _ _ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] _) H5B) as [H5D H5T].
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in H5T.
    match type of H5T with rw_cells _ _ ?a _ => replace a with (DCTX + 30200) in H5T by (clear; lia) end.
    clear H5C H5B.
    pose proof (munch_refl [(SPV - 2288, SPV); (DCTX + 30184, DCTX + 30212)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    pose proof (bytes_at_bound _ _ _ _ SB) as DB. rewrite length_map in DB.
    (* [comment removed for export] *)
    assert (DSH : forall m', munch [(SPV - 2288, SPV); (DCTX + 30184, DCTX + 30212)] m m' -> unpoisoned m' DCTX (DCTX + 95992)).
    { intros m' MU'. eapply unpoisoned_munch; [exact UD0| exact MU'|]. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF, KLS, KHIGH in *.
      clear - DL DBD RSP LO KHI ATR. repeat split; Z.div_mod_to_equations; lia. }
    assert (DJ4 : forall X k, (X + k <= SPV - 2288 \/ SPV <= X) -> (X + k <= DCTX + 30184 \/ DCTX + 30212 <= X) -> 0 <= k -> disjoint_from [(SPV - 2288, SPV); (DCTX + 30184, DCTX + 30212)] X k)
      by (intros X k A B C; cbn [disjoint_from]; clear - A B C; repeat split; lia).
    fk_hold FPC. fk_hold XSC. fk_hold PT. fk_hold H1. fk_hold H3. fk_hold TX. fk_hold OWE. fk_hold OWX. fk_hold H5Co. fk_hold EWS. fk_hold K1. fk_hold H5OK.
    fk_hold AFP. fk_hold AH. fk_hold ASH. fk_hold ART. fk_hold LBH. fk_hold AZS. fk_hold ARO. fk_hold ARS. fk_hold AIS. fk_hold AHS. fk_hold ARD. fk_hold AHD. fk_hold AID. fk_hold ADST.
    fk_hold SB. fk_hold DSK. fk_hold S_DS. fk_hold S_SR. fk_hold S_GT. fk_hold D_DC. fk_hold D_SR. fk_hold SR_DC. fk_hold GT_DC. fk_hold GT_DS. fk_hold DNULL. fk_hold DNN. fk_hold GOT.
    fk_hold DL. fk_hold DBD. fk_hold UD0. fk_hold RSTKT. fk_hold RFS. fk_hold DSH. fk_hold DJ4. fk_hold DB. fk_hold H5A.
    unfold APZD_DDCTX.
    zstep.                                        (* [comment removed for export] *)
    carve_frame 80%nat ST.
    do 9 zstep.                                   (* [comment removed for export] *)
    zstep. zstep.                                 (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    try (let w := getreg 8 in replace w with (Z_to_bv 64 (DCTX + 30208)) by (f_equal; clear; lia)).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    unfold fk_held in DSH. pose proof (DSH m1 MU) as UD1. fk_hold DSH.
    pose proof (unp_sh_rd0 m1 DCTX 95992 (DCTX + 30208) UD1 ltac:(clear; lia) ltac:(clear - RD8; Z.div_mod_to_equations; lia) ltac:(clear - RD0; lia) ltac:(clear - RD1; lia)) as RDz.
    assert (RTz : rng RNG ((DCTX + 30208) ≫ 3 + SHB) 1)
      by (eapply rng_sub'; [exact RDc2|]; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8; unfold shspan; rewrite shad_div; unfold ASHOFF; clear - RD8; Z.div_mod_to_equations; lia).
    zstep. zstep. zstep.                          (* [comment removed for export] *)
    clear RDz RTz. try replace (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) by reflexivity.
    zstep. if_false.                              (* [comment removed for export] *)
    zstep. rewrite (sx32w_small 0) by (clear; lia).   (* [comment removed for export] *)
    zstep. zstep. zstep.                          (* [comment removed for export] *)
    try (let w := getreg 9 in replace w with (Z_to_bv 64 (DCTX + 30184)) by (f_equal; clear; lia)).
    zstep. try (if_cases Km; zify_cond Km; [exfalso; clear - Km; lia|]).   (* [comment removed for export] *)
    zstep. zstep. try (if_cases K1'; zify_cond K1'; [| exfalso; clear - K1'; lia]).   (* [comment removed for export] *)
    (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    pose proof (unp_sh_rd0 m1 DCTX 95992 (DCTX + 30184) UD1 ltac:(clear; lia) ltac:(clear - RD8; Z.div_mod_to_equations; lia) ltac:(clear - RD0; lia) ltac:(clear - RD1; lia)) as RDz.
    assert (RTz : rng RNG ((DCTX + 30184) ≫ 3 + SHB) 1)
      by (eapply rng_sub'; [exact RDc2|]; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8; unfold shspan; rewrite shad_div; unfold ASHOFF; clear - RD8; Z.div_mod_to_equations; lia).
    zstep. zstep. zstep.                          (* [comment removed for export] *)
    clear RDz RTz. try (let w := getreg 10 in replace w with (Z_to_bv 64 0) by reflexivity).
    zstep. if_false.                              (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.                   (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    carve_frame 32%nat ST.
    do 4 zstep.                                   (* [comment removed for export] *)
    zstep. try (if_cases Kz; zify_cond Kz; [| exfalso; clear - Kz; lia]).   (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    do 4 zstep.                                   (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    lazymatch goal with H : rw_cells bsegs _ (SPV + -112) _ |- _ => release_frame H ST (SPV + -80) end.
    zstep. try rd_retlit.                         (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    unfold fk_held in DSH. pose proof (DSH m2 MU) as UD2. fk_hold DSH.
    pose proof (unp_sh_rd0 m2 DCTX 95992 (DCTX + 30208) UD2 ltac:(clear; lia) ltac:(clear - RD8; Z.div_mod_to_equations; lia) ltac:(clear - RD0; lia) ltac:(clear - RD1; lia)) as RDz.
    assert (RTz : rng RNG ((DCTX + 30208) ≫ 3 + SHB) 1)
      by (eapply rng_sub'; [exact RDc2|]; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8; unfold shspan; rewrite shad_div; unfold ASHOFF; clear - RD8; Z.div_mod_to_equations; lia).
    zstep.                                        (* [comment removed for export] *)
    clear RDz RTz. try replace (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) by reflexivity.
    zstep. if_false.                              (* [comment removed for export] *)
    clear UD1 UD2.
    zstep.                                        (* [comment removed for export] *)
    (* [comment removed for export] *)
    zstep. zstep. zstep.                          (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    unfold fk_held in DSH, AH, AID, AHD. pose proof (DSH m3 MU) as UD3. fk_hold DSH.
    assert (AH3 : AHEAP AI L RNG st LB m3).
    { eapply (AI_frame AI); [exact AH| exact MU| exact WM|].
      constructor; [cbn [fst snd]; left; left; cbn; clear - BOT LO RSP; lia|].
      constructor; [cbn [fst snd]; apply fk_acr_inblk; destruct AID as (bb & Hb & Hb1 & Hb2); exists bb; split; [exact Hb| cbn; clear - Hb1 Hb2; lia] | constructor]. }
    pose proof (AI_rtcells AI _ _ _ _ _ AH3) as (_ & RT1 & RT2 & RT3 & RT4 & _ & RT6 & RT7 & _). clear AH3. fk_hold AH. fk_hold AID.
    lazymatch goal with H : rw_cells bsegs _ (DCTX + 30184) _ |- _ => destruct (rw_cells_forget bsegs _ _ _ H) as [jk HJ]; clear H end.
    cbn [cells_size csize Nat.add] in HJ.
    call (zd_memsetZ_proofA RNG (DCTX + 30184) 16 0 (SPV + -80));
      [ exact HJ | lia | lia | eassumption | clear - LO; lia | clear - RSP; lia | clear - S_DC LO; lia
      | apply ablk_app_blk; [eapply ablk_sub; [exact DBK| clear; lia| clear; lia] | clear; lia]
      | eapply aro_sub; [split; [exact UD3| split; [exact RDc1| exact RDc2]] | clear; lia | clear; lia | clear; lia]
      | eapply dd_ahull_sub; [eapply dd_ahull_wmono; [exact AHD| exact WM]| clear; lia| clear; lia]
      | unfold art; split; [exact RT1|]; split; [exact RT2|]; split; [exact RT4|]; split; [exact RT6|]; split; [exact RT7| exact RT3]
      | eapply astk_sub; [split; [exact KHI| split; [exact RSTK| exact RI]] | clear - LO; lia]
      | eassumption
      | reflexivity | reflexivity | reflexivity | ].
    clear UD3. fk_hold AHD. rename x into xw.
    lazymatch goal with H : stk bsegs _ lo (SPV + -80) |- _ => rename H into ST end.
    lazymatch goal with H : rw_cells bsegs _ (DCTX + 30184) [CB _ _] |- _ => try change (Z.to_nat 16) with 16%nat in H; apply zero16_c8sA in H end.
    do 8 zstep.                                   (* [comment removed for export] *)
    do 9 zstep.                                   (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    lazymatch goal with H : rw_cells bsegs _ (SPV + -80) _ |- _ => release_frame H ST SPV end.
    zstep.                                        (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
    unfold fk_held in *.
    rename MU into MU04. rename WM into WM04.
    lazymatch goal with H : mem_inv bsegs m4 |- _ => rename H into MI4 end.
    lazymatch goal with H : stk bsegs m4 lo SPV |- _ => rename H into ST4 end.
    lazymatch goal with H : rw_cells bsegs m4 (DCTX + 30184) _ |- _ => rename H into H5D4 end.
    pose proof (DSH m4 MU04) as UD4.
    (* [comment removed for export] *)
    assert (H5C4 : rw_cells bsegs m4 (DCTX + 30096) (h5_cells ws)).
    { rewrite EWS. cbv beta iota delta [h5_cells h5_sizes mk_wcells].
      apply (proj2 (rw_cells_app bsegs _ _ [C8 w0; C4 w1; C4 w2; C4 w3; C4 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C4 w12; C4 w13] _)).
      split; [eapply rw_cells_transport; [exact H5A| exact MU04| exact WM04| cbn; apply DJ4; [clear - S_DC LO; lia| clear; lia| clear; lia]]|].
      cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]. match goal with |- rw_cells _ _ ?a _ => replace a with (DCTX + 30184) by (clear; lia) end.
      apply (proj2 (rw_cells_app bsegs _ _ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] _)). split; [exact H5D4|].
      cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. match goal with |- rw_cells _ _ ?a _ => replace a with (DCTX + 30200) by (clear; lia) end.
      lazymatch type of H5T with rw_cells _ ?mm _ _ => first [ exact H5T | eapply rw_cells_transport; [exact H5T| exact MU04| exact WM04| cbn; apply DJ4; [clear - S_DC LO; lia| clear; lia| clear; lia]] ] end. }
    assert (DA4 : dctx_any m4 DCTX).
    { exists llt, mlt, oft, huf, pde, pfx, vst, dend, expd, fp, pcs, dsz, bt, stg, le, fe, xs, ws, jhb, ovd, dcb, dce, trace.
      assert (TR : forall A cs, rw_cells bsegs m A cs -> DCTX <= A -> A + Z.of_nat (cells_size cs) <= DCTX + 95992 ->
                   (A + Z.of_nat (cells_size cs) <= DCTX + 30184 \/ DCTX + 30212 <= A) -> rw_cells bsegs m4 A cs).
      { intros A cs RC L1 L2 L3. eapply rw_cells_transport; [exact RC | exact MU04 | exact WM04 |]. cbn [disjoint_from]. clear - L1 L2 L3 S_DC LO. repeat split; lia. }
      assert (TS : forall a b, stk bsegs m a b -> DCTX <= a -> a <= b -> b <= DCTX + 95992 -> (b <= DCTX + 30184 \/ DCTX + 30212 <= a) -> stk bsegs m4 a b).
      { intros a b SK L1 L2 L3 L4. eapply stk_transport_disjoint; [exact SK | exact MU04 | exact WM04 |]. cbn [disjoint_from]. clear - L1 L2 L3 L4 S_DC LO. repeat split; lia. }
      unfold dctx_ptrs, dctx_h1, dctx_h3, dctx_tx in *.
      split; [apply TR; [exact PT | clear; lia | cbn; clear; lia | cbn; clear; lia]|].
      split; [apply TR; [exact H1 | clear; lia | cbn; clear; lia | cbn; clear; lia]|].
      split; [split; [apply TR; [exact FPC | clear; lia | rewrite FPSZ; clear; lia | rewrite FPSZ; clear; lia]| exact FPSZ]|].
      split; [apply TR; [exact H3 | clear; lia | cbn; clear; lia | cbn; clear; lia]|].
      split; [split; [apply TR; [exact XSC | clear; lia | rewrite XSSZ; clear; lia | rewrite XSSZ; clear; lia]| exact XSSZ]|].
      split; [split; [exact H5C4| exact H5L]|].
      split; [exact H5OK|].
      split; [apply TR; [exact TX | clear; lia | cbn; clear; lia | cbn; clear; lia]|].
      split; (apply TS; [assumption| clear; lia| clear; lia| clear; lia| clear; lia]). }
    assert (AH4 : AHEAP AI L RNG st LB m4).
    { eapply (AI_frame AI); [exact AH| exact MU04| exact WM04|].
      constructor; [cbn [fst snd]; left; left; cbn; clear - BOT LO RSP; lia|].
      constructor; [cbn [fst snd]; apply fk_acr_inblk; destruct AID as (bb & Hb & Hb1 & Hb2); exists bb; split; [exact Hb| cbn; clear - Hb1 Hb2; lia] | constructor]. }
    assert (ART4 : art m4).
    { pose proof (AI_rtcells AI _ _ _ _ _ AH4) as (_ & A & B & C & D & E & F' & G' & _).
      unfold art. split; [exact A|]. split; [exact B|]. split; [exact D|]. split; [exact F'|]. split; [exact G'| exact C]. }
    assert (AW : aappW [(SPV - 2288, SPV); (DCTX + 30184, DCTX + 30212)]).
    { unfold aappW. unfold KLS, KLOW, KHIGH in *. apply Forall_cons; [cbn [fst snd]; clear - KHI LO; lia|]. apply Forall_cons; [cbn [fst snd]; clear - DBD; lia| apply Forall_nil]. }
    assert (DS4 : forall X n, 0 <= X -> 0 <= n -> X + n <= 2^47 -> disjoint_from [(SPV - 2288, SPV); (DCTX + 30184, DCTX + 30212)] (shad X) (shad (X + n - 1) + 1 - shad X)).
    { intros X n A B C. apply aappW_shadow_disjoint; [exact AW| | | |]; rewrite ?shad_div; unfold ASHOFF, KEND in *; clear - A B C ATR; Z.div_mod_to_equations; lia. }
    unfold zd_dmf_stmtA, APZD_DMF in DMF.
    eapply evtF_mono.
    - eapply (DMF L RNG st LB) with (lo := lo) (DCTX := DCTX) (DST := DST) (CAP := CAP) (SRC := SRC) (src := src) (size := size);
        first [ exact DA4 | exact RD0 | exact RD1 | exact RD8 | exact OK | exact N0 | exact NLEN | exact N40 | exact RS0 | exact RS1 | exact RC0 | exact RC40 | exact DNULL | exact DNN | exact DZ | exact RDST
              | exact RLO | exact LO | exact RSP | exact S_DC | exact S_DS | exact S_SR | exact S_GT | exact D_DC | exact D_SR | exact SR_DC | exact GT_DC | exact GT_DS | exact TP | exact AIS | exact AID | exact MI4 | reflexivity
              | eapply rw_cells_transport; [exact GOT| exact MU04| exact WM04| cbn; clear - S_GT GT_DC LO; repeat split; lia]
              | eapply bytes_at_transport; [exact SB| exact MU04| rewrite length_map; cbn; clear - S_SR SR_DC LO DB; repeat split; lia]
              | eapply stk_transport_disjoint; [exact DSK| exact MU04| exact WM04| cbn; clear - S_DS D_DC LO RC0; repeat split; lia]
              | exact ST4
              | unfold afpre, astk; split; [exact AH4|]; split; [exact ASH|]; split; [exact ART4|]; split; [split; [exact KHI| split; [exact RSTK| exact RI]]|];
                split; [exact RFS|]; split; [exact BOT|]; split; [exact SPT|]; split; [exact SP16|]; split; [exact RSTKT| exact LBH]
              | eapply azstk_transport; [exact AZS| exact MU04| exact WM04| exact AW| clear - LO; lia]
              | eapply aro_client_transport_gen; [exact WM04| exact ARO| exact MU04|]; intros A n HIn; destruct (aclient_bounds A n HIn) as (B1 & B2 & B3);
                cbn [disjoint_from]; rewrite !shad_div; unfold ASHOFF; unfold KHIGH in KHI; clear - B1 B2 B3 KHI LO DL; repeat split; Z.div_mod_to_equations; lia
              | intros NZ; destruct (ARS NZ) as (Q1 & Q2 & Q3 & Q4); split; [exact Q1| split; [eapply unpoisoned_munch; [exact Q2| exact MU04| apply DS4; pose proof (fk_ablk_lits _ _ Q1) as QL; clear - QL NZ ATR; lia]| split; [exact Q3| exact Q4]]]
              | intros NZ; eapply dd_ahull_wmono; [exact (AHS NZ)| exact WM04]
              | intros _; split; [exact DBK| split; [exact UD4| split; [exact RDc1| exact RDc2]]]
              | eapply dd_ahull_wmono; [exact AHD| exact WM04]
              | intros NC; destruct (ADST NC) as (Q1 & Q2 & Q3); split; [| split; [eapply dd_ahull_wmono; [exact Q2| exact WM04]| exact Q3]];
                intros _; destruct (Q1 NC) as (P1 & P2 & P3 & P4); split; [exact P1| split; [eapply unpoisoned_munch; [exact P2| exact MU04| apply DS4; pose proof (fk_ablk_lits _ _ P1) as PL; clear - PL NC ATR RDST; lia]| split; [exact P3| exact P4]]]
              | lazymatch goal with |- ?Gg => idtac "LEFT:" Gg end ].
    - intros ms' PO'. unfold zd_dmf_postA in PO' |- *.
      destruct PO' as (q0 & q1 & q2 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q23 & q24 & q25 & q26 & m5 & r & -> & MU5 & WM5 & MI5 & ST5 & FFR5 & AH5 & DA5 & DSK5 & RR & ROK).
      do 14 eexists. exists m5, r. split; [reflexivity|].
      split; [eapply munch_trans; [eapply munch_weaken; [| exact MU04]; unfold sub_fp; cbn [outside app]; intros x Hx; clear - Hx LO; lia | exact MU5]|].
      split; [exact (wmono_trans _ _ _ _ WM04 WM5)|]. split; [exact MI5|]. split; [exact ST5|].
      split; [| split; [exact AH5| split; [exact DA5| split; [exact DSK5| split; [exact RR| exact ROK]]]]].
      eapply ffr_pres_trans; [| exact FFR5].
      (* [comment removed for export] *)
      eapply magree_mono; [eapply magree_of_munch; [exact MU04| exact WM04]|].
      intros a [((c & A & k & Hb & Hr) & HO)|(a' & (c & A & k & Hb & Hr) & ->)];
        pose proof (AI_block_bounds AI _ _ _ _ _ _ AH Hb) as (B1 & B2 & B3); cbn [ab_addr ab_size] in B1, B2, B3.
      + cbn [outside]. cbn [outside app] in HO. destruct HO as (O1 & O2 & _). clear - Hr B3 O1 BOT LO. repeat split; lia.
      + cbn [outside]. rewrite shad_div. unfold ASHOFF, AIMG_HI, KLS, KHIGH in *. clear - Hr B1 B3 ATR BOT LO DBD DL. repeat split; Z.div_mod_to_equations; lia.
  Qed.
End Thm.
End CANSEC1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
