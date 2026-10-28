(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable ZdLit.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import DrvAgree FseWalkKit FseRdKit FseRdKit2 ZdFrameW ZdWalkKit ZdCellKit ZdDctxRep ZdTbl MemRange.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AProto AMalloc_iface AProg_kit AFake_iface AFakeK_iface
     AZ_kit AZ_globals AZ_globalsR AZ_fkit AZ_frame_iface AZ_libc_iface AF_fse_rd_base AF_fse_rd_mem AF_fse_rd_seg AF_fse_rd_asm
     AZ_huf_iface AZ_block_iface AZ_blk_iface3 AZ_blk_iface5 AZ_blk_iface6 AZ_seq_iface AZ_hufinv AZ_tbl
     AZ_findfsi_a AZ_dblock_a AZ_dblock_b AZ_dblock_c AZ_dblock_d AZ_dblock_e AZ_dblock_g AZ_dblock_h.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKitF.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_enrich ::= rewrite ?shad_div in *; rewrite ?nshad_div in *; unfold ASHOFF, KLOW, KHIGH, KEND in *; rewrite ?Z.shiftr_div_pow2 in * by lia.
Ltac rd_retlit := lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.

Notation zlen l := (Z.of_nat (length l)).
Notation FB0 F := (mkABlock (ABFake 0) F 64).
Notation SHB := 2147450880.
Notation BF1 := (Z_to_bv 8 18446744073709551601).
Notation BF3 := (Z_to_bv 8 18446744073709551603).
Notation BF8 := (Z_to_bv 8 18446744073709551608).
Notation B00 := (Z_to_bv 8 0).

Section CANSEC1. Context {rc : runConstT}.
Lemma db_got_cells : forall m, (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None) ->
  rw_cells bsegs m 0xc7360 [C8 (Z_to_bv 64 0xcfd00)] /\ rw_cells bsegs m 0xc7308 [C8 (Z_to_bv 64 0xcfcf8)].
Proof.
  intros m R. split; (apply relro_wordA; [exact R| unfold ARELRO_LO; lia| unfold ARELRO_HI; lia| vm_compute; reflexivity]).
Qed.

Definition DSH00 : list cell := [C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00; C1 B00].
Lemma db_shadow8_c1s : forall (m : amem) s, rw_cells bsegs m s [C8 (Z_to_bv 64 0)] -> rw_cells bsegs m s DSH00.
Proof. intros m s H. eapply rw_cells_recast; [exact H| cbn; repeat split; exact I| vm_compute; reflexivity| reflexivity]. Qed.

(* [comment removed for export] *)
Lemma db_stk_pres : forall AI LB SP (m m' : amem) lo hi,
  aheap_pres (aci AI) LB SP m m' -> ainblk LB lo (hi - lo) -> stk bsegs m lo hi -> stk bsegs m' lo hi.
Proof.
  intros AI LB SP m m' lo hi HP (b & Hb & H1 & H2) (A0 & A1 & HW). split; [exact A0|]. split; [exact A1|].
  intros i Hi. destruct (HP i ltac:(clear - Hi A0 A1; lia) ltac:(right; right; left; exists b; split; [exact Hb| clear - Hi H1 H2; lia])) as [E W].
  destruct (HW i Hi) as [W0 [bb Hbb]]. split; [apply W, W0|]. exists bb. unfold mrd in *. rewrite E. exact Hbb.
Qed.

(* [comment removed for export] *)
Lemma db_atbl_pres : forall AI LB SP (m m' : amem) DCTX llt mlt oft huf le fe,
  aheap_pres (aci AI) LB SP m m' -> ainblk LB DCTX 95992 -> mem_inv bsegs m' ->
  atbl HUFINVw m DCTX llt mlt oft huf le fe -> atbl HUFINVw m' DCTX llt mlt oft huf le fe.
Proof.
  intros AI LB SP m m' DCTX llt mlt oft huf le fe HP IB MI' [TS (E & (h4 & B4 & L4 & N4) & TOK)].
  assert (BY : forall A bs, bytes_at bsegs m A bs -> DCTX <= A -> A + zlen bs <= DCTX + 95992 -> bytes_at bsegs m' A bs).
  { intros A bs B G1 G2. eapply (fk_bytes_pres AI); [exact HP| | exact B]. destruct IB as (bb & Hb & Hb1 & Hb2). exists bb. split; [exact Hb| clear - Hb1 Hb2 G1 G2; lia]. }
  split.
  - intros NZ. destruct (TS NZ) as (LLT & MLT & OFT & tLL & tOF & tML & E1 & E2 & E3 & P1 & P2 & P3 & A1 & A2 & A3).
    exists LLT, MLT, OFT, tLL, tOF, tML. repeat (split; [assumption|]).
    assert (OWN : forall k T t own dflt d, seq_tbl_at bsegs m k T t -> tbl_ptr DCTX own dflt d T t -> seq_tbl_at bsegs m' k dflt d ->
                  32 <= own -> own + 8 * (1 + 2^(kind_maxLog k)) <= 10296 -> seq_tbl_at bsegs m' k T t).
    { intros k T t own dflt d (BA & OK) [-> | [-> ->]] DF O1 O2; [| exact DF]. split; [| exact OK]. pose proof (seq_tbl_len_le k t OK) as LEN.
      apply BY; [exact BA| clear - O1; lia| clear - O2 LEN; lia]. }
    split; [| split].
    + eapply (OWN K_LL); [exact A1| exact P1| split; [apply all_default_at; exact MI'| apply LL_default_ok]| unfold DCTX_entropy_LLTable; clear; lia| unfold DCTX_entropy_LLTable; cbn [kind_maxLog]; clear; lia].
    + eapply (OWN K_OF); [exact A2| exact P2| split; [apply aof_default_at; exact MI'| apply OF_default_ok]| unfold DCTX_entropy_OFTable; clear; lia| unfold DCTX_entropy_OFTable; cbn [kind_maxLog]; clear; lia].
    + eapply (OWN K_ML); [exact A3| exact P3| split; [apply aml_default_at; exact MI'| apply ML_default_ok]| unfold DCTX_entropy_MLTable; clear; lia| unfold DCTX_entropy_MLTable; cbn [kind_maxLog]; clear; lia].
  - split; [exact E|]. split.
    + exists h4. split; [| split; [exact L4| exact N4]]. apply BY; [exact B4| clear; lia| rewrite L4; clear; cbn; lia].
    + intros NZ. destruct (TOK NZ) as (dtb & BA & OK). exists dtb. split; [|exact OK].
      assert (LD : zlen dtb = 16388) by (destruct OK as [[LD _] _]; exact LD).
      apply BY; [exact BA| clear; lia| rewrite LD; clear; lia].
Qed.

Section S.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32).
  Variables (SPV lo : Z).
  Hypothesis SP16 : SPV mod 16 = 0.
  Hypothesis SPT : SPV + 16 < KEND.
  Hypothesis LOS : lo <= SPV - 208 - 4096.
  Hypothesis LOC : ATOP <= lo.
  Variable RNG : footprint.
  Hypothesis RSTK : rng RNG lo (SPV - lo).
  Hypothesis RI : rng_aimg RNG.

  Definition HSPA : Z := (SPV - 192) - (SPV - 192) mod 32.
  Lemma hspa_props : SPV - 208 <= HSPA <= SPV - 192 /\ HSPA mod 32 = 0 /\ (SPV + -192) - (SPV + -192) mod 2^5 = HSPA.
  Proof. unfold HSPA. change (2^5) with 32. clear - SP16. Z.div_mod_to_equations. lia. Qed.

  (* [comment removed for export] *)
  Lemma db_pro : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m,
    stk bsegs m lo SPV -> mem_inv bsegs m ->
    rt_shbase m -> rw_cells bsegs m 0xc7360 [C8 (Z_to_bv 64 0xcfd00)] -> rw_cells bsegs m 0xc7308 [C8 (Z_to_bv 64 0xcfcf8)] ->
    rw_cells bsegs m 0xcfd00 [C4 (Z_to_bv 64 1)] ->
    evtF bsegs RNG (fun ms' => exists m' jA jB,
        ms' = MS (mkR (Z_to_bv 64 0x893f0) (Z_to_bv 64 HSPA) gp tp t0 t1 t2 (Z_to_bv 64 SPV) (Z_to_bv 64 HSPA)
                     (Z_to_bv 64 64) (Z_to_bv 64 1) a2 a3 a4 a5 a0 a7
                     a0 s3 s4 (Z_to_bv 64 SHB) (Z_to_bv 64 29904) a4 a3 a5 s10 s11 t3 t4 t5 t6)
                 FR (Z_to_bv 64 0x3ee8c) fc None m' (seg_rom bsegs)
        /\ munch [(SPV - 192, SPV)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
        /\ rw_cells bsegs m' (SPV + -104) (FSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
        /\ rw_cells bsegs m' HSPA [CB 48 jA; C8 a1; C8 a2; CB 24 jB]
        /\ stk bsegs m' lo HSPA /\ stk bsegs m' (HSPA + 88) (SPV + -104))
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 0x89360) fc None m (seg_rom bsegs)).
  Proof.
    intros until m. intros ST MI SHBm GOT1 GOT2 SUA.
    unfold KEND in SPT. pose proof atop_range as ATR.
    pose proof hspa_props as (SPAB & SPA32 & ESPA').
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(SPV - 192, SPV)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    zstep.                                        (* [comment removed for export] *)
    carve_frame 104%nat ST. carve_frame 88%nat ST.
    zstep.                                        (* [comment removed for export] *)
    do 13 zstep.                                  (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    change 18446744073709551584 with (2^64 - 2^5). rewrite land_align_downA by lia. rewrite ESPA'.
    release_frame FR1 ST (SPV + -104).
    destruct (stk_split bsegs _ lo (HSPA + 88) (SPV + -104) ST ltac:(lia)) as [ST1 STG]. clear ST.
    destruct (stk_carve bsegs _ lo (HSPA + 88) 88 ST1 ltac:(cbn; lia)) as [STL [jA FRA]]. clear ST1.
    change (Z.of_nat 88) with 88 in STL, FRA. replace (HSPA + 88 - 88) with HSPA in STL, FRA by lia.
    zstep.                                        (* [comment removed for export] *)
    zstep. zstep.                                 (* [comment removed for export] *)
    zstep. zstep.                                 (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.     (* [comment removed for export] *)
    clear GOT1 GOT2.
    zstep. rewrite (sx32_small 1) by lia.         (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep. zstep.                                 (* [comment removed for export] *)
    zstep. bcase K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|].   (* [comment removed for export] *)
    zstep. zstep. zstep.                          (* [comment removed for export] *)
    apply evtF_done.
    eexists _, _, _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [exact FR0|]. split; [eassumption|]. split; [exact STL| exact STG].
  Qed.

  (* [comment removed for export] *)
  Lemma db_hdr : forall (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 xs3 xs4 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31 : word) m (FF FLG DCTX : Z)
      (j0 j1 j2 wd wc : word) (jA jB : list byte) (junk : list byte),
    rw_cells bsegs m FF [C8 j0; C8 j1; C8 j2; CB 32 junk; C8 (Z_to_bv 64 FLG)] ->
    rw_cells bsegs m (shad FF) [C8 (Z_to_bv 64 0)] ->
    rw_cells bsegs m HSPA [CB 48 jA; C8 wd; C8 wc; CB 24 jB] ->
    rw_cells bsegs m 0xc7fb8 [C8 (Z_to_bv 64 0x89360)] ->
    mem_inv bsegs m ->
    ablk FF (FF + 64) -> FF + 64 <= ATOP -> FF mod 64 = 0 -> rng RNG FF 64 -> rng RNG (shad FF) 8 ->
    4096 <= DCTX -> DCTX + 95992 < 2^47 -> DCTX mod 8 = 0 -> (DCTX + 95992 <= FF \/ FF + 64 <= DCTX) -> ablk DCTX (DCTX + 95992) ->
    unpoisoned m DCTX (DCTX + 95992) -> rng RNG (shad DCTX) (shspan DCTX 95992) ->
    evtF bsegs RNG (fun ms' => exists m' (ya0 ya1 ya2 ya3 ya4 ya5 : word) jB',
        ms' = MS (mkR (Z_to_bv 64 0x893f0) (Z_to_bv 64 HSPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 HSPA)
                     ya0 ya1 ya2 ya3 ya4 ya5 (Z_to_bv 64 DCTX) x17
                     (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr (DCTX + 30176) 3 + SHB)) (Z_to_bv 64 (Z.shiftr FF 3 + SHB)) (Z_to_bv 64 SHB) (Z_to_bv 64 (DCTX + 29904))
                     xs7 xs8 xs9 (Z_to_bv 64 (DCTX + 30176)) (Z_to_bv 64 FF) x28 x29 x30 x31)
                 FR (Z_to_bv 64 0x894a4) fc None m' (seg_rom bsegs)
        /\ munch [(FF, FF + 24); (Z.shiftr FF 3 + SHB, Z.shiftr FF 3 + SHB + 8); (HSPA + 80, HSPA + 88)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
        /\ rw_cells bsegs m' FF [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x1d28b); C8 (Z_to_bv 64 0x89360); CB 32 junk; C8 (Z_to_bv 64 FLG)]
        /\ rw_cells bsegs m' (Z.shiftr FF 3 + SHB) BSH0
        /\ rw_cells bsegs m' HSPA [CB 48 jA; C8 wd; C8 wc; CB 16 jB'; C8 (Z_to_bv 64 FF)])
      (MS (mkR (Z_to_bv 64 0x893f0) (Z_to_bv 64 HSPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 HSPA)
               (Z_to_bv 64 FF) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 DCTX) xs3 xs4 (Z_to_bv 64 SHB) (Z_to_bv 64 29904) xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31)
          FR (Z_to_bv 64 0x893f0) fc None m (seg_rom bsegs)).
  Proof.
    intros until junk. intros FFC SHF FRA GOT3 MI FH FC F64 RF RSF DCL DCH DCA DCAP DBK UD RDS.
    pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in *.
    pose proof atop_range as ATR. unfold KEND in SPT.
    pose proof hspa_props as (SPAB & SPA32 & _).
    pose proof (fk_ablk_lits _ _ DBK) as DL. pose proof (fk_ablk_lits _ _ FH) as FL.
    apply db_shadow8_c1s in SHF. unfold DSH00 in SHF. replace (shad FF) with (Z.shiftr FF 3 + SHB) in SHF, RSF by (unfold shad, ASHOFF; lia).
    assert (BSF : SHB + 805376 <= Z.shiftr FF 3 + SHB /\ Z.shiftr FF 3 + SHB + 8 <= 17594333495296)
      by (rewrite Z.shiftr_div_pow2 by lia; clear - FL ATR; Z.div_mod_to_equations; lia).
    pose proof FH as FHu. unfold ablk, AIMG_HI, KLS in FHu.
    pose proof (munch_refl [(FF, FF + 24); (Z.shiftr FF 3 + SHB, Z.shiftr FF 3 + SHB + 8); (HSPA + 80, HSPA + 88)] m) as MU.
    pose proof (wmono_refl bsegs m) as WM.
    assert (DG : DCTX mod 8 = 0 /\ 0 <= DCTX /\ DCTX + 95992 <= 2^47) by (clear - DCA DCL DCH; lia).
    fk_hold UD. fk_hold RDS. fk_hold DCAP.
    zstep. zstep. zstep. zstep.                   (* [comment removed for export] *)
    zstep. bcase K0; [| exfalso; rewrite ?unsigned_lit in K0 by lia; lia].   (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    do 6 zstep.                                   (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep. clear GOT3.                            (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    zstep. zstep. zstep.                          (* [comment removed for export] *)
    zstep. try (let w := getreg 26 in replace w with (Z_to_bv 64 (DCTX + 30176)) by (f_equal; clear; lia)).   (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    replace (Z_to_bv 64 (-8)) with (Z_to_bv 64 18446744073709551608) by (apply Z_to_bv_eqm; reflexivity).
    replace (Z_to_bv 64 (-13)) with (Z_to_bv 64 18446744073709551603) by (apply Z_to_bv_eqm; reflexivity).
    zstep.                                        (* [comment removed for export] *)
    zstep. zstep. zstep.                          (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    replace (Z_to_bv 64 (-15)) with (Z_to_bv 64 18446744073709551601) by (apply Z_to_bv_eqm; reflexivity).
    do 4 zstep.                                   (* [comment removed for export] *)
    (* [comment removed for export] *)
    zstep.                                        (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    try (let w := getreg 22 in replace w with (Z_to_bv 64 (DCTX + 29904)) by (f_equal; clear; lia)).
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    unfold fk_held in UD, RDS, DCAP.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (UDx : unpoisoned mx DCTX (DCTX + 95992))
        by (eapply unpoisoned_munch; [exact UD| exact MU|]; cbn [disjoint_from]; rewrite !shad_div; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8; unfold ASHOFF;
            clear - DL FL ATR DCAP F64 SPAB LOC LOS; repeat split; Z.div_mod_to_equations; lia);
      pose proof (db_sh_rd0s mx DCTX 95992 (DCTX + 30176) UDx ltac:(clear; lia) ltac:(clear - DG; Z.div_mod_to_equations; lia) ltac:(clear - DG; lia) ltac:(clear - DG; lia)) as RDz;
      pose proof (db_sh_rng1 RNG DCTX (DCTX + 30176) RDS (proj1 DG) ltac:(clear; lia) ltac:(clear; lia)) as RTz; clear UDx end.
    zstep. clear RDz RTz. try replace (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) by reflexivity.   (* [comment removed for export] *)
    zstep. zstep; if_false.                       (* [comment removed for export] *)
    apply evtF_done.
    eexists _, _, _, _, _, _, _, _. split; [reflexivity|]. split; [eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia|].
    split; [exact WM|]. split; [eassumption|].
    split; [exact FFC|]. split; [unfold BSH0; exact SHF| exact FRA].
  Qed.
End S.

(* [comment removed for export] *)
Section Thm.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variable fflag : alayout -> Z -> Z -> Z.
  Variable rng_fs : alayout -> footprint -> Prop.
  Hypothesis SM0K : forall k, Z.of_nat k < 16384 -> stack_malloc_0k_stmt AI fflag rng_fs k.
  Hypothesis FFLAG : fake_flag_law AI fflag.
  Hypothesis FREL : fake_release_law AI fflag.
  Hypothesis FHL : fake_heap_law AI.
  Hypothesis DECLIT : zd_declit_stmtA AI rng_fs.
  Hypothesis SEQHDR : zd_seqhdr_stmtA AI rng_fs.
  Hypothesis OFFINFO : zd_offinfo_stmtA.
  Hypothesis SEQD : zd_seq_default_stmtA AI rng_fs.
  Hypothesis SEQS : zd_seq_split_stmtA AI rng_fs.
  Hypothesis SEQL : zd_seq_long_stmtA AI rng_fs.

  Theorem zd_dblock_proofA : zd_dblock_stmtA AI rng_fs (atbl HUFINVw).
  Proof.
    intros L RNG st LB ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m SPV lo DCTX DST CAP B0 B1 PFX SRC src ip cbs h
           llt mlt oft huf pde expd pcs dsz bt stg le fe ws
           PT H1C FPC BSM WND H3C H5C ISF OWN TB DCL DCH DCA SB FBYa IP0 CBSR IPC SRCL SRCH BUF B0D DCB CAP0 B1H WIN DNULL DNN DNB
           ST LO4 LOS SPH S_DC S_B S_SR BD BSRC SRCD AFP TP AZS ARO ARS AIS AHS DCA' ARD AHD AID ADST MI -> -> -> -> -> ->.
    destruct AFP as (AH & ASH & ART & (KHI & RSTK & RI) & RFS & BOT & SPT & SP16 & RSTKT & LBH).
    pose proof atop_range as ATR.
    pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & LY4 & LY5).
    destruct (FHL _ _ _ _ _ AH) as [FAB _]. pose proof (fk_ablk_lits _ _ FAB) as FABL.
    pose proof (AI_rtcells AI _ _ _ _ _ AH) as RTC. unfold artcells in RTC.
    destruct RTC as (C0 & GOT & RIC & REAL & SHBc & SUA & _).
    destruct (db_got_cells m (AI_relro AI _ _ _ _ _ AH)) as [G1 G2].
    assert (LOS' : lo <= SPV - 208 - 4096) by (clear - LOS; lia).
    assert (LOC : ATOP <= lo) by (clear - BOT; lia).
    assert (SPK : SPV + 16 < KEND) by (unfold KEND; clear - SPT LY3; lia).
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (hspa_props SPV SP16) as (SPAB & SPA32 & _).
    pose proof (ARD ltac:(clear; lia)) as (DBK & UD0 & RD1r & RD2r). pose proof (fk_ablk_lits _ _ DBK) as DL.
    destruct H5C as [H5C H5L]. unfold dctx_ptrs in PT. unfold dctx_h1 in H1C. unfold dctx_h3 in H3C. destruct OWN as [OW1 OW2].
    pose proof (bytes_at_bound _ _ _ _ SB) as SBL. rewrite length_map in SBL.
    unfold APZD_DBLOCK.
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply (db_pro ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc SPV lo SP16 SPK LOS' LOC RNG RSTK RI);
        [exact ST| exact MI| exact SHBc| exact G1| exact G2| exact SUA]. }
    cbv beta. intros ms' (m1 & jA & jB & -> & MU1 & WM1 & MI1 & SAV1 & FRA1 & STL1 & STG1).
    clear C0 GOT RIC REAL SHBc SUA G1 G2.
    assert (AH1 : AHEAP AI L RNG st LB m1).
    { eapply (AI_frame AI); [exact AH| exact MU1| exact WM1|]. constructor; [| constructor]. left; left. cbn. clear - BOT LOS SPH; lia. }
    assert (D1 : forall X n, (X + n <= lo \/ SPV <= X) -> 0 <= n -> disjoint_from [(SPV - 192, SPV)] X n).
    { intros X nn HX Hn. cbn [disjoint_from]. split; [clear - HX Hn LOS; lia| exact I]. }
    assert (DS1 : forall X n, 0 <= X -> 0 <= n -> X + n <= 2^47 -> disjoint_from [(SPV - 192, SPV)] (shad X) (shad (X + n - 1) + 1 - shad X)).
    { intros X nn X0 Hn Hb. cbn [disjoint_from]. split; [| exact I]. left. rewrite !shad_div. unfold ASHOFF in *.
      clear - X0 Hn Hb ATR BOT LOS. Z.div_mod_to_equations. lia. }
    pose proof (rw_cells_transport _ _ _ _ _ _ PT MU1 WM1 ltac:(cbn; apply D1; [clear - S_DC; lia| clear; lia])) as PT1.
    pose proof (rw_cells_transport _ _ _ _ _ _ H1C MU1 WM1 ltac:(cbn; apply D1; [clear - S_DC; lia| clear; lia])) as H1C1.
    pose proof (rw_cells_transport _ _ _ _ _ _ FPC MU1 WM1 ltac:(unfold zfh_cells; cbn; apply D1; [clear - S_DC; lia| clear; lia])) as FPC1.
    pose proof (rw_cells_transport _ _ _ _ _ _ H3C MU1 WM1 ltac:(cbn; apply D1; [clear - S_DC; lia| clear; lia])) as H3C1.
    pose proof (rw_cells_transport _ _ _ _ _ _ H5C MU1 WM1 ltac:(rewrite (h5_cells_size _ H5L); apply D1; [clear - S_DC; lia| clear; lia])) as H5C1.
    pose proof (stk_transport_disjoint _ _ _ _ _ _ OW1 MU1 WM1 ltac:(apply D1; clear - S_DC; lia)) as OW11.
    pose proof (stk_transport_disjoint _ _ _ _ _ _ OW2 MU1 WM1 ltac:(apply D1; clear - S_DC; lia)) as OW21.
    assert (TB1 : atbl HUFINVw m1 DCTX llt mlt oft huf le fe).
    { eapply (atbl_frame HUFINVw hufw_frame); [exact TB| exact MU1| exact MI| exact MI1|]. intros x Hx. cbn [outside]. split; [clear - Hx S_DC LOS; lia| exact I]. }
    (* [comment removed for export] *)
    pose proof (ASH 0 ltac:(clear; lia)) as FLE.
    eapply evtF_cut.
    { pose proof (SM0K (Z.to_nat (4096 - 6)) ltac:(clear; lia)) as SMC. unfold stack_malloc_0k_stmt in SMC. eapply SMC with (lo := lo); clear SMC;
        rewrite ?(unsigned_lit (HSPA SPV)) by (clear - SPAB BOT LOS SPH ATR; lia);
        first [exact AH1| exact FLE| exact MI1| exact STL1| exact TP| reflexivity| exact RSTKT| exact RI| exact RFS
              | unfold SMK_STACK; clear - SPAB BOT LOS SPT; lia]. }
    cbv beta. intros ms' PO.
    destruct PO as (FF & z5 & z6 & z7 & e11 & e12 & e13 & e14 & e15 & e16 & e17 & z28 & z29 & z30 & z31 & m2 & j0 & j1 & j2 & junk
                    & -> & MI2 & ST2 & HPR2 & AH2 & F64 & FH & FC & FFC2 & SHF2 & RFF & RSFF & MUF2 & WM2 & FFA1 & FFA2).
    rewrite ?(unsigned_lit (HSPA SPV)) in ST2, HPR2, MUF2 by (clear - SPAB BOT LOS SPH ATR; lia).
    rd_retlit.
    pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in FHa. pose proof (fk_ablk_lits _ _ FH) as FL.
    pose proof (fk_frame_apart AI _ _ _ _ _ _ _ _ AH2) as FFD.
    pose proof (aheap_pres_rw_cells _ _ _ _ _ _ _ HPR2 SAV1 ltac:(left; left; cbn; clear - SPAB BOT LOS SPH; lia)) as SAV2.
    pose proof (aheap_pres_rw_cells _ _ _ _ _ _ _ HPR2 FRA1 ltac:(left; left; cbn; clear - SPAB BOT LOS SPH; lia)) as FRA2.
    pose proof (aheap_pres_stk _ _ _ _ _ _ _ HPR2 STG1 ltac:(clear - SPAB; lia) ltac:(clear - SPH; lia)) as STG2.
    assert (AINS : forall X k, DCTX <= X -> X + k <= DCTX + 95992 -> ainblk LB X k)
      by (intros X k A B; destruct AID as (bb & Hb & Hb1 & Hb2); exists bb; split; [exact Hb| clear - A B Hb1 Hb2; lia]).
    pose proof (fk_cells_pres AI LB (HSPA SPV) m1 m2 DCTX [C8 llt; C8 mlt; C8 oft; C8 huf] HPR2 ltac:(apply AINS; cbn; clear; lia) PT1) as PT2.
    pose proof (fk_cells_pres AI LB (HSPA SPV) m1 m2 (DCTX + 29888) [C8 pde; C8 (Z_to_bv 64 PFX); C8 (Z_to_bv 64 PFX); C8 (Z_to_bv 64 0); C8 expd] HPR2 ltac:(apply AINS; cbn; clear; lia) H1C1) as H1C2.
    pose proof (fk_cells_pres AI LB (HSPA SPV) m1 m2 (DCTX + 29928) (zfh_cells h) HPR2 ltac:(unfold zfh_cells; apply AINS; cbn; clear; lia) FPC1) as FPC2.
    pose proof (fk_cells_pres AI LB (HSPA SPV) m1 m2 (DCTX + 29976) [C8 pcs; C8 dsz; C4 bt; C4 stg; C4 le; C4 fe] HPR2 ltac:(apply AINS; cbn; clear; lia) H3C1) as H3C2.
    pose proof (fk_cells_pres AI LB (HSPA SPV) m1 m2 (DCTX + 30096) (h5_cells ws) HPR2 ltac:(rewrite (h5_cells_size _ H5L); apply AINS; clear; lia) H5C1) as H5C2.
    pose proof (db_stk_pres AI LB (HSPA SPV) m1 m2 (DCTX + 32) (DCTX + 29888) HPR2 ltac:(apply AINS; clear; lia) OW11) as OW12.
    pose proof (db_stk_pres AI LB (HSPA SPV) m1 m2 (DCTX + 30372) (DCTX + 95940) HPR2 ltac:(apply AINS; clear; lia) OW21) as OW22.
    assert (TB2 : atbl HUFINVw m2 DCTX llt mlt oft huf le fe) by (eapply (db_atbl_pres AI); [exact HPR2| exact AID| exact MI2| exact TB1]).
    pose proof (fk_relro_C8 AI _ _ _ _ _ 0xc7fb8 0x89360 AH2 ltac:(unfold ARELRO_LO; clear; lia) ltac:(unfold ARELRO_HI; clear; lia) ltac:(vm_compute; reflexivity)) as GOT3.
    assert (DCAP : DCTX + 95992 <= FF \/ FF + 64 <= DCTX) by (exact (fk_inblk_apart AI _ _ _ _ _ _ _ _ DCTX 95992 AH2 AID ltac:(clear; lia))).
    assert (UD2 : unpoisoned m2 DCTX (DCTX + 95992)).
    { assert (INLB : forall b, In b LB -> In b (FB0 FF :: LB)) by (intros b Hb; right; exact Hb).
      eapply (fk_unp_pres AI); [exact AH2| exact INLB| exact HPR2| exact AID| clear; lia|].
      eapply unpoisoned_munch; [exact UD0| exact MU1| apply DS1; clear - DL ATR; lia]. }
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply (db_hdr gp tp FR fc SPV lo SP16 LOS' LOC RNG RSTK RI);
        first [exact FFC2| exact SHF2| exact FRA2| exact GOT3| exact MI2| exact FH| exact FC| exact F64| exact RFF| exact RSFF| exact DCL| exact DCH| exact DCA| exact DCAP| exact DBK| exact UD2| exact RD2r]. }
    cbv beta. intros ms' (m3 & ya0 & ya1 & ya2 & ya3 & ya4 & ya5 & jB' & -> & MU3 & WM3 & MI3 & FFC3 & XS3 & FRA3).
    (* [comment removed for export] *)
    assert (BSF : SHB + 805376 <= Z.shiftr FF 3 + SHB /\ Z.shiftr FF 3 + SHB + 8 <= 17594333495296) by (rewrite Z.shiftr_div_pow2 by (clear; lia); clear - FL ATR; Z.div_mod_to_equations; lia).
    destruct (FFLAG _ _ _ _ _ 0 FF 64 AH2 ltac:(left; reflexivity)) as (XL2 & RL & LBK & LTOP & LAP & _ & LFA).
    pose proof (fk_ablk_lits _ _ LBK) as LL. pose proof (LAP _ ltac:(left; reflexivity)) as LFF. cbn [ab_addr ab_size] in LFF.
    assert (NZB : 0 < zlen src -> ablk SRC (SRC + zlen src) /\ unpoisoned m SRC (SRC + zlen src) /\ rng RNG SRC (zlen src) /\ rng RNG (shad SRC) (shspan SRC (zlen src)) /\ ainblk LB SRC (zlen src)).
    { intros NZ. destruct (ARS NZ) as (SBK & US0 & RS1 & RS2). pose proof (fk_ablk_lits _ _ SBK) as SL.
      assert (IB : ainblk LB SRC (zlen src)) by (destruct (AIS NZ) as [IB|[IM1 IM2]]; [exact IB| unfold AIMG_HI in IM2; exfalso; clear - IM2 SL NZ ATR; lia]).
      exact (conj SBK (conj US0 (conj RS1 (conj RS2 IB)))). }
    assert (SRCAP : 0 < zlen src -> SRC + zlen src <= FF \/ FF + 64 <= SRC).
    { intros NZ. destruct (NZB NZ) as (_ & _ & _ & _ & IB). exact (fk_inblk_apart AI _ _ _ _ _ _ _ _ SRC (zlen src) AH2 IB ltac:(clear - NZ; lia)). }
    assert (OUTB : B0 < B1 -> ablk B0 B1 /\ ainblk LB B0 (B1 - B0) /\ (B1 <= FF \/ FF + 64 <= B0)).
    { intros HB. destruct (ADST HB) as (ARb & _ & IBb). destruct (ARb ltac:(clear - HB; lia)) as (ABb & _).
      replace (B0 + (B1 - B0)) with B1 in ABb by (clear; lia).
      split; [exact ABb|]. split; [exact IBb|].
      pose proof (fk_inblk_apart AI _ _ _ _ _ _ _ _ B0 (B1 - B0) AH2 IBb ltac:(clear - HB; lia)) as AP. clear - AP; lia. }
    assert (CTX3 : AZ_dblock_a.DBCTX fflag rng_fs L RNG LB tp SPV (HSPA SPV) lo DCTX DST CAP B0 B1 PFX SRC src ip cbs h ws FF (Z.shiftr FF 3 + SHB) (fflag L 0 FF)).
    { unfold AZ_dblock_a.DBCTX.
      split; [clear - DCL DCH DCA IP0 CBSR IPC SRCL SRCH B0D DCB CAP0 B1H DNULL DNN LO4 LOS SPH; repeat split; first [assumption| lia]|].
      split; [exact (conj WIN (conj S_DC (conj S_B (conj S_SR (conj BD (conj BSRC SRCD))))))|].
      split; [split; [apply all_bytes_Forall; exact FBYa| split; [exact BSM| split; [exact WND| split; [exact ISF| exact H5L]]]]|].
      split; [unfold KHIGH in KHI |- *; unfold KEND in SPK; clear - BOT LOS SPAB SPA32 SPK SP16 KHI; repeat split; lia|].
      split; [split; [exact DBK| split; [exact AID| exact DCAP]]|].
      split; [split; [intros NZ; exact (proj1 (NZB NZ))| split; [intros NZ; destruct (NZB NZ) as (_ & _ & _ & _ & IB); exact IB| exact SRCAP]]|].
      split; [exact OUTB|].
      split; [split; [exact FH|]; split; [exact F64|]; split; [exact FC|]; split; [unfold shad, ASHOFF; clear; lia|]; split; [exact FFA1| exact FFA2]|].
      split; [split; [reflexivity|]; split; [exact LBK|]; split; [exact LTOP|]; split; [exact LFA| exact LAP]|].
      split; [split; [exact RSTK|]; split; [exact RI|]; split; [intros NZ; destruct (NZB NZ) as (_ & _ & R1 & R2 & _); exact (conj R1 R2)|];
              split; [exact RD1r|]; split; [exact RD2r|];
              split; [intros HB; destruct (ADST HB) as (ARb & _); destruct (ARb ltac:(clear - HB; lia)) as (_ & _ & R1 & R2); exact (conj R1 R2)|];
              split; [exact RFF|]; split; [replace (Z.shiftr FF 3 + SHB) with (shad FF) by (unfold shad, ASHOFF; clear; lia); exact RSFF| exact RL]|].
      split; [split; [exact LBH|]; split; [exact ASH|]; split; [exact RFS|]; split; [exact SPT|]; split; [exact RSTKT| exact TP]| exact DNB]. }
    (* [comment removed for export] *)
    assert (FFR02 : ffr_pres [] LB m m2).
    { eapply ffr_pres_trans; [eapply (fk_ffr_stack AI); [exact AH| exact MU1| exact WM1| constructor; [cbn; clear - BOT LOS SPH; lia| constructor]]|].
      eapply (fk_ffr_of_pres AI); exact HPR2. }
    assert (FFR03 : ffr_pres [(DST, DST + CAP); (DCTX, DCTX + 29888); (DCTX + 30000, DCTX + 30008); (DCTX + 30096, DCTX + 95940)] LB m m3).
    { apply ffr_pres_mono_nil1.
      eapply (fk_ffr_fin AI L RNG st LB m m2 m3 0 FF 64 (Z.shiftr FF 3 + SHB) 8 [] [(HSPA SPV + 80, HSPA SPV + 88); (FF, FF + 24)]);
        [ exact AH2 | exact LBH | exact FH | clear - F64; Z.div_mod_to_equations; lia | unfold shad, ASHOFF; clear; lia | clear; lia | clear; lia
        | constructor; [cbn [fst snd]; split; [clear; lia| left; unfold KEND in SPK; clear - BOT LOS SPAB SPK; lia]|];
          constructor; [cbn [fst snd]; split; [clear; lia | right; split; [intros b Hb; pose proof (FFD b Hb) as HB; cbn [ab_addr ab_size] in HB; clear - HB; lia
                                                            | exists FF, (FF + 64); split; [exact FH| clear; lia]]] | constructor]
        | constructor | exact FFR02 | | exact WM3 ].
      cbn [app]. eapply munch_weaken; [| exact MU3]. unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia. }
    assert (FA8 : al_fake L mod 8 = 0) by (clear; unfold al_fake; Z.div_mod_to_equations; lia).
    assert (MU03 : munch ([(DST, DST + CAP); (DCTX, DCTX + 29888); (DCTX + 30000, DCTX + 30008); (DCTX + 30096, DCTX + 95940); (SPV - 6384, SPV)] ++ fake_area L) m m3).
    { eapply munch_trans; [eapply munch_weaken; [| exact MU1]; unfold sub_fp, fake_area; cbn [outside app]; intros x Hx; clear - Hx; lia|].
      eapply munch_trans; [eapply munch_weaken; [| exact MUF2]; unfold sub_fp, fake_area, SMK_STACK; cbn [outside app]; intros x Hx; clear - Hx SPAB; repeat split; lia|].
      eapply munch_weaken; [| exact MU3]. unfold sub_fp, fake_area; cbn [outside app]; intros x Hx.
      rewrite shad_div in Hx. rewrite Z.shiftr_div_pow2 by (clear; lia). change (2^3) with 8. unfold ASHOFF, FAKESZ in *.
      clear - Hx FFA1 FFA2 FA8 F64 SPAB. Z.div_mod_to_equations. lia. }
    assert (WM03 : wmono bsegs m m3) by exact (wmono_trans _ _ _ _ WM1 (wmono_trans _ _ _ _ WM2 WM3)).
    assert (AH3 : AHEAP AI L RNG st (FB0 FF :: LB) m3).
    { eapply (AI_frame AI); [exact AH2| exact MU3| exact WM3|].
      constructor; [cbn [fst snd]; eapply fk_acr_frame; [left; reflexivity | clear; lia | clear; lia]|].
      constructor; [cbn [fst snd] |].
      { replace (Z.shiftr FF 3 + SHB + 8 - (Z.shiftr FF 3 + SHB)) with 8 by (clear; lia). replace (Z.shiftr FF 3 + SHB) with (shad FF) by (unfold shad, ASHOFF; clear; lia).
        eapply (fk_acr_fshadow AI _ 0 FF 64 FF 8); [left; reflexivity | clear; lia | clear; lia | clear - F64; Z.div_mod_to_equations; lia | clear - FL; lia]. }
      constructor; [cbn [fst snd]; left; left; cbn; unfold KEND in SPK; clear - BOT LOS SPAB SPK; lia| constructor]. }
    (* [comment removed for export] *)
    assert (D3 : forall X n, (X + n <= FF \/ FF + 64 <= X) -> ((6443008 <= X /\ X + n <= 2147446784) \/ (17594333495296 <= X /\ X + n <= ATOP)) -> (X + n <= lo \/ SPV <= X) -> 0 <= n ->
                 disjoint_from [(FF, FF + 24); (Z.shiftr FF 3 + SHB, Z.shiftr FF 3 + SHB + 8); (HSPA SPV + 80, HSPA SPV + 88)] X n).
    { intros X nn HF HB HS Hn. cbn [disjoint_from]. split; [clear - HF Hn; lia|]. split; [clear - HB BSF ATR Hn; lia|]. split; [clear - HS Hn SPAB LOS; lia| exact I]. }
    assert (D3s : forall X n, lo <= X -> X + n <= SPV -> (X + n <= HSPA SPV + 80 \/ HSPA SPV + 88 <= X) -> 0 <= n ->
                 disjoint_from [(FF, FF + 24); (Z.shiftr FF 3 + SHB, Z.shiftr FF 3 + SHB + 8); (HSPA SPV + 80, HSPA SPV + 88)] X n).
    { intros X nn A B C Hn. cbn [disjoint_from]. unfold KHIGH in KHI. split; [clear - A B Hn FHc LOC; lia|]. split; [clear - A B Hn BSF KHI; lia|]. split; [exact C| exact I]. }
    assert (DS3 : forall X n, 0 <= X -> 0 <= n -> X + n <= 2^47 -> (X + n <= FF \/ FF + 64 <= X) ->
                 disjoint_from [(FF, FF + 24); (Z.shiftr FF 3 + SHB, Z.shiftr FF 3 + SHB + 8); (HSPA SPV + 80, HSPA SPV + 88)] (shad X) (shad (X + n - 1) + 1 - shad X)).
    { intros X nn X0 Hn Hb HF. cbn [disjoint_from]. rewrite !shad_div. rewrite Z.shiftr_div_pow2 by (clear; lia). change (2^3) with 8. unfold ASHOFF in *.
      split; [clear - X0 Hn Hb FL ATR; Z.div_mod_to_equations; lia|].
      split; [clear - X0 Hn Hb HF F64; Z.div_mod_to_equations; lia|].
      split; [left; clear - X0 Hn Hb ATR BOT LOS SPAB; Z.div_mod_to_equations; lia| exact I]. }
    assert (INLB : forall b, In b LB -> In b (FB0 FF :: LB)) by (intros b Hb; right; exact Hb).
    assert (SAV3 : rw_cells bsegs m3 (SPV + -104) (FSAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
    { eapply rw_cells_transport; [exact SAV2| exact MU3| exact WM3| unfold FSAVED; cbn; apply D3s; clear - SPAB LOS BOT; lia]. }
    assert (STL3 : stk bsegs m3 lo (HSPA SPV)).
    { eapply stk_transport_disjoint; [exact ST2| exact MU3| exact WM3| apply D3s; clear - SPAB LOS BOT LO0; lia]. }
    assert (STG3 : stk bsegs m3 (HSPA SPV + 88) (SPV + -104)).
    { eapply stk_transport_disjoint; [exact STG2| exact MU3| exact WM3| apply D3s; clear - SPAB LOS BOT; lia]. }
    assert (PT3 : rw_cells bsegs m3 DCTX [C8 llt; C8 mlt; C8 oft; C8 huf]) by (eapply rw_cells_transport; [exact PT2| exact MU3| exact WM3| cbn; apply D3; [clear - DCAP; lia| clear - DL; lia| clear - S_DC; lia| clear; lia]]).
    assert (H1C3 : rw_cells bsegs m3 (DCTX + 29888) [C8 pde; C8 (Z_to_bv 64 PFX); C8 (Z_to_bv 64 PFX); C8 (Z_to_bv 64 0); C8 expd]) by (eapply rw_cells_transport; [exact H1C2| exact MU3| exact WM3| cbn; apply D3; [clear - DCAP; lia| clear - DL; lia| clear - S_DC; lia| clear; lia]]).
    assert (FPC3 : rw_cells bsegs m3 (DCTX + 29928) (zfh_cells h)) by (eapply rw_cells_transport; [exact FPC2| exact MU3| exact WM3| unfold zfh_cells; cbn; apply D3; [clear - DCAP; lia| clear - DL; lia| clear - S_DC; lia| clear; lia]]).
    assert (H3C3 : rw_cells bsegs m3 (DCTX + 29976) [C8 pcs; C8 dsz; C4 bt; C4 stg; C4 le; C4 fe]) by (eapply rw_cells_transport; [exact H3C2| exact MU3| exact WM3| cbn; apply D3; [clear - DCAP; lia| clear - DL; lia| clear - S_DC; lia| clear; lia]]).
    assert (H5C3 : rw_cells bsegs m3 (DCTX + 30096) (h5_cells ws)) by (eapply rw_cells_transport; [exact H5C2| exact MU3| exact WM3| rewrite (h5_cells_size _ H5L); apply D3; [clear - DCAP; lia| clear - DL; lia| clear - S_DC; lia| clear; lia]]).
    assert (OW13 : stk bsegs m3 (DCTX + 32) (DCTX + 29888)) by (eapply stk_transport_disjoint; [exact OW12| exact MU3| exact WM3| apply D3; [clear - DCAP; lia| clear - DL; lia| clear - S_DC; lia| clear; lia]]).
    assert (OW23 : stk bsegs m3 (DCTX + 30372) (DCTX + 95940)) by (eapply stk_transport_disjoint; [exact OW22| exact MU3| exact WM3| apply D3; [clear - DCAP; lia| clear - DL; lia| clear - S_DC; lia| clear; lia]]).
    destruct (stk_split bsegs m3 (DCTX + 32) (DCTX + 10296) (DCTX + 29888) OW13 ltac:(clear; lia)) as [ESEQ3 OR1].
    destruct (stk_split bsegs m3 (DCTX + 10296) (DCTX + 26684) (DCTX + 29888) OR1 ltac:(clear; lia)) as [EHUF3 OR2].
    destruct (stk_split bsegs m3 (DCTX + 26684) (DCTX + 27324) (DCTX + 29888) OR2 ltac:(clear; lia)) as [EREP3 OR3].
    destruct (stk_split bsegs m3 (DCTX + 27324) (DCTX + 29884) (DCTX + 29888) OR3 ltac:(clear; lia)) as [EWK3 EPAD3]. clear OR1 OR2 OR3.
    assert (SB3 : bytes_at bsegs m3 SRC (map (Z_to_bv 8) src)).
    { destruct (Z_lt_ge_dec 0 (zlen src)) as [NZ|Hz].
      - destruct (NZB NZ) as (SBK & US0 & RS1 & RS2 & IB). pose proof (fk_ablk_lits _ _ SBK) as SL.
        eapply bytes_at_transport; [| exact MU3| rewrite length_map; apply D3; [exact (SRCAP NZ)| exact SL| exact S_SR| clear; lia]].
        eapply (fk_bytes_pres AI); [exact HPR2| rewrite length_map; exact IB|].
        eapply bytes_at_transport; [exact SB| exact MU1| rewrite length_map; apply D1; [exact S_SR| clear; lia]].
      - destruct SB as (X1 & X2 & X3). split; [exact X1| split; [exact X2| intros j Hj; exfalso; rewrite length_map in Hj; clear - Hj Hz; lia]]. }
    assert (BUF3 : stk bsegs m3 B0 B1).
    { destruct (Z_lt_ge_dec B0 B1) as [HB|HB].
      - destruct (OUTB HB) as (ABb & IBb & BFF). pose proof (fk_ablk_lits _ _ ABb) as BL.
        eapply stk_transport_disjoint; [| exact MU3| exact WM3| apply D3; [clear - BFF; lia| clear - BL; lia| clear - S_B; lia| clear - HB; lia]].
        eapply (db_stk_pres AI); [exact HPR2| exact IBb|].
        eapply stk_transport_disjoint; [exact BUF| exact MU1| exact WM1| apply D1; [clear - S_B; lia| clear - HB; lia]].
      - pose proof BUF as (B00 & B11 & _). replace B1 with B0 in B11 |- * by (clear - HB B0D DCB CAP0; lia). apply (stk_empty bsegs). clear - B00 B11. lia. }
    assert (UD3 : unpoisoned m3 DCTX (DCTX + 95992)).
    { eapply unpoisoned_munch; [exact UD2| exact MU3| apply DS3; [clear - DL; lia| clear; lia| clear - DL ATR; lia| exact DCAP]]. }
    assert (US3 : 0 < zlen src -> unpoisoned m3 SRC (SRC + zlen src)).
    { intros NZ. destruct (NZB NZ) as (SBK & US0 & RS1 & RS2 & IB). pose proof (fk_ablk_lits _ _ SBK) as SL.
      eapply unpoisoned_munch; [| exact MU3| apply DS3; [clear - SL; lia| clear - NZ; lia| clear - SL ATR; lia| exact (SRCAP NZ)]].
      eapply (fk_unp_pres AI); [exact AH2| exact INLB| exact HPR2| exact IB| clear - NZ; lia|].
      eapply unpoisoned_munch; [exact US0| exact MU1| apply DS1; clear - SL ATR NZ; lia]. }
    assert (UB3 : B0 < B1 -> unpoisoned m3 B0 B1).
    { intros HB. destruct (OUTB HB) as (ABb & IBb & BFF). pose proof (fk_ablk_lits _ _ ABb) as BL.
      destruct (ADST HB) as (ARb & _). destruct (ARb ltac:(clear - HB; lia)) as (_ & UB0 & _). replace (B0 + (B1 - B0)) with B1 in UB0 by (clear; lia).
      replace B1 with (B0 + (B1 - B0)) by (clear; lia).
      eapply unpoisoned_munch; [| exact MU3| apply DS3; [clear - BL; lia| clear - HB; lia| clear - BL ATR; lia| clear - BFF; lia]].
      eapply (fk_unp_pres AI); [exact AH2| exact INLB| exact HPR2| exact IBb| clear - HB; lia|].
      eapply unpoisoned_munch; [replace (B0 + (B1 - B0)) with B1 by (clear; lia); exact UB0| exact MU1| apply DS1; clear - BL ATR HB; lia]. }
    assert (DSTB : (0 < CAP /\ ((6443008 <= DST /\ DST + CAP <= 2147446784) \/ (17594333495296 <= DST /\ DST + CAP <= ATOP))) \/ CAP = 0).
    { destruct (Z_lt_le_dec 0 CAP) as [HC|HC]; [left| right; clear - HC CAP0; lia].
      assert (HB : B0 < B1) by (clear - HC B0D DCB; lia). destruct (OUTB HB) as (ABb & _). pose proof (fk_ablk_lits _ _ ABb) as BL. clear - HC BL B0D DCB; lia. }
    assert (ARO3 : aro_client RNG m3).
    { (* [comment removed for export] *)
      assert (MU03' : munch ((if 0 <? CAP then [(DST, DST + CAP)] else []) ++ [(DCTX, DCTX + 29888); (DCTX + 30000, DCTX + 30008); (DCTX + 30096, DCTX + 95940); (SPV - 6384, SPV)] ++ fake_area L) m m3).
      { eapply munch_weaken; [| exact MU03]. unfold sub_fp; cbn [outside app]; intros x Hx.
        destruct (Z.ltb_spec 0 CAP) as [HC|HC]; cbn [app outside] in Hx; [exact Hx| split; [clear - HC CAP0; lia| exact Hx]]. }
      eapply aro_client_transport_gen; [exact WM03 | exact ARO | exact MU03' |]. intros A n HIn.
      destruct (aclient_bounds A n HIn) as (Q1 & Q2 & Q3). destruct LY5 as (_ & _ & FA1 & FA2).
      destruct (Z.ltb_spec 0 CAP) as [HC|HC]; cbn [disjoint_from app fake_area]; rewrite !shad_div; unfold ASHOFF, AIMG_HI, FAKESZ in *;
        [clear - Q1 Q2 Q3 DL DSTB HC FA1 FA2 FABL ATR BOT LOS| clear - Q1 Q2 Q3 DL FA1 FA2 FABL ATR BOT LOS]; repeat split; Z.div_mod_to_equations; lia. }
    assert (AZS3 : azstk RNG m3 lo SPV).
    { assert (AZS1 : azstk RNG m1 lo SPV).
      { eapply azstk_transport; [exact AZS| exact MU1| exact WM1| | clear - LOS; lia]. apply Forall_cons; [cbn [fst snd]; unfold KLOW, KHIGH; unfold KHIGH in KHI; clear - KHI LOS; lia| apply Forall_nil]. }
      assert (AZS2 : azstk RNG m2 lo SPV).
      { eapply (azstk_transport_F RNG m1 m2 [(HSPA SPV - SMK_STACK, HSPA SPV)] L); [exact AZS1| | exact WM2| | exact FAB| exact FA8| clear - FABL BOT; lia| clear - LOS; lia].
        - eapply munch_weaken; [| exact MUF2]. unfold sub_fp. intros x Hx. apply (proj1 (fk_outside_app _ _ _)) in Hx. destruct Hx as [Hx1 Hx2]. apply (proj2 (fk_outside_app _ _ _)). split; [exact Hx2| exact Hx1].
        - apply Forall_cons; [cbn [fst snd]; unfold KLOW, KHIGH, SMK_STACK; unfold KHIGH in KHI; clear - KHI LOS SPAB; lia| apply Forall_nil]. }
      destruct AZS2 as (RLOz & RHIz & Uz & Hz & W0z & ABz & Rz). exists RLOz, RHIz.
      split; [| split; [exact Hz| split; [eapply wr_at_transport; [exact W0z| exact WM3]| split; [exact ABz| exact Rz]]]].
      eapply unpoisoned_munch; [exact Uz| exact MU3|]. cbn [disjoint_from]. rewrite !shad_div. rewrite Z.shiftr_div_pow2 by (clear; lia). change (2^3) with 8. unfold ASHOFF.
      unfold KHIGH in KHI. clear - KHI LOS BOT SPH SPAB FL FHc ATR. repeat split; Z.div_mod_to_equations; lia. }
    pose proof (fk_ahull_pres _ _ _ _ _ WM03 AHD) as AHD3.
    assert (DB3 : AZ_dblock_a.DBB AI L RNG st LB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m SPV (HSPA SPV) lo DCTX DST CAP B0 B1 PFX SRC src h pde expd pcs dsz bt stg FF llt mlt oft huf le fe ws m3).
    { unfold AZ_dblock_a.DBB, dctx_ptrs, dctx_h1, dctx_h3, dctx_h5.
      split; [exact PT3|]. split; [exact H1C3|]. split; [exact FPC3|]. split; [exact H3C3|]. split; [exact (conj H5C3 H5L)|].
      split; [exact ESEQ3|]. split; [exact EHUF3|]. split; [exact EREP3|]. split; [exact EWK3|]. split; [exact EPAD3|]. split; [exact OW23|].
      split; [exact SB3|]. split; [exact BUF3|]. split; [exact STL3|]. split; [exact SAV3|]. split; [exact STG3|]. split; [exact MI3|].
      split; [exact AH3|]. split; [exact FFR03|]. split; [exact MU03|]. split; [exact WM03|].
      split; [exact UD3|]. split; [exact US3|]. split; [exact UB3|]. split; [exact ARO3|]. split; [exact AZS3|]. split; [exact AHD3|].
      split; [intros NZ; exact (fk_ahull_pres _ _ _ _ _ WM03 (AHS NZ))| intros HB; destruct (ADST HB) as (_ & AHb & _); exact (fk_ahull_pres _ _ _ _ _ WM03 AHb)]. }
    (* [comment removed for export] *)
    apply (rw_cells_split_CB bsegs _ _ [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x1d28b); C8 (Z_to_bv 64 0x89360)] 32 junk [C8 (Z_to_bv 64 (fflag L 0 FF))] [8; 12; 12]%nat) in FFC3; [| reflexivity].
    cbn [mk_CB_cells app] in FFC3.
    pose proof (proj1 (rw_cells_app bsegs _ _ [C8 (Z_to_bv 64 0x41b58ab3)] _) FFC3) as [XM3 XR1].
    pose proof (proj1 (rw_cells_app bsegs _ _ [C8 (Z_to_bv 64 0x1d28b); C8 (Z_to_bv 64 0x89360); CB 8 (firstn 8 junk)] _) XR1) as [_ XR2].
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul] in XR2.
    match type of XR2 with rw_cells _ _ ?a _ => replace a with (FF + 32) in XR2 by (clear; lia) end.
    pose proof (proj1 (rw_cells_app bsegs _ _ [CB 12 (firstn 12 (skipn 8 junk))] _) XR2) as [XNc XR3].
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul] in XR3.
    match type of XR3 with rw_cells _ _ ?a _ => replace a with (FF + 44) in XR3 by (clear; lia) end.
    pose proof (proj1 (rw_cells_app bsegs _ _ [CB 12 (firstn 12 (skipn 12 (skipn 8 junk)))] _) XR3) as [_ XP3].
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul] in XP3.
    match type of XP3 with rw_cells _ _ ?a _ => replace a with (FF + 56) in XP3 by (clear; lia) end.
    destruct (AZ_dblock_f.db_cb12_as_c4s m3 _ _ XNc) as (nbw & nb1 & nb2 & XN12).
    pose proof (proj1 (rw_cells_app bsegs _ _ [C4 nbw] _) XN12) as [XN3 _].
    clear XR1 XR2 XR3 XNc XN12 FFC3.
    assert (TB3 : atbl HUFINVw m3 DCTX llt mlt oft huf le fe).
    { eapply (atbl_frame HUFINVw hufw_frame); [exact TB2| exact MU3| exact MI2| exact MI3|]. intros x Hx. cbn [outside].
      clear - Hx DCAP DL BSF ATR S_DC LOS SPAB. repeat split; lia. }
    (* [comment removed for export] *)
    pose proof (AZ_dblock_g.p_long AI fflag rng_fs L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m SPV (HSPA SPV) lo DCTX DST CAP B0 B1 PFX SRC src ip cbs h pde expd pcs dsz bt stg ws
                  FF (Z.shiftr FF 3 + SHB) (fflag L 0 FF) CTX3 FHL FFLAG FREL SEQL) as PLONG.
    pose proof (AZ_dblock_h.p_norm AI fflag rng_fs L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m SPV (HSPA SPV) lo DCTX DST CAP B0 B1 PFX SRC src ip cbs h pde expd pcs dsz bt stg ws
                  FF (Z.shiftr FF 3 + SHB) (fflag L 0 FF) CTX3 FHL FFLAG FREL SEQD SEQS SEQL OFFINFO) as PNORM.
    pose proof (AZ_dblock_e.p_ok AI fflag rng_fs L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m SPV (HSPA SPV) lo DCTX DST CAP B0 B1 PFX SRC src ip cbs h pde expd pcs dsz bt stg ws
                  FF (Z.shiftr FF 3 + SHB) (fflag L 0 FF) CTX3 FHL OFFINFO SEQD SEQS SEQL PLONG PNORM) as POK.
    pose proof (AZ_dblock_d.p_seq AI fflag rng_fs L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m SPV (HSPA SPV) lo DCTX DST CAP B0 B1 PFX SRC src ip cbs h pde expd pcs dsz bt stg ws
                  FF (Z.shiftr FF 3 + SHB) (fflag L 0 FF) CTX3 FHL FFLAG FREL OFFINFO SEQD SEQS SEQL POK) as PSH.
    pose proof (AZ_dblock_c.p_lit AI fflag rng_fs L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m SPV (HSPA SPV) lo DCTX DST CAP B0 B1 PFX SRC src ip cbs h pde expd pcs dsz bt stg ws
                  FF (Z.shiftr FF 3 + SHB) (fflag L 0 FF) CTX3 FHL FFLAG FREL SEQHDR PSH) as PDL.
    eapply (AZ_dblock_b.p_top AI fflag rng_fs L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m SPV (HSPA SPV) lo DCTX DST CAP B0 B1 PFX SRC src ip cbs h pde expd pcs dsz bt stg ws
              FF (Z.shiftr FF 3 + SHB) (fflag L 0 FF) CTX3 FHL FFLAG FREL DECLIT PDL m3 llt mlt oft huf le fe jA jB' (Z_to_bv 64 0x41b58ab3) nbw);
      [exact DB3| exact FRA3| exact XM3| exact XN3| exact XP3| exact XS3| exact TB3].
  Qed.
End Thm.
End CANSEC1.
