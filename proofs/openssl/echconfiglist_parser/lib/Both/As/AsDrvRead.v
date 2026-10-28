(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes AgentLib SReach HeapCeil Frame FileSim RefNodes SymDriveX
  SymExec2 SymExec2Sound RegsEquivM MainEqv MemSplit MainMem LazyRestrict LazySR LazyFdNodes StreamSim StoreOk.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import WsegFast.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Mem Cells Arr Step Frame MState SysStep Exec CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsCXXHeap AsDriverLaws AsDrvHeap AsDrvRun AsDrvOpen
  AsDrvMem N9_read.
Import OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.PropExec.
Import ListNotations.
Import SymExec2.SX2. Import SymExec2Sound.SX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.

Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma AECALL : fetch_word asegs (Z_to_bv 64 AREAD_ECALL) = Some ECALLW.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma amem_inv_wbytes_data : forall m (A : Z) bs,
  mem_inv asegs m -> 0x571000 <= A -> A < 2 ^ 64 -> A + Z.of_nat (length bs) <= 2 ^ 64 ->
  mem_inv asegs (wbytes m (Z_to_bv 64 A) bs).
Proof.
  intros m A bs Hinv HA HA64 Hl a b Hab. pose proof (u64_range a) as Ha.
  destruct (Z_lt_le_dec (bv_unsigned a) A) as [Hlt|Hge].
  - rewrite wbytes_below in Hab by (rewrite ?u_small by lia; lia). exact (Hinv a b Hab).
  - destruct (Z_lt_le_dec (bv_unsigned a) (A + Z.of_nat (length bs))) as [Hin|Hout].
    + apply aro_addr_false. lia.
    + rewrite wbytes_above in Hab by (rewrite u_small by lia; lia). exact (Hinv a b Hab).
Qed.

Section DrvRead.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Hypothesis DL : asan_driver_laws H.

  Let rom := seg_rom asegs.

  (* [comment removed for export] *)
  Lemma awseg_stage : wseg_ok RSEGS (0xbccf50 : word) 65536%nat = true.
  Proof. apply wseg_fast_ok. vm_compute. reflexivity. Qed.   (* [comment removed for export] *)

  Lemma store_ok_stage : forall m (a : word) n,
    0xbccf50 <= bv_unsigned a -> bv_unsigned a + Z.of_nat n <= 0xbdcf50 -> store_ok RSEGS m a n = true.
  Proof.
    intros m a n Hlo Hhi.
    eapply (store_ok_window RSEGS m (0xbccf50 : word) a 65536%nat n 0xbccf50 0xbdcf50);
      [reflexivity | reflexivity | lia | exact awseg_stage | exact Hlo | exact Hhi].
  Qed.

  Lemma mkR_of_upd10 : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 v,
    mkR_of (regupd (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) 10 v)
    = mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 v x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
  Proof.
    intros. rewrite mkR_of_getr. rewrite getr_same by (intros E; apply (f_equal bv_unsigned) in E; discriminate).
    rewrite !getr_other by (intros E; apply (f_equal bv_unsigned) in E; discriminate). rewrite !getr_mkR. reflexivity.
  Qed.

  Lemma aconst_ok_stage : aconst_ok (AREAD_STAGE, (AREAD_STAGE + 65536)%Z).
  Proof.
    apply aconst_ok_intro; unfold AREAD_STAGE, ASHBASE_CELL, AMEMCPYP_CELL, AINITED_CELL, AHIEND_CELL, ADYING_CELL, APGSZ_CELL,
      ACANPOISON_CELL, AF_DCO_CELL, AVERBOSITY_CELL, AREAL_TLSGA_CELL, ATSD_CELL, AREGISTERED_CELL, ACOVFLAG_CELL, sh, AIMG_LO, AIMG_TOP in *;
      rewrite ?ASHADOW_BASE_val; try lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma aread_stage_file : forall s msF mo regs mem (fd cnt lo : Z) (p : list byte) (off : word) (data : list byte) (ra : Z) K,
    as_VIS H s msF = mkst regs (Z_to_bv 64 AREAD_STUB) mem rom -> as_AKREL H s (mkCfg msF mo) ->
    getr regs 1 = Z_to_bv 64 ra -> 0 <= ra < 2 ^ 64 -> ra mod 2 = 0 ->
    getr regs 4 = Z_to_bv 64 ATP ->
    getr regs 10 = Z_to_bv 64 fd -> getr regs 11 = Z_to_bv 64 AREAD_STAGE -> getr regs 12 = Z_to_bv 64 cnt ->
    0 <= fd < 2 ^ 32 -> 1 <= cnt <= 65536 ->
    stk asegs mem lo (bv_unsigned (getr regs 2)) -> aceil <= lo -> lo <= bv_unsigned (getr regs 2) - AREAD_STACK ->
    mem_inv asegs mem -> ACONST mem ->
    fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdFile p off) -> fs_lookup (m_fs mo) p = Some data ->
    let bs := file_read data off (Z_to_bv 64 cnt) in
    (forall regs' mem' msF' mo',
       as_VIS H s msF' = mkst regs' (Z_to_bv 64 ra) mem' rom -> as_AKREL H s (mkCfg msF' mo') ->
       (forall r, In r aheap_kept -> getr regs' r = getr regs r) -> getr regs' 10 = len_word bs ->
       munch [(AREAD_STAGE, AREAD_STAGE + 65536); (bv_unsigned (getr regs 2) - AREAD_STACK, bv_unsigned (getr regs 2))] mem mem' ->
       wmono asegs mem mem' -> mem_inv asegs mem' -> stk asegs mem' lo (bv_unsigned (getr regs 2)) -> ACONST mem' ->
       rdn RSEGS mem' (Z_to_bv 64 AREAD_STAGE) (length bs) = Some bs ->
       m_fs mo' = m_fs mo -> m_fds mo' = fd_insert (m_fds mo) (Z_to_bv 64 fd) (FdFile p (off + len_word bs)%bv) ->
       realizes asegs (mkCfg msF' mo') K) ->
    realizes asegs (mkCfg msF mo) K.
  Proof.
    intros s msF mo regs mem fd cnt lo p off data ra K HV HA Hra Hra64 Hra2 Htp H10 H11 H12 Hfd Hcnt HSTK HCL HLO HINV HAC Hlk Hfs bs HK.
    pose proof (u64_range (getr regs 2)) as Hsp. acb. pose proof HLO as HLO'. unfold AREAD_STACK in HLO'.
    eapply (aevt_call H HH DL _ s msF mo regs _ mem K HV HA).
    { rewrite mkR_of_getr, Hra, Htp, H10, H11, H12.
      eapply aread_pre with (lo := lo) (fd := fd) (buf := AREAD_STAGE) (cnt := cnt);
        [ exact HCL | exact HLO | lia | reflexivity | reflexivity | reflexivity | exact HSTK | exact HINV | exact HAC
        | exact (proj1 (proj2 (ACONST_drv_reals mem HAC))) ]. }
    intros msF1 mo1 HA1 MP1 HP1.
    destruct HP1 as (m1 & fj & fj2 & HV1 & MU1 & WM1 & INV1 & STK1 & FR1 & FRJ1 & FRM1 & AC1 & RRD1).
    (* [comment removed for export] *)
    unfold read_at in HV1. change (MS ?R ?F ?pc ?fc None ?m ?ro) with (mkst R pc m ro) in HV1.
    set (R1 := mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) in HV1.
    assert (G10 : getr R1 10 = Z_to_bv 64 fd) by (subst R1; rewrite getr_mkR; reflexivity).
    assert (G11 : getr R1 11 = Z_to_bv 64 AREAD_STAGE) by (subst R1; rewrite getr_mkR; reflexivity).
    assert (G12 : getr R1 12 = Z_to_bv 64 cnt) by (subst R1; rewrite getr_mkR; reflexivity).
    assert (G17 : getr R1 17 = Z_to_bv 64 63) by (subst R1; rewrite getr_mkR; reflexivity).
    eapply (drv_read_file H DL s msF1 R1 (Z_to_bv 64 AREAD_ECALL) m1 mo1 ECALLW (Z_to_bv 64 fd) p off data cnt K AECALL is_ecall_ECALLW HV1 HA1 G17 G10);
      [ rewrite u_small by lia; lia
      | destruct (adl_mpres H DL _ _ MP1) as (_ & E & _); rewrite E; exact Hlk
      | rewrite (proj1 (adl_mpres H DL _ _ MP1)); exact Hfs
      | exact G12
      | lia | unfold MAX_RW_COUNT; lia | lia
      | rewrite G11, u_small by (unfold AREAD_STAGE; lia); unfold AREAD_STAGE, TASK_SIZE; lia
      | | ].
    { rewrite G11. apply store_ok_stage; rewrite u_small by (unfold AREAD_STAGE; lia); unfold AREAD_STAGE; lia. }
    cbv zeta. rewrite G11, G12. fold bs. intros msF2 mo2 HV2 HA2 SB2.
    (* [comment removed for export] *)
    set (m2 := wbytes m1 (Z_to_bv 64 AREAD_STAGE) bs) in HV2.
    assert (Lbs : Z.of_nat (length bs) <= cnt).
    { subst bs. pose proof (proj1 (file_read_length_le data off (Z_to_bv 64 cnt))) as FL. unfold word_to_nat in FL. rewrite u_small in FL by lia. lia. }
    assert (MU2 : munch [(AREAD_STAGE, AREAD_STAGE + 65536)]%Z m1 m2).
    { subst m2. rewrite MainMem.wbytes_eq. replace (Z_to_bv 64 AREAD_STAGE) with (wa AREAD_STAGE) by reflexivity.
      apply munch_write; [apply munch_refl | unfold AREAD_STAGE; lia | unfold AREAD_STAGE; lia | cbn; left; unfold AREAD_STAGE; lia]. }
    assert (WM2 : wmono asegs m1 m2) by (subst m2; rewrite MainMem.wbytes_eq; apply wmono_write; apply wmono_refl).
    assert (INV2 : mem_inv asegs m2) by (subst m2; apply amem_inv_wbytes_data; [exact INV1 | unfold AREAD_STAGE; lia | unfold AREAD_STAGE; lia | unfold AREAD_STAGE; lia]).
    assert (STK2 : stk asegs m2 lo (bv_unsigned (getr regs 2) + -2144)).
    { subst m2. rewrite MainMem.wbytes_eq. replace (Z_to_bv 64 AREAD_STAGE) with (wa AREAD_STAGE) by reflexivity.
      apply stk_write; [exact STK1 | unfold AREAD_STAGE; lia | unfold AREAD_STAGE; lia]. }
    assert (AC2 : ACONST m2).
    { eapply ACONST_frame; [exact AC1 | exact MU2 | exact WM2 |]. constructor; [apply aconst_ok_stage | constructor]. }
    assert (DJ : forall a n, aceil <= a -> disjoint_from [(AREAD_STAGE, AREAD_STAGE + 65536)]%Z a n).
    { intros a n Ha. cbn. unfold AREAD_STAGE. lia. }
    assert (FR2' : rw_cells asegs m2 (bv_unsigned (getr regs 2) + -48) [C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8); C8 (Z_to_bv 64 ra)]).
    { eapply rw_cells_transport; [exact FR1 | exact MU2 | exact WM2 | apply DJ; lia]. }
    assert (FRJ2 : rw_cells asegs m2 (bv_unsigned (getr regs 2) + -2128) [CB 2080 fj]).
    { eapply rw_cells_transport; [exact FRJ1 | exact MU2 | exact WM2 | apply DJ; lia]. }
    assert (FRM2 : rw_cells asegs m2 (bv_unsigned (getr regs 2) + -2144) [CB 8 fj2; C8 (Z_to_bv 64 1750696)]).
    { eapply rw_cells_transport; [exact FRM1 | exact MU2 | exact WM2 | apply DJ; lia]. }
    assert (RD2 : rdn RSEGS m2 (Z_to_bv 64 AREAD_STAGE) (length bs) = Some bs).
    { subst m2. apply rdn_wbytes_hit. rewrite u_small by (unfold AREAD_STAGE; lia). unfold AREAD_STAGE; lia. }
    (* [comment removed for export] *)
    assert (FS2 : m_fs mo2 = m_fs mo).
    { rewrite (same_but_materialized_fs _ _ SB2). cbn. exact (proj1 (adl_mpres H DL _ _ MP1)). }
    assert (FDS2 : m_fds mo2 = fd_insert (m_fds mo) (Z_to_bv 64 fd) (FdFile p (off + len_word bs)%bv)).
    { rewrite (same_but_materialized_fds _ _ SB2), with_fds_fds. destruct (adl_mpres H DL _ _ MP1) as (_ & E & _). rewrite E. reflexivity. }
    (* [comment removed for export] *)
    assert (TAIL : forall msF3 mo3 (x10 : word),
      as_AKREL H s (mkCfg msF3 mo3) -> as_MPRES H mo2 mo3 ->
      aread_ret_post (Z_to_bv 64 ra) (getr regs 2) (getr regs 3) (Z_to_bv 64 ATP) (getr regs 8) (getr regs 9)
        (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25)
        (getr regs 26) (getr regs 27) bvmap_empty (Z_to_bv 32 0) lo x10 m2 (as_VIS H s msF3) ->
      x10 = len_word bs ->
      realizes asegs (mkCfg msF3 mo3) K).
    { intros msF3 mo3 x10 HA3 MP3 HP3 Ex10. unfold aread_ret_post in HP3.
      destruct HP3 as (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m3 & HV3 & MU3 & WM3 & INV3 & STK3 & AC3).
      rewrite (ret_pc_even ra Hra64 Hra2) in HV3.
      change (MS ?R ?F ?pc ?fc None ?m ?ro) with (mkst R pc m ro) in HV3.
      apply (HK _ m3 msF3 mo3 HV3 HA3).
      - intros r Hr. unfold aheap_kept in Hr. cbn [In] in Hr.
        destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]];
          rewrite (getr_mkR (Z_to_bv 64 ra)); cbn; first [reflexivity | symmetry; exact Htp].
      - rewrite (getr_mkR (Z_to_bv 64 ra)). cbn. exact Ex10.
      - intros x Hx. cbn in Hx. unfold AREAD_STACK, AREAD_STAGE in *.
        rewrite (MU3 x) by (cbn; lia). rewrite (MU2 x) by (cbn; lia). apply MU1. cbn. lia.
      - eapply wmono_trans; [exact WM1 | eapply wmono_trans; [exact WM2 | exact WM3]].
      - exact INV3.
      - exact STK3.
      - exact AC3.
      - rewrite (rdn_ext RSEGS (length bs) m3 m2); [exact RD2 | rewrite u_small by (unfold AREAD_STAGE; lia); unfold AREAD_STAGE; lia |].
        intros x Hx. rewrite u_small in Hx by (unfold AREAD_STAGE; lia). apply MU3. cbn. unfold AREAD_STAGE in Hx. lia.
      - rewrite (proj1 (adl_mpres H DL _ _ MP3)). exact FS2.
      - destruct (adl_mpres H DL _ _ MP3) as (_ & E' & _). rewrite E'. exact FDS2. }
    (* [comment removed for export] *)
    rewrite AgentLib.v_addi_lit in HV2 by (unfold AREAD_ECALL; lia).
    destruct (Nat.eq_dec (length bs) 0) as [L0|Lp].
    - eapply (aevt_call H HH DL _ s msF2 mo2 _ _ m2 K HV2 HA2).
      { subst R1. rewrite mkR_of_upd10, len_word_of_nat, L0. change (Z.of_nat 0) with 0.
        eapply aread_post_zero;
          [ exact HLO | lia | exact INV2 | exact STK2 | exact FR2' | exact FRJ2 | exact FRM2 | exact AC2 ]. }
      intros msF3 mo3 HA3 MP3 HP3. eapply (TAIL msF3 mo3 _ HA3 MP3 HP3). rewrite len_word_of_nat, L0. reflexivity.
    - eapply (aevt_call H HH DL _ s msF2 mo2 _ _ m2 K HV2 HA2).
      { subst R1. rewrite mkR_of_upd10, len_word_of_nat.
        eapply aread_post_pos;
          [ exact HCL | exact HLO | lia | unfold AREAD_STAGE; lia | unfold AREAD_STAGE, AAPP_HI; lia
          | exact INV2 | exact STK2 | exact FR2' | exact FRJ2 | exact FRM2 | exact AC2
          | lia | lia
          | eapply addressable_accessible; [apply ACONST_read_stage; exact AC2 | lia | lia | unfold AREAD_STAGE, AAPP_HI; lia]
          | apply ACONST_shvis; [exact AC2 | unfold AREAD_STAGE, AIMG_LO; lia | lia | unfold AREAD_STAGE, AIMG_TOP; lia]
          | left; unfold AREAD_STAGE; rewrite ASHADOW_BASE_val; lia ]. }
      intros msF3 mo3 HA3 MP3 HP3. eapply (TAIL msF3 mo3 _ HA3 MP3 HP3). rewrite len_word_of_nat. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma aread_stage_dir : forall s msF mo regs mem (fd cnt lo : Z) (errv : word) (ra : Z) K,
    as_VIS H s msF = mkst regs (Z_to_bv 64 AREAD_STUB) mem rom -> as_AKREL H s (mkCfg msF mo) ->
    getr regs 1 = Z_to_bv 64 ra -> 0 <= ra < 2 ^ 64 -> ra mod 2 = 0 ->
    getr regs 4 = Z_to_bv 64 ATP ->
    getr regs 10 = Z_to_bv 64 fd -> getr regs 11 = Z_to_bv 64 AREAD_STAGE -> getr regs 12 = Z_to_bv 64 cnt ->
    0 <= fd < 2 ^ 32 -> 1 <= cnt <= 65536 ->
    stk asegs mem lo (bv_unsigned (getr regs 2)) -> aceil <= lo -> lo <= bv_unsigned (getr regs 2) - AREAD_STACK ->
    mem_inv asegs mem -> ACONST mem -> rw_cells asegs mem AERRNO [C4 errv] ->
    fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some FdDir ->
    (forall regs' mem' msF' mo',
       as_VIS H s msF' = mkst regs' (Z_to_bv 64 ra) mem' rom -> as_AKREL H s (mkCfg msF' mo') ->
       (forall r, In r aheap_kept -> getr regs' r = getr regs r) -> bv_unsigned (getr regs' 10) = 2 ^ 64 - 1 ->
       munch [(AERRNO, AERRNO + 4); (bv_unsigned (getr regs 2) - AREAD_STACK, bv_unsigned (getr regs 2))] mem mem' ->
       wmono asegs mem mem' -> mem_inv asegs mem' -> stk asegs mem' lo (bv_unsigned (getr regs 2)) -> ACONST mem' ->
       rw_cells asegs mem' AERRNO [C4 (Z_to_bv 64 EISDIR)] ->
       m_fs mo' = m_fs mo -> m_fds mo' = m_fds mo ->
       realizes asegs (mkCfg msF' mo') K) ->
    realizes asegs (mkCfg msF mo) K.
  Proof.
    intros s msF mo regs mem fd cnt lo errv ra K HV HA Hra Hra64 Hra2 Htp H10 H11 H12 Hfd Hcnt HSTK HCL HLO HINV HAC HERR Hlk HK.
    pose proof (u64_range (getr regs 2)) as Hsp. acb. pose proof HLO as HLO'. unfold AREAD_STACK in HLO'.
    (* [comment removed for export] *)
    eapply (aevt_call H HH DL _ s msF mo regs _ mem K HV HA).
    { rewrite mkR_of_getr, Hra, Htp, H10, H11, H12.
      eapply aread_pre with (lo := lo) (fd := fd) (buf := AREAD_STAGE) (cnt := cnt);
        [ exact HCL | exact HLO | lia | reflexivity | reflexivity | reflexivity | exact HSTK | exact HINV | exact HAC
        | exact (proj1 (proj2 (ACONST_drv_reals mem HAC))) ]. }
    intros msF1 mo1 HA1 MP1 HP1.
    destruct HP1 as (m1 & fj & fj2 & HV1 & MU1 & WM1 & INV1 & STK1 & FR1 & FRJ1 & FRM1 & AC1 & RRD1).
    (* [comment removed for export] *)
    unfold read_at in HV1. change (MS ?R ?F ?pc ?fc None ?m ?ro) with (mkst R pc m ro) in HV1.
    set (R1 := mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) in HV1.
    assert (G10 : getr R1 10 = Z_to_bv 64 fd) by (subst R1; rewrite getr_mkR; reflexivity).
    assert (G11 : getr R1 11 = Z_to_bv 64 AREAD_STAGE) by (subst R1; rewrite getr_mkR; reflexivity).
    assert (G12 : getr R1 12 = Z_to_bv 64 cnt) by (subst R1; rewrite getr_mkR; reflexivity).
    assert (G17 : getr R1 17 = Z_to_bv 64 63) by (subst R1; rewrite getr_mkR; reflexivity).
    eapply (drv_read_dir H DL s msF1 R1 (Z_to_bv 64 AREAD_ECALL) m1 mo1 ECALLW (Z_to_bv 64 fd) cnt K AECALL is_ecall_ECALLW HV1 HA1 G17 G10);
      [ rewrite u_small by lia; lia
      | destruct (adl_mpres H DL _ _ MP1) as (_ & E & _); rewrite E; exact Hlk
      | exact G12
      | lia | lia
      | rewrite G11, u_small by (unfold AREAD_STAGE; lia); unfold AREAD_STAGE, TASK_SIZE; lia
      | rewrite G11; apply store_ok_stage; rewrite u_small by (unfold AREAD_STAGE; lia); unfold AREAD_STAGE; lia
      | ].
    intros msF2 HV2 HA2.
    rewrite AgentLib.v_addi_lit in HV2 by (unfold AREAD_ECALL; lia).
    replace (errno_ret EISDIR) with (Z_to_bv 64 (2 ^ 64 - 21)) in HV2 by (apply bv_eq; reflexivity).
    (* [comment removed for export] *)
    assert (ERR1 : rw_cells asegs m1 AERRNO [C4 errv]).
    { eapply rw_cells_transport; [exact HERR | exact MU1 | exact WM1 |]. cbn. unfold AERRNO, ATP. lia. }
    (* [comment removed for export] *)
    eapply (aevt_call H HH DL _ s msF2 mo1 _ _ m1 K HV2 HA2).
    { subst R1. rewrite mkR_of_upd10.
      eapply aread_post_err;
        [ exact HCL | exact HLO | lia | exact INV1 | exact STK1 | exact FR1 | exact FRJ1 | exact FRM1 | exact AC1
        | reflexivity | exact ERR1 | lia ]. }
    intros msF3 mo3 HA3 MP3 HP3. unfold aread_err_post in HP3.
    destruct HP3 as (x5 & x6 & x7 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m3
                     & HV3 & U10 & MU3 & WM3 & INV3 & STK3 & AC3 & ERR3).
    rewrite (ret_pc_even ra Hra64 Hra2) in HV3.
    change (MS ?R ?F ?pc ?fc None ?m ?ro) with (mkst R pc m ro) in HV3.
    apply (HK _ m3 msF3 mo3 HV3 HA3).
    - intros r Hr. unfold aheap_kept in Hr. cbn [In] in Hr.
      destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]];
        rewrite (getr_mkR (Z_to_bv 64 ra)); cbn; first [reflexivity | symmetry; exact Htp].
    - rewrite (getr_mkR (Z_to_bv 64 ra)). cbn. exact U10.
    - intros x Hx. cbn in Hx. unfold AREAD_STACK, AERRNO, ATP in *.
      rewrite (MU3 x) by (cbn; lia). apply MU1. cbn. lia.
    - eapply wmono_trans; [exact WM1 | exact WM3].
    - exact INV3.
    - exact STK3.
    - exact AC3.
    - exact ERR3.
    - rewrite (proj1 (adl_mpres H DL _ _ MP3)). exact (proj1 (adl_mpres H DL _ _ MP1)).
    - destruct (adl_mpres H DL _ _ MP3) as (_ & E3 & _). rewrite E3. destruct (adl_mpres H DL _ _ MP1) as (_ & E1 & _). exact E1.
  Qed.
End DrvRead.
