(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling Arr.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts ATac IcptA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7A0 Require Import ShadowKit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.AW Require Import HttpRepA AWKit AWAuto AWAuto2 FakeKit HObjK HObjF H_scanner_get_token H_vfm_A H_vfm_G H_match_shell.
Import ListNotations.
Open Scope Z_scope.

Notation FMT_RESP_A := 0x218c0%Z.
Notation FMT_CRLF_A := 0x21a40%Z.
Notation FMT_HDR_A := 0x21900%Z.
Notation FMT_REQ09_A := 0x21a60%Z.
Notation FMT_REQ_A := 0x21a80%Z.

Section M.
Context {HC : HasCeiling}.
Hypothesis IC : icpt_contracts.
Variable FI : fs_if.
Hypothesis STACK_MALLOC_0 : stack_malloc_stmt FI 0.
Hypothesis STACK_MALLOC_1 : stack_malloc_stmt FI 1.
Local Notation FSIV W := ((FSB FI, FSB FI + A0_FS_SIZE) :: (sh (FSB FI), sh (FSB FI) + A0_FS_SHSIZE) :: W)%Z.

#[using="Type"] Lemma match_q_facts : forall q, q mod 16 = 0 -> q + -160 <= match_q q <= q + -128 /\ match_q q mod 16 = 0.
Proof. intros q H. unfold match_q. Z.div_mod_to_equations. lia. Qed.

Definition match_resp_postA (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32)
    (st : fsstate FI) (lo S MB A len cap cur0 P1 : Z) (bs : list byte) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (r cur' : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (st' : fsstate FI),
    ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F_ (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch ((lo, q) :: FSIV [(S + 8, S + 16); (P1, P1 + 16)]) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ fkeep FI [(S + 8, S + 16); (P1, P1 + 16)] st m m' /\ fs_live FI st' = fs_live FI st /\ RFAKE FI st' m'
    /\ stk asegs m' lo q /\ asan_env asegs m'
    /\ rw_cells asegs m' S [C8 (wz MB); C8 (wz cur'); C4 (wz 0)]
    /\ 0 <= r <= 5 /\ 0 <= cur' <= len /\ (r = 4 -> cur0 <= cur') /\ (r <> 4 -> cur' = cur0)
    /\ X_respA A len cur0 bs P1 m' r cur'.
#[using="IC STACK_MALLOC_0 STACK_MALLOC_1"] Theorem match_respA : forall (S MB A len cap cur0 P1 lo q : Z) (bs : list byte) (st : fsstate FI) (pw1 pw2 : word)
    (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F_ : bvmap 5 word) (fc : bv 32) (m : mem),
  rw_cells asegs m S [C8 (wz MB); C8 (wz cur0); C4 (wz 0)] ->
  rw_cells asegs m MB (mbuf_cells A len cap) ->
  bytes_at asegs m A bs ->
  rw_cells asegs m P1 [C8 pw1; C8 pw2] ->
  alloc_ceiling <= lo -> lo <= q - 16384 -> q mod 16 = 0 -> q <= 2^47 - 64 ->
  0x609000 <= MB -> MB + 32 <= S -> S + 24 <= alloc_ceiling -> S mod 8 = 0 -> MB mod 8 = 0 ->
  lb (fs_live FI st) MB (S + 24 - MB) ->
  0 <= A -> A + Z.of_nat (length bs) <= alloc_ceiling -> Z.of_nat (length bs) >= len -> len <= cap -> A + cap + 1 < 2^63 ->
  (0 < len -> 0 < A) ->
  0 <= cur0 <= len ->
  (A + Z.of_nat (length bs) <= MB \/ S + 24 <= A) ->
  (A + Z.of_nat (length bs) <= FSB FI \/ FSB FI + A0_FS_SIZE <= A) ->
  (A + Z.of_nat (length bs) <= 0x7fff7000 \/ 0x10007fff8000 <= A) ->
  P1 mod 8 = 0 -> lb (fs_live FI st) P1 16 ->
  (P1 + 16 <= MB \/ S + 24 <= P1) -> (P1 + 16 <= A \/ A + Z.of_nat (length bs) <= P1) ->
  shw m S 24 -> shw m MB 32 -> (0 < len -> shw m A len) -> shw m SEPTAB_A 20 -> shw m P1 16 -> shw m FMT_RESP_A 16 ->
  shz m (sh lo) (sh q) -> shr m (sh lo - sh lo mod 8) (sh q + 8) ->
  stk asegs m lo q -> mem_inv asegs m -> asan_env asegs m -> RFAKE FI st m -> fs_call_ok FI st tp 2 ->
  FSENV FI m ->
  a0 = wz S -> a1 = wz FMT_RESP_A -> a2 = wz P1 ->
  evt asegs (match_resp_postA ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc st lo S MB A len cap cur0 P1 bs m)
      (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz match_entry) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros SC MBC BUF PC1 CLO LO AL16 QHI MBLO MBS SHI SAL MBAL PLB A0 AHI LBS CAP ACAP ANZ CUR0 TXP TFS TBAND PAL PLP PPAR PTXT
    SHS SHMB SHA SHSEP SHP SHFMT SHZ SHR ST MI AE RF FCO FE -> -> ->.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  assert (EQ : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  destruct (match_q_facts q AL16) as [QV QVAL].
  pose (X := fun (m2 : mem) (r : Z) => exists cur', rw_cells asegs m2 S [C8 (wz MB); C8 (wz cur'); C4 (wz 0)]
               /\ 0 <= r <= 5 /\ 0 <= cur' <= len /\ (r = 4 -> cur0 <= cur') /\ (r <> 4 -> cur' = cur0) /\ X_respA A len cur0 bs P1 m2 r cur').
  eapply evt_mono.
  { eapply (match_shell_A FI STACK_MALLOC_0 st [(S + 8, S + 16); (P1, P1 + 16)] lo S FMT_RESP_A X) with (sp := wz q); rewrite ?EQ.
    3: exact ST. 3: exact CLO. 3: lia. 3: exact AL16. 3: exact MI. 3: exact AE. 3: exact RF. 3: exact FCO. 3: exact FE.
    3: { cbn [disjoint_from]. pose proof (fsb_ok FI) as (B1 & B2 & _). destruct (lb_in_fs FI st m RF _ _ PLP) as [H1 H2]. repeat split; lia. }

    all: try (destruct (new_frame_facts FI st 0 m (fs_F FI st 0) (sh (fs_F FI st 0)) (fs_FL FI st 0) RF ltac:(lia) eq_refl eq_refl eq_refl) as (FCLS & FLO & FHI & FAL & FLLO & FLHI & APART);
              cbn [FB_of SB_of] in FHI, APART;
              assert (PC8 : lb (fs_live FI st) S 24) by (apply (Contracts.lb_sub _ _ _ _ _ PLB); lia);
              assert (SHF1 : sh (FSB FI) <= sh (fs_F FI st 0) /\ sh (fs_F FI st 0) + 8 <= sh (FSB FI) + A0_FS_SHSIZE)
                by (pose proof (fsb_ok FI) as (B1 & B2 & _ & B4 & _); unfold sh, SHADOW_OFF; clear - FLO FHI B4; Z.div_mod_to_equations; lia);
              pose proof (lb_apart_frame _ _ _ (fs_F FI st 0) 64 _ _ PC8 APART) as Q1; pose proof (lb_apart_frame _ _ _ (fs_F FI st 0) 64 _ _ PLP APART) as Q2;
              pose proof (lb_apart_shadow FI st m _ _ (sh (fs_F FI st 0)) 8 RF PC8 ltac:(lia) ltac:(lia)) as Q3;
              pose proof (lb_apart_shadow FI st m _ _ (sh (fs_F FI st 0)) 8 RF PLP ltac:(lia) ltac:(lia)) as Q4;
              pose proof (lb_apart_flag FI st m _ _ (fs_FL FI st 0) RF PC8 FLLO FLHI) as Q5; pose proof (lb_apart_flag FI st m _ _ (fs_FL FI st 0) RF PLP FLLO FLHI) as Q6).
    3: { cbn [disjoint_from]. repeat split; lia. }
    3: { cbn [disjoint_from]. repeat split; lia. }
    3: { cbn [disjoint_from]. repeat split; lia. }
    2: {
      intros mA mB r (cur' & SCx & R1 & R2 & R3 & R4 & (pa & pb & PCx & HX)) MUx WMx.
      exists cur'. split; [| split; [exact R1| split; [exact R2| split; [exact R3| split; [exact R4|]]]]].
      - eapply rw_cells_transport; [exact SCx| exact MUx| exact WMx|]. cbn [disjoint_from]. simpl_sizes. repeat split; lia.
      - exists pa, pb. split; [| exact HX]. eapply rw_cells_transport; [exact PCx| exact MUx| exact WMx|]. cbn [disjoint_from]. simpl_sizes. repeat split; lia. }

    unfold vf_body_A. intros m1. cbn zeta. intros MU1 WM1 FK1 ST1 MI1 AE1 RF1 FCO1 FE1 LIVE1 t0' t1' t2' a3' a4' a5' a6' a7' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6' F_' fc' VA.
    set (qv := match_q q) in *.
    assert (LSUB : forall g, In g (fs_live FI st) -> In g (fs_live FI (fs_next FI st 0))) by (intros g Hg; rewrite LIVE1; right; exact Hg).
    pose proof (fsb_ok FI) as (B1 & B2 & _ & B4 & _).
    assert (FW : Forall (fsw_iv FI) ((lo, q) :: FSIV [])).
    { apply fsw_cons_app; [apply app_iv_stack; lia|]. apply (fsw_FSIV FI []). constructor. }
    assert (PS24 : lb (fs_live FI st) S 24) by (apply (Contracts.lb_sub _ _ _ _ _ PLB); lia).
    assert (PM32 : lb (fs_live FI st) MB 32) by (apply (Contracts.lb_sub _ _ _ _ _ PLB); lia).

    pose proof (shz_stack_fs FI _ m m1 lo _ _ SHZ CLO (stack_lo_ok lo) (sh_hi_ok q ltac:(lia)) MU1 FW) as SHZ1.
    pose proof (shr_stack_fs FI _ m m1 lo _ _ SHR CLO ltac:(lia) (sh_hi_ok8 q QHI) MU1 FW) as SHR1.
    split_chunk VA 1%nat GC VArest.
    eapply evt_mono.
    { eapply (vf_respA IC FI STACK_MALLOC_1 qv lo S MB A len cap cur0 bs (fs_next FI st 0) (q + -48) P1 pw1 pw2).
      -
        unfold vf_okA. split; [exact CLO|]. split; [lia|]. split; [exact QVAL|]. split; [lia|].
        split; [exact MBLO|]. split; [exact MBS|]. split; [exact SHI|]. split; [exact SAL|]. split; [exact MBAL|].
        split; [exact (lb_mono _ _ _ _ PLB LSUB)|]. split; [exact A0|]. split; [exact AHI|]. split; [exact LBS|]. split; [exact CAP|]. split; [exact ACAP|].
        split; [exact CUR0|]. split; [exact TXP|]. split; [exact TFS|]. split; [exact TBAND|].
        split; [constructor; [split; [cbn [fst snd]; lia| left; cbn [fst snd]; replace (P1 + 16 - P1) with 16 by lia; exact (lb_mono _ _ _ _ PLP LSUB)]| constructor]|].
        split; [cbn [disjoint_from]; split; [lia| exact I]| split; [cbn [disjoint_from]; split; [lia| exact I]| exact ANZ]].
      - exact RF1.
      - exact FCO1.
      - exact FE1.
      - exact ST1.
      - exact (rw_cells_fkeep FI [] st m m1 S _ SC FK1 WM1 ltac:(left; apply (Contracts.lb_sub _ _ _ _ _ PS24); simpl_sizes; lia) I).
      - unfold mbuf_cells, MEMBUF_DEF_SIZE_INC in *. exact (rw_cells_fkeep FI [] st m m1 MB _ MBC FK1 WM1 ltac:(left; apply (Contracts.lb_sub _ _ _ _ _ PM32); simpl_sizes; lia) I).
      - apply (bytes_at_transport asegs _ m m1 A bs BUF MU1). cbn [disjoint_from].
        split; [lia|]. split; [lia|]. split; [unfold sh, SHADOW_OFF; clear - TBAND B1 B2 ACR; Z.div_mod_to_equations; lia| exact I].
      - exact MI1.
      - exact AE1.
      - exact (shw_fkeep0 FI st m m1 S 24 SHS FK1 RF PS24).
      - exact (shw_fkeep0 FI st m m1 MB 32 SHMB FK1 RF PM32).
      - intros HL. apply (shw_frame_fs FI _ m m1 A len (SHA HL) MU1 FW). clear - TFS LBS. lia.
      - exact (shw_frame_fs FI _ m m1 SEPTAB_A 20 SHSEP MU1 FW ltac:(left; unfold SEPTAB_A; lia)).
      - exact (shw_frame_fs FI _ m m1 FMT_RESP_A 16 SHFMT MU1 FW ltac:(left; lia)).
      - eapply shz_sub; [exact SHZ1| lia| apply sh_mono; lia].
      - exact GC.
      - eapply (shw_of_shz_shr m1 _ _ _ _ (q + -48) 8 SHZ1 SHR1).
        + unfold win_ok. split; [lia|]. right. change (2^47) with 140737488355328 in *. lia.
        + apply sh_mono. lia.
        + unfold sh, SHADOW_OFF. clear. Z.div_mod_to_equations. lia.
        + pose proof (sh_mono lo (q + -48) ltac:(lia)). pose proof (Z.mod_pos_bound (sh lo) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (sh (q + -48)) 8 ltac:(lia)).
          assert (E8 : sh lo - sh lo mod 8 <= sh (q + -48) - sh (q + -48) mod 8) by (clear - H; Z.div_mod_to_equations; lia). exact E8.
        + unfold sh, SHADOW_OFF. clear - AL16. Z.div_mod_to_equations. lia.
      - lia.
      - change (2^47) with 140737488355328 in *. lia.
      - clear - AL16. Z.div_mod_to_equations. lia.
      - exact (rw_cells_fkeep FI [] st m m1 P1 _ PC1 FK1 WM1 ltac:(left; apply (Contracts.lb_sub _ _ _ _ _ PLP); simpl_sizes; lia) I).
      - exact (shw_fkeep0 FI st m m1 P1 16 SHP FK1 RF PLP).
      - exact PAL. }
    intros ms' (r & cur' & u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & st2 & E & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & HX).
    unfold vf_post_A. exists r, u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m2, st2.
    split; [exact E|]. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|]. split; [exact H6|].
    split; [exact H7|]. split; [exact H8|].
    unfold X. exists cur'. split; [exact H9|]. split; [exact H13|]. split; [exact H14|]. split; [exact H15|]. split; [exact H16| exact HX]. }

  intros ms' (r & u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & st' & E & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & HX).
  rewrite EQ in *. destruct HX as (cur' & SCx & R1 & R2 & R3 & R4 & HXR).
  unfold match_resp_postA. exists r, cur', u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m', st'.
  split; [exact E|]. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|]. split; [exact H6|].
  split; [exact H7|]. split; [exact H8|]. split; [exact SCx|]. split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4| exact HXR].
Qed.

#[using="Type"] Lemma vf_ok_move : forall q lo S MB A len cap cur0 bs st st1 Wx,
  vf_okA FI q lo S MB A len cap cur0 bs st Wx -> lo <= q - 16384 -> q <= 2^47 - 64 ->
  (forall g, In g (fs_live FI st) -> In g (fs_live FI st1)) ->
  vf_okA FI (match_q q) lo S MB A len cap cur0 bs st1 Wx.
Proof.
  intros q lo S MB A len cap cur0 bs st st1 Wx (CLO & LO & AL16 & QHI & MBLO & MBS & SHI & SAL & MBAL & PLB & A0 & AHI & LBS & CAP & ACAP & CUR0 & TXP & TFS & TBAND & WXL & WXT & WXP & ANZ) LO2 Q2 LSUB.
  destruct (match_q_facts q AL16) as [QV QVAL].
  unfold vf_okA. split; [exact CLO|]. split; [lia|]. split; [exact QVAL|]. split; [lia|].
  split; [exact MBLO|]. split; [exact MBS|]. split; [exact SHI|]. split; [exact SAL|]. split; [exact MBAL|].
  split; [exact (lb_mono _ _ _ _ PLB LSUB)|]. split; [exact A0|]. split; [exact AHI|]. split; [exact LBS|]. split; [exact CAP|]. split; [exact ACAP|].
  split; [exact CUR0|]. split; [exact TXP|]. split; [exact TFS|]. split; [exact TBAND|].
  split; [| split; [exact WXT| split; [exact WXP| exact ANZ]]].
  eapply Forall_impl; [| exact WXL]. intros iv [LE [LB|ER]]; (split; [exact LE|]); [left; exact (lb_mono _ _ _ _ LB LSUB)| right; exact ER].
Qed.

#[using="Type"] Lemma mctx_move : forall q lo S MB A len cap cur0 bs st Wx FMT flen m m1,
  vf_okA FI q lo S MB A len cap cur0 bs st Wx -> lo <= q - 16384 -> q <= 2^47 - 64 -> RFAKE FI st m ->
  0x10000 <= FMT -> FMT + flen <= 0x609000 ->
  munch ((lo, q) :: FSIV []) m m1 -> wmono asegs m m1 -> fkeep FI [] st m m1 ->
  rw_cells asegs m S [C8 (wz MB); C8 (wz cur0); C4 (wz 0)] -> rw_cells asegs m MB (mbuf_cells A len cap) -> bytes_at asegs m A bs ->
  shw m S 24 -> shw m MB 32 -> (0 < len -> shw m A len) -> shw m SEPTAB_A 20 -> shw m FMT flen ->
  shz m (sh lo) (sh q) -> shr m (sh lo - sh lo mod 8) (sh q + 8) ->
  rw_cells asegs m1 S [C8 (wz MB); C8 (wz cur0); C4 (wz 0)] /\ rw_cells asegs m1 MB (mbuf_cells A len cap) /\ bytes_at asegs m1 A bs
  /\ shw m1 S 24 /\ shw m1 MB 32 /\ (0 < len -> shw m1 A len) /\ shw m1 SEPTAB_A 20 /\ shw m1 FMT flen
  /\ shz m1 (sh lo) (sh (match_q q)) /\ shz m1 (sh lo) (sh q) /\ shr m1 (sh lo - sh lo mod 8) (sh q + 8).
Proof.
  intros q lo S MB A len cap cur0 bs st Wx FMT flen m m1 (CLO & LO & AL16 & QHI & MBLO & MBS & SHI & SAL & MBAL & PLB & A0 & AHI & LBS & CAP & ACAP & CUR0 & TXP & TFS & TBAND & WXL & WXT & WXP & _)
    LO2 Q2 RF F1 F2 MU1 WM1 FK1 SC MBC BUF SHS SHMB SHA SHSEP SHFMT SHZ SHR.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  destruct (match_q_facts q AL16) as [QV QVAL].
  pose proof (fsb_ok FI) as (B1 & B2 & _ & B4 & _).
  assert (FW : Forall (fsw_iv FI) ((lo, q) :: FSIV [])).
  { apply fsw_cons_app; [apply app_iv_stack; lia|]. apply (fsw_FSIV FI []). constructor. }
  assert (PS24 : lb (fs_live FI st) S 24) by (apply (Contracts.lb_sub _ _ _ _ _ PLB); lia).
  assert (PM32 : lb (fs_live FI st) MB 32) by (apply (Contracts.lb_sub _ _ _ _ _ PLB); lia).
  pose proof (shz_stack_fs FI _ m m1 lo _ _ SHZ CLO (stack_lo_ok lo) (sh_hi_ok q ltac:(lia)) MU1 FW) as SHZ1.
  pose proof (shr_stack_fs FI _ m m1 lo _ _ SHR CLO ltac:(lia) (sh_hi_ok8 q Q2) MU1 FW) as SHR1.
  split; [exact (rw_cells_fkeep FI [] st m m1 S _ SC FK1 WM1 ltac:(left; apply (Contracts.lb_sub _ _ _ _ _ PS24); simpl_sizes; lia) I)|].
  split; [unfold mbuf_cells, MEMBUF_DEF_SIZE_INC in *; exact (rw_cells_fkeep FI [] st m m1 MB _ MBC FK1 WM1 ltac:(left; apply (Contracts.lb_sub _ _ _ _ _ PM32); simpl_sizes; lia) I)|].
  split. { apply (bytes_at_transport asegs _ m m1 A bs BUF MU1). cbn [disjoint_from].
           split; [lia|]. split; [lia|]. split; [unfold sh, SHADOW_OFF; clear - TBAND B1 B2 ACR; Z.div_mod_to_equations; lia| exact I]. }
  split; [exact (shw_fkeep0 FI st m m1 S 24 SHS FK1 RF PS24)|]. split; [exact (shw_fkeep0 FI st m m1 MB 32 SHMB FK1 RF PM32)|].
  split; [intros HL; apply (shw_frame_fs FI _ m m1 A len (SHA HL) MU1 FW); clear - TFS LBS; lia|].
  split; [exact (shw_frame_fs FI _ m m1 SEPTAB_A 20 SHSEP MU1 FW ltac:(left; unfold SEPTAB_A; lia))|].
  split; [exact (shw_frame_fs FI _ m m1 FMT flen SHFMT MU1 FW ltac:(left; lia))|].
  split; [eapply shz_sub; [exact SHZ1| lia| apply sh_mono; lia]|]. split; [exact SHZ1| exact SHR1].
Qed.

#[using="Type"] Lemma mout_move : forall st m m1 P (pa pb : word), RFAKE FI st m -> wmono asegs m m1 -> fkeep FI [] st m m1 -> lb (fs_live FI st) P 16 ->
  rw_cells asegs m P [C8 pa; C8 pb] -> shw m P 16 -> rw_cells asegs m1 P [C8 pa; C8 pb] /\ shw m1 P 16.
Proof.
  intros st m m1 P pa pb RF WM1 FK1 LB PC SHP. split.
  - exact (rw_cells_fkeep FI [] st m m1 P _ PC FK1 WM1 ltac:(left; apply (Contracts.lb_sub _ _ _ _ _ LB); simpl_sizes; lia) I).
  - exact (shw_fkeep0 FI st m m1 P 16 SHP FK1 RF LB).
Qed.

#[using="Type"] Lemma mva_shw : forall q lo m1 X, alloc_ceiling <= lo -> lo <= q - 16384 -> q mod 16 = 0 -> q <= 2^47 - 64 ->
  shz m1 (sh lo) (sh q) -> shr m1 (sh lo - sh lo mod 8) (sh q + 8) -> q + -48 <= X -> X + 8 <= q -> X mod 8 = 0 -> shw m1 X 8.
Proof.
  intros q lo m1 X CLO LO AL16 QHI SHZ1 SHR1 X1 X2 XAL.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  eapply (shw_of_shz_shr m1 _ _ _ _ X 8 SHZ1 SHR1).
  - unfold win_ok. split; [lia|]. right. change (2^47) with 140737488355328 in *. lia.
  - apply sh_mono. lia.
  - unfold sh, SHADOW_OFF. clear - X2 XAL AL16. Z.div_mod_to_equations. lia.
  - pose proof (sh_mono lo X ltac:(lia)) as H. clear - H. Z.div_mod_to_equations. lia.
  - unfold sh, SHADOW_OFF. clear - X2 XAL AL16. Z.div_mod_to_equations. lia.
Qed.

#[using="Type"] Lemma chunk_mframe : forall st m0 m m' P cs, RFAKE FI st m0 -> lb (fs_live FI st) P (Z.of_nat (cells_size cs)) ->
  rw_cells asegs m P cs -> munch [(fs_F FI st 0, fs_F FI st 0 + 64); (sh (fs_F FI st 0), sh (fs_F FI st 0) + 8); (fs_FL FI st 0, fs_FL FI st 0 + 1)] m m' ->
  wmono asegs m m' -> rw_cells asegs m' P cs.
Proof.
  intros st m0 m m' P cs RF LB PC MU WM.
  destruct (new_frame_facts FI st 0 m0 (fs_F FI st 0) (sh (fs_F FI st 0)) (fs_FL FI st 0) RF ltac:(lia) eq_refl eq_refl eq_refl) as (FCLS & FLO & FHI & FAL & FLLO & FLHI & APART).
  cbn [FB_of SB_of] in FHI, APART.
  assert (SHF1 : sh (FSB FI) <= sh (fs_F FI st 0) /\ sh (fs_F FI st 0) + 8 <= sh (FSB FI) + A0_FS_SHSIZE)
    by (pose proof (fsb_ok FI) as (B1 & B2 & _ & B4 & _); unfold sh, SHADOW_OFF; clear - FLO FHI B4; Z.div_mod_to_equations; lia).
  pose proof (lb_apart_frame _ _ _ (fs_F FI st 0) 64 _ _ LB APART) as Q1.
  pose proof (lb_apart_shadow FI st m0 _ _ (sh (fs_F FI st 0)) 8 RF LB ltac:(lia) ltac:(lia)) as Q3.
  pose proof (lb_apart_flag FI st m0 _ _ (fs_FL FI st 0) RF LB FLLO FLHI) as Q5.
  eapply rw_cells_transport; [exact PC| exact MU| exact WM|]. cbn [disjoint_from]. repeat split; lia.
Qed.

#[using="Type"] Lemma mshell_dj : forall st m0 (Wx : list ivl), RFAKE FI st m0 ->
  Forall (fun iv : ivl => fst iv <= snd iv /\ (lb (fs_live FI st) (fst iv) (snd iv - fst iv) \/ (0x5e7508 <= fst iv /\ snd iv <= 0x5e7510))) Wx ->
  disjoint_from Wx (fs_F FI st 0) 64 /\ disjoint_from Wx (sh (fs_F FI st 0)) 8 /\ disjoint_from Wx (fs_FL FI st 0) 1.
Proof.
  intros st m0 Wx RF WXL.
  destruct (new_frame_facts FI st 0 m0 (fs_F FI st 0) (sh (fs_F FI st 0)) (fs_FL FI st 0) RF ltac:(lia) eq_refl eq_refl eq_refl) as (FCLS & FLO & FHI & FAL & FLLO & FLHI & APART).
  cbn [FB_of SB_of] in FHI, APART.
  assert (SHF1 : sh (FSB FI) <= sh (fs_F FI st 0) /\ sh (fs_F FI st 0) + 8 <= sh (FSB FI) + A0_FS_SHSIZE)
    by (pose proof (fsb_ok FI) as (B1 & B2 & _ & B4 & _); unfold sh, SHADOW_OFF; clear - FLO FHI B4; Z.div_mod_to_equations; lia).
  induction Wx as [|[a b] W IH]; cbn [disjoint_from]; [repeat split; exact I|].
  inversion WXL as [|? ? [LE [LB|ER]] WXL']; subst; cbn [fst snd] in *; destruct (IH WXL') as (I1 & I2 & I3).
  - pose proof (lb_apart_frame _ _ _ (fs_F FI st 0) 64 _ _ LB APART) as Q1.
    pose proof (lb_apart_shadow FI st m0 _ _ (sh (fs_F FI st 0)) 8 RF LB ltac:(lia) ltac:(lia)) as Q3.
    pose proof (lb_apart_flag FI st m0 _ _ (fs_FL FI st 0) RF LB FLLO FLHI) as Q5.
    repeat split; try assumption; lia.
  - assert (LOW : 0x609000 <= fs_F FI st 0 /\ 0x609000 <= sh (fs_F FI st 0) /\ 0x609000 <= fs_FL FI st 0).
    { pose proof (fsb_ok FI) as (B1 & _). unfold sh, SHADOW_OFF in *. clear - FLO FLLO SHF1 B1. Z.div_mod_to_equations. lia. }
    repeat split; try assumption; right; lia.
Qed.
#[using="Type"] Lemma mshell_dj_stack : forall st m0 (Wx : list ivl) q lo, RFAKE FI st m0 -> alloc_ceiling <= lo -> lo + 144 <= q ->
  Forall (fun iv : ivl => fst iv <= snd iv /\ (lb (fs_live FI st) (fst iv) (snd iv - fst iv) \/ (0x5e7508 <= fst iv /\ snd iv <= 0x5e7510))) Wx -> disjoint_from Wx (q + -144) 144.
Proof.
  intros st m0 Wx q lo RF CLO LO WXL. pose proof (fsb_ok FI) as (B1 & B2 & _).
  induction Wx as [|[a b] W IH]; cbn [disjoint_from]; [exact I|].
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  inversion WXL as [|? ? [LE [LB|ER]] WXL']; subst; cbn [fst snd] in *; [destruct (lb_in_fs FI st m0 RF _ _ LB) as [H1 H2]|];
  (split; [right; lia| exact (IH WXL')]).
Qed.

Definition match_postXA (Wx : list ivl) (XF : mem -> Z -> Z -> Prop)
    (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32)
    (st : fsstate FI) (lo S MB len cur0 : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (r cur' : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (st' : fsstate FI),
    ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F_ (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch ((lo, q) :: FSIV ((S + 8, S + 16) :: Wx)) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ fkeep FI ((S + 8, S + 16) :: Wx) st m m' /\ fs_live FI st' = fs_live FI st /\ RFAKE FI st' m'
    /\ stk asegs m' lo q /\ asan_env asegs m'
    /\ rw_cells asegs m' S [C8 (wz MB); C8 (wz cur'); C4 (wz 0)]
    /\ 0 <= r <= 5 /\ 0 <= cur' <= len /\ (r = 4 -> cur0 <= cur') /\ (r <> 4 -> cur' = cur0)
    /\ XF m' r cur'.

Definition mframed (st : fsstate FI) (XF : mem -> Z -> Z -> Prop) : Prop :=
  forall m m' r c, XF m r c ->
    munch [(fs_F FI st 0, fs_F FI st 0 + 64); (sh (fs_F FI st 0), sh (fs_F FI st 0) + 8); (fs_FL FI st 0, fs_FL FI st 0 + 1)] m m' -> wmono asegs m m' -> XF m' r c.

#[using="STACK_MALLOC_0"] Lemma match_wrapA : forall (Wx : list ivl) (FMT : Z) (XF : mem -> Z -> Z -> Prop)
    (S MB A len cap cur0 lo q : Z) (bs : list byte) (st : fsstate FI)
    (ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F_ : bvmap 5 word) (fc : bv 32) (m : mem),
  vf_okA FI q lo S MB A len cap cur0 bs st Wx -> lo <= q - 16384 -> q <= 2^47 - 64 -> RFAKE FI st m -> fs_call_ok FI st tp 2 -> FSENV FI m ->
  stk asegs m lo q -> mem_inv asegs m -> asan_env asegs m ->
  mframed st XF ->

  (forall m1 t0' t1' t2' a3' a4' a5' a6' a7' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6' (F_' : bvmap 5 word) fc',
     munch ((lo, q) :: FSIV []) m m1 -> wmono asegs m m1 -> fkeep FI [] st m m1 ->
     stk asegs m1 lo (match_q q) -> mem_inv asegs m1 -> asan_env asegs m1 -> RFAKE FI (fs_next FI st 0) m1 -> fs_call_ok FI (fs_next FI st 0) tp 1 -> FSENV FI m1 ->
     fs_live FI (fs_next FI st 0) = fs_newff FI st 0 :: fs_live FI st ->
     rw_cells asegs m1 (q + -48) [C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7] ->
     evt asegs (vpostA FI (match_q q) lo S MB A len cap cur0 bs (fs_next FI st 0) Wx (wz 0x88344) gp tp (wz (q + -48)) (wz (match_q q))
                       (wz (fs_F FI st 0)) (wz (sh (fs_F FI st 0))) (wz (fs_F FI st 0)) s5' s6' s7' s8' s9' s10' s11' F_' fc' m1 XF)
       (MS (mkR (wz 0x88344) (wz (match_q q)) gp tp t0' t1' t2' (wz (q + -48)) (wz (match_q q)) (wz S) (wz FMT) (wz (q + -48)) a3' a4' a5' a6' a7'
                (wz (fs_F FI st 0)) (wz (sh (fs_F FI st 0))) (wz (fs_F FI st 0)) s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6')
           F_' (wz vfmatch_entryA) fc' None m1 (seg_rom asegs))) ->
  evt asegs (match_postXA Wx XF ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc st lo S MB len cur0 m)
      (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz S) (wz FMT) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz match_entry) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros VOK LO Q2 RF FCO FE ST MI AE XFR BODY.
  pose proof VOK as VOK'. destruct VOK' as (CLO & _ & AL16 & _ & MBLO & MBS & SHI & _ & _ & PLB & _ & _ & _ & _ & _ & _ & _ & _ & _ & WXL & _ & WXP & _).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  assert (EQ : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  assert (PS24 : lb (fs_live FI st) S 24) by (apply (Contracts.lb_sub _ _ _ _ _ PLB); lia).
  assert (WVL : Forall (fun iv : ivl => fst iv <= snd iv /\ (lb (fs_live FI st) (fst iv) (snd iv - fst iv) \/ (0x5e7508 <= fst iv /\ snd iv <= 0x5e7510))) ((S + 8, S + 16) :: Wx)).
  { constructor; [split; [cbn [fst snd]; lia| left; cbn [fst snd]; apply (Contracts.lb_sub _ _ _ _ _ PLB); lia]| exact WXL]. }
  pose (X := fun (m2 : mem) (r : Z) => exists cur', rw_cells asegs m2 S [C8 (wz MB); C8 (wz cur'); C4 (wz 0)]
               /\ 0 <= r <= 5 /\ 0 <= cur' <= len /\ (r = 4 -> cur0 <= cur') /\ (r <> 4 -> cur' = cur0) /\ XF m2 r cur').
  destruct (mshell_dj st m ((S + 8, S + 16) :: Wx) RF WVL) as (DJ1 & DJ2 & DJ3).
  eapply evt_mono.
  { eapply (match_shell_A FI STACK_MALLOC_0 st ((S + 8, S + 16) :: Wx) lo S FMT X) with (sp := wz q); rewrite ?EQ.
    3: exact ST. 3: exact CLO. 3: lia. 3: exact AL16. 3: exact MI. 3: exact AE. 3: exact RF. 3: exact FCO. 3: exact FE.
    3: exact (mshell_dj_stack st m _ q lo RF CLO ltac:(lia) WVL). 3: exact DJ1. 3: exact DJ2. 3: exact DJ3.
    2: { intros mA mB r (cur' & SCx & R1 & R2 & R3 & R4 & HX) MUx WMx.
         exists cur'. split; [| split; [exact R1| split; [exact R2| split; [exact R3| split; [exact R4| exact (XFR _ _ _ _ HX MUx WMx)]]]]].
         eapply (chunk_mframe st m mA mB S _ RF); [apply (Contracts.lb_sub _ _ _ _ _ PS24); simpl_sizes; lia| exact SCx| exact MUx| exact WMx]. }
    unfold vf_body_A. intros m1. cbn zeta. intros MU1 WM1 FK1 ST1 MI1 AE1 RF1 FCO1 FE1 LIVE1 t0' t1' t2' a3' a4' a5' a6' a7' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6' F_' fc' VA.
    eapply evt_mono; [eapply (BODY m1); eassumption|].
    intros ms' (r & cur' & u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & st2 & E & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & HX).
    unfold vf_post_A. exists r, u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m2, st2.
    split; [exact E|]. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|]. split; [exact H6|].
    split; [exact H7|]. split; [exact H8|].
    unfold X. exists cur'. split; [exact H9|]. split; [exact H13|]. split; [exact H14|]. split; [exact H15|]. split; [exact H16| exact HX]. }
  intros ms' (r & u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & st' & E & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & HX).
  rewrite EQ in *. destruct HX as (cur' & SCx & R1 & R2 & R3 & R4 & HXR).
  unfold match_postXA. exists r, cur', u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m', st'.
  split; [exact E|]. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|]. split; [exact H6|].
  split; [exact H7|]. split; [exact H8|]. split; [exact SCx|]. split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4| exact HXR].
Qed.

#[using="Type"] Lemma out_mframed : forall st m0 P, RFAKE FI st m0 -> lb (fs_live FI st) P 16 ->
  forall m m' (pa pb : word), rw_cells asegs m P [C8 pa; C8 pb] ->
    munch [(fs_F FI st 0, fs_F FI st 0 + 64); (sh (fs_F FI st 0), sh (fs_F FI st 0) + 8); (fs_FL FI st 0, fs_FL FI st 0 + 1)] m m' -> wmono asegs m m' ->
    rw_cells asegs m' P [C8 pa; C8 pb].
Proof. intros st m0 P RF LB m m' pa pb PC MU WM. exact (chunk_mframe st m0 m m' P [C8 pa; C8 pb] RF LB PC MU WM). Qed.

#[using="IC STACK_MALLOC_0 STACK_MALLOC_1"] Theorem match_hdrA : forall (S MB A len cap cur0 P1 lo q : Z) (bs : list byte) (st : fsstate FI) (pw1 pw2 : word)
    (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F_ : bvmap 5 word) (fc : bv 32) (m : mem),
  vf_okA FI q lo S MB A len cap cur0 bs st [(P1, P1 + 16)] -> lo <= q - 16384 -> q <= 2^47 - 64 -> RFAKE FI st m -> fs_call_ok FI st tp 2 -> FSENV FI m ->
  stk asegs m lo q -> mem_inv asegs m -> asan_env asegs m ->
  rw_cells asegs m S [C8 (wz MB); C8 (wz cur0); C4 (wz 0)] -> rw_cells asegs m MB (mbuf_cells A len cap) -> bytes_at asegs m A bs ->
  shw m S 24 -> shw m MB 32 -> (0 < len -> shw m A len) -> shw m SEPTAB_A 20 -> shw m FMT_HDR_A 8 ->
  shz m (sh lo) (sh q) -> shr m (sh lo - sh lo mod 8) (sh q + 8) ->
  rw_cells asegs m P1 [C8 pw1; C8 pw2] -> shw m P1 16 -> P1 mod 8 = 0 ->
  evt asegs (match_postXA [(P1, P1 + 16)] (X_hdrA A len cur0 P1) ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc st lo S MB len cur0 m)
      (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz S) (wz FMT_HDR_A) (wz P1) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz match_entry) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros VOK LO Q2 RF FCO FE ST MI AE SC MBC BUF SHS SHMB SHA SHSEP SHFMT SHZ SHR PC1 SHP PAL.
  pose proof VOK as VOK'. destruct VOK' as (CLO & _ & AL16 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & WXL & _ & _).
  assert (LBP : lb (fs_live FI st) P1 16).
  { inversion WXL as [|? ? [LE [LB|ER]] _]; subst; cbn [fst snd] in *; [| exfalso; clear - ER; lia]. replace (P1 + 16 - P1) with 16 in LB by lia. exact LB. }
  destruct (match_q_facts q AL16) as [QV QVAL].
  eapply (match_wrapA [(P1, P1 + 16)] FMT_HDR_A (X_hdrA A len cur0 P1)); try eassumption.
  - intros mA mB r c (pa & pb & PC & HX) MU WM. exists pa, pb. split; [exact (out_mframed st m P1 RF LBP mA mB pa pb PC MU WM)| exact HX].
  - intros m1 t0' t1' t2' a3' a4' a5' a6' a7' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6' F_' fc' MU1 WM1 FK1 ST1 MI1 AE1 RF1 FCO1 FE1 LIVE1 VA.
    assert (LSUB : forall g, In g (fs_live FI st) -> In g (fs_live FI (fs_next FI st 0))) by (intros g Hg; rewrite LIVE1; right; exact Hg).
    destruct (mctx_move q lo S MB A len cap cur0 bs st _ FMT_HDR_A 8 m m1 VOK LO Q2 RF ltac:(lia) ltac:(lia) MU1 WM1 FK1 SC MBC BUF SHS SHMB SHA SHSEP SHFMT SHZ SHR)
      as (SC1 & MBC1 & BUF1 & SHS1 & SHMB1 & SHA1 & SHSEP1 & SHFMT1 & SHZv & SHZ1 & SHR1).
    destruct (mout_move st m m1 P1 pw1 pw2 RF WM1 FK1 LBP PC1 SHP) as [PC1' SHP'].
    split_chunk VA 1%nat GC VArest.
    eapply (vf_hdrA IC FI STACK_MALLOC_1 (match_q q) lo S MB A len cap cur0 bs (fs_next FI st 0) (q + -48) P1 pw1 pw2); try eassumption.
    + exact (vf_ok_move q lo S MB A len cap cur0 bs st _ _ VOK LO Q2 LSUB).
    + exact (mva_shw q lo m1 (q + -48) CLO LO AL16 Q2 SHZ1 SHR1 ltac:(lia) ltac:(lia) ltac:(clear - AL16; Z.div_mod_to_equations; lia)).
    + lia.
    + change (2^47) with 140737488355328 in *. lia.
    + clear - AL16. Z.div_mod_to_equations. lia.
Qed.

#[using="IC STACK_MALLOC_0 STACK_MALLOC_1"] Theorem match_crlfA : forall (S MB A len cap cur0 lo q : Z) (bs : list byte) (st : fsstate FI)
    (ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F_ : bvmap 5 word) (fc : bv 32) (m : mem),
  vf_okA FI q lo S MB A len cap cur0 bs st [] -> lo <= q - 16384 -> q <= 2^47 - 64 -> RFAKE FI st m -> fs_call_ok FI st tp 2 -> FSENV FI m ->
  stk asegs m lo q -> mem_inv asegs m -> asan_env asegs m ->
  rw_cells asegs m S [C8 (wz MB); C8 (wz cur0); C4 (wz 0)] -> rw_cells asegs m MB (mbuf_cells A len cap) -> bytes_at asegs m A bs ->
  shw m S 24 -> shw m MB 32 -> (0 < len -> shw m A len) -> shw m SEPTAB_A 20 -> shw m FMT_CRLF_A 3 ->
  shz m (sh lo) (sh q) -> shr m (sh lo - sh lo mod 8) (sh q + 8) ->
  evt asegs (match_postXA [] (fun m' r cur' => True /\ (r = 4 -> cur0 + 1 <= cur')) ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc st lo S MB len cur0 m)
      (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz S) (wz FMT_CRLF_A) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz match_entry) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros VOK LO Q2 RF FCO FE ST MI AE SC MBC BUF SHS SHMB SHA SHSEP SHFMT SHZ SHR.
  eapply (match_wrapA [] FMT_CRLF_A (fun m' r cur' => True /\ (r = 4 -> cur0 + 1 <= cur'))); try eassumption.
  - intros mA mB r c HX _ _. exact HX.
  - intros m1 t0' t1' t2' a3' a4' a5' a6' a7' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6' F_' fc' MU1 WM1 FK1 ST1 MI1 AE1 RF1 FCO1 FE1 LIVE1 VA.
    assert (LSUB : forall g, In g (fs_live FI st) -> In g (fs_live FI (fs_next FI st 0))) by (intros g Hg; rewrite LIVE1; right; exact Hg).
    destruct (mctx_move q lo S MB A len cap cur0 bs st _ FMT_CRLF_A 3 m m1 VOK LO Q2 RF ltac:(lia) ltac:(lia) MU1 WM1 FK1 SC MBC BUF SHS SHMB SHA SHSEP SHFMT SHZ SHR)
      as (SC1 & MBC1 & BUF1 & SHS1 & SHMB1 & SHA1 & SHSEP1 & SHFMT1 & SHZv & SHZ1 & SHR1).
    eapply (vf_crlfA IC FI STACK_MALLOC_1 (match_q q) lo S MB A len cap cur0 bs (fs_next FI st 0) (q + -48)); try eassumption.
    exact (vf_ok_move q lo S MB A len cap cur0 bs st _ _ VOK LO Q2 LSUB).
Qed.
#[using="Type"] Lemma wxl_lb : forall st (Wx : list ivl) P, Forall (fun iv : ivl => fst iv <= snd iv /\ (lb (fs_live FI st) (fst iv) (snd iv - fst iv) \/ (0x5e7508 <= fst iv /\ snd iv <= 0x5e7510))) Wx ->
  In (P, P + 16) Wx -> lb (fs_live FI st) P 16.
Proof.
  intros st Wx P WXL HI. rewrite Forall_forall in WXL. destruct (WXL _ HI) as [_ [LB|ER]]; cbn [fst snd] in *; [| exfalso; clear - ER; lia]. replace (P + 16 - P) with 16 in LB by lia. exact LB.
Qed.

#[using="IC STACK_MALLOC_0 STACK_MALLOC_1"] Theorem match_req09A : forall (S MB A len cap cur0 P1 P2 lo q : Z) (bs : list byte) (st : fsstate FI) (pw1 pw2 pw3 pw4 : word)
    (ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F_ : bvmap 5 word) (fc : bv 32) (m : mem),
  vf_okA FI q lo S MB A len cap cur0 bs st [(P1, P1 + 16); (P2, P2 + 16)] -> lo <= q - 16384 -> q <= 2^47 - 64 -> RFAKE FI st m -> fs_call_ok FI st tp 2 -> FSENV FI m ->
  stk asegs m lo q -> mem_inv asegs m -> asan_env asegs m ->
  rw_cells asegs m S [C8 (wz MB); C8 (wz cur0); C4 (wz 0)] -> rw_cells asegs m MB (mbuf_cells A len cap) -> bytes_at asegs m A bs ->
  shw m S 24 -> shw m MB 32 -> (0 < len -> shw m A len) -> shw m SEPTAB_A 20 -> shw m FMT_REQ09_A 10 ->
  shz m (sh lo) (sh q) -> shr m (sh lo - sh lo mod 8) (sh q + 8) ->
  rw_cells asegs m P1 [C8 pw1; C8 pw2] -> shw m P1 16 -> P1 mod 8 = 0 ->
  rw_cells asegs m P2 [C8 pw3; C8 pw4] -> shw m P2 16 -> P2 mod 8 = 0 ->
  (P1 + 16 <= P2 \/ P2 + 16 <= P1) ->
  evt asegs (match_postXA [(P1, P1 + 16); (P2, P2 + 16)] (X_req09A A len cur0 P1 P2) ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc st lo S MB len cur0 m)
      (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz S) (wz FMT_REQ09_A) (wz P1) (wz P2) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz match_entry) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros VOK LO Q2 RF FCO FE ST MI AE SC MBC BUF SHS SHMB SHA SHSEP SHFMT SHZ SHR PC1 SHP1 PAL1 PC2 SHP2 PAL2 AP12.
  pose proof VOK as VOK'. destruct VOK' as (CLO & _ & AL16 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & WXL & _ & _).
  pose proof (wxl_lb st _ P1 WXL ltac:(left; reflexivity)) as LBP1. pose proof (wxl_lb st _ P2 WXL ltac:(right; left; reflexivity)) as LBP2.
  destruct (match_q_facts q AL16) as [QV QVAL].
  eapply (match_wrapA [(P1, P1 + 16); (P2, P2 + 16)] FMT_REQ09_A (X_req09A A len cur0 P1 P2)); try eassumption.
  - intros mA mB r c (pa & pb & pc & pd & H1 & H2 & HX) MU WM. exists pa, pb, pc, pd.
    split; [exact (out_mframed st m P1 RF LBP1 mA mB pa pb H1 MU WM)|]. split; [exact (out_mframed st m P2 RF LBP2 mA mB pc pd H2 MU WM)| exact HX].
  - intros m1 t0' t1' t2' a3' a4' a5' a6' a7' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6' F_' fc' MU1 WM1 FK1 ST1 MI1 AE1 RF1 FCO1 FE1 LIVE1 VA.
    assert (LSUB : forall g, In g (fs_live FI st) -> In g (fs_live FI (fs_next FI st 0))) by (intros g Hg; rewrite LIVE1; right; exact Hg).
    destruct (mctx_move q lo S MB A len cap cur0 bs st _ FMT_REQ09_A 10 m m1 VOK LO Q2 RF ltac:(lia) ltac:(lia) MU1 WM1 FK1 SC MBC BUF SHS SHMB SHA SHSEP SHFMT SHZ SHR)
      as (SC1 & MBC1 & BUF1 & SHS1 & SHMB1 & SHA1 & SHSEP1 & SHFMT1 & SHZv & SHZ1 & SHR1).
    destruct (mout_move st m m1 P1 pw1 pw2 RF WM1 FK1 LBP1 PC1 SHP1) as [PC1' SHP1'].
    destruct (mout_move st m m1 P2 pw3 pw4 RF WM1 FK1 LBP2 PC2 SHP2) as [PC2' SHP2'].
    split_chunk VA 1%nat GC1 VA2. split_chunk VA2 1%nat GC2 VArest. replace (q + -40) with (q + -48 + 8) in GC2 by lia.
    eapply (vf_req09A IC FI STACK_MALLOC_1 (match_q q) lo S MB A len cap cur0 bs (fs_next FI st 0) (q + -48) P1 P2 pw1 pw2 pw3 pw4); try eassumption.
    + exact (vf_ok_move q lo S MB A len cap cur0 bs st _ _ VOK LO Q2 LSUB).
    + exact (mva_shw q lo m1 (q + -48) CLO LO AL16 Q2 SHZ1 SHR1 ltac:(lia) ltac:(lia) ltac:(clear - AL16; Z.div_mod_to_equations; lia)).
    + exact (mva_shw q lo m1 (q + -48 + 8) CLO LO AL16 Q2 SHZ1 SHR1 ltac:(lia) ltac:(lia) ltac:(clear - AL16; Z.div_mod_to_equations; lia)).
    + lia.
    + change (2^47) with 140737488355328 in *. lia.
    + clear - AL16. Z.div_mod_to_equations. lia.
Qed.

#[using="IC STACK_MALLOC_0 STACK_MALLOC_1"] Theorem match_reqA : forall (S MB A len cap cur0 P1 P2 P3 lo q : Z) (bs : list byte) (st : fsstate FI) (pw1 pw2 pw3 pw4 pw5 pw6 : word)
    (ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F_ : bvmap 5 word) (fc : bv 32) (m : mem),
  vf_okA FI q lo S MB A len cap cur0 bs st [(P1, P1 + 16); (P2, P2 + 16); (P3, P3 + 16)] -> lo <= q - 16384 -> q <= 2^47 - 64 -> RFAKE FI st m -> fs_call_ok FI st tp 2 -> FSENV FI m ->
  stk asegs m lo q -> mem_inv asegs m -> asan_env asegs m ->
  rw_cells asegs m S [C8 (wz MB); C8 (wz cur0); C4 (wz 0)] -> rw_cells asegs m MB (mbuf_cells A len cap) -> bytes_at asegs m A bs ->
  shw m S 24 -> shw m MB 32 -> (0 < len -> shw m A len) -> shw m SEPTAB_A 20 -> shw m FMT_REQ_A 22 ->
  shz m (sh lo) (sh q) -> shr m (sh lo - sh lo mod 8) (sh q + 8) ->
  rw_cells asegs m P1 [C8 pw1; C8 pw2] -> shw m P1 16 -> P1 mod 8 = 0 ->
  rw_cells asegs m P2 [C8 pw3; C8 pw4] -> shw m P2 16 -> P2 mod 8 = 0 ->
  rw_cells asegs m P3 [C8 pw5; C8 pw6] -> shw m P3 16 -> P3 mod 8 = 0 ->
  (P1 + 16 <= P2 \/ P2 + 16 <= P1) -> (P1 + 16 <= P3 \/ P3 + 16 <= P1) -> (P2 + 16 <= P3 \/ P3 + 16 <= P2) ->
  evt asegs (match_postXA [(P1, P1 + 16); (P2, P2 + 16); (P3, P3 + 16)] (X_reqA A len cur0 bs P1 P2 P3) ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc st lo S MB len cur0 m)
      (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz S) (wz FMT_REQ_A) (wz P1) (wz P2) (wz P3) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz match_entry) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros VOK LO Q2 RF FCO FE ST MI AE SC MBC BUF SHS SHMB SHA SHSEP SHFMT SHZ SHR PC1 SHP1 PAL1 PC2 SHP2 PAL2 PC3 SHP3 PAL3 AP12 AP13 AP23.
  pose proof VOK as VOK'. destruct VOK' as (CLO & _ & AL16 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & WXL & _ & _).
  pose proof (wxl_lb st _ P1 WXL ltac:(left; reflexivity)) as LBP1. pose proof (wxl_lb st _ P2 WXL ltac:(right; left; reflexivity)) as LBP2.
  pose proof (wxl_lb st _ P3 WXL ltac:(right; right; left; reflexivity)) as LBP3.
  destruct (match_q_facts q AL16) as [QV QVAL].
  eapply (match_wrapA [(P1, P1 + 16); (P2, P2 + 16); (P3, P3 + 16)] FMT_REQ_A (X_reqA A len cur0 bs P1 P2 P3)); try eassumption.
  - intros mA mB r c (pa & pb & pc & pd & pe & pf & H1 & H2 & H3 & HX) MU WM. exists pa, pb, pc, pd, pe, pf.
    split; [exact (out_mframed st m P1 RF LBP1 mA mB pa pb H1 MU WM)|]. split; [exact (out_mframed st m P2 RF LBP2 mA mB pc pd H2 MU WM)|].
    split; [exact (out_mframed st m P3 RF LBP3 mA mB pe pf H3 MU WM)| exact HX].
  - intros m1 t0' t1' t2' a3' a4' a5' a6' a7' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6' F_' fc' MU1 WM1 FK1 ST1 MI1 AE1 RF1 FCO1 FE1 LIVE1 VA.
    assert (LSUB : forall g, In g (fs_live FI st) -> In g (fs_live FI (fs_next FI st 0))) by (intros g Hg; rewrite LIVE1; right; exact Hg).
    destruct (mctx_move q lo S MB A len cap cur0 bs st _ FMT_REQ_A 22 m m1 VOK LO Q2 RF ltac:(lia) ltac:(lia) MU1 WM1 FK1 SC MBC BUF SHS SHMB SHA SHSEP SHFMT SHZ SHR)
      as (SC1 & MBC1 & BUF1 & SHS1 & SHMB1 & SHA1 & SHSEP1 & SHFMT1 & SHZv & SHZ1 & SHR1).
    destruct (mout_move st m m1 P1 pw1 pw2 RF WM1 FK1 LBP1 PC1 SHP1) as [PC1' SHP1'].
    destruct (mout_move st m m1 P2 pw3 pw4 RF WM1 FK1 LBP2 PC2 SHP2) as [PC2' SHP2'].
    destruct (mout_move st m m1 P3 pw5 pw6 RF WM1 FK1 LBP3 PC3 SHP3) as [PC3' SHP3'].
    split_chunk VA 1%nat GC1 VA2. split_chunk VA2 1%nat GC2 VA3. split_chunk VA3 1%nat GC3 VArest.
    replace (q + -40) with (q + -48 + 8) in GC2 by lia. replace (q + -32) with (q + -48 + 16) in GC3 by lia.
    eapply (vf_reqA IC FI STACK_MALLOC_1 (match_q q) lo S MB A len cap cur0 bs (fs_next FI st 0) (q + -48) P1 P2 P3 pw1 pw2 pw3 pw4 pw5 pw6); try eassumption.
    + exact (vf_ok_move q lo S MB A len cap cur0 bs st _ _ VOK LO Q2 LSUB).
    + exact (mva_shw q lo m1 (q + -48) CLO LO AL16 Q2 SHZ1 SHR1 ltac:(lia) ltac:(lia) ltac:(clear - AL16; Z.div_mod_to_equations; lia)).
    + exact (mva_shw q lo m1 (q + -48 + 8) CLO LO AL16 Q2 SHZ1 SHR1 ltac:(lia) ltac:(lia) ltac:(clear - AL16; Z.div_mod_to_equations; lia)).
    + exact (mva_shw q lo m1 (q + -48 + 16) CLO LO AL16 Q2 SHZ1 SHR1 ltac:(lia) ltac:(lia) ltac:(clear - AL16; Z.div_mod_to_equations; lia)).
    + lia.
    + change (2^47) with 140737488355328 in *. lia.
    + clear - AL16. Z.div_mod_to_equations. lia.
Qed.
End M.
