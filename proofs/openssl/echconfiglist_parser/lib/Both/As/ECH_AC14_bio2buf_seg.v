(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCall AsCallX ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AStmt_C1 ECH_AStmt_C7 ECH_AKit ECH_AsKit AsWalk.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N6_tac.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim StrFun.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ARP_RSM : Z := 0x5530c0.    (* [comment removed for export] *)
Definition ARP_RSF : Z := 0x553170.    (* [comment removed for export] *)
Definition ARP_R1 : Z := 0x553200.     (* [comment removed for export] *)
Definition ARP_R2 : Z := 0x553218.     (* [comment removed for export] *)
Definition ARP_LSET : Z := 0x51a4dc.   (* [comment removed for export] *)
Definition ARP_LHEAD : Z := 0x55338c.  (* [comment removed for export] *)
Definition ARP_R3 : Z := 0x5533ac.     (* [comment removed for export] *)
(* [comment removed for export] *)
Definition ARP_FILE : Z := 0x11238e.   (* [comment removed for export] *)
Definition ARP_FUNC : Z := 0x112460.   (* [comment removed for export] *)
Definition ARP_DESCR : Z := 0x2252e.   (* [comment removed for export] *)
Definition AFRAME_MAGIC : Z := 0x41b58ab3.
Definition AFRAME_RETIRED : Z := 0x45e0360e.
Definition ARP_FFREQ : Z := 0x900.     (* [comment removed for export] *)
Definition ASHB : Z := 0x7fff8000.     (* [comment removed for export] *)
Definition OSSL_ECH_BUFCHUNK : Z := 512.

(* [comment removed for export] *)
Definition rp_s1 (esp : Z) : Z := esp - 448 - (esp - 448) mod 32.
Lemma rp_s1_cases : forall esp, esp mod 16 = 0 -> rp_s1 esp = esp - 448 \/ rp_s1 esp = esp - 464.
Proof. intros esp H. unfold rp_s1. Z.div_mod_to_equations. lia. Qed.
Lemma rp_s1_al : forall esp, esp mod 16 = 0 -> rp_s1 esp mod 32 = 0 /\ esp - 464 <= rp_s1 esp <= esp - 448.
Proof. intros esp H. unfold rp_s1. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
Definition arp_saves (s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma sx32_lit : forall x, 0 <= x < 2^31 -> sx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof. intros x Hx. apply (sx32_wz x Hx). Qed.

Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.
  Local Ltac br := let K0 := fresh "K0" in if_cases K0; zify_cond K0; try kill K0; try clear K0.
  Local Ltac retpc := match goal with |- context [ret_pc (Z_to_bv 64 ?v)] => replace (ret_pc (Z_to_bv 64 v)) with (Z_to_bv 64 v) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.
  (* [comment removed for export] *)
  Local Ltac rw_join H1 H2 J :=
    lazymatch type of H1 with rw_cells ?sg ?mx ?A ?cs1 =>
    lazymatch type of H2 with rw_cells _ _ ?B ?cs2 =>
      let n := eval lazy in (Z.of_nat (cells_size cs1)) in
      assert (J : rw_cells sg mx A (cs1 ++ cs2));
      [ apply (proj2 (rw_cells_app sg mx A cs1 cs2)); split;
        [ exact H1 | change (A + Z.of_nat (cells_size cs1)) with (A + n); replace (A + n) with B by lia; exact H2 ]
      | cbn [app] in J; clear H1 H2 ] end end.

  (* [comment removed for export] *)
  Lemma arp_seg1a :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st mb lo : Z),
      0 <= st < 2^64 -> 0 <= mb < 2^64 ->
      bv_unsigned sp mod 16 = 0 ->
      rw_cells asegs m AGOT_UAR [C8 (wz AUAR_CELL)] -> rw_cells asegs m AUAR_CELL [C4 (wz 1)] ->
      rw_cells asegs m AGOT_SHBASE [C8 (wz ASHBASE_CELL)] -> rw_cells asegs m ASHBASE_CELL [C8 (wz ASHADOW_BASE)] ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 464 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1 (j : list byte),
          ms' = MS (mkR (Z_to_bv 64 ARP_RSM) (Z_to_bv 64 (rp_s1 (bv_unsigned sp))) gp tp t0 t1 t2
                       sp (Z_to_bv 64 (rp_s1 (bv_unsigned sp))) (Z_to_bv 64 ARP_FFREQ) (Z_to_bv 64 ASHBASE_CELL) (Z_to_bv 64 1) (Z_to_bv 64 0) a4 a5 a6 a7
                       s2 s3 s4 (Z_to_bv 64 0) (Z_to_bv 64 mb) (Z_to_bv 64 st) s8 (Z_to_bv 64 ASHB) s10 (Z_to_bv 64 0) t3 t4 t5 t6)
                   F (Z_to_bv 64 AFS_MALLOC_6) fc None m1 (seg_rom asegs)
          /\ munch [(bv_unsigned sp + -448, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo (bv_unsigned sp + -448)
          /\ rw_cells asegs m1 (bv_unsigned sp + -448) (C8 (Z_to_bv 64 0) :: CB 336 j :: arp_saves s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 st) (Z_to_bv 64 mb) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_OSSL_ECHSTORE_read_echconfiglist) fc None m (seg_rom asegs)).
  Proof.
    intros until lo. intros STR MBR SP16 GU UAR GSB SHB0 ST CEIL LO MI.
    unfold P_OSSL_ECHSTORE_read_echconfiglist, ARP_RSM, ARP_FFREQ, ASHB, AFS_MALLOC_6.
    acb. unfold AGOT_UAR, AUAR_CELL, AGOT_SHBASE, ASHBASE_CELL, wz in GU, UAR, GSB, SHB0 |- *. rewrite ASHADOW_BASE_val in SHB0.
    pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -448, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    step. carve_frame 448%nat ST.
    do 2 st1. do 3 step. do 2 step. step. step.
    (* [comment removed for export] *)
    step. do 14 st1. step.
    (* [comment removed for export] *)
    zstep. rewrite land_align32 by lia.
    replace (bv_unsigned sp + -448 - (bv_unsigned sp + -448) mod 32) with (rp_s1 (bv_unsigned sp)) by (unfold rp_s1; lia).
    step.
    (* [comment removed for export] *)
    step. step. step. step. step. st1. st1. st1. rewrite (sx32_lit 1) by lia. st1. step.
    (* [comment removed for export] *)
    step. if_lit. zstep. zstep. step. step.
    finish. unfold arp_saves. exact FR.
  Qed.

  (* [comment removed for export] *)
  Definition arp_slotsP (j0 j1 j2 j3 j4 : list byte) (st ff : Z) : list cell :=
    [CB 16 j0; CB 128 j1; C8 (wz (Z.shiftr ff 3 + ASHB + 10)); CB 24 j2; C8 (wz ASHB); CB 32 j3; C8 (wz ff); CB 120 j4].
  (* [comment removed for export] *)
  Definition arp_fframe (q : Z) (j1 : list byte) (rb : Z) (j2 : list byte) (fp : Z) : list cell :=
    [C8 (wz AFRAME_MAGIC); C8 (wz ARP_DESCR); C8 (wz P_ech_read_priv_echconfiglist); C8 (wz q); CB 2224 j1; C8 (wz rb); CB 1824 j2; C8 (wz fp)].
  (* [comment removed for export] *)
  Definition arp_fshadow (a : list byte) (b : byte) (c : list byte) (b2 c2 : byte) (d e : list byte) (r : byte) (g : list byte) : list cell :=
    [CB 4 a; C1 b; CB 3 c; C1 b2; C1 c2; CB 256 d; CB 16 e; C1 r; CB 229 g].

  (* [comment removed for export] *)
  Lemma arp_seg1b :
    forall (rax s0w a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 t0 t1 t2 t3 t4 t5 t6 gp tp : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (q ff fp st mb : Z) (j0 js junk1 junk2 sh0 : list byte),
      set_shadow_f8_stmt ->
      0 < st < 2^64 -> 0 < mb < 2^64 ->
      AIMG_TOP + 32 <= ff -> ff + 4096 <= aceil -> ff mod 64 = 0 -> aapp ff 4096 ->
      aceil <= q -> q + 432 <= 2^64 ->
      rw_cells asegs m q [CB 16 j0; CB 328 js] ->
      rw_cells asegs m ff [CB 24 junk1; C8 (wz q); CB 4056 junk2; C8 (wz fp)] ->
      rw_cells asegs m (Z.shiftr ff 3 + ASHB) [CB 512 sh0] ->
      mem_inv asegs m -> ACONST m ->
      evt asegs (fun ms' => exists m1 (a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s4' s5' : word) (j1 j2 j3 j4 fj1 fj2 e5 : list byte),
          ms' = MS (mkR (Z_to_bv 64 ARP_R1) (Z_to_bv 64 q) gp tp t0' t1' t2'
                       s0w (Z_to_bv 64 q) (Z_to_bv 64 OSSL_ECH_BUFCHUNK) (Z_to_bv 64 ARP_FILE) (Z_to_bv 64 115) a3' a4' a5' a6' a7'
                       s4' (Z_to_bv 64 (Z.shiftr ff 3 + ASHB)) s5' (Z_to_bv 64 0) (Z_to_bv 64 mb) (Z_to_bv 64 st)
                       (Z_to_bv 64 ff) (Z_to_bv 64 (ff + 2256)) (Z_to_bv 64 ff) (Z_to_bv 64 0) t3' t4' t5' t6')
                   F (Z_to_bv 64 P_CRYPTO_zalloc) fc None m1 (seg_rom asegs)
          /\ munch [(q, q + 344); (ff, ff + 4096); (Z.shiftr ff 3 + ASHB, Z.shiftr ff 3 + ASHB + 512)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ rw_cells asegs m1 q (arp_slotsP j0 j1 j2 j3 j4 st ff)
          /\ rw_cells asegs m1 ff (arp_fframe q fj1 0 fj2 fp)
          /\ rw_cells asegs m1 (Z.shiftr ff 3 + ASHB)
               (arp_fshadow (poison_bytes 4 0xf1) (b8 0xf8) (poison_bytes 3 0xf2) (b8 0xf8) (b8 0xf2) (poison_bytes 256 0xf8) (poison_bytes 16 0xf2) (b8 0) e5)
          /\ ACONST m1)
        (MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 ff) a1 a2 a3 a4 a5 a6 a7
                 s5 s3 s4 (Z_to_bv 64 0) (Z_to_bv 64 mb) (Z_to_bv 64 st) s6 (Z_to_bv 64 ASHB) s7 (Z_to_bv 64 0) t3 t4 t5 t6)
            F (Z_to_bv 64 ARP_RSM) fc None m (seg_rom asegs)).
  Proof.
    intros until sh0. intros SF8 STR MBR FF1 FF2 FF64 AAP Q1 Q2 SL FRM SHC MI AC.
    unfold ARP_RSM, ARP_R1, OSSL_ECH_BUFCHUNK, ARP_FILE, P_CRYPTO_zalloc. unfold ASHB in *.
    acb. unfold aapp, aapp_lo, aapp_hi, AIMG_TOP, AHI_LO, ALOWSH_LO in *. unfold wz in FRM.
    pose proof (munch_refl [(q, q + 344); (ff, ff + 4096); (Z.shiftr ff 3 + 2147450880, Z.shiftr ff 3 + 2147450880 + 512)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    assert (SHR : Z.shiftr ff 3 = ff / 8) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    (* [comment removed for export] *)
    go. br.
    (* [comment removed for export] *)
    go.
    (* [comment removed for export] *)
    step.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    match type of SHC with rw_cells _ ?mx ?ax (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?rest) =>
      change (rw_cells asegs mx ax ([c1; c2; c3; c4; c5; c6; c7; c8; c9; c10] ++ rest)) in SHC end.
    apply (proj1 (rw_cells_app _ _ _ _ _)) in SHC. destruct SHC as [SH8 SHR5]. cbn [cells_size csize Nat.add] in SHR5. change (Z.of_nat 10) with 10 in SHR5.
    lazymatch goal with |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?sa) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      lazymatch type of SHR5 with rw_cells _ _ ?a0 _ => replace a0 with sa in SHR5 by lia end end.
    (* [comment removed for export] *)
    pose proof (rw_cells_CB_split _ _ _ _ 256%nat _ SHR5 ltac:(lia)) as [SH256 SH248]. clear SHR5.
    cbn [Nat.sub] in SH248. change (Z.of_nat 256) with 256 in SH248.
    lazymatch type of SH248 with rw_cells _ _ (Z.shiftr ff 3 + ?k + 256) _ =>
      let k' := eval vm_compute in (k + 256) in replace (Z.shiftr ff 3 + k + 256) with (Z.shiftr ff 3 + k') in SH248 by lia end.
    (* [comment removed for export] *)
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (ACc : ACONST mc) by
        (eapply ACONST_frame; [exact AC| exact MU| exact WM|];
         apply Forall_cons; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia|];
         apply Forall_cons; [eapply aconst_ok_aapp; [exact AAP| lia| lia]|];
         apply Forall_cons; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia| apply Forall_nil]) end.
    eapply evt_cut.
    { unfold set_shadow_f8_stmt, set_shadow_stmt in SF8. eapply SF8 with (n := 256); [reflexivity| reflexivity| lia| change (Z.to_nat 256) with 256%nat; exact SH256| assumption| exact ACc]. }
    intros ms2 (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2 & MI2 & SHP).
    retpc. change (Z.to_nat 256) with 256%nat in SHP.
    (* [comment removed for export] *)
    eapply rw_cells_transport in SL; [| exact MU2| exact WM2| cbn [cells_size csize Nat.add length disjoint_from fst snd Z.of_nat Pos.of_succ_nat Pos.succ]; lia].
    eapply rw_cells_transport in FRM; [| exact MU2| exact WM2| cbn [cells_size csize Nat.add length disjoint_from fst snd Z.of_nat Pos.of_succ_nat Pos.succ]; lia].
    eapply rw_cells_transport in SH8; [| exact MU2| exact WM2| cbn [cells_size csize Nat.add length disjoint_from fst snd Z.of_nat Pos.of_succ_nat Pos.succ]; lia].
    eapply rw_cells_transport in SH248; [| exact MU2| exact WM2| cbn [cells_size csize Nat.add length disjoint_from fst snd Z.of_nat Pos.of_succ_nat Pos.succ]; lia].
    assert (MU02 : munch [(q, q + 344); (ff, ff + 4096); (Z.shiftr ff 3 + 2147450880, Z.shiftr ff 3 + 2147450880 + 512)] m m2).
    { eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MU2]]. intros z Hz; cbn in Hz |- *; lia. }
    pose proof (wmono_trans asegs _ _ _ WM WM2) as WM02. clear MU WM MI ACc MU2 WM2. rename MI2 into MI. rename MU02 into MU. rename WM02 into WM.
    (* [comment removed for export] *)
    go.
    (* [comment removed for export] *)
    br. go. br.
    (* [comment removed for export] *)
    go.
    (* [comment removed for export] *)
    step.
    (* [comment removed for export] *)
    match type of SH8 with rw_cells _ ?mx ?ax [?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8; ?c9; ?c10] =>
      apply (rw_cells_merge asegs mx ax [] [c1; c2; c3; c4] [c5; c6; c7; c8; c9; c10]) in SH8;
      apply (rw_cells_merge asegs mx ax [CB (cells_size [c1; c2; c3; c4]) (cells_bytes [c1; c2; c3; c4]); c5] [c6; c7; c8] [c9; c10]) in SH8;
      cbn [cells_size csize cells_bytes cbytes app Nat.add] in SH8 end.
    match type of SH248 with rw_cells _ ?mx ?ax (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?c13 :: ?c14 :: ?c15 :: ?c16 :: ?cz :: ?rest) =>
      apply (rw_cells_merge asegs mx ax [] [c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13; c14; c15; c16] (cz :: rest)) in SH248;
      cbn [cells_size csize app Nat.add] in SH248;
      lazymatch type of SH248 with rw_cells _ _ _ (?c16s :: cz :: ?rest') =>
        rewrite <- (app_nil_r rest') in SH248; apply (rw_cells_merge asegs mx ax [c16s; cz] rest' []) in SH248; cbn [cells_size csize app Nat.add] in SH248 end end.
    rw_join SHP SH248 SHQ. rw_join SH8 SHQ SHALL.
    lazymatch type of SL with context [Z_to_bv 64 (Z.shiftr ff 3 + ?k)] =>
      replace (Z.shiftr ff 3 + k) with (Z.shiftr ff 3 + 2147450880 + 10) in SL by lia end.
    replace (Z.shiftr ff 3 + 2147450880 + 512) with (Z.shiftr ff 3 + 2147451392) in MU by lia.
    apply evt_done. eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _. eexists _, _, _, _, _, _, _.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split; [exact SL|]. split; [exact FRM|]. split; [exact SHALL|].
    eapply ACONST_frame; [exact AC| exact MU| exact WM|].
    apply Forall_cons; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia|].
    apply Forall_cons; [eapply aconst_ok_aapp; [exact AAP| lia| lia]|].
    apply Forall_cons; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia| apply Forall_nil].
  Qed.

  (* [comment removed for export] *)
  Definition arp_slotsQ (j0 j1 j2 j3 j4 : list byte) (st ff : Z) : list cell :=
    [CB 16 j0; CB 128 j1; C8 (wz (Z.shiftr ff 3 + ASHB + 10)); C8 (wz ff); CB 16 j2; C8 (wz ASHB); CB 32 j3; C8 (wz ff); CB 120 j4].
  (* [comment removed for export] *)
  Definition arp_slotsL (j0 j1 j3 j4 : list byte) (st ff shf A : Z) : list cell :=
    [CB 16 j0; CB 80 j1; C8 (wz 0); C8 (wz (ff + 80)); C8 (wz (ff + 64)); C8 (wz 0); C8 (wz st); C8 (wz (ff + 32));
     C8 (wz (shf + 10)); C8 (wz ff); C8 (wz ff); C8 (wz ARP_FILE); C8 (wz ASHB); C8 (wz A); CB 24 j3; C8 (wz ff); CB 120 j4].

  (* [comment removed for export] *)
  Lemma arp_seg2 :
    forall (rax s0w a1 a2 a3 a4 a5 a6 a7 s2w s4w s5w t0 t1 t2 t3 t4 t5 t6 gp tp : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (q ff fp st mb A shf s9v s11v : Z) (j0 j1 j2 j3 j4 : list byte),
      0 < A < 2^64 -> 0 <= q -> q + 432 <= 2^64 ->
      rw_cells asegs m q (arp_slotsP j0 j1 j2 j3 j4 st ff) -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1 j2',
          ms' = MS (mkR (Z_to_bv 64 ARP_R2) (Z_to_bv 64 q) gp tp t0 t1 t2
                       s0w (Z_to_bv 64 q) (Z_to_bv 64 mb) a1 a2 a3 a4 a5 a6 a7
                       s2w (Z_to_bv 64 shf) (Z_to_bv 64 A) s5w (Z_to_bv 64 mb) (Z_to_bv 64 st)
                       (Z_to_bv 64 ff) (Z_to_bv 64 s9v) (Z_to_bv 64 ff) (Z_to_bv 64 s11v) t3 t4 t5 t6)
                   F (Z_to_bv 64 P_BIO_eof) fc None m1 (seg_rom asegs)
          /\ munch [(q, q + 344)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ rw_cells asegs m1 q (arp_slotsQ j0 j1 j2' j3 j4 st ff))
        (MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7
                 s2w (Z_to_bv 64 shf) s4w s5w (Z_to_bv 64 mb) (Z_to_bv 64 st)
                 (Z_to_bv 64 ff) (Z_to_bv 64 s9v) (Z_to_bv 64 ff) (Z_to_bv 64 s11v) t3 t4 t5 t6)
            F (Z_to_bv 64 ARP_R1) fc None m (seg_rom asegs)).
  Proof.
    intros until j4. intros AR Q1 Q2 SL MI. unfold ARP_R1, ARP_R2, P_BIO_eof. unfold ASHB in *.
    pose proof (munch_refl [(q, q + 344)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold arp_slotsP, wz in SL.
    go. br. go. step.
    apply evt_done. eexists _, _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    unfold arp_slotsQ, wz. exact SL.
  Qed.

  (* [comment removed for export] *)
  Lemma arp_seg3 :
    forall (rax s0w a1 a2 a3 a4 a5 a6 a7 s2w t0 t1 t2 t3 t4 t5 t6 gp tp : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (q ff st mb A : Z) (j0 j1 j2 j3 j4 : list byte),
      0 < A < 2^64 -> 0 <= q -> q + 432 <= 2^64 -> 0 <= ff -> ff + 4096 < 2^64 ->
      rw_cells asegs m q (arp_slotsQ j0 j1 j2 j3 j4 st ff) -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1 j1',
          ms' = MS (mkR (Z_to_bv 64 ARP_R3) (Z_to_bv 64 q) gp tp t0 t1 t2
                       s0w (Z_to_bv 64 q) (Z_to_bv 64 mb) (Z_to_bv 64 A) (Z_to_bv 64 OSSL_ECH_BUFCHUNK) (Z_to_bv 64 (ff + 2256)) a4 a5 a6 a7
                       (Z_to_bv 64 OSSL_ECH_BUFCHUNK) (Z_to_bv 64 (Z.shiftr ff 3 + ASHB)) (Z_to_bv 64 A) (Z_to_bv 64 0) (Z_to_bv 64 mb) (Z_to_bv 64 A)
                       (Z_to_bv 64 32) (Z_to_bv 64 (ff + 2256)) (Z_to_bv 64 ff) (Z_to_bv 64 0) t3 t4 t5 t6)
                   F (Z_to_bv 64 P_BIO_read_ex) fc None m1 (seg_rom asegs)
          /\ munch [(q, q + 344)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ rw_cells asegs m1 q (arp_slotsL j0 j1' (skipn 8 j3) j4 st ff (Z.shiftr ff 3 + ASHB) A))
        (MS (mkR rax (Z_to_bv 64 q) gp tp t0 t1 t2 s0w (Z_to_bv 64 q) (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                 s2w (Z_to_bv 64 (Z.shiftr ff 3 + ASHB)) (Z_to_bv 64 A) (Z_to_bv 64 0) (Z_to_bv 64 mb) (Z_to_bv 64 st)
                 (Z_to_bv 64 ff) (Z_to_bv 64 (ff + 2256)) (Z_to_bv 64 ff) (Z_to_bv 64 0) t3 t4 t5 t6)
            F (Z_to_bv 64 ARP_R2) fc None m (seg_rom asegs)).
  Proof.
    intros until j4. intros AR Q1 Q2 F1 F2 SL MI. unfold ARP_R2, ARP_R3, P_BIO_read_ex, OSSL_ECH_BUFCHUNK, ARP_FILE. unfold ASHB in *.
    pose proof (munch_refl [(q, q + 344)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (SHR : 0 <= Z.shiftr ff 3 <= ff) by (rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]).
    unfold arp_slotsQ, wz in SL.
    (* [comment removed for export] *)
    go.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    step.
    apply evt_done. eexists _, _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    unfold arp_slotsL, wz. exact SL.
  Qed.

  (* [comment removed for export] *)
  Definition arp_sg1 (w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 : word) : list cell :=
    [C8 w16; C8 w24; C8 w32; C8 w40; C8 w48; C8 w56; C8 w64; C8 w72; C8 w80; C8 w88; C8 w96; C8 w104; C8 w112; C8 w120; C8 w128; C8 w136].
  Definition arp_sg2 (w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 : word) : list cell :=
    [C8 w144; C8 w152; C8 w160; C8 w168; C8 w176; C8 w184; C8 w192; C8 w200; C8 w208; C8 w216; C8 w224; C8 w232].
  Definition arp_sg3 (w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336 : word) : list cell :=
    [C8 w240; C8 w248; C8 w256; C8 w264; C8 w272; C8 w280; C8 w288; C8 w296; C8 w304; C8 w312; C8 w320; C8 w328; C8 w336].
  (* [comment removed for export] *)
  Definition arp_sg2L (w192 w200 w208 w224 w232 : word) (ff shf A : Z) : list cell :=
    arp_sg2 (wz (shf + 10)) (wz ff) (wz ff) (wz ARP_FILE) (wz ASHB) (wz A) w192 w200 w208 (wz ff) w224 w232.

  Lemma le8_of_bytes : forall bs : list byte, length bs = 8%nat -> exists w : word, le8 w = bs.
  Proof.
    intros bs L. exists (le_bytes_to_word bs). unfold le8, word_to_le_bytes, le_bytes_to_word.
    rewrite Z_to_bv_unsigned. pose proof (bytes_le_to_Z_bound bs) as B. pose proof (bytes_le_to_Z_nonneg bs) as B0. rewrite L in B.
    change (bv_wrap 64 ?x) with (x mod 2^64). rewrite Z.mod_small by (cbn in B; clear - B B0; lia). rewrite <- L. apply Z_to_le_bytes_to_Z.
  Qed.
  (* [comment removed for export] *)
  Lemma CB_words : forall (n : nat) m A (j : list byte) post,
    rw_cells asegs m A (CB (8 * n) j :: post) -> exists ws : list word, length ws = n /\ rw_cells asegs m A (map C8 ws ++ post).
  Proof.
    induction n as [|n IH]; intros m A j post RC; pose proof RC as [[WF _] _]; cbn [cells_wf cell_wf csize length] in WF; destruct WF as [LJ WFP].
    - exists []. split; [reflexivity|]. cbn [map app]. destruct j; [| cbn in LJ; lia].
      eapply arw_cells_recut; [exact RC| exact WFP| reflexivity].
    - replace (8 * S n)%nat with (8 + 8 * n)%nat in RC by lia.
      pose proof (rw_cells_split_CB asegs m A [] (8 + 8 * n) j post [8%nat; (8 * n)%nat] RC ltac:(cbn [sum_nat]; lia)) as RC2. cbn [mk_CB_cells app] in RC2.
      destruct (le8_of_bytes (firstn 8 j) ltac:(rewrite length_firstn; lia)) as [w Hw].
      pose proof (proj1 (rw_cells_app asegs m A [CB 8 (firstn 8 j)] (CB (8 * n) (firstn (8 * n) (skipn 8 j)) :: post)) RC2) as [R1 R2].
      cbn [cells_size csize Nat.add] in R2.
      destruct (IH m _ _ post R2) as (ws & LW & RW).
      exists (w :: ws). split; [cbn [length]; lia|]. cbn [map app].
      apply (proj2 (rw_cells_app asegs m A [C8 w] (map C8 ws ++ post))). split.
      + eapply arw_cells_recut; [exact R1| cbn [cells_wf]; split; [reflexivity| exact I]| cbn [cells_bytes cbytes app]; rewrite !app_nil_r, Hw; reflexivity].
      + cbn [cells_size csize Nat.add]. exact RW.
  Qed.
  Local Ltac lenD ws LEN := destruct ws as [|? ws]; [cbn in LEN; exfalso; lia| cbn [length] in LEN].
  Local Ltac lenE ws LEN := destruct ws; [| cbn in LEN; exfalso; lia].

  (* [comment removed for export] *)
  Lemma arp_slots_split : forall m q (j0 j1 j3 j4 : list byte) (st ff shf A : Z),
    rw_cells asegs m q (arp_slotsL j0 j1 j3 j4 st ff shf A) ->
    exists (w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w192 w200 w208 w224 w232 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336 : word),
         rw_cells asegs m q [CB 16 j0]
      /\ rw_cells asegs m (q + 16) (arp_sg1 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 (wz 0) (wz (ff + 80)) (wz (ff + 64)) (wz 0) (wz st) (wz (ff + 32)))
      /\ rw_cells asegs m (q + 144) (arp_sg2L w192 w200 w208 w224 w232 ff shf A)
      /\ rw_cells asegs m (q + 240) (arp_sg3 w240 w248 w256 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336).
  Proof.
    intros m q j0 j1 j3 j4 st ff shf A SL. unfold arp_slotsL in SL.
    match type of SL with rw_cells _ _ _ (?c0 :: ?rest) => change (rw_cells asegs m q ([c0] ++ rest)) in SL end.
    apply (proj1 (rw_cells_app _ _ _ _ _)) in SL. destruct SL as [S0 SL]. cbn [cells_size csize Nat.add] in SL. change (Z.of_nat 16) with 16 in SL.
    change 80%nat with (8 * 10)%nat in SL. destruct (CB_words 10 _ _ _ _ SL) as (ws & LEN & SL1). clear SL.
    lenD ws LEN. lenD ws LEN. lenD ws LEN. lenD ws LEN. lenD ws LEN. lenD ws LEN. lenD ws LEN. lenD ws LEN. lenD ws LEN. lenD ws LEN. lenE ws LEN.
    cbn [map app] in SL1.
    match type of SL1 with rw_cells _ _ _ (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?c13 :: ?c14 :: ?c15 :: ?c16 :: ?rest) =>
      change (rw_cells asegs m (q + 16) ([c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13; c14; c15; c16] ++ rest)) in SL1 end.
    apply (proj1 (rw_cells_app _ _ _ _ _)) in SL1. destruct SL1 as [S1 SL2]. cbn [cells_size csize Nat.add] in SL2. change (Z.of_nat 128) with 128 in SL2.
    replace (q + 16 + 128) with (q + 144) in SL2 by lia.
    (* [comment removed for export] *)
    match type of SL2 with rw_cells _ _ _ (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?rest) =>
      change (rw_cells asegs m (q + 144) ([c1; c2; c3; c4; c5; c6] ++ rest)) in SL2 end.
    apply (proj1 (rw_cells_app _ _ _ _ _)) in SL2. destruct SL2 as [S2a SL3]. cbn [cells_size csize Nat.add] in SL3. change (Z.of_nat 48) with 48 in SL3.
    replace (q + 144 + 48) with (q + 192) in SL3 by lia.
    change 24%nat with (8 * 3)%nat in SL3. destruct (CB_words 3 _ _ _ _ SL3) as (ws1 & LEN1 & SL4). clear SL3.
    lenD ws1 LEN1. lenD ws1 LEN1. lenD ws1 LEN1. lenE ws1 LEN1. cbn [map app] in SL4.
    match type of SL4 with rw_cells _ _ _ (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?rest) => change (rw_cells asegs m (q + 192) ([c1; c2; c3; c4] ++ rest)) in SL4 end.
    apply (proj1 (rw_cells_app _ _ _ _ _)) in SL4. destruct SL4 as [S2b SL5]. cbn [cells_size csize Nat.add] in SL5. change (Z.of_nat 32) with 32 in SL5.
    replace (q + 192 + 32) with (q + 224) in SL5 by lia.
    change 120%nat with (8 * 15)%nat in SL5. destruct (CB_words 15 _ _ _ _ SL5) as (ws3 & LEN3 & SL6). clear SL5.
    lenD ws3 LEN3. lenD ws3 LEN3. lenD ws3 LEN3. lenD ws3 LEN3. lenD ws3 LEN3. lenD ws3 LEN3. lenD ws3 LEN3. lenD ws3 LEN3. lenD ws3 LEN3. lenD ws3 LEN3. lenD ws3 LEN3. lenD ws3 LEN3. lenD ws3 LEN3. lenD ws3 LEN3. lenD ws3 LEN3. lenE ws3 LEN3.
    cbn [map app] in SL6.
    match type of SL6 with rw_cells _ _ _ (?c1 :: ?c2 :: ?rest) => change (rw_cells asegs m (q + 224) ([c1; c2] ++ rest)) in SL6 end.
    apply (proj1 (rw_cells_app _ _ _ _ _)) in SL6. destruct SL6 as [S2c SL7]. cbn [cells_size csize Nat.add] in SL7. change (Z.of_nat 16) with 16 in SL7.
    replace (q + 224 + 16) with (q + 240) in SL7 by lia.
    rw_join S2a S2b S2ab. rw_join S2ab S2c S2.
    do 28 eexists. split; [exact S0|]. split; [exact S1|]. split; [unfold arp_sg2L, arp_sg2; exact S2| exact SL7].
  Qed.
End S.
