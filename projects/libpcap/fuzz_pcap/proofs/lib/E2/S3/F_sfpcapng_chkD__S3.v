(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool String Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Tac Arr Bytes ZBridge ITree Nodes Decode SysStep MonadX Image ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI PcapRep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcap_chkA__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_pcap_err__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_aiE__S3.
From OSSVerify.libpcap.fuzz_pcap.images Require Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3 Require F_sfpcap_chkF__U3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3 Require F_sfpcapng_ai__U3.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require KeepHyps.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_ngnextA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Startup_B__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_ngnextD__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3 Require NgnPure.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module F_sfpcapng_chkD.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep MonadX Image ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcap_chkA__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_pcap_err__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_aiE__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface_ng OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_blkA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_aiA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_sfpcapng_chkA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_chkF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_chkC.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia_e2w2_base := first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                                 | zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac ceil_mentioned := lazymatch goal with | |- context [@alloc_ceiling _] => idtac | _ : context [@alloc_ceiling _] |- _ => idtac end.
(* [comment removed for export] *)
Local Ltac gio_ceil_fact :=
  match goal with
  | G : GIo _ _ _ _ _ _ |- _ => let H := fresh "CLO__" in pose proof (PcapRep.GIo_ceil_lo _ _ _ _ _ _ G) as H; unfold rc_lo in H
  end.
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try gio_ceil_fact; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Lemma bt_minus2_ltu : forall bt, (0 <= bt < 2^32)%Z ->
  ((bv_unsigned (Z_to_bv 64 (s32 bt + -2)) <? 2) = ((bt =? 2) || (bt =? 3)))%Z.
Proof using Type. pin_using tt.
  intros bt Hbt. rewrite unsigned_lit_wrap. unfold s32.
  destruct (Z.eq_dec bt 2) as [->|N2]; [reflexivity|]. destruct (Z.eq_dec bt 3) as [->|N3]; [reflexivity|].
  rewrite (proj2 (Z.eqb_neq _ _) N2), (proj2 (Z.eqb_neq _ _) N3). cbn [orb]. apply Z.ltb_ge.
  change (bv_modulus 64) with (2^64)%Z. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
End WithCeil.

Ltac prsMG GL := intros a Ha; rewrite cells_size_map_C1, GL in Ha; cbn [outside]; repeat match goal with |- _ /\ _ => split end; fastfirst (first [lia | left; lia | exact Logic.I]).

(* [comment removed for export] *)
Lemma msg_ok_b : forall l : list Z, forallb (fun z => (0 <? z)%Z && (z <? 256)%Z) l = true -> Forall (fun z => 0 < z < 256)%Z l.
Proof. intros l H. apply Forall_forall. intros x Hx. rewrite forallb_forall in H. specialize (H x Hx). apply andb_prop in H as [H1 H2].
  apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. lia. Qed.
Ltac msg_ok := first [ apply msg_ok_b; vm_compute; reflexivity
                     | vm_compute; repeat first [apply Forall_nil | apply Forall_cons; [split; reflexivity|]] ].

Section WithCeil.
Context {CEILV : CEIL}.
Lemma eqb_s32_lit : forall bt k, (0 <= bt < 2^32)%Z -> (0 <= k < 2^31)%Z -> bv_eqb (Z_to_bv 64 (s32 bt)) (Z_to_bv 64 k) = (bt =? k)%Z.
Proof using Type. pin_using tt.
  intros bt k Hb Hk. replace (Z_to_bv 64 k) with (Z_to_bv 64 (s32 k)) by (rewrite (s32_small k) by lia; reflexivity).
  apply eqb_s32; lia.
Qed.

Section ChkNgD.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation PS := (PState H hptr).
  #[local] Notation pcapT := (PcapTypes.pcap hptr hptr).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HPL : heap_perm_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis FREE : free_stmt_o HO K.
  Hypothesis SNPRINTF : snprintf_spec_stmt K.
  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : mem) (R : rctx) (s : PS) (CL FB : list cblk) (lo MG FA EB ERR : Z) (f : hptr) (magic : list Z).
  Hypothesis CTX : ngc_ctx K sites sp tp R s CL FB lo MG FA EB ERR f magic m.
  #[local] Notation POSTQ := (check_header_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL FB lo MG EB ERR magic f m (ps_outfile s)).
  #[local] Notation AGQ := (ngc_AGQ sp CL EB ERR m).
  #[local] Notation FRS := (ngc_FRS ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9).
  #[local] Notation PR := (prims HO fo_nop sites).
  (* [comment removed for export] *)
  Variables (qs : hptr) (P : Z) (sw : bool) (BS0 MINOR : Z) (ew : word).
  Hypothesis P14 : 0 < P /\ P + 680 <= CEILZ.
  Hypothesis P16 : P mod 16 = 0.
  Hypothesis P5 : out_of_image P 680.
  Hypothesis BS0R : 1 <= BS0 <= 2^21.
  Hypothesis MINR : 0 <= MINOR < 2^16.

  #[local] Notation pL := (ngc_p f qs sw BS0 MINOR).
  #[local] Notation hcells := (ngc_hcells P sw BS0 MINOR).

  Open Scope bv_scope.

  Hypothesis RB : read_block_stmt HO K sites.
  Hypothesis AI : add_interface_stmt HO K sites.

  (* [comment removed for export] *)
  Lemma hcells_rebuf : forall mX mY B B',
    rw_cells ssegs mX P (hcells B) ->
    agrees_on (fun a => (P <= a < P + 24 \/ P + 32 <= a < P + 648)%Z) mX mY ->
    rw_cells ssegs mY (P + 24) [C8 (Z_to_bv 64 B')] -> rw_cells ssegs mY P (hcells B').
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt).
    intros mX mY B B' HC AG HB. unfold ngc_hcells, ngcells in HC |- *.
    destruct (rw_cells_cut _ _ _ 4 HC) as [A X]. destruct (rw_cells_cut _ _ _ 1 X) as [_ C]. clear X. cbn [firstn skipn cells_size csize Nat.add app] in A, C.
    transport A mY AG ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; lia).
    transport C mY AG ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; lia).
    replace (P + 24)%Z with (P + Z.of_nat 24)%Z in HB by lia.
    pose proof (rw_cells_uncut _ _ _ _ _ A HB ltac:(cbn; lia)) as AB.
    exact (rw_cells_uncut _ _ _ _ _ AB C ltac:(cbn; lia)).
  Qed.
  Lemma hcells_cut20 : forall mX B,
    rw_cells ssegs mX P (hcells B) -> rw_cells ssegs mX (P + 20) [C4 (Z_to_bv 64 BS0); C8 (Z_to_bv 64 B)].
  Proof using Type. pin_using tt.
    intros mX B HC. unfold ngc_hcells, ngcells in HC.
    destruct (rw_cells_cut _ _ _ 3 HC) as [_ X]. destruct (rw_cells_cut _ _ _ 2 X) as [X1 _]. cbn [firstn skipn cells_size csize Nat.add app] in X1.
    replace (P + 20)%Z with (P + Z.of_nat 20)%Z by lia. exact X1.
  Qed.
  Lemma ngcells_cut656 : forall mX sg I pad,
    rw_cells ssegs mX (P + 648) (ng_cells sg I pad) -> rw_cells ssegs mX (P + 656) [C4 (Z_to_bv 64 (ng_max_blocksize sg))].
  Proof using Type. pin_using tt.
    intros mX sg I pad HN. unfold ng_cells in HN. destruct (rw_cells_cut _ _ _ 1 HN) as [_ X]. destruct (rw_cells_cut _ _ _ 1 X) as [X1 _].
    cbn [firstn skipn cells_size csize Nat.add app] in X1. replace (P + 656)%Z with (P + 648 + Z.of_nat 8)%Z by lia. exact X1.
  Qed.

  (* [comment removed for export] *)
  Definition NGI (m3 : mem) (ps3 : PS) (qb : hptr) (B bufalloc : Z) (bufdata : list Z) (sg : pcap_ng_sf) (i : option hptr) (I : Z)
             (pad bs e : list byte) (hc : list cell) : Prop :=
    mem_inv ssegs m3 /\ stk ssegs m3 lo (bv_unsigned sp + -128) /\ AGQ m3 /\
    GIo K R ps3 (IBLK i I sg ++ (qs, P, 680%Z) :: (qb, B, bufalloc) :: CL) FB m3 /\ ps_outfile ps3 = ps_outfile s /\
    rw_cells ssegs m3 (bv_unsigned sp + -128) hc /\ cells_size hc = 40%nat /\ FRS m3 /\
    rw_cells ssegs m3 ERR [C4 ew] /\ rw_cells ssegs m3 MG (map (fun z => C1 (Z_to_bv 8 z)) magic) /\ rw_cells ssegs m3 EB [CB 256 e] /\
    rw_cells ssegs m3 P (hcells B) /\ rw_cells ssegs m3 (P + 648) (ng_cells sg I pad) /\
    ng_user_tsresol sg = 1000000%Z /\ ng_max_blocksize sg = INITIAL_MAX_BLOCKSIZE /\ (0 <= ng_ifcount sg < 2^32)%Z /\ (0 <= ng_ifaces_size sg < 2^32)%Z /\
    ifaces_ok (pL qb bufalloc bufdata sg i) I m3 /\
    rw_cells ssegs m3 B [CB (Z.to_nat bufalloc) bs] /\ firstn (length bufdata) bs = map b8 bufdata /\
    (Z.of_nat (length bufdata) <= bufalloc)%Z /\ (0 <= bufalloc < 2^32)%Z /\ (BS0 <= bufalloc)%Z /\ Forall (fun z => 0 <= z < 256)%Z bufdata.

  Lemma ngc_loop : forall (fuel : nat) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' x8 : word) (m3 : mem) (ps3 : PS)
           (qb : hptr) (B bufalloc : Z) (bufdata : list Z) (sg : pcap_ng_sf) (i : option hptr) (I : Z) (pad bs e : list byte) (hc : list cell),
      bv_unsigned x8 = (2^64 - 1)%Z ->
      NGI m3 ps3 qb B bufalloc bufdata sg i I pad bs e hc ->
      implM ssegs (ngc_find MOps PR fuel 0 (pL qb bufalloc bufdata sg i)) ps3 POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 ERR) (Z_to_bv 64 EB) a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 P) (Z_to_bv 64 FA) (Z_to_bv 64 2) (Z_to_bv 64 1) (Z_to_bv 64 (P + 648)) (Z_to_bv 64 1) x8 (Z_to_bv 64 6) s10 s11 t3' t4' t5' t6')
            F (Z_to_bv 64 0x16950) fc None m3 (seg_rom ssegs)).
  Proof using AI BS0R CTX FREE HFL HPL MINR P14 P16 RB SFL SNPRINTF. pin_using (fun (AI BS0R CTX FREE HFL HPL MINR P14 P16 RB SFL SNPRINTF : unit) => tt).
    induction fuel as [|fuel IH]; intros until hc; intros X8 IV.
    { unfold ngc_find. cbn [ng_find_idb]. apply (implM_unr ssegs). }
    destruct IV as (MI3 & ST3 & AG3 & G3 & OF3 & HC3 & Hhc & FRS3 & ERR3 & MG3 & HEB3 & CELLS & NG3 & UTS & MB & IC & IS & HIF & BUF3 & PFX & LENB & BAR & BSB & GRD).
    pose proof CTX as (G & LO & BU & SPM & TP & ALN & HinF & SITES & GL & GR & R1 & R2 & R3 & E1 & E2 & D1 & E8).
    pose proof (GIo_spw K _ _ _ _ _ G) as SPW. pose proof (GIo_sp47 K _ _ _ _ _ G) as SP47. pose proof (bv_unsigned_in_range 64 sp) as RSP. change (bv_modulus 64) with (2^64)%Z in RSP.
    pose proof E2 as EBU. unfold rc_spmain in EBU.
    destruct P14 as [P1 P4].
    destruct (ngl_facts K HPL _ _ _ _ _ _ _ _ _ _ _ _ _ G3 ltac:(lia)) as ((B1 & B2 & B4) & APB & API & NPB).
    assert (CLB : forall a, in_block CL a -> (a < CEILZ)%Z).
    { intros a Ha. destruct (GIo_CLc_facts K R s CL [] FB m a ltac:(rewrite app_nil_r; exact G) Ha) as [Hc _]. exact (proj2 Hc). }
    assert (HI : match i with Some _ => True | None => I = 0%Z end).
    { unfold ifaces_ok in HIF. cbn [pc_priv ngc_p] in HIF. destruct i; [exact Logic.I| exact (proj1 HIF)]. }
    assert (IR : (0 <= I < 2^64)%Z) by (destruct i as [q|]; [destruct (API sg q eq_refl) as (I1 & I4 & _); lia| cbn in HI; lia]).
    (* [comment removed for export] *)
    unfold ngc_find. rewrite (ng_find_idb_S MOps PR). apply (implM_bind_assoc ssegs). fold (ngc_find MOps PR fuel 0).
    (* [comment removed for export] *)
    destruct (rw_cells_forget _ _ _ _ HC3) as [hj HC']. clear HC3. rewrite Hhc in HC'.
    pose proof (rw_cells_split_CB _ _ _ [] _ _ [] [8%nat; 24%nat; 8%nat] HC' ltac:(cbn; lia)) as HC''. clear HC'. cbn [mk_CB_cells app] in HC''.
    destruct (rw_cells_cut _ _ _ 1 HC'') as [HD X]. destruct (rw_cells_cut _ _ _ 1 X) as [HCUR HTL]. clear HC'' X.
    cbn [firstn skipn cells_size csize Nat.add app] in HD, HCUR, HTL.
    replace (bv_unsigned sp + -128 + Z.of_nat 8)%Z with (bv_unsigned sp + -120)%Z in HCUR by lia.
    replace (bv_unsigned sp + -128 + Z.of_nat 8 + Z.of_nat 24)%Z with (bv_unsigned sp + -96)%Z in HTL by lia.
    pose proof (hcells_cut20 _ _ CELLS) as HBS. pose proof (proj2 (hcells_cut _ _ _ _ _ _ CELLS)) as HPV. pose proof (ngcells_cut656 _ _ _ _ NG3) as HMB.
    hide HD. hide HTL. hide FRS3. hide ERR3. hide MG3. hide HEB3. hide CELLS. hide NG3. hide BUF3. hide HCUR. hide HBS. hide HPV. hide HMB.
    unfold implM. iprefix.
    do 5 step.
    unhide HEB3. unhide BUF3. unhide HCUR. unhide HBS. unhide HPV. unhide HMB.
    rewrite (ngl_assoc_rb i I sg qs P qb B bufalloc CL) in G3.
    apply evt_done. name_sp sp (-128)%Z. eapply (implM_bind ssegs).
    { eapply (RB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 R ps3 (IBLK i I sg ++ [(qs, P, 680%Z)]) CL FB f FA P B (bv_unsigned sp + -120)%Z EB lo
                 (pL qb bufalloc bufdata sg i) sg i (DStack SiteBhdrCheckHeader 0) bs e);
        [ split; [exact G3|]; split; [rewrite Hsp; exact ST3|]; split; [unfold rc_lo; lia|]; split; [unfold READ_BLOCK_STACK, PCAP_L1_STACK; rewrite Hsp; lia|];
          split; [rewrite Hsp; lia|]; split; [exact MI3|]; split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]
        | exact HinF | reflexivity | reflexivity
        | apply in_or_app; left; apply in_or_app; right; left; reflexivity
        | intros st'; cbn [eval_rdest fo_site fo_nop prims]; rewrite SITES, Hsp; unfold sites_at, D_CHECK_HEADER; lia
        | reflexivity | reflexivity | rewrite ?Hsp; f_equal; lia | reflexivity
        | split; [exact HBS|]; split; [exact HPV|]; split; [exact HMB|]; rewrite MB; unfold INITIAL_MAX_BLOCKSIZE; cbn [pc_bufsize pc_bufalloc ngc_p]; lia
        | exact BUF3 | exact PFX | cbn [pc_bufdata pc_bufalloc ngc_p]; lia
        | exact HCUR | reflexivity | rewrite ?Hsp; lia | lia | rewrite ?Hsp; apply aligned16_8; [exact ALN| reflexivity]
        | exact HEB3 | left; rewrite Hsp; lia | exact E8 ]. }
    intros rb ps4 ms4 PO.
    destruct PO as (a0v & m4 & p' & B' & bs' & E & OF4 & MI4 & ST4 & AG4 & G4 & BH4 & BUF4 & PFX4 & LEN4 & Q1 & Q2 & Q3 & Q4 & Q5 & SM & RM).
    unfold hpost_regs in E. destruct_exs E. subst ms4. rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 0x16964)) with (Z_to_bv 64 0x16964) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    (* [comment removed for export] *)
    destruct p' as [f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17]. unfold same_meta in SM.
    cbn [pc_priv pc_rfile pc_self pc_bufsize pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext
         pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_buffer pc_bufalloc pc_bufdata ngc_p] in Q1, Q2, Q3, Q4, Q5, SM, RM, G4, BH4, BUF4, PFX4, LEN4.
    destruct SM as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9). subst f1 f2 f3 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17.
    rename f4 into bufalloc'. rename f5 into qb'. rename f6 into bufdata'.
    (* [comment removed for export] *)
    assert (INP4 : forall a, (P <= a < P + 680)%Z -> in_block ((IBLK i I sg ++ [(qs, P, 680%Z)]) ++ CL) a).
    { intros a Ha. apply (proj2 (in_block_app _ _ _)). left. apply (proj2 (in_block_app _ _ _)). right. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    assert (INI4 : forall sg' q, PrivNg sg i = PrivNg sg' (Some q) -> forall a, (I <= a < I + 40 * ng_ifaces_size sg')%Z -> in_block ((IBLK i I sg ++ [(qs, P, 680%Z)]) ++ CL) a).
    { intros sg' q E a Ha. injection E as Ei Es. subst i sg'. apply (proj2 (in_block_app _ _ _)). left. apply (proj2 (in_block_app _ _ _)). left.
      unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    pose proof (GIo_perm K HPL _ _ _ _ _ _ G4 (ngl_perm_rb i I sg qs P qb' B' bufalloc' CL)) as G4'. clear G4.
    destruct (ngl_facts K HPL _ _ _ _ _ _ _ _ _ _ _ _ _ G4' ltac:(unfold blk_handle in BH4; cbn [pc_bufsize pc_bufalloc ngc_p] in BH4; lia)) as ((B1' & B2' & B4') & APB' & API' & NPB').
    unhide HD. unhide HTL. unhide FRS3. unhide ERR3. unhide MG3. unhide CELLS. unhide NG3.
    transport HD m4 AG4 ltac:(prs). transport HTL m4 AG4 ltac:(prs). unfold ngc_FRS in FRS3. transport FRS3 m4 AG4 ltac:(prs).
    transport ERR3 m4 AG4 ltac:(prs). transport MG3 m4 AG4 ltac:(prsMG GL).
    transport NG3 m4 AG4 ltac:(unfold ng_cells; prs).
    assert (CELLS4 : rw_cells ssegs m4 P (hcells B')).
    { eapply hcells_rebuf; [exact CELLS | | ].
      - eapply agrees_on_weaken; [exact AG4|]. intros a Ha. split; [right; apply INP4; lia|]. lia.
      - destruct BH4 as (X & _). destruct (rw_cells_cut _ _ _ 1 X) as [_ X2]. cbn [firstn skipn cells_size csize Nat.add app pc_bufsize ngc_p] in X2.
        replace (P + 24)%Z with (P + 20 + Z.of_nat 4)%Z by lia. exact X2. }
    clear CELLS HBS HPV HMB BUF3 PFX HCUR HEB3.
    assert (HIF4 : ifaces_ok (pL qb' bufalloc' bufdata' sg i) I m4).
    { assert (HIF' : ifaces_ok (pL qb' bufalloc' bufdata' sg i) I m3) by exact HIF.
      eapply ifaces_ok_agree; [exact AG4 | | exact HIF']. intros sg' q E a Ha. cbn [pc_priv ngc_p] in E.
      destruct (API sg' q E) as (I1 & I4 & IP & IB). split; [right; exact (INI4 sg' q E a Ha)|]. lia. }
    clear HIF.
    assert (AG04 : AGQ m4).
    { unfold ngc_AGQ in AG3 |- *. eapply agrees_on_trans; [exact AG3|]. eapply agrees_on_weaken; [exact AG4|].
      intros a [[Ha|Ha] [Hn _]]; [split; [left; lia| lia]|]. pose proof (CLB a Ha). pose proof (NPB a Ha).
      split; [right; apply (proj2 (in_block_app _ _ _)); right; exact Ha| lia]. }
    (* [comment removed for export] *)
    assert (E8T : bv_eqb (Z_to_bv 64 (-1)) x8 = true) by (unfold bv_eqb; rewrite X8; vm_compute; reflexivity).
    assert (E8F0 : bv_eqb (Z_to_bv 64 0) x8 = false) by (unfold bv_eqb; rewrite X8; vm_compute; reflexivity).
    assert (E8F1 : bv_eqb (Z_to_bv 64 1) x8 = false) by (unfold bv_eqb; rewrite X8; vm_compute; reflexivity).
    destruct rb as [p'' | msg p'' | c p''].
    - (* [comment removed for export] *)
      destruct RM as (-> & -> & HEB4 & (ccs' & HCUR4 & Hccs')).
      unfold ngc_K. cbn [mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims]. apply (implM_retb ssegs). unfold ngc_loop_tail.
      hide HD. hide HTL. hide FRS3. hide ERR3. hide MG3. hide HEB4. hide CELLS4. hide NG3. hide BUF4. hide HCUR4.
      unfold implM. iprefix.
      step. rewrite E8F0. cbv iota. step. rewrite (eqb_lits_eq 0 0 eq_refl). cbv iota.
      step. step. step.
      unhide HD. unhide HTL. unhide FRS3. unhide ERR3. unhide MG3. unhide HEB4. unhide CELLS4. unhide NG3. unhide BUF4. unhide HCUR4.
      assert (MSG : fmt_at m4 0x10e35 "the capture file has no Interface Description Blocks"%string)
        by (apply (fmt_at_intro m4 _ _ MI4); [vm_compute; reflexivity| lia| cbn; lia]).
      pose proof (rw_cells_uncut _ _ _ _ _ HD HCUR4 ltac:(cbn; lia)) as J1.
      pose proof (rw_cells_uncut _ _ _ _ _ J1 HTL ltac:(rewrite cells_size_app, Hccs'; cbn; lia)) as HC4.
      apply evt_done.
      eapply (ngc_mcp_fail HO K sites HFL SFL HPL FREE ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m R s CL FB lo MG FA EB ERR f magic CTX qs P sw BS0 MINOR ew (conj P1 P4)
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m4 ps4 0x10e35 53 "the capture file has no Interface Description Blocks"%string Msg.no_idb bufdata' qb' i sg B' I bufalloc' e);
        [ exact MI4 | exact ST4 | exact AG04 | exact G4' | rewrite OF4; exact OF3 | exact HI | exact HC4 | rewrite !cells_size_app, Hccs'; reflexivity | exact FRS3 | exact ERR3 | exact MG3 | exact HEB4
        | exact (proj1 (hcells_cut _ _ _ _ _ _ CELLS4)) | exact (ngcells_cut672 _ _ _ _ _ NG3) | exact IR | unfold blk_handle in BH4; cbn [pc_bufsize pc_bufalloc] in BH4; lia
        | exact MSG | cbn; lia | lia | vm_compute; reflexivity | msg_ok ].
    - (* [comment removed for export] *)
      destruct RM as (-> & -> & (junk4 & HEB4) & LENM & MOK & (ccs' & HCUR4 & Hccs')).
      unfold ngc_K. cbn [mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims]. apply (implM_retb ssegs). unfold ngc_loop_tail. unfold ngc_fail. cbn [e_fenter e_fret fo_enter fo_ret fo_nop prims]. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_free prims free_opt ng_ifaces_ptr_of pc_buffer pc_self pc_priv ngc_p].
      hide HD. hide HTL. hide FRS3. hide ERR3. hide MG3. hide HEB4. hide CELLS4. hide NG3. hide BUF4. hide HCUR4.
      unfold implM. iprefix.
      step. rewrite E8T. cbv iota.
      unhide HD. unhide HTL. unhide FRS3. unhide ERR3. unhide MG3. unhide HEB4. unhide CELLS4. unhide NG3. unhide BUF4. unhide HCUR4.
      pose proof (rw_cells_uncut _ _ _ _ _ HD HCUR4 ltac:(cbn; lia)) as J1.
      pose proof (rw_cells_uncut _ _ _ _ _ J1 HTL ltac:(rewrite cells_size_app, Hccs'; cbn; lia)) as HC4.
      apply evt_done.
      eapply (ngc_fail3 HO K sites HFL SFL FREE ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R s CL FB lo MG FA EB ERR f magic m) with (i := i) (ni := (40 * ng_ifaces_size sg)%Z);
        [ exact CTX | exact MI4 | exact ST4 | exact AG04 | destruct i; exact G4' | exact HI | exact HC4 | rewrite !cells_size_app, Hccs'; reflexivity | exact FRS3 | exact ERR3 | exact MG3 | exact HEB4
        | exact LENM | exact MOK | rewrite OF4; exact OF3 | exact (proj1 (hcells_cut _ _ _ _ _ _ CELLS4)) | exact (ngcells_cut672 _ _ _ _ _ NG3) | exact IR | lia | lia ].
    - (* [comment removed for export] *)
      destruct RM as (-> & -> & HEB4 & (cpad & HCUR4) & COFF & CREM & CR1 & CR2 & CBT & LEN' & GRD').
      set (bt := cur_block_type c) in *.
      hide HD. hide HTL. hide FRS3. hide ERR3. hide MG3. hide HEB4. hide CELLS4. hide NG3. hide BUF4.
      unfold implM. iprefix.
      step. rewrite E8F1. cbv iota. step. rewrite (eqb_lits_false 1 0) by lia. cbv iota.
      step. rewrite (sx32_s32 bt) by lia. step. step.
      unfold bv_ltu. rewrite (unsigned_lit 2), (bt_minus2_ltu bt) by lia.
      (* [comment removed for export] *)
      assert (PKT : forall (a1x : word),
        (bt = 2 \/ bt = 3 \/ bt = 6)%Z ->
        evt ssegs (fun ms1 => impl ssegs (at_node ssegs) (npeek ssegs)
               ((Monad.mbind (ngc_K MOps PR fuel (RB_Ok c (pL qb' bufalloc' bufdata' sg i))) (ngc_loop_tail MOps PR 0)) ps4)
               (epost (fun p0 => POSTQ (fst p0) (snd p0))) ms1)
          (MS (mkR (Z_to_bv 64 0x16964) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp x x0 x1 (Z_to_bv 64 ERR) (Z_to_bv 64 EB) (Z_to_bv 64 (s32 bt)) a1x x3 x4 x5 x6 x7 x9
                   (Z_to_bv 64 P) (Z_to_bv 64 FA) (Z_to_bv 64 2) (Z_to_bv 64 1) (Z_to_bv 64 (P + 648)) (Z_to_bv 64 1) x8 (Z_to_bv 64 6) s10 s11 x10 x11 x12 x13)
              F (Z_to_bv 64 0x16a0c) fc None m4 (seg_rom ssegs))).
      { intros a1x HBT.
        unfold ngc_K. fold bt. replace (bt =? BT_IDB) with false by (symmetry; apply Z.eqb_neq; unfold BT_IDB; lia).
        replace ((bt =? BT_EPB) || (bt =? BT_SPB) || (bt =? BT_PB)) with true
          by (unfold BT_EPB, BT_SPB, BT_PB; destruct HBT as [-> |[-> | ->]]; reflexivity). cbv iota. cbn [mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims].
        do 4 step.
        unhide HD. unhide HTL. unhide FRS3. unhide ERR3. unhide MG3. unhide HEB4. unhide CELLS4. unhide NG3. unhide BUF4.
        assert (MSG : fmt_at m4 0x10aac "the capture file has a packet block before any Interface Description Blocks"%string)
          by (apply (fmt_at_intro m4 _ _ MI4); [vm_compute; reflexivity| lia| cbn; lia]).
        pose proof (rw_cells_uncut _ _ _ _ _ HD HCUR4 ltac:(cbn; lia)) as J1.
        pose proof (rw_cells_uncut _ _ _ _ _ J1 HTL ltac:(cbn; lia)) as HC4.
        apply evt_done. apply (implM_retb ssegs). unfold ngc_loop_tail.
        eapply (ngc_mcp_fail HO K sites HFL SFL HPL FREE ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m R s CL FB lo MG FA EB ERR f magic CTX qs P sw BS0 MINOR ew (conj P1 P4)
                  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m4 ps4 0x10aac 76 "the capture file has a packet block before any Interface Description Blocks"%string Msg.packet_before_idb bufdata' qb' i sg B' I bufalloc' e);
          [ exact MI4 | exact ST4 | exact AG04 | exact G4' | rewrite OF4; exact OF3 | exact HI | exact HC4 | reflexivity | exact FRS3 | exact ERR3 | exact MG3 | exact HEB4
          | exact (proj1 (hcells_cut _ _ _ _ _ _ CELLS4)) | exact (ngcells_cut672 _ _ _ _ _ NG3) | exact IR | unfold blk_handle in BH4; cbn [pc_bufsize pc_bufalloc] in BH4; lia
          | exact MSG | cbn; lia | lia | vm_compute; reflexivity | msg_ok ]. }
      destruct (Z.eq_dec bt 2) as [E2'|N2]; [| destruct (Z.eq_dec bt 3) as [E3|N3]].
      1,2: replace ((bt =? 2) || (bt =? 3)) with true by (symmetry; apply Bool.orb_true_iff; first [left; apply Z.eqb_eq; exact E2' | right; apply Z.eqb_eq; exact E3]); cbv iota.
      1,2: apply PKT; lia.
      replace ((bt =? 2) || (bt =? 3)) with false by (symmetry; rewrite (proj2 (Z.eqb_neq _ _) N2), (proj2 (Z.eqb_neq _ _) N3); reflexivity). cbv iota.
      (* [comment removed for export] *)
      step. rewrite (eqb_s32_lit bt 6) by lia.
      destruct (Z.eq_dec bt 6) as [E6|N6].
      { rewrite (proj2 (Z.eqb_eq _ _) E6). cbv iota. apply PKT; lia. }
      rewrite (proj2 (Z.eqb_neq _ _) N6). cbv iota.
      (* [comment removed for export] *)
      step. rewrite (eqb_s32_lit bt 1) by lia.
      destruct (Z.eq_dec bt 1) as [E1'|N1].
      + (* [comment removed for export] *)
        rewrite (proj2 (Z.eqb_eq _ _) E1'). cbv iota.
        unhide HD. unhide HTL. unhide FRS3. unhide ERR3. unhide MG3. unhide HEB4. unhide CELLS4. unhide NG3. unhide BUF4.
        apply evt_done.
        eapply (ngc_idb HO K sites HFL SFL HPL FREE SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m R s CL FB lo MG FA EB ERR f magic CTX qs P sw BS0 MINOR ew (conj P1 P4) P16 BS0R MINR AI
                  fuel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x8 m4 ps4 qb' B' bufalloc' bufdata' sg i I pad bs' e cpad _ _ c);
          [ exact MI4 | exact ST4 | exact AG04 | exact G4' | rewrite OF4; exact OF3 | exact HD | | exact HTL | exact FRS3 | exact ERR3 | exact MG3 | exact HEB4
          | exact CELLS4 | exact NG3 | exact UTS | exact MB | exact IC | exact IS | exact HIF4 | exact BUF4 | exact PFX4 | exact LEN'
          | exact COFF | exact CREM | exact CR1 | exact CR2 | exact E1' | unfold blk_handle in BH4; cbn [pc_bufsize pc_bufalloc] in BH4; lia | unfold blk_handle in BH4; cbn [pc_bufsize pc_bufalloc] in BH4; lia | exact GRD' ].
        unfold cursor_cells. rewrite COFF. fold bt. exact HCUR4.
      + (* [comment removed for export] *)
        rewrite (proj2 (Z.eqb_neq _ _) N1). cbv iota.
        unfold ngc_K. fold bt. replace (bt =? BT_IDB) with false by (symmetry; apply Z.eqb_neq; unfold BT_IDB; lia).
        replace ((bt =? BT_EPB) || (bt =? BT_SPB) || (bt =? BT_PB)) with false
          by (unfold BT_EPB, BT_SPB, BT_PB; rewrite (proj2 (Z.eqb_neq _ _) N6), (proj2 (Z.eqb_neq _ _) N3), (proj2 (Z.eqb_neq _ _) N2); reflexivity). cbv iota.
        unhide HD. unhide HTL. unhide FRS3. unhide ERR3. unhide MG3. unhide HEB4. unhide CELLS4. unhide NG3. unhide BUF4.
        pose proof (rw_cells_uncut _ _ _ _ _ HD HCUR4 ltac:(cbn; lia)) as J1.
        pose proof (rw_cells_uncut _ _ _ _ _ J1 HTL ltac:(cbn; lia)) as HC4.
        apply evt_done.
        eapply IH; [exact X8|].
        split; [exact MI4|]. split; [exact ST4|]. split; [exact AG04|]. split; [exact G4'|]. split; [rewrite OF4; exact OF3|].
        split; [exact HC4|]. split; [reflexivity|]. split; [exact FRS3|]. split; [exact ERR3|]. split; [exact MG3|]. split; [exact HEB4|].
        split; [exact CELLS4|]. split; [exact NG3|]. split; [exact UTS|]. split; [exact MB|]. split; [exact IC|]. split; [exact IS|]. split; [exact HIF4|].
        split; [exact BUF4|]. split; [exact PFX4|]. split; [lia|]. split; [unfold blk_handle in BH4; cbn [pc_bufsize pc_bufalloc] in BH4; lia|].
        split; [unfold blk_handle in BH4; cbn [pc_bufsize pc_bufalloc] in BH4; lia| exact GRD'].
  Qed.
End ChkNgD.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3 Require F_sfpcap_chkF__U3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3 Require F_sfpcapng_ai__U3.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
Module TwB.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MonadX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface_ng.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.TwB. 
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3.F_sfpcap_chkF__U3.F_sfpcapng_chkK. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_sfpcapng_chkA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_chkF.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3.F_sfpcapng_ai__U3.F_sfpcapng_chkC.
Import OSSVerify.libpcap.fuzz_pcap.images.Ubsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Ceiling.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia_e2w2_base := first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                                 | zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac ceil_mentioned := lazymatch goal with | |- context [@alloc_ceiling _] => idtac | _ : context [@alloc_ceiling _] |- _ => idtac end.
(* [comment removed for export] *)
Local Ltac gio_ceil_fact :=
  match goal with
  | G : GIo _ _ _ _ _ _ |- _ => let H := fresh "CLO__" in pose proof (S3.PcapRep.TwB.GIo_ceil_lo _ _ _ _ _ _ G) as H; unfold rc_lo in H
  end.
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try gio_ceil_fact; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Lemma bt_minus2_ltu : forall bt, (0 <= bt < 2^32)%Z ->
  ((bv_unsigned (Z_to_bv 64 (s32 bt + -2)) <? 2) = ((bt =? 2) || (bt =? 3)))%Z.
Proof using Type. pin_using tt.
  intros bt Hbt. rewrite unsigned_lit_wrap. unfold s32.
  destruct (Z.eq_dec bt 2) as [->|N2]; [reflexivity|]. destruct (Z.eq_dec bt 3) as [->|N3]; [reflexivity|].
  rewrite (proj2 (Z.eqb_neq _ _) N2), (proj2 (Z.eqb_neq _ _) N3). cbn [orb]. apply Z.ltb_ge.
  change (bv_modulus 64) with (2^64)%Z. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
End WithCeil.

Ltac prsMG GL := intros a Ha; rewrite cells_size_map_C1, GL in Ha; cbn [outside]; repeat match goal with |- _ /\ _ => split end; fastfirst (first [lia | left; lia | exact Logic.I]).

(* [comment removed for export] *)
Lemma msg_ok_b : forall l : list Z, forallb (fun z => (0 <? z)%Z && (z <? 256)%Z) l = true -> Forall (fun z => 0 < z < 256)%Z l.
Proof. intros l H. apply Forall_forall. intros x Hx. rewrite forallb_forall in H. specialize (H x Hx). apply andb_prop in H as [H1 H2].
  apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. lia. Qed.
Ltac msg_ok := first [ apply msg_ok_b; vm_compute; reflexivity
                     | vm_compute; repeat first [apply Forall_nil | apply Forall_cons; [split; reflexivity|]] ].

Section WithCeil.
Context {CEILV : CEIL}.
Lemma eqb_s32_lit : forall bt k, (0 <= bt < 2^32)%Z -> (0 <= k < 2^31)%Z -> bv_eqb (Z_to_bv 64 (s32 bt)) (Z_to_bv 64 k) = (bt =? k)%Z.
Proof using Type. pin_using tt.
  intros bt k Hb Hk. replace (Z_to_bv 64 k) with (Z_to_bv 64 (s32 k)) by (rewrite (s32_small k) by lia; reflexivity).
  apply eqb_s32; lia.
Qed.

Section ChkNgD.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation PS := (PState H hptr).
  #[local] Notation pcapT := (PcapTypes.pcap hptr hptr).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HPL : heap_perm_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis FREE : free_stmt_o HO K.
  Hypothesis SNPRINTF : snprintf_spec_stmt K.
  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : mem) (R : rctx) (s : PS) (CL FB : list cblk) (lo MG FA EB ERR : Z) (f : hptr) (magic : list Z).
  Hypothesis CTX : ngc_ctx K sites sp tp R s CL FB lo MG FA EB ERR f magic m.
  #[local] Notation POSTQ := (check_header_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL FB lo MG EB ERR magic f m (ps_outfile s)).
  #[local] Notation AGQ := (ngc_AGQ sp CL EB ERR m).
  #[local] Notation FRS := (ngc_FRS ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9).
  #[local] Notation PR := (prims HO fo_nop sites).
  (* [comment removed for export] *)
  Variables (qs : hptr) (P : Z) (sw : bool) (BS0 MINOR : Z) (ew : word).
  Hypothesis P14 : 0 < P /\ P + 680 <= CEILZ.
  Hypothesis P16 : P mod 16 = 0.
  Hypothesis P5 : out_of_image P 680.
  Hypothesis BS0R : 1 <= BS0 <= 2^21.
  Hypothesis MINR : 0 <= MINOR < 2^16.

  #[local] Notation pL := (ngc_p f qs sw BS0 MINOR).
  #[local] Notation hcells := (ngc_hcells P sw BS0 MINOR).

  Open Scope bv_scope.

  Hypothesis RB : read_block_stmt HO K sites.
  Hypothesis AI : add_interface_stmt HO K sites.

  (* [comment removed for export] *)
  Lemma hcells_rebuf : forall mX mY B B',
    rw_cells usegs mX P (hcells B) ->
    agrees_on (fun a => (P <= a < P + 24 \/ P + 32 <= a < P + 648)%Z) mX mY ->
    rw_cells usegs mY (P + 24) [C8 (Z_to_bv 64 B')] -> rw_cells usegs mY P (hcells B').
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt).
    intros mX mY B B' HC AG HB. unfold ngc_hcells, ngcells in HC |- *.
    destruct (rw_cells_cut _ _ _ 4 HC) as [A X]. destruct (rw_cells_cut _ _ _ 1 X) as [_ C]. clear X. cbn [firstn skipn cells_size csize Nat.add app] in A, C.
    transport A mY AG ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; lia).
    transport C mY AG ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; lia).
    replace (P + 24)%Z with (P + Z.of_nat 24)%Z in HB by lia.
    pose proof (rw_cells_uncut _ _ _ _ _ A HB ltac:(cbn; lia)) as AB.
    exact (rw_cells_uncut _ _ _ _ _ AB C ltac:(cbn; lia)).
  Qed.
  Lemma hcells_cut20 : forall mX B,
    rw_cells usegs mX P (hcells B) -> rw_cells usegs mX (P + 20) [C4 (Z_to_bv 64 BS0); C8 (Z_to_bv 64 B)].
  Proof using Type. pin_using tt.
    intros mX B HC. unfold ngc_hcells, ngcells in HC.
    destruct (rw_cells_cut _ _ _ 3 HC) as [_ X]. destruct (rw_cells_cut _ _ _ 2 X) as [X1 _]. cbn [firstn skipn cells_size csize Nat.add app] in X1.
    replace (P + 20)%Z with (P + Z.of_nat 20)%Z by lia. exact X1.
  Qed.
  Lemma ngcells_cut656 : forall mX sg I pad,
    rw_cells usegs mX (P + 648) (ng_cells sg I pad) -> rw_cells usegs mX (P + 656) [C4 (Z_to_bv 64 (ng_max_blocksize sg))].
  Proof using Type. pin_using tt.
    intros mX sg I pad HN. unfold ng_cells in HN. destruct (rw_cells_cut _ _ _ 1 HN) as [_ X]. destruct (rw_cells_cut _ _ _ 1 X) as [X1 _].
    cbn [firstn skipn cells_size csize Nat.add app] in X1. replace (P + 656)%Z with (P + 648 + Z.of_nat 8)%Z by lia. exact X1.
  Qed.

  (* [comment removed for export] *)
  Definition NGI (m3 : mem) (ps3 : PS) (qb : hptr) (B bufalloc : Z) (bufdata : list Z) (sg : pcap_ng_sf) (i : option hptr) (I : Z)
             (pad bs e : list byte) (hc : list cell) : Prop :=
    mem_inv usegs m3 /\ stk usegs m3 lo (bv_unsigned sp + -128) /\ AGQ m3 /\
    GIo K R ps3 (IBLK i I sg ++ (qs, P, 680%Z) :: (qb, B, bufalloc) :: CL) FB m3 /\ ps_outfile ps3 = ps_outfile s /\
    rw_cells usegs m3 (bv_unsigned sp + -128) hc /\ cells_size hc = 40%nat /\ FRS m3 /\
    rw_cells usegs m3 ERR [C4 ew] /\ rw_cells usegs m3 MG (map (fun z => C1 (Z_to_bv 8 z)) magic) /\ rw_cells usegs m3 EB [CB 256 e] /\
    rw_cells usegs m3 P (hcells B) /\ rw_cells usegs m3 (P + 648) (ng_cells sg I pad) /\
    ng_user_tsresol sg = 1000000%Z /\ ng_max_blocksize sg = INITIAL_MAX_BLOCKSIZE /\ (0 <= ng_ifcount sg < 2^32)%Z /\ (0 <= ng_ifaces_size sg < 2^32)%Z /\
    ifaces_ok (pL qb bufalloc bufdata sg i) I m3 /\
    rw_cells usegs m3 B [CB (Z.to_nat bufalloc) bs] /\ firstn (length bufdata) bs = map b8 bufdata /\
    (Z.of_nat (length bufdata) <= bufalloc)%Z /\ (0 <= bufalloc < 2^32)%Z /\ (BS0 <= bufalloc)%Z /\ Forall (fun z => 0 <= z < 256)%Z bufdata.

  Lemma ngc_loop : forall (fuel : nat) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' x8 : word) (m3 : mem) (ps3 : PS)
           (qb : hptr) (B bufalloc : Z) (bufdata : list Z) (sg : pcap_ng_sf) (i : option hptr) (I : Z) (pad bs e : list byte) (hc : list cell),
      bv_unsigned x8 = (2^64 - 1)%Z ->
      NGI m3 ps3 qb B bufalloc bufdata sg i I pad bs e hc ->
      implM usegs (ngc_find MOps PR fuel 0 (pL qb bufalloc bufdata sg i)) ps3 POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 ERR) (Z_to_bv 64 EB) a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 FA) (Z_to_bv 64 P) (Z_to_bv 64 1) (Z_to_bv 64 2) (Z_to_bv 64 (P + 648)) x8 (Z_to_bv 64 1) (Z_to_bv 64 6) s10 s11 t3' t4' t5' t6')
            F (Z_to_bv 64 0x16e64) fc None m3 (seg_rom usegs)).
  Proof using AI BS0R CTX FREE HFL HPL MINR P14 P16 RB SFL SNPRINTF. pin_using (fun (AI BS0R CTX FREE HFL HPL MINR P14 P16 RB SFL SNPRINTF : unit) => tt).
    induction fuel as [|fuel IH]; intros until hc; intros X8 IV.
    { unfold ngc_find. cbn [ng_find_idb]. apply (implM_unr usegs). }
    destruct IV as (MI3 & ST3 & AG3 & G3 & OF3 & HC3 & Hhc & FRS3 & ERR3 & MG3 & HEB3 & CELLS & NG3 & UTS & MB & IC & IS & HIF & BUF3 & PFX & LENB & BAR & BSB & GRD).
    pose proof CTX as (G & LO & BU & SPM & TP & ALN & HinF & SITES & GL & GR & R1 & R2 & R3 & E1 & E2 & D1 & E4 & E8).
    pose proof (GIo_spw K _ _ _ _ _ G) as SPW. pose proof (GIo_sp47 K _ _ _ _ _ G) as SP47. pose proof (bv_unsigned_in_range 64 sp) as RSP. change (bv_modulus 64) with (2^64)%Z in RSP.
    pose proof E2 as EBU. unfold rc_spmain in EBU.
    destruct P14 as [P1 P4].
    destruct (ngl_facts K HPL _ _ _ _ _ _ _ _ _ _ _ _ _ G3 ltac:(lia)) as ((B1 & B2 & B4) & APB & API & NPB).
    assert (CLB : forall a, in_block CL a -> (a < CEILZ)%Z).
    { intros a Ha. destruct (GIo_CLc_facts K R s CL [] FB m a ltac:(rewrite app_nil_r; exact G) Ha) as [Hc _]. exact (proj2 Hc). }
    assert (HI : match i with Some _ => True | None => I = 0%Z end).
    { unfold ifaces_ok in HIF. cbn [pc_priv ngc_p] in HIF. destruct i; [exact Logic.I| exact (proj1 HIF)]. }
    assert (IR : (0 <= I < 2^64)%Z) by (destruct i as [q|]; [destruct (API sg q eq_refl) as (I1 & I4 & _); lia| cbn in HI; lia]).
    (* [comment removed for export] *)
    unfold ngc_find. rewrite (ng_find_idb_S MOps PR). apply (implM_bind_assoc usegs). fold (ngc_find MOps PR fuel 0).
    (* [comment removed for export] *)
    destruct (rw_cells_forget _ _ _ _ HC3) as [hj HC']. clear HC3. rewrite Hhc in HC'.
    pose proof (rw_cells_split_CB _ _ _ [] _ _ [] [8%nat; 24%nat; 8%nat] HC' ltac:(cbn; lia)) as HC''. clear HC'. cbn [mk_CB_cells app] in HC''.
    destruct (rw_cells_cut _ _ _ 1 HC'') as [HD X]. destruct (rw_cells_cut _ _ _ 1 X) as [HCUR HTL]. clear HC'' X.
    cbn [firstn skipn cells_size csize Nat.add app] in HD, HCUR, HTL.
    replace (bv_unsigned sp + -128 + Z.of_nat 8)%Z with (bv_unsigned sp + -120)%Z in HCUR by lia.
    replace (bv_unsigned sp + -128 + Z.of_nat 8 + Z.of_nat 24)%Z with (bv_unsigned sp + -96)%Z in HTL by lia.
    pose proof (hcells_cut20 _ _ CELLS) as HBS. pose proof (proj2 (hcells_cut _ _ _ _ _ _ CELLS)) as HPV. pose proof (ngcells_cut656 _ _ _ _ NG3) as HMB.
    hide HD. hide HTL. hide FRS3. hide ERR3. hide MG3. hide HEB3. hide CELLS. hide NG3. hide BUF3. hide HCUR. hide HBS. hide HPV. hide HMB.
    unfold implM. iprefix.
    do 5 step.
    unhide HEB3. unhide BUF3. unhide HCUR. unhide HBS. unhide HPV. unhide HMB.
    rewrite (ngl_assoc_rb i I sg qs P qb B bufalloc CL) in G3.
    apply evt_done. name_sp sp (-128)%Z. eapply (implM_bind usegs).
    { eapply (RB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 R ps3 (IBLK i I sg ++ [(qs, P, 680%Z)]) CL FB f FA P B (bv_unsigned sp + -120)%Z EB lo
                 (pL qb bufalloc bufdata sg i) sg i (DStack SiteBhdrCheckHeader 0) bs e);
        [ split; [exact G3|]; split; [rewrite Hsp; exact ST3|]; split; [unfold rc_lo; lia|]; split; [unfold READ_BLOCK_STACK, PCAP_L1_STACK; rewrite Hsp; lia|];
          split; [rewrite Hsp; lia|]; split; [exact MI3|]; split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]
        | exact HinF | reflexivity | reflexivity
        | apply in_or_app; left; apply in_or_app; right; left; reflexivity
        | intros st'; cbn [eval_rdest fo_site fo_nop prims]; rewrite SITES, Hsp; unfold sites_at, D_CHECK_HEADER; lia
        | reflexivity | reflexivity | rewrite ?Hsp; f_equal; lia | reflexivity
        | split; [exact HBS|]; split; [exact HPV|]; split; [exact HMB|]; rewrite MB; unfold INITIAL_MAX_BLOCKSIZE; cbn [pc_bufsize pc_bufalloc ngc_p]; lia
        | exact BUF3 | exact PFX | cbn [pc_bufdata pc_bufalloc ngc_p]; lia
        | exact HCUR | reflexivity | rewrite ?Hsp; lia | lia | rewrite ?Hsp; apply aligned16_8; [exact ALN| reflexivity]
        | exact HEB3 | left; rewrite Hsp; lia | exact E8 ]. }
    intros rb ps4 ms4 PO.
    destruct PO as (a0v & m4 & p' & B' & bs' & E & OF4 & MI4 & ST4 & AG4 & G4 & BH4 & BUF4 & PFX4 & LEN4 & Q1 & Q2 & Q3 & Q4 & Q5 & SM & RM).
    unfold hpost_regs in E. destruct_exs E. subst ms4. rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 0x16e78)) with (Z_to_bv 64 0x16e78) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    (* [comment removed for export] *)
    destruct p' as [f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17]. unfold same_meta in SM.
    cbn [pc_priv pc_rfile pc_self pc_bufsize pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext
         pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_buffer pc_bufalloc pc_bufdata ngc_p] in Q1, Q2, Q3, Q4, Q5, SM, RM, G4, BH4, BUF4, PFX4, LEN4.
    destruct SM as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9). subst f1 f2 f3 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17.
    rename f4 into bufalloc'. rename f5 into qb'. rename f6 into bufdata'.
    (* [comment removed for export] *)
    assert (INP4 : forall a, (P <= a < P + 680)%Z -> in_block ((IBLK i I sg ++ [(qs, P, 680%Z)]) ++ CL) a).
    { intros a Ha. apply (proj2 (in_block_app _ _ _)). left. apply (proj2 (in_block_app _ _ _)). right. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    assert (INI4 : forall sg' q, PrivNg sg i = PrivNg sg' (Some q) -> forall a, (I <= a < I + 40 * ng_ifaces_size sg')%Z -> in_block ((IBLK i I sg ++ [(qs, P, 680%Z)]) ++ CL) a).
    { intros sg' q E a Ha. injection E as Ei Es. subst i sg'. apply (proj2 (in_block_app _ _ _)). left. apply (proj2 (in_block_app _ _ _)). left.
      unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    pose proof (GIo_perm K HPL _ _ _ _ _ _ G4 (ngl_perm_rb i I sg qs P qb' B' bufalloc' CL)) as G4'. clear G4.
    destruct (ngl_facts K HPL _ _ _ _ _ _ _ _ _ _ _ _ _ G4' ltac:(unfold blk_handle in BH4; cbn [pc_bufsize pc_bufalloc ngc_p] in BH4; lia)) as ((B1' & B2' & B4') & APB' & API' & NPB').
    unhide HD. unhide HTL. unhide FRS3. unhide ERR3. unhide MG3. unhide CELLS. unhide NG3.
    transport HD m4 AG4 ltac:(prs). transport HTL m4 AG4 ltac:(prs). unfold ngc_FRS in FRS3. transport FRS3 m4 AG4 ltac:(prs).
    transport ERR3 m4 AG4 ltac:(prs). transport MG3 m4 AG4 ltac:(prsMG GL).
    transport NG3 m4 AG4 ltac:(unfold ng_cells; prs).
    assert (CELLS4 : rw_cells usegs m4 P (hcells B')).
    { eapply hcells_rebuf; [exact CELLS | | ].
      - eapply agrees_on_weaken; [exact AG4|]. intros a Ha. split; [right; apply INP4; lia|]. lia.
      - destruct BH4 as (X & _). destruct (rw_cells_cut _ _ _ 1 X) as [_ X2]. cbn [firstn skipn cells_size csize Nat.add app pc_bufsize ngc_p] in X2.
        replace (P + 24)%Z with (P + 20 + Z.of_nat 4)%Z by lia. exact X2. }
    clear CELLS HBS HPV HMB BUF3 PFX HCUR HEB3.
    assert (HIF4 : ifaces_ok (pL qb' bufalloc' bufdata' sg i) I m4).
    { assert (HIF' : ifaces_ok (pL qb' bufalloc' bufdata' sg i) I m3) by exact HIF.
      eapply ifaces_ok_agree; [exact AG4 | | exact HIF']. intros sg' q E a Ha. cbn [pc_priv ngc_p] in E.
      destruct (API sg' q E) as (I1 & I4 & IP & IB). split; [right; exact (INI4 sg' q E a Ha)|]. lia. }
    clear HIF.
    assert (AG04 : AGQ m4).
    { unfold ngc_AGQ in AG3 |- *. eapply agrees_on_trans; [exact AG3|]. eapply agrees_on_weaken; [exact AG4|].
      intros a [[Ha|Ha] [Hn _]]; [split; [left; lia| lia]|]. pose proof (CLB a Ha). pose proof (NPB a Ha).
      split; [right; apply (proj2 (in_block_app _ _ _)); right; exact Ha| lia]. }
    (* [comment removed for export] *)
    assert (E8T : bv_eqb (Z_to_bv 64 (-1)) x8 = true) by (unfold bv_eqb; rewrite X8; vm_compute; reflexivity).
    assert (E8F0 : bv_eqb (Z_to_bv 64 0) x8 = false) by (unfold bv_eqb; rewrite X8; vm_compute; reflexivity).
    assert (E8F1 : bv_eqb (Z_to_bv 64 1) x8 = false) by (unfold bv_eqb; rewrite X8; vm_compute; reflexivity).
    destruct rb as [p'' | msg p'' | c p''].
    - (* [comment removed for export] *)
      destruct RM as (-> & -> & HEB4 & (ccs' & HCUR4 & Hccs')).
      unfold ngc_K. cbn [mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims]. apply (implM_retb usegs). unfold ngc_loop_tail.
      hide HD. hide HTL. hide FRS3. hide ERR3. hide MG3. hide HEB4. hide CELLS4. hide NG3. hide BUF4. hide HCUR4.
      unfold implM. iprefix.
      step. rewrite E8F0. cbv iota. step. rewrite (eqb_lits_eq 0 0 eq_refl). cbv iota.
      step. step. step.
      unhide HD. unhide HTL. unhide FRS3. unhide ERR3. unhide MG3. unhide HEB4. unhide CELLS4. unhide NG3. unhide BUF4. unhide HCUR4.
      assert (MSG : fmt_at m4 0x10e35 "the capture file has no Interface Description Blocks"%string)
        by (apply (fmt_at_intro m4 _ _ MI4); [vm_compute; reflexivity| lia| cbn; lia]).
      pose proof (rw_cells_uncut _ _ _ _ _ HD HCUR4 ltac:(cbn; lia)) as J1.
      pose proof (rw_cells_uncut _ _ _ _ _ J1 HTL ltac:(rewrite cells_size_app, Hccs'; cbn; lia)) as HC4.
      apply evt_done.
      eapply (ngc_mcp_fail HO K sites HFL SFL HPL FREE ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m R s CL FB lo MG FA EB ERR f magic CTX qs P sw BS0 MINOR ew (conj P1 P4)
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m4 ps4 0x10e35 53 "the capture file has no Interface Description Blocks"%string Msg.no_idb bufdata' qb' i sg B' I bufalloc' e);
        [ exact MI4 | exact ST4 | exact AG04 | exact G4' | rewrite OF4; exact OF3 | exact HI | exact HC4 | rewrite !cells_size_app, Hccs'; reflexivity | exact FRS3 | exact ERR3 | exact MG3 | exact HEB4
        | exact (proj1 (hcells_cut _ _ _ _ _ _ CELLS4)) | exact (ngcells_cut672 _ _ _ _ _ NG3) | exact IR | unfold blk_handle in BH4; cbn [pc_bufsize pc_bufalloc] in BH4; lia
        | exact MSG | cbn; lia | lia | vm_compute; reflexivity | msg_ok ].
    - (* [comment removed for export] *)
      destruct RM as (-> & -> & (junk4 & HEB4) & LENM & MOK & (ccs' & HCUR4 & Hccs')).
      unfold ngc_K. cbn [mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims]. apply (implM_retb usegs). unfold ngc_loop_tail. unfold ngc_fail. cbn [e_fenter e_fret fo_enter fo_ret fo_nop prims]. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_free prims free_opt ng_ifaces_ptr_of pc_buffer pc_self pc_priv ngc_p].
      hide HD. hide HTL. hide FRS3. hide ERR3. hide MG3. hide HEB4. hide CELLS4. hide NG3. hide BUF4. hide HCUR4.
      unfold implM. iprefix.
      step. rewrite E8T. cbv iota.
      unhide HD. unhide HTL. unhide FRS3. unhide ERR3. unhide MG3. unhide HEB4. unhide CELLS4. unhide NG3. unhide BUF4. unhide HCUR4.
      pose proof (rw_cells_uncut _ _ _ _ _ HD HCUR4 ltac:(cbn; lia)) as J1.
      pose proof (rw_cells_uncut _ _ _ _ _ J1 HTL ltac:(rewrite cells_size_app, Hccs'; cbn; lia)) as HC4.
      apply evt_done.
      eapply (ngc_fail3 HO K sites HFL SFL FREE ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R s CL FB lo MG FA EB ERR f magic m) with (i := i) (ni := (40 * ng_ifaces_size sg)%Z);
        [ exact CTX | exact MI4 | exact ST4 | exact AG04 | destruct i; exact G4' | exact HI | exact HC4 | rewrite !cells_size_app, Hccs'; reflexivity | exact FRS3 | exact ERR3 | exact MG3 | exact HEB4
        | exact LENM | exact MOK | rewrite OF4; exact OF3 | exact (proj1 (hcells_cut _ _ _ _ _ _ CELLS4)) | exact (ngcells_cut672 _ _ _ _ _ NG3) | exact IR | lia | lia ].
    - (* [comment removed for export] *)
      destruct RM as (-> & -> & HEB4 & (cpad & HCUR4) & COFF & CREM & CR1 & CR2 & CBT & LEN' & GRD').
      set (bt := cur_block_type c) in *.
      hide HD. hide HTL. hide FRS3. hide ERR3. hide MG3. hide HEB4. hide CELLS4. hide NG3. hide BUF4.
      unfold implM. iprefix.
      step. rewrite E8F1. cbv iota. step. rewrite (eqb_lits_false 1 0) by lia. cbv iota.
      step. rewrite (sx32_s32 bt) by lia. step. step.
      unfold bv_ltu. rewrite (unsigned_lit 2), (bt_minus2_ltu bt) by lia.
      (* [comment removed for export] *)
      assert (PKT : forall (a1x : word),
        (bt = 2 \/ bt = 3 \/ bt = 6)%Z ->
        evt usegs (fun ms1 => impl usegs (at_node usegs) (npeek usegs)
               ((Monad.mbind (ngc_K MOps PR fuel (RB_Ok c (pL qb' bufalloc' bufdata' sg i))) (ngc_loop_tail MOps PR 0)) ps4)
               (epost (fun p0 => POSTQ (fst p0) (snd p0))) ms1)
          (MS (mkR (Z_to_bv 64 0x16e78) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp x x0 x1 (Z_to_bv 64 ERR) (Z_to_bv 64 EB) (Z_to_bv 64 (s32 bt)) a1x x3 x4 x5 x6 x7 x9
                   (Z_to_bv 64 FA) (Z_to_bv 64 P) (Z_to_bv 64 1) (Z_to_bv 64 2) (Z_to_bv 64 (P + 648)) x8 (Z_to_bv 64 1) (Z_to_bv 64 6) s10 s11 x10 x11 x12 x13)
              F (Z_to_bv 64 0x16ff0) fc None m4 (seg_rom usegs))).
      { intros a1x HBT.
        unfold ngc_K. fold bt. replace (bt =? BT_IDB) with false by (symmetry; apply Z.eqb_neq; unfold BT_IDB; lia).
        replace ((bt =? BT_EPB) || (bt =? BT_SPB) || (bt =? BT_PB)) with true
          by (unfold BT_EPB, BT_SPB, BT_PB; destruct HBT as [-> |[-> | ->]]; reflexivity). cbv iota. cbn [mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims].
        do 4 step.
        unhide HD. unhide HTL. unhide FRS3. unhide ERR3. unhide MG3. unhide HEB4. unhide CELLS4. unhide NG3. unhide BUF4.
        assert (MSG : fmt_at m4 0x10aac "the capture file has a packet block before any Interface Description Blocks"%string)
          by (apply (fmt_at_intro m4 _ _ MI4); [vm_compute; reflexivity| lia| cbn; lia]).
        pose proof (rw_cells_uncut _ _ _ _ _ HD HCUR4 ltac:(cbn; lia)) as J1.
        pose proof (rw_cells_uncut _ _ _ _ _ J1 HTL ltac:(cbn; lia)) as HC4.
        apply evt_done. apply (implM_retb usegs). unfold ngc_loop_tail.
        eapply (ngc_mcp_fail HO K sites HFL SFL HPL FREE ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m R s CL FB lo MG FA EB ERR f magic CTX qs P sw BS0 MINOR ew (conj P1 P4)
                  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m4 ps4 0x10aac 76 "the capture file has a packet block before any Interface Description Blocks"%string Msg.packet_before_idb bufdata' qb' i sg B' I bufalloc' e);
          [ exact MI4 | exact ST4 | exact AG04 | exact G4' | rewrite OF4; exact OF3 | exact HI | exact HC4 | reflexivity | exact FRS3 | exact ERR3 | exact MG3 | exact HEB4
          | exact (proj1 (hcells_cut _ _ _ _ _ _ CELLS4)) | exact (ngcells_cut672 _ _ _ _ _ NG3) | exact IR | unfold blk_handle in BH4; cbn [pc_bufsize pc_bufalloc] in BH4; lia
          | exact MSG | cbn; lia | lia | vm_compute; reflexivity | msg_ok ]. }
      destruct (Z.eq_dec bt 2) as [E2'|N2]; [| destruct (Z.eq_dec bt 3) as [E3|N3]].
      1,2: replace ((bt =? 2) || (bt =? 3)) with true by (symmetry; apply Bool.orb_true_iff; first [left; apply Z.eqb_eq; exact E2' | right; apply Z.eqb_eq; exact E3]); cbv iota.
      1,2: apply PKT; lia.
      replace ((bt =? 2) || (bt =? 3)) with false by (symmetry; rewrite (proj2 (Z.eqb_neq _ _) N2), (proj2 (Z.eqb_neq _ _) N3); reflexivity). cbv iota.
      (* [comment removed for export] *)
      step. rewrite (eqb_s32_lit bt 6) by lia.
      destruct (Z.eq_dec bt 6) as [E6|N6].
      { rewrite (proj2 (Z.eqb_eq _ _) E6). cbv iota. apply PKT; lia. }
      rewrite (proj2 (Z.eqb_neq _ _) N6). cbv iota.
      (* [comment removed for export] *)
      step. rewrite (eqb_s32_lit bt 1) by lia.
      destruct (Z.eq_dec bt 1) as [E1'|N1].
      + (* [comment removed for export] *)
        rewrite (proj2 (Z.eqb_eq _ _) E1'). cbv iota.
        unhide HD. unhide HTL. unhide FRS3. unhide ERR3. unhide MG3. unhide HEB4. unhide CELLS4. unhide NG3. unhide BUF4.
        apply evt_done.
        eapply (ngc_idb HO K sites HFL SFL HPL FREE SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m R s CL FB lo MG FA EB ERR f magic CTX qs P sw BS0 MINOR ew (conj P1 P4) P16 BS0R MINR AI
                  fuel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x8 m4 ps4 qb' B' bufalloc' bufdata' sg i I pad bs' e cpad _ _ c);
          [ exact MI4 | exact ST4 | exact AG04 | exact G4' | rewrite OF4; exact OF3 | exact HD | | exact HTL | exact FRS3 | exact ERR3 | exact MG3 | exact HEB4
          | exact CELLS4 | exact NG3 | exact UTS | exact MB | exact IC | exact IS | exact HIF4 | exact BUF4 | exact PFX4 | exact LEN'
          | exact COFF | exact CREM | exact CR1 | exact CR2 | exact E1' | unfold blk_handle in BH4; cbn [pc_bufsize pc_bufalloc] in BH4; lia | unfold blk_handle in BH4; cbn [pc_bufsize pc_bufalloc] in BH4; lia | exact GRD' ].
        unfold cursor_cells. rewrite COFF. fold bt. exact HCUR4.
      + (* [comment removed for export] *)
        rewrite (proj2 (Z.eqb_neq _ _) N1). cbv iota.
        unfold ngc_K. fold bt. replace (bt =? BT_IDB) with false by (symmetry; apply Z.eqb_neq; unfold BT_IDB; lia).
        replace ((bt =? BT_EPB) || (bt =? BT_SPB) || (bt =? BT_PB)) with false
          by (unfold BT_EPB, BT_SPB, BT_PB; rewrite (proj2 (Z.eqb_neq _ _) N6), (proj2 (Z.eqb_neq _ _) N3), (proj2 (Z.eqb_neq _ _) N2); reflexivity). cbv iota.
        unhide HD. unhide HTL. unhide FRS3. unhide ERR3. unhide MG3. unhide HEB4. unhide CELLS4. unhide NG3. unhide BUF4.
        pose proof (rw_cells_uncut _ _ _ _ _ HD HCUR4 ltac:(cbn; lia)) as J1.
        pose proof (rw_cells_uncut _ _ _ _ _ J1 HTL ltac:(cbn; lia)) as HC4.
        apply evt_done.
        eapply IH; [exact X8|].
        split; [exact MI4|]. split; [exact ST4|]. split; [exact AG04|]. split; [exact G4'|]. split; [rewrite OF4; exact OF3|].
        split; [exact HC4|]. split; [reflexivity|]. split; [exact FRS3|]. split; [exact ERR3|]. split; [exact MG3|]. split; [exact HEB4|].
        split; [exact CELLS4|]. split; [exact NG3|]. split; [exact UTS|]. split; [exact MB|]. split; [exact IC|]. split; [exact IS|]. split; [exact HIF4|].
        split; [exact BUF4|]. split; [exact PFX4|]. split; [lia|]. split; [unfold blk_handle in BH4; cbn [pc_bufsize pc_bufalloc] in BH4; lia|].
        split; [unfold blk_handle in BH4; cbn [pc_bufsize pc_bufalloc] in BH4; lia| exact GRD'].
  Qed.
End ChkNgD.

End WithCeil.
End TwB.
End F_sfpcapng_chkD.

(* [comment removed for export] *)
Module F_sfpcapng_chkE.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep MonadX Image ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_pcap_err__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_aiE__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcap_chkA__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface_ng OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_small OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_open OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_fopen OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.F_sfpcapng_blkA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_aiE OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcap_chkA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_sfpcapng_chkA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcapng_chkF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_aiE__S3.F_sfpcapng_chkC OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_chkD__S3.F_sfpcapng_chkD.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import KeepHyps.
(* [comment removed for export] *)
Local Ltac lia_e2w2_base := first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                                 | zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac ceil_mentioned := lazymatch goal with | |- context [@alloc_ceiling _] => idtac | _ : context [@alloc_ceiling _] |- _ => idtac end.
(* [comment removed for export] *)
Local Ltac gio_ceil_fact :=
  match goal with
  | G : GIo _ _ _ _ _ _ |- _ => let H := fresh "CLO__" in pose proof (PcapRep.GIo_ceil_lo _ _ _ _ _ _ G) as H; unfold rc_lo in H
  end.
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try gio_ceil_fact; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Lemma swap16_word : forall a b, (0 <= a < 256)%Z -> (0 <= b < 256)%Z ->
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zx16 (Z_to_bv 64 (a + 256 * b)))) 8)))
                    (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (zx16 (Z_to_bv 64 (a + 256 * b)))) 8))))
  = Z_to_bv 64 (b + 256 * a + 65536 * b)%Z.
Proof using Type. pin_using tt.
  intros a b Ha Hb. apply bv_eq. rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.swap16_val _ a b); [| lia | lia | apply unsigned_zx16; lia]. rewrite unsigned_lit by lia. reflexivity.
Qed.
Lemma shl48_lit : forall x, (0 <= x < 65536)%Z -> Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 x)) 48) = Z_to_bv 64 (x * 2 ^ 48)%Z.
Proof using Type. pin_using tt. intros x Hx. rewrite unsigned_lit by lia. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. Qed.
(* [comment removed for export] *)
Lemma sextw_low : forall (w : word) x hi, (bv_unsigned w = x + 4294967296 * hi)%Z -> (0 <= x < 2^31)%Z ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned w + 0)) = Z_to_bv 64 x.
Proof using Type. pin_using tt. intros w x hi E Hx. rewrite (swrap32_low _ x hi E). rewrite s32_small by lia. reflexivity. Qed.
(* [comment removed for export] *)
Lemma le4_low : forall (w : word) x hi, (bv_unsigned w = x + 4294967296 * hi)%Z -> (0 <= x < 2^32)%Z -> (0 <= hi < 2^32)%Z ->
  le4 w = map b8 (le_bytes 4 x).
Proof using Type. pin_using tt.
  intros w x hi E Hx Hhi. replace w with (Z_to_bv 64 (x + 4294967296 * hi)) by (apply bv_eq; rewrite unsigned_lit by lia; lia).
  rewrite le4_mod32 by lia. apply le4_le_bytes. lia.
Qed.
End WithCeil.


(* [comment removed for export] *)
Lemma msg_ok_b : forall l : list Z, forallb (fun z => (0 <? z)%Z && (z <? 256)%Z) l = true -> Forall (fun z => 0 < z < 256)%Z l.
Proof. intros l H. apply Forall_forall. intros x Hx. rewrite forallb_forall in H. specialize (H x Hx). apply andb_prop in H as [H1 H2].
  apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. lia. Qed.
Ltac msg_ok := first [ apply msg_ok_b; vm_compute; reflexivity
                     | vm_compute; repeat first [apply Forall_nil | apply Forall_cons; [split; reflexivity|]] ].
Ltac prsMG GL := intros a Ha; rewrite cells_size_map_C1, GL in Ha; cbn [outside]; repeat match goal with |- _ /\ _ => split end; fastfirst (first [lia | left; lia | exact Logic.I]).

Section WithCeil.
Context {CEILV : CEIL}.
Definition land2_cases__stmt : Prop := forall x, (0 <= x)%Z -> Z.land x 2 = 0%Z \/ Z.land x 2 = 2%Z.
Section Sz5.
Variables x : ltac2:(SecDiet.SzSec.tyM 'land2_cases__stmt "v" @x).
Lemma land2_cases__body : ltac2:(SecDiet.SzSec.bodyP 'land2_cases__stmt "v").
Proof using Type. pin_using tt.
  intros Hx.
 destruct (Z.testbit x 1) eqn:E.
  - right. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec.
    destruct (Z.eq_dec n 1) as [->|Hn1]; [rewrite E; reflexivity|].
    replace (Z.testbit 2 n) with false; [apply Bool.andb_false_r|].
    change 2%Z with (2^1)%Z. rewrite Z.pow2_bits_eqb by lia. symmetry. apply Z.eqb_neq. lia.
  - left. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.eq_dec n 1) as [->|Hn1]; [rewrite E; reflexivity|].
    replace (Z.testbit 2 n) with false; [apply Bool.andb_false_r|].
    change 2%Z with (2^1)%Z. rewrite Z.pow2_bits_eqb by lia. symmetry. apply Z.eqb_neq. lia.
Qed.
End Sz5.
Lemma land2_cases : ltac:(let t := eval cbv delta [land2_cases__stmt] in land2_cases__stmt in exact t).
Proof using Type. intros x. ltac2:(SecDiet.SzSec.closeP 'land2_cases__body "v"). Qed.
Lemma lor2_eqb2 : forall x, (0 <= x)%Z -> (Z.lor x 2 =? 2)%Z = ((x =? 0) || (x =? 2))%Z.
Proof using Type. pin_using tt.
  intros x Hx.
  pose proof (Z.add_lor_land x 2) as A. pose proof (land2_cases x Hx) as B.
  destruct (Z.eq_dec x 0) as [->|N0]; [reflexivity|]. destruct (Z.eq_dec x 2) as [->|N2]; [reflexivity|].
  destruct (Z.eq_dec x 1) as [->|N1]; [reflexivity|].
  rewrite (proj2 (Z.eqb_neq x 0) N0), (proj2 (Z.eqb_neq x 2) N2). cbn. apply Z.eqb_neq. lia.
Qed.
Lemma lor2_range : forall x, (0 <= x < 65536)%Z -> (0 <= Z.lor x 2 < 65538)%Z.
Proof using Type. pin_using tt. intros x Hx. pose proof (Z.add_lor_land x 2) as A. pose proof (land2_cases x ltac:(lia)). pose proof (proj2 (Z.lor_nonneg x 2) ltac:(lia)). lia. Qed.

Section ChkNg.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  #[local] Notation cblk := (@cblock hptr).
  #[local] Notation PS := (PState H hptr).
  #[local] Notation pcapT := (PcapTypes.pcap hptr hptr).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HPL : heap_perm_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis FREE : free_stmt_o HO K.
  Hypothesis SNPRINTF : snprintf_spec_stmt K.
  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : mem) (R : rctx) (s : PS) (CL FB : list cblk) (lo MG FA EB ERR : Z) (f : hptr) (magic : list Z).
  Hypothesis CTX : ngc_ctx K sites sp tp R s CL FB lo MG FA EB ERR f magic m.
  #[local] Notation POSTQ := (check_header_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL FB lo MG EB ERR magic f m (ps_outfile s)).
  #[local] Notation AGQ := (ngc_AGQ sp CL EB ERR m).
  #[local] Notation FRS := (ngc_FRS ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9).
  #[local] Notation PR := (prims HO fo_nop sites).

  Open Scope bv_scope.

  Hypothesis OPEN_COMMON : open_offline_common_stmt HO K sites.
  Hypothesis MALLOCS : malloc_stmt_o HO K.
  Hypothesis RBYTES : read_bytes_stmt HO K sites.
  Hypothesis RB : read_block_stmt HO K sites.
  Hypothesis AI : add_interface_stmt HO K sites.

  (* [comment removed for export] *)
  Definition ngc_fill__stmt : Prop := forall (fuel : nat) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' w7 w9 : word) (sw : bool) (TL hi7 hi9 : Z)
           (m1 : mem) (ps1 : PS) (hc : list cell) (ew : word) (e : list byte),
      (bv_unsigned w9 = TL + 4294967296 * hi9)%Z -> (0 <= hi9 < 2^32)%Z -> (28 <= TL <= 1048576)%Z ->
      (bv_unsigned w7 = BYTE_ORDER_MAGIC + 4294967296 * hi7)%Z -> (0 <= hi7 < 2^32)%Z ->
      mem_inv ssegs m1 -> stk ssegs m1 lo (bv_unsigned sp + -128) -> AGQ m1 -> GIo K R ps1 CL FB m1 -> ps_outfile ps1 = ps_outfile s ->
      rw_cells ssegs m1 (bv_unsigned sp + -128) hc -> cells_size hc = 40%nat -> FRS m1 ->
      rw_cells ssegs m1 ERR [C4 ew] -> rw_cells ssegs m1 MG (map (fun z => C1 (Z_to_bv 8 z)) magic) -> rw_cells ssegs m1 EB [CB 256 e] ->
      implM ssegs (ngc_open MOps PR fuel f 0 BT_SHB sw TL) ps1 POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 ERR) (Z_to_bv 64 EB) a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 (Z.b2z sw)) (Z_to_bv 64 FA) s4 s5 s6 w7 (Z_to_bv 64 0) w9 s10 s11 t3' t4' t5' t6')
            F (Z_to_bv 64 0x16820) fc None m1 (seg_rom ssegs)).
  Section Sz8.
  Variables fuel ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' w7 w9 sw TL hi7 hi9 m1 ps1 hc ew e : ltac2:(SecDiet.SzSec.tyM 'ngc_fill__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvv" @fuel).
  Lemma ngc_fill__body : ltac2:(SecDiet.SzSec.bodyP 'ngc_fill__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AI CTX FREE HAL HFL HPL MALLOCS OPEN_COMMON RB RBYTES SFL SNPRINTF. pin_using (fun (AI CTX FREE HAL HFL HPL MALLOCS OPEN_COMMON RB RBYTES SFL SNPRINTF : unit) => tt).
    intros W9 HI9 TLR W7 HI7 MI1 ST1 AG1 G1 OF1 HC1 Hhc FRS1 ERR1 MG1 HEB1.
    pose proof CTX as (G & LO & BU & SPM & TP & ALN & HinF & SITES & GL & GR & R1 & R2 & R3 & E1 & E2 & D1 & E8).
    pose proof (GIo_spw K _ _ _ _ _ G) as SPW. pose proof (GIo_sp47 K _ _ _ _ _ G) as SP47. pose proof (bv_unsigned_in_range 64 sp) as RSP. change (bv_modulus 64) with (2^64)%Z in RSP.
    pose proof E2 as EBU. unfold rc_spmain in EBU.
    assert (CLB : forall a, in_block CL a -> (a < CEILZ)%Z).
    { intros a Ha. destruct (GIo_CLc_facts K R s CL [] FB m a ltac:(rewrite app_nil_r; exact G) Ha) as [Hc _]. exact (proj2 Hc). }
    unfold ngc_open. cbn [e_fenter e_fret fo_enter fo_ret fo_nop prims]. unfold PCAP_TSTAMP_PRECISION_MICRO. cbn [Z.eqb mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_free prims].
    hide HC1. hide FRS1. hide ERR1. hide MG1.
    unfold implM. iprefix.
    do 4 step.
    apply evt_done. name_sp sp (-128)%Z. eapply (implM_bind ssegs).
    { eapply (OPEN_COMMON _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 R ps1 CL FB lo EB PCAP_NG_SF_TOTAL e);
        [ split; [exact G1|]; split; [rewrite Hsp; exact ST1|]; split; [unfold rc_lo; lia|]; split; [unfold PCAP_L1B_STACK; rewrite Hsp; lia|];
          split; [rewrite Hsp; lia|]; split; [exact MI1|]; split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]
        | reflexivity | reflexivity | reflexivity | right; reflexivity | exact HEB1 | right; rewrite Hsp; lia | exact E8 ]. }
    intros r ps2 ms2 PO. destruct PO as (a0v & m2 & E & OF2 & MI2 & ST2 & AG2 & RM).
    unfold hpost_regs in E. destruct_exs E. subst ms2. rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 0x16830)) with (Z_to_bv 64 0x16830) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    unhide HC1. unhide FRS1. unhide ERR1. unhide MG1.
    transport HC1 m2 AG2 ltac:(intros a Ha; rewrite Hhc in Ha; split; [left; lia| lia]).
    unfold ngc_FRS in FRS1. transport FRS1 m2 AG2 ltac:(prs). transport ERR1 m2 AG2 ltac:(prs). transport MG1 m2 AG2 ltac:(prsMG GL).
    assert (AG12 : AGQ m2).
    { unfold ngc_AGQ in AG1 |- *. eapply agrees_on_trans; [exact AG1|]. eapply agrees_on_weaken; [exact AG2|]. intros a [Ha [Hn _]]. split; [| exact Hn].
      destruct Ha as [Ha|Ha]; [left; lia| right; exact Ha]. }
    clear AG1 AG2 MI1 ST1.
    destruct r as [msg | q].
    { (* [comment removed for export] *)
      destruct RM as (junk2 & -> & G2 & HEB2 & LENM & MOK). cbv iota. apply (implM_ret ssegs).
      hide HC1. hide FRS1. hide ERR1. hide MG1. hide HEB2.
      step. rewrite (eqb_lits_eq 0 0 eq_refl). cbv iota.
      unhide HC1. unhide FRS1. unhide ERR1. unhide MG1. unhide HEB2.
      eapply (ngc_err_exit K sites HFL SFL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R s CL FB lo MG FA EB ERR f magic m);
        [ exact CTX | right; right; split; reflexivity | exact MI2 | exact ST2 | exact AG12 | exact G2 | exact HC1 | exact Hhc | exact FRS1 | exact ERR1 | exact MG1 | exact HEB2
        | exact LENM | exact MOK | rewrite OF2; exact OF1 ]. }
    (* [comment removed for export] *)
    destruct RM as (P & -> & G2 & CELLS0 & HEB2).
    pose proof (GIo_block_ok K _ _ _ _ _ _ G2 ltac:(left; reflexivity)) as (P1 & P2 & P3 & P4 & P5 & P6).
    cbn [cb_addr cb_size fst snd] in P1, P2, P3, P4, P5, P6. unfold PCAP_NG_SF_TOTAL in P4, P5, P6.
    assert (NPB2 : forall a, in_block CL a -> ~ (P <= a < P + 680)%Z).
    { intros a Ha Hin. destruct (GIo_CLc_facts K R ps2 [(q, P, PCAP_NG_SF_TOTAL)] CL FB m2 a G2
                 ltac:(unfold in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; unfold PCAP_NG_SF_TOTAL; exact Hin)) as [_ Hn]. exact (Hn Ha). }
    apply blank_recell_ng in CELLS0. unfold ngcells0, ngcells, ng_cells, ng0, pad0 in CELLS0. cbn [ng_user_tsresol ng_max_blocksize ng_ifcount ng_ifaces_size] in CELLS0.
    destruct (rw_cells_cut _ _ _ 33 CELLS0) as [CELLS NG]. clear CELLS0.
    cbn [firstn skipn cells_size csize Nat.add app] in CELLS, NG.
    replace (P + Z.of_nat 648)%Z with (P + 648)%Z in NG by lia.
    cbv iota.
    set (BS0 := (if 2048 <? TL then TL else 2048)%Z).
    assert (BS0R : (1 <= BS0 <= 2^21 /\ TL <= BS0 /\ 2048 <= BS0)%Z) by (subst BS0; destruct (Z.ltb_spec 2048 TL); lia).
    unfold ngc_buf. cbn [e_fenter e_fret fo_enter fo_ret fo_nop prims]. fold BS0. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_malloc e_free prims].
    hide HC1. hide FRS1. hide ERR1. hide MG1. hide HEB2.
    unfold implM. iprefix.
    step. rewrite (eqb_lits_false P 0) by lia. cbv iota.
    step.
    pose proof (munch_refl [(P, P + 680)]%Z m2) as MU. pose proof (wmono_refl ssegs m2) as WM.
    step. step. step. rewrite (eqb_lits_eq 0 0 eq_refl). cbv iota.
    step. step. pstep.
    step. rewrite (sextw_low w9 TL hi9 W9) by lia.
    step. step. pstep.
    step. unfold bv_ltu. rewrite (unsigned_lit 2048), (unsigned_lit TL) by lia.
    (* [comment removed for export] *)
    assert (K740 : forall (m3 : mem),
      mem_inv ssegs m3 -> stk ssegs m3 lo (bv_unsigned sp + -128) -> munch [(P, P + 680)]%Z m2 m3 -> wmono ssegs m2 m3 ->
      rw_cells ssegs m3 P (ngcells P (C8 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 0)) (C8 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 (Z.b2z sw))) (C4 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 0))
                             (C4 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 0)) (C8 (Z_to_bv 64 0))) ->
      rw_cells ssegs m3 (P + 648) [C8 (Z_to_bv 64 1000000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0)] ->
      evt ssegs (fun ms1 => impl ssegs (at_node ssegs) (npeek ssegs)
           ((Monad.mbind (pmalloc HO BS0)
               (fun b => match b with
                         | Some buf => Monad.mbind (read_bytes MOps PR f (DHeap buf 12) (TL - 12) true)
                                        (fun x : rb_status * list Z => let '(st, data) := x in ngc_after_rb MOps PR fuel 0 sw (ngc_p0 q f 0 BT_SHB sw TL buf 1000000) st data)
                         | None => Monad.mbind (pfree HO q) (fun _ => Monad.mret (@CH_Err hptr hptr Msg.out_of_memory))
                         end)) ps2)
           (epost (fun p0 => POSTQ (fst p0) (snd p0))) ms1)
        (MS (mkR (Z_to_bv 64 0x16830) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp x x0 x1 (Z_to_bv 64 ERR) (Z_to_bv 64 EB)
                 (Z_to_bv 64 P) (Z_to_bv 64 BS0) (Z_to_bv 64 2048) (Z_to_bv 64 0) x5 x6 x7 x8
                 (Z_to_bv 64 (Z.b2z sw)) (Z_to_bv 64 FA) s4 s5 (Z_to_bv 64 (P + 648)) w7 (Z_to_bv 64 0) w9 s10 s11 x9 x10 x11 x12)
            F (Z_to_bv 64 0x1687c) fc None m3 (seg_rom ssegs))).
    2: { destruct (Z.lt_ge_cases 2048 TL) as [LT|GE].
         - rewrite (proj2 (Z.ltb_lt _ _) LT). cbv iota. replace (Z_to_bv 64 TL) with (Z_to_bv 64 BS0) by (subst BS0; rewrite (proj2 (Z.ltb_lt _ _) LT); reflexivity).
           eapply K740; [assumption | assumption | exact MU | exact WM | exact CELLS | exact NG].
         - rewrite (proj2 (Z.ltb_ge _ _) GE). cbv iota. step. replace (Z_to_bv 64 2048) with (Z_to_bv 64 BS0) at 1 by (subst BS0; rewrite (proj2 (Z.ltb_ge _ _) GE); reflexivity).
           eapply K740; [assumption | assumption | exact MU | exact WM | exact CELLS | exact NG]. }
    clear MU WM CELLS NG. intros m3 MI3 ST3 MU WM CELLS NG.
    unfold ngcells in CELLS.
    step. step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m3' end.
    assert (AGS23 : agrees_on (fun a => outside [(P, P + 680)]%Z a) m2 m3') by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]).
    assert (G3 : GIo K R ps2 ((q, P, PCAP_NG_SF_TOTAL) :: CL) FB m3').
    { eapply (GIo_client_frame K HFL SFL); [exact G2 | exact MU | exact WM |]. apply Forall_cons; [| apply Forall_nil]. right.
      unfold iv_in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. unfold PCAP_NG_SF_TOTAL. lia. }
    assert (AG13 : AGQ m3').
    { unfold ngc_AGQ in AG12 |- *. eapply agrees_on_trans; [exact AG12|]. eapply agrees_on_weaken; [exact AGS23|].
      intros a [[Ha|Ha] _]; cbn [outside]; [lia|]. pose proof (NPB2 a Ha). lia. }
    unhide HC1. unhide FRS1. unhide ERR1. unhide MG1. unhide HEB2.
    transport HC1 m3' AGS23 ltac:(intros a Ha; rewrite Hhc in Ha; cbn [outside]; lia). transport FRS1 m3' AGS23 ltac:(prs).
    transport ERR1 m3' AGS23 ltac:(prs). transport MG1 m3' AGS23 ltac:(intros a Ha; rewrite cells_size_map_C1, GL in Ha; cbn [outside]; lia). transport HEB2 m3' AGS23 ltac:(prs).
    clear MU WM AGS23 MI2 ST2 G2. rename ST3 into ST3'.
    (* [comment removed for export] *)
    hide HC1. hide FRS1. hide ERR1. hide MG1. hide HEB2. hide CELLS. hide NG.
    apply evt_done. name_sp sp (-128)%Z. eapply (implM_bind ssegs).
    { eapply (MALLOCS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3' R ps2 ((q, P, PCAP_NG_SF_TOTAL) :: CL) FB lo BS0); [| reflexivity | lia].
      split; [exact G3|]. split; [rewrite Hsp; exact ST3'|]. split; [unfold rc_lo; lia|]. split; [unfold MALLOC_STACK; rewrite Hsp; lia|].
      split; [rewrite Hsp; lia|]. split; [assumption|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
    intros bo ps3 ms3 PO. cbv beta in PO. destruct PO as (a0v & m4 & E & OF3 & MI4 & ST4 & AG4 & RM).
    unfold hpost_regs in E. destruct_exs E. subst ms3. rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 0x1688c)) with (Z_to_bv 64 0x1688c) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    assert (INP3 : forall a, (P <= a < P + 680)%Z -> in_block ((q, P, PCAP_NG_SF_TOTAL) :: CL) a).
    { intros a Ha. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. unfold PCAP_NG_SF_TOTAL. lia. }
    unhide HC1. unhide FRS1. unhide ERR1. unhide MG1. unhide HEB2. unhide CELLS. unhide NG.
    transport HC1 m4 AG4 ltac:(intros a Ha; rewrite Hhc in Ha; left; lia). transport FRS1 m4 AG4 ltac:(prs). transport ERR1 m4 AG4 ltac:(prs).
    transport MG1 m4 AG4 ltac:(intros a Ha; rewrite cells_size_map_C1, GL in Ha; left; lia). transport HEB2 m4 AG4 ltac:(prs).
    transport CELLS m4 AG4 ltac:(prs). transport NG m4 AG4 ltac:(prs).
    assert (AG14 : AGQ m4).
    { unfold ngc_AGQ in AG13 |- *. eapply agrees_on_trans; [exact AG13|]. eapply agrees_on_weaken; [exact AG4|].
      intros a [[Ha|Ha] _]; [left; lia| right]. unfold in_block in Ha |- *. apply Exists_cons_tl. exact Ha. }
    clear AG4 AG13 ST3' G3.
    hide HC1. hide FRS1. hide ERR1. hide MG1. hide HEB2. hide NG.
    unfold implM. iprefix. step.
    destruct bo as [qb|].
    2: { (* [comment removed for export] *)
      destruct RM as (-> & G4 & _). cbv iota.
      pose proof (munch_refl [(P, P + 680)]%Z m4) as MU4. pose proof (wmono_refl ssegs m4) as WM4.
      pstep. step. rewrite (eqb_lits_eq 0 0 eq_refl). cbv iota.
      step. step. step. step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m5 end.
      assert (AGS45 : agrees_on (fun a => outside [(P, P + 680)]%Z a) m4 m5) by (eapply agrees_on_of_munch; [exact MU4 | exact WM4 | intros a _ Ho; exact Ho]).
      assert (G5 : GIo K R ps3 ((q, P, PCAP_NG_SF_TOTAL) :: CL) FB m5).
      { eapply (GIo_client_frame K HFL SFL); [exact G4 | exact MU4 | exact WM4 |]. apply Forall_cons; [| apply Forall_nil]. right.
        unfold iv_in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. unfold PCAP_NG_SF_TOTAL. lia. }
      assert (AG15 : AGQ m5).
      { unfold ngc_AGQ in AG14 |- *. eapply agrees_on_trans; [exact AG14|]. eapply agrees_on_weaken; [exact AGS45|].
        intros a [[Ha|Ha] _]; cbn [outside]; [lia|]. pose proof (NPB2 a Ha). lia. }
      unhide HC1. unhide FRS1. unhide ERR1. unhide MG1. unhide HEB2.
      transport HC1 m5 AGS45 ltac:(intros a Ha; rewrite Hhc in Ha; cbn [outside]; lia). transport FRS1 m5 AGS45 ltac:(prs).
      transport ERR1 m5 AGS45 ltac:(prs). transport MG1 m5 AGS45 ltac:(intros a Ha; rewrite cells_size_map_C1, GL in Ha; cbn [outside]; lia). transport HEB2 m5 AGS45 ltac:(prs).
      clear MU4 WM4 CELLS NG AG14 G4.
      (* [comment removed for export] *)
      assert (LE : length e = 256%nat) by (destruct HEB2 as [[WF _] _]; cbn in WF; (keep_hyps CEILV sp R MG EB ERR TL hi7 hi9 e P WF; tauto)).
      pose proof (rw_cells_split_CB _ _ _ [] _ _ [] [14%nat; 242%nat] HEB2 ltac:(cbn; lia)) as HE'. clear HEB2. cbn [mk_CB_cells app] in HE'.
      destruct (rw_cells_cut _ _ _ 1 HE') as [HE1 HE2]. clear HE'. cbn [firstn skipn cells_size csize Nat.add] in HE1, HE2.
      hide HC1. hide FRS1. hide ERR1. hide MG1. hide HE2.
      assert (LENM : length (map b8 Msg.out_of_memory ++ [Z_to_bv 8 0]) = 14%nat) by (vm_compute; reflexivity).
      eapply evt_cut.
      { eapply (memcpy_specZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ EB 0x10df2%Z 14%Z (map b8 Msg.out_of_memory ++ [Z_to_bv 8 0]) (firstn 14 e));
          [ reflexivity | reflexivity | reflexivity
          | exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image ssegs m5 0x10df2 (map b8 Msg.out_of_memory ++ [Z_to_bv 8 0]) ltac:(assumption) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(rewrite LENM; cbn; lia)))
          | rewrite LENM; reflexivity | lia | exact HE1 | lia | lia | lia | assumption ]. }
      cbv beta. intros ms' PO. destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & m6 & -> & MU6 & WM6 & MI6 & HE1' & _). clear HE1.
      replace (ret_pc (Z_to_bv 64 0x169e8)) with (Z_to_bv 64 0x169e8) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      assert (AGS56 : agrees_on (fun a => outside [(EB, EB + 14)]%Z a) m5 m6) by (eapply agrees_on_of_munch; [exact MU6 | exact WM6 | intros a _ Ho; exact Ho]).
      assert (ST6 : stk ssegs m6 lo (bv_unsigned sp + -128)).
      { eapply stk_transport_disjoint; [eassumption | exact MU6 | exact WM6 | cbn [disjoint_from]; unfold rc_lo in *; lia]. }
      assert (G6 : GIo K R ps3 ((q, P, PCAP_NG_SF_TOTAL) :: CL) FB m6).
      { eapply (GIo_client_frame K HFL SFL); [exact G5 | exact MU6 | exact WM6 |]. apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil]. }
      assert (AG16 : AGQ m6).
      { unfold ngc_AGQ in AG15 |- *. eapply agrees_on_trans; [exact AG15|]. eapply agrees_on_weaken; [exact AGS56|]. intros a [_ [Hn _]]; cbn [outside]. lia. }
      unhide HC1. unhide FRS1. unhide ERR1. unhide MG1. unhide HE2.
      transport HC1 m6 AGS56 ltac:(intros a Ha; rewrite Hhc in Ha; cbn [outside]; lia). transport FRS1 m6 AGS56 ltac:(prs).
      transport ERR1 m6 AGS56 ltac:(prs). transport MG1 m6 AGS56 ltac:(intros a Ha; rewrite cells_size_map_C1, GL in Ha; cbn [outside]; lia). transport HE2 m6 AGS56 ltac:(prs).
      assert (HEB6 : rw_cells ssegs m6 EB [CB (length Msg.out_of_memory + 1) (map b8 Msg.out_of_memory ++ [Z_to_bv 8 0]); CB (255 - length Msg.out_of_memory) (skipn 14 e)]).
      { join_cells HE1' HE2.
        eapply rw_cells_recell; [exact HE1' | pose proof (proj1 (proj1 HE1')) as WF; cbn in WF |- *; rewrite ?length_app, ?length_map, ?length_skipn in *;
                                               assert (LOM : length Msg.out_of_memory = 13%nat) by (vm_compute; reflexivity); rewrite ?LOM, ?LE in *; cbn; repeat split; try lia; tauto |].
        cbn [cells_bytes cbytes app]. rewrite ?firstn_all2 by (rewrite length_skipn, LE; lia). rewrite !app_nil_r, <- app_assoc. reflexivity. }
      hide HC1. hide FRS1. hide ERR1. hide MG1. hide HEB6.
      step. step.
      (* [comment removed for export] *)
      apply evt_done. name_sp sp (-128)%Z. eapply (implM_bind ssegs).
      { eapply (FREE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6 R ps3 [] CL FB q P PCAP_NG_SF_TOTAL lo); [| reflexivity].
        split; [exact G6|]. split; [rewrite Hsp; exact ST6|]. split; [unfold rc_lo; lia|]. split; [unfold FREE_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [exact MI6|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
      intros [] ps7 ms7 PO. cbv beta in PO. destruct PO as (av7 & m7 & E & OF7 & MI7 & ST7 & AG7 & G7).
      unfold hpost_regs in E. destruct_exs E. subst ms7. rewrite Hsp in *. unname_sp.
      replace (ret_pc (Z_to_bv 64 0x169f0)) with (Z_to_bv 64 0x169f0) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      cbn [app] in G7, AG7.
      unhide HC1. unhide FRS1. unhide ERR1. unhide MG1. unhide HEB6.
      transport HC1 m7 AG7 ltac:(intros a Ha; left; lia). transport FRS1 m7 AG7 ltac:(intros a Ha; left; lia). transport ERR1 m7 AG7 ltac:(intros a Ha; left; lia).
      transport MG1 m7 AG7 ltac:(intros a Ha; left; lia). transport HEB6 m7 AG7 ltac:(intros a Ha; left; lia).
      assert (AG17 : AGQ m7).
      { unfold ngc_AGQ in AG16 |- *. eapply agrees_on_trans; [exact AG16|]. eapply agrees_on_weaken; [exact AG7|]. intros a [[Ha|Ha] _]; [left; lia| right; exact Ha]. }
      apply (implM_ret ssegs).
      hide HC1. hide FRS1. hide ERR1. hide MG1. hide HEB6. step. unhide HC1. unhide FRS1. unhide ERR1. unhide MG1. unhide HEB6.
      eapply (ngc_err_exit K sites HFL SFL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R s CL FB lo MG FA EB ERR f magic m);
        [ exact CTX | right; left; reflexivity | exact MI7 | exact ST7 | exact AG17 | exact G7 | exact HC1 | exact Hhc | exact FRS1 | exact ERR1 | exact MG1 | exact HEB6
        | replace (length Msg.out_of_memory) with 13%nat by (vm_compute; reflexivity); lia | msg_ok | rewrite OF7, OF3, OF2; exact OF1 ]. }
    (* [comment removed for export] *)
    destruct RM as (B & bjunk & -> & G4 & HBUF). cbv iota.
    pose proof (GIo_block_ok K _ _ _ _ _ _ G4 ltac:(left; reflexivity)) as (B1 & B2 & B3 & B4 & B5 & B6). cbn [cb_addr cb_size fst snd] in B1, B2, B3, B4, B5, B6.
    pose proof (blocks2_apart K _ _ _ _ _ _ _ _ _ _ _ G4 ltac:(lia) ltac:(unfold PCAP_NG_SF_TOTAL; lia)) as APB. unfold PCAP_NG_SF_TOTAL in APB.
    assert (NPB4 : forall a, in_block CL a -> ~ (P <= a < P + 680)%Z /\ ~ (B <= a < B + BS0)%Z).
    { intros a Ha. pose proof (GIo_perm K HPL _ _ _ _ _ _ G4 (Permutation_app_comm [(qb, B, BS0); (q, P, PCAP_NG_SF_TOTAL)] CL)) as G4'.
      destruct (GIo_CLc_facts K R ps3 CL _ FB m4 a G4' Ha) as [_ Hn]. split; intros Hin; apply Hn; unfold in_block.
      - apply Exists_cons_tl, Exists_cons_hd. cbn [cb_addr cb_size fst snd]. unfold PCAP_NG_SF_TOTAL. lia.
      - apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    pose proof (munch_refl [(P, P + 680); (B, B + 12)]%Z m4) as MU4. pose proof (wmono_refl ssegs m4) as WM4.
    (* [comment removed for export] *)
    pose proof (rw_cells_split_CB _ _ _ [] _ _ [] [4%nat; 4%nat; 4%nat; Z.to_nat (TL - 12); Z.to_nat (BS0 - TL)] HBUF ltac:(cbn; lia)) as HB'. clear HBUF. cbn [mk_CB_cells app] in HB'.
    destruct (rw_cells_cut _ _ _ 3 HB') as [HBH X]. destruct (rw_cells_cut _ _ _ 1 X) as [HBD HBR]. clear HB' X.
    cbn [firstn skipn cells_size csize Nat.add app] in HBH, HBD, HBR.
    lazymatch type of HBD with rw_cells _ _ ?A _ => replace A with (B + 12)%Z in HBD by lia end.
    lazymatch type of HBR with rw_cells _ _ ?A [CB ?n ?j] => replace A with (B + TL)%Z in HBR by lia; replace n with (Z.to_nat (BS0 - TL)) in HBR by lia end.
    hide HBD. hide HBR. unhide NG.
    step. step. rewrite (eqb_lits_false B 0) by lia. cbv iota.
    step. step. step. step. pstep.
    step. rewrite (sextw_low w9 TL hi9 W9) by lia. step.
    pstep. step. step.
    step. step. step. step. step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m5 end.
    assert (AGS45 : agrees_on (fun a => outside [(P, P + 680); (B, B + 12)]%Z a) m4 m5) by (eapply agrees_on_of_munch; [exact MU4 | exact WM4 | intros a _ Ho; exact Ho]).
    assert (G5 : GIo K R ps3 ((qb, B, BS0) :: (q, P, PCAP_NG_SF_TOTAL) :: CL) FB m5).
    { eapply (GIo_client_frame K HFL SFL); [exact G4 | exact MU4 | exact WM4 |]. apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; right; unfold iv_in_block.
      - apply Exists_cons_tl, Exists_cons_hd. cbn [cb_addr cb_size fst snd]. unfold PCAP_NG_SF_TOTAL. lia.
      - apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    assert (AG15 : AGQ m5).
    { unfold ngc_AGQ in AG14 |- *. eapply agrees_on_trans; [exact AG14|]. eapply agrees_on_weaken; [exact AGS45|].
      intros a [[Ha|Ha] _]; cbn [outside]; [lia|]. pose proof (NPB4 a Ha). lia. }
    unhide HC1. unhide FRS1. unhide ERR1. unhide MG1. unhide HEB2. unhide HBD. unhide HBR.
    transport HC1 m5 AGS45 ltac:(intros a Ha; rewrite Hhc in Ha; cbn [outside]; lia). transport FRS1 m5 AGS45 ltac:(prs).
    transport ERR1 m5 AGS45 ltac:(prs). transport MG1 m5 AGS45 ltac:(intros a Ha; rewrite cells_size_map_C1, GL in Ha; cbn [outside]; lia). transport HEB2 m5 AGS45 ltac:(prs).
    transport HBD m5 AGS45 ltac:((keep_hyps CEILV sp R lo EB magic TL hc P B bjunk BS0R APB; prs)). transport HBR m5 AGS45 ltac:((keep_hyps CEILV sp R lo EB magic TL hc P B bjunk TLR APB; prs)).
    clear MU4 WM4 AGS45 G4 AG14.
    (* [comment removed for export] *)
    hide HC1. hide FRS1. hide ERR1. hide MG1. hide CELLS. hide NG. hide HBH. hide HBR.
    apply evt_done. name_sp sp (-128)%Z. eapply (implM_bind ssegs).
    { eapply (RBYTES _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 R ps3 ((qb, B, BS0) :: (q, P, PCAP_NG_SF_TOTAL) :: CL) FB f FA (B + 12)%Z (TL - 12)%Z EB lo true (DHeap qb 12));
        [ split; [exact G5|]; split; [rewrite Hsp; eassumption|]; split; [unfold rc_lo; lia|]; split; [unfold READ_BYTES_STACK, PCAP_L1_STACK; rewrite Hsp; lia|];
          split; [rewrite Hsp; lia|]; split; [assumption|]; split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]
        | exact HinF
        | unfold eval_rdest, blk_addr; cbn [fo_site fo_nop]; rewrite (GIo_addr HO K HAL _ _ _ _ _ _ _ _ G5 ltac:(apply in_or_app; left; left; reflexivity)); reflexivity
        | reflexivity | reflexivity | f_equal; lia | reflexivity | reflexivity | lia
        | exact HBD | left; intros a Ha; unfold in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; lia
        | exact HEB2 | left; rewrite Hsp; lia | lia | exact E8 ]. }
    intros [st got] ps5 ms5 PO. cbv beta in PO.
    destruct PO as (a0v & m6 & junk' & E & OF5 & MI6 & ST6 & AG5 & G6 & HD6 & GR6 & GL6 & RM).
    unfold hpost_regs in E. destruct_exs E. subst ms5. rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 0x168dc)) with (Z_to_bv 64 0x168dc) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    unhide HC1. unhide FRS1. unhide ERR1. unhide MG1. unhide CELLS. unhide NG. unhide HBH. unhide HBR.
    assert (INPB : forall a, (P <= a < P + 680 \/ B <= a < B + BS0)%Z -> in_block ((qb, B, BS0) :: (q, P, PCAP_NG_SF_TOTAL) :: CL) a).
    { intros a [Ha|Ha]; unfold in_block; [apply Exists_cons_tl, Exists_cons_hd| apply Exists_cons_hd]; cbn [cb_addr cb_size fst snd]; unfold PCAP_NG_SF_TOTAL; lia. }
    transport HC1 m6 AG5 ltac:(intros a Ha; rewrite Hhc in Ha; split; [left; lia| lia]). transport FRS1 m6 AG5 ltac:(prs). transport ERR1 m6 AG5 ltac:((keep_hyps CEILV H hptr K sp R CL FB lo MG EB ERR magic TL hc ew q P qb B ps5 m6 LO BU R1 R2 D1 BS0R B4 G6; prs)).
    transport MG1 m6 AG5 ltac:(prsMG GL).
    transport CELLS m6 AG5 ltac:((keep_hyps CEILV H hptr K sp R CL FB lo EB magic sw TL hc q P qb B ps5 m6 LO BU E1 P4 BS0R APB G6 INPB; prs)). transport NG m6 AG5 ltac:((keep_hyps CEILV H hptr K sp R CL FB lo EB magic TL hc q P qb B ps5 m6 LO BU E1 P4 BS0R APB G6 INPB; prs)). transport HBH m6 AG5 ltac:(prs). transport HBR m6 AG5 ltac:(prs).
    assert (AG16 : AGQ m6).
    { unfold ngc_AGQ in AG15 |- *. eapply agrees_on_trans; [exact AG15|]. eapply agrees_on_weaken; [exact AG5|].
      intros a [[Ha|Ha] [Hn _]]; [split; [left; lia| lia]|]. pose proof (CLB a Ha). pose proof (NPB4 a Ha). split; [right; unfold in_block in Ha |- *; do 2 apply Exists_cons_tl; exact Ha| lia]. }
    clear AG5 AG15 G5.
    hide HC1. hide FRS1. hide ERR1. hide MG1. hide CELLS. hide NG. hide HBH. hide HBR. hide HD6.
    unfold implM. iprefix. step. step.
    destruct st as [ | | msg].
    2: { (* [comment removed for export] *) destruct RM as (_ & _ & X & _). discriminate X. }
    2: { (* [comment removed for export] *)
      destruct RM as (junk6 & -> & HEB6 & LENM & MOK).
      change (bv_eqb (Z_to_bv 64 (-1)) (Z_to_bv 64 (-1))) with true. cbv iota.
      unhide HC1. unhide FRS1. unhide ERR1. unhide MG1. unhide CELLS. unhide NG.
      apply evt_done. unfold ngc_after_rb. unfold ngc_fail. cbn [e_fenter e_fret fo_enter fo_ret fo_nop prims]. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_free prims free_opt ng_ifaces_ptr_of pc_buffer pc_self pc_priv ngc_p0 set_bufdata].
      destruct (rw_cells_cut _ _ _ 4 CELLS) as [_ X1]. destruct (rw_cells_cut _ _ _ 1 X1) as [HPB _]. cbn [firstn skipn cells_size csize Nat.add app] in HPB.
      replace (P + Z.of_nat 24)%Z with (P + 24)%Z in HPB by lia.
      destruct (rw_cells_cut _ _ _ 5 NG) as [_ HPI]. cbn [firstn skipn cells_size csize Nat.add app] in HPI.
      replace (P + 648 + Z.of_nat 24)%Z with (P + 672)%Z in HPI by lia.
      eapply (ngc_fail3 HO K sites HFL SFL FREE ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R s CL FB lo MG FA EB ERR f magic m) with (i := None) (ni := 0%Z);
        [ exact CTX | exact MI6 | exact ST6 | exact AG16 | cbn [app]; eapply (GIo_perm K HPL); [exact G6| apply Permutation.perm_swap]
        | reflexivity | exact HC1 | exact Hhc | exact FRS1 | exact ERR1 | exact MG1 | exact HEB6
        | exact LENM | exact MOK | rewrite OF5, OF3, OF2; exact OF1 | exact HPB | exact HPI | lia | lia | lia ]. }
    (* [comment removed for export] *)
    destruct RM as (-> & GLn & HEB6).
    change (bv_eqb (Z_to_bv 64 1) (Z_to_bv 64 (-1))) with false. cbv iota.
    unfold zlength in GLn, GL6.
    (* [comment removed for export] *)
    destruct got as [|g0 [|g1 [|g2 [|g3 rest]]]]; try (exfalso; cbn [length] in GLn; (keep_hyps CEILV sp R lo EB magic TL hc P B TLR GLn g0 g1 g2; lia)).
    pose proof (Forall_inv GR6) as X0. pose proof (Forall_inv (Forall_inv_tail GR6)) as X1.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail GR6))) as X2. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail GR6)))) as X3.
    cbv beta in X0, X1, X2, X3.
    assert (Lrest : Z.of_nat (length rest) = (TL - 16)%Z) by (cbn [length] in GLn; lia).
    unhide HD6. destruct (rw_cells_cut _ _ _ 1 HD6) as [HDg _]. clear HD6. cbn [firstn skipn cells_size csize Nat.add app map] in HDg.
    pose proof (rw_cells_recell _ _ _ [C2 (Z_to_bv 64 (g0 + 256 * g1)); C2 (Z_to_bv 64 (g2 + 256 * g3)); CB (length rest) (map b8 rest)] HDg
                  ltac:(cbn; rewrite ?length_map; repeat split; fastfirst (first [reflexivity | lia | exact Logic.I]))
                  ltac:(cbn [cells_bytes cbytes app]; rewrite !le2_lit by lia; rewrite !app_nil_r; reflexivity)) as HDV. clear HDg.
    (* [comment removed for export] *)
    set (HDR := le_bytes 4 BT_SHB ++ le_bytes 4 TL ++ le_bytes 4 BYTE_ORDER_MAGIC).
    assert (LHDR : length HDR = 12%nat) by (subst HDR; rewrite !length_app, !length_le_bytes; reflexivity).
    assert (GHDR : Forall (fun z => 0 <= z < 256)%Z HDR).
    { subst HDR. apply (proj2 (Forall_app _ _ _)). split; [apply le_bytes_4_range|]. apply (proj2 (Forall_app _ _ _)). split; apply le_bytes_4_range. }
    assert (BHDR : map b8 HDR = le4 (Z_to_bv 64 168627466) ++ le4 w9 ++ le4 w7).
    { subst HDR. rewrite !map_app. rewrite (le4_low w9 TL hi9 W9), (le4_low w7 BYTE_ORDER_MAGIC hi7 W7) by (unfold BYTE_ORDER_MAGIC; lia).
      rewrite (le4_le_bytes 168627466) by lia. reflexivity. }
    unfold ngc_after_rb. cbn [pc_bufdata ngc_p0 set_bufdata pc_self pc_rfile pc_bufsize pc_bufalloc pc_buffer pc_swapped pc_snapshot pc_linktype pc_linktype_ext pc_priv].
    fold BS0. fold HDR.
    (* [comment removed for export] *)
    assert (KVER : forall (a2x a3x : word) (m7 : mem) (v0 v1 v2 v3 : Z) (jr : list byte),
      (0 <= v0 < 256)%Z -> (0 <= v1 < 256)%Z -> (0 <= v2 < 256)%Z -> (0 <= v3 < 256)%Z ->
      mem_inv ssegs m7 -> stk ssegs m7 lo (bv_unsigned sp + -128) -> AGQ m7 -> GIo K R ps5 ((qb, B, BS0) :: (q, P, PCAP_NG_SF_TOTAL) :: CL) FB m7 ->
      rw_cells ssegs m7 (bv_unsigned sp + -128) hc -> FRS m7 -> rw_cells ssegs m7 ERR [C4 ew] -> rw_cells ssegs m7 MG (map (fun z => C1 (Z_to_bv 8 z)) magic) ->
      rw_cells ssegs m7 EB [CB 256 e] ->
      rw_cells ssegs m7 P (ngcells P (C8 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 BS0)) (C8 (Z_to_bv 64 B)) (C4 (Z_to_bv 64 (Z.b2z sw))) (C4 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 0))
                             (C4 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 0)) (C4 (Z_to_bv 64 0)) (C8 (Z_to_bv 64 0))) ->
      rw_cells ssegs m7 (P + 648) [C8 (Z_to_bv 64 1000000); C4 (Z_to_bv 64 16777216); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0)] ->
      rw_cells ssegs m7 B [C4 (Z_to_bv 64 168627466); C4 w9; C4 w7] ->
      rw_cells ssegs m7 (B + 12) [C2 (Z_to_bv 64 (v0 + 256 * v1)); C2 (Z_to_bv 64 (v2 + 256 * v3)); CB (length rest) (map b8 rest)] ->
      rw_cells ssegs m7 (B + TL) [CB (Z.to_nat (BS0 - TL)) jr] ->
      Forall (fun z => 0 <= z < 256)%Z rest ->
      evt ssegs (fun ms1 => impl ssegs (at_node ssegs) (npeek ssegs)
           ((if negb ((v0 + 256 * v1 =? 1) && ((v2 + 256 * v3 =? 0) || (v2 + 256 * v3 =? 2)))%Z
             then ngc_fail MOps PR (Msg.unsupported_pcapng_version (v0 + 256 * v1) (v2 + 256 * v3))
                    (mkPcap q f BS0 BS0 qb (HDR ++ v0 :: v1 :: v2 :: v3 :: rest) sw 0 0 0 0 0 0 0 [] hdr0 (PrivNg (mkNg 1000000 INITIAL_MAX_BLOCKSIZE 0 0 []) None))
             else ngc_find MOps PR fuel 0
                    (mkPcap q f BS0 BS0 qb (HDR ++ v0 :: v1 :: v2 :: v3 :: rest) sw (v0 + 256 * v1) (v2 + 256 * v3) 0 0 0 0 0 [] hdr0 (PrivNg (mkNg 1000000 INITIAL_MAX_BLOCKSIZE 0 0 []) None))) ps5)
           (epost (fun p0 => POSTQ (fst p0) (snd p0))) ms1)
        (MS (mkR (Z_to_bv 64 0x168dc) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp x27 x28 x29 (Z_to_bv 64 ERR) (Z_to_bv 64 EB)
                 (Z_to_bv 64 P) (Z_to_bv 64 ((v0 + 256 * v1) * 2 ^ 48)) a2x a3x x33 x34 x35 x36
                 (Z_to_bv 64 P) (Z_to_bv 64 FA) (Z_to_bv 64 B) (Z_to_bv 64 (B + 12)) (Z_to_bv 64 (P + 648)) (Z_to_bv 64 1) (Z_to_bv 64 0) w9 s10 s11 x37 x38 x39 x40)
            F (Z_to_bv 64 0x1691c) fc None m7 (seg_rom ssegs))).
    { intros until jr. intros V0 V1 V2 V3 MI7 ST7 AG7 G7 HC7 FRS7 ERR7 MG7 HEB7 CELLS7 NG7 HBH7 HDV7 HBR7 GRr.
      clear HEB6 GLn GL6 GR6.
      hide HC7. hide FRS7. hide ERR7. hide MG7. hide HEB7. hide CELLS7. hide NG7. hide HBH7. hide HBR7.
      step. rewrite (zx16_lit (v2 + 256 * v3)) by lia. step. rewrite (shr48_of_shl48 (v0 + 256 * v1)) by lia. step. step.
      set (MAJ := (v0 + 256 * v1)%Z) in *. set (MIN := (v2 + 256 * v3)%Z) in *.
      assert (MAJR : (0 <= MAJ < 65536)%Z) by lia. assert (MINR : (0 <= MIN < 65536)%Z) by lia.
      (* [comment removed for export] *)
      assert (VERR : forall (a1y s4y : word) (m8 : mem),
        mem_inv ssegs m8 -> stk ssegs m8 lo (bv_unsigned sp + -128) -> m8 = m7 ->
        evt ssegs (fun ms1 => impl ssegs (at_node ssegs) (npeek ssegs)
             (ngc_fail MOps PR (Msg.unsupported_pcapng_version MAJ MIN)
                      (mkPcap q f BS0 BS0 qb (HDR ++ v0 :: v1 :: v2 :: v3 :: rest) sw 0 0 0 0 0 0 0 [] hdr0 (PrivNg (mkNg 1000000 INITIAL_MAX_BLOCKSIZE 0 0 []) None)) ps5)
             (epost (fun p0 => POSTQ (fst p0) (snd p0))) ms1)
          (MS (mkR (Z_to_bv 64 0x168dc) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp x27 x28 x29 (Z_to_bv 64 ERR) (Z_to_bv 64 EB)
                   (Z_to_bv 64 P) a1y a2x (Z_to_bv 64 MAJ) (Z_to_bv 64 MIN) x34 x35 x36
                   (Z_to_bv 64 P) (Z_to_bv 64 FA) s4y (Z_to_bv 64 (B + 12)) (Z_to_bv 64 (P + 648)) (Z_to_bv 64 1) (Z_to_bv 64 0) w9 s10 s11 x37 x38 x39 x40)
              F (Z_to_bv 64 0x169f4) fc None m8 (seg_rom ssegs))).
      { intros a1y s4y m8 MI8 ST8 ->.
        do 5 step.
        unhide HC7. unhide FRS7. unhide ERR7. unhide MG7. unhide HEB7. unhide CELLS7. unhide NG7.
        assert (MSG : fmt_at m7 0x105d0 "unsupported pcapng savefile version %u.%u"%string)
          by (apply (fmt_at_intro m7 _ _ MI8); [vm_compute; reflexivity| lia| cbn; lia]).
        destruct (rw_cells_cut _ _ _ 4 CELLS7) as [_ Y1]. destruct (rw_cells_cut _ _ _ 1 Y1) as [HPB _]. cbn [firstn skipn cells_size csize Nat.add app] in HPB.
        replace (P + Z.of_nat 24)%Z with (P + 24)%Z in HPB by lia.
        destruct (rw_cells_cut _ _ _ 5 NG7) as [_ HPI]. cbn [firstn skipn cells_size csize Nat.add app] in HPI.
        replace (P + 648 + Z.of_nat 24)%Z with (P + 672)%Z in HPI by lia.
        apply evt_done.
        eapply (ngc_snp_fail HO K sites HFL SFL HPL FREE SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m R s CL FB lo MG FA EB ERR f magic CTX q P sw BS0 0 ew
                   (conj P1 P4)
                   _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 MAJ) (Z_to_bv 64 MIN) _ _ _ _ _ 0x16a08 m7 ps5
                   "unsupported pcapng savefile version %u.%u"%string [AInt MAJ; AInt MIN] 0x105d0 (Msg.unsupported_pcapng_version MAJ MIN) (HDR ++ v0 :: v1 :: v2 :: v3 :: rest)
                   qb None (mkNg 1000000 INITIAL_MAX_BLOCKSIZE 0 0 []) B 0 BS0 e hc);
          [ right; reflexivity | exact MI8 | exact ST8 | exact AG7 | cbn [IBLK app]; eapply (GIo_perm K HPL); [exact G7| apply Permutation.perm_swap] | rewrite OF5, OF3, OF2; exact OF1
          | reflexivity | exact HC7 | exact Hhc | exact FRS7 | exact ERR7 | exact MG7 | exact HEB7 | exact HPB | exact HPI | lia | lia
          | exact MSG | reflexivity | cbn; lia | intros; cbn [length firstn]; constructor; [reflexivity|]; constructor; [reflexivity| constructor]
          | vm_compute; reflexivity | apply args_ok_ints2 | unfold Msg.unsupported_pcapng_version, PCAP_ERRBUF_SIZE; reflexivity ]. }
      destruct (Z.eq_dec MAJ 1) as [M1|M1].
      2: { rewrite (eqb_lits_false MAJ 1) by lia. rewrite (proj2 (Z.eqb_neq _ _) M1). cbn [negb andb]. cbv iota. eapply VERR; [exact MI7 | exact ST7 | reflexivity]. }
      rewrite (eqb_lits_eq MAJ 1 M1). cbn [negb]. cbv iota.
      step. step. step.
      unfold bv_eqb at 1. rewrite (unsigned_lit MIN), (unsigned_lit 2) by lia. rewrite (unsigned_lit (Z.lor MIN 2)) by (pose proof (lor2_range MIN MINR); lia).
      rewrite (lor2_eqb2 MIN) by lia. rewrite (proj2 (Z.eqb_eq _ _) M1). cbn [andb].
      destruct ((MIN =? 0) || (MIN =? 2)) eqn:MOK; cbn [negb]; cbv iota.
      2: { eapply VERR; [exact MI7 | exact ST7 | reflexivity]. }
      (* [comment removed for export] *)
      unhide CELLS7. unhide NG7. unfold ngcells in CELLS7.
      pose proof (munch_refl [(P, P + 680)]%Z m7) as MU7. pose proof (wmono_refl ssegs m7) as WM7.
      step. pstep. step. pstep. step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m9 end.
      assert (AGS79 : agrees_on (fun a => outside [(P, P + 680)]%Z a) m7 m9) by (eapply agrees_on_of_munch; [exact MU7 | exact WM7 | intros a _ Ho; exact Ho]).
      assert (G9 : GIo K R ps5 ((q, P, 680%Z) :: (qb, B, BS0) :: CL) FB m9).
      { eapply (GIo_perm K HPL); [| apply Permutation.perm_swap]. unfold PCAP_NG_SF_TOTAL in G7.
        eapply (GIo_client_frame K HFL SFL); [exact G7 | exact MU7 | exact WM7 |]. apply Forall_cons; [| apply Forall_nil]. right.
        unfold iv_in_block. apply Exists_cons_tl, Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
      assert (AG9 : AGQ m9).
      { unfold ngc_AGQ in AG7 |- *. eapply agrees_on_trans; [exact AG7|]. eapply agrees_on_weaken; [exact AGS79|].
        intros a [[Ha|Ha] _]; cbn [outside]; [lia|]. pose proof (NPB4 a Ha). lia. }
      unhide HC7. unhide FRS7. unhide ERR7. unhide MG7. unhide HEB7. unhide HBH7. unhide HBR7.
      transport HC7 m9 AGS79 ltac:(intros a Ha; rewrite Hhc in Ha; cbn [outside]; lia). unfold ngc_FRS in FRS7. transport FRS7 m9 AGS79 ltac:(prs).
      transport ERR7 m9 AGS79 ltac:(prs). transport MG7 m9 AGS79 ltac:(intros a Ha; rewrite cells_size_map_C1, GL in Ha; cbn [outside]; lia). transport HEB7 m9 AGS79 ltac:(prs).
      transport HBH7 m9 AGS79 ltac:((keep_hyps CEILV sp R lo EB magic w7 w9 TL hc P B rest v0 v1 v2 v3 BS0R APB; prs)). transport HBR7 m9 AGS79 ltac:((keep_hyps CEILV sp R lo EB magic TL hc P B rest v0 v1 v2 v3 jr TLR APB; prs)).
      (* [comment removed for export] *)
      assert (Ljr : length jr = Z.to_nat (BS0 - TL)) by (pose proof (proj1 (proj1 HBR7)) as WF; cbn in WF; lia).
      assert (BUF9 : rw_cells ssegs m9 B [CB (Z.to_nat BS0) (map b8 (HDR ++ v0 :: v1 :: v2 :: v3 :: rest) ++ jr)]).
      { replace (B + 12)%Z with (B + Z.of_nat (cells_size [C4 (Z_to_bv 64 168627466); C4 w9; C4 w7]))%Z in HDV7 by (cbn; lia).
        pose proof (rw_cells_uncut _ _ _ _ _ HBH7 HDV7 ltac:(cbn; lia)) as J1.
        replace (B + TL)%Z with (B + Z.of_nat (cells_size ([C4 (Z_to_bv 64 168627466); C4 w9; C4 w7] ++ [C2 (Z_to_bv 64 (v0 + 256 * v1)); C2 (Z_to_bv 64 (v2 + 256 * v3)); CB (length rest) (map b8 rest)])))%Z in HBR7
          by (rewrite cells_size_app; cbn [cells_size csize Nat.add]; lia).
        pose proof (rw_cells_uncut _ _ _ _ _ J1 HBR7 ltac:(reflexivity)) as J2. cbn [app] in J2.
        eapply rw_cells_recell; [exact J2 | cbn; rewrite ?length_app, ?length_map; cbn; rewrite ?length_app, ?LHDR; cbn; repeat split; try exact Logic.I; lia |].
        cbn [cells_bytes cbytes app]. cbv delta [MAJ MIN]. rewrite map_app, BHDR. cbn [map app]. rewrite !le2_lit by lia. rewrite !app_nil_r, <- !app_assoc. reflexivity. }
      clear HBH7 HDV7 HBR7.
      rewrite M1. apply evt_done.
      eapply (ngc_loop HO K sites HFL SFL HPL FREE SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m R s CL FB lo MG FA EB ERR f magic CTX q P sw BS0 MIN ew
                (conj P1 P4) P2 ltac:(lia) ltac:(lia) RB AI fuel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (-1)) m9 ps5 qb B BS0 (HDR ++ v0 :: v1 :: v2 :: v3 :: rest)
                (mkNg 1000000 INITIAL_MAX_BLOCKSIZE 0 0 []) None 0 pad0 _ e hc); [vm_compute; reflexivity|].
      split; [exact MI7|]. split; [exact ST7|]. split; [exact AG9|]. split; [cbn [IBLK app]; exact G9|]. split; [rewrite OF5, OF3, OF2; exact OF1|].
      split; [exact HC7|]. split; [exact Hhc|]. split; [exact FRS7|]. split; [exact ERR7|]. split; [exact MG7|]. split; [exact HEB7|].
      split; [exact CELLS7|]. split; [unfold ng_cells, pad0, INITIAL_MAX_BLOCKSIZE; cbn [ng_user_tsresol ng_max_blocksize ng_ifcount ng_ifaces_size]; exact NG7|].
      split; [reflexivity|]. split; [reflexivity|]. split; [cbn; lia|]. split; [cbn; lia|].
      split; [unfold ifaces_ok; cbn; repeat split; reflexivity|].
      split; [exact BUF9|].
      split; [cbn [pc_bufdata ngc_p]; apply firstn_len_app'; rewrite length_map; reflexivity|].
      split; [cbn [pc_bufdata ngc_p]; rewrite length_app, LHDR; cbn [length]; lia|]. split; [lia|]. split; [lia|].
      cbn [pc_bufdata ngc_p]. apply Forall_app. split; [exact GHDR|]. repeat (constructor; [cbv beta; lia|]). exact GRr. }
    unhide CELLS.
    step. step. rewrite (sx32_small (Z.b2z sw)) by (destruct sw; cbn; lia). step. step.
    destruct sw; cbn [Z.b2z].
    - (* [comment removed for export] *)
      rewrite (eqb_lits_false 1 0) by lia. cbv iota.
      pose proof (munch_refl [(B + 12, B + 16)]%Z m6) as MUv. pose proof (wmono_refl ssegs m6) as WMv.
      hide CELLS. hide HEB6.
      do 9 step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m7 end.
      rewrite (swap16_word g0 g1), (swap16_word g2 g3) in HDV |- * by lia.
      pose proof (rw_cells_recell _ _ _ [C2 (Z_to_bv 64 (g1 + 256 * g0)); C2 (Z_to_bv 64 (g3 + 256 * g2)); CB (length rest) (map b8 rest)] HDV
                    ltac:(cbn; rewrite ?length_map; repeat split; fastfirst (first [reflexivity | lia | exact Logic.I]))
                    ltac:(cbn [cells_bytes cbytes app]; rewrite !le2_lit by (keep_hyps CEILV sp R EB magic TL hc P B g0 g1 g2 g3 rest X1 X0 X3 X2; lia);
                          rewrite (le2_of_val (Z_to_bv 64 (g1 + 256 * g0 + 65536 * g1)) g1 g0 g1) by (fastfirst (first [(keep_hyps CEILV sp R EB magic TL hc P B g0 g1 g2 g3 rest X1 X0; lia) | rewrite unsigned_lit by (keep_hyps CEILV sp R lo EB magic TL hc P B g0 g1 g2 g3 rest X0 X1; lia); (keep_hyps CEILV sp R EB magic TL hc P B g0 g1 g2 g3 rest; lia)]));
                          rewrite (le2_of_val (Z_to_bv 64 (g3 + 256 * g2 + 65536 * g3)) g3 g2 g3) by (fastfirst (first [(keep_hyps CEILV sp R EB magic TL hc P B g0 g1 g2 g3 rest X3 X2; lia) | rewrite unsigned_lit by (keep_hyps CEILV sp R lo EB magic TL hc P B g0 g1 g2 g3 rest X2 X3; lia); (keep_hyps CEILV sp R EB magic TL hc P B g0 g1 g2 g3 rest; lia)])); reflexivity)) as HDV'. clear HDV.
      step. rewrite (swap16_shl48 g1 g0) by lia.
      assert (AGSv : agrees_on (fun a => outside [(B + 12, B + 16)]%Z a) m6 m7) by (eapply agrees_on_of_munch; [exact MUv | exact WMv | intros a _ Ho; exact Ho]).
      assert (G7 : GIo K R ps5 ((qb, B, BS0) :: (q, P, PCAP_NG_SF_TOTAL) :: CL) FB m7).
      { eapply (GIo_client_frame K HFL SFL); [exact G6 | exact MUv | exact WMv |]. apply Forall_cons; [| apply Forall_nil]. right. unfold iv_in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
      assert (AG17 : AGQ m7).
      { unfold ngc_AGQ in AG16 |- *. eapply agrees_on_trans; [exact AG16|]. eapply agrees_on_weaken; [exact AGSv|].
        intros a [[Ha|Ha] _]; cbn [outside]; [lia|]. pose proof (NPB4 a Ha). (keep_hyps CEILV sp R lo EB magic TL hc P B g0 g1 g2 g3 rest a BS0R H0; lia). }
      unhide HC1. unhide FRS1. unhide ERR1. unhide MG1. unhide CELLS. unhide NG. unhide HBH. unhide HBR. unhide HEB6.
      transport HC1 m7 AGSv ltac:(intros a Ha; rewrite Hhc in Ha; cbn [outside]; lia). transport FRS1 m7 AGSv ltac:(prs). transport ERR1 m7 AGSv ltac:(prs).
      transport MG1 m7 AGSv ltac:(intros a Ha; rewrite cells_size_map_C1, GL in Ha; cbn [outside]; lia). transport CELLS m7 AGSv ltac:((keep_hyps CEILV sp R lo EB magic TL hc P B g0 g1 g2 g3 rest BS0R APB; prs)). transport NG m7 AGSv ltac:((keep_hyps CEILV sp R lo EB magic TL hc P B g0 g1 g2 g3 rest BS0R APB; prs)).
      transport HBH m7 AGSv ltac:(prs). transport HBR m7 AGSv ltac:(prs). transport HEB6 m7 AGSv ltac:(prs).
      (* [comment removed for export] *)
      assert (SW12 : swap_field 2 14 (swap_field 2 12 (HDR ++ g0 :: g1 :: g2 :: g3 :: rest)) = HDR ++ g1 :: g0 :: g3 :: g2 :: rest).
      { replace 12%Z with (Z.of_nat (length HDR)) by lia. rewrite swap2_at. replace 14%Z with (Z.of_nat (length HDR) + 2)%Z by lia. rewrite swap2_at2. reflexivity. }
      rewrite !SW12. cbn [pc_bufdata set_bufdata pc_self pc_rfile pc_bufsize pc_bufalloc pc_buffer pc_swapped pc_snapshot pc_linktype pc_linktype_ext pc_priv].
      replace (get_le16 (HDR ++ g1 :: g0 :: g3 :: g2 :: rest) 12) with (g1 + 256 * g0)%Z by (replace 12%Z with (Z.of_nat (length HDR)) by lia; symmetry; apply get_le16_at).
      replace (get_le16 (HDR ++ g1 :: g0 :: g3 :: g2 :: rest) 14) with (g3 + 256 * g2)%Z by (replace 14%Z with (Z.of_nat (length HDR) + 2)%Z by lia; symmetry; apply get_le16_at2).
      eapply (KVER _ _ m7 g1 g0 g3 g2);
        [ lia | lia | lia | lia | assumption | assumption | exact AG17 | exact G7 | exact HC1 | exact FRS1 | exact ERR1 | exact MG1 | exact HEB6 | exact CELLS | exact NG
        | exact HBH | exact HDV' | exact HBR | do 4 apply Forall_inv_tail in GR6; exact GR6 ].
    - (* [comment removed for export] *)
      rewrite (eqb_lits_eq 0 0 eq_refl). cbv iota.
      rewrite (zx16_lit (g0 + 256 * g1)) by lia. step. rewrite (shl48_lit (g0 + 256 * g1)) by lia.
      unhide HC1. unhide FRS1. unhide ERR1. unhide MG1. unhide NG. unhide HBH. unhide HBR.
      cbn [pc_bufdata set_bufdata pc_self pc_rfile pc_bufsize pc_bufalloc pc_buffer pc_swapped pc_snapshot pc_linktype pc_linktype_ext pc_priv].
      replace (get_le16 (HDR ++ g0 :: g1 :: g2 :: g3 :: rest) 12) with (g0 + 256 * g1)%Z by (replace 12%Z with (Z.of_nat (length HDR)) by lia; symmetry; apply get_le16_at).
      replace (get_le16 (HDR ++ g0 :: g1 :: g2 :: g3 :: rest) 14) with (g2 + 256 * g3)%Z by (replace 14%Z with (Z.of_nat (length HDR) + 2)%Z by lia; symmetry; apply get_le16_at2).
      eapply (KVER _ _ m6 g0 g1 g2 g3);
        [ lia | lia | lia | lia | assumption | assumption | exact AG16 | exact G6 | exact HC1 | exact FRS1 | exact ERR1 | exact MG1 | exact HEB6 | exact CELLS | exact NG
        | exact HBH | exact HDV | exact HBR | do 4 apply Forall_inv_tail in GR6; exact GR6 ].
  Qed.
  End Sz8.
  Lemma ngc_fill : ltac:(let t := eval cbv delta [ngc_fill__stmt] in ngc_fill__stmt in exact t).
  Proof using AI CTX FREE HAL HFL HPL MALLOCS OPEN_COMMON RB RBYTES SFL SNPRINTF. intros fuel ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' w7 w9 sw TL hi7 hi9 m1 ps1 hc ew e. ltac2:(SecDiet.SzSec.closeP 'ngc_fill__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End ChkNg.

End WithCeil.
End F_sfpcapng_chkE.

(* [comment removed for export] *)
Module F_ngnextI.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep MonadX Image ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_ngnextA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Startup_B__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_ngnextD__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.Pcap_iface_pp OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface_ng OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.PPFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.PP_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.NpArith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextS.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia_e2w2_base := first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                                 | zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac ceil_mentioned := lazymatch goal with | |- context [@alloc_ceiling _] => idtac | _ : context [@alloc_ceiling _] |- _ => idtac end.
(* [comment removed for export] *)
Local Ltac gio_ceil_fact :=
  match goal with
  | G : GIo _ _ _ _ _ _ |- _ => let H := fresh "CLO__" in pose proof (PcapRep.GIo_ceil_lo _ _ _ _ _ _ G) as H; unfold rc_lo in H
  end.
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try gio_ceil_fact; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Close Scope bv_scope.
(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Lemma zext16_shifts : forall (w : word),
  Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned w) 48))) 48) = Z_to_bv 64 (bv_unsigned w mod 2^16).
Proof using Type. pin_using tt.
  intros w. pose proof (bv_unsigned_in_range 64 w) as R. unfold bv_modulus in R. cbn in R.
  f_equal. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. rewrite unsigned_lit_wrap. Z.div_mod_to_equations. lia.
Qed.
(* [comment removed for export] *)
Lemma sxv_s32_word : forall a b c d, 0 <= a < 256 -> 0 <= b < 256 -> 0 <= c < 256 -> 0 <= d < 256 ->
  Z_to_bv 64 (sxv a b c d) = Z_to_bv 64 (s32 (le4val a b c d)).
Proof using Type. pin_using tt.
  intros a b c d Ha Hb Hc Hd. rewrite <- (sx32_lit a b c d) by lia. apply sx32_s32. unfold le4val. lia.
Qed.
(* [comment removed for export] *)
Lemma idb_splice_le16 : forall (data : list Z) l1 l0 r0 r1 n3 n2 n1 n0, (16 <= length data)%nat ->
  get_le16 (firstn 8 data ++ [l1; l0; r0; r1; n3; n2; n1; n0] ++ skipn 16 data) 8 = l1 + 256 * l0.
Proof using Type. pin_using tt.
  intros data l1 l0 r0 r1 n3 n2 n1 n0 Hl.
  assert (L8 : length (firstn 8 data) = 8%nat) by (rewrite length_firstn; lia).
  rewrite (get_le16_of_slice 8 _ l1 l0); [lia|].
  unfold zslice, zfirstn, zskipn. change (Z.to_nat 8) with 8%nat. change (Z.to_nat 2) with 2%nat.
  rewrite skipn_app, L8, skipn_all2 by lia. cbn [Nat.sub skipn app firstn]. reflexivity.
Qed.
Lemma idb_splice_le32 : forall (data : list Z) l1 l0 r0 r1 n3 n2 n1 n0, (16 <= length data)%nat ->
  get_le32 (firstn 8 data ++ [l1; l0; r0; r1; n3; n2; n1; n0] ++ skipn 16 data) 12 = le4val n3 n2 n1 n0.
Proof using Type. pin_using tt.
  intros data l1 l0 r0 r1 n3 n2 n1 n0 Hl.
  assert (L8 : length (firstn 8 data) = 8%nat) by (rewrite length_firstn; lia).
  rewrite (get_le32_of_slice 12 _ n3 n2 n1 n0); [unfold le4val; lia|].
  unfold zslice, zfirstn, zskipn. change (Z.to_nat 12) with 12%nat. change (Z.to_nat 4) with 4%nat.
  rewrite skipn_app, L8, skipn_all2 by lia. cbn [Nat.sub skipn app firstn]. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma idb_swap_data' : forall data, 16 <= Z.of_nat (length data) ->
  swap_field 4 12 (swap_field 2 8 data)
  = firstn 8 data ++ [q8 data 8 1; q8 data 8 0; q8 data 10 0; q8 data 10 1; q8 data 12 3; q8 data 12 2; q8 data 12 1; q8 data 12 0] ++ skipn 16 data.
Proof using Type. pin_using tt. intros data Hl. rewrite idb_swap_data by lia. reflexivity. Qed.
End WithCeil.

Local Open Scope bv_scope.
Section WithCeil.
Context {CEILV : CEIL}.
Section NgnCtx.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HPL : heap_perm_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis SNPRINTF : snprintf_spec_stmt K.
  Hypothesis PP : post_process_stmt.
  Hypothesis ADJ : adjust_snapshot_stmt.
  Hypothesis RBLK : read_block_stmt HO K sites.
  Hypothesis ADDIF : add_interface_stmt HO K sites.

  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (R : rctx) (CLc FB : list (cblock (hptr:=hptr))) (lo P HA DA Af : Z) (m : mem) (o : option hptr).
  Variables (self f : hptr) (bufsize : Z) (swapped : bool) (vmaj vmin snapshot linktype ltext prec brk : Z) (header : pkthdr).
  Hypothesis LO : (usp0 R - 8388608 <= lo)%Z.
  Hypothesis BU : (lo + 81920 <= bv_unsigned sp)%Z.
  Hypothesis SPM : (bv_unsigned sp <= rc_spmain R)%Z.
  Hypothesis TP : tp = rc_tp R.
  Hypothesis ALN : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis SITES : sites = sites_at (bv_unsigned sp + D_NEXT_PACKET).
  Hypothesis R1 : (bv_unsigned sp <= HA)%Z.
  Hypothesis R2 : (HA + 24 <= DA)%Z.
  Hypothesis R3 : (DA + 8 <= rc_spmain R)%Z.
  Hypothesis AH : (HA mod 8 = 0)%Z.
  Hypothesis AD : (DA mod 8 = 0)%Z.
  Hypothesis SPW : (140735340871680 <= usp0 R)%Z.
  Hypothesis SP47 : (usp0 R <= 2^47)%Z.
  Hypothesis HinF : In (f, Af, FILE_BLOCK) FB.
  Hypothesis P1 : (0 < P)%Z.  Hypothesis P2 : (P mod 16 = 0)%Z.  Hypothesis P4 : (P + 680 <= CEILZ)%Z.
  Hypothesis P5 : (P + 680 <= 65536 \/ 348160 <= P)%Z.  Hypothesis P6 : (P + 680 <= utp R - 200 \/ utp R - 200 + 4096 <= P)%Z.
  Hypothesis A1 : (0 < Af)%Z.  Hypothesis A4 : (Af + 1264 <= CEILZ)%Z.
  Hypothesis W1 : (1 <= snapshot <= INT_MAX)%Z.  Hypothesis W2 : (0 <= bufsize <= 2^30)%Z.
  Hypothesis W5 : brk = 0%Z.  Hypothesis W6 : prec = 0%Z.
  Hypothesis W7 : (0 <= vmaj < 2^16)%Z.  Hypothesis W8 : (0 <= vmin < 2^16)%Z.
  Hypothesis W9 : (0 <= linktype < 2^31)%Z.  Hypothesis W10 : (-2^31 <= ltext < 2^31)%Z.

  Let POSTQ := next_packet_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o.

  (* [comment removed for export] *)
  #[local] Abbreviation pv := (F_ngnextA.pv self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header).
  #[local] Abbreviation ngn_frame := (F_ngnextA.ngn_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 P HA DA).
  #[local] Abbreviation ngn_final := (F_ngnextA.ngn_final K sp R CLc FB P HA DA m o).
  #[local] Abbreviation ngn_finalC := (F_ngnextA.ngn_finalC K sp R CLc FB P HA DA m o).
  #[local] Abbreviation ngn_final_C := (F_ngnextA.ngn_final_C K sp R CLc FB P HA DA m o).
  #[local] Abbreviation ngn_ret_m1 := (F_ngnextA.ngn_ret_m1 K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o BU).
  #[local] Abbreviation ngn_ret_0 := (F_ngnextA.ngn_ret_0 K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o BU).
  #[local] Abbreviation ngn_ret_1 := (F_ngnextA.ngn_ret_1 K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o BU).
  #[local] Abbreviation ngn_CLc_facts := (F_ngnextA.ngn_CLc_facts K R CLc FB).
  #[local] Abbreviation ngn_snp_call := (F_ngnextA.ngn_snp_call K HFL SFL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU SPM TP ALN R1 R2 AH AD SPW P1 P4 P5).
  #[local] Abbreviation ngn_snp := (F_ngnextA.ngn_snp K HFL SFL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU SPM TP ALN R1 R2 AH AD SPW P1 P4 P5).
  #[local] Abbreviation ngn_mcp := (F_ngnextA.ngn_mcp K HFL SFL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU ALN R1 R2 AH AD SPW P1 P4 P5 P6).
  #[local] Abbreviation PCAPRC_errbuf := (F_ngnextA.PCAPRC_errbuf K sp R lo P HA DA LO BU ALN R1 R2 AH AD SPW P1).

  Ltac norm_g :=
    unfold F_ngnextA.pv; unfold pcap_blocks; unfold psize; unfold is_ng;
    cbn [pc_self pc_rfile pc_bufsize pc_bufalloc pc_buffer pc_bufdata pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype
         pc_linktype_ext pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_priv priv_cells ng_of ng_ifaces_ptr_of
         set_bufdata set_errbuf set_buffer set_ng set_priv];
    unfold PCAP_NG_SF_TOTAL, PCAP_PRIV_OFF.
  Ltac norm_p :=
    unfold F_ngnextA.pv in *; unfold pcap_blocks in *; unfold psize in *; unfold is_ng in *;
    cbn [pc_self pc_rfile pc_bufsize pc_bufalloc pc_buffer pc_bufdata pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype
         pc_linktype_ext pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_priv priv_cells ng_of ng_ifaces_ptr_of
         set_bufdata set_errbuf set_buffer set_ng set_priv] in *;
    unfold PCAP_NG_SF_TOTAL, PCAP_PRIV_OFF in *.

  #[local] Abbreviation ngn_pp := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB.ngn_pp K HFL SFL PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPM R1 R2 R3 AH AD SPW SP47 P1 P2 P4 P5 P6 W1 W2 W5 W6 W7 W8 W9 W10).

  #[local] Abbreviation ngn_found := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.ngn_found K HFL SFL SNPRINTF PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPM TP ALN R1 R2 R3 AH AD SPW SP47 P1 P2 P4 P5 P6 W1 W2 W5 W6 W7 W8 W9 W10).
  #[local] Abbreviation ccells := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.ccells).
  #[local] Abbreviation ngn_spb := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.ngn_spb K HFL SFL SNPRINTF PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPM TP ALN R1 R2 R3 AH AD SPW SP47 P1 P2 P4 P5 P6 W1 W2 W5 W6 W7 W8 W9 W10).
  #[local] Abbreviation ngn_epb := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.ngn_epb K HFL SFL SNPRINTF PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPM TP ALN R1 R2 R3 AH AD SPW SP47 P1 P2 P4 P5 P6 W1 W2 W5 W6 W7 W8 W9 W10).
  #[local] Abbreviation ngn_pb := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.ngn_pb K HFL SFL SNPRINTF PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPM TP ALN R1 R2 R3 AH AD SPW SP47 P1 P2 P4 P5 P6 W1 W2 W5 W6 W7 W8 W9 W10).


  #[local] Abbreviation pcapT := (pcap hptr hptr).
  #[local] Abbreviation MR := (M (PState H hptr) ((Z + ng_found) * pcap hptr hptr)).

  #[local] Abbreviation ngn_KF := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_KF (H:=H) (hptr:=hptr)).
  #[local] Abbreviation ngn_shbK := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_shbK (H:=H) (hptr:=hptr)).
  #[local] Abbreviation ngn_idbK := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_idbK HO sites).
  #[local] Abbreviation ngn_head := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_head K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA Af m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header).
  #[local] Abbreviation ngn_too_short := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_too_short K HFL SFL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU SPM TP ALN R1 R2 AH AD SPW P1 P4 P5).
  #[local] Abbreviation PCAPR_bufdata := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.PCAPR_bufdata K sp R CLc FB lo P HA DA self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU ALN R1 R2 AH AD SPW P1 P5).
  #[local] Abbreviation get_le16_q8' := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.get_le16_q8').
  #[local] Abbreviation firstn2_q8 := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.firstn2_q8 sp R lo P HA DA LO BU R1 R2 SPW P1).
  #[local] Abbreviation bswap16_2 := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.bswap16_2 sp P HA DA).

  Ltac name_field data off a b c d DRNG :=
    set (a := q8 data off 0%Z) in *; set (b := q8 data off 1%Z) in *; set (c := q8 data off 2%Z) in *; set (d := q8 data off 3%Z) in *;
    let Ra := fresh "R" a in let Rb := fresh "R" b in let Rc := fresh "R" c in let Rd := fresh "R" d in
    pose proof (q8_range data off 0%Z DRNG ltac:(lia)) as Ra; pose proof (q8_range data off 1%Z DRNG ltac:(lia)) as Rb;
    pose proof (q8_range data off 2%Z DRNG ltac:(lia)) as Rc; pose proof (q8_range data off 3%Z DRNG ltac:(lia)) as Rd;
    fold a in Ra; fold b in Rb; fold c in Rc; fold d in Rd.

  #[local] Abbreviation ngn_snp90 := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextS.ngn_snp90 K HFL SFL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU SPM TP ALN R1 R2 AH AD SPW P1 P4 P5).
  #[local] Abbreviation ngn_snp8c := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextS.ngn_snp8c K HFL SFL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU SPM TP ALN R1 R2 AH AD SPW P1 P4 P5).

  (* [comment removed for export] *)
  Definition ngn_idb_swap__stmt : Prop := forall (ra' t0' t1' t2' x0 x1 a0' a2' a3' a4' a5' a6' a7' x3 x4 x5 x7 x8 x9 x10 x11 t3' t4' t5' t6' : word) (mx : mem)
           (l0 l1 n0 n1 n2 n3 : Z) (Bq : Z) (pre r2 : list byte) (rest : list cell),
      Forall (fun x => 0 <= x < 256)%Z [l0; l1; n0; n1; n2; n3] ->
      rw_cells ssegs mx Bq ([CB 8 pre; C2 (Z_to_bv 64 (l0 + 256 * l1)); CB 2 r2; C4 (Z_to_bv 64 (le4val n0 n1 n2 n3))] ++ rest) ->
      mem_inv ssegs mx -> (0 <= Bq)%Z -> (Bq + 16 <= 2^64)%Z ->
      evt ssegs (fun ms' => exists (a0v a1v a2v a3v : word) (m' : mem),
          ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' x0 x1 a0v a1v a2v a3v a4' a5' a6' a7'
                       (Z_to_bv 64 65280) x3 x4 x5 (Z_to_bv 64 (Bq + 8)) x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 0x1758c) fc None m' (seg_rom ssegs)
          /\ munch [(Bq + 8, Bq + 16)]%Z mx m' /\ wmono ssegs mx m' /\ mem_inv ssegs m'
          /\ rw_cells ssegs m' Bq ([CB 8 pre; C2 a1v; CB 2 r2; C4 a0v] ++ rest)
          /\ (bv_unsigned a1v = l1 + 256 * l0 + 65536 * l1)%Z /\ (bv_unsigned a0v mod 2^32 = le4val n3 n2 n1 n0)%Z)
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' x0 x1 a0' (Z_to_bv 64 (l0 + 256 * l1)) a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 65280) x3 x4 x5 (Z_to_bv 64 (Bq + 8)) x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 0x17550) fc None mx (seg_rom ssegs)).
  Section Sz6.
  Variables ra' t0' t1' t2' x0 x1 a0' a2' a3' a4' a5' a6' a7' x3 x4 x5 x7 x8 x9 x10 x11 t3' t4' t5' t6' mx l0 l1 n0 n1 n2 n3 Bq pre r2 rest : ltac2:(SecDiet.SzSec.tyM 'ngn_idb_swap__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma ngn_idb_swap__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_idb_swap__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using BU LO P1 R1 R2 SPW. pin_using (fun (BU LO P1 R1 R2 SPW : unit) => tt).
    intros GR HB MI B0 B64.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof GR as GR'. do 6 (apply Forall_cons_iff in GR'; destruct GR' as [? GR']). clear GR'.
    pose proof (munch_refl [(Bq + 8, Bq + 16)]%Z mx) as MU. pose proof (wmono_refl ssegs mx) as WM.
    step. rewrite (sx32_lit n0 n1 n2 n3) by lia.
    do 12 step.
    step. step.
    apply evt_done. cbv beta.
    lazymatch goal with HX : rw_cells ssegs ?mm Bq (CB 8 pre :: C2 ?w1 :: CB 2 r2 :: C4 ?w0 :: _) |- _ =>
      exists w0, w1; do 2 eexists; exists mm; split; [reflexivity|];
      split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [exact HX|] end.
    split; [apply (swap16_val _ l0 l1); [assumption | assumption | apply unsigned_lit; lia] |].
    apply swap32_sxv_mod32; assumption.
  Qed.
  End Sz6.
  Lemma ngn_idb_swap : ltac:(let t := eval cbv delta [ngn_idb_swap__stmt] in ngn_idb_swap__stmt in exact t).
  Proof using BU LO P1 R1 R2 SPW. intros ra' t0' t1' t2' x0 x1 a0' a2' a3' a4' a5' a6' a7' x3 x4 x5 x7 x8 x9 x10 x11 t3' t4' t5' t6' mx l0 l1 n0 n1 n2 n3 Bq pre r2 rest. ltac2:(SecDiet.SzSec.closeP 'ngn_idb_swap__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
  (* [comment removed for export] *)
  Definition ngn_idb_call__stmt : Prop := forall (LOOP : pcapT -> MR),
    ngn_head (fun p' ps' ms' => implM ssegs (mbind (LOOP p') ngn_KF) ps' POSTQ ms') ->
    forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x10 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (bq : hptr) (Bq Ix alloc rem : Z) (data eb : list Z) (sx : pcap_ng_sf) (ix : option hptr) (bt : Z) (hcs : list cell) (dw : cell) (dj : list byte) (cpad : list byte),
      stk ssegs m5 lo (bv_unsigned sp + -160) ->
      rw_cells ssegs m5 (bv_unsigned sp + -160) (ngn_frame dj [C8 (Z_to_bv 64 (Bq + 16)); C8 (Z_to_bv 64 (rem - 8)); C4 (Z_to_bv 64 bt); CB 4 cpad]) -> mem_inv ssegs m5 ->
      GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells ssegs m5 HA hcs -> cells_size hcs = 24%nat -> rw_cells ssegs m5 DA [dw] -> csize dw = 8%nat ->
      Forall (fun x => 0 <= x < 256)%Z data -> (Z.of_nat (length data) = rem + 12)%Z -> (rem + 12 <= 2^30)%Z -> (8 <= rem)%Z ->
      (0 <= bt < 2^32)%Z -> ps_outfile ps = o ->
      implM ssegs (mbind (mbind (add_interface MOps (prims HO fo_nop sites) (pv bq alloc data eb sx ix) 8 (mkCursor 16 (rem - 8) bt))
                          (fun r => let '(ok, c, p, msg) := r in if ok then LOOP p else mret (inl (-1)%Z, set_errbuf msg p))) ngn_KF) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 (P + 216)) a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 65280) (Z_to_bv 64 168627466) (Z_to_bv 64 P) (Z_to_bv 64 Af) (Z_to_bv 64 (Bq + 8)) (Z_to_bv 64 439041101) (Z_to_bv 64 2) (Z_to_bv 64 1) x10 (Z_to_bv 64 15)
                 t3' t4' t5' t6') F (Z_to_bv 64 0x175ac) fc None m5 (seg_rom ssegs)).
  Section Sz7.
  Variables LOOP ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x10 t3' t4' t5' t6' m5 ps bq Bq Ix alloc rem data eb sx ix bt hcs dw dj cpad : ltac2:(SecDiet.SzSec.tyM 'ngn_idb_call__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @LOOP).
  Lemma ngn_idb_call__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_idb_call__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using ADDIF ALN BU HPL LO P1 P4 R1 R2 SPM SPW TP. pin_using (fun (ADDIF ALN BU HPL LO P1 P4 R1 R2 SPM SPW TP : unit) => tt).
    intros HLOOP ST5 FR5 MI5 G5 PC5 AG5 HH Hh HD Hd DRNG LEN L30 REM Hbt OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof PC5 as (Afx & Hin & (Bx' & Ix' & jx' & padx & bsx' & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    pose proof G5 as G5e. rewrite EPB in G5e.
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G5e ltac:(right; left; reflexivity)) as (K1 & K2 & K3 & K4 & K5 & K6).
    pose proof (PB_apart K _ _ _ _ _ _ _ _ _ _ G5 eq_refl) as [APB API].
    pose proof WF as (W1' & W2' & W3 & W4 & W5' & W6' & W7' & W8' & W9' & W10' & W11 & W12 & W13 & W14).
    unfold F_ngnextA.pv, pcap_blocks, psize, is_ng in EPB, K1, K2, K3, K4, K5, K6, APB. cbn [pc_self pc_buffer pc_bufalloc pc_priv] in EPB, K1, K2, K3, K4, K5, K6, APB.
    unfold PCAP_NG_SF_TOTAL in APB.
    unfold F_ngnextA.pv in W3, W4, W13. cbn [pc_bufalloc pc_bufdata pc_priv] in W3, W4, W13.
    assert (EBX : Bx' = Bq) by congruence. subst Bx'.
    unfold F_ngnextA.pv in Hin. cbn [pc_rfile] in Hin.
    unfold F_ngnextA.pv in BUF. cbn [pc_bufalloc] in BUF. cbn [pc_bufdata] in PFX.
    pose proof PRIV as NG5. unfold priv_cells, F_ngnextA.pv, PCAP_PRIV_OFF in NG5. cbn [pc_priv] in NG5.
    assert (NPB : forall a, in_block CLc a -> (a < alloc_ceiling)%Z /\ ~ (P <= a < P + 680)%Z /\ ~ (Bq <= a < Bq + alloc)%Z).
    { intros a Ha. destruct (ngn_CLc_facts _ _ _ _ G5 Ha) as [Hc Hnb]. split; [clear - Hc; lia|]. split; intros Hr; apply Hnb; unfold pcap_blocks, in_block.
      - apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. unfold psize, is_ng, F_ngnextA.pv. cbn [pc_priv]. unfold PCAP_NG_SF_TOTAL. clear - Hr; lia.
      - apply Exists_cons_tl. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd pc_buffer pc_bufalloc F_ngnextA.pv]. clear - Hr; lia. }
    assert (INP : forall a, (P <= a < P + 680)%Z -> client_keeps ((CLc ++ [(self, P, PCAP_NG_SF_TOTAL); (bq, Bq, alloc)]) ++ []) (bv_unsigned sp + -160) a).
    { intros a Ha. right. rewrite app_nil_r. apply in_block_app. right. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. unfold PCAP_NG_SF_TOTAL. exact Ha. }
    (* [comment removed for export] *)
    apply pcap_cells_split4 in CELLS as (PRE & CE & HDR & OPS); [|reflexivity].
    apply (rw_cells_split_CB ssegs m5 _ [] 304 _ [] [256; 48]%nat) in CE; [|reflexivity]. cbn [mk_CB_cells app] in CE.
    destruct (rw_cells_cut _ _ _ 1 CE) as [CE1 CE2]. clear CE. cbn [firstn skipn cells_size csize Nat.add] in CE1, CE2.
    replace (P + 216 + Z.of_nat 256)%Z with (P + 472)%Z in CE2 by lia.
    unfold pc_pre in PRE. destruct (rw_cells_cut _ _ _ 7 PRE) as [PRE0 PRE7]. destruct (rw_cells_cut _ _ _ 2 PRE7) as [P48 PRE9]. clear PRE PRE7.
    cbn [firstn skipn cells_size csize Nat.add app] in PRE0, P48, PRE9.
    replace (P + Z.of_nat 48)%Z with (P + 48)%Z in P48 by lia. replace (P + Z.of_nat 48 + Z.of_nat 12)%Z with (P + 60)%Z in PRE9 by lia.
    (* [comment removed for export] *)
    pose proof FR5 as FRJ. unfold F_ngnextA.ngn_frame in FRJ. cbn [app] in FRJ.
    destruct (rw_cells_cut _ _ _ 4 FRJ) as [F0 F4]. destruct (rw_cells_cut _ _ _ 4 F4) as [FCUR FS]. clear FRJ F4.
    cbn [firstn skipn cells_size csize Nat.add app] in F0, FCUR, FS.
    replace (bv_unsigned sp + -160 + Z.of_nat 32)%Z with (bv_unsigned sp + -128)%Z in FCUR by lia.
    replace (bv_unsigned sp + -160 + Z.of_nat 32 + Z.of_nat 24)%Z with (bv_unsigned sp + -104)%Z in FS by lia.
    hide F0. hide FCUR. hide FS. hide PRE0. hide P48. hide PRE9. hide CE1. hide CE2. hide HDR. hide OPS. hide NG5. hide BUF. hide HH. hide HD. hide FR5. hide PRIV. hide IFS.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl ssegs m5) as WM.
    unfold implM. iprefix. step. step. step. step. step. clear MU WM.
    unhide F0. unhide FCUR. unhide FS. unhide PRE0. unhide P48. unhide PRE9. unhide CE1. unhide CE2. unhide HDR. unhide OPS. unhide NG5. unhide BUF. unhide HH. unhide HD. unhide FR5. unhide PRIV. unhide IFS.
    apply evt_done. apply (implM_bind_assoc ssegs). name_sp sp (-160)%Z. eapply (implM_bind ssegs).
    { eapply (ADDIF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 R ps (CLc ++ [(self, P, PCAP_NG_SF_TOTAL); (bq, Bq, alloc)]) [] FB P Bq Ix' (bv_unsigned sp + -128)%Z (P + 216)%Z lo 8%Z
                (pv bq alloc data eb sx ix) sx ix (mkCursor 16 (rem - 8) bt) bsx' (firstn 256 (pj_g jx')) padx cpad);
        [ split; [rewrite app_nil_r, <- app_assoc; cbn [app]; pose proof G5e as GX; unfold pcap_blocks, F_ngnextA.pv, psize, is_ng in GX; cbn [pc_self pc_buffer pc_bufalloc pc_priv] in GX; unfold IBLK; exact GX |];
          split; [rewrite Hsp; exact ST5|]; split; [unfold rc_lo; lia|]; split; [unfold ADD_INTERFACE_STACK, MALLOC_STACK; rewrite Hsp; lia|];
          split; [rewrite Hsp; unfold rc_spmain in *; lia|]; split; [exact MI5|]; split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]
        | reflexivity
        | rewrite app_nil_r; apply in_or_app; right; left; reflexivity
        | rewrite app_nil_r; apply in_or_app; right; right; left; reflexivity
        | unfold PCAP_NG_SF_TOTAL; cbn [pc_bufalloc F_ngnextA.pv]; exact APB
        | reflexivity | reflexivity | f_equal; lia | reflexivity
        | exact P48 | exact NG5 | exact IFS | clear - W13; lia | clear - W13; lia
        | exact BUF | exact PFX | cbn [pc_bufdata pc_bufalloc F_ngnextA.pv]; clear - W3 W4; lia | exact DRNG
        | exact FCUR | rewrite Hsp; lia | unfold rc_spmain in *; lia | replace (bv_unsigned sp + -128)%Z with (bv_unsigned sp + (-128))%Z by lia; apply aligned16_8; [exact ALN| reflexivity]
        | lia | reflexivity | cbn [cur_remaining]; lia | cbn [cur_off cur_remaining pc_bufdata F_ngnextA.pv]; lia | cbn [cur_block_type]; exact Hbt
        | exact CE1 | right; reflexivity ]. }
    intros [[[ok c5] p5] msg5] ps5 ms5 PO.
    destruct PO as (a0v & m6 & s' & i' & I' & pad' & bs' & E & OF6 & MI6 & ST6 & AG6 & EP & G6 & NG6 & U1 & U2 & U3 & U4 & BUF6 & PFX6 & LEN6 & GR6 & -> & RM).
    unfold hpost_regs in E. destruct_exs E. subst ms5. rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 0x175c0)) with (Z_to_bv 64 0x175c0) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    set (bd' := pc_bufdata p5) in *. clearbody bd'. subst p5.
    change (set_ng s' i' (set_bufdata bd' (pv bq alloc data eb sx ix))) with (pv bq alloc bd' eb s' i') in *.
    cbn [pc_bufdata pc_bufalloc F_ngnextA.pv] in LEN6. change (pc_bufalloc (pv bq alloc data eb sx ix)) with alloc in AG6, BUF6.
    unfold PCAP_PRIV_OFF, PCAP_NG_SF_TOTAL in AG6.
    assert (OF7 : ps_outfile ps5 = o) by (rewrite OF6; exact OF5).
    (* [comment removed for export] *)
    transport F0 m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [left; clear - Ha; lia| gio_ceil_fact; clear -CLO__ Ha LO BU SPW P4 K4 APB RSP; lia]).
    transport FS m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [left; clear - Ha; lia| gio_ceil_fact; clear -CLO__ Ha LO BU SPW P4 K4 APB RSP; lia]).
    transport HH m6 AG6 ltac:(intros a Ha; rewrite Hh in Ha; split; [left; clear - Ha R1; lia| gio_ceil_fact; clear -CLO__ Ha R1 LO BU SPW P4 K4; lia]).
    transport HD m6 AG6 ltac:(intros a Ha; cbn [cells_size] in Ha; rewrite Hd in Ha; split; [left; clear - Ha R1 R2; lia| gio_ceil_fact; clear -CLO__ Ha R1 R2 LO BU SPW P4 K4; lia]).
    transport PRE0 m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [apply INP; clear - Ha; lia| gio_ceil_fact; clear -CLO__ Ha LO BU SPW P4 APB K3; lia]).
    transport P48 m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [apply INP; clear - Ha; lia| gio_ceil_fact; clear -CLO__ Ha LO BU SPW P4 APB K3; lia]).
    transport PRE9 m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [apply INP; clear - Ha; lia| gio_ceil_fact; clear -CLO__ Ha LO BU SPW P4 APB K3; lia]).
    transport CE2 m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [apply INP; clear - Ha; lia| gio_ceil_fact; clear -CLO__ Ha LO BU SPW P4 APB K3; lia]).
    transport HDR m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add hdr_cells pc_header F_ngnextA.pv] in Ha; split; [apply INP; clear - Ha; lia| gio_ceil_fact; clear -CLO__ Ha LO BU SPW P4 APB K3; lia]).
    transport OPS m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add pc_ops] in Ha; split; [apply INP; clear - Ha; lia| gio_ceil_fact; clear -CLO__ Ha LO BU SPW P4 APB K3; lia]).
    pose proof (rw_cells_uncut _ _ _ _ _ PRE0 P48 ltac:(cbn; lia)) as PRE'. pose proof (rw_cells_uncut _ _ _ _ _ PRE' PRE9 ltac:(cbn; lia)) as PRE. clear PRE' PRE0 P48 PRE9.
    cbn [app] in PRE.
    assert (AG7 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m6).
    { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [exact AG6|]. intros a [[Ha|Ha] _].
      - split; [left; clear - Ha; lia| gio_ceil_fact; clear -CLO__ Ha LO BU SPW P4 K4; lia].
      - destruct (NPB a Ha) as (Hc & Hn1 & Hn2). split; [right; rewrite app_nil_r; apply in_block_app; left; exact Ha| gio_ceil_fact; clear -CLO__ Hc Hn1 Hn2 LO BU SPW; lia]. }
    assert (PBE : pcap_blocks (pv bq alloc bd' eb s' i') P Bq I' = [(self, P, PCAP_NG_SF_TOTAL); (bq, Bq, alloc)] ++ IBLK i' I' s').
    { unfold pcap_blocks, IBLK, F_ngnextA.pv, psize, is_ng. cbn [pc_self pc_buffer pc_bufalloc pc_priv app]. destruct i'; reflexivity. }
    assert (G6' : GIo K R ps5 (CLc ++ pcap_blocks (pv bq alloc bd' eb s' i') P Bq I') FB m6).
    { eapply (GIo_perm K HPL); [exact G6|]. rewrite PBE, app_nil_r, (app_assoc CLc). apply Permutation.Permutation_app_comm. }
    assert (WF' : pcap_wf (pv bq alloc bd' eb s' i')).
    { unfold pcap_wf, F_ngnextA.pv in WF |- *.
      cbn [pc_snapshot pc_bufsize pc_bufalloc pc_bufdata pc_break_loop pc_tstamp_precision pc_version_major pc_version_minor pc_linktype pc_linktype_ext pc_header pc_priv] in WF |- *.
      rewrite LEN6, U1, U2. clear - WF U3 U4. lia. }
    (* [comment removed for export] *)
    assert (JOIN : forall cs, rw_cells ssegs m6 (P + 216) cs -> cells_size cs = 304%nat ->
              rw_cells ssegs m6 P (pcap_cells_gen (pv bq alloc bd' eb s' i') P Bq (C8 (Z_to_bv 64 Afx)) (C8 (Z_to_bv 64 (pk_stats PK))) (C8 (Z_to_bv 64 (pk_oneshot PK))) (set_pj_g (cells_bytes cs) jx'))).
    { intros cs HCS Hcs.
      exact (pcap_cells_join4 _ P (pv bq alloc bd' eb s' i') Bq (C8 (Z_to_bv 64 Afx)) (C8 (Z_to_bv 64 (pk_stats PK))) (C8 (Z_to_bv 64 (pk_oneshot PK))) jx' cs header eq_refl PRE HCS Hcs HDR OPS). }
    cbv beta. unfold implM. iprefix.
    destruct ok; cbn [Z.b2z].
    - (* [comment removed for export] *)
      destruct RM as (HIF6 & (cpad' & HCUR6) & CR1' & CR2' & CR3' & CBT' & HEB6 & ->).
      pose proof (rw_cells_uncut _ _ _ _ _ HEB6 CE2 ltac:(cbn; lia)) as CE6.
      pose proof (JOIN _ CE6 eq_refl) as CELLS6.
      pose proof (rw_cells_uncut _ _ _ _ _ HCUR6 FS ltac:(cbn; lia)) as F46. pose proof (rw_cells_uncut _ _ _ _ _ F0 F46 ltac:(cbn; lia)) as FR6. clear F46.
      assert (PC6 : PCAPR (hptr:=hptr) P (pv bq alloc bd' eb s' i') (pcap_blocks (pv bq alloc bd' eb s' i') P Bq I') FB m6).
      { exists Afx. split; [exact Hin|]. eexists Bq, I', _, pad', bs'.
        split; [reflexivity|]. split; [exact CELLS6|]. split; [exact NG6|]. split; [exact BUF6|]. split; [exact PFX6|]. split; [exact HIF6| exact WF']. }
      hide FR6. hide CELLS6. hide NG6. hide BUF6. hide HH. hide HD. hide HCUR6. hide F0. hide FS. hide CE6. hide HEB6. hide CE2. hide HDR. hide OPS. hide PRE.
      pose proof (munch_refl ([] : list (Z * Z)) m6) as MU. pose proof (wmono_refl ssegs m6) as WM.
      step. if_cases BRK; zify_cond BRK; [| exfalso; rewrite ?unsigned_lit in BRK by lia; clear - BRK; lia].
      unhide FR6. unhide CELLS6. unhide NG6. unhide BUF6. unhide HH. unhide HD.
      apply evt_done.
      unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_head in HLOOP. unfold NGN_LOOP in HLOOP.
      eapply HLOOP; [exact ST6 | exact FR6 | reflexivity | exact MI6 | exact G6' | exact PC6 | exact AG7 | exact HH | exact Hh | exact HD | exact Hd | exact OF7].
    - (* [comment removed for export] *)
      destruct RM as (CLOS & (ccs' & HCUR6 & Hccs') & (junk6 & HEB6) & LENM & MOK).
      pose proof (rw_cells_uncut _ _ _ _ _ HEB6 CE2 ltac:(cbn [cells_size csize]; clear - LENM; lia)) as CE6. cbn [app] in CE6.
      pose proof (JOIN _ CE6 ltac:(cbn [cells_size csize]; clear - LENM; lia)) as CELLS6.
      pose proof (rw_cells_uncut _ _ _ _ _ HCUR6 FS ltac:(rewrite Hccs'; cbn; lia)) as F46. pose proof (rw_cells_uncut _ _ _ _ _ F0 F46 ltac:(cbn; lia)) as FR6. clear F46.
      assert (PC6 : PCAPR_closable (hptr:=hptr) P (set_errbuf msg5 (pv bq alloc bd' eb s' i')) (pcap_blocks (pv bq alloc bd' eb s' i') P Bq I') FB m6).
      { exists Afx. split; [exact Hin|]. eexists Bq, I', _, pad', bs'.
        split; [reflexivity|]. split; [exact CELLS6|]. split; [exact NG6|]. split; [exact BUF6|]. split; [exact PFX6|]. split; [| exact WF'].
        unfold ifaces_closable, F_ngnextA.pv. cbn [pc_priv set_errbuf]. unfold ng_ifaces_closable in CLOS. destruct i'; exact CLOS. }
      hide FR6. hide CELLS6. hide NG6. hide BUF6. hide HH. hide HD. hide HCUR6. hide F0. hide FS. hide CE6. hide HEB6. hide CE2. hide HDR. hide OPS. hide PRE.
      pose proof (munch_refl ([] : list (Z * Z)) m6) as MU. pose proof (wmono_refl ssegs m6) as WM.
      step. if_cases BRK; zify_cond BRK; [exfalso; rewrite ?unsigned_lit in BRK by lia; clear - BRK; lia|].
      step.
      unhide FR6. unhide CELLS6. unhide NG6. unhide BUF6. unhide HH. unhide HD.
      apply evt_done. apply implM_retb. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_KF. unfold NGN_EPILOGUE.
      eapply (ngn_ret_m1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6 ps5 (pcap_blocks (pv bq alloc bd' eb s' i') P Bq I'));
        [exact ST6 | exact FR6 | exact Hccs' | exact MI6 |].
      split; [exact G6'|]. split; [exact PC6|]. split; [exact AG7|]. split; [exact HH|]. split; [exact Hh|]. split; [exact HD|]. split; [exact Hd| exact OF7].
  Qed.
  End Sz7.
  Lemma ngn_idb_call : ltac:(let t := eval cbv delta [ngn_idb_call__stmt] in ngn_idb_call__stmt in exact t).
  Proof using ADDIF ALN BU HPL LO P1 P4 R1 R2 SPM SPW TP. intros LOOP HLOOP ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x10 t3' t4' t5' t6' m5 ps bq Bq Ix alloc rem data eb sx ix bt hcs dw dj cpad. ltac2:(SecDiet.SzSec.closeP 'ngn_idb_call__body "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
  (* [comment removed for export] *)
  Definition ngn_idb_tail__stmt : Prop := forall (LOOP : pcapT -> MR),
    ngn_head (fun p' ps' ms' => implM ssegs (mbind (LOOP p') ngn_KF) ps' POSTQ ms') ->
    forall (ra' t0' t1' t2' a0' a2' a3' a4' a5' a6' a7' x10 t3' t4' t5' t6' ltw : word) (m5 : mem) (ps : PState H hptr)
           (bq : hptr) (Bq Ix alloc rem : Z) (data eb : list Z) (sx : pcap_ng_sf) (ix : option hptr) (bt : Z) (hcs : list cell) (dw : cell) (dj : list byte) (cpad : list byte),
      stk ssegs m5 lo (bv_unsigned sp + -160) ->
      rw_cells ssegs m5 (bv_unsigned sp + -160) (ngn_frame dj [C8 (Z_to_bv 64 (Bq + 16)); C8 (Z_to_bv 64 (rem - 8)); C4 (Z_to_bv 64 bt); CB 4 cpad]) -> mem_inv ssegs m5 ->
      GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells ssegs m5 HA hcs -> cells_size hcs = 24%nat -> rw_cells ssegs m5 DA [dw] -> csize dw = 8%nat ->
      Forall (fun x => 0 <= x < 256)%Z data -> (Z.of_nat (length data) = rem + 12)%Z -> (rem + 12 <= 2^30)%Z -> (8 <= rem)%Z ->
      (0 <= bt < 2^32)%Z -> ps_outfile ps = o -> (bv_unsigned ltw mod 2^16 = get_le16 data 8)%Z ->
      implM ssegs (mbind (let lt := get_le16 data 8 in
                          let sl := get_le32 data 12 in
                          if negb (linktype =? lt) then mret (inl (-1)%Z, set_errbuf (Msg.iface_type_differs lt) (pv bq alloc data eb sx ix))
                          else if negb (snapshot =? pcapint_adjust_snapshot linktype sl) then mret (inl (-1)%Z, set_errbuf (Msg.iface_snaplen_differs sl) (pv bq alloc data eb sx ix))
                          else mbind (add_interface MOps (prims HO fo_nop sites) (pv bq alloc data eb sx ix) 8 (mkCursor 16 (rem - 8) bt))
                                     (fun r => let '(ok, c, p, msg) := r in if ok then LOOP p else mret (inl (-1)%Z, set_errbuf msg p))) ngn_KF) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 (P + 216)) a0' ltw a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 65280) (Z_to_bv 64 168627466) (Z_to_bv 64 P) (Z_to_bv 64 Af) (Z_to_bv 64 (Bq + 8)) (Z_to_bv 64 439041101) (Z_to_bv 64 2) (Z_to_bv 64 1) x10 (Z_to_bv 64 15)
                 t3' t4' t5' t6') F (Z_to_bv 64 0x1758c) fc None m5 (seg_rom ssegs)).
  Section Sz8.
  Variables LOOP ra' t0' t1' t2' a0' a2' a3' a4' a5' a6' a7' x10 t3' t4' t5' t6' ltw m5 ps bq Bq Ix alloc rem data eb sx ix bt hcs dw dj cpad : ltac2:(SecDiet.SzSec.tyM 'ngn_idb_tail__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @LOOP).
  Lemma ngn_idb_tail__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_idb_tail__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AD ADDIF ADJ AH ALN BU HFL HPL LO P1 P2 P4 P5 P6 R1 R2 SFL SNPRINTF SPM SPW TP W1 W9. pin_using (fun (AD ADDIF ADJ AH ALN BU HFL HPL LO P1 P2 P4 P5 P6 R1 R2 SFL SNPRINTF SPM SPW TP W1 W9 : unit) => tt).
    intros HLOOP ST5 FR5 MI5 G5 PC5 AG5 HH Hh HD Hd DRNG LEN L30 REM Hbt OF5 Hlt.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof PC5 as (Afx & Hin & (Bx' & Ix' & jx' & padx & bsx' & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    pose proof G5 as G5e. rewrite EPB in G5e.
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G5e ltac:(right; left; reflexivity)) as (K1 & K2 & K3 & K4 & K5 & K6).
    pose proof WF as (W1' & _ & W3 & W4 & _).
    unfold F_ngnextA.pv, pcap_blocks, psize, is_ng in EPB, K1, K2, K3, K4, K5, K6. cbn [pc_self pc_buffer pc_bufalloc pc_priv] in EPB, K1, K2, K3, K4, K5, K6.
    unfold F_ngnextA.pv in W3, W4, W1'. cbn [pc_bufalloc pc_bufdata pc_snapshot] in W3, W4, W1'. unfold INT_MAX in W1'.
    assert (EBX : Bx' = Bq) by congruence. subst Bx'.
    unfold pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF, F_ngnextA.pv in CELLS.
    cbn [app pc_bufsize pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_header pc_priv pk_next_ng pk_cleanup_ng PK] in CELLS.
    unfold F_ngnextA.pv in BUF. cbn [pc_bufalloc] in BUF. cbn [pc_bufdata] in PFX.
    (* [comment removed for export] *)
    cbv zeta. rewrite (get_le16_q8' data 8) in Hlt |- * by lia. rewrite (get_le32_q8 data 12) by lia.
    set (l0 := q8 data 8 0) in *. set (l1 := q8 data 8 1) in *.
    pose proof (q8_range data 8 0 DRNG ltac:(lia)) as Rl0. pose proof (q8_range data 8 1 DRNG ltac:(lia)) as Rl1. fold l0 in Rl0. fold l1 in Rl1.
    name_field data 12%Z n0 n1 n2 n3 DRNG.
    assert (LBS : length bsx' = Z.to_nat alloc) by (destruct BUF as [[WFB _] _]; cbn in WFB; lia).
    apply (rw_cells_split_CB ssegs m5 _ [] (Z.to_nat alloc) _ [] [8; 2; 2; 4; Z.to_nat alloc - 16]%nat) in BUF; [| cbn; lia]. cbn [mk_CB_cells app] in BUF.
    rewrite !skipn_skipn in BUF. cbn [Nat.add] in BUF.
    rewrite (firstn4_q8 data bsx' 12 12 PFX eq_refl) in BUF by lia. fold n0 n1 n2 n3 in BUF.
    assert (BUF4 : rw_cells ssegs m5 Bq [CB 8 (firstn 8 bsx'); CB 2 (firstn 2 (skipn 8 bsx')); CB 2 (firstn 2 (skipn 10 bsx')); C4 (Z_to_bv 64 (le4val n0 n1 n2 n3)); CB (Z.to_nat alloc - 16) (firstn (Z.to_nat alloc - 16) (skipn 16 bsx'))]).
    { eapply rw_cells_recell; [exact BUF | | ].
      { cbn. rewrite ?length_firstn, ?length_skipn. repeat split; try exact Logic.I; lia. }
      cbn [cells_bytes cbytes app]. rewrite (le4_lit n0 n1 n2 n3) by lia. reflexivity. }
    clear BUF.
    pose proof FR5 as FRJ. unfold F_ngnextA.ngn_frame in FRJ. cbn [app] in FRJ.
    pose proof (adjust_snapshot_range linktype (le4val n0 n1 n2 n3) ltac:(unfold le4val; lia)) as ADR. unfold INT_MAX in ADR.
    hide FR5. hide PRIV. hide IFS. hide HH. hide HD.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl ssegs m5) as WM.
    unfold implM. iprefix.
    step. rewrite (sx32_small linktype) by lia.
    step. step. rewrite (zext16_shifts ltw), Hlt.
    step. if_cases BR; zify_cond BR; rewrite ?unsigned_lit in BR by lia.
    - (* [comment removed for export] *)
      replace (linktype =? l0 + 256 * l1) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb]. cbv iota.
      step. step. step.
      unhide FR5. unhide PRIV. unhide IFS. unhide HH. unhide HD.
      assert (MSG : fmt_at m5 NGN_FMT_IFTYPE "an interface has a type %u different from the type of the first interface"%string)
        by (apply fmt_at_intro; [exact MI5 | vm_compute; reflexivity | unfold NGN_FMT_IFTYPE; lia | unfold NGN_FMT_IFTYPE; cbn; lia]).
      unfold NGN_FMT_IFTYPE in MSG.
      apply evt_done. apply implM_retb. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_KF.
      eapply ngn_snp8c with (args := [AInt (l0 + 256 * l1)%Z]);
        [exact ST5 | exact FR5 | reflexivity | exact MI5 | | exact MSG | reflexivity | cbn; lia | cbn; apply Forall2_cons; [reflexivity| apply Forall2_nil]].
      split; [exact G5|]. split; [apply PCAPR_closable_of; exact PC5|]. split; [exact AG5|]. split; [exact HH|]. split; [exact Hh|].
      split; [exact HD|]. split; [exact Hd| exact OF5].
    - (* [comment removed for export] *)
      replace (linktype =? l0 + 256 * l1) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb]. cbv iota.
      step. rewrite (sx32_small snapshot) by lia.
      step. rewrite (sx32_s32 (le4val n0 n1 n2 n3)) by (unfold le4val; lia).
      step.
      eapply evt_cut.
      { eapply (ADJ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m5 linktype (le4val n0 n1 n2 n3)); [reflexivity | lia | reflexivity | unfold le4val; lia]. }
      cbv beta. intros ms' (y0 & y1 & y2 & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & -> & ->).
      replace (ret_pc (Z_to_bv 64 0x175a8)) with (Z_to_bv 64 0x175a8) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      step. if_cases BR2; zify_cond BR2; rewrite ?unsigned_lit in BR2 by lia.
      + (* [comment removed for export] *)
        replace (snapshot =? pcapint_adjust_snapshot linktype (le4val n0 n1 n2 n3)) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb]. cbv iota.
        step. rewrite (sx32_lit n0 n1 n2 n3) by lia. step. step. step.
        unhide FR5. unhide PRIV. unhide IFS. unhide HH. unhide HD.
        assert (MSG : fmt_at m5 NGN_FMT_IFSNAP "an interface has a snapshot length %u different from the snapshot length of the first interface"%string)
          by (apply fmt_at_intro; [exact MI5 | vm_compute; reflexivity | unfold NGN_FMT_IFSNAP; lia | unfold NGN_FMT_IFSNAP; cbn; lia]).
        unfold NGN_FMT_IFSNAP in MSG.
        apply evt_done. apply implM_retb. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_KF.
        eapply ngn_snp8c with (args := [AInt (sxv n0 n1 n2 n3)]);
          [exact ST5 | exact FR5 | reflexivity | exact MI5 | | exact MSG | reflexivity | cbn; lia | cbn; apply Forall2_cons; [reflexivity| apply Forall2_nil]].
        split; [exact G5|]. split; [apply PCAPR_closable_of; exact PC5|]. split; [exact AG5|]. split; [exact HH|]. split; [exact Hh|].
        split; [exact HD|]. split; [exact Hd| exact OF5].
      + (* [comment removed for export] *)
        replace (snapshot =? pcapint_adjust_snapshot linktype (le4val n0 n1 n2 n3)) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb]. cbv iota.
        unhide FR5. unhide PRIV. unhide IFS. unhide HH. unhide HD.
        apply evt_done.
        eapply (ngn_idb_call LOOP HLOOP); [exact ST5 | exact FR5 | exact MI5 | exact G5 | exact PC5 | exact AG5 | exact HH | exact Hh | exact HD | exact Hd | exact DRNG | exact LEN | exact L30 | exact REM | exact Hbt | exact OF5].
  Qed.
  End Sz8.
  Lemma ngn_idb_tail : ltac:(let t := eval cbv delta [ngn_idb_tail__stmt] in ngn_idb_tail__stmt in exact t).
  Proof using AD ADDIF ADJ AH ALN BU HFL HPL LO P1 P2 P4 P5 P6 R1 R2 SFL SNPRINTF SPM SPW TP W1 W9. intros LOOP HLOOP ra' t0' t1' t2' a0' a2' a3' a4' a5' a6' a7' x10 t3' t4' t5' t6' ltw m5 ps bq Bq Ix alloc rem data eb sx ix bt hcs dw dj cpad. ltac2:(SecDiet.SzSec.closeP 'ngn_idb_tail__body "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
  (* [comment removed for export] *)
  Definition ngn_idb__stmt : Prop := forall (LOOP : pcapT -> MR),
    ngn_head (fun p' ps' ms' => implM ssegs (mbind (LOOP p') ngn_KF) ps' POSTQ ms') ->
    forall (ra' t0' t1' t2' a0' a1' a2' a4' a5' a6' a7' x6 x10 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (bq : hptr) (Bq Ix alloc rem : Z) (data eb : list Z) (sx : pcap_ng_sf) (ix : option hptr) (bt : Z) (hcs : list cell) (dw : cell) (dj : list byte) (cpad : list byte),
      stk ssegs m5 lo (bv_unsigned sp + -160) ->
      rw_cells ssegs m5 (bv_unsigned sp + -160) (ngn_frame dj (ccells Bq rem bt cpad)) -> mem_inv ssegs m5 ->
      GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells ssegs m5 HA hcs -> cells_size hcs = 24%nat -> rw_cells ssegs m5 DA [dw] -> csize dw = 8%nat ->
      Forall (fun x => 0 <= x < 256)%Z data -> (Z.of_nat (length data) = rem + 12)%Z -> (rem + 12 <= 2^30)%Z -> (0 <= rem)%Z ->
      (0 <= bt < 2^32)%Z -> ps_outfile ps = o ->
      implM ssegs (mbind (ngn_idbK LOOP (mkCursor 8 rem bt) (pv bq alloc data eb sx ix)) ngn_KF) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 (P + 216))
                 a0' a1' a2' (Z_to_bv 64 (s32 bt)) a4' a5' a6' a7'
                 (Z_to_bv 64 65280) (Z_to_bv 64 168627466) (Z_to_bv 64 P) (Z_to_bv 64 Af) x6 (Z_to_bv 64 439041101) (Z_to_bv 64 2) (Z_to_bv 64 1) x10 (Z_to_bv 64 15)
                 t3' t4' t5' t6') F (Z_to_bv 64 0x17520) fc None m5 (seg_rom ssegs)).
  Section Sz9.
  Variables LOOP ra' t0' t1' t2' a0' a1' a2' a4' a5' a6' a7' x6 x10 t3' t4' t5' t6' m5 ps bq Bq Ix alloc rem data eb sx ix bt hcs dw dj cpad : ltac2:(SecDiet.SzSec.tyM 'ngn_idb__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @LOOP).
  Lemma ngn_idb__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_idb__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AD ADDIF ADJ AH ALN BU HFL HPL LO P1 P2 P4 P5 P6 R1 R2 SFL SNPRINTF SPM SPW TP W1 W9. pin_using (fun (AD ADDIF ADJ AH ALN BU HFL HPL LO P1 P2 P4 P5 P6 R1 R2 SFL SNPRINTF SPM SPW TP W1 W9 : unit) => tt).
    intros HLOOP ST5 FR5 MI5 G5 PC5 AG5 HH Hh HD Hd DRNG LEN L30 REM Hbt OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_idbK, get_from_block_data. cbn [cur_remaining cur_off cur_block_type].
    change (pc_swapped (pv bq alloc data eb sx ix)) with swapped. change (pc_bufdata (pv bq alloc data eb sx ix)) with data.
    change (pc_linktype (pv bq alloc data eb sx ix)) with linktype. change (pc_snapshot (pv bq alloc data eb sx ix)) with snapshot.
    pose proof FR5 as FRJ. unfold F_ngnextA.ngn_frame, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.ccells in FRJ. cbn [app] in FRJ.
    hide FR5. hide HH. hide HD.
    pose proof (munch_refl [(bv_unsigned sp + -160 + 32, bv_unsigned sp + -160 + 48)]%Z m5) as MU. pose proof (wmono_refl ssegs m5) as WM.
    unfold implM. iprefix. step. step.
    step. if_cases BR0; zify_cond BR0; rewrite ?unsigned_lit in BR0 by lia.
    - (* [comment removed for export] *)
      replace (rem <? 8) with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
      step. step. step. step. step.
      unhide FR5. unhide HH. unhide HD. apply evt_done. apply implM_retb. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_KF.
      eapply (ngn_too_short _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 ps (pv bq alloc data eb sx ix) _ 1);
        [exact ST5 | exact FR5 | reflexivity | exact MI5 |].
      split; [exact G5|]. split; [apply PCAPR_closable_of; exact PC5|]. split; [exact AG5|]. split; [exact HH|]. split; [exact Hh|].
      split; [exact HD|]. split; [exact Hd| exact OF5].
    - (* [comment removed for export] *)
      replace (rem <? 8) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota. cbv beta. change (8 + 8)%Z with 16%Z. change (8 + 4)%Z with 12%Z.
      pose proof PC5 as (Afx & Hin & (Bx' & Ix' & jx' & padx & bsx' & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
      pose proof G5 as G5e. rewrite EPB in G5e.
      pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G5e ltac:(right; left; reflexivity)) as (K1 & K2 & K3 & K4 & K5 & K6).
      pose proof (PB_apart K _ _ _ _ _ _ _ _ _ _ G5 eq_refl) as [APB API].
      pose proof WF as (W1' & _ & W3 & W4 & _).
      unfold F_ngnextA.pv, pcap_blocks, psize, is_ng in EPB, K1, K2, K3, K4, K5, K6, APB. cbn [pc_self pc_buffer pc_bufalloc pc_priv] in EPB, K1, K2, K3, K4, K5, K6, APB.
      unfold PCAP_NG_SF_TOTAL in APB.
      unfold F_ngnextA.pv in W3, W4, W1'. cbn [pc_bufalloc pc_bufdata pc_snapshot] in W3, W4, W1'. unfold INT_MAX in W1'.
      assert (EBX : Bx' = Bq) by congruence. subst Bx'.
      unfold pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF, F_ngnextA.pv in CELLS.
      cbn [app pc_bufsize pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_header pc_priv pk_next_ng pk_cleanup_ng PK] in CELLS.
      unfold F_ngnextA.pv in BUF. cbn [pc_bufalloc] in BUF. cbn [pc_bufdata] in PFX.
      (* [comment removed for export] *)
      set (l0 := q8 data 8 0) in *. set (l1 := q8 data 8 1) in *. set (r0 := q8 data 10 0) in *. set (r1 := q8 data 10 1) in *.
      pose proof (q8_range data 8 0 DRNG ltac:(lia)) as Rl0. pose proof (q8_range data 8 1 DRNG ltac:(lia)) as Rl1.
      pose proof (q8_range data 10 0 DRNG ltac:(lia)) as Rr0. pose proof (q8_range data 10 1 DRNG ltac:(lia)) as Rr1.
      fold l0 in Rl0. fold l1 in Rl1. fold r0 in Rr0. fold r1 in Rr1.
      name_field data 12%Z n0 n1 n2 n3 DRNG.
      assert (LBS : length bsx' = Z.to_nat alloc) by (destruct BUF as [[WFB _] _]; cbn in WFB; lia).
      apply (rw_cells_split_CB ssegs m5 _ [] (Z.to_nat alloc) _ [] [8; 2; 2; 4; Z.to_nat alloc - 16]%nat) in BUF; [| cbn; lia]. cbn [mk_CB_cells app] in BUF.
      rewrite !skipn_skipn in BUF. cbn [Nat.add] in BUF.
      rewrite (firstn2_q8 data bsx' 8 8 PFX eq_refl), (firstn2_q8 data bsx' 10 10 PFX eq_refl), (firstn4_q8 data bsx' 12 12 PFX eq_refl) in BUF by lia.
      fold l0 l1 r0 r1 n0 n1 n2 n3 in BUF.
      replace (firstn (Z.to_nat alloc - 16) (skipn 16 bsx')) with (skipn 16 bsx') in BUF by (symmetry; apply firstn_all2; rewrite length_skipn; lia).
      assert (BUF4 : rw_cells ssegs m5 Bq [CB 8 (firstn 8 bsx'); C2 (Z_to_bv 64 (l0 + 256 * l1)); CB 2 [b8 r0; b8 r1]; C4 (Z_to_bv 64 (le4val n0 n1 n2 n3)); CB (Z.to_nat alloc - 16) (skipn 16 bsx')]).
      { eapply rw_cells_recell; [exact BUF | | ].
        { cbn. rewrite ?length_firstn, ?length_skipn. repeat split; try exact Logic.I; lia. }
        cbn [cells_bytes cbytes app]. rewrite (le2_lit l0 l1), (le4_lit n0 n1 n2 n3) by lia. reflexivity. }
      clear BUF.
      hide PRIV. hide IFS.
      (* [comment removed for export] *)
      step. step. step. step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (AGF : agrees_on (fun a => outside [(bv_unsigned sp + -160 + 32, bv_unsigned sp + -160 + 48)]%Z a) m5 mm) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]);
        rename mm into m6 end.
      unhide FR5. unhide HH. unhide HD. unhide PRIV. unhide IFS. clear FR5.
      apply (agrees_rw_cells _ _ _ _ _ AGF) in HH; [| intros a Ha; rewrite Hh in Ha; cbn [outside]; clear - Ha R1; lia].
      apply (agrees_rw_cells _ _ _ _ _ AGF) in HD; [| intros a Ha; cbn [cells_size] in Ha; rewrite Hd in Ha; cbn [outside]; clear - Ha R1 R2; lia].
      apply (agrees_rw_cells _ _ _ _ _ AGF) in PRIV; [| intros a Ha; pose proof (priv_cells_psize _ _ _ _ _ PRIV) as PZ; unfold psize, is_ng, F_ngnextA.pv, PCAP_PRIV_OFF, priv_cells in PZ, Ha; cbn [pc_priv] in PZ, Ha; unfold PCAP_NG_SF_TOTAL in PZ; cbn [outside]; gio_ceil_fact; clear -CLO__ Ha PZ LO BU SPW P4; lia].
      assert (G6 : GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m6).
      { eapply (GIo_pcap_frame K HFL SFL); [exact G5 | exact MU | exact WM |]. apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd]. unfold rc_lo, rc_spmain in *. clear - LO BU SPM; lia. }
      assert (PC6 : PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m6).
      { eapply PCAPR_agree; [exact AGF | | exact PC5]. intros a Ha. pose proof (in_PB_below K _ _ _ _ _ _ _ G5 Ha). cbn [outside]. gio_ceil_fact; clear -CLO__ H0 LO BU SPW; lia. }
      assert (IFS6 : ifaces_ok (pv bq alloc data eb sx ix) Ix' m6).
      { eapply ifaces_ok_agree; [exact AGF | | exact IFS]. intros sg q Hq a Ha. unfold F_ngnextA.pv in Hq. cbn [pc_priv] in Hq. injection Hq as E1 E2. subst sg ix.
        destruct (API sx q eq_refl) as [X1 X2].
        pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G5e ltac:(right; right; left; reflexivity)) as (I1 & I2 & I3 & I4 & I5 & I6).
        cbn [outside]. gio_ceil_fact; clear -CLO__ Ha I1 I4 LO BU SPW. lia. }
      assert (AG6 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m6).
      { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [exact AGF|]. intros a [[Ha|Ha] _]; cbn [outside]; [clear - Ha; lia|].
        destruct (ngn_CLc_facts _ _ _ _ G5 Ha) as [Hc Hnb]. gio_ceil_fact; clear -CLO__ Hc LO BU SPW. lia. }
      clear MU WM AGF G5 PC5 AG5 IFS G5e.
      step. if_cases BRZ; zify_cond BRZ. { exfalso. rewrite ?unsigned_lit in BRZ by lia. clear -BRZ K1 K3 K4. lia. }
      step. rewrite (sx32_small (Z.b2z swapped)) by (destruct swapped; cbn; lia).
      step. rewrite (zx16_lit (l0 + 256 * l1)) by lia.
      (* [comment removed for export] *)
      lazymatch goal with FRX : rw_cells ssegs m6 (bv_unsigned sp + -160) (_ :: _ :: _ :: _ :: C8 (Z_to_bv 64 ?v1) :: C8 (Z_to_bv 64 ?v2) :: _) |- _ =>
        replace (Z_to_bv 64 v1) with (Z_to_bv 64 (Bq + 16)) in FRX by (f_equal; lia);
        replace (Z_to_bv 64 v2) with (Z_to_bv 64 (rem - 8)) in FRX by (f_equal; lia);
        assert (FR6 : rw_cells ssegs m6 (bv_unsigned sp + -160) (F_ngnextA.ngn_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 P HA DA dj [C8 (Z_to_bv 64 (Bq + 16)); C8 (Z_to_bv 64 (rem - 8)); C4 (Z_to_bv 64 bt); CB 4 cpad])) by exact FRX end.
      step. if_cases BRS; zify_cond BRS.
      + (* [comment removed for export] *)
        assert (SW : swapped = false) by (destruct swapped; [| reflexivity]; exfalso; revert BRS; rewrite ?unsigned_lit by (cbn; lia); cbn; lia).
        lazymatch goal with |- context [if swapped then ?X else ?Y] => replace (if swapped then X else Y) with Y by (rewrite SW; reflexivity) end.
        cbv zeta. change (pc_bufdata (pv bq alloc data eb sx ix)) with data.
        change (pc_linktype (pv bq alloc data eb sx ix)) with linktype. change (pc_snapshot (pv bq alloc data eb sx ix)) with snapshot.
        apply evt_done.
        eapply (ngn_idb_tail LOOP HLOOP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (l0 + 256 * l1)) m6 ps bq Bq Ix alloc rem data eb sx ix bt hcs dw dj cpad);
          [assumption | exact FR6 | assumption | exact G6 | exact PC6 | exact AG6 | exact HH | exact Hh | exact HD | exact Hd | exact DRNG
          | exact LEN | exact L30 | clear - BR0; lia | exact Hbt | exact OF5 | rewrite (get_le16_q8' data 8) by lia; fold l0 l1; rewrite unsigned_lit by lia; apply Z.mod_small; lia].
      + (* [comment removed for export] *)
        assert (SW : swapped = true) by (destruct swapped; [reflexivity|]; exfalso; revert BRS; rewrite ?unsigned_lit by (cbn; lia); cbn; lia).
        lazymatch goal with |- context [if swapped then ?X else ?Y] => replace (if swapped then X else Y) with X by (rewrite SW; reflexivity) end.
        cbv zeta.
        change (set_bufdata (swap_field 4 12 (swap_field 2 8 data)) (pv bq alloc data eb sx ix)) with (pv bq alloc (swap_field 4 12 (swap_field 2 8 data)) eb sx ix).
        rewrite (idb_swap_data' data) by lia. fold l0 l1 r0 r1 n0 n1 n2 n3.
        set (data' := firstn 8 data ++ [l1; l0; r0; r1; n3; n2; n1; n0] ++ skipn 16 data).
        change (pc_bufdata (pv bq alloc data' eb sx ix)) with data'.
        change (pc_linktype (pv bq alloc data' eb sx ix)) with linktype. change (pc_snapshot (pv bq alloc data' eb sx ix)) with snapshot.
        hide FR6. hide HH. hide HD. hide PRIV. hide CELLS.
        eapply evt_cut.
        { eapply (ngn_idb_swap _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6 l0 l1 n0 n1 n2 n3 Bq);
            [repeat (apply Forall_cons; [lia|]); apply Forall_nil | exact BUF4 | assumption | clear - K1; lia | clear - K4 W4 LEN REM BR0; lia]. }
        cbv beta. intros ms' (a0v & a1v & a2v & a3v & m7 & -> & MU7 & WM7 & MI7 & HB7 & E1 & E0).
        assert (AGP : agrees_on (fun a => outside [(Bq + 8, Bq + 16)]%Z a) m6 m7) by (eapply agrees_on_of_munch; [exact MU7 | exact WM7 | intros a _ Ho; exact Ho]).
        unhide FR6. unhide HH. unhide HD. unhide PRIV. unhide CELLS.
        lazymatch goal with STX : stk ssegs m6 _ _ |- _ => pose proof (agrees_stk _ _ _ _ _ AGP STX ltac:(intros a Ha; cbn [outside]; gio_ceil_fact; clear -CLO__ Ha K4 LO BU SPW W4 LEN REM BR0; lia)) as ST7 end.
        apply (agrees_rw_cells _ _ _ _ _ AGP) in FR6; [| intros a Ha; unfold F_ngnextA.ngn_frame in Ha; rewrite !cells_size_app in Ha; cbn [outside cells_size csize Nat.add] in Ha |- *; gio_ceil_fact; clear -CLO__ Ha K4 LO BU SPW W4 LEN REM BR0; lia].
        apply (agrees_rw_cells _ _ _ _ _ AGP) in HH; [| intros a Ha; rewrite Hh in Ha; cbn [outside]; gio_ceil_fact; clear -CLO__ Ha K4 LO BU SPW R1 W4 LEN REM BR0; lia].
        apply (agrees_rw_cells _ _ _ _ _ AGP) in HD; [| intros a Ha; cbn [cells_size] in Ha; rewrite Hd in Ha; cbn [outside]; gio_ceil_fact; clear -CLO__ Ha K4 LO BU SPW R1 R2 W4 LEN REM BR0; lia].
        assert (G7 : GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m7).
        { eapply (GIo_pcap_frame K HFL SFL); [exact G6 | exact MU7 | exact WM7 |]. apply Forall_cons; [| apply Forall_nil].
          right. unfold iv_in_block, pcap_blocks. apply Exists_cons_tl. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd pc_buffer pc_bufalloc F_ngnextA.pv]. clear - W4 LEN REM BR0; lia. }
        (* [comment removed for export] *)
        assert (BUF7 : rw_cells ssegs m7 Bq [CB (Z.to_nat alloc) (firstn 8 bsx' ++ [b8 l1; b8 l0; b8 r0; b8 r1; b8 n3; b8 n2; b8 n1; b8 n0] ++ skipn 16 bsx')]).
        { assert (R7 : rw_cells ssegs m7 Bq [CB 8 (firstn 8 bsx'); C2 (Z_to_bv 64 (l1 + 256 * l0)); CB 2 [b8 r0; b8 r1]; C4 (Z_to_bv 64 (le4val n3 n2 n1 n0)); CB (Z.to_nat alloc - 16) (skipn 16 bsx')]).
          { eapply rw_cells_recell; [exact HB7 | | ].
            { cbn. rewrite ?length_firstn, ?length_skipn. repeat split; try exact Logic.I; lia. }
            cbn [cells_bytes cbytes app]. rewrite (le2_of_val a1v l1 l0 l1), (le4_word_mod32 a0v (le4val n3 n2 n1 n0) E0) by lia. rewrite (le2_lit l1 l0), (le4_lit n3 n2 n1 n0) by lia. reflexivity. }
          pose proof (rw_cells_merge ssegs m7 Bq [] _ [] ltac:(rewrite app_nil_r; exact R7)) as R8.
          lazymatch type of R8 with rw_cells _ _ _ ([] ++ [CB ?n ?bs]) =>
            replace n with (Z.to_nat alloc) in R8 by (cbn [cells_size csize]; clear - W4 LEN REM BR0; lia);
            cbn [app cells_bytes cbytes] in R8 end.
          rewrite (le2_lit l1 l0), (le4_lit n3 n2 n1 n0), app_nil_r in R8 by lia. exact R8. }
        assert (LEN' : length data' = length data).
        { subst data'. change (skipn 16 data) with (skipn (8 + length [l1; l0; r0; r1; n3; n2; n1; n0]) data). apply splice_length. cbn [length]. clear - LEN REM BR0; lia. }
        assert (PFX7 : firstn (length data') (firstn 8 bsx' ++ [b8 l1; b8 l0; b8 r0; b8 r1; b8 n3; b8 n2; b8 n1; b8 n0] ++ skipn 16 bsx') = map b8 data').
        { subst data'. change ([b8 l1; b8 l0; b8 r0; b8 r1; b8 n3; b8 n2; b8 n1; b8 n0] ++ skipn 16 bsx') with (map b8 [l1; l0; r0; r1; n3; n2; n1; n0] ++ skipn (8 + length [l1; l0; r0; r1; n3; n2; n1; n0]) bsx').
          change ([l1; l0; r0; r1; n3; n2; n1; n0] ++ skipn 16 data) with ([l1; l0; r0; r1; n3; n2; n1; n0] ++ skipn (8 + length [l1; l0; r0; r1; n3; n2; n1; n0]) data).
          apply splice_pfx; [exact PFX | cbn [length]; clear - LEN REM BR0; lia | clear - LBS W4; lia]. }
        assert (HQ7 : forall a, (0 <= a < 2^64)%Z -> ~ (Bq <= a < Bq + alloc)%Z -> outside [(Bq + 8, Bq + 16)]%Z a) by (intros a _ Hn; cbn [outside]; clear - Hn W4 LEN REM BR0; lia).
        pose proof (PCAPR_bufdata ps bq Bq Ix alloc data data' eb sx ix m6 m7 _ _ G6 PC6 AGP HQ7 BUF7 PFX7 LEN') as PC7.
        assert (G7' : GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data' eb sx ix) P Bq Ix) FB m7) by exact G7.
        assert (AG7 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m7).
        { eapply agrees_on_trans; [exact AG6|]. eapply agrees_on_weaken; [exact AGP|]. intros a [[Ha|Ha] _]; cbn [outside]; [gio_ceil_fact; clear -CLO__ Ha K4 LO BU SPW W4 LEN REM BR0; lia|].
          destruct (ngn_CLc_facts _ _ _ _ G6 Ha) as [Hc Hnb]. split; [| exact Logic.I].
          intros Hr. apply Hnb. unfold pcap_blocks, in_block. apply Exists_cons_tl. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd pc_buffer pc_bufalloc F_ngnextA.pv]. clear - Hr W4 LEN REM BR0; lia. }
        assert (DRNG' : Forall (fun x => 0 <= x < 256)%Z data').
        { subst data'. change (skipn 16 data) with (skipn (8 + length [l1; l0; r0; r1; n3; n2; n1; n0]) data). apply splice_Forall; [exact DRNG|].
          repeat (apply Forall_cons; [lia|]). apply Forall_nil. }
        apply evt_done.
        eapply (ngn_idb_tail LOOP HLOOP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a1v m7 ps bq Bq Ix alloc rem data' eb sx ix bt hcs dw dj cpad);
          [exact ST7 | exact FR6 | exact MI7 | exact G7' | exact PC7 | exact AG7 | exact HH | exact Hh | exact HD | exact Hd | exact DRNG'
          | rewrite LEN'; exact LEN | exact L30 | clear - BR0; lia | exact Hbt | exact OF5 | rewrite E1; subst data'; rewrite idb_splice_le16 by (clear - LEN REM BR0; lia); clear - Rl0 Rl1; Z.div_mod_to_equations; lia].
  Qed.
  End Sz9.
  Lemma ngn_idb : ltac:(let t := eval cbv delta [ngn_idb__stmt] in ngn_idb__stmt in exact t).
  Proof using AD ADDIF ADJ AH ALN BU HFL HPL LO P1 P2 P4 P5 P6 R1 R2 SFL SNPRINTF SPM SPW TP W1 W9. intros LOOP HLOOP ra' t0' t1' t2' a0' a1' a2' a4' a5' a6' a7' x6 x10 t3' t4' t5' t6' m5 ps bq Bq Ix alloc rem data eb sx ix bt hcs dw dj cpad. ltac2:(SecDiet.SzSec.closeP 'ngn_idb__body "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NgnCtx.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3 Require NgnPure.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MonadX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.NpArith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.PPFacts.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.Pcap_iface_pp.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface_ng.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.PP_kit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3.NgnPure. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextS.TwB.
Import OSSVerify.libpcap.fuzz_pcap.images.Ubsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Ceiling.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia_e2w2_base := first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                                 | zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac ceil_mentioned := lazymatch goal with | |- context [@alloc_ceiling _] => idtac | _ : context [@alloc_ceiling _] |- _ => idtac end.
(* [comment removed for export] *)
Local Ltac gio_ceil_fact :=
  match goal with
  | G : GIo _ _ _ _ _ _ |- _ => let H := fresh "CLO__" in pose proof (S3.PcapRep.TwB.GIo_ceil_lo _ _ _ _ _ _ G) as H; unfold rc_lo in H
  end.
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try gio_ceil_fact; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Open Scope bv_scope.
Section WithCeil.
Context {CEILV : CEIL}.
Section NgnCtx.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HPL : heap_perm_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis SNPRINTF : snprintf_spec_stmt K.
  Hypothesis PP : post_process_stmt.
  Hypothesis ADJ : adjust_snapshot_stmt.
  Hypothesis RBLK : read_block_stmt HO K sites.
  Hypothesis ADDIF : add_interface_stmt HO K sites.

  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (R : rctx) (CLc FB : list (cblock (hptr:=hptr))) (lo P HA DA Af : Z) (m : mem) (o : option hptr).
  Variables (self f : hptr) (bufsize : Z) (swapped : bool) (vmaj vmin snapshot linktype ltext prec brk : Z) (header : pkthdr).
  Hypothesis LO : (usp0 R - 8388608 <= lo)%Z.
  Hypothesis BU : (lo + 81920 <= bv_unsigned sp)%Z.
  Hypothesis SPM : (bv_unsigned sp <= rc_spmain R)%Z.
  Hypothesis TP : tp = rc_tp R.
  Hypothesis ALN : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis SITES : sites = sites_at (bv_unsigned sp + D_NEXT_PACKET).
  Hypothesis R1 : (bv_unsigned sp <= HA)%Z.
  Hypothesis R2 : (HA + 24 <= DA)%Z.
  Hypothesis R3 : (DA + 8 <= rc_spmain R)%Z.
  Hypothesis AH : (HA mod 8 = 0)%Z.
  Hypothesis AD : (DA mod 8 = 0)%Z.
  Hypothesis SPW : (140735340871680 <= usp0 R)%Z.
  Hypothesis SP47 : (usp0 R <= 2^47)%Z.
  Hypothesis HinF : In (f, Af, FILE_BLOCK) FB.
  Hypothesis P1 : (0 < P)%Z.  Hypothesis P2 : (P mod 16 = 0)%Z.  Hypothesis P4 : (P + 680 <= CEILZ)%Z.
  Hypothesis P5 : (P + 680 <= 65536 \/ 352256 <= P)%Z.  Hypothesis P6 : (P + 680 <= utp R - 200 \/ utp R - 200 + 4096 <= P)%Z.
  Hypothesis A1 : (0 < Af)%Z.  Hypothesis A4 : (Af + 1264 <= CEILZ)%Z.
  Hypothesis W1 : (1 <= snapshot <= INT_MAX)%Z.  Hypothesis W2 : (0 <= bufsize <= 2^30)%Z.
  Hypothesis W5 : brk = 0%Z.  Hypothesis W6 : prec = 0%Z.
  Hypothesis W7 : (0 <= vmaj < 2^16)%Z.  Hypothesis W8 : (0 <= vmin < 2^16)%Z.
  Hypothesis W9 : (0 <= linktype < 2^31)%Z.  Hypothesis W10 : (-2^31 <= ltext < 2^31)%Z.

  Let POSTQ := next_packet_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o.

  (* [comment removed for export] *)
  #[local] Abbreviation pv := (S3.F_ngnextA.TwB.pv self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header).
  #[local] Abbreviation ngn_frame := (S3.F_ngnextA.TwB.ngn_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 P HA DA).
  #[local] Abbreviation ngn_final := (S3.F_ngnextA.TwB.ngn_final K sp R CLc FB P HA DA m o).
  #[local] Abbreviation ngn_finalC := (S3.F_ngnextA.TwB.ngn_finalC K sp R CLc FB P HA DA m o).
  #[local] Abbreviation ngn_final_C := (S3.F_ngnextA.TwB.ngn_final_C K sp R CLc FB P HA DA m o).
  #[local] Abbreviation ngn_ret_m1 := (S3.F_ngnextA.TwB.ngn_ret_m1 K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o BU).
  #[local] Abbreviation ngn_ret_0 := (S3.F_ngnextA.TwB.ngn_ret_0 K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o BU).
  #[local] Abbreviation ngn_ret_1 := (S3.F_ngnextA.TwB.ngn_ret_1 K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o BU).
  #[local] Abbreviation ngn_CLc_facts := (S3.F_ngnextA.TwB.ngn_CLc_facts K R CLc FB).
  #[local] Abbreviation ngn_snp_call := (S3.F_ngnextA.TwB.ngn_snp_call K HFL SFL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU SPM TP ALN R1 R2 AH AD SPW P1 P4 P5).
  #[local] Abbreviation ngn_snp := (S3.F_ngnextA.TwB.ngn_snp K HFL SFL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU SPM TP ALN R1 R2 AH AD SPW P1 P4 P5).
  #[local] Abbreviation ngn_mcp := (S3.F_ngnextA.TwB.ngn_mcp K HFL SFL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU ALN R1 R2 AH AD SPW P1 P4 P5 P6).
  #[local] Abbreviation PCAPRC_errbuf := (S3.F_ngnextA.TwB.PCAPRC_errbuf K sp R lo P HA DA LO BU ALN R1 R2 AH AD SPW P1).

  Ltac norm_g :=
    unfold S3.F_ngnextA.TwB.pv; unfold pcap_blocks; unfold psize; unfold is_ng;
    cbn [pc_self pc_rfile pc_bufsize pc_bufalloc pc_buffer pc_bufdata pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype
         pc_linktype_ext pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_priv priv_cells ng_of ng_ifaces_ptr_of
         set_bufdata set_errbuf set_buffer set_ng set_priv];
    unfold PCAP_NG_SF_TOTAL, PCAP_PRIV_OFF.
  Ltac norm_p :=
    unfold S3.F_ngnextA.TwB.pv in *; unfold pcap_blocks in *; unfold psize in *; unfold is_ng in *;
    cbn [pc_self pc_rfile pc_bufsize pc_bufalloc pc_buffer pc_bufdata pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype
         pc_linktype_ext pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_priv priv_cells ng_of ng_ifaces_ptr_of
         set_bufdata set_errbuf set_buffer set_ng set_priv] in *;
    unfold PCAP_NG_SF_TOTAL, PCAP_PRIV_OFF in *.

  #[local] Abbreviation ngn_pp := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB.TwB.ngn_pp K HFL SFL PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPM R1 R2 R3 AH AD SPW SP47 P1 P2 P4 P5 P6 W1 W2 W5 W6 W7 W8 W9 W10).

  #[local] Abbreviation ngn_found := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.TwB.ngn_found K HFL SFL SNPRINTF PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPM TP ALN R1 R2 R3 AH AD SPW SP47 P1 P2 P4 P5 P6 W1 W2 W5 W6 W7 W8 W9 W10).
  #[local] Abbreviation ccells := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.TwB.ccells ).
  #[local] Abbreviation ngn_spb := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.TwB.ngn_spb K HFL SFL SNPRINTF PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPM TP ALN R1 R2 R3 AH AD SPW SP47 P1 P2 P4 P5 P6 W1 W2 W5 W6 W7 W8 W9 W10).
  #[local] Abbreviation ngn_epb := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.TwB.ngn_epb K HFL SFL SNPRINTF PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPM TP ALN R1 R2 R3 AH AD SPW SP47 P1 P2 P4 P5 P6 W1 W2 W5 W6 W7 W8 W9 W10).
  #[local] Abbreviation ngn_pb := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.TwB.ngn_pb K HFL SFL SNPRINTF PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPM TP ALN R1 R2 R3 AH AD SPW SP47 P1 P2 P4 P5 P6 W1 W2 W5 W6 W7 W8 W9 W10).


  #[local] Abbreviation pcapT := (pcap hptr hptr).
  #[local] Abbreviation MR := (M (PState H hptr) ((Z + ng_found) * pcap hptr hptr)).

  #[local] Abbreviation ngn_KF := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.TwB.ngn_KF (H:=H) (hptr:=hptr)).
  #[local] Abbreviation ngn_shbK := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.TwB.ngn_shbK (H:=H) (hptr:=hptr)).
  #[local] Abbreviation ngn_idbK := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.TwB.ngn_idbK HO sites).
  #[local] Abbreviation ngn_head := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.TwB.ngn_head K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA Af m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header).
  #[local] Abbreviation ngn_too_short := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.TwB.ngn_too_short K HFL SFL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU SPM TP ALN R1 R2 AH AD SPW P1 P4 P5).
  #[local] Abbreviation PCAPR_bufdata := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.TwB.PCAPR_bufdata K sp R CLc FB lo P HA DA self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU ALN R1 R2 AH AD SPW P1 P5).
  #[local] Abbreviation get_le16_q8' := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.TwB.get_le16_q8' ).
  #[local] Abbreviation firstn2_q8 := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.TwB.firstn2_q8 sp R lo P HA DA LO BU R1 R2 SPW P1).
  #[local] Abbreviation bswap16_2 := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.TwB.bswap16_2 sp P HA DA).

  Ltac name_field data off a b c d DRNG :=
    set (a := q8 data off 0%Z) in *; set (b := q8 data off 1%Z) in *; set (c := q8 data off 2%Z) in *; set (d := q8 data off 3%Z) in *;
    let Ra := fresh "R" a in let Rb := fresh "R" b in let Rc := fresh "R" c in let Rd := fresh "R" d in
    pose proof (q8_range data off 0%Z DRNG ltac:(lia)) as Ra; pose proof (q8_range data off 1%Z DRNG ltac:(lia)) as Rb;
    pose proof (q8_range data off 2%Z DRNG ltac:(lia)) as Rc; pose proof (q8_range data off 3%Z DRNG ltac:(lia)) as Rd;
    fold a in Ra; fold b in Rb; fold c in Rc; fold d in Rd.

  #[local] Abbreviation ngn_snp90 := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextS.TwB.ngn_snp90 K HFL SFL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU SPM TP ALN R1 R2 AH AD SPW P1 P4 P5).
  #[local] Abbreviation ngn_snp8c := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextS.TwB.ngn_snp8c K HFL SFL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU SPM TP ALN R1 R2 AH AD SPW P1 P4 P5).

  (* [comment removed for export] *)
  Definition ngn_idb_swap__stmt : Prop := forall (ra' t0' t1' t2' x0 x1 a0' a1' a2' a3' a4' a5' a6' a7' x2 x3 x5 x7 x8 x9 x10 x11 t3' t4' t5' t6' : word) (mx : mem)
           (l0 l1 n0 n1 n2 n3 : Z) (Bq : Z) (pre r2 : list byte) (rest : list cell),
      Forall (fun x => 0 <= x < 256)%Z [l0; l1; n0; n1; n2; n3] ->
      rw_cells usegs mx Bq ([CB 8 pre; C2 (Z_to_bv 64 (l0 + 256 * l1)); CB 2 r2; C4 (Z_to_bv 64 (le4val n0 n1 n2 n3))] ++ rest) ->
      mem_inv usegs mx -> (0 <= Bq)%Z -> (Bq + 16 <= 2^64)%Z ->
      evt usegs (fun ms' => exists (a1v a2v a3v a4v : word) (m' : mem),
          ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' x0 x1 a0' a1v a2v a3v a4v a5' a6' a7'
                       x2 x3 (Z_to_bv 64 65280) x5 (Z_to_bv 64 (Bq + 8)) x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 0x17bc0) fc None m' (seg_rom usegs)
          /\ munch [(Bq + 8, Bq + 16)]%Z mx m' /\ wmono usegs mx m' /\ mem_inv usegs m'
          /\ rw_cells usegs m' Bq ([CB 8 pre; C2 a1v; CB 2 r2; C4 a2v] ++ rest)
          /\ (bv_unsigned a1v = l1 + 256 * l0 + 65536 * l1)%Z /\ (bv_unsigned a2v mod 2^32 = le4val n3 n2 n1 n0)%Z)
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' x0 x1 a0' a1' a2' a3' a4' a5' a6' a7'
                 x2 x3 (Z_to_bv 64 65280) x5 (Z_to_bv 64 (Bq + 8)) x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 0x17b80) fc None mx (seg_rom usegs)).
  Section Sz1.
  Variables ra' t0' t1' t2' x0 x1 a0' a1' a2' a3' a4' a5' a6' a7' x2 x3 x5 x7 x8 x9 x10 x11 t3' t4' t5' t6' mx l0 l1 n0 n1 n2 n3 Bq pre r2 rest : ltac2:(SecDiet.SzSec.tyM 'ngn_idb_swap__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma ngn_idb_swap__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_idb_swap__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using BU LO P1 R1 R2 SPW. pin_using (fun (BU LO P1 R1 R2 SPW : unit) => tt).
 intros GR HB MI B0 B64.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof GR as GR'. do 6 (apply Forall_cons_iff in GR'; destruct GR' as [? GR']). clear GR'.
    pose proof (munch_refl [(Bq + 8, Bq + 16)]%Z mx) as MU. pose proof (wmono_refl usegs mx) as WM.
    step. rewrite (zx16_lit (l0 + 256 * l1)) by lia.
    step. rewrite (sx32_lit n0 n1 n2 n3) by lia.
    do 12 step.
    step. step.
    apply evt_done. cbv beta.
    lazymatch goal with HX : rw_cells usegs ?mm Bq (CB 8 pre :: C2 ?w1 :: CB 2 r2 :: C4 ?w0 :: _) |- _ =>
      exists w1, w0; do 2 eexists; exists mm; split; [reflexivity|];
      split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [exact HX|] end.
    split; [apply (swap16_val _ l0 l1); [assumption | assumption | apply unsigned_lit; lia] |].
    apply swap32_sxv_mod32; assumption.
  Qed.
  End Sz1.
  Lemma ngn_idb_swap : ltac:(let t := eval cbv delta [ngn_idb_swap__stmt] in ngn_idb_swap__stmt in exact t).
  Proof using BU LO P1 R1 R2 SPW. intros ra' t0' t1' t2' x0 x1 a0' a1' a2' a3' a4' a5' a6' a7' x2 x3 x5 x7 x8 x9 x10 x11 t3' t4' t5' t6' mx l0 l1 n0 n1 n2 n3 Bq pre r2 rest. ltac2:(SecDiet.SzSec.closeP 'ngn_idb_swap__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
  (* [comment removed for export] *)
  Definition ngn_idb_call__stmt : Prop := forall (LOOP : pcapT -> MR),
    ngn_head (fun p' ps' ms' => implM usegs (mbind (LOOP p') ngn_KF) ps' POSTQ ms') ->
    forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x7 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (bq : hptr) (Bq Ix alloc rem : Z) (data eb : list Z) (sx : pcap_ng_sf) (ix : option hptr) (bt : Z) (hcs : list cell) (dw : cell) (dj : list byte) (cpad : list byte),
      stk usegs m5 lo (bv_unsigned sp + -160) ->
      rw_cells usegs m5 (bv_unsigned sp + -160) (ngn_frame dj [C8 (Z_to_bv 64 (Bq + 16)); C8 (Z_to_bv 64 (rem - 8)); C4 (Z_to_bv 64 bt); CB 4 cpad]) -> mem_inv usegs m5 ->
      GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells usegs m5 HA hcs -> cells_size hcs = 24%nat -> rw_cells usegs m5 DA [dw] -> csize dw = 8%nat ->
      Forall (fun x => 0 <= x < 256)%Z data -> (Z.of_nat (length data) = rem + 12)%Z -> (rem + 12 <= 2^30)%Z -> (8 <= rem)%Z ->
      (0 <= bt < 2^32)%Z -> ps_outfile ps = o ->
      implM usegs (mbind (mbind (add_interface MOps (prims HO fo_nop sites) (pv bq alloc data eb sx ix) 8 (mkCursor 16 (rem - 8) bt))
                          (fun r => let '(ok, c, p, msg) := r in if ok then LOOP p else mret (inl (-1)%Z, set_errbuf msg p))) ngn_KF) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 (P + 216)) a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 0) (Z_to_bv 64 P) (Z_to_bv 64 65280) (Z_to_bv 64 Af) (Z_to_bv 64 (Bq + 8)) x7 (Z_to_bv 64 439041101) (Z_to_bv 64 2) (Z_to_bv 64 1) (Z_to_bv 64 168627466)
                 t3' t4' t5' t6') F (Z_to_bv 64 0x17be0) fc None m5 (seg_rom usegs)).
  Section Sz2.
  Variables LOOP ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x7 t3' t4' t5' t6' m5 ps bq Bq Ix alloc rem data eb sx ix bt hcs dw dj cpad : ltac2:(SecDiet.SzSec.tyM 'ngn_idb_call__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @LOOP).
  Lemma ngn_idb_call__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_idb_call__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using ADDIF ALN BU HPL LO P1 P4 R1 R2 SPM SPW TP. pin_using (fun (ADDIF ALN BU HPL LO P1 P4 R1 R2 SPM SPW TP : unit) => tt).
    intros HLOOP.
 intros ST5 FR5 MI5 G5 PC5 AG5 HH Hh HD Hd DRNG LEN L30 REM Hbt OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof PC5 as (Afx & Hin & (Bx' & Ix' & jx' & padx & bsx' & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    pose proof G5 as G5e. rewrite EPB in G5e.
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G5e ltac:(right; left; reflexivity)) as (K1 & K2 & K3 & K4 & K5 & K6).
    pose proof (PB_apart K _ _ _ _ _ _ _ _ _ _ G5 eq_refl) as [APB API].
    pose proof WF as (W1' & W2' & W3 & W4 & W5' & W6' & W7' & W8' & W9' & W10' & W11 & W12 & W13 & W14).
    unfold S3.F_ngnextA.TwB.pv, pcap_blocks, psize, is_ng in EPB, K1, K2, K3, K4, K5, K6, APB. cbn [pc_self pc_buffer pc_bufalloc pc_priv] in EPB, K1, K2, K3, K4, K5, K6, APB.
    unfold PCAP_NG_SF_TOTAL in APB.
    unfold S3.F_ngnextA.TwB.pv in W3, W4, W13. cbn [pc_bufalloc pc_bufdata pc_priv] in W3, W4, W13.
    assert (EBX : Bx' = Bq) by congruence. subst Bx'.
    unfold S3.F_ngnextA.TwB.pv in Hin. cbn [pc_rfile] in Hin.
    unfold S3.F_ngnextA.TwB.pv in BUF. cbn [pc_bufalloc] in BUF. cbn [pc_bufdata] in PFX.
    pose proof PRIV as NG5. unfold priv_cells, S3.F_ngnextA.TwB.pv, PCAP_PRIV_OFF in NG5. cbn [pc_priv] in NG5.
    assert (NPB : forall a, in_block CLc a -> (a < alloc_ceiling)%Z /\ ~ (P <= a < P + 680)%Z /\ ~ (Bq <= a < Bq + alloc)%Z).
    { intros a Ha. destruct (ngn_CLc_facts _ _ _ _ G5 Ha) as [Hc Hnb]. split; [clear - Hc; lia|]. split; intros Hr; apply Hnb; unfold pcap_blocks, in_block.
      - apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. unfold psize, is_ng, S3.F_ngnextA.TwB.pv. cbn [pc_priv]. unfold PCAP_NG_SF_TOTAL. clear - Hr; lia.
      - apply Exists_cons_tl. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd pc_buffer pc_bufalloc S3.F_ngnextA.TwB.pv]. clear - Hr; lia. }
    assert (INP : forall a, (P <= a < P + 680)%Z -> client_keeps ((CLc ++ [(self, P, PCAP_NG_SF_TOTAL); (bq, Bq, alloc)]) ++ []) (bv_unsigned sp + -160) a).
    { intros a Ha. right. rewrite app_nil_r. apply in_block_app. right. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. unfold PCAP_NG_SF_TOTAL. exact Ha. }
    (* [comment removed for export] *)
    apply pcap_cells_split4 in CELLS as (PRE & CE & HDR & OPS); [|reflexivity].
    apply (rw_cells_split_CB usegs m5 _ [] 304 _ [] [256; 48]%nat) in CE; [|reflexivity]. cbn [mk_CB_cells app] in CE.
    destruct (rw_cells_cut _ _ _ 1 CE) as [CE1 CE2]. clear CE. cbn [firstn skipn cells_size csize Nat.add] in CE1, CE2.
    replace (P + 216 + Z.of_nat 256)%Z with (P + 472)%Z in CE2 by lia.
    unfold pc_pre in PRE. destruct (rw_cells_cut _ _ _ 7 PRE) as [PRE0 PRE7]. destruct (rw_cells_cut _ _ _ 2 PRE7) as [P48 PRE9]. clear PRE PRE7.
    cbn [firstn skipn cells_size csize Nat.add app] in PRE0, P48, PRE9.
    replace (P + Z.of_nat 48)%Z with (P + 48)%Z in P48 by lia. replace (P + Z.of_nat 48 + Z.of_nat 12)%Z with (P + 60)%Z in PRE9 by lia.
    (* [comment removed for export] *)
    pose proof FR5 as FRJ. unfold S3.F_ngnextA.TwB.ngn_frame in FRJ. cbn [app] in FRJ.
    destruct (rw_cells_cut _ _ _ 4 FRJ) as [F0 F4]. destruct (rw_cells_cut _ _ _ 4 F4) as [FCUR FS]. clear FRJ F4.
    cbn [firstn skipn cells_size csize Nat.add app] in F0, FCUR, FS.
    replace (bv_unsigned sp + -160 + Z.of_nat 32)%Z with (bv_unsigned sp + -128)%Z in FCUR by lia.
    replace (bv_unsigned sp + -160 + Z.of_nat 32 + Z.of_nat 24)%Z with (bv_unsigned sp + -104)%Z in FS by lia.
    hide F0. hide FCUR. hide FS. hide PRE0. hide P48. hide PRE9. hide CE1. hide CE2. hide HDR. hide OPS. hide NG5. hide BUF. hide HH. hide HD. hide FR5. hide PRIV. hide IFS.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl usegs m5) as WM.
    unfold implM. iprefix. step. step. step. step. step. clear MU WM.
    unhide F0. unhide FCUR. unhide FS. unhide PRE0. unhide P48. unhide PRE9. unhide CE1. unhide CE2. unhide HDR. unhide OPS. unhide NG5. unhide BUF. unhide HH. unhide HD. unhide FR5. unhide PRIV. unhide IFS.
    apply evt_done. apply (implM_bind_assoc usegs). name_sp sp (-160)%Z. eapply (implM_bind usegs).
    { eapply (ADDIF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 R ps (CLc ++ [(self, P, PCAP_NG_SF_TOTAL); (bq, Bq, alloc)]) [] FB P Bq Ix' (bv_unsigned sp + -128)%Z (P + 216)%Z lo 8%Z
                (pv bq alloc data eb sx ix) sx ix (mkCursor 16 (rem - 8) bt) bsx' (firstn 256 (pj_g jx')) padx cpad);
        [ split; [rewrite app_nil_r, <- app_assoc; cbn [app]; pose proof G5e as GX; unfold pcap_blocks, S3.F_ngnextA.TwB.pv, psize, is_ng in GX; cbn [pc_self pc_buffer pc_bufalloc pc_priv] in GX; unfold IBLK; exact GX |];
          split; [rewrite Hsp; exact ST5|]; split; [unfold rc_lo; lia|]; split; [unfold ADD_INTERFACE_STACK, MALLOC_STACK; rewrite Hsp; lia|];
          split; [rewrite Hsp; unfold rc_spmain in *; lia|]; split; [exact MI5|]; split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]
        | reflexivity
        | rewrite app_nil_r; apply in_or_app; right; left; reflexivity
        | rewrite app_nil_r; apply in_or_app; right; right; left; reflexivity
        | unfold PCAP_NG_SF_TOTAL; cbn [pc_bufalloc S3.F_ngnextA.TwB.pv]; exact APB
        | reflexivity | reflexivity | f_equal; lia | reflexivity
        | exact P48 | exact NG5 | exact IFS | clear - W13; lia | clear - W13; lia
        | exact BUF | exact PFX | cbn [pc_bufdata pc_bufalloc S3.F_ngnextA.TwB.pv]; clear - W3 W4; lia | exact DRNG
        | exact FCUR | rewrite Hsp; lia | unfold rc_spmain in *; lia | replace (bv_unsigned sp + -128)%Z with (bv_unsigned sp + (-128))%Z by lia; apply aligned16_8; [exact ALN| reflexivity]
        | lia | reflexivity | reflexivity | cbn [cur_remaining]; lia | cbn [cur_off cur_remaining pc_bufdata S3.F_ngnextA.TwB.pv]; lia | cbn [cur_block_type]; exact Hbt
        | exact CE1 | right; reflexivity ]. }
    intros [[[ok c5] p5] msg5] ps5 ms5 PO.
    destruct PO as (a0v & m6 & s' & i' & I' & pad' & bs' & E & OF6 & MI6 & ST6 & AG6 & EP & G6 & NG6 & U1 & U2 & U3 & U4 & BUF6 & PFX6 & LEN6 & GR6 & -> & RM).
    unfold hpost_regs in E. destruct_exs E. subst ms5. rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 0x17bf4)) with (Z_to_bv 64 0x17bf4) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    set (bd' := pc_bufdata p5) in *. clearbody bd'. subst p5.
    change (set_ng s' i' (set_bufdata bd' (pv bq alloc data eb sx ix))) with (pv bq alloc bd' eb s' i') in *.
    cbn [pc_bufdata pc_bufalloc S3.F_ngnextA.TwB.pv] in LEN6. change (pc_bufalloc (pv bq alloc data eb sx ix)) with alloc in AG6, BUF6.
    unfold PCAP_PRIV_OFF, PCAP_NG_SF_TOTAL in AG6.
    assert (OF7 : ps_outfile ps5 = o) by (rewrite OF6; exact OF5).
    (* [comment removed for export] *)
    transport F0 m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [left; clear - Ha; lia| gio_ceil_fact; clear -CLO__ Ha LO BU SPW P4 K4 APB RSP; lia]).
    transport FS m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [left; clear - Ha; lia| gio_ceil_fact; clear -CLO__ Ha LO BU SPW P4 K4 APB RSP; lia]).
    transport HH m6 AG6 ltac:(intros a Ha; rewrite Hh in Ha; split; [left; clear - Ha R1; lia| gio_ceil_fact; clear -CLO__ Ha R1 LO BU SPW P4 K4; lia]).
    transport HD m6 AG6 ltac:(intros a Ha; cbn [cells_size] in Ha; rewrite Hd in Ha; split; [left; clear - Ha R1 R2; lia| gio_ceil_fact; clear -CLO__ Ha R1 R2 LO BU SPW P4 K4; lia]).
    transport PRE0 m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [apply INP; clear - Ha; lia| gio_ceil_fact; clear -CLO__ Ha LO BU SPW P4 APB K3; lia]).
    transport P48 m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [apply INP; clear - Ha; lia| gio_ceil_fact; clear -CLO__ Ha LO BU SPW P4 APB K3; lia]).
    transport PRE9 m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [apply INP; clear - Ha; lia| gio_ceil_fact; clear -CLO__ Ha LO BU SPW P4 APB K3; lia]).
    transport CE2 m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [apply INP; clear - Ha; lia| gio_ceil_fact; clear -CLO__ Ha LO BU SPW P4 APB K3; lia]).
    transport HDR m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add hdr_cells pc_header S3.F_ngnextA.TwB.pv] in Ha; split; [apply INP; clear - Ha; lia| gio_ceil_fact; clear -CLO__ Ha LO BU SPW P4 APB K3; lia]).
    transport OPS m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add pc_ops] in Ha; split; [apply INP; clear - Ha; lia| gio_ceil_fact; clear -CLO__ Ha LO BU SPW P4 APB K3; lia]).
    pose proof (rw_cells_uncut _ _ _ _ _ PRE0 P48 ltac:(cbn; lia)) as PRE'. pose proof (rw_cells_uncut _ _ _ _ _ PRE' PRE9 ltac:(cbn; lia)) as PRE. clear PRE' PRE0 P48 PRE9.
    cbn [app] in PRE.
    assert (AG7 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m6).
    { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [exact AG6|]. intros a [[Ha|Ha] _].
      - split; [left; clear - Ha; lia| gio_ceil_fact; clear -CLO__ Ha LO BU SPW P4 K4; lia].
      - destruct (NPB a Ha) as (Hc & Hn1 & Hn2). split; [right; rewrite app_nil_r; apply in_block_app; left; exact Ha| gio_ceil_fact; clear -CLO__ Hc Hn1 Hn2 LO BU SPW; lia]. }
    assert (PBE : pcap_blocks (pv bq alloc bd' eb s' i') P Bq I' = [(self, P, PCAP_NG_SF_TOTAL); (bq, Bq, alloc)] ++ IBLK i' I' s').
    { unfold pcap_blocks, IBLK, S3.F_ngnextA.TwB.pv, psize, is_ng. cbn [pc_self pc_buffer pc_bufalloc pc_priv app]. destruct i'; reflexivity. }
    assert (G6' : GIo K R ps5 (CLc ++ pcap_blocks (pv bq alloc bd' eb s' i') P Bq I') FB m6).
    { eapply (GIo_perm K HPL); [exact G6|]. rewrite PBE, app_nil_r, (app_assoc CLc). apply Permutation.Permutation_app_comm. }
    assert (WF' : pcap_wf (pv bq alloc bd' eb s' i')).
    { unfold pcap_wf, S3.F_ngnextA.TwB.pv in WF |- *.
      cbn [pc_snapshot pc_bufsize pc_bufalloc pc_bufdata pc_break_loop pc_tstamp_precision pc_version_major pc_version_minor pc_linktype pc_linktype_ext pc_header pc_priv] in WF |- *.
      rewrite LEN6, U1, U2. clear - WF U3 U4. lia. }
    (* [comment removed for export] *)
    assert (JOIN : forall cs, rw_cells usegs m6 (P + 216) cs -> cells_size cs = 304%nat ->
              rw_cells usegs m6 P (pcap_cells_gen (pv bq alloc bd' eb s' i') P Bq (C8 (Z_to_bv 64 Afx)) (C8 (Z_to_bv 64 (pk_stats PK))) (C8 (Z_to_bv 64 (pk_oneshot PK))) (set_pj_g (cells_bytes cs) jx'))).
    { intros cs HCS Hcs.
      exact (pcap_cells_join4 _ P (pv bq alloc bd' eb s' i') Bq (C8 (Z_to_bv 64 Afx)) (C8 (Z_to_bv 64 (pk_stats PK))) (C8 (Z_to_bv 64 (pk_oneshot PK))) jx' cs header eq_refl PRE HCS Hcs HDR OPS). }
    cbv beta. unfold implM. iprefix.
    destruct ok; cbn [Z.b2z].
    - (* [comment removed for export] *)
      destruct RM as (HIF6 & (cpad' & HCUR6) & CR1' & CR2' & CR3' & CBT' & HEB6 & ->).
      pose proof (rw_cells_uncut _ _ _ _ _ HEB6 CE2 ltac:(cbn; lia)) as CE6.
      pose proof (JOIN _ CE6 eq_refl) as CELLS6.
      pose proof (rw_cells_uncut _ _ _ _ _ HCUR6 FS ltac:(cbn; lia)) as F46. pose proof (rw_cells_uncut _ _ _ _ _ F0 F46 ltac:(cbn; lia)) as FR6. clear F46.
      assert (PC6 : PCAPR (hptr:=hptr) P (pv bq alloc bd' eb s' i') (pcap_blocks (pv bq alloc bd' eb s' i') P Bq I') FB m6).
      { exists Afx. split; [exact Hin|]. eexists Bq, I', _, pad', bs'.
        split; [reflexivity|]. split; [exact CELLS6|]. split; [exact NG6|]. split; [exact BUF6|]. split; [exact PFX6|]. split; [exact HIF6| exact WF']. }
      hide FR6. hide CELLS6. hide NG6. hide BUF6. hide HH. hide HD. hide HCUR6. hide F0. hide FS. hide CE6. hide HEB6. hide CE2. hide HDR. hide OPS. hide PRE.
      pose proof (munch_refl ([] : list (Z * Z)) m6) as MU. pose proof (wmono_refl usegs m6) as WM.
      step. if_cases BRK; zify_cond BRK; [| exfalso; rewrite ?unsigned_lit in BRK by lia; clear - BRK; lia].
      unhide FR6. unhide CELLS6. unhide NG6. unhide BUF6. unhide HH. unhide HD.
      apply evt_done.
      unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.TwB.ngn_head in HLOOP. unfold NGN_LOOP in HLOOP.
      eapply (HLOOP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6 ps5 bq Bq I' alloc bd' eb s' i' hcs dw dj); [exact ST6 | exact FR6 | reflexivity | exact MI6 | exact G6' | exact PC6 | exact AG7 | exact HH | exact Hh | exact HD | exact Hd | exact OF7].
    - (* [comment removed for export] *)
      destruct RM as (CLOS & (ccs' & HCUR6 & Hccs') & (junk6 & HEB6) & LENM & MOK).
      pose proof (rw_cells_uncut _ _ _ _ _ HEB6 CE2 ltac:(cbn [cells_size csize]; clear - LENM; lia)) as CE6. cbn [app] in CE6.
      pose proof (JOIN _ CE6 ltac:(cbn [cells_size csize]; clear - LENM; lia)) as CELLS6.
      pose proof (rw_cells_uncut _ _ _ _ _ HCUR6 FS ltac:(rewrite Hccs'; cbn; lia)) as F46. pose proof (rw_cells_uncut _ _ _ _ _ F0 F46 ltac:(cbn; lia)) as FR6. clear F46.
      assert (PC6 : PCAPR_closable (hptr:=hptr) P (set_errbuf msg5 (pv bq alloc bd' eb s' i')) (pcap_blocks (pv bq alloc bd' eb s' i') P Bq I') FB m6).
      { exists Afx. split; [exact Hin|]. eexists Bq, I', _, pad', bs'.
        split; [reflexivity|]. split; [exact CELLS6|]. split; [exact NG6|]. split; [exact BUF6|]. split; [exact PFX6|]. split; [| exact WF'].
        unfold ifaces_closable, S3.F_ngnextA.TwB.pv. cbn [pc_priv set_errbuf]. unfold ng_ifaces_closable in CLOS. destruct i'; exact CLOS. }
      hide FR6. hide CELLS6. hide NG6. hide BUF6. hide HH. hide HD. hide HCUR6. hide F0. hide FS. hide CE6. hide HEB6. hide CE2. hide HDR. hide OPS. hide PRE.
      pose proof (munch_refl ([] : list (Z * Z)) m6) as MU. pose proof (wmono_refl usegs m6) as WM.
      step. if_cases BRK; zify_cond BRK; [exfalso; rewrite ?unsigned_lit in BRK by lia; clear - BRK; lia|].
      step.
      unhide FR6. unhide CELLS6. unhide NG6. unhide BUF6. unhide HH. unhide HD.
      apply evt_done. apply implM_retb. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.TwB.ngn_KF. unfold NGN_EPILOGUE.
      eapply (ngn_ret_m1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6 ps5 (pcap_blocks (pv bq alloc bd' eb s' i') P Bq I') _ _ _ _ dj);
        [exact ST6 | exact FR6 | exact Hccs' | exact MI6 |].
      split; [exact G6'|]. split; [exact PC6|]. split; [exact AG7|]. split; [exact HH|]. split; [exact Hh|]. split; [exact HD|]. split; [exact Hd| exact OF7].
  Qed.
  End Sz2.
  Lemma ngn_idb_call : ltac:(let t := eval cbv delta [ngn_idb_call__stmt] in ngn_idb_call__stmt in exact t).
  Proof using ADDIF ALN BU HPL LO P1 P4 R1 R2 SPM SPW TP. intros LOOP HLOOP ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x7 t3' t4' t5' t6' m5 ps bq Bq Ix alloc rem data eb sx ix bt hcs dw dj cpad. ltac2:(SecDiet.SzSec.closeP 'ngn_idb_call__body "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
  (* [comment removed for export] *)
  Definition ngn_idb_tail__stmt : Prop := forall (LOOP : pcapT -> MR),
    ngn_head (fun p' ps' ms' => implM usegs (mbind (LOOP p') ngn_KF) ps' POSTQ ms') ->
    forall (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' x7 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (bq : hptr) (Bq Ix alloc rem : Z) (data eb : list Z) (sx : pcap_ng_sf) (ix : option hptr) (bt : Z) (hcs : list cell) (dw : cell) (dj : list byte) (cpad : list byte),
      stk usegs m5 lo (bv_unsigned sp + -160) ->
      rw_cells usegs m5 (bv_unsigned sp + -160) (ngn_frame dj [C8 (Z_to_bv 64 (Bq + 16)); C8 (Z_to_bv 64 (rem - 8)); C4 (Z_to_bv 64 bt); CB 4 cpad]) -> mem_inv usegs m5 ->
      GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells usegs m5 HA hcs -> cells_size hcs = 24%nat -> rw_cells usegs m5 DA [dw] -> csize dw = 8%nat ->
      Forall (fun x => 0 <= x < 256)%Z data -> (Z.of_nat (length data) = rem + 12)%Z -> (rem + 12 <= 2^30)%Z -> (8 <= rem)%Z ->
      (0 <= bt < 2^32)%Z -> ps_outfile ps = o ->
      implM usegs (mbind (let lt := get_le16 data 8 in
                          let sl := get_le32 data 12 in
                          if negb (linktype =? lt) then mret (inl (-1)%Z, set_errbuf (Msg.iface_type_differs lt) (pv bq alloc data eb sx ix))
                          else if negb (snapshot =? pcapint_adjust_snapshot linktype sl) then mret (inl (-1)%Z, set_errbuf (Msg.iface_snaplen_differs sl) (pv bq alloc data eb sx ix))
                          else mbind (add_interface MOps (prims HO fo_nop sites) (pv bq alloc data eb sx ix) 8 (mkCursor 16 (rem - 8) bt))
                                     (fun r => let '(ok, c, p, msg) := r in if ok then LOOP p else mret (inl (-1)%Z, set_errbuf msg p))) ngn_KF) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 (P + 216)) (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 0) (Z_to_bv 64 P) (Z_to_bv 64 65280) (Z_to_bv 64 Af) (Z_to_bv 64 (Bq + 8)) x7 (Z_to_bv 64 439041101) (Z_to_bv 64 2) (Z_to_bv 64 1) (Z_to_bv 64 168627466)
                 t3' t4' t5' t6') F (Z_to_bv 64 0x17bc0) fc None m5 (seg_rom usegs)).
  Section Sz3.
  Variables LOOP ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' x7 t3' t4' t5' t6' m5 ps bq Bq Ix alloc rem data eb sx ix bt hcs dw dj cpad : ltac2:(SecDiet.SzSec.tyM 'ngn_idb_tail__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @LOOP).
  Lemma ngn_idb_tail__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_idb_tail__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AD ADDIF ADJ AH ALN BU HFL HPL LO P1 P2 P4 P5 P6 R1 R2 SFL SNPRINTF SPM SPW TP W1 W9. pin_using (fun (AD ADDIF ADJ AH ALN BU HFL HPL LO P1 P2 P4 P5 P6 R1 R2 SFL SNPRINTF SPM SPW TP W1 W9 : unit) => tt).
    intros HLOOP.
 intros ST5 FR5 MI5 G5 PC5 AG5 HH Hh HD Hd DRNG LEN L30 REM Hbt OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof PC5 as (Afx & Hin & (Bx' & Ix' & jx' & padx & bsx' & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    pose proof G5 as G5e. rewrite EPB in G5e.
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G5e ltac:(right; left; reflexivity)) as (K1 & K2 & K3 & K4 & K5 & K6).
    pose proof WF as (W1' & _ & W3 & W4 & _).
    unfold S3.F_ngnextA.TwB.pv, pcap_blocks, psize, is_ng in EPB, K1, K2, K3, K4, K5, K6. cbn [pc_self pc_buffer pc_bufalloc pc_priv] in EPB, K1, K2, K3, K4, K5, K6.
    unfold S3.F_ngnextA.TwB.pv in W3, W4, W1'. cbn [pc_bufalloc pc_bufdata pc_snapshot] in W3, W4, W1'. unfold INT_MAX in W1'.
    assert (EBX : Bx' = Bq) by congruence. subst Bx'.
    unfold pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF, S3.F_ngnextA.TwB.pv in CELLS.
    cbn [app pc_bufsize pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_header pc_priv pk_next_ng pk_cleanup_ng PK] in CELLS.
    unfold S3.F_ngnextA.TwB.pv in BUF. cbn [pc_bufalloc] in BUF. cbn [pc_bufdata] in PFX.
    (* [comment removed for export] *)
    cbv zeta. rewrite (get_le16_q8' data 8) by lia. rewrite (get_le32_q8 data 12) by lia.
    set (l0 := q8 data 8 0) in *. set (l1 := q8 data 8 1) in *.
    pose proof (q8_range data 8 0 DRNG ltac:(lia)) as Rl0. pose proof (q8_range data 8 1 DRNG ltac:(lia)) as Rl1. fold l0 in Rl0. fold l1 in Rl1.
    name_field data 12%Z n0 n1 n2 n3 DRNG.
    assert (LBS : length bsx' = Z.to_nat alloc) by (destruct BUF as [[WFB _] _]; cbn in WFB; lia).
    apply (rw_cells_split_CB usegs m5 _ [] (Z.to_nat alloc) _ [] [8; 2; 2; 4; Z.to_nat alloc - 16]%nat) in BUF; [| cbn; lia]. cbn [mk_CB_cells app] in BUF.
    rewrite !skipn_skipn in BUF. cbn [Nat.add] in BUF.
    rewrite (firstn2_q8 data bsx' 8 8 PFX eq_refl), (firstn4_q8 data bsx' 12 12 PFX eq_refl) in BUF by lia. fold l0 l1 n0 n1 n2 n3 in BUF.
    assert (BUF4 : rw_cells usegs m5 Bq [CB 8 (firstn 8 bsx'); C2 (Z_to_bv 64 (l0 + 256 * l1)); CB 2 (firstn 2 (skipn 10 bsx')); C4 (Z_to_bv 64 (le4val n0 n1 n2 n3)); CB (Z.to_nat alloc - 16) (firstn (Z.to_nat alloc - 16) (skipn 16 bsx'))]).
    { eapply rw_cells_recell; [exact BUF | | ].
      { cbn. rewrite ?length_firstn, ?length_skipn. repeat split; try exact Logic.I; lia. }
      cbn [cells_bytes cbytes app]. rewrite (le2_lit l0 l1), (le4_lit n0 n1 n2 n3) by lia. reflexivity. }
    clear BUF.
    pose proof FR5 as FRJ. unfold S3.F_ngnextA.TwB.ngn_frame in FRJ. cbn [app] in FRJ.
    pose proof (adjust_snapshot_range linktype (le4val n0 n1 n2 n3) ltac:(unfold le4val; lia)) as ADR. unfold INT_MAX in ADR.
    hide FR5. hide PRIV. hide IFS. hide HH. hide HD.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl usegs m5) as WM.
    unfold implM. iprefix.
    (* [comment removed for export] *)
    step. if_false.
    step. rewrite (sx32_small linktype) by lia.
    step. rewrite (zx16_lit (l0 + 256 * l1)) by lia.
    step. if_cases BR; zify_cond BR; rewrite ?unsigned_lit in BR by lia.
    - (* [comment removed for export] *)
      replace (linktype =? l0 + 256 * l1) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb]. cbv iota.
      step. step. step.
      unhide FR5. unhide PRIV. unhide IFS. unhide HH. unhide HD.
      assert (MSG : fmt_at m5 NGN_FMT_IFTYPE "an interface has a type %u different from the type of the first interface"%string)
        by (apply fmt_at_intro; [exact MI5 | vm_compute; reflexivity | unfold NGN_FMT_IFTYPE; lia | unfold NGN_FMT_IFTYPE; cbn; lia]).
      unfold NGN_FMT_IFTYPE in MSG.
      apply evt_done. apply implM_retb. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.TwB.ngn_KF.
      eapply ngn_snp8c with (args := [AInt (l0 + 256 * l1)%Z]);
        [exact ST5 | exact FR5 | reflexivity | exact MI5 | | exact MSG | reflexivity | cbn; lia | cbn; apply Forall2_cons; [reflexivity| apply Forall2_nil]].
      split; [exact G5|]. split; [apply PCAPR_closable_of; exact PC5|]. split; [exact AG5|]. split; [exact HH|]. split; [exact Hh|].
      split; [exact HD|]. split; [exact Hd| exact OF5].
    - (* [comment removed for export] *)
      replace (linktype =? l0 + 256 * l1) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb]. cbv iota.
      step. rewrite (sx32_small snapshot) by lia.
      step. rewrite (sx32_s32 (le4val n0 n1 n2 n3)) by (unfold le4val; lia).
      step.
      eapply evt_cut.
      { eapply (ADJ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m5 linktype (le4val n0 n1 n2 n3)); [reflexivity | lia | reflexivity | unfold le4val; lia]. }
      cbv beta. intros ms' (y0 & y1 & y2 & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & -> & ->).
      replace (ret_pc (Z_to_bv 64 0x17bdc)) with (Z_to_bv 64 0x17bdc) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      step. if_cases BR2; zify_cond BR2; rewrite ?unsigned_lit in BR2 by lia.
      + (* [comment removed for export] *)
        replace (snapshot =? pcapint_adjust_snapshot linktype (le4val n0 n1 n2 n3)) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb]. cbv iota.
        step. rewrite (sx32_lit n0 n1 n2 n3) by lia. step. step. step.
        unhide FR5. unhide PRIV. unhide IFS. unhide HH. unhide HD.
        assert (MSG : fmt_at m5 NGN_FMT_IFSNAP "an interface has a snapshot length %u different from the snapshot length of the first interface"%string)
          by (apply fmt_at_intro; [exact MI5 | vm_compute; reflexivity | unfold NGN_FMT_IFSNAP; lia | unfold NGN_FMT_IFSNAP; cbn; lia]).
        unfold NGN_FMT_IFSNAP in MSG.
        apply evt_done. apply implM_retb. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.TwB.ngn_KF.
        eapply ngn_snp8c with (args := [AInt (sxv n0 n1 n2 n3)]);
          [exact ST5 | exact FR5 | reflexivity | exact MI5 | | exact MSG | reflexivity | cbn; lia | cbn; apply Forall2_cons; [reflexivity| apply Forall2_nil]].
        split; [exact G5|]. split; [apply PCAPR_closable_of; exact PC5|]. split; [exact AG5|]. split; [exact HH|]. split; [exact Hh|].
        split; [exact HD|]. split; [exact Hd| exact OF5].
      + (* [comment removed for export] *)
        replace (snapshot =? pcapint_adjust_snapshot linktype (le4val n0 n1 n2 n3)) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb]. cbv iota.
        unhide FR5. unhide PRIV. unhide IFS. unhide HH. unhide HD.
        apply evt_done.
        eapply (ngn_idb_call LOOP HLOOP); [exact ST5 | exact FR5 | exact MI5 | exact G5 | exact PC5 | exact AG5 | exact HH | exact Hh | exact HD | exact Hd | exact DRNG | exact LEN | exact L30 | exact REM | exact Hbt | exact OF5].
  Qed.
  End Sz3.
  Lemma ngn_idb_tail : ltac:(let t := eval cbv delta [ngn_idb_tail__stmt] in ngn_idb_tail__stmt in exact t).
  Proof using AD ADDIF ADJ AH ALN BU HFL HPL LO P1 P2 P4 P5 P6 R1 R2 SFL SNPRINTF SPM SPW TP W1 W9. intros LOOP HLOOP ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' x7 t3' t4' t5' t6' m5 ps bq Bq Ix alloc rem data eb sx ix bt hcs dw dj cpad. ltac2:(SecDiet.SzSec.closeP 'ngn_idb_tail__body "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
  (* [comment removed for export] *)
  Definition ngn_idb__stmt : Prop := forall (LOOP : pcapT -> MR),
    ngn_head (fun p' ps' ms' => implM usegs (mbind (LOOP p') ngn_KF) ps' POSTQ ms') ->
    forall (ra' t0' t1' t2' a0' a1' a2' a4' a5' a6' a7' x6 x7 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (bq : hptr) (Bq Ix alloc rem : Z) (data eb : list Z) (sx : pcap_ng_sf) (ix : option hptr) (bt : Z) (hcs : list cell) (dw : cell) (dj : list byte) (cpad : list byte),
      stk usegs m5 lo (bv_unsigned sp + -160) ->
      rw_cells usegs m5 (bv_unsigned sp + -160) (ngn_frame dj (ccells Bq rem bt cpad)) -> mem_inv usegs m5 ->
      GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells usegs m5 HA hcs -> cells_size hcs = 24%nat -> rw_cells usegs m5 DA [dw] -> csize dw = 8%nat ->
      Forall (fun x => 0 <= x < 256)%Z data -> (Z.of_nat (length data) = rem + 12)%Z -> (rem + 12 <= 2^30)%Z -> (0 <= rem)%Z ->
      (0 <= bt < 2^32)%Z -> ps_outfile ps = o ->
      implM usegs (mbind (ngn_idbK LOOP (mkCursor 8 rem bt) (pv bq alloc data eb sx ix)) ngn_KF) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 (P + 216))
                 a0' a1' a2' (Z_to_bv 64 (s32 bt)) a4' a5' a6' a7'
                 (Z_to_bv 64 0) (Z_to_bv 64 P) (Z_to_bv 64 65280) (Z_to_bv 64 Af) x6 x7 (Z_to_bv 64 439041101) (Z_to_bv 64 2) (Z_to_bv 64 1) (Z_to_bv 64 168627466)
                 t3' t4' t5' t6') F (Z_to_bv 64 0x17b48) fc None m5 (seg_rom usegs)).
  Section Sz4.
  Variables LOOP ra' t0' t1' t2' a0' a1' a2' a4' a5' a6' a7' x6 x7 t3' t4' t5' t6' m5 ps bq Bq Ix alloc rem data eb sx ix bt hcs dw dj cpad : ltac2:(SecDiet.SzSec.tyM 'ngn_idb__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @LOOP).
  Lemma ngn_idb__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_idb__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AD ADDIF ADJ AH ALN BU HFL HPL LO P1 P2 P4 P5 P6 R1 R2 SFL SNPRINTF SPM SPW TP W1 W9. pin_using (fun (AD ADDIF ADJ AH ALN BU HFL HPL LO P1 P2 P4 P5 P6 R1 R2 SFL SNPRINTF SPM SPW TP W1 W9 : unit) => tt).
    intros HLOOP.
 intros ST5 FR5 MI5 G5 PC5 AG5 HH Hh HD Hd DRNG LEN L30 REM Hbt OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.TwB.ngn_idbK, get_from_block_data. cbn [cur_remaining cur_off cur_block_type].
    change (pc_swapped (pv bq alloc data eb sx ix)) with swapped. change (pc_bufdata (pv bq alloc data eb sx ix)) with data.
    change (pc_linktype (pv bq alloc data eb sx ix)) with linktype. change (pc_snapshot (pv bq alloc data eb sx ix)) with snapshot.
    pose proof FR5 as FRJ. unfold S3.F_ngnextA.TwB.ngn_frame, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.TwB.ccells in FRJ. cbn [app] in FRJ.
    hide FR5. hide HH. hide HD.
    pose proof (munch_refl [(bv_unsigned sp + -160 + 32, bv_unsigned sp + -160 + 48)]%Z m5) as MU. pose proof (wmono_refl usegs m5) as WM.
    unfold implM. iprefix. step. step.
    step. if_cases BR0; zify_cond BR0; rewrite ?unsigned_lit in BR0 by lia.
    - (* [comment removed for export] *)
      replace (rem <? 8) with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
      step. step. step. step. step.
      unhide FR5. unhide HH. unhide HD. apply evt_done. apply implM_retb. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.TwB.ngn_KF.
      eapply (ngn_too_short _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 ps (pv bq alloc data eb sx ix) _ 1);
        [exact ST5 | exact FR5 | reflexivity | exact MI5 |].
      split; [exact G5|]. split; [apply PCAPR_closable_of; exact PC5|]. split; [exact AG5|]. split; [exact HH|]. split; [exact Hh|].
      split; [exact HD|]. split; [exact Hd| exact OF5].
    - (* [comment removed for export] *)
      replace (rem <? 8) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota. cbv beta. change (8 + 8)%Z with 16%Z. change (8 + 4)%Z with 12%Z.
      pose proof PC5 as (Afx & Hin & (Bx' & Ix' & jx' & padx & bsx' & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
      pose proof G5 as G5e. rewrite EPB in G5e.
      pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G5e ltac:(right; left; reflexivity)) as (K1 & K2 & K3 & K4 & K5 & K6).
      pose proof (PB_apart K _ _ _ _ _ _ _ _ _ _ G5 eq_refl) as [APB API].
      pose proof WF as (W1' & _ & W3 & W4 & _).
      unfold S3.F_ngnextA.TwB.pv, pcap_blocks, psize, is_ng in EPB, K1, K2, K3, K4, K5, K6, APB. cbn [pc_self pc_buffer pc_bufalloc pc_priv] in EPB, K1, K2, K3, K4, K5, K6, APB.
      unfold PCAP_NG_SF_TOTAL in APB.
      unfold S3.F_ngnextA.TwB.pv in W3, W4, W1'. cbn [pc_bufalloc pc_bufdata pc_snapshot] in W3, W4, W1'. unfold INT_MAX in W1'.
      assert (EBX : Bx' = Bq) by congruence. subst Bx'.
      unfold pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF, S3.F_ngnextA.TwB.pv in CELLS.
      cbn [app pc_bufsize pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_header pc_priv pk_next_ng pk_cleanup_ng PK] in CELLS.
      unfold S3.F_ngnextA.TwB.pv in BUF. cbn [pc_bufalloc] in BUF. cbn [pc_bufdata] in PFX.
      (* [comment removed for export] *)
      set (l0 := q8 data 8 0) in *. set (l1 := q8 data 8 1) in *. set (r0 := q8 data 10 0) in *. set (r1 := q8 data 10 1) in *.
      pose proof (q8_range data 8 0 DRNG ltac:(lia)) as Rl0. pose proof (q8_range data 8 1 DRNG ltac:(lia)) as Rl1.
      pose proof (q8_range data 10 0 DRNG ltac:(lia)) as Rr0. pose proof (q8_range data 10 1 DRNG ltac:(lia)) as Rr1.
      fold l0 in Rl0. fold l1 in Rl1. fold r0 in Rr0. fold r1 in Rr1.
      name_field data 12%Z n0 n1 n2 n3 DRNG.
      assert (LBS : length bsx' = Z.to_nat alloc) by (destruct BUF as [[WFB _] _]; cbn in WFB; lia).
      apply (rw_cells_split_CB usegs m5 _ [] (Z.to_nat alloc) _ [] [8; 2; 2; 4; Z.to_nat alloc - 16]%nat) in BUF; [| cbn; lia]. cbn [mk_CB_cells app] in BUF.
      rewrite !skipn_skipn in BUF. cbn [Nat.add] in BUF.
      rewrite (firstn2_q8 data bsx' 8 8 PFX eq_refl), (firstn2_q8 data bsx' 10 10 PFX eq_refl), (firstn4_q8 data bsx' 12 12 PFX eq_refl) in BUF by lia.
      fold l0 l1 r0 r1 n0 n1 n2 n3 in BUF.
      replace (firstn (Z.to_nat alloc - 16) (skipn 16 bsx')) with (skipn 16 bsx') in BUF by (symmetry; apply firstn_all2; rewrite length_skipn; lia).
      assert (BUF4 : rw_cells usegs m5 Bq [CB 8 (firstn 8 bsx'); C2 (Z_to_bv 64 (l0 + 256 * l1)); CB 2 [b8 r0; b8 r1]; C4 (Z_to_bv 64 (le4val n0 n1 n2 n3)); CB (Z.to_nat alloc - 16) (skipn 16 bsx')]).
      { eapply rw_cells_recell; [exact BUF | | ].
        { cbn. rewrite ?length_firstn, ?length_skipn. repeat split; try exact Logic.I; lia. }
        cbn [cells_bytes cbytes app]. rewrite (le2_lit l0 l1), (le4_lit n0 n1 n2 n3) by lia. reflexivity. }
      clear BUF.
      hide PRIV. hide IFS.
      (* [comment removed for export] *)
      step. step. step. step. if_false_by (geu_lits_false 8 (Bq + 16) ltac:(clear -K1; lia) ltac:(clear -K1 K3 K4 W4 LEN REM BR0; lia)).
      step. rewrite (sx32_small (Z.b2z swapped)) by (destruct swapped; cbn; lia).
      step. step. step.
      step. rewrite (and3_aligned (Bq + 8)) by (clear -K1 K2 K3 K4; try lia; Z.div_mod_to_equations; lia).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (AGF : agrees_on (fun a => outside [(bv_unsigned sp + -160 + 32, bv_unsigned sp + -160 + 48)]%Z a) m5 mm) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]);
        rename mm into m6 end.
      unhide FR5. unhide HH. unhide HD. unhide PRIV. unhide IFS. clear FR5.
      apply (agrees_rw_cells _ _ _ _ _ AGF) in HH; [| intros a Ha; rewrite Hh in Ha; cbn [outside]; clear - Ha R1; lia].
      apply (agrees_rw_cells _ _ _ _ _ AGF) in HD; [| intros a Ha; cbn [cells_size] in Ha; rewrite Hd in Ha; cbn [outside]; clear - Ha R1 R2; lia].
      apply (agrees_rw_cells _ _ _ _ _ AGF) in PRIV; [| intros a Ha; pose proof (priv_cells_psize _ _ _ _ _ PRIV) as PZ; unfold psize, is_ng, S3.F_ngnextA.TwB.pv, PCAP_PRIV_OFF, priv_cells in PZ, Ha; cbn [pc_priv] in PZ, Ha; unfold PCAP_NG_SF_TOTAL in PZ; cbn [outside]; gio_ceil_fact; clear -CLO__ Ha PZ LO BU SPW P4; lia].
      assert (G6 : GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m6).
      { eapply (GIo_pcap_frame K HFL SFL); [exact G5 | exact MU | exact WM |]. apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd]. unfold rc_lo, rc_spmain in *. clear - LO BU SPM; lia. }
      assert (PC6 : PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m6).
      { eapply PCAPR_agree; [exact AGF | | exact PC5]. intros a Ha. pose proof (in_PB_below K _ _ _ _ _ _ _ G5 Ha). cbn [outside]. gio_ceil_fact; clear -CLO__ H0 LO BU SPW; lia. }
      assert (IFS6 : ifaces_ok (pv bq alloc data eb sx ix) Ix' m6).
      { eapply ifaces_ok_agree; [exact AGF | | exact IFS]. intros sg q Hq a Ha. unfold S3.F_ngnextA.TwB.pv in Hq. cbn [pc_priv] in Hq. injection Hq as E1 E2. subst sg ix.
        destruct (API sx q eq_refl) as [X1 X2].
        pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G5e ltac:(right; right; left; reflexivity)) as (I1 & I2 & I3 & I4 & I5 & I6).
        cbn [outside]. gio_ceil_fact; clear -CLO__ Ha I1 I4 LO BU SPW. lia. }
      assert (AG6 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m6).
      { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [exact AGF|]. intros a [[Ha|Ha] _]; cbn [outside]; [clear - Ha; lia|].
        destruct (ngn_CLc_facts _ _ _ _ G5 Ha) as [Hc Hnb]. gio_ceil_fact; clear -CLO__ Hc LO BU SPW. lia. }
      clear MU WM AGF G5 PC5 AG5 IFS G5e.
      (* [comment removed for export] *)
      lazymatch goal with FRX : rw_cells usegs m6 (bv_unsigned sp + -160) (_ :: _ :: _ :: _ :: C8 (Z_to_bv 64 ?v1) :: C8 (Z_to_bv 64 ?v2) :: _) |- _ =>
        replace (Z_to_bv 64 v1) with (Z_to_bv 64 (Bq + 16)) in FRX by (f_equal; lia);
        replace (Z_to_bv 64 v2) with (Z_to_bv 64 (rem - 8)) in FRX by (f_equal; lia);
        assert (FR6 : rw_cells usegs m6 (bv_unsigned sp + -160) (S3.F_ngnextA.TwB.ngn_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 P HA DA dj [C8 (Z_to_bv 64 (Bq + 16)); C8 (Z_to_bv 64 (rem - 8)); C4 (Z_to_bv 64 bt); CB 4 cpad])) by exact FRX end.
      step. if_cases BRS; zify_cond BRS.
      + (* [comment removed for export] *)
        assert (SW : swapped = false) by (destruct swapped; [| reflexivity]; exfalso; revert BRS; rewrite ?unsigned_lit by (cbn; lia); cbn; lia).
        lazymatch goal with |- context [if swapped then ?X else ?Y] => replace (if swapped then X else Y) with Y by (rewrite SW; reflexivity) end.
        cbv zeta. change (pc_bufdata (pv bq alloc data eb sx ix)) with data.
        change (pc_linktype (pv bq alloc data eb sx ix)) with linktype. change (pc_snapshot (pv bq alloc data eb sx ix)) with snapshot.
        apply evt_done.
        eapply (ngn_idb_tail LOOP HLOOP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6 ps bq Bq Ix alloc rem data eb sx ix bt hcs dw dj cpad);
          [assumption | exact FR6 | assumption | exact G6 | exact PC6 | exact AG6 | exact HH | exact Hh | exact HD | exact Hd | exact DRNG
          | exact LEN | exact L30 | clear - BR0; lia | exact Hbt | exact OF5].
      + (* [comment removed for export] *)
        assert (SW : swapped = true) by (destruct swapped; [reflexivity|]; exfalso; revert BRS; rewrite ?unsigned_lit by (cbn; lia); cbn; lia).
        hide FR6. hide HH. hide HD. hide PRIV. step. if_false. unhide FR6. unhide HH. unhide HD. unhide PRIV.
        lazymatch goal with |- context [if swapped then ?X else ?Y] => replace (if swapped then X else Y) with X by (rewrite SW; reflexivity) end.
        cbv zeta.
        change (set_bufdata (swap_field 4 12 (swap_field 2 8 data)) (pv bq alloc data eb sx ix)) with (pv bq alloc (swap_field 4 12 (swap_field 2 8 data)) eb sx ix).
        rewrite (idb_swap_data' data) by lia. fold l0 l1 r0 r1 n0 n1 n2 n3.
        set (data' := firstn 8 data ++ [l1; l0; r0; r1; n3; n2; n1; n0] ++ skipn 16 data).
        change (pc_bufdata (pv bq alloc data' eb sx ix)) with data'.
        change (pc_linktype (pv bq alloc data' eb sx ix)) with linktype. change (pc_snapshot (pv bq alloc data' eb sx ix)) with snapshot.
        hide FR6. hide HH. hide HD. hide PRIV. hide CELLS.
        eapply evt_cut.
        { eapply (ngn_idb_swap _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6 l0 l1 n0 n1 n2 n3 Bq);
            [repeat (apply Forall_cons; [lia|]); apply Forall_nil | exact BUF4 | assumption | clear - K1; lia | clear - K4 W4 LEN REM BR0; lia]. }
        cbv beta. intros ms' (a1v & a0v & a3v & a4v & m7 & -> & MU7 & WM7 & MI7 & HB7 & E1 & E0).
        assert (AGP : agrees_on (fun a => outside [(Bq + 8, Bq + 16)]%Z a) m6 m7) by (eapply agrees_on_of_munch; [exact MU7 | exact WM7 | intros a _ Ho; exact Ho]).
        unhide FR6. unhide HH. unhide HD. unhide PRIV. unhide CELLS.
        lazymatch goal with STX : stk usegs m6 _ _ |- _ => pose proof (agrees_stk _ _ _ _ _ AGP STX ltac:(intros a Ha; cbn [outside]; gio_ceil_fact; clear -CLO__ Ha K4 LO BU SPW W4 LEN REM BR0; lia)) as ST7 end.
        apply (agrees_rw_cells _ _ _ _ _ AGP) in FR6; [| intros a Ha; unfold S3.F_ngnextA.TwB.ngn_frame in Ha; rewrite !cells_size_app in Ha; cbn [outside cells_size csize Nat.add] in Ha |- *; gio_ceil_fact; clear -CLO__ Ha K4 LO BU SPW W4 LEN REM BR0; lia].
        apply (agrees_rw_cells _ _ _ _ _ AGP) in HH; [| intros a Ha; rewrite Hh in Ha; cbn [outside]; gio_ceil_fact; clear -CLO__ Ha K4 LO BU SPW R1 W4 LEN REM BR0; lia].
        apply (agrees_rw_cells _ _ _ _ _ AGP) in HD; [| intros a Ha; cbn [cells_size] in Ha; rewrite Hd in Ha; cbn [outside]; gio_ceil_fact; clear -CLO__ Ha K4 LO BU SPW R1 R2 W4 LEN REM BR0; lia].
        assert (G7 : GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m7).
        { eapply (GIo_pcap_frame K HFL SFL); [exact G6 | exact MU7 | exact WM7 |]. apply Forall_cons; [| apply Forall_nil].
          right. unfold iv_in_block, pcap_blocks. apply Exists_cons_tl. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd pc_buffer pc_bufalloc S3.F_ngnextA.TwB.pv]. clear - W4 LEN REM BR0; lia. }
        (* [comment removed for export] *)
        assert (BUF7 : rw_cells usegs m7 Bq [CB (Z.to_nat alloc) (firstn 8 bsx' ++ [b8 l1; b8 l0; b8 r0; b8 r1; b8 n3; b8 n2; b8 n1; b8 n0] ++ skipn 16 bsx')]).
        { assert (R7 : rw_cells usegs m7 Bq [CB 8 (firstn 8 bsx'); C2 (Z_to_bv 64 (l1 + 256 * l0)); CB 2 [b8 r0; b8 r1]; C4 (Z_to_bv 64 (le4val n3 n2 n1 n0)); CB (Z.to_nat alloc - 16) (skipn 16 bsx')]).
          { eapply rw_cells_recell; [exact HB7 | | ].
            { cbn. rewrite ?length_firstn, ?length_skipn. repeat split; try exact Logic.I; lia. }
            cbn [cells_bytes cbytes app]. rewrite (le2_of_val a1v l1 l0 l1), (le4_word_mod32 a0v (le4val n3 n2 n1 n0) E0) by lia. rewrite (le2_lit l1 l0), (le4_lit n3 n2 n1 n0) by lia. reflexivity. }
          pose proof (rw_cells_merge usegs m7 Bq [] _ [] ltac:(rewrite app_nil_r; exact R7)) as R8.
          lazymatch type of R8 with rw_cells _ _ _ ([] ++ [CB ?n ?bs]) =>
            replace n with (Z.to_nat alloc) in R8 by (cbn [cells_size csize]; clear - W4 LEN REM BR0; lia);
            cbn [app cells_bytes cbytes] in R8 end.
          rewrite (le2_lit l1 l0), (le4_lit n3 n2 n1 n0), app_nil_r in R8 by lia. exact R8. }
        assert (LEN' : length data' = length data).
        { subst data'. change (skipn 16 data) with (skipn (8 + length [l1; l0; r0; r1; n3; n2; n1; n0]) data). apply splice_length. cbn [length]. clear - LEN REM BR0; lia. }
        assert (PFX7 : firstn (length data') (firstn 8 bsx' ++ [b8 l1; b8 l0; b8 r0; b8 r1; b8 n3; b8 n2; b8 n1; b8 n0] ++ skipn 16 bsx') = map b8 data').
        { subst data'. change ([b8 l1; b8 l0; b8 r0; b8 r1; b8 n3; b8 n2; b8 n1; b8 n0] ++ skipn 16 bsx') with (map b8 [l1; l0; r0; r1; n3; n2; n1; n0] ++ skipn (8 + length [l1; l0; r0; r1; n3; n2; n1; n0]) bsx').
          change ([l1; l0; r0; r1; n3; n2; n1; n0] ++ skipn 16 data) with ([l1; l0; r0; r1; n3; n2; n1; n0] ++ skipn (8 + length [l1; l0; r0; r1; n3; n2; n1; n0]) data).
          apply splice_pfx; [exact PFX | cbn [length]; clear - LEN REM BR0; lia | clear - LBS W4; lia]. }
        assert (HQ7 : forall a, (0 <= a < 2^64)%Z -> ~ (Bq <= a < Bq + alloc)%Z -> outside [(Bq + 8, Bq + 16)]%Z a) by (intros a _ Hn; cbn [outside]; clear - Hn W4 LEN REM BR0; lia).
        pose proof (PCAPR_bufdata ps bq Bq Ix alloc data data' eb sx ix m6 m7 _ _ G6 PC6 AGP HQ7 BUF7 PFX7 LEN') as PC7.
        assert (G7' : GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data' eb sx ix) P Bq Ix) FB m7) by exact G7.
        assert (AG7 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m7).
        { eapply agrees_on_trans; [exact AG6|]. eapply agrees_on_weaken; [exact AGP|]. intros a [[Ha|Ha] _]; cbn [outside]; [gio_ceil_fact; clear -CLO__ Ha K4 LO BU SPW W4 LEN REM BR0; lia|].
          destruct (ngn_CLc_facts _ _ _ _ G6 Ha) as [Hc Hnb]. split; [| exact Logic.I].
          intros Hr. apply Hnb. unfold pcap_blocks, in_block. apply Exists_cons_tl. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd pc_buffer pc_bufalloc S3.F_ngnextA.TwB.pv]. clear - Hr W4 LEN REM BR0; lia. }
        assert (DRNG' : Forall (fun x => 0 <= x < 256)%Z data').
        { subst data'. change (skipn 16 data) with (skipn (8 + length [l1; l0; r0; r1; n3; n2; n1; n0]) data). apply splice_Forall; [exact DRNG|].
          repeat (apply Forall_cons; [lia|]). apply Forall_nil. }
        apply evt_done.
        eapply (ngn_idb_tail LOOP HLOOP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m7 ps bq Bq Ix alloc rem data' eb sx ix bt hcs dw dj cpad);
          [exact ST7 | exact FR6 | exact MI7 | exact G7' | exact PC7 | exact AG7 | exact HH | exact Hh | exact HD | exact Hd | exact DRNG'
          | rewrite LEN'; exact LEN | exact L30 | clear - BR0; lia | exact Hbt | exact OF5].
  Qed.
  End Sz4.
  Lemma ngn_idb : ltac:(let t := eval cbv delta [ngn_idb__stmt] in ngn_idb__stmt in exact t).
  Proof using AD ADDIF ADJ AH ALN BU HFL HPL LO P1 P2 P4 P5 P6 R1 R2 SFL SNPRINTF SPM SPW TP W1 W9. intros LOOP HLOOP ra' t0' t1' t2' a0' a1' a2' a4' a5' a6' a7' x6 x7 t3' t4' t5' t6' m5 ps bq Bq Ix alloc rem data eb sx ix bt hcs dw dj cpad. ltac2:(SecDiet.SzSec.closeP 'ngn_idb__body "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NgnCtx.

End WithCeil.
End TwB.
End F_ngnextI.

(* [comment removed for export] *)
Module F_ngnextL.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep MonadX Image ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy GI. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_ngnextA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Startup_B__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_ngnextD__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.Pcap_iface_pp OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface_ng OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_small OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.PPFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.PP_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.NpArith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_chkD__S3.F_ngnextI.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia_e2w2_base := first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                                 | zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac ceil_mentioned := lazymatch goal with | |- context [@alloc_ceiling _] => idtac | _ : context [@alloc_ceiling _] |- _ => idtac end.
(* [comment removed for export] *)
Local Ltac gio_ceil_fact :=
  match goal with
  | G : GIo _ _ _ _ _ _ |- _ => let H := fresh "CLO__" in pose proof (PcapRep.GIo_ceil_lo _ _ _ _ _ _ G) as H; unfold rc_lo in H
  end.
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try gio_ceil_fact; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Close Scope bv_scope.
Section WithCeil.
Context {CEILV : CEIL}.
Lemma signed_lit_s32 : forall x, bv_signed (Z_to_bv 64 (s32 x)) = s32 x.
Proof using Type. pin_using tt.
  intros x. pose proof (s32_range x) as R. rewrite zb_signed, unsigned_lit_wrap.
  destruct (Z_lt_dec (s32 x) 0).
  - replace ((s32 x) mod 2^64) with (s32 x + 2^64) by (Z.div_mod_to_equations; lia).
    replace (s32 x + 2 ^ 64 <? 2 ^ 63) with false by (symmetry; apply Z.ltb_ge; lia). lia.
  - rewrite Z.mod_small by lia. replace (s32 x <? 2 ^ 63) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.
Lemma s32_cases : forall x, 0 <= x < 2^32 -> (x < 2^31 /\ s32 x = x) \/ (2^31 <= x /\ s32 x = x - 2^32).
Proof using Type. pin_using tt. intros x Hx. unfold s32. destruct (Z_lt_dec x (2^31)); [left | right]; split; try lia; Z.div_mod_to_equations; lia. Qed.
End WithCeil.

Local Open Scope bv_scope.
Section WithCeil.
Context {CEILV : CEIL}.
Section NgnCtx.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HPL : heap_perm_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis SNPRINTF : snprintf_spec_stmt K.
  Hypothesis PP : post_process_stmt.
  Hypothesis ADJ : adjust_snapshot_stmt.
  Hypothesis RBLK : read_block_stmt HO K sites.
  Hypothesis ADDIF : add_interface_stmt HO K sites.

  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (R : rctx) (CLc FB : list (cblock (hptr:=hptr))) (lo P HA DA Af : Z) (m : mem) (o : option hptr).
  Variables (self f : hptr) (bufsize : Z) (swapped : bool) (vmaj vmin snapshot linktype ltext prec brk : Z) (header : pkthdr).
  Hypothesis LO : (usp0 R - 8388608 <= lo)%Z.
  Hypothesis BU : (lo + 81920 <= bv_unsigned sp)%Z.
  Hypothesis SPM : (bv_unsigned sp <= rc_spmain R)%Z.
  Hypothesis TP : tp = rc_tp R.
  Hypothesis ALN : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis SITES : sites = sites_at (bv_unsigned sp + D_NEXT_PACKET).
  Hypothesis R1 : (bv_unsigned sp <= HA)%Z.
  Hypothesis R2 : (HA + 24 <= DA)%Z.
  Hypothesis R3 : (DA + 8 <= rc_spmain R)%Z.
  Hypothesis AH : (HA mod 8 = 0)%Z.
  Hypothesis AD : (DA mod 8 = 0)%Z.
  Hypothesis SPW : (140735340871680 <= usp0 R)%Z.
  Hypothesis SP47 : (usp0 R <= 2^47)%Z.
  Hypothesis HinF : In (f, Af, FILE_BLOCK) FB.
  Hypothesis P1 : (0 < P)%Z.  Hypothesis P2 : (P mod 16 = 0)%Z.  Hypothesis P4 : (P + 680 <= CEILZ)%Z.
  Hypothesis P5 : (P + 680 <= 65536 \/ 348160 <= P)%Z.  Hypothesis P6 : (P + 680 <= utp R - 200 \/ utp R - 200 + 4096 <= P)%Z.
  Hypothesis A1 : (0 < Af)%Z.  Hypothesis A4 : (Af + 1264 <= CEILZ)%Z.
  Hypothesis W1 : (1 <= snapshot <= INT_MAX)%Z.  Hypothesis W2 : (0 <= bufsize <= 2^30)%Z.
  Hypothesis W5 : brk = 0%Z.  Hypothesis W6 : prec = 0%Z.
  Hypothesis W7 : (0 <= vmaj < 2^16)%Z.  Hypothesis W8 : (0 <= vmin < 2^16)%Z.
  Hypothesis W9 : (0 <= linktype < 2^31)%Z.  Hypothesis W10 : (-2^31 <= ltext < 2^31)%Z.

  Let POSTQ := next_packet_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o.

  (* [comment removed for export] *)
  #[local] Abbreviation pv := (F_ngnextA.pv self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header).
  #[local] Abbreviation ngn_frame := (F_ngnextA.ngn_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 P HA DA).
  #[local] Abbreviation ngn_final := (F_ngnextA.ngn_final K sp R CLc FB P HA DA m o).
  #[local] Abbreviation ngn_finalC := (F_ngnextA.ngn_finalC K sp R CLc FB P HA DA m o).
  #[local] Abbreviation ngn_final_C := (F_ngnextA.ngn_final_C K sp R CLc FB P HA DA m o).
  #[local] Abbreviation ngn_ret_m1 := (F_ngnextA.ngn_ret_m1 K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o BU).
  #[local] Abbreviation ngn_ret_0 := (F_ngnextA.ngn_ret_0 K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o BU).
  #[local] Abbreviation ngn_ret_1 := (F_ngnextA.ngn_ret_1 K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o BU).
  #[local] Abbreviation ngn_CLc_facts := (F_ngnextA.ngn_CLc_facts K R CLc FB).
  #[local] Abbreviation ngn_snp_call := (F_ngnextA.ngn_snp_call K HFL SFL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU SPM TP ALN R1 R2 AH AD SPW P1 P4 P5).
  #[local] Abbreviation ngn_snp := (F_ngnextA.ngn_snp K HFL SFL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU SPM TP ALN R1 R2 AH AD SPW P1 P4 P5).
  #[local] Abbreviation ngn_mcp := (F_ngnextA.ngn_mcp K HFL SFL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU ALN R1 R2 AH AD SPW P1 P4 P5 P6).
  #[local] Abbreviation PCAPRC_errbuf := (F_ngnextA.PCAPRC_errbuf K sp R lo P HA DA LO BU ALN R1 R2 AH AD SPW P1).

  Ltac norm_g :=
    unfold F_ngnextA.pv; unfold pcap_blocks; unfold psize; unfold is_ng;
    cbn [pc_self pc_rfile pc_bufsize pc_bufalloc pc_buffer pc_bufdata pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype
         pc_linktype_ext pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_priv priv_cells ng_of ng_ifaces_ptr_of
         set_bufdata set_errbuf set_buffer set_ng set_priv];
    unfold PCAP_NG_SF_TOTAL, PCAP_PRIV_OFF.
  Ltac norm_p :=
    unfold F_ngnextA.pv in *; unfold pcap_blocks in *; unfold psize in *; unfold is_ng in *;
    cbn [pc_self pc_rfile pc_bufsize pc_bufalloc pc_buffer pc_bufdata pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype
         pc_linktype_ext pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_priv priv_cells ng_of ng_ifaces_ptr_of
         set_bufdata set_errbuf set_buffer set_ng set_priv] in *;
    unfold PCAP_NG_SF_TOTAL, PCAP_PRIV_OFF in *.

  #[local] Abbreviation ngn_pp := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB.ngn_pp K HFL SFL PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPM R1 R2 R3 AH AD SPW SP47 P1 P2 P4 P5 P6 W1 W2 W5 W6 W7 W8 W9 W10).

  #[local] Abbreviation ngn_found := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.ngn_found K HFL SFL SNPRINTF PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPM TP ALN R1 R2 R3 AH AD SPW SP47 P1 P2 P4 P5 P6 W1 W2 W5 W6 W7 W8 W9 W10).
  #[local] Abbreviation ccells := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.ccells).
  #[local] Abbreviation ngn_spb := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.ngn_spb K HFL SFL SNPRINTF PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPM TP ALN R1 R2 R3 AH AD SPW SP47 P1 P2 P4 P5 P6 W1 W2 W5 W6 W7 W8 W9 W10).
  #[local] Abbreviation ngn_epb := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.ngn_epb K HFL SFL SNPRINTF PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPM TP ALN R1 R2 R3 AH AD SPW SP47 P1 P2 P4 P5 P6 W1 W2 W5 W6 W7 W8 W9 W10).
  #[local] Abbreviation ngn_pb := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.ngn_pb K HFL SFL SNPRINTF PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPM TP ALN R1 R2 R3 AH AD SPW SP47 P1 P2 P4 P5 P6 W1 W2 W5 W6 W7 W8 W9 W10).


  #[local] Abbreviation pcapT := (pcap hptr hptr).
  #[local] Abbreviation MR := (M (PState H hptr) ((Z + ng_found) * pcap hptr hptr)).

  #[local] Abbreviation ngn_KF := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_KF (H:=H) (hptr:=hptr)).
  #[local] Abbreviation ngn_shbK := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_shbK (H:=H) (hptr:=hptr)).
  #[local] Abbreviation ngn_idbK := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_idbK HO sites).
  #[local] Abbreviation ngn_blkK := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_blkK HO sites).
  #[local] Abbreviation ngn_body := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_body HO sites).
  #[local] Abbreviation ngn_head := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_head K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA Af m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header).
  #[local] Abbreviation ngn_too_short := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_too_short K HFL SFL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU SPM TP ALN R1 R2 AH AD SPW P1 P4 P5).
  #[local] Abbreviation PCAPR_bufdata := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.PCAPR_bufdata K sp R CLc FB lo P HA DA self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU ALN R1 R2 AH AD SPW P1 P5).
  #[local] Abbreviation get_le16_q8' := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.get_le16_q8').
  #[local] Abbreviation firstn2_q8 := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.firstn2_q8 sp R lo P HA DA LO BU R1 R2 SPW P1).
  #[local] Abbreviation bswap16_2 := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.bswap16_2 sp P HA DA).

  Ltac name_field data off a b c d DRNG :=
    set (a := q8 data off 0%Z) in *; set (b := q8 data off 1%Z) in *; set (c := q8 data off 2%Z) in *; set (d := q8 data off 3%Z) in *;
    let Ra := fresh "R" a in let Rb := fresh "R" b in let Rc := fresh "R" c in let Rd := fresh "R" d in
    pose proof (q8_range data off 0%Z DRNG ltac:(lia)) as Ra; pose proof (q8_range data off 1%Z DRNG ltac:(lia)) as Rb;
    pose proof (q8_range data off 2%Z DRNG ltac:(lia)) as Rc; pose proof (q8_range data off 3%Z DRNG ltac:(lia)) as Rd;
    fold a in Ra; fold b in Rb; fold c in Rc; fold d in Rd.

  #[local] Abbreviation ngn_snp90 := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextS.ngn_snp90 K HFL SFL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU SPM TP ALN R1 R2 AH AD SPW P1 P4 P5).
  #[local] Abbreviation ngn_snp8c := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextS.ngn_snp8c K HFL SFL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU SPM TP ALN R1 R2 AH AD SPW P1 P4 P5).

  #[local] Abbreviation ngn_shb := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextS.ngn_shb K HFL SFL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA Af m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPM TP ALN R1 R2 AH AD SPW P1 P2 P4 P5 P6).
  #[local] Abbreviation ngn_idb := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_chkD__S3.F_ngnextI.ngn_idb HO K sites HFL SFL HPL SNPRINTF ADJ ADDIF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA Af m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPM TP ALN R1 R2 AH AD SPW P1 P2 P4 P5 P6 W1 W9).
  #[local] Abbreviation ngn_epb_full := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_epb_full K HFL SFL SNPRINTF PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPM TP ALN R1 R2 R3 AH AD SPW SP47 P1 P2 P4 P5 P6 W1 W2 W5 W6 W7 W8 W9 W10).
  #[local] Abbreviation ngn_spb_full := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_spb_full K HFL SFL SNPRINTF PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPM TP ALN R1 R2 R3 AH AD SPW SP47 P1 P2 P4 P5 P6 W1 W2 W5 W6 W7 W8 W9 W10).
  #[local] Abbreviation ngn_pb_full := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_pb_full K HFL SFL SNPRINTF PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPM TP ALN R1 R2 R3 AH AD SPW SP47 P1 P2 P4 P5 P6 W1 W2 W5 W6 W7 W8 W9 W10).

  Ltac decide_eqb :=
    repeat (match goal with
            | |- context [Z.eqb ?x ?k] => fastfirst (first [ replace (Z.eqb x k) with false by (symmetry; apply Z.eqb_neq; lia)
                                                | replace (Z.eqb x k) with true by (symmetry; apply Z.eqb_eq; lia) ])
            end; cbv iota).

  (* [comment removed for export] *)
  Definition ngn_dispatch__stmt : Prop := forall (LOOP : pcapT -> MR),
    ngn_head (fun p' ps' ms' => implM ssegs (mbind (LOOP p') ngn_KF) ps' POSTQ ms') ->
    forall (t0' t1' t2' x0 a1' a2' a3' a4' a5' a6' a7' x6 x10 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (bq : hptr) (Bq Ix alloc rem : Z) (data eb : list Z) (sx : pcap_ng_sf) (ix : option hptr) (bt : Z) (hcs : list cell) (dw : cell) (dj : list byte) (cpad : list byte),
      stk ssegs m5 lo (bv_unsigned sp + -160) ->
      rw_cells ssegs m5 (bv_unsigned sp + -160) (ngn_frame dj (ccells Bq rem bt cpad)) -> mem_inv ssegs m5 ->
      GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells ssegs m5 HA hcs -> cells_size hcs = 24%nat -> rw_cells ssegs m5 DA [dw] -> csize dw = 8%nat ->
      Forall (fun x => 0 <= x < 256)%Z data -> (Z.of_nat (length data) = rem + 12)%Z -> (rem + 12 <= 2^30)%Z -> (0 <= rem)%Z ->
      (0 <= bt < 2^32)%Z -> ps_outfile ps = o ->
      implM ssegs (mbind (ngn_blkK LOOP (mkCursor 8 rem bt) (pv bq alloc data eb sx ix)) ngn_KF) ps POSTQ
        (MS (mkR (Z_to_bv 64 0x17480) (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' x0 (Z_to_bv 64 (P + 216))
                 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 65280) (Z_to_bv 64 168627466) (Z_to_bv 64 P) (Z_to_bv 64 Af) x6 (Z_to_bv 64 439041101) (Z_to_bv 64 2) (Z_to_bv 64 1) x10 (Z_to_bv 64 15)
                 t3' t4' t5' t6') F (Z_to_bv 64 0x17480) fc None m5 (seg_rom ssegs)).
  Section Sz3.
  Variables LOOP t0' t1' t2' x0 a1' a2' a3' a4' a5' a6' a7' x6 x10 t3' t4' t5' t6' m5 ps bq Bq Ix alloc rem data eb sx ix bt hcs dw dj cpad : ltac2:(SecDiet.SzSec.tyM 'ngn_dispatch__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @LOOP).
  Lemma ngn_dispatch__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_dispatch__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AD ADDIF ADJ AH ALN BU HFL HPL LO P1 P2 P4 P5 P6 PP R1 R2 R3 SFL SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9. pin_using (fun (AD ADDIF ADJ AH ALN BU HFL HPL LO P1 P2 P4 P5 P6 PP R1 R2 R3 SFL SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 : unit) => tt).
    intros HLOOP ST5 FR5 MI5 G5 PC5 AG5 HH Hh HD Hd DRNG LEN L30 REM Hbt OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof (ngn_shb LOOP HLOOP) as SHB. pose proof (ngn_idb LOOP HLOOP) as IDB.
    unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_blkK. cbn [cur_block_type]. unfold BT_EPB, BT_SPB, BT_PB, BT_IDB, BT_SHB.
    pose proof (s32_cases bt Hbt) as SC.
    pose proof FR5 as FRJ. unfold F_ngnextA.ngn_frame, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.ccells in FRJ. cbn [app] in FRJ.
    hide FR5. hide HH. hide HD.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl ssegs m5) as WM.
    unfold implM. iprefix.
    step. step. if_cases B1; zify_cond B1. { exfalso. rewrite ?unsigned_lit in B1 by lia. clear - B1. lia. }
    step. if_cases B2; zify_cond B2. { exfalso. rewrite ?unsigned_lit in B2 by lia. clear - B2. lia. }
    step. rewrite (sx32_s32 bt) by lia.
    step. if_cases B3; zify_cond B3; rewrite ?signed_lit_s32 in B3.
    - (* [comment removed for export] *)
      step. if_cases B4; zify_cond B4; rewrite ?unsigned_lit_wrap in B4.
      + (* [comment removed for export] *)
        step. if_cases B5; zify_cond B5; rewrite ?unsigned_lit_wrap in B5.
        * (* [comment removed for export] *)
          assert (NB : (bt <> 1 /\ bt <> 2 /\ bt <> 3 /\ bt <> 6 /\ bt <> 168627466)%Z).
          { destruct SC as [[LT E]|[GE E]]; rewrite E in B3, B4, B5; [rewrite Z.mod_small in B4, B5 by lia; lia|].
            clear - GE Hbt. lia. }
          decide_eqb.
          unhide FR5. unhide HH. unhide HD. apply evt_done.
          unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_head in HLOOP. unfold NGN_LOOP in HLOOP.
          eapply HLOOP; [exact ST5 | exact FR5 | reflexivity | exact MI5 | exact G5 | exact PC5 | exact AG5 | exact HH | exact Hh | exact HD | exact Hd | exact OF5].
        * (* [comment removed for export] *)
          assert (EB : (bt = 2)%Z) by (destruct SC as [[LT E]|[GE E]]; rewrite E in B5; [rewrite Z.mod_small in B5 by lia; lia| exfalso; clear - GE Hbt B5; Z.div_mod_to_equations; lia]).
          decide_eqb.
          unhide FR5. unhide HH. unhide HD. apply evt_done.
          eapply ngn_pb_full; [exact ST5 | exact FR5 | exact MI5 | exact G5 | exact PC5 | exact AG5 | exact HH | exact Hh | exact HD | exact Hd | exact DRNG | exact LEN | exact L30 | exact REM | exact Hbt | exact OF5].
      + (* [comment removed for export] *)
        assert (EB : (bt = 1)%Z) by (destruct SC as [[LT E]|[GE E]]; rewrite E in B4; [rewrite Z.mod_small in B4 by lia; lia| exfalso; clear - GE Hbt B4; Z.div_mod_to_equations; lia]).
        decide_eqb.
        unhide FR5. unhide HH. unhide HD. apply evt_done.
        eapply IDB; [exact ST5 | exact FR5 | exact MI5 | exact G5 | exact PC5 | exact AG5 | exact HH | exact Hh | exact HD | exact Hd | exact DRNG | exact LEN | exact L30 | exact REM | exact Hbt | exact OF5].
    - (* [comment removed for export] *)
      assert (LT31 : (bt < 2^31 /\ s32 bt = bt)%Z) by (destruct SC as [[LT E]|[GE E]]; [split; [exact LT| exact E]| exfalso; rewrite E in B3; clear - GE Hbt B3; lia]).
      destruct LT31 as [LT31 E32]. rewrite E32 in B3.
      step. if_cases B6; zify_cond B6; rewrite ?E32, ?unsigned_lit in B6 by lia.
      + (* [comment removed for export] *)
        step. step. if_cases B7; zify_cond B7; rewrite ?E32, ?unsigned_lit in B7 by lia.
        * (* [comment removed for export] *)
          decide_eqb.
          unhide FR5. unhide HH. unhide HD. apply evt_done.
          eapply ngn_spb_full; [exact ST5 | exact FR5 | exact MI5 | exact G5 | exact PC5 | exact AG5 | exact HH | exact Hh | exact HD | exact Hd | exact DRNG | exact LEN | exact L30 | exact REM | exact Hbt | exact OF5].
        * step. step. if_cases B8; zify_cond B8; rewrite ?E32, ?unsigned_lit in B8 by lia.
          -- (* [comment removed for export] *)
             decide_eqb.
             unhide FR5. unhide HH. unhide HD. apply evt_done.
             unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_head in HLOOP. unfold NGN_LOOP in HLOOP.
             eapply HLOOP; [exact ST5 | exact FR5 | reflexivity | exact MI5 | exact G5 | exact PC5 | exact AG5 | exact HH | exact Hh | exact HD | exact Hd | exact OF5].
          -- (* [comment removed for export] *)
             decide_eqb. step.
             unhide FR5. unhide HH. unhide HD. apply evt_done.
             eapply ngn_epb_full; [exact ST5 | exact FR5 | exact MI5 | exact G5 | exact PC5 | exact AG5 | exact HH | exact Hh | exact HD | exact Hd | exact DRNG | exact LEN | exact L30 | exact REM | exact Hbt | exact OF5].
      + (* [comment removed for export] *)
        decide_eqb.
        unhide FR5. unhide HH. unhide HD. apply evt_done.
        eapply SHB; [exact ST5 | exact FR5 | exact MI5 | exact G5 | exact PC5 | exact AG5 | exact HH | exact Hh | exact HD | exact Hd | exact DRNG | exact LEN | exact L30 | exact REM | exact Hbt | exact OF5].
  Qed.
  End Sz3.
  Lemma ngn_dispatch : ltac:(let t := eval cbv delta [ngn_dispatch__stmt] in ngn_dispatch__stmt in exact t).
  Proof using AD ADDIF ADJ AH ALN BU HFL HPL LO P1 P2 P4 P5 P6 PP R1 R2 R3 SFL SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9. intros LOOP HLOOP t0' t1' t2' x0 a1' a2' a3' a4' a5' a6' a7' x6 x10 t3' t4' t5' t6' m5 ps bq Bq Ix alloc rem data eb sx ix bt hcs dw dj cpad. ltac2:(SecDiet.SzSec.closeP 'ngn_dispatch__body "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
  (* [comment removed for export] *)
  Definition ngn_loop_S__stmt : Prop := forall (LOOP : pcapT -> MR),
    ngn_head (fun p' ps' ms' => implM ssegs (mbind (LOOP p') ngn_KF) ps' POSTQ ms') ->
    ngn_head (fun p' ps' ms' => implM ssegs (mbind (mbind (read_block MOps (prims HO fo_nop sites) (DStack SiteBhdrNextPacket 0) p') (ngn_body LOOP)) ngn_KF) ps' POSTQ ms').
  Section Sz4.
  Variables LOOP ra' t0' t1' t2' x0 a0' a1' a2' a3' a4' a5' a6' a7' x6 x10 t3' t4' t5' t6' m5 ps bq Bq Ix alloc data eb sx ix hcs dw dj ccs : ltac2:(SecDiet.SzSec.tyM 'ngn_loop_S__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @LOOP).
  Lemma ngn_loop_S__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_loop_S__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AD ADDIF ADJ AH ALN BU HFL HPL HinF LO P1 P2 P4 P5 P6 PP R1 R2 R3 RBLK SFL SITES SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9. pin_using (fun (AD ADDIF ADJ AH ALN BU HFL HPL HinF LO P1 P2 P4 P5 P6 PP R1 R2 R3 RBLK SFL SITES SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 : unit) => tt).
    intros HLOOP ST5 FR5 Hccs MI5 G5 PC5 AG5 HH Hh HD Hd OF5.
 unfold NGN_LOOP.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof PC5 as (Afx & Hin & (Bx' & Ix' & jx' & padx & bsx' & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    pose proof G5 as G5e. rewrite EPB in G5e.
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G5e ltac:(right; left; reflexivity)) as (K1 & K2 & K3 & K4 & K5 & K6).
    pose proof (PB_apart K _ _ _ _ _ _ _ _ _ _ G5 eq_refl) as [APB API].
    pose proof WF as (W1' & W2' & W3 & W4 & W5' & W6' & W7' & W8' & W9' & W10' & W11 & W12 & W13 & W14).
    unfold F_ngnextA.pv, pcap_blocks, psize, is_ng in EPB, K1, K2, K3, K4, K5, K6, APB. cbn [pc_self pc_buffer pc_bufalloc pc_priv] in EPB, K1, K2, K3, K4, K5, K6, APB.
    unfold PCAP_NG_SF_TOTAL in APB.
    unfold F_ngnextA.pv in W3, W4, W13, W14. cbn [pc_bufalloc pc_bufdata pc_priv pc_bufsize] in W3, W4, W13, W14.
    assert (EBX : Bx' = Bq) by congruence. subst Bx'.
    unfold F_ngnextA.pv in Hin. cbn [pc_rfile] in Hin.
    unfold F_ngnextA.pv in BUF. cbn [pc_bufalloc] in BUF. cbn [pc_bufdata] in PFX.
    pose proof PRIV as NG. unfold priv_cells, F_ngnextA.pv, PCAP_PRIV_OFF in NG. cbn [pc_priv] in NG. unfold ng_cells in NG.
    assert (NPB : forall a, in_block CLc a -> (a < alloc_ceiling)%Z /\ ~ (P <= a < P + 680)%Z /\ ~ (Bq <= a < Bq + alloc)%Z).
    { intros a Ha. destruct (ngn_CLc_facts _ _ _ _ G5 Ha) as [Hc Hnb]. split; [clear - Hc; lia|]. split; intros Hr; apply Hnb; unfold pcap_blocks, in_block.
      - apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. unfold psize, is_ng, F_ngnextA.pv. cbn [pc_priv]. unfold PCAP_NG_SF_TOTAL. clear - Hr; lia.
      - apply Exists_cons_tl. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd pc_buffer pc_bufalloc F_ngnextA.pv]. clear - Hr; lia. }
    assert (INP : forall a, (P <= a < P + 680)%Z -> client_keeps ((CLc ++ [(self, P, PCAP_NG_SF_TOTAL)]) ++ IBLK ix Ix' sx) (bv_unsigned sp + -160) a).
    { intros a Ha. right. apply in_block_app. left. apply in_block_app. right. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. unfold PCAP_NG_SF_TOTAL. exact Ha. }
    (* [comment removed for export] *)
    apply pcap_cells_split4 in CELLS as (PRE & CE & HDR & OPS); [|reflexivity].
    apply (rw_cells_split_CB ssegs m5 _ [] 304 _ [] [256; 48]%nat) in CE; [|reflexivity]. cbn [mk_CB_cells app] in CE.
    destruct (rw_cells_cut _ _ _ 1 CE) as [CE1 CE2]. clear CE. cbn [firstn skipn cells_size csize Nat.add] in CE1, CE2.
    replace (P + 216 + Z.of_nat 256)%Z with (P + 472)%Z in CE2 by lia.
    unfold pc_pre in PRE.
    destruct (rw_cells_cut _ _ _ 3 PRE) as [PRE0 PRE3]. destruct (rw_cells_cut _ _ _ 2 PRE3) as [P20 PRE5].
    destruct (rw_cells_cut _ _ _ 2 PRE5) as [P32 PRE7]. destruct (rw_cells_cut _ _ _ 2 PRE7) as [P48 PRE9]. clear PRE PRE3 PRE5 PRE7.
    cbn [firstn skipn cells_size csize Nat.add app] in PRE0, P20, P32, P48, PRE9.
    replace (P + Z.of_nat 20)%Z with (P + 20)%Z in P20 by lia. replace (P + Z.of_nat 20 + Z.of_nat 12)%Z with (P + 32)%Z in P32 by lia.
    replace (P + Z.of_nat 20 + Z.of_nat 12 + Z.of_nat 16)%Z with (P + 48)%Z in P48 by lia.
    replace (P + Z.of_nat 20 + Z.of_nat 12 + Z.of_nat 16 + Z.of_nat 12)%Z with (P + 60)%Z in PRE9 by lia.
    destruct (rw_cells_cut _ _ _ 1 NG) as [NG0 NG1]. destruct (rw_cells_cut _ _ _ 1 NG1) as [NG656 NGR]. clear NG NG1.
    cbn [firstn skipn cells_size csize Nat.add app] in NG0, NG656, NGR.
    replace (P + 648 + Z.of_nat 8)%Z with (P + 656)%Z in NG656 by lia. replace (P + 648 + Z.of_nat 8 + Z.of_nat 4)%Z with (P + 660)%Z in NGR by lia.
    (* [comment removed for export] *)
    pose proof FR5 as FRJ. unfold F_ngnextA.ngn_frame in FRJ.
    destruct (proj1 (rw_cells_app ssegs m5 _ _ _) FRJ) as [F0 F4]. destruct (proj1 (rw_cells_app ssegs m5 _ _ _) F4) as [FCUR FS]. clear FRJ F4.
    cbn [cells_size csize Nat.add] in FCUR, FS. rewrite Hccs in FS.
    replace (bv_unsigned sp + -160 + Z.of_nat 32)%Z with (bv_unsigned sp + -128)%Z in FCUR, FS by lia.
    replace (bv_unsigned sp + -128 + Z.of_nat 24)%Z with (bv_unsigned sp + -104)%Z in FS by lia.
    hide F0. hide FCUR. hide FS. hide PRE0. hide P20. hide P32. hide P48. hide PRE9. hide CE1. hide CE2. hide HDR. hide OPS. hide NG0. hide NG656. hide NGR. hide BUF. hide HH. hide HD. hide FR5. hide PRIV. hide IFS.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl ssegs m5) as WM.
    apply (implM_bind_assoc ssegs). unfold implM. iprefix. step. step. step. step. step. clear MU WM.
    unhide F0. unhide FCUR. unhide FS. unhide PRE0. unhide P20. unhide P32. unhide P48. unhide PRE9. unhide CE1. unhide CE2. unhide HDR. unhide OPS. unhide NG0. unhide NG656. unhide NGR. unhide BUF. unhide HH. unhide HD. unhide FR5. unhide PRIV. unhide IFS.
    apply evt_done. name_sp sp (-160)%Z. eapply (implM_bind ssegs).
    { eapply (RBLK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 R ps (CLc ++ [(self, P, PCAP_NG_SF_TOTAL)]) (IBLK ix Ix' sx) FB f Af P Bq (bv_unsigned sp + -128)%Z (P + 216)%Z lo
                (pv bq alloc data eb sx ix) sx ix (DStack SiteBhdrNextPacket 0) bsx' (firstn 256 (pj_g jx')) ccs);
        [ split; [rewrite <- app_assoc; cbn [app]; pose proof G5e as GX; unfold pcap_blocks, F_ngnextA.pv, psize, is_ng in GX; cbn [pc_self pc_buffer pc_bufalloc pc_priv] in GX; unfold IBLK; exact GX |];
          split; [rewrite Hsp; exact ST5|]; split; [unfold rc_lo; lia|]; split; [unfold READ_BLOCK_STACK, PCAP_L1_STACK; rewrite Hsp; lia|];
          split; [rewrite Hsp; unfold rc_spmain in *; lia|]; split; [exact MI5|]; split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]
        | exact HinF | reflexivity | reflexivity
        | apply in_or_app; left; apply in_or_app; right; left; reflexivity
        | intros st'; cbn [eval_rdest fo_site fo_nop]; rewrite SITES; unfold sites_at, D_NEXT_PACKET; rewrite Hsp; lia
        | reflexivity | reflexivity | f_equal; lia | reflexivity
        | split; [exact P20|]; split; [exact P48|]; split; [exact NG656|]; cbn [pc_bufsize pc_bufalloc F_ngnextA.pv]; clear - W2 W13 W3 W14; lia
        | exact BUF | exact PFX | cbn [pc_bufdata pc_bufalloc F_ngnextA.pv]; exact W4
        | exact FCUR | exact Hccs | rewrite Hsp; lia | unfold rc_spmain in *; lia | replace (bv_unsigned sp + -128)%Z with (bv_unsigned sp + (-128))%Z by lia; apply aligned16_8; [exact ALN| reflexivity]
        | exact CE1 | right; reflexivity | apply aligned16_8; [exact P2| reflexivity] ]. }
    intros rb st' ms' PO.
    destruct PO as (a0v & m6 & p' & B' & bs' & E & OF6 & MI6 & ST6 & AG6 & G6 & BH6 & BUF6 & PFX6 & LEN6 & PRIVE & RFE & SELFE & BSZE & SWE & META & RM).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 0x17480)) with (Z_to_bv 64 0x17480) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    destruct p' as [self' f' bsz' alloc' bq' data' sw' vmaj' vmin' snap' lt' lte' prec' brk' eb' hdr' priv'].
    cbn [pc_priv pc_rfile pc_self pc_bufsize pc_swapped F_ngnextA.pv] in PRIVE, RFE, SELFE, BSZE, SWE.
    unfold same_meta in META. cbn [pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_break_loop pc_errbuf pc_header F_ngnextA.pv] in META.
    destruct META as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9). subst priv' f' self' bsz' sw' vmaj' vmin' snap' lt' lte' prec' brk' eb' hdr'.
    change ({| pc_self := self; pc_rfile := f; pc_bufsize := bufsize; pc_bufalloc := alloc'; pc_buffer := bq'; pc_bufdata := data'; pc_swapped := swapped;
               pc_version_major := vmaj; pc_version_minor := vmin; pc_snapshot := snapshot; pc_linktype := linktype; pc_linktype_ext := ltext;
               pc_tstamp_precision := prec; pc_break_loop := brk; pc_errbuf := eb; pc_header := header; pc_priv := PrivNg sx ix |})
      with (pv bq' alloc' data' eb sx ix) in *.
    cbn [pc_buffer pc_bufalloc pc_bufdata F_ngnextA.pv] in G6, BUF6, PFX6, LEN6, RM.
    destruct BH6 as (P20' & P48' & NG656' & BR1 & BR2 & BR3 & BR4). cbn [pc_bufsize pc_swapped pc_bufalloc F_ngnextA.pv] in P20', P48', BR1, BR3, BR4.
    assert (OF7 : ps_outfile st' = o) by (rewrite OF6; exact OF5).
    (* [comment removed for export] *)
    transport F0 m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [left; clear - Ha; lia| gio_ceil_fact; clear -CLO__ Ha LO BU SPW P4 RSP; lia]).
    transport FS m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [left; clear - Ha; lia| gio_ceil_fact; clear -CLO__ Ha LO BU SPW P4 RSP; lia]).
    transport HH m6 AG6 ltac:(intros a Ha; rewrite Hh in Ha; split; [left; clear - Ha R1; lia| gio_ceil_fact; clear -CLO__ Ha R1 LO BU SPW P4; lia]).
    transport HD m6 AG6 ltac:(intros a Ha; cbn [cells_size] in Ha; rewrite Hd in Ha; split; [left; clear - Ha R1 R2; lia| gio_ceil_fact; clear -CLO__ Ha R1 R2 LO BU SPW P4; lia]).
    transport PRE0 m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [apply INP; clear - Ha; lia| gio_ceil_fact; clear -CLO__ Ha LO BU SPW P4; lia]).
    transport P32 m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [apply INP; clear - Ha; lia| gio_ceil_fact; clear -CLO__ Ha LO BU SPW P4; lia]).
    transport PRE9 m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [apply INP; clear - Ha; lia| gio_ceil_fact; clear -CLO__ Ha LO BU SPW P4; lia]).
    transport CE2 m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [apply INP; clear - Ha; lia| gio_ceil_fact; clear -CLO__ Ha LO BU SPW P4; lia]).
    transport HDR m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add hdr_cells pc_header F_ngnextA.pv] in Ha; split; [apply INP; clear - Ha; lia| gio_ceil_fact; clear -CLO__ Ha LO BU SPW P4; lia]).
    transport OPS m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add pc_ops] in Ha; split; [apply INP; clear - Ha; lia| gio_ceil_fact; clear -CLO__ Ha LO BU SPW P4; lia]).
    transport NG0 m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [apply INP; clear - Ha; lia| gio_ceil_fact; clear -CLO__ Ha LO BU SPW P4; lia]).
    transport NGR m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [apply INP; clear - Ha; lia| gio_ceil_fact; clear -CLO__ Ha LO BU SPW P4; lia]).
    assert (IFS6 : ifaces_ok (pv bq' alloc' data' eb sx ix) Ix' m6).
    { eapply ifaces_ok_agree; [exact AG6 | | exact IFS]. intros sg q Hq a Ha. unfold F_ngnextA.pv in Hq. cbn [pc_priv] in Hq. injection Hq as E1 E2. subst sg ix.
      destruct (API sx q eq_refl) as [X1 X2]. unfold psize, is_ng, F_ngnextA.pv in X1. cbn [pc_priv] in X1. unfold PCAP_NG_SF_TOTAL in X1.
      pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G5e ltac:(right; right; left; reflexivity)) as (I1 & I2 & I3 & I4 & I5 & I6).
      assert (EI : Ix = Ix') by congruence.
      split; [right; apply in_block_app; right; unfold IBLK, in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; exact Ha|].
      gio_ceil_fact; clear -CLO__ Ha X1 I1 I4 EI LO BU SPW. lia. }
    pose proof (rw_cells_uncut _ _ _ _ _ PRE0 P20' ltac:(cbn; lia)) as PREa. pose proof (rw_cells_uncut _ _ _ _ _ PREa P32 ltac:(cbn; lia)) as PREb.
    pose proof (rw_cells_uncut _ _ _ _ _ PREb P48' ltac:(cbn; lia)) as PREc. pose proof (rw_cells_uncut _ _ _ _ _ PREc PRE9 ltac:(cbn; lia)) as PRE.
    clear PREa PREb PREc PRE0 P20' P32 P48' PRE9 P20 P48. cbn [app] in PRE.
    pose proof (rw_cells_uncut _ _ _ _ _ NG0 NG656' ltac:(cbn; lia)) as NGa. pose proof (rw_cells_uncut _ _ _ _ _ NGa NGR ltac:(cbn; lia)) as NG6.
    clear NGa NG0 NG656' NGR NG656. cbn [app] in NG6.
    assert (AG7 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m6).
    { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [exact AG6|]. intros a [[Ha|Ha] _].
      - split; [left; clear - Ha; lia| gio_ceil_fact; clear -CLO__ Ha LO BU SPW P4; lia].
      - destruct (NPB a Ha) as (Hc & Hn1 & Hn2). split; [right; apply in_block_app; left; apply in_block_app; left; exact Ha| gio_ceil_fact; clear -CLO__ Hc Hn1 Hn2 LO BU SPW; lia]. }
    assert (G6' : GIo K R st' (CLc ++ pcap_blocks (pv bq' alloc' data' eb sx ix) P B' Ix') FB m6).
    { eapply (GIo_perm K HPL); [exact G6|]. unfold pcap_blocks, F_ngnextA.pv, psize, is_ng. cbn [pc_self pc_buffer pc_bufalloc pc_priv]. unfold IBLK.
      change (CLc ++ (self, P, PCAP_NG_SF_TOTAL) :: (bq', B', alloc') :: match ix with Some q => [(q, Ix', (40 * ng_ifaces_size sx)%Z)] | None => [] end)
        with (CLc ++ [(self, P, PCAP_NG_SF_TOTAL)] ++ (bq', B', alloc') :: match ix with Some q => [(q, Ix', (40 * ng_ifaces_size sx)%Z)] | None => [] end).
      rewrite (app_assoc CLc). apply Permutation.Permutation_cons_app. apply Permutation.Permutation_refl. }
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G6' ltac:(right; left; reflexivity)) as (K1' & K2' & K3' & K4' & K5' & K6').
    assert (WF' : pcap_wf (pv bq' alloc' data' eb sx ix)).
    { unfold pcap_wf, F_ngnextA.pv in WF |- *.
      cbn [pc_snapshot pc_bufsize pc_bufalloc pc_bufdata pc_break_loop pc_tstamp_precision pc_version_major pc_version_minor pc_linktype pc_linktype_ext pc_header pc_priv] in WF |- *.
      clear - WF BR3 BR4 LEN6. lia. }
    assert (JOIN : forall cs, rw_cells ssegs m6 (P + 216) cs -> cells_size cs = 304%nat ->
              rw_cells ssegs m6 P (pcap_cells_gen (pv bq' alloc' data' eb sx ix) P B' (C8 (Z_to_bv 64 Afx)) (C8 (Z_to_bv 64 (pk_stats PK))) (C8 (Z_to_bv 64 (pk_oneshot PK))) (set_pj_g (cells_bytes cs) jx'))).
    { intros cs HCS Hcs.
      exact (pcap_cells_join4 _ P (pv bq' alloc' data' eb sx ix) B' (C8 (Z_to_bv 64 Afx)) (C8 (Z_to_bv 64 (pk_stats PK))) (C8 (Z_to_bv 64 (pk_oneshot PK))) jx' cs header eq_refl PRE HCS Hcs HDR OPS). }
    (* [comment removed for export] *)
    assert (FIN : forall cs ccs', rw_cells ssegs m6 (P + 216) cs -> cells_size cs = 304%nat ->
              rw_cells ssegs m6 (bv_unsigned sp + -128) ccs' -> cells_size ccs' = 24%nat ->
              rw_cells ssegs m6 (bv_unsigned sp + -160) (F_ngnextA.ngn_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 P HA DA dj ccs')
              /\ ngn_final m6 st' (pcap_blocks (pv bq' alloc' data' eb sx ix) P B' Ix') (pv bq' alloc' data' eb sx ix) hcs dw).
    { intros cs ccs' HCS Hcs HCUR' Hccs'.
      split. { unfold F_ngnextA.ngn_frame. eapply (rw_cells_uncut _ _ _ _ _ F0); [eapply (rw_cells_uncut _ _ _ _ _ HCUR' FS); rewrite Hccs'; cbn; lia | cbn; lia]. }
      split; [exact G6'|]. split.
      { exists Afx. split; [exact Hin|]. eexists B', Ix', _, padx, bs'.
        split; [reflexivity|]. split; [exact (JOIN cs HCS Hcs)|]. split; [exact NG6|]. split; [exact BUF6|]. split; [exact PFX6|]. split; [exact IFS6| exact WF']. }
      split; [exact AG7|]. split; [exact HH|]. split; [exact Hh|]. split; [exact HD|]. split; [exact Hd| exact OF7]. }
    cbv beta. unfold implM. iprefix.
    destruct rb as [p'' | msg p'' | c p''].
    - (* [comment removed for export] *)
      destruct RM as (-> & -> & HEB6 & (ccs' & HCUR6 & Hccs')).
      pose proof (rw_cells_uncut _ _ _ _ _ HEB6 CE2 ltac:(cbn; lia)) as CE6.
      destruct (FIN _ _ CE6 eq_refl HCUR6 Hccs') as [FR6 FIN6].
      hide FR6. hide FIN6. hide HH. hide HD. hide CE6. hide HEB6. hide CE2. hide HDR. hide OPS. hide PRE. hide NG6. hide BUF6. hide HCUR6. hide F0. hide FS. hide CE1. hide PRIV.
      pose proof (munch_refl ([] : list (Z * Z)) m6) as MU. pose proof (wmono_refl ssegs m6) as WM.
      step. step. if_cases B1; zify_cond B1. { exfalso. rewrite ?unsigned_lit in B1 by lia. clear - B1. lia. }
      step. if_cases B2; zify_cond B2; [| exfalso; rewrite ?unsigned_lit in B2 by lia; clear - B2; lia].
      step. step.
      unhide FR6. unhide FIN6. apply evt_done. cbn [OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_body]. apply implM_retb. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_KF. unfold NGN_EPILOGUE.
      eapply ngn_ret_0; [exact ST6 | exact FR6 | exact Hccs' | exact MI6 | exact FIN6].
    - (* [comment removed for export] *)
      destruct RM as (-> & -> & (junk6 & HEB6) & LENM & MOK & (ccs' & HCUR6 & Hccs')).
      pose proof (rw_cells_uncut _ _ _ _ _ HEB6 CE2 ltac:(cbn [cells_size csize]; clear - LENM; lia)) as CE6. cbn [app] in CE6.
      destruct (FIN _ _ CE6 ltac:(cbn [cells_size csize]; clear - LENM; lia) HCUR6 Hccs') as [FR6 FIN6].
      hide FR6. hide FIN6. hide HH. hide HD. hide CE6. hide HEB6. hide CE2. hide HDR. hide OPS. hide PRE. hide NG6. hide BUF6. hide HCUR6. hide F0. hide FS. hide CE1. hide PRIV.
      pose proof (munch_refl ([] : list (Z * Z)) m6) as MU. pose proof (wmono_refl ssegs m6) as WM.
      step. step. if_cases B1; zify_cond B1; [| exfalso; rewrite ?unsigned_lit in B1 by lia; clear - B1; lia].
      unhide FR6. unhide FIN6. apply evt_done. cbn [OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_body]. apply implM_retb. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_KF. unfold NGN_EPILOGUE.
      eapply ngn_ret_m1; [exact ST6 | exact FR6 | exact Hccs' | exact MI6 |].
      destruct FIN6 as (G7 & PC7 & REST). split; [exact G7|]. split; [| exact REST].
      apply PCAPR_closable_of in PC7. destruct PC7 as (Afy & Hiny & (By & Iy & jy & pady & bsy & EPBy & CEy & PRy & BUFy & PFXy & IFCy & WFy)).
      exists Afy. split; [exact Hiny|]. exists By, Iy, jy, pady, bsy.
      split; [exact EPBy|]. split; [exact CEy|]. split; [exact PRy|]. split; [exact BUFy|]. split; [exact PFXy|]. split; [| exact WFy].
      unfold ifaces_closable, F_ngnextA.pv in IFCy |- *. cbn [pc_priv set_errbuf] in IFCy |- *. exact IFCy.
    - (* [comment removed for export] *)
      destruct RM as (-> & -> & HEB6 & (cpad & HCUR6) & COFF & CR0 & CR1 & CR2 & CBT & LEND & GRD).
      destruct c as [coff crem cbt]. cbn [cur_off cur_remaining cur_block_type] in COFF, CR0, CR1, CR2, CBT, LEND, HCUR6. subst coff.
      pose proof (rw_cells_uncut _ _ _ _ _ HEB6 CE2 ltac:(cbn; lia)) as CE6.
      destruct (FIN _ _ CE6 eq_refl HCUR6 eq_refl) as [FR6 FIN6]. destruct FIN6 as (_ & PC6 & _).
      apply evt_done. cbn [OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_body].
      eapply (ngn_dispatch LOOP HLOOP); [exact ST6 | exact FR6 | exact MI6 | exact G6' | exact PC6 | exact AG7 | exact HH | exact Hh | exact HD | exact Hd | exact GRD | exact LEND | exact CR2 | exact CR0 | exact CBT | exact OF7].
  Qed.
  End Sz4.
  Lemma ngn_loop_S : ltac:(let t := eval cbv delta [ngn_loop_S__stmt] in ngn_loop_S__stmt in exact t).
  Proof using AD ADDIF ADJ AH ALN BU HFL HPL HinF LO P1 P2 P4 P5 P6 PP R1 R2 R3 RBLK SFL SITES SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9. intros LOOP HLOOP ra' t0' t1' t2' x0 a0' a1' a2' a3' a4' a5' a6' a7' x6 x10 t3' t4' t5' t6' m5 ps bq Bq Ix alloc data eb sx ix hcs dw dj ccs. ltac2:(SecDiet.SzSec.closeP 'ngn_loop_S__body "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Lemma ngn_loop : forall fuel, ngn_head (fun p' ps' ms' => implM ssegs (mbind (ng_scan_blocks MOps (prims HO fo_nop sites) fuel p') ngn_KF) ps' POSTQ ms').
  Proof using AD ADDIF ADJ AH ALN BU HFL HPL HinF LO P1 P2 P4 P5 P6 PP R1 R2 R3 RBLK SFL SITES SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9. pin_using (fun (AD ADDIF ADJ AH ALN BU HFL HPL HinF LO P1 P2 P4 P5 P6 PP R1 R2 R3 RBLK SFL SITES SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 : unit) => tt).
    induction fuel as [|fuel IH].
    - unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_head. intros. cbn [ng_scan_blocks].
      eapply (implM_bind ssegs _ _ _ (fun _ _ _ => False)); [apply implM_unr | intros a s' ms' X; exact (False_rect _ X)].
    - unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_head. intros. rewrite ng_scan_blocks_S.
      revert H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11. apply (ngn_loop_S _ IH).
  Qed.
End NgnCtx.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3 Require NgnPure.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MonadX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.NpArith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.PPFacts.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.Pcap_iface_pp.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface_ng.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_small.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.PP_kit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3.NgnPure. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_chkD__S3.F_ngnextI.TwB.
Import OSSVerify.libpcap.fuzz_pcap.images.Ubsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Ceiling.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia_e2w2_base := first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                                 | zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac ceil_mentioned := lazymatch goal with | |- context [@alloc_ceiling _] => idtac | _ : context [@alloc_ceiling _] |- _ => idtac end.
(* [comment removed for export] *)
Local Ltac gio_ceil_fact :=
  match goal with
  | G : GIo _ _ _ _ _ _ |- _ => let H := fresh "CLO__" in pose proof (S3.PcapRep.TwB.GIo_ceil_lo _ _ _ _ _ _ G) as H; unfold rc_lo in H
  end.
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try gio_ceil_fact; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section WithCeil.
Context {CEILV : CEIL}.
Section NgnCtx.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HPL : heap_perm_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis SNPRINTF : snprintf_spec_stmt K.
  Hypothesis PP : post_process_stmt.
  Hypothesis ADJ : adjust_snapshot_stmt.
  Hypothesis RBLK : read_block_stmt HO K sites.
  Hypothesis ADDIF : add_interface_stmt HO K sites.

  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (R : rctx) (CLc FB : list (cblock (hptr:=hptr))) (lo P HA DA Af : Z) (m : mem) (o : option hptr).
  Variables (self f : hptr) (bufsize : Z) (swapped : bool) (vmaj vmin snapshot linktype ltext prec brk : Z) (header : pkthdr).
  Hypothesis LO : (usp0 R - 8388608 <= lo)%Z.
  Hypothesis BU : (lo + 81920 <= bv_unsigned sp)%Z.
  Hypothesis SPM : (bv_unsigned sp <= rc_spmain R)%Z.
  Hypothesis TP : tp = rc_tp R.
  Hypothesis ALN : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis SITES : sites = sites_at (bv_unsigned sp + D_NEXT_PACKET).
  Hypothesis R1 : (bv_unsigned sp <= HA)%Z.
  Hypothesis R2 : (HA + 24 <= DA)%Z.
  Hypothesis R3 : (DA + 8 <= rc_spmain R)%Z.
  Hypothesis AH : (HA mod 8 = 0)%Z.
  Hypothesis AD : (DA mod 8 = 0)%Z.
  Hypothesis SPW : (140735340871680 <= usp0 R)%Z.
  Hypothesis SP47 : (usp0 R <= 2^47)%Z.
  Hypothesis HinF : In (f, Af, FILE_BLOCK) FB.
  Hypothesis P1 : (0 < P)%Z.  Hypothesis P2 : (P mod 16 = 0)%Z.  Hypothesis P4 : (P + 680 <= CEILZ)%Z.
  Hypothesis P5 : (P + 680 <= 65536 \/ 352256 <= P)%Z.  Hypothesis P6 : (P + 680 <= utp R - 200 \/ utp R - 200 + 4096 <= P)%Z.
  Hypothesis A1 : (0 < Af)%Z.  Hypothesis A4 : (Af + 1264 <= CEILZ)%Z.
  Hypothesis W1 : (1 <= snapshot <= INT_MAX)%Z.  Hypothesis W2 : (0 <= bufsize <= 2^30)%Z.
  Hypothesis W5 : brk = 0%Z.  Hypothesis W6 : prec = 0%Z.
  Hypothesis W7 : (0 <= vmaj < 2^16)%Z.  Hypothesis W8 : (0 <= vmin < 2^16)%Z.
  Hypothesis W9 : (0 <= linktype < 2^31)%Z.  Hypothesis W10 : (-2^31 <= ltext < 2^31)%Z.

  Let POSTQ := next_packet_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o.

  (* [comment removed for export] *)
  #[local] Abbreviation pv := (S3.F_ngnextA.TwB.pv self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header).
  #[local] Abbreviation ngn_frame := (S3.F_ngnextA.TwB.ngn_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 P HA DA).
  #[local] Abbreviation ngn_final := (S3.F_ngnextA.TwB.ngn_final K sp R CLc FB P HA DA m o).
  #[local] Abbreviation ngn_finalC := (S3.F_ngnextA.TwB.ngn_finalC K sp R CLc FB P HA DA m o).
  #[local] Abbreviation ngn_final_C := (S3.F_ngnextA.TwB.ngn_final_C K sp R CLc FB P HA DA m o).
  #[local] Abbreviation ngn_ret_m1 := (S3.F_ngnextA.TwB.ngn_ret_m1 K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o BU).
  #[local] Abbreviation ngn_ret_0 := (S3.F_ngnextA.TwB.ngn_ret_0 K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o BU).
  #[local] Abbreviation ngn_ret_1 := (S3.F_ngnextA.TwB.ngn_ret_1 K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o BU).
  #[local] Abbreviation ngn_CLc_facts := (S3.F_ngnextA.TwB.ngn_CLc_facts K R CLc FB).
  #[local] Abbreviation ngn_snp_call := (S3.F_ngnextA.TwB.ngn_snp_call K HFL SFL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU SPM TP ALN R1 R2 AH AD SPW P1 P4 P5).
  #[local] Abbreviation ngn_snp := (S3.F_ngnextA.TwB.ngn_snp K HFL SFL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU SPM TP ALN R1 R2 AH AD SPW P1 P4 P5).
  #[local] Abbreviation ngn_mcp := (S3.F_ngnextA.TwB.ngn_mcp K HFL SFL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU ALN R1 R2 AH AD SPW P1 P4 P5 P6).
  #[local] Abbreviation PCAPRC_errbuf := (S3.F_ngnextA.TwB.PCAPRC_errbuf K sp R lo P HA DA LO BU ALN R1 R2 AH AD SPW P1).

  Ltac norm_g :=
    unfold S3.F_ngnextA.TwB.pv; unfold pcap_blocks; unfold psize; unfold is_ng;
    cbn [pc_self pc_rfile pc_bufsize pc_bufalloc pc_buffer pc_bufdata pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype
         pc_linktype_ext pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_priv priv_cells ng_of ng_ifaces_ptr_of
         set_bufdata set_errbuf set_buffer set_ng set_priv];
    unfold PCAP_NG_SF_TOTAL, PCAP_PRIV_OFF.
  Ltac norm_p :=
    unfold S3.F_ngnextA.TwB.pv in *; unfold pcap_blocks in *; unfold psize in *; unfold is_ng in *;
    cbn [pc_self pc_rfile pc_bufsize pc_bufalloc pc_buffer pc_bufdata pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype
         pc_linktype_ext pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_priv priv_cells ng_of ng_ifaces_ptr_of
         set_bufdata set_errbuf set_buffer set_ng set_priv] in *;
    unfold PCAP_NG_SF_TOTAL, PCAP_PRIV_OFF in *.

  #[local] Abbreviation ngn_pp := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB.TwB.ngn_pp K HFL SFL PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPM R1 R2 R3 AH AD SPW SP47 P1 P2 P4 P5 P6 W1 W2 W5 W6 W7 W8 W9 W10).

  #[local] Abbreviation ngn_found := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.TwB.ngn_found K HFL SFL SNPRINTF PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPM TP ALN R1 R2 R3 AH AD SPW SP47 P1 P2 P4 P5 P6 W1 W2 W5 W6 W7 W8 W9 W10).
  #[local] Abbreviation ccells := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.TwB.ccells ).
  #[local] Abbreviation ngn_spb := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.TwB.ngn_spb K HFL SFL SNPRINTF PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPM TP ALN R1 R2 R3 AH AD SPW SP47 P1 P2 P4 P5 P6 W1 W2 W5 W6 W7 W8 W9 W10).
  #[local] Abbreviation ngn_epb := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.TwB.ngn_epb K HFL SFL SNPRINTF PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPM TP ALN R1 R2 R3 AH AD SPW SP47 P1 P2 P4 P5 P6 W1 W2 W5 W6 W7 W8 W9 W10).
  #[local] Abbreviation ngn_pb := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.TwB.ngn_pb K HFL SFL SNPRINTF PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPM TP ALN R1 R2 R3 AH AD SPW SP47 P1 P2 P4 P5 P6 W1 W2 W5 W6 W7 W8 W9 W10).


  #[local] Abbreviation pcapT := (pcap hptr hptr).
  #[local] Abbreviation MR := (M (PState H hptr) ((Z + ng_found) * pcap hptr hptr)).

  #[local] Abbreviation ngn_KF := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.TwB.ngn_KF (H:=H) (hptr:=hptr)).
  #[local] Abbreviation ngn_shbK := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.TwB.ngn_shbK (H:=H) (hptr:=hptr)).
  #[local] Abbreviation ngn_idbK := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.TwB.ngn_idbK HO sites).
  #[local] Abbreviation ngn_blkK := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.TwB.ngn_blkK HO sites).
  #[local] Abbreviation ngn_body := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.TwB.ngn_body HO sites).
  #[local] Abbreviation ngn_head := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.TwB.ngn_head K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA Af m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header).
  #[local] Abbreviation ngn_too_short := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.TwB.ngn_too_short K HFL SFL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU SPM TP ALN R1 R2 AH AD SPW P1 P4 P5).
  #[local] Abbreviation PCAPR_bufdata := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.TwB.PCAPR_bufdata K sp R CLc FB lo P HA DA self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU ALN R1 R2 AH AD SPW P1 P5).
  #[local] Abbreviation get_le16_q8' := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.TwB.get_le16_q8' ).
  #[local] Abbreviation firstn2_q8 := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.TwB.firstn2_q8 sp R lo P HA DA LO BU R1 R2 SPW P1).
  #[local] Abbreviation bswap16_2 := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.TwB.bswap16_2 sp P HA DA).

  Ltac name_field data off a b c d DRNG :=
    set (a := q8 data off 0%Z) in *; set (b := q8 data off 1%Z) in *; set (c := q8 data off 2%Z) in *; set (d := q8 data off 3%Z) in *;
    let Ra := fresh "R" a in let Rb := fresh "R" b in let Rc := fresh "R" c in let Rd := fresh "R" d in
    pose proof (q8_range data off 0%Z DRNG ltac:(lia)) as Ra; pose proof (q8_range data off 1%Z DRNG ltac:(lia)) as Rb;
    pose proof (q8_range data off 2%Z DRNG ltac:(lia)) as Rc; pose proof (q8_range data off 3%Z DRNG ltac:(lia)) as Rd;
    fold a in Ra; fold b in Rb; fold c in Rc; fold d in Rd.

  #[local] Abbreviation ngn_snp90 := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextS.TwB.ngn_snp90 K HFL SFL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU SPM TP ALN R1 R2 AH AD SPW P1 P4 P5).
  #[local] Abbreviation ngn_snp8c := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextS.TwB.ngn_snp8c K HFL SFL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o LO BU SPM TP ALN R1 R2 AH AD SPW P1 P4 P5).

  #[local] Abbreviation ngn_shb := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextS.TwB.ngn_shb K HFL SFL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA Af m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPM TP ALN R1 R2 AH AD SPW P1 P2 P4 P5 P6).
  #[local] Abbreviation ngn_idb := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_chkD__S3.F_ngnextI.TwB.ngn_idb HO K sites HFL SFL HPL SNPRINTF ADJ ADDIF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA Af m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPM TP ALN R1 R2 AH AD SPW P1 P2 P4 P5 P6 W1 W9).
  #[local] Abbreviation ngn_epb_full := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.TwB.ngn_epb_full K HFL SFL SNPRINTF PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPM TP ALN R1 R2 R3 AH AD SPW SP47 P1 P2 P4 P5 P6 W1 W2 W5 W6 W7 W8 W9 W10).
  #[local] Abbreviation ngn_spb_full := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.TwB.ngn_spb_full K HFL SFL SNPRINTF PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPM TP ALN R1 R2 R3 AH AD SPW SP47 P1 P2 P4 P5 P6 W1 W2 W5 W6 W7 W8 W9 W10).
  #[local] Abbreviation ngn_pb_full := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.TwB.ngn_pb_full K HFL SFL SNPRINTF PP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPM TP ALN R1 R2 R3 AH AD SPW SP47 P1 P2 P4 P5 P6 W1 W2 W5 W6 W7 W8 W9 W10).

  Ltac decide_eqb :=
    repeat (match goal with
            | |- context [Z.eqb ?x ?k] => fastfirst (first [ replace (Z.eqb x k) with false by (symmetry; apply Z.eqb_neq; lia)
                                                | replace (Z.eqb x k) with true by (symmetry; apply Z.eqb_eq; lia) ])
            end; cbv iota).

  (* [comment removed for export] *)
  Definition ngn_dispatch__stmt : Prop := forall (LOOP : pcapT -> MR),
    ngn_head (fun p' ps' ms' => implM usegs (mbind (LOOP p') ngn_KF) ps' POSTQ ms') ->
    forall (t0' t1' t2' x0 a1' a2' a3' a4' a5' a6' a7' x6 x7 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (bq : hptr) (Bq Ix alloc rem : Z) (data eb : list Z) (sx : pcap_ng_sf) (ix : option hptr) (bt : Z) (hcs : list cell) (dw : cell) (dj : list byte) (cpad : list byte),
      stk usegs m5 lo (bv_unsigned sp + -160) ->
      rw_cells usegs m5 (bv_unsigned sp + -160) (ngn_frame dj (ccells Bq rem bt cpad)) -> mem_inv usegs m5 ->
      GIo K R ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells usegs m5 HA hcs -> cells_size hcs = 24%nat -> rw_cells usegs m5 DA [dw] -> csize dw = 8%nat ->
      Forall (fun x => 0 <= x < 256)%Z data -> (Z.of_nat (length data) = rem + 12)%Z -> (rem + 12 <= 2^30)%Z -> (0 <= rem)%Z ->
      (0 <= bt < 2^32)%Z -> ps_outfile ps = o ->
      implM usegs (mbind (ngn_blkK LOOP (mkCursor 8 rem bt) (pv bq alloc data eb sx ix)) ngn_KF) ps POSTQ
        (MS (mkR (Z_to_bv 64 0x17aac) (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' x0 (Z_to_bv 64 (P + 216))
                 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 0) (Z_to_bv 64 P) (Z_to_bv 64 65280) (Z_to_bv 64 Af) x6 x7 (Z_to_bv 64 439041101) (Z_to_bv 64 2) (Z_to_bv 64 1) (Z_to_bv 64 168627466)
                 t3' t4' t5' t6') F (Z_to_bv 64 0x17aac) fc None m5 (seg_rom usegs)).
  Section Sz1.
  Variables LOOP t0' t1' t2' x0 a1' a2' a3' a4' a5' a6' a7' x6 x7 t3' t4' t5' t6' m5 ps bq Bq Ix alloc rem data eb sx ix bt hcs dw dj cpad : ltac2:(SecDiet.SzSec.tyM 'ngn_dispatch__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @LOOP).
  Lemma ngn_dispatch__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_dispatch__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AD ADDIF ADJ AH ALN BU HFL HPL LO P1 P2 P4 P5 P6 PP R1 R2 R3 SFL SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9. pin_using (fun (AD ADDIF ADJ AH ALN BU HFL HPL LO P1 P2 P4 P5 P6 PP R1 R2 R3 SFL SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 : unit) => tt).
    intros HLOOP.
 intros ST5 FR5 MI5 G5 PC5 AG5 HH Hh HD Hd DRNG LEN L30 REM Hbt OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof (ngn_shb LOOP HLOOP) as SHB. pose proof (ngn_idb LOOP HLOOP) as IDB.
    unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.TwB.ngn_blkK. cbn [cur_block_type]. unfold BT_EPB, BT_SPB, BT_PB, BT_IDB, BT_SHB.
    pose proof (s32_cases bt Hbt) as SC.
    pose proof FR5 as FRJ. unfold S3.F_ngnextA.TwB.ngn_frame, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.TwB.ccells in FRJ. cbn [app] in FRJ.
    hide FR5. hide HH. hide HD.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl usegs m5) as WM.
    unfold implM. iprefix.
    step. step. if_cases B1; zify_cond B1. { exfalso. rewrite ?unsigned_lit in B1 by lia. clear - B1. lia. }
    step. if_cases B2; zify_cond B2. { exfalso. rewrite ?unsigned_lit in B2 by lia. clear - B2. lia. }
    step. rewrite (sx32_s32 bt) by lia.
    step. if_cases B3; zify_cond B3; rewrite ?signed_lit_s32 in B3.
    - (* [comment removed for export] *)
      step. if_cases B4; zify_cond B4; rewrite ?unsigned_lit_wrap in B4.
      + (* [comment removed for export] *)
        step. if_cases B5; zify_cond B5; rewrite ?unsigned_lit_wrap in B5.
        * (* [comment removed for export] *)
          assert (NB : (bt <> 1 /\ bt <> 2 /\ bt <> 3 /\ bt <> 6 /\ bt <> 168627466)%Z).
          { destruct SC as [[LT E]|[GE E]]; rewrite E in B3, B4, B5; [rewrite Z.mod_small in B4, B5 by lia; lia|].
            clear - GE Hbt. lia. }
          decide_eqb.
          unhide FR5. unhide HH. unhide HD. apply evt_done.
          unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.TwB.ngn_head in HLOOP. unfold NGN_LOOP in HLOOP.
          eapply HLOOP; [exact ST5 | exact FR5 | reflexivity | exact MI5 | exact G5 | exact PC5 | exact AG5 | exact HH | exact Hh | exact HD | exact Hd | exact OF5].
        * (* [comment removed for export] *)
          assert (EB : (bt = 2)%Z) by (destruct SC as [[LT E]|[GE E]]; rewrite E in B5; [rewrite Z.mod_small in B5 by lia; lia| exfalso; clear - GE Hbt B5; Z.div_mod_to_equations; lia]).
          decide_eqb. step.
          unhide FR5. unhide HH. unhide HD. apply evt_done.
          eapply ngn_pb_full; [exact ST5 | exact FR5 | exact MI5 | exact G5 | exact PC5 | exact AG5 | exact HH | exact Hh | exact HD | exact Hd | exact DRNG | exact LEN | exact L30 | exact REM | exact Hbt | exact OF5].
      + (* [comment removed for export] *)
        assert (EB : (bt = 1)%Z) by (destruct SC as [[LT E]|[GE E]]; rewrite E in B4; [rewrite Z.mod_small in B4 by lia; lia| exfalso; clear - GE Hbt B4; Z.div_mod_to_equations; lia]).
        decide_eqb.
        unhide FR5. unhide HH. unhide HD. apply evt_done.
        eapply IDB; [exact ST5 | exact FR5 | exact MI5 | exact G5 | exact PC5 | exact AG5 | exact HH | exact Hh | exact HD | exact Hd | exact DRNG | exact LEN | exact L30 | exact REM | exact Hbt | exact OF5].
    - (* [comment removed for export] *)
      assert (LT31 : (bt < 2^31 /\ s32 bt = bt)%Z) by (destruct SC as [[LT E]|[GE E]]; [split; [exact LT| exact E]| exfalso; rewrite E in B3; clear - GE Hbt B3; lia]).
      destruct LT31 as [LT31 E32]. rewrite E32 in B3.
      step. if_cases B6; zify_cond B6; rewrite ?E32, ?unsigned_lit in B6 by lia.
      + (* [comment removed for export] *)
        step. step. if_cases B7; zify_cond B7; rewrite ?E32, ?unsigned_lit in B7 by lia.
        * (* [comment removed for export] *)
          decide_eqb.
          unhide FR5. unhide HH. unhide HD. apply evt_done.
          eapply ngn_spb_full; [exact ST5 | exact FR5 | exact MI5 | exact G5 | exact PC5 | exact AG5 | exact HH | exact Hh | exact HD | exact Hd | exact DRNG | exact LEN | exact L30 | exact REM | exact Hbt | exact OF5].
        * step. step. if_cases B8; zify_cond B8; rewrite ?E32, ?unsigned_lit in B8 by lia.
          -- (* [comment removed for export] *)
             decide_eqb.
             unhide FR5. unhide HH. unhide HD. apply evt_done.
             unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.TwB.ngn_head in HLOOP. unfold NGN_LOOP in HLOOP.
             eapply HLOOP; [exact ST5 | exact FR5 | reflexivity | exact MI5 | exact G5 | exact PC5 | exact AG5 | exact HH | exact Hh | exact HD | exact Hd | exact OF5].
          -- (* [comment removed for export] *)
             decide_eqb. step.
             unhide FR5. unhide HH. unhide HD. apply evt_done.
             eapply ngn_epb_full; [exact ST5 | exact FR5 | exact MI5 | exact G5 | exact PC5 | exact AG5 | exact HH | exact Hh | exact HD | exact Hd | exact DRNG | exact LEN | exact L30 | exact REM | exact Hbt | exact OF5].
      + (* [comment removed for export] *)
        decide_eqb.
        unhide FR5. unhide HH. unhide HD. apply evt_done.
        eapply SHB; [exact ST5 | exact FR5 | exact MI5 | exact G5 | exact PC5 | exact AG5 | exact HH | exact Hh | exact HD | exact Hd | exact DRNG | exact LEN | exact L30 | exact REM | exact Hbt | exact OF5].
  Qed.
  End Sz1.
  Lemma ngn_dispatch : ltac:(let t := eval cbv delta [ngn_dispatch__stmt] in ngn_dispatch__stmt in exact t).
  Proof using AD ADDIF ADJ AH ALN BU HFL HPL LO P1 P2 P4 P5 P6 PP R1 R2 R3 SFL SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9. intros LOOP HLOOP t0' t1' t2' x0 a1' a2' a3' a4' a5' a6' a7' x6 x7 t3' t4' t5' t6' m5 ps bq Bq Ix alloc rem data eb sx ix bt hcs dw dj cpad. ltac2:(SecDiet.SzSec.closeP 'ngn_dispatch__body "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
  (* [comment removed for export] *)
  Definition ngn_loop_S__stmt : Prop := forall (LOOP : pcapT -> MR),
    ngn_head (fun p' ps' ms' => implM usegs (mbind (LOOP p') ngn_KF) ps' POSTQ ms') ->
    ngn_head (fun p' ps' ms' => implM usegs (mbind (mbind (read_block MOps (prims HO fo_nop sites) (DStack SiteBhdrNextPacket 0) p') (ngn_body LOOP)) ngn_KF) ps' POSTQ ms').
  Section Sz2.
  Variables LOOP ra' t0' t1' t2' x0 a0' a1' a2' a3' a4' a5' a6' a7' x6 x7 t3' t4' t5' t6' m5 ps bq Bq Ix alloc data eb sx ix hcs dw dj ccs : ltac2:(SecDiet.SzSec.tyM 'ngn_loop_S__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @LOOP).
  Lemma ngn_loop_S__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_loop_S__stmt "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AD ADDIF ADJ AH ALN BU HFL HPL HinF LO P1 P2 P4 P5 P6 PP R1 R2 R3 RBLK SFL SITES SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9. pin_using (fun (AD ADDIF ADJ AH ALN BU HFL HPL HinF LO P1 P2 P4 P5 P6 PP R1 R2 R3 RBLK SFL SITES SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 : unit) => tt).
    intros HLOOP.
 intros ST5 FR5 Hccs MI5 G5 PC5 AG5 HH Hh HD Hd OF5. unfold NGN_LOOP.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof PC5 as (Afx & Hin & (Bx' & Ix' & jx' & padx & bsx' & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    pose proof G5 as G5e. rewrite EPB in G5e.
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G5e ltac:(right; left; reflexivity)) as (K1 & K2 & K3 & K4 & K5 & K6).
    pose proof (PB_apart K _ _ _ _ _ _ _ _ _ _ G5 eq_refl) as [APB API].
    pose proof WF as (W1' & W2' & W3 & W4 & W5' & W6' & W7' & W8' & W9' & W10' & W11 & W12 & W13 & W14).
    unfold S3.F_ngnextA.TwB.pv, pcap_blocks, psize, is_ng in EPB, K1, K2, K3, K4, K5, K6, APB. cbn [pc_self pc_buffer pc_bufalloc pc_priv] in EPB, K1, K2, K3, K4, K5, K6, APB.
    unfold PCAP_NG_SF_TOTAL in APB.
    unfold S3.F_ngnextA.TwB.pv in W3, W4, W13, W14. cbn [pc_bufalloc pc_bufdata pc_priv pc_bufsize] in W3, W4, W13, W14.
    assert (EBX : Bx' = Bq) by congruence. subst Bx'.
    unfold S3.F_ngnextA.TwB.pv in Hin. cbn [pc_rfile] in Hin.
    unfold S3.F_ngnextA.TwB.pv in BUF. cbn [pc_bufalloc] in BUF. cbn [pc_bufdata] in PFX.
    pose proof PRIV as NG. unfold priv_cells, S3.F_ngnextA.TwB.pv, PCAP_PRIV_OFF in NG. cbn [pc_priv] in NG. unfold ng_cells in NG.
    assert (NPB : forall a, in_block CLc a -> (a < alloc_ceiling)%Z /\ ~ (P <= a < P + 680)%Z /\ ~ (Bq <= a < Bq + alloc)%Z).
    { intros a Ha. destruct (ngn_CLc_facts _ _ _ _ G5 Ha) as [Hc Hnb]. split; [clear - Hc; lia|]. split; intros Hr; apply Hnb; unfold pcap_blocks, in_block.
      - apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. unfold psize, is_ng, S3.F_ngnextA.TwB.pv. cbn [pc_priv]. unfold PCAP_NG_SF_TOTAL. clear - Hr; lia.
      - apply Exists_cons_tl. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd pc_buffer pc_bufalloc S3.F_ngnextA.TwB.pv]. clear - Hr; lia. }
    assert (INP : forall a, (P <= a < P + 680)%Z -> client_keeps ((CLc ++ [(self, P, PCAP_NG_SF_TOTAL)]) ++ IBLK ix Ix' sx) (bv_unsigned sp + -160) a).
    { intros a Ha. right. apply in_block_app. left. apply in_block_app. right. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. unfold PCAP_NG_SF_TOTAL. exact Ha. }
    (* [comment removed for export] *)
    apply pcap_cells_split4 in CELLS as (PRE & CE & HDR & OPS); [|reflexivity].
    apply (rw_cells_split_CB usegs m5 _ [] 304 _ [] [256; 48]%nat) in CE; [|reflexivity]. cbn [mk_CB_cells app] in CE.
    destruct (rw_cells_cut _ _ _ 1 CE) as [CE1 CE2]. clear CE. cbn [firstn skipn cells_size csize Nat.add] in CE1, CE2.
    replace (P + 216 + Z.of_nat 256)%Z with (P + 472)%Z in CE2 by lia.
    unfold pc_pre in PRE.
    destruct (rw_cells_cut _ _ _ 3 PRE) as [PRE0 PRE3]. destruct (rw_cells_cut _ _ _ 2 PRE3) as [P20 PRE5].
    destruct (rw_cells_cut _ _ _ 2 PRE5) as [P32 PRE7]. destruct (rw_cells_cut _ _ _ 2 PRE7) as [P48 PRE9]. clear PRE PRE3 PRE5 PRE7.
    cbn [firstn skipn cells_size csize Nat.add app] in PRE0, P20, P32, P48, PRE9.
    replace (P + Z.of_nat 20)%Z with (P + 20)%Z in P20 by lia. replace (P + Z.of_nat 20 + Z.of_nat 12)%Z with (P + 32)%Z in P32 by lia.
    replace (P + Z.of_nat 20 + Z.of_nat 12 + Z.of_nat 16)%Z with (P + 48)%Z in P48 by lia.
    replace (P + Z.of_nat 20 + Z.of_nat 12 + Z.of_nat 16 + Z.of_nat 12)%Z with (P + 60)%Z in PRE9 by lia.
    destruct (rw_cells_cut _ _ _ 1 NG) as [NG0 NG1]. destruct (rw_cells_cut _ _ _ 1 NG1) as [NG656 NGR]. clear NG NG1.
    cbn [firstn skipn cells_size csize Nat.add app] in NG0, NG656, NGR.
    replace (P + 648 + Z.of_nat 8)%Z with (P + 656)%Z in NG656 by lia. replace (P + 648 + Z.of_nat 8 + Z.of_nat 4)%Z with (P + 660)%Z in NGR by lia.
    (* [comment removed for export] *)
    pose proof FR5 as FRJ. unfold S3.F_ngnextA.TwB.ngn_frame in FRJ.
    destruct (proj1 (rw_cells_app usegs m5 _ _ _) FRJ) as [F0 F4]. destruct (proj1 (rw_cells_app usegs m5 _ _ _) F4) as [FCUR FS]. clear FRJ F4.
    cbn [cells_size csize Nat.add] in FCUR, FS. rewrite Hccs in FS.
    replace (bv_unsigned sp + -160 + Z.of_nat 32)%Z with (bv_unsigned sp + -128)%Z in FCUR, FS by lia.
    replace (bv_unsigned sp + -128 + Z.of_nat 24)%Z with (bv_unsigned sp + -104)%Z in FS by lia.
    hide F0. hide FCUR. hide FS. hide PRE0. hide P20. hide P32. hide P48. hide PRE9. hide CE1. hide CE2. hide HDR. hide OPS. hide NG0. hide NG656. hide NGR. hide BUF. hide HH. hide HD. hide FR5. hide PRIV. hide IFS.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl usegs m5) as WM.
    apply (implM_bind_assoc usegs). unfold implM. iprefix. step. step. step. step. step. clear MU WM.
    unhide F0. unhide FCUR. unhide FS. unhide PRE0. unhide P20. unhide P32. unhide P48. unhide PRE9. unhide CE1. unhide CE2. unhide HDR. unhide OPS. unhide NG0. unhide NG656. unhide NGR. unhide BUF. unhide HH. unhide HD. unhide FR5. unhide PRIV. unhide IFS.
    apply evt_done. name_sp sp (-160)%Z. eapply (implM_bind usegs).
    { eapply (RBLK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 R ps (CLc ++ [(self, P, PCAP_NG_SF_TOTAL)]) (IBLK ix Ix' sx) FB f Af P Bq (bv_unsigned sp + -128)%Z (P + 216)%Z lo
                (pv bq alloc data eb sx ix) sx ix (DStack SiteBhdrNextPacket 0) bsx' (firstn 256 (pj_g jx')) ccs);
        [ split; [rewrite <- app_assoc; cbn [app]; pose proof G5e as GX; unfold pcap_blocks, S3.F_ngnextA.TwB.pv, psize, is_ng in GX; cbn [pc_self pc_buffer pc_bufalloc pc_priv] in GX; unfold IBLK; exact GX |];
          split; [rewrite Hsp; exact ST5|]; split; [unfold rc_lo; lia|]; split; [unfold READ_BLOCK_STACK, PCAP_L1_STACK; rewrite Hsp; lia|];
          split; [rewrite Hsp; unfold rc_spmain in *; lia|]; split; [exact MI5|]; split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]
        | exact HinF | reflexivity | reflexivity
        | apply in_or_app; left; apply in_or_app; right; left; reflexivity
        | intros st'; cbn [eval_rdest fo_site fo_nop]; rewrite SITES; unfold sites_at, D_NEXT_PACKET; rewrite Hsp; lia
        | reflexivity | reflexivity | f_equal; lia | reflexivity
        | split; [exact P20|]; split; [exact P48|]; split; [exact NG656|]; cbn [pc_bufsize pc_bufalloc S3.F_ngnextA.TwB.pv]; clear - W2 W13 W3 W14; lia
        | exact BUF | exact PFX | cbn [pc_bufdata pc_bufalloc S3.F_ngnextA.TwB.pv]; exact W4
        | exact FCUR | exact Hccs | rewrite Hsp; lia | unfold rc_spmain in *; lia | replace (bv_unsigned sp + -128)%Z with (bv_unsigned sp + (-128))%Z by lia; apply aligned16_8; [exact ALN| reflexivity]
        | exact CE1 | right; reflexivity | apply aligned16_8; [exact P2| reflexivity] ]. }
    intros rb st' ms' PO.
    destruct PO as (a0v & m6 & p' & B' & bs' & E & OF6 & MI6 & ST6 & AG6 & G6 & BH6 & BUF6 & PFX6 & LEN6 & PRIVE & RFE & SELFE & BSZE & SWE & META & RM).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 0x17aac)) with (Z_to_bv 64 0x17aac) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    destruct p' as [self' f' bsz' alloc' bq' data' sw' vmaj' vmin' snap' lt' lte' prec' brk' eb' hdr' priv'].
    cbn [pc_priv pc_rfile pc_self pc_bufsize pc_swapped S3.F_ngnextA.TwB.pv] in PRIVE, RFE, SELFE, BSZE, SWE.
    unfold same_meta in META. cbn [pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_break_loop pc_errbuf pc_header S3.F_ngnextA.TwB.pv] in META.
    destruct META as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9). subst priv' f' self' bsz' sw' vmaj' vmin' snap' lt' lte' prec' brk' eb' hdr'.
    change ({| pc_self := self; pc_rfile := f; pc_bufsize := bufsize; pc_bufalloc := alloc'; pc_buffer := bq'; pc_bufdata := data'; pc_swapped := swapped;
               pc_version_major := vmaj; pc_version_minor := vmin; pc_snapshot := snapshot; pc_linktype := linktype; pc_linktype_ext := ltext;
               pc_tstamp_precision := prec; pc_break_loop := brk; pc_errbuf := eb; pc_header := header; pc_priv := PrivNg sx ix |})
      with (pv bq' alloc' data' eb sx ix) in *.
    cbn [pc_buffer pc_bufalloc pc_bufdata S3.F_ngnextA.TwB.pv] in G6, BUF6, PFX6, LEN6, RM.
    destruct BH6 as (P20' & P48' & NG656' & BR1 & BR2 & BR3 & BR4). cbn [pc_bufsize pc_swapped pc_bufalloc S3.F_ngnextA.TwB.pv] in P20', P48', BR1, BR3, BR4.
    assert (OF7 : ps_outfile st' = o) by (rewrite OF6; exact OF5).
    (* [comment removed for export] *)
    transport F0 m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [left; clear - Ha; lia| gio_ceil_fact; clear -CLO__ Ha LO BU SPW P4 RSP; lia]).
    transport FS m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [left; clear - Ha; lia| gio_ceil_fact; clear -CLO__ Ha LO BU SPW P4 RSP; lia]).
    transport HH m6 AG6 ltac:(intros a Ha; rewrite Hh in Ha; split; [left; clear - Ha R1; lia| gio_ceil_fact; clear -CLO__ Ha R1 LO BU SPW P4; lia]).
    transport HD m6 AG6 ltac:(intros a Ha; cbn [cells_size] in Ha; rewrite Hd in Ha; split; [left; clear - Ha R1 R2; lia| gio_ceil_fact; clear -CLO__ Ha R1 R2 LO BU SPW P4; lia]).
    transport PRE0 m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [apply INP; clear - Ha; lia| gio_ceil_fact; clear -CLO__ Ha LO BU SPW P4; lia]).
    transport P32 m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [apply INP; clear - Ha; lia| gio_ceil_fact; clear -CLO__ Ha LO BU SPW P4; lia]).
    transport PRE9 m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [apply INP; clear - Ha; lia| gio_ceil_fact; clear -CLO__ Ha LO BU SPW P4; lia]).
    transport CE2 m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [apply INP; clear - Ha; lia| gio_ceil_fact; clear -CLO__ Ha LO BU SPW P4; lia]).
    transport HDR m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add hdr_cells pc_header S3.F_ngnextA.TwB.pv] in Ha; split; [apply INP; clear - Ha; lia| gio_ceil_fact; clear -CLO__ Ha LO BU SPW P4; lia]).
    transport OPS m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add pc_ops] in Ha; split; [apply INP; clear - Ha; lia| gio_ceil_fact; clear -CLO__ Ha LO BU SPW P4; lia]).
    transport NG0 m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [apply INP; clear - Ha; lia| gio_ceil_fact; clear -CLO__ Ha LO BU SPW P4; lia]).
    transport NGR m6 AG6 ltac:(intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [apply INP; clear - Ha; lia| gio_ceil_fact; clear -CLO__ Ha LO BU SPW P4; lia]).
    assert (IFS6 : ifaces_ok (pv bq' alloc' data' eb sx ix) Ix' m6).
    { eapply ifaces_ok_agree; [exact AG6 | | exact IFS]. intros sg q Hq a Ha. unfold S3.F_ngnextA.TwB.pv in Hq. cbn [pc_priv] in Hq. injection Hq as E1 E2. subst sg ix.
      destruct (API sx q eq_refl) as [X1 X2]. unfold psize, is_ng, S3.F_ngnextA.TwB.pv in X1. cbn [pc_priv] in X1. unfold PCAP_NG_SF_TOTAL in X1.
      pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G5e ltac:(right; right; left; reflexivity)) as (I1 & I2 & I3 & I4 & I5 & I6).
      assert (EI : Ix = Ix') by congruence.
      split; [right; apply in_block_app; right; unfold IBLK, in_block; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; exact Ha|].
      gio_ceil_fact; clear -CLO__ Ha X1 I1 I4 EI LO BU SPW. lia. }
    pose proof (rw_cells_uncut _ _ _ _ _ PRE0 P20' ltac:(cbn; lia)) as PREa. pose proof (rw_cells_uncut _ _ _ _ _ PREa P32 ltac:(cbn; lia)) as PREb.
    pose proof (rw_cells_uncut _ _ _ _ _ PREb P48' ltac:(cbn; lia)) as PREc. pose proof (rw_cells_uncut _ _ _ _ _ PREc PRE9 ltac:(cbn; lia)) as PRE.
    clear PREa PREb PREc PRE0 P20' P32 P48' PRE9 P20 P48. cbn [app] in PRE.
    pose proof (rw_cells_uncut _ _ _ _ _ NG0 NG656' ltac:(cbn; lia)) as NGa. pose proof (rw_cells_uncut _ _ _ _ _ NGa NGR ltac:(cbn; lia)) as NG6.
    clear NGa NG0 NG656' NGR NG656. cbn [app] in NG6.
    assert (AG7 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m6).
    { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [exact AG6|]. intros a [[Ha|Ha] _].
      - split; [left; clear - Ha; lia| gio_ceil_fact; clear -CLO__ Ha LO BU SPW P4; lia].
      - destruct (NPB a Ha) as (Hc & Hn1 & Hn2). split; [right; apply in_block_app; left; apply in_block_app; left; exact Ha| gio_ceil_fact; clear -CLO__ Hc Hn1 Hn2 LO BU SPW; lia]. }
    assert (G6' : GIo K R st' (CLc ++ pcap_blocks (pv bq' alloc' data' eb sx ix) P B' Ix') FB m6).
    { eapply (GIo_perm K HPL); [exact G6|]. unfold pcap_blocks, S3.F_ngnextA.TwB.pv, psize, is_ng. cbn [pc_self pc_buffer pc_bufalloc pc_priv]. unfold IBLK.
      change (CLc ++ (self, P, PCAP_NG_SF_TOTAL) :: (bq', B', alloc') :: match ix with Some q => [(q, Ix', (40 * ng_ifaces_size sx)%Z)] | None => [] end)
        with (CLc ++ [(self, P, PCAP_NG_SF_TOTAL)] ++ (bq', B', alloc') :: match ix with Some q => [(q, Ix', (40 * ng_ifaces_size sx)%Z)] | None => [] end).
      rewrite (app_assoc CLc). apply Permutation.Permutation_cons_app. apply Permutation.Permutation_refl. }
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G6' ltac:(right; left; reflexivity)) as (K1' & K2' & K3' & K4' & K5' & K6').
    assert (WF' : pcap_wf (pv bq' alloc' data' eb sx ix)).
    { unfold pcap_wf, S3.F_ngnextA.TwB.pv in WF |- *.
      cbn [pc_snapshot pc_bufsize pc_bufalloc pc_bufdata pc_break_loop pc_tstamp_precision pc_version_major pc_version_minor pc_linktype pc_linktype_ext pc_header pc_priv] in WF |- *.
      clear - WF BR3 BR4 LEN6. lia. }
    assert (JOIN : forall cs, rw_cells usegs m6 (P + 216) cs -> cells_size cs = 304%nat ->
              rw_cells usegs m6 P (pcap_cells_gen (pv bq' alloc' data' eb sx ix) P B' (C8 (Z_to_bv 64 Afx)) (C8 (Z_to_bv 64 (pk_stats PK))) (C8 (Z_to_bv 64 (pk_oneshot PK))) (set_pj_g (cells_bytes cs) jx'))).
    { intros cs HCS Hcs.
      exact (pcap_cells_join4 _ P (pv bq' alloc' data' eb sx ix) B' (C8 (Z_to_bv 64 Afx)) (C8 (Z_to_bv 64 (pk_stats PK))) (C8 (Z_to_bv 64 (pk_oneshot PK))) jx' cs header eq_refl PRE HCS Hcs HDR OPS). }
    (* [comment removed for export] *)
    assert (FIN : forall cs ccs', rw_cells usegs m6 (P + 216) cs -> cells_size cs = 304%nat ->
              rw_cells usegs m6 (bv_unsigned sp + -128) ccs' -> cells_size ccs' = 24%nat ->
              rw_cells usegs m6 (bv_unsigned sp + -160) (S3.F_ngnextA.TwB.ngn_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 P HA DA dj ccs')
              /\ ngn_final m6 st' (pcap_blocks (pv bq' alloc' data' eb sx ix) P B' Ix') (pv bq' alloc' data' eb sx ix) hcs dw).
    { intros cs ccs' HCS Hcs HCUR' Hccs'.
      split. { unfold S3.F_ngnextA.TwB.ngn_frame. eapply (rw_cells_uncut _ _ _ _ _ F0); [eapply (rw_cells_uncut _ _ _ _ _ HCUR' FS); rewrite Hccs'; cbn; lia | cbn; lia]. }
      split; [exact G6'|]. split.
      { exists Afx. split; [exact Hin|]. eexists B', Ix', _, padx, bs'.
        split; [reflexivity|]. split; [exact (JOIN cs HCS Hcs)|]. split; [exact NG6|]. split; [exact BUF6|]. split; [exact PFX6|]. split; [exact IFS6| exact WF']. }
      split; [exact AG7|]. split; [exact HH|]. split; [exact Hh|]. split; [exact HD|]. split; [exact Hd| exact OF7]. }
    cbv beta. unfold implM. iprefix.
    destruct rb as [p'' | msg p'' | c p''].
    - (* [comment removed for export] *)
      destruct RM as (-> & -> & HEB6 & (ccs' & HCUR6 & Hccs')).
      pose proof (rw_cells_uncut _ _ _ _ _ HEB6 CE2 ltac:(cbn; lia)) as CE6.
      destruct (FIN _ _ CE6 eq_refl HCUR6 Hccs') as [FR6 FIN6].
      hide FR6. hide FIN6. hide HH. hide HD. hide CE6. hide HEB6. hide CE2. hide HDR. hide OPS. hide PRE. hide NG6. hide BUF6. hide HCUR6. hide F0. hide FS. hide CE1. hide PRIV.
      pose proof (munch_refl ([] : list (Z * Z)) m6) as MU. pose proof (wmono_refl usegs m6) as WM.
      step. step. if_cases B1; zify_cond B1. { exfalso. rewrite ?unsigned_lit in B1 by lia. clear - B1. lia. }
      step. if_cases B2; zify_cond B2; [| exfalso; rewrite ?unsigned_lit in B2 by lia; clear - B2; lia].
      step. step.
      unhide FR6. unhide FIN6. apply evt_done. cbn [OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.TwB.ngn_body]. apply implM_retb. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.TwB.ngn_KF. unfold NGN_EPILOGUE.
      eapply ngn_ret_0; [exact ST6 | exact FR6 | exact Hccs' | exact MI6 | exact FIN6].
    - (* [comment removed for export] *)
      destruct RM as (-> & -> & (junk6 & HEB6) & LENM & MOK & (ccs' & HCUR6 & Hccs')).
      pose proof (rw_cells_uncut _ _ _ _ _ HEB6 CE2 ltac:(cbn [cells_size csize]; clear - LENM; lia)) as CE6. cbn [app] in CE6.
      destruct (FIN _ _ CE6 ltac:(cbn [cells_size csize]; clear - LENM; lia) HCUR6 Hccs') as [FR6 FIN6].
      hide FR6. hide FIN6. hide HH. hide HD. hide CE6. hide HEB6. hide CE2. hide HDR. hide OPS. hide PRE. hide NG6. hide BUF6. hide HCUR6. hide F0. hide FS. hide CE1. hide PRIV.
      pose proof (munch_refl ([] : list (Z * Z)) m6) as MU. pose proof (wmono_refl usegs m6) as WM.
      step. step. if_cases B1; zify_cond B1; [| exfalso; rewrite ?unsigned_lit in B1 by lia; clear - B1; lia].
      unhide FR6. unhide FIN6. apply evt_done. cbn [OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.TwB.ngn_body]. apply implM_retb. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.TwB.ngn_KF. unfold NGN_EPILOGUE.
      eapply ngn_ret_m1; [exact ST6 | exact FR6 | exact Hccs' | exact MI6 |].
      destruct FIN6 as (G7 & PC7 & REST). split; [exact G7|]. split; [| exact REST].
      apply PCAPR_closable_of in PC7. destruct PC7 as (Afy & Hiny & (By & Iy & jy & pady & bsy & EPBy & CEy & PRy & BUFy & PFXy & IFCy & WFy)).
      exists Afy. split; [exact Hiny|]. exists By, Iy, jy, pady, bsy.
      split; [exact EPBy|]. split; [exact CEy|]. split; [exact PRy|]. split; [exact BUFy|]. split; [exact PFXy|]. split; [| exact WFy].
      unfold ifaces_closable, S3.F_ngnextA.TwB.pv in IFCy |- *. cbn [pc_priv set_errbuf] in IFCy |- *. exact IFCy.
    - (* [comment removed for export] *)
      destruct RM as (-> & -> & HEB6 & (cpad & HCUR6) & COFF & CR0 & CR1 & CR2 & CBT & LEND & GRD).
      destruct c as [coff crem cbt]. cbn [cur_off cur_remaining cur_block_type] in COFF, CR0, CR1, CR2, CBT, LEND, HCUR6. subst coff.
      pose proof (rw_cells_uncut _ _ _ _ _ HEB6 CE2 ltac:(cbn; lia)) as CE6.
      destruct (FIN _ _ CE6 eq_refl HCUR6 eq_refl) as [FR6 FIN6]. destruct FIN6 as (_ & PC6 & _).
      apply evt_done. cbn [OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.TwB.ngn_body].
      eapply (ngn_dispatch LOOP HLOOP); [exact ST6 | exact FR6 | exact MI6 | exact G6' | exact PC6 | exact AG7 | exact HH | exact Hh | exact HD | exact Hd | exact GRD | exact LEND | exact CR2 | exact CR0 | exact CBT | exact OF7].
  Qed.
  End Sz2.
  Lemma ngn_loop_S : ltac:(let t := eval cbv delta [ngn_loop_S__stmt] in ngn_loop_S__stmt in exact t).
  Proof using AD ADDIF ADJ AH ALN BU HFL HPL HinF LO P1 P2 P4 P5 P6 PP R1 R2 R3 RBLK SFL SITES SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9. intros LOOP HLOOP ra' t0' t1' t2' x0 a0' a1' a2' a3' a4' a5' a6' a7' x6 x7 t3' t4' t5' t6' m5 ps bq Bq Ix alloc data eb sx ix hcs dw dj ccs. ltac2:(SecDiet.SzSec.closeP 'ngn_loop_S__body "vhvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Lemma ngn_loop : forall fuel, ngn_head (fun p' ps' ms' => implM usegs (mbind (ng_scan_blocks MOps (prims HO fo_nop sites) fuel p') ngn_KF) ps' POSTQ ms').
  Proof using AD ADDIF ADJ AH ALN BU HFL HPL HinF LO P1 P2 P4 P5 P6 PP R1 R2 R3 RBLK SFL SITES SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9. pin_using (fun (AD ADDIF ADJ AH ALN BU HFL HPL HinF LO P1 P2 P4 P5 P6 PP R1 R2 R3 RBLK SFL SITES SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 : unit) => tt).
    induction fuel as [|fuel IH].
    - unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.TwB.ngn_head. intros. cbn [ng_scan_blocks].
      eapply (implM_bind usegs _ _ _ (fun _ _ _ => False)); [apply implM_unr | intros a s' ms' X; exact (False_rect _ X)].
    - unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.TwB.ngn_head. intros. rewrite ng_scan_blocks_S.
      revert H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11. apply (ngn_loop_S _ IH).
  Qed.
End NgnCtx.

End WithCeil.
End TwB.
End F_ngnextL.

(* [comment removed for export] *)
Module F_ngnext.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep MonadX Image ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy GI. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_ngnextA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Startup_B__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_ngnextD__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.Pcap_iface_pp OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface_ng OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_small OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.PPFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.PP_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.NpArith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_chkD__S3.F_ngnextI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_chkD__S3.F_ngnextL.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia_e2w2_base := first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                                 | zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac ceil_mentioned := lazymatch goal with | |- context [@alloc_ceiling _] => idtac | _ : context [@alloc_ceiling _] |- _ => idtac end.
(* [comment removed for export] *)
Local Ltac gio_ceil_fact :=
  match goal with
  | G : GIo _ _ _ _ _ _ |- _ => let H := fresh "CLO__" in pose proof (PcapRep.GIo_ceil_lo _ _ _ _ _ _ G) as H; unfold rc_lo in H
  end.
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try gio_ceil_fact; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section WithCeil.
Context {CEILV : CEIL}.
Section NgnThm.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HPL : heap_perm_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis SNPRINTF : snprintf_spec_stmt K.
  Hypothesis PP : post_process_stmt.
  Hypothesis ADJ : adjust_snapshot_stmt.
  Hypothesis RBLK : read_block_stmt HO K sites.
  Hypothesis ADDIF : add_interface_stmt HO K sites.

  Definition pcap_ng_next_packet_proof__stmt : Prop := pcap_ng_next_packet_stmt HO K sites.
  Section Sz1.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CLc PB FB lo P HA DA p fuel hcs dc : ltac2:(SecDiet.SzSec.tyM 'pcap_ng_next_packet_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma pcap_ng_next_packet_proof__body : ltac2:(SecDiet.SzSec.bodyP 'pcap_ng_next_packet_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using ADDIF ADJ HFL HPL PP RBLK SFL SNPRINTF. pin_using (fun (ADDIF ADJ HFL HPL PP RBLK SFL SNPRINTF : unit) => tt).
    intros PRE PC NG SITES -> -> -> HH Hh HD Hd R1 R2 R3 AH AD.
    destruct PRE as (G & ST & LO & BU & SPM & MI & TP & ALN).
    pose proof (GIo_spw K _ _ _ _ _ G) as SPW. pose proof (GIo_sp47 K _ _ _ _ _ G) as SP47. unfold rc_lo in LO. unfold PCAP_L2_STACK in BU.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    destruct p as [self rfile bufsize bufalloc buffer bufdata swapped vmaj vmin snapshot linktype ltext prec brk errbuf header priv].
    destruct priv as [sf|sx ix]; [discriminate NG|]. clear NG.
    pose proof PC as (Af & HinF & (B & I & j & pad & bs & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    cbn [pc_rfile] in HinF.
    pose proof WF as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11 & W12 & W13 & W14).
    cbn [pc_snapshot pc_bufsize pc_bufalloc pc_bufdata pc_break_loop pc_tstamp_precision pc_version_major pc_version_minor pc_linktype pc_linktype_ext pc_header pc_priv] in W1, W2, W3, W4, W5, W6, W7, W8, W9, W10, W11, W12, W13, W14.
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G ltac:(rewrite EPB; left; reflexivity)) as (P1 & P2 & P3 & P4 & P5 & P6).
    unfold psize, is_ng in P3, P4, P5, P6. cbn [pc_priv] in P3, P4, P5, P6. unfold PCAP_NG_SF_TOTAL in P3, P4, P5, P6.
    pose proof (GIo_block_ok K _ _ _ _ _ _ G ltac:(apply in_or_app; right; exact HinF)) as (A1 & _ & _ & A4 & _ & _).
    cbn [cb_addr cb_size fst snd] in A1, A4. unfold FILE_BLOCK in A4.
    rewrite EPB in G, PC.
    unfold next_packet_op, PcapRep.np_entry, is_ng. cbn [pc_priv pk_next_ng PK].
    rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.pcap_ng_next_packet_KF HO sites).
    (* [comment removed for export] *)
    pose proof CELLS as CJ. unfold pcap_cells_gen, pc_pre, hdr_cells, pc_ops, PcapRep.np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF in CJ.
    cbn [app pc_bufsize pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_header pc_priv pk_next_ng pk_cleanup_ng PK] in CJ.
    clear CELLS PRIV BUF PFX IFS.
    hide HH. hide HD.
    pose proof (munch_refl [(bv_unsigned sp + -160, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ssegs m) as WM.
    unfold implM. iprefix.
    carve_frame 160%nat ST.
    apply (rw_cells_split_CB ssegs _ _ [] 160 _ [] [8; 8; 8; 8; 24; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB _ ?t] =>
      lazymatch t with firstn _ _ => idtac | skipn _ _ => idtac end; let j := fresh "jk" in set (j := t) in FR; clearbody j end.
    do 30 step.
    unhide HH. unhide HD.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (AGP : agrees_on (fun a => outside [(bv_unsigned sp + -160, bv_unsigned sp)]%Z a) m mm) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]);
      rename mm into m0 end.
    apply (agrees_rw_cells _ _ _ _ _ AGP) in HH; [| intros a Ha; rewrite Hh in Ha; cbn [outside]; clear - Ha R1; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGP) in HD; [| intros a Ha; cbn [cells_size] in Ha; rewrite Hd in Ha; cbn [outside]; clear - Ha R1 R2; lia].
    lazymatch type of G with GIo K R s ?BL FB m =>
      assert (G0 : GIo K R s BL FB m0) by (eapply (GIo_pcap_frame K HFL SFL); [exact G | exact MU | exact WM |]; apply Forall_cons; [| apply Forall_nil]; left; cbn [fst snd]; unfold rc_lo, rc_spmain in *; clear - LO BU SPM; lia) end.
    lazymatch type of PC with PCAPR P ?p ?PB FB m =>
      assert (PC0 : PCAPR (hptr:=hptr) P p PB FB m0) by (eapply PCAPR_agree; [exact AGP | | exact PC]; intros a Ha; pose proof (in_PB_below K _ _ _ _ _ _ _ G Ha); cbn [outside]; gio_ceil_fact; clear -CLO__ H0 LO BU SPW; lia) end.
    assert (AG0 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m0).
    { eapply agrees_on_weaken; [exact AGP|]. intros a [[Ha|Ha] _]; cbn [outside]; [clear - Ha; lia|].
      destruct (GIo_CLc_facts K _ _ _ _ _ _ _ G Ha) as [Hc _]. gio_ceil_fact; clear -CLO__ Hc LO BU SPW. lia. }
    apply evt_done.
    (* [comment removed for export] *)
    pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_chkD__S3.F_ngnextL.ngn_loop HO K sites) as LOOPX.
    unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_head in LOOPX. unfold NGN_LOOP in LOOPX.
    lazymatch goal with FRX : rw_cells ssegs m0 (bv_unsigned sp + -160) (CB 8 ?j0 :: _ :: _ :: _ :: CB 24 ?j4 :: _) |- _ =>
      eapply (LOOPX HFL SFL HPL SNPRINTF PP ADJ RBLK ADDIF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA Af m (ps_outfile s)
                self rfile bufsize swapped vmaj vmin snapshot linktype ltext prec brk header) with (dj := j0) (ccs := [CB 24 j4]) end.
    all: try eassumption. all: try reflexivity. all: try lia.
  Qed.
  End Sz1.
  Theorem pcap_ng_next_packet_proof : ltac:(let t := eval cbv delta [pcap_ng_next_packet_proof__stmt] in pcap_ng_next_packet_proof__stmt in exact t).
  Proof using ADDIF ADJ HFL HPL PP RBLK SFL SNPRINTF. red. unfold next_packet_op_stmt_for. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CLc PB FB lo P HA DA p fuel hcs dc. ltac2:(SecDiet.SzSec.closeP 'pcap_ng_next_packet_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NgnThm.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3 Require NgnPure.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MonadX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.NpArith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.PPFacts.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.Pcap_iface_pp.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface_ng.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_small.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.PP_kit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.U3.NgnPure. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_chkD__S3.F_ngnextI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_chkD__S3.F_ngnextL.TwB.
Import OSSVerify.libpcap.fuzz_pcap.images.Ubsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Ceiling.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia_e2w2_base := first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                                 | zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac ceil_mentioned := lazymatch goal with | |- context [@alloc_ceiling _] => idtac | _ : context [@alloc_ceiling _] |- _ => idtac end.
(* [comment removed for export] *)
Local Ltac gio_ceil_fact :=
  match goal with
  | G : GIo _ _ _ _ _ _ |- _ => let H := fresh "CLO__" in pose proof (S3.PcapRep.TwB.GIo_ceil_lo _ _ _ _ _ _ G) as H; unfold rc_lo in H
  end.
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try gio_ceil_fact; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section WithCeil.
Context {CEILV : CEIL}.
Section NgnThm.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HPL : heap_perm_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis SNPRINTF : snprintf_spec_stmt K.
  Hypothesis PP : post_process_stmt.
  Hypothesis ADJ : adjust_snapshot_stmt.
  Hypothesis RBLK : read_block_stmt HO K sites.
  Hypothesis ADDIF : add_interface_stmt HO K sites.

  Definition pcap_ng_next_packet_proof__stmt : Prop := pcap_ng_next_packet_stmt HO K sites.
  Section Sz1.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CLc PB FB lo P HA DA p fuel hcs dc : ltac2:(SecDiet.SzSec.tyM 'pcap_ng_next_packet_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma pcap_ng_next_packet_proof__body : ltac2:(SecDiet.SzSec.bodyP 'pcap_ng_next_packet_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using ADDIF ADJ HFL HPL PP RBLK SFL SNPRINTF. pin_using (fun (ADDIF ADJ HFL HPL PP RBLK SFL SNPRINTF : unit) => tt).
 intros PRE PC NG SITES -> -> -> HH Hh HD Hd R1 R2 R3 AH AD.
    destruct PRE as (G & ST & LO & BU & SPM & MI & TP & ALN).
    pose proof (GIo_spw K _ _ _ _ _ G) as SPW. pose proof (GIo_sp47 K _ _ _ _ _ G) as SP47. unfold rc_lo in LO. unfold PCAP_L2_STACK in BU.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    destruct p as [self rfile bufsize bufalloc buffer bufdata swapped vmaj vmin snapshot linktype ltext prec brk errbuf header priv].
    destruct priv as [sf|sx ix]; [discriminate NG|]. clear NG.
    pose proof PC as (Af & HinF & (B & I & j & pad & bs & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    cbn [pc_rfile] in HinF.
    pose proof WF as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11 & W12 & W13 & W14).
    cbn [pc_snapshot pc_bufsize pc_bufalloc pc_bufdata pc_break_loop pc_tstamp_precision pc_version_major pc_version_minor pc_linktype pc_linktype_ext pc_header pc_priv] in W1, W2, W3, W4, W5, W6, W7, W8, W9, W10, W11, W12, W13, W14.
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G ltac:(rewrite EPB; left; reflexivity)) as (P1 & P2 & P3 & P4 & P5 & P6).
    unfold psize, is_ng in P3, P4, P5, P6. cbn [pc_priv] in P3, P4, P5, P6. unfold PCAP_NG_SF_TOTAL in P3, P4, P5, P6.
    pose proof (GIo_block_ok K _ _ _ _ _ _ G ltac:(apply in_or_app; right; exact HinF)) as (A1 & _ & _ & A4 & _ & _).
    cbn [cb_addr cb_size fst snd] in A1, A4. unfold FILE_BLOCK in A4.
    rewrite EPB in G, PC.
    unfold next_packet_op, S3.PcapRep.TwB.np_entry, is_ng. cbn [pc_priv pk_next_ng PK].
    rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.TwB.pcap_ng_next_packet_KF HO sites).
    (* [comment removed for export] *)
    pose proof CELLS as CJ. unfold pcap_cells_gen, pc_pre, hdr_cells, pc_ops, S3.PcapRep.TwB.np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF in CJ.
    cbn [app pc_bufsize pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_header pc_priv pk_next_ng pk_cleanup_ng PK] in CJ.
    clear CELLS PRIV BUF PFX IFS.
    hide HH. hide HD.
    pose proof (munch_refl [(bv_unsigned sp + -160, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold implM. iprefix.
    carve_frame 160%nat ST.
    apply (rw_cells_split_CB usegs _ _ [] 160 _ [] [8; 8; 8; 8; 24; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB _ ?t] =>
      lazymatch t with firstn _ _ => idtac | skipn _ _ => idtac end; let j := fresh "jk" in set (j := t) in FR; clearbody j end.
    (* [comment removed for export] *)
    do 16 step.
    (* [comment removed for export] *)
    step. if_false_by (eqz_false P ltac:(clear - P1 P4; lia)).
    step. step. rewrite (and7_aligned P) by (clear - P1 P2 P4; try lia; Z.div_mod_to_equations; lia). step. if_false.
    (* [comment removed for export] *)
    do 11 step.
    (* [comment removed for export] *)
    step. rewrite (seqz_pos' (P + 648)) by (clear - P1 P4; lia).
    step.
    step. rewrite (and7_aligned (P + 648)) by (clear - P1 P2 P4; try lia; Z.div_mod_to_equations; lia).
    pstep.
    step. step.
    assert (SZ : v_sltu z64 z64 = z64) by (rewrite v_sltu_b2z; reflexivity).
    rewrite !SZ. change (Z.lor 0 (bv_unsigned z64)) with 0%Z. clear SZ.
    unhide HH. unhide HD.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (AGP : agrees_on (fun a => outside [(bv_unsigned sp + -160, bv_unsigned sp)]%Z a) m mm) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]);
      rename mm into m0 end.
    apply (agrees_rw_cells _ _ _ _ _ AGP) in HH; [| intros a Ha; rewrite Hh in Ha; cbn [outside]; clear - Ha R1; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGP) in HD; [| intros a Ha; cbn [cells_size] in Ha; rewrite Hd in Ha; cbn [outside]; clear - Ha R1 R2; lia].
    lazymatch type of G with GIo K R s ?BL FB m =>
      assert (G0 : GIo K R s BL FB m0) by (eapply (GIo_pcap_frame K HFL SFL); [exact G | exact MU | exact WM |]; apply Forall_cons; [| apply Forall_nil]; left; cbn [fst snd]; unfold rc_lo, rc_spmain in *; clear - LO BU SPM; lia) end.
    lazymatch type of PC with PCAPR P ?p ?PB FB m =>
      assert (PC0 : PCAPR (hptr:=hptr) P p PB FB m0) by (eapply PCAPR_agree; [exact AGP | | exact PC]; intros a Ha; pose proof (in_PB_below K _ _ _ _ _ _ _ G Ha); cbn [outside]; gio_ceil_fact; clear -CLO__ H0 LO BU SPW; lia) end.
    assert (AG0 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m0).
    { eapply agrees_on_weaken; [exact AGP|]. intros a [[Ha|Ha] _]; cbn [outside]; [clear - Ha; lia|].
      destruct (GIo_CLc_facts K _ _ _ _ _ _ _ G Ha) as [Hc _]. gio_ceil_fact; clear -CLO__ Hc LO BU SPW. lia. }
    apply evt_done.
    (* [comment removed for export] *)
    pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_chkD__S3.F_ngnextL.TwB.ngn_loop HO K sites) as LOOPX.
    unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.TwB.ngn_head in LOOPX. unfold NGN_LOOP in LOOPX.
    lazymatch goal with FRX : rw_cells usegs m0 (bv_unsigned sp + -160) (_ :: _ :: _ :: _ :: CB 24 ?j4 :: _) |- _ =>
      eapply (LOOPX HFL SFL HPL SNPRINTF PP ADJ RBLK ADDIF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA Af m (ps_outfile s)
                self rfile bufsize swapped vmaj vmin snapshot linktype ltext prec brk header) with (dj := []) (ccs := [CB 24 j4]) end.
    all: try eassumption. all: try reflexivity. all: try lia.
  Qed.
  End Sz1.
  Theorem pcap_ng_next_packet_proof : ltac:(let t := eval cbv delta [pcap_ng_next_packet_proof__stmt] in pcap_ng_next_packet_proof__stmt in exact t).
  Proof using ADDIF ADJ HFL HPL PP RBLK SFL SNPRINTF. red. unfold next_packet_op_stmt_for. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m R s CLc PB FB lo P HA DA p fuel hcs dc. ltac2:(SecDiet.SzSec.closeP 'pcap_ng_next_packet_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NgnThm.

End WithCeil.
End TwB.
End F_ngnext.
