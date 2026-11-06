(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep MonadX Image ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcapng_blkA__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.Pcap_iface_pp OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface_ng OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_small.
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
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Definition NGN_FMT_TOO_SHORT : Z := 0x10cd0.    (* [comment removed for export] *)
Definition NGN_FMT_MAJOR : Z := 0x10373.        (* [comment removed for export] *)
Definition NGN_STR_SECTIONS : Z := 0x109c7.     (* [comment removed for export] *)
Definition NGN_STR_BADBOM : Z := 0x10b82.       (* [comment removed for export] *)
Definition NGN_FMT_IFTYPE : Z := 0x10da4.       (* [comment removed for export] *)
Definition NGN_FMT_IFSNAP : Z := 0x10d3e.       (* [comment removed for export] *)
Definition NGN_FMT_NOIDB : Z := 0x10bbb.        (* [comment removed for export] *)
Definition NGN_FMT_CAPLEN : Z := 0x1095e.       (* [comment removed for export] *)
Definition NGN_EPILOGUE : Z := 0x176d4.
Definition NGN_LOOP : Z := 0x1746c.

(* [comment removed for export] *)
(* [comment removed for export] *)
End WithCeil.

Ltac merge_cells H k n :=
  lazymatch type of H with
  | rw_cells ?segs ?m ?A ?cs =>
      let pre := eval cbv beta iota delta [firstn skipn] in (firstn k cs) in
      let mid := eval cbv beta iota delta [firstn skipn] in (firstn n (skipn k cs)) in
      let post := eval cbv beta iota delta [firstn skipn Nat.add] in (skipn (k + n) cs) in
      change cs with (pre ++ mid ++ post) in H;
      apply (rw_cells_merge segs m A pre mid post) in H;
      cbn [cells_size csize cells_bytes cbytes Nat.add app] in H
  end.
(* [comment removed for export] *)
Ltac fix_lit_store :=
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
           change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
           change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) =>
           change (Z_to_le_bytes 2 z) with (le2 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
           change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]; mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
           change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]; mem_after_store
       end).
Ltac pstep := step; fix_lit_store.
(* [comment removed for export] *)
Ltac norm_addr H P :=
  lazymatch type of H with
  | rw_cells _ _ (?b + Z.of_nat ?n)%Z _ =>
      lazymatch b with
      | (P + ?k0)%Z => let k := eval vm_compute in (k0 + Z.of_nat n)%Z in replace (b + Z.of_nat n)%Z with (P + k)%Z in H by lia
      | P => let k := eval vm_compute in (Z.of_nat n) in replace (P + Z.of_nat n)%Z with (P + k)%Z in H by lia
      end
  end.
(* [comment removed for export] *)
Ltac cut_cells H k H1 P :=
  let H2 := fresh "TMP" in
  destruct (rw_cells_cut _ _ _ k H) as [H1 H2]; clear H; cbn [firstn skipn cells_size csize Nat.add] in H1, H2;
  norm_addr H2 P; rename H2 into H.
(* [comment removed for export] *)
Ltac merge_all H :=
  lazymatch type of H with
  | rw_cells ?s ?m ?A ?cs =>
      change cs with ([] ++ cs ++ []) in H; apply (rw_cells_merge s m A [] cs []) in H;
      cbn [cells_size csize cells_bytes cbytes Nat.add app] in H
  end.
(* [comment removed for export] *)
Ltac join_cells H1 H2 :=
  lazymatch type of H1 with rw_cells ?s ?m ?A1 ?cs1 =>
  lazymatch type of H2 with rw_cells _ _ ?A2 ?cs2 =>
    let J := fresh "J" in
    pose proof (rw_cells_uncut m A1 cs1 cs2 A2 H1 H2 ltac:(cbn [cells_size csize Nat.add]; lia)) as J;
    clear H1 H2; cbn [app] in J; rename J into H1
  end end.

Section WithCeil.
Context {CEILV : CEIL}.
Lemma snprintf_length : forall n f args, (length (Fmt.snprintf n f args) <= Z.to_nat (n - 1))%nat.
Proof using Type. pin_using tt. intros. unfold Fmt.snprintf, snprintf_out. apply firstn_le_length. Qed.

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
  (* [comment removed for export] *)
  Definition pv (bq : hptr) (alloc : Z) (data eb : list Z) (s : pcap_ng_sf) (i : option hptr) : pcap hptr hptr :=
    mkPcap self f bufsize alloc bq data swapped vmaj vmin snapshot linktype ltext prec brk eb header (PrivNg s i).
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
  Definition ngn_frame (dj : list byte) (ccs : list cell) : list cell :=
    [CB 8 dj; C8 (Z_to_bv 64 DA); C8 (Z_to_bv 64 HA); C8 (Z_to_bv 64 (P + 648))] ++ ccs ++
    [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Lemma ngn_epilogue :
    forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' : word)
           (m5 : mem) (dj : list byte) (ccs : list cell) (Q : machine_state -> Prop),
      stk ssegs m5 lo (bv_unsigned sp + -160) ->
      rw_cells ssegs m5 (bv_unsigned sp + -160) (ngn_frame dj ccs) -> cells_size ccs = 24%nat -> mem_inv ssegs m5 ->
      (forall t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'',
          stk ssegs m5 lo (bv_unsigned sp) ->
          Q (MS (mkR ra sp gp tp t0'' t1'' t2'' s0 s1 x0 a1'' a2'' a3'' a4'' a5'' a6'' a7'' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3'' t4'' t5'' t6'')
                F (ret_pc ra) fc None m5 (seg_rom ssegs))) ->
      evt ssegs Q
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' x0 x1 a0' a1' a2' a3' a4' a5' a6' a7'
                 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 NGN_EPILOGUE) fc None m5 (seg_rom ssegs)).
  Proof using BU. pin_using (fun (BU : unit) => tt).
    intros until Q. intros ST5 FR5 Hccs MI5 HQ.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl ssegs m5) as WM.
    unfold ngn_frame in FR5.
    apply rw_cells_app in FR5 as [FRJ FR5]. apply rw_cells_app in FR5 as [FRC FRS].
    cbn [cells_size csize Nat.add] in FRS, FRC. rewrite Hccs in FRS.
    replace (bv_unsigned sp + -160 + Z.of_nat 32 + Z.of_nat 24)%Z with (bv_unsigned sp + -104)%Z in FRS by lia.
    replace (bv_unsigned sp + -160 + Z.of_nat 32)%Z with (bv_unsigned sp + -128)%Z in FRC by lia.
    destruct (rw_cells_forget _ _ _ _ FRC) as [cj FRC']. clear FRC. rewrite Hccs in FRC'.
    unfold NGN_EPILOGUE. do 16 step.
    release_frame FRJ ST5 (bv_unsigned sp + -128)%Z. release_frame FRC' ST5 (bv_unsigned sp + -104)%Z. release_frame FRS ST5 (bv_unsigned sp).
    apply evt_done. apply HQ. exact ST5.
  Qed.

  (* [comment removed for export] *)
  Lemma PCAPRC_errbuf : forall Rx sx CLx Px (p : pcap hptr hptr) PB FBx (mx mx' : mem) (Q : Z -> Prop) cs e,
    GIo K Rx sx (CLx ++ PB) FBx mx -> PCAPR_closable (hptr:=hptr) Px p PB FBx mx -> agrees_on Q mx mx' ->
    (forall a, in_block PB a -> ~ (Px + 216 <= a < Px + 472)%Z -> Q a) ->
    rw_cells ssegs mx' (Px + 216) cs -> cells_size cs = 256%nat ->
    PCAPR_closable (hptr:=hptr) Px (set_errbuf e p) PB FBx mx'.
  Proof using AD AH ALN BU LO P1 R1 R2 SPW. pin_using (fun (AD AH ALN BU LO P1 R1 R2 SPW : unit) => tt).
    intros Rx sx CLx Px p PB FBx mx mx' Q cs e G PC AG HQ HCS Hsz.
    destruct PC as (Afx & Hin & (Bx & I & jx & padx & bsx & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    pose proof (psize_pos p) as PS. pose proof (PB_apart K _ _ _ _ _ _ _ _ _ _ G EPB) as [APB API].
    assert (Q1 : forall a, (Px <= a < Px + psize p)%Z -> ~ (Px + 216 <= a < Px + 472)%Z -> Q a).
    { intros a Ha Hn. apply HQ; [|exact Hn]. rewrite EPB. unfold pcap_blocks, in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. exact Ha. }
    apply pcap_cells_split4 in CELLS as (CA & CE & CH & CO); [|reflexivity].
    apply (rw_cells_split_CB ssegs mx _ [] 304 _ [] [256; 48]%nat) in CE; [|reflexivity]. cbn [mk_CB_cells app] in CE.
    destruct (rw_cells_cut _ _ _ 1 CE) as [_ CE2]. clear CE. cbn [firstn skipn cells_size csize Nat.add] in CE2.
    replace (Px + 216 + Z.of_nat 256)%Z with (Px + 472)%Z in CE2 by lia.
    apply (agrees_rw_cells _ _ _ _ _ AG) in CA; [| intros a Ha; rewrite (pc_pre_size p Px Bx (C8 (Z_to_bv 64 Afx)) jx eq_refl) in Ha; apply Q1; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG) in CH; [| intros a Ha; cbn [cells_size csize hdr_cells Nat.add] in Ha; apply Q1; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG) in CO; [| intros a Ha; cbn [cells_size csize pc_ops Nat.add] in Ha; apply Q1; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG) in CE2; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply Q1; lia].
    pose proof (rw_cells_uncut _ _ _ _ _ HCS CE2 ltac:(rewrite Hsz; lia)) as CE'.
    pose proof WF as (_ & _ & W3 & _).
    destruct (pcap_aux_closable_agree p Px Bx I padx bsx mx mx' Q AG) as (BUF' & PRIV' & IFS');
      [ intros a Ha; apply HQ; [rewrite EPB; unfold pcap_blocks, in_block; apply Exists_cons_tl, Exists_cons_hd; cbn [cb_addr cb_size fst snd]; exact Ha| lia]
      | intros a Ha; apply Q1; unfold PCAP_PRIV_OFF in Ha; lia
      | intros sg q Hq a Ha; destruct (API sg q Hq) as [X1 X2]; apply HQ;
          [rewrite EPB; unfold pcap_blocks, in_block; rewrite Hq; do 2 apply Exists_cons_tl; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; exact Ha| lia]
      | lia | exact BUF | exact PRIV | exact IFS |].
    exists Afx. split; [destruct p; exact Hin|].
    exists Bx, I, (set_pj_g (cells_bytes (cs ++ [CB 48 (firstn 48 (skipn 256 (pj_g jx)))])) jx), padx, bsx.
    split; [rewrite EPB; destruct p; reflexivity|].
    split. { pose proof (pcap_cells_join4 mx' Px p Bx (C8 (Z_to_bv 64 Afx)) (C8 (Z_to_bv 64 (pk_stats PK))) (C8 (Z_to_bv 64 (pk_oneshot PK))) jx _ (pc_header p)
                           eq_refl CA CE' ltac:(rewrite cells_size_app, Hsz; reflexivity) CH CO) as J.
             replace (set_header (pc_header p) p) with p in J by (destruct p; reflexivity).
             destruct p; cbn. exact J. }
    split; [destruct p; exact PRIV'|]. split; [destruct p; exact BUF'|]. split; [destruct p; exact PFX|].
    split; [destruct p; exact IFS'|]. destruct p; exact WF.
  Qed.

  (* [comment removed for export] *)
  Definition ngn_final (m5 : mem) (ps : PState H hptr) (PB' : list (cblock (hptr:=hptr))) (p' : pcap hptr hptr) (hcs' : list cell) (dw : cell) : Prop :=
    GIo K R ps (CLc ++ PB') FB m5 /\ PCAPR (hptr:=hptr) P p' PB' FB m5
    /\ agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5
    /\ rw_cells ssegs m5 HA hcs' /\ cells_size hcs' = 24%nat /\ rw_cells ssegs m5 DA [dw] /\ csize dw = 8%nat /\ ps_outfile ps = o.
  (* [comment removed for export] *)
  Definition ngn_finalC (m5 : mem) (ps : PState H hptr) (PB' : list (cblock (hptr:=hptr))) (p' : pcap hptr hptr) (hcs' : list cell) (dw : cell) : Prop :=
    GIo K R ps (CLc ++ PB') FB m5 /\ PCAPR_closable (hptr:=hptr) P p' PB' FB m5
    /\ agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5
    /\ rw_cells ssegs m5 HA hcs' /\ cells_size hcs' = 24%nat /\ rw_cells ssegs m5 DA [dw] /\ csize dw = 8%nat /\ ps_outfile ps = o.

  Lemma ngn_final_C : forall m5 ps PB' p' hcs' dw, ngn_final m5 ps PB' p' hcs' dw -> ngn_finalC m5 ps PB' p' hcs' dw.
  Proof using Type. pin_using tt. intros m5 ps PB' p' hcs' dw (G5 & PC5 & REST). split; [exact G5|]. split; [apply PCAPR_closable_of; exact PC5| exact REST]. Qed.

  (* [comment removed for export] *)
  Lemma ngn_ret_m1 :
    forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (PB' : list (cblock (hptr:=hptr))) (p' : pcap hptr hptr) (h : pkthdr) (hcs' : list cell) (dw : cell) (dj : list byte) (ccs : list cell),
      stk ssegs m5 lo (bv_unsigned sp + -160) ->
      rw_cells ssegs m5 (bv_unsigned sp + -160) (ngn_frame dj ccs) -> cells_size ccs = 24%nat -> mem_inv ssegs m5 ->
      ngn_finalC m5 ps PB' p' hcs' dw ->
      implM ssegs (mret ((-1)%Z, h, p')) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) x1 a0' a1' a2' a3' a4' a5' a6' a7'
                 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 NGN_EPILOGUE) fc None m5 (seg_rom ssegs)).
  Proof using BU. pin_using (fun (BU : unit) => tt).
    intros until ccs. intros ST5 FR5 Hccs MI5 (G5 & PC5 & AG5 & HH & Hh & HD & Hd & OF).
    apply (implM_ret ssegs). eapply ngn_epilogue; [exact ST5 | exact FR5 | exact Hccs | exact MI5 |].
    intros t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' ST6.
    subst POSTQ. unfold next_packet_post. exists (Z_to_bv 64 (-1)), m5, PB', dw.
    split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
    split; [exact OF|]. split; [exact MI5|]. split; [exact ST6|]. split; [exact AG5|]. split; [exact G5|].
    split; [intros X; exfalso; lia|]. split; [intros _; exact PC5|].
    split; [reflexivity|]. split; [lia|]. split; [intros X; lia|]. split; [intros _; exists hcs'; split; [exact Hh| exact HH]|].
    split; [exact HD| exact Hd].
  Qed.

  (* [comment removed for export] *)
  Lemma ngn_ret_0 :
    forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (PB' : list (cblock (hptr:=hptr))) (p' : pcap hptr hptr) (h : pkthdr) (hcs' : list cell) (dw : cell) (dj : list byte) (ccs : list cell),
      stk ssegs m5 lo (bv_unsigned sp + -160) ->
      rw_cells ssegs m5 (bv_unsigned sp + -160) (ngn_frame dj ccs) -> cells_size ccs = 24%nat -> mem_inv ssegs m5 ->
      ngn_final m5 ps PB' p' hcs' dw ->
      implM ssegs (mret (0%Z, h, p')) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' (Z_to_bv 64 0) x1 a0' a1' a2' a3' a4' a5' a6' a7'
                 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 NGN_EPILOGUE) fc None m5 (seg_rom ssegs)).
  Proof using BU. pin_using (fun (BU : unit) => tt).
    intros until ccs. intros ST5 FR5 Hccs MI5 (G5 & PC5 & AG5 & HH & Hh & HD & Hd & OF).
    apply (implM_ret ssegs). eapply ngn_epilogue; [exact ST5 | exact FR5 | exact Hccs | exact MI5 |].
    intros t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' ST6.
    subst POSTQ. unfold next_packet_post. exists (Z_to_bv 64 0), m5, PB', dw.
    split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
    split; [exact OF|]. split; [exact MI5|]. split; [exact ST6|]. split; [exact AG5|]. split; [exact G5|].
    split; [intros _; exact PC5|]. split; [intros X; exfalso; lia|].
    split; [reflexivity|]. split; [lia|]. split; [intros X; lia|]. split; [intros _; exists hcs'; split; [exact Hh| exact HH]|].
    split; [exact HD| exact Hd].
  Qed.

  (* [comment removed for export] *)
  Lemma ngn_ret_1 :
    forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (PB' : list (cblock (hptr:=hptr))) (p' : pcap hptr hptr) (h : pkthdr) (dw : cell) (dj : list byte) (ccs : list cell),
      stk ssegs m5 lo (bv_unsigned sp + -160) ->
      rw_cells ssegs m5 (bv_unsigned sp + -160) (ngn_frame dj ccs) -> cells_size ccs = 24%nat -> mem_inv ssegs m5 ->
      ngn_final m5 ps PB' p' (hdr_cells h) dw -> (0 <= h_caplen h < 2^32)%Z -> (0 <= h_len h < 2^32)%Z ->
      implM ssegs (mret (1%Z, h, p')) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' x0 x1 a0' a1' a2' a3' a4' a5' a6' a7'
                 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 0x17ae0) fc None m5 (seg_rom ssegs)).
  Proof using BU. pin_using (fun (BU : unit) => tt).
    intros until ccs. intros ST5 FR5 Hccs MI5 (G5 & PC5 & AG5 & HH & Hh & HD & Hd & OF) HC HL.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    apply (implM_ret ssegs). hide HH. hide HD. hide FR5.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl ssegs m5) as WM.
    do 2 step. unhide FR5. eapply ngn_epilogue; [exact ST5 | exact FR5 | exact Hccs | exact MI5 |].
    intros t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' ST6. unhide HH. unhide HD.
    subst POSTQ. unfold next_packet_post. exists (Z_to_bv 64 1), m5, PB', dw.
    split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
    split; [exact OF|]. split; [exact MI5|]. split; [exact ST6|]. split; [exact AG5|]. split; [exact G5|].
    split; [intros _; exact PC5|]. split; [intros X; exfalso; lia|].
    split; [reflexivity|]. split; [lia|]. split; [intros _; split; [exact HH| split; [exact HC| exact HL]]|]. split; [intros X; exfalso; lia|].
    split; [exact HD| exact Hd].
  Qed.

  (* [comment removed for export] *)
  Lemma ngn_CLc_facts : forall ps PB' m5 a, GIo K R ps (CLc ++ PB') FB m5 -> in_block CLc a -> (0 < a < CEILZ)%Z /\ ~ in_block PB' a.
  Proof using Type. pin_using tt. intros. eapply GIo_CLc_facts; eassumption. Qed.

  (* [comment removed for export] *)
  Lemma ngn_snp_call :
    forall (RA : Z) (t0' t1' t2' x0 a3' a4' a5' a6' a7' x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (PB' : list (cblock (hptr:=hptr))) (p' : pcap hptr hptr) (hcs' : list cell) (dw : cell) (dj : list byte) (ccs : list cell)
           (FMTA : Z) (fs : string) (args : list farg) (Q : machine_state -> Prop),
      stk ssegs m5 lo (bv_unsigned sp + -160) ->
      rw_cells ssegs m5 (bv_unsigned sp + -160) (ngn_frame dj ccs) -> cells_size ccs = 24%nat -> mem_inv ssegs m5 ->
      ngn_finalC m5 ps PB' p' hcs' dw ->
      fmt_at m5 FMTA fs -> fmt_ok fs args = true -> (length args <= 3)%nat ->
      Forall2 (farg_word R (CLc ++ PB') (bv_unsigned sp + -160) (P + 216) 256 m5) args (firstn (length args) [a3'; a4'; a5']) ->
      (0 <= RA < 2^64)%Z -> (RA mod 2 = 0)%Z ->
      (forall (m6 : mem) (t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' : word),
          stk ssegs m6 lo (bv_unsigned sp + -160) -> rw_cells ssegs m6 (bv_unsigned sp + -160) (ngn_frame dj ccs) -> mem_inv ssegs m6 ->
          (forall e, ngn_finalC m6 ps PB' (set_errbuf e p') hcs' dw) ->
          evt ssegs Q (MS (mkR (Z_to_bv 64 RA) (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0'' t1'' t2'' x0 x1 a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7''
                           x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3'' t4'' t5'' t6'') F (Z_to_bv 64 RA) fc None m6 (seg_rom ssegs))) ->
      evt ssegs Q
        (MS (mkR (Z_to_bv 64 RA) (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' x0 x1
                 (Z_to_bv 64 (P + 216)) (Z_to_bv 64 256) (Z_to_bv 64 FMTA) a3' a4' a5' a6' a7'
                 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 SNPRINTF_ENTRY) fc None m5 (seg_rom ssegs)).
  Proof using AD AH ALN BU HFL LO P1 P4 P5 R1 R2 SFL SNPRINTF SPM SPW TP. pin_using (fun (AD AH ALN BU HFL LO P1 P4 P5 R1 R2 SFL SNPRINTF SPM SPW TP : unit) => tt).
    intros until Q. intros ST5 FR5 Hccs MI5 (G5 & PC5 & AG5 & HH & Hh & HD & Hd & OF5) FMT5 FOK LA FW RA64 RAE HK.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof PC5 as (Afx & _ & (Bx & Ix & jx & padx & bsx & EPB & CELLS & _ & _ & _ & _ & WF)).
    pose proof (psize_pos p') as PS.
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G5 ltac:(rewrite EPB; left; reflexivity)) as (K1 & K2 & K3 & K4 & K5 & K6).
    apply pcap_cells_split4 in CELLS as (_ & CE & _ & _); [|reflexivity].
    apply (rw_cells_split_CB ssegs m5 _ [] 304 _ [] [256; 48]%nat) in CE; [|reflexivity]. cbn [mk_CB_cells app] in CE.
    destruct (rw_cells_cut _ _ _ 1 CE) as [CE1 _]. clear CE. cbn [firstn skipn cells_size csize Nat.add] in CE1.
    assert (HinP : forall a, (P + 216 <= a < P + 216 + 256)%Z -> in_block (CLc ++ PB') a).
    { intros a Ha. apply in_block_app. right. rewrite EPB. unfold pcap_blocks, in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    name_sp sp (-160)%Z.
    eapply evt_cut.
    { eapply (SNPRINTF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R ps (CLc ++ PB') FB lo (P + 216)%Z 256%Z FMTA fs args (firstn 256 (pj_g jx)));
        [| reflexivity | reflexivity | reflexivity | lia | exact FMT5 | exact FOK | exact LA | rewrite Hsp; exact FW | exact CE1 | left; exact HinP].
      split; [exact G5|]. split; [rewrite Hsp; exact ST5|]. split; [unfold rc_lo; lia|]. split; [unfold STDIO_STACK; rewrite Hsp; lia|].
      split; [rewrite Hsp; lia|]. split; [exact MI5|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
    cbv beta. intros ms' PO. destruct PO as (av & m6 & junk6 & E & MU6 & WM6 & MI6 & ST6 & -> & HEB6).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 RA)) with (Z_to_bv 64 RA) by (symmetry; apply ret_pc_even; [exact RA64| exact RAE]).
    unfold STDIO_STACK in MU6.
    assert (AGS : agrees_on (fun a => outside [(bv_unsigned sp + -160 - 65536, bv_unsigned sp + -160); (P + 216, P + 216 + 256)]%Z a) m5 m6)
      by (eapply agrees_on_of_munch; [exact MU6 | exact WM6 | intros a _ Ho; exact Ho]).
    apply (agrees_rw_cells _ _ _ _ _ AGS) in FR5; [| intros a Ha; unfold ngn_frame in Ha; rewrite !cells_size_app in Ha; cbn [outside cells_size csize Nat.add] in *; rewrite Hccs in Ha; unfold rc_lo in LO; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGS) in HH; [| intros a Ha; rewrite Hh in Ha; cbn [outside]; unfold rc_lo in LO; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGS) in HD; [| intros a Ha; cbn [cells_size] in Ha; rewrite Hd in Ha; cbn [outside]; unfold rc_lo in LO; lia].
    assert (G6 : GIo K R ps (CLc ++ PB') FB m6).
    { eapply (GIo_pcap_frame K HFL SFL); [exact G5 | exact MU6 | exact WM6 |].
      apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia|]. apply Forall_cons; [| apply Forall_nil].
      right. rewrite EPB. unfold iv_in_block, pcap_blocks. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    assert (PC6 : forall e, PCAPR_closable (hptr:=hptr) P (set_errbuf e p') PB' FB m6).
    { intros e. eapply (PCAPRC_errbuf _ _ _ _ _ _ _ _ _ _ _ _ G5 PC5 AGS); [| exact HEB6 | pose proof (snprintf_length 256 fs args); cbn [cells_size csize Nat.add]; lia].
      intros a Ha Hn. cbn [outside]. pose proof (in_PB_below K _ _ _ _ _ _ _ G5 Ha). unfold rc_lo in LO. lia. }
    assert (AG6 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m6).
    { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [exact AGS|]. intros a [[Ha|Ha] _]; cbn [outside]; [unfold rc_lo in LO; lia|].
      destruct (ngn_CLc_facts _ _ _ _ G5 Ha) as [Hc Hnb]. split; [unfold rc_lo in LO; lia|]. split; [| exact Logic.I].
      intros Hin. apply Hnb. rewrite EPB. unfold pcap_blocks, in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    apply HK; [exact ST6 | exact FR5 | exact MI6 |].
    intros e. split; [exact G6|]. split; [exact (PC6 e)|]. split; [exact AG6|]. split; [exact HH|]. split; [exact Hh|]. split; [exact HD|]. split; [exact Hd| exact OF5].
  Qed.

  (* [comment removed for export] *)
  Lemma ngn_snp :
    forall (t0' t1' t2' a3' a4' a5' a6' a7' x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (PB' : list (cblock (hptr:=hptr))) (p' : pcap hptr hptr) (h : pkthdr) (hcs' : list cell) (dw : cell) (dj : list byte) (ccs : list cell)
           (FMTA : Z) (fs : string) (args : list farg) (e : list Z),
      stk ssegs m5 lo (bv_unsigned sp + -160) ->
      rw_cells ssegs m5 (bv_unsigned sp + -160) (ngn_frame dj ccs) -> cells_size ccs = 24%nat -> mem_inv ssegs m5 ->
      ngn_finalC m5 ps PB' p' hcs' dw ->
      fmt_at m5 FMTA fs -> fmt_ok fs args = true -> (length args <= 3)%nat ->
      Forall2 (farg_word R (CLc ++ PB') (bv_unsigned sp + -160) (P + 216) 256 m5) args (firstn (length args) [a3'; a4'; a5']) ->
      implM ssegs (mret ((-1)%Z, h, set_errbuf e p')) ps POSTQ
        (MS (mkR (Z_to_bv 64 NGN_EPILOGUE) (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) x1
                 (Z_to_bv 64 (P + 216)) (Z_to_bv 64 256) (Z_to_bv 64 FMTA) a3' a4' a5' a6' a7'
                 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 SNPRINTF_ENTRY) fc None m5 (seg_rom ssegs)).
  Proof using AD AH ALN BU HFL LO P1 P4 P5 R1 R2 SFL SNPRINTF SPM SPW TP. pin_using (fun (AD AH ALN BU HFL LO P1 P4 P5 R1 R2 SFL SNPRINTF SPM SPW TP : unit) => tt).
    intros until e. intros ST5 FR5 Hccs MI5 FIN FMT5 FOK LA FW.
    unfold implM. iprefix. unfold NGN_EPILOGUE.
    eapply ngn_snp_call; [exact ST5 | exact FR5 | exact Hccs | exact MI5 | exact FIN | exact FMT5 | exact FOK | exact LA | exact FW | lia | reflexivity |].
    intros m6 t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' ST6 FR6 MI6 FIN6.
    apply evt_done. eapply ngn_ret_m1; [exact ST6 | exact FR6 | exact Hccs | exact MI6 | exact (FIN6 e)].
  Qed.

  (* [comment removed for export] *)
  Lemma ngn_mcp :
    forall (ra' t0' t1' t2' a0' a3' a4' a5' a6' a7' x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (PB' : list (cblock (hptr:=hptr))) (p' : pcap hptr hptr) (h : pkthdr) (hcs' : list cell) (dw : cell) (dj : list byte) (ccs : list cell)
           (STR n : Z) (src : list byte) (e : list Z),
      stk ssegs m5 lo (bv_unsigned sp + -160) ->
      rw_cells ssegs m5 (bv_unsigned sp + -160) (ngn_frame dj ccs) -> cells_size ccs = 24%nat -> mem_inv ssegs m5 ->
      ngn_finalC m5 ps PB' p' hcs' dw ->
      bytes_at ssegs m5 STR src -> length src = Z.to_nat n -> (0 <= n <= 256)%Z -> (0x10000 <= STR /\ STR + n <= 0x13000)%Z ->
      implM ssegs (mret ((-1)%Z, h, set_errbuf e p')) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 (P + 216))
                 a0' (Z_to_bv 64 STR) (Z_to_bv 64 n) a3' a4' a5' a6' a7'
                 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 0x176a4) fc None m5 (seg_rom ssegs)).
  Proof using AD AH ALN BU HFL LO P1 P4 P5 P6 R1 R2 SFL SPW. pin_using (fun (AD AH ALN BU HFL LO P1 P4 P5 P6 R1 R2 SFL SPW : unit) => tt).
    intros until e. intros ST5 FR5 Hccs MI5 (G5 & PC5 & AG5 & HH & Hh & HD & Hd & OF5) SRC LEN Hn HSTR.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof PC5 as (Afx & _ & (Bx & Ix & jx & padx & bsx & EPB & CELLS & _ & _ & _ & _ & WF)).
    pose proof (psize_pos p') as PS.
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G5 ltac:(rewrite EPB; left; reflexivity)) as (K1 & K2 & K3 & K4 & K5 & K6).
    apply pcap_cells_split4 in CELLS as (_ & CE & _ & _); [|reflexivity].
    apply (rw_cells_split_CB ssegs m5 _ [] 304 _ [] [Z.to_nat n; 256 - Z.to_nat n; 48]%nat) in CE; [|cbn; lia]. cbn [mk_CB_cells app] in CE.
    destruct (rw_cells_cut _ _ _ 1 CE) as [CE1 CE23]. clear CE. cbn [firstn skipn cells_size csize Nat.add] in CE1, CE23.
    destruct (rw_cells_cut _ _ _ 1 CE23) as [CE2 _]. clear CE23. cbn [firstn skipn cells_size csize Nat.add] in CE2.
    unfold implM. iprefix. hide FR5. hide HH. hide HD. hide CE2.
    pose proof (munch_refl [(P + 216, P + 216 + n)]%Z m5) as MU. pose proof (wmono_refl ssegs m5) as WM.
    step. step.
    eapply evt_cut.
    { eapply (memcpy_specZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m5 (P + 216)%Z STR n src (firstn (Z.to_nat n) (pj_g jx)));
        [reflexivity | reflexivity | reflexivity | exact SRC | exact LEN | lia | exact CE1 | lia | lia | lia | exact MI5]. }
    cbv beta. intros ms' PO. destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & m6 & -> & MU6 & WM6 & MI6 & HEB6 & _).
    replace (ret_pc (Z_to_bv 64 95916)) with (Z_to_bv 64 95916) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    unhide FR5. unhide HH. unhide HD. unhide CE2.
    assert (AGS : agrees_on (fun a => outside [(P + 216, P + 216 + n)]%Z a) m5 m6)
      by (eapply agrees_on_of_munch; [exact MU6 | exact WM6 | intros a _ Ho; exact Ho]).
    apply (agrees_rw_cells _ _ _ _ _ AGS) in FR5; [| intros a Ha; unfold ngn_frame in Ha; rewrite !cells_size_app in Ha; cbn [outside cells_size csize Nat.add] in *; rewrite Hccs in Ha; unfold rc_lo in LO; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGS) in HH; [| intros a Ha; rewrite Hh in Ha; cbn [outside]; unfold rc_lo in LO; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGS) in HD; [| intros a Ha; cbn [cells_size] in Ha; rewrite Hd in Ha; cbn [outside]; unfold rc_lo in LO; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGS) in CE2; [| intros a Ha; cbn [outside cells_size csize Nat.add] in *; lia].
    pose proof (agrees_stk _ _ _ _ _ AGS ST5 ltac:(intros a Ha; cbn [outside]; unfold rc_lo in LO; lia)) as ST6.
    pose proof (rw_cells_uncut _ _ _ _ _ HEB6 CE2 ltac:(cbn [cells_size csize Nat.add]; lia)) as HEB. cbn [app] in HEB.
    assert (G6 : GIo K R ps (CLc ++ PB') FB m6).
    { eapply (GIo_pcap_frame K HFL SFL); [exact G5 | exact MU6 | exact WM6 |].
      apply Forall_cons; [| apply Forall_nil].
      right. rewrite EPB. unfold iv_in_block, pcap_blocks. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    assert (PC6 : PCAPR_closable (hptr:=hptr) P (set_errbuf e p') PB' FB m6).
    { eapply (PCAPRC_errbuf _ _ _ _ _ _ _ _ _ _ _ _ G5 PC5 AGS); [| exact HEB | cbn [cells_size csize Nat.add]; lia].
      intros a Ha Hna. cbn [outside]. lia. }
    assert (AG6 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m6).
    { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [exact AGS|]. intros a [[Ha|Ha] _]; cbn [outside]; [unfold rc_lo in LO; lia|].
      destruct (ngn_CLc_facts _ _ _ _ G5 Ha) as [Hc Hnb]. split; [| exact Logic.I].
      intros Hin. apply Hnb. rewrite EPB. unfold pcap_blocks, in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    clear MU WM. pose proof (munch_refl ([] : list (Z * Z)) m6) as MU. pose proof (wmono_refl ssegs m6) as WM.
    hide FR5. hide HH. hide HD. hide HEB.
    step. unhide FR5. unhide HH. unhide HD.
    apply evt_done. eapply ngn_ret_m1; [exact ST6 | exact FR5 | exact Hccs | exact MI6 |].
    split; [exact G6|]. split; [exact PC6|]. split; [exact AG6|]. split; [exact HH|]. split; [exact Hh|]. split; [exact HD|]. split; [exact Hd| exact OF5].
  Qed.

End NgnCtx.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.Pcap_iface_pp.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface_ng.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcapng_blkA__S3.SfNgKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_small.TwB.
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

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Definition NGN_FMT_TOO_SHORT : Z := 0x10cd0.    (* [comment removed for export] *)
Definition NGN_FMT_MAJOR : Z := 0x10373.        (* [comment removed for export] *)
Definition NGN_STR_SECTIONS : Z := 0x109c7.     (* [comment removed for export] *)
Definition NGN_STR_BADBOM : Z := 0x10b82.       (* [comment removed for export] *)
Definition NGN_FMT_IFTYPE : Z := 0x10da4.       (* [comment removed for export] *)
Definition NGN_FMT_IFSNAP : Z := 0x10d3e.       (* [comment removed for export] *)
Definition NGN_FMT_NOIDB : Z := 0x10bbb.        (* [comment removed for export] *)
Definition NGN_FMT_CAPLEN : Z := 0x1095e.       (* [comment removed for export] *)
Definition NGN_EPILOGUE : Z := 0x17d30.
Definition NGN_LOOP : Z := 0x17a98.

(* [comment removed for export] *)
(* [comment removed for export] *)
End WithCeil.

Ltac merge_cells H k n :=
  lazymatch type of H with
  | rw_cells ?segs ?m ?A ?cs =>
      let pre := eval cbv beta iota delta [firstn skipn] in (firstn k cs) in
      let mid := eval cbv beta iota delta [firstn skipn] in (firstn n (skipn k cs)) in
      let post := eval cbv beta iota delta [firstn skipn Nat.add] in (skipn (k + n) cs) in
      change cs with (pre ++ mid ++ post) in H;
      apply (rw_cells_merge segs m A pre mid post) in H;
      cbn [cells_size csize cells_bytes cbytes Nat.add app] in H
  end.
(* [comment removed for export] *)
Ltac fix_lit_store :=
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
           change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
           change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) =>
           change (Z_to_le_bytes 2 z) with (le2 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
           change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]; mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
           change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]; mem_after_store
       end).
Ltac pstep := step; fix_lit_store.
(* [comment removed for export] *)
Ltac norm_addr H P :=
  lazymatch type of H with
  | rw_cells _ _ (?b + Z.of_nat ?n)%Z _ =>
      lazymatch b with
      | (P + ?k0)%Z => let k := eval vm_compute in (k0 + Z.of_nat n)%Z in replace (b + Z.of_nat n)%Z with (P + k)%Z in H by lia
      | P => let k := eval vm_compute in (Z.of_nat n) in replace (P + Z.of_nat n)%Z with (P + k)%Z in H by lia
      end
  end.
(* [comment removed for export] *)
Ltac cut_cells H k H1 P :=
  let H2 := fresh "TMP" in
  destruct (rw_cells_cut _ _ _ k H) as [H1 H2]; clear H; cbn [firstn skipn cells_size csize Nat.add] in H1, H2;
  norm_addr H2 P; rename H2 into H.
(* [comment removed for export] *)
Ltac merge_all H :=
  lazymatch type of H with
  | rw_cells ?s ?m ?A ?cs =>
      change cs with ([] ++ cs ++ []) in H; apply (rw_cells_merge s m A [] cs []) in H;
      cbn [cells_size csize cells_bytes cbytes Nat.add app] in H
  end.
(* [comment removed for export] *)
Ltac join_cells H1 H2 :=
  lazymatch type of H1 with rw_cells ?s ?m ?A1 ?cs1 =>
  lazymatch type of H2 with rw_cells _ _ ?A2 ?cs2 =>
    let J := fresh "J" in
    pose proof (rw_cells_uncut m A1 cs1 cs2 A2 H1 H2 ltac:(cbn [cells_size csize Nat.add]; lia)) as J;
    clear H1 H2; cbn [app] in J; rename J into H1
  end end.

Section WithCeil.
Context {CEILV : CEIL}.
Lemma snprintf_length : forall n f args, (length (Fmt.snprintf n f args) <= Z.to_nat (n - 1))%nat.
Proof using Type. pin_using tt. intros. unfold Fmt.snprintf, snprintf_out. apply firstn_le_length. Qed.

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
  (* [comment removed for export] *)
  Definition pv (bq : hptr) (alloc : Z) (data eb : list Z) (s : pcap_ng_sf) (i : option hptr) : pcap hptr hptr :=
    mkPcap self f bufsize alloc bq data swapped vmaj vmin snapshot linktype ltext prec brk eb header (PrivNg s i).
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
  (* [comment removed for export] *)
  Definition ngn_frame (dj : list byte) (ccs : list cell) : list cell :=
    [C8 (Z_to_bv 64 DA); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 HA); C8 (Z_to_bv 64 (P + 648))] ++ ccs ++
    [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Definition ngn_epilogue__stmt : Prop := forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' : word)
           (m5 : mem) (dj : list byte) (ccs : list cell) (Q : machine_state -> Prop),
      stk usegs m5 lo (bv_unsigned sp + -160) ->
      rw_cells usegs m5 (bv_unsigned sp + -160) (ngn_frame dj ccs) -> cells_size ccs = 24%nat -> mem_inv usegs m5 ->
      (forall t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'',
          stk usegs m5 lo (bv_unsigned sp) ->
          Q (MS (mkR ra sp gp tp t0'' t1'' t2'' s0 s1 x0 a1'' a2'' a3'' a4'' a5'' a6'' a7'' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3'' t4'' t5'' t6'')
                F (ret_pc ra) fc None m5 (seg_rom usegs))) ->
      evt usegs Q
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' x0 x1 a0' a1' a2' a3' a4' a5' a6' a7'
                 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 NGN_EPILOGUE) fc None m5 (seg_rom usegs)).
  Section Sz2.
  Variables ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' m5 dj ccs Q : ltac2:(SecDiet.SzSec.tyM 'ngn_epilogue__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma ngn_epilogue__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_epilogue__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using BU. pin_using (fun (BU : unit) => tt).
 intros ST5 FR5 Hccs MI5 HQ.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl usegs m5) as WM.
    unfold ngn_frame in FR5.
    apply rw_cells_app in FR5 as [FRJ FR5]. apply rw_cells_app in FR5 as [FRC FRS].
    cbn [cells_size csize Nat.add] in FRS, FRC. rewrite Hccs in FRS.
    replace (bv_unsigned sp + -160 + Z.of_nat 32 + Z.of_nat 24)%Z with (bv_unsigned sp + -104)%Z in FRS by lia.
    replace (bv_unsigned sp + -160 + Z.of_nat 32)%Z with (bv_unsigned sp + -128)%Z in FRC by lia.
    destruct (rw_cells_forget _ _ _ _ FRC) as [cj FRC']. clear FRC. rewrite Hccs in FRC'.
    unfold NGN_EPILOGUE. do 16 step.
    release_frame FRJ ST5 (bv_unsigned sp + -128)%Z. release_frame FRC' ST5 (bv_unsigned sp + -104)%Z. release_frame FRS ST5 (bv_unsigned sp).
    apply evt_done. apply HQ. exact ST5.
  Qed.
  End Sz2.
  Lemma ngn_epilogue : ltac:(let t := eval cbv delta [ngn_epilogue__stmt] in ngn_epilogue__stmt in exact t).
  Proof using BU. intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' m5 dj ccs Q. ltac2:(SecDiet.SzSec.closeP 'ngn_epilogue__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition PCAPRC_errbuf__stmt : Prop := forall Rx sx CLx Px (p : pcap hptr hptr) PB FBx (mx mx' : mem) (Q : Z -> Prop) cs e,
    GIo K Rx sx (CLx ++ PB) FBx mx -> PCAPR_closable (hptr:=hptr) Px p PB FBx mx -> agrees_on Q mx mx' ->
    (forall a, in_block PB a -> ~ (Px + 216 <= a < Px + 472)%Z -> Q a) ->
    rw_cells usegs mx' (Px + 216) cs -> cells_size cs = 256%nat ->
    PCAPR_closable (hptr:=hptr) Px (set_errbuf e p) PB FBx mx'.
  Section Sz3.
  Variables Rx sx CLx Px p PB FBx mx mx' Q cs e : ltac2:(SecDiet.SzSec.tyM 'PCAPRC_errbuf__stmt "vvvvvvvvvvvv" @Rx).
  Lemma PCAPRC_errbuf__body : ltac2:(SecDiet.SzSec.bodyP 'PCAPRC_errbuf__stmt "vvvvvvvvvvvv").
  Proof using AD AH ALN BU LO P1 R1 R2 SPW. pin_using (fun (AD AH ALN BU LO P1 R1 R2 SPW : unit) => tt).
    intros G PC AG HQ HCS Hsz.
    destruct PC as (Afx & Hin & (Bx & I & jx & padx & bsx & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    pose proof (psize_pos p) as PS. pose proof (PB_apart K _ _ _ _ _ _ _ _ _ _ G EPB) as [APB API].
    assert (Q1 : forall a, (Px <= a < Px + psize p)%Z -> ~ (Px + 216 <= a < Px + 472)%Z -> Q a).
    { intros a Ha Hn. apply HQ; [|exact Hn]. rewrite EPB. unfold pcap_blocks, in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. exact Ha. }
    apply pcap_cells_split4 in CELLS as (CA & CE & CH & CO); [|reflexivity].
    apply (rw_cells_split_CB usegs mx _ [] 304 _ [] [256; 48]%nat) in CE; [|reflexivity]. cbn [mk_CB_cells app] in CE.
    destruct (rw_cells_cut _ _ _ 1 CE) as [_ CE2]. clear CE. cbn [firstn skipn cells_size csize Nat.add] in CE2.
    replace (Px + 216 + Z.of_nat 256)%Z with (Px + 472)%Z in CE2 by lia.
    apply (agrees_rw_cells _ _ _ _ _ AG) in CA; [| intros a Ha; rewrite (pc_pre_size p Px Bx (C8 (Z_to_bv 64 Afx)) jx eq_refl) in Ha; apply Q1; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG) in CH; [| intros a Ha; cbn [cells_size csize hdr_cells Nat.add] in Ha; apply Q1; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG) in CO; [| intros a Ha; cbn [cells_size csize pc_ops Nat.add] in Ha; apply Q1; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG) in CE2; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply Q1; lia].
    pose proof (rw_cells_uncut _ _ _ _ _ HCS CE2 ltac:(rewrite Hsz; lia)) as CE'.
    pose proof WF as (_ & _ & W3 & _).
    destruct (pcap_aux_closable_agree p Px Bx I padx bsx mx mx' Q AG) as (BUF' & PRIV' & IFS');
      [ intros a Ha; apply HQ; [rewrite EPB; unfold pcap_blocks, in_block; apply Exists_cons_tl, Exists_cons_hd; cbn [cb_addr cb_size fst snd]; exact Ha| lia]
      | intros a Ha; apply Q1; unfold PCAP_PRIV_OFF in Ha; lia
      | intros sg q Hq a Ha; destruct (API sg q Hq) as [X1 X2]; apply HQ;
          [rewrite EPB; unfold pcap_blocks, in_block; rewrite Hq; do 2 apply Exists_cons_tl; apply Exists_cons_hd; cbn [cb_addr cb_size fst snd]; exact Ha| lia]
      | lia | exact BUF | exact PRIV | exact IFS |].
    exists Afx. split; [destruct p; exact Hin|].
    exists Bx, I, (set_pj_g (cells_bytes (cs ++ [CB 48 (firstn 48 (skipn 256 (pj_g jx)))])) jx), padx, bsx.
    split; [rewrite EPB; destruct p; reflexivity|].
    split. { pose proof (pcap_cells_join4 mx' Px p Bx (C8 (Z_to_bv 64 Afx)) (C8 (Z_to_bv 64 (pk_stats PK))) (C8 (Z_to_bv 64 (pk_oneshot PK))) jx _ (pc_header p)
                           eq_refl CA CE' ltac:(rewrite cells_size_app, Hsz; reflexivity) CH CO) as J.
             replace (set_header (pc_header p) p) with p in J by (destruct p; reflexivity).
             destruct p; cbn. exact J. }
    split; [destruct p; exact PRIV'|]. split; [destruct p; exact BUF'|]. split; [destruct p; exact PFX|].
    split; [destruct p; exact IFS'|]. destruct p; exact WF.
  Qed.
  End Sz3.
  Lemma PCAPRC_errbuf : ltac:(let t := eval cbv delta [PCAPRC_errbuf__stmt] in PCAPRC_errbuf__stmt in exact t).
  Proof using AD AH ALN BU LO P1 R1 R2 SPW. intros Rx sx CLx Px p PB FBx mx mx' Q cs e. ltac2:(SecDiet.SzSec.closeP 'PCAPRC_errbuf__body "vvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition ngn_final (m5 : mem) (ps : PState H hptr) (PB' : list (cblock (hptr:=hptr))) (p' : pcap hptr hptr) (hcs' : list cell) (dw : cell) : Prop :=
    GIo K R ps (CLc ++ PB') FB m5 /\ PCAPR (hptr:=hptr) P p' PB' FB m5
    /\ agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5
    /\ rw_cells usegs m5 HA hcs' /\ cells_size hcs' = 24%nat /\ rw_cells usegs m5 DA [dw] /\ csize dw = 8%nat /\ ps_outfile ps = o.
  (* [comment removed for export] *)
  Definition ngn_finalC (m5 : mem) (ps : PState H hptr) (PB' : list (cblock (hptr:=hptr))) (p' : pcap hptr hptr) (hcs' : list cell) (dw : cell) : Prop :=
    GIo K R ps (CLc ++ PB') FB m5 /\ PCAPR_closable (hptr:=hptr) P p' PB' FB m5
    /\ agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5
    /\ rw_cells usegs m5 HA hcs' /\ cells_size hcs' = 24%nat /\ rw_cells usegs m5 DA [dw] /\ csize dw = 8%nat /\ ps_outfile ps = o.

  Lemma ngn_final_C : forall m5 ps PB' p' hcs' dw, ngn_final m5 ps PB' p' hcs' dw -> ngn_finalC m5 ps PB' p' hcs' dw.
  Proof using Type. pin_using tt. intros m5 ps PB' p' hcs' dw (G5 & PC5 & REST). split; [exact G5|]. split; [apply PCAPR_closable_of; exact PC5| exact REST]. Qed.

  (* [comment removed for export] *)
  Definition ngn_ret_m1__stmt : Prop := forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (PB' : list (cblock (hptr:=hptr))) (p' : pcap hptr hptr) (h : pkthdr) (hcs' : list cell) (dw : cell) (dj : list byte) (ccs : list cell),
      stk usegs m5 lo (bv_unsigned sp + -160) ->
      rw_cells usegs m5 (bv_unsigned sp + -160) (ngn_frame dj ccs) -> cells_size ccs = 24%nat -> mem_inv usegs m5 ->
      ngn_finalC m5 ps PB' p' hcs' dw ->
      implM usegs (mret ((-1)%Z, h, p')) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) x1 a0' a1' a2' a3' a4' a5' a6' a7'
                 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 NGN_EPILOGUE) fc None m5 (seg_rom usegs)).
  Section Sz5.
  Variables ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' m5 ps PB' p' h hcs' dw dj ccs : ltac2:(SecDiet.SzSec.tyM 'ngn_ret_m1__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma ngn_ret_m1__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_ret_m1__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using BU. pin_using (fun (BU : unit) => tt).
 intros ST5 FR5 Hccs MI5 (G5 & PC5 & AG5 & HH & Hh & HD & Hd & OF).
    apply (implM_ret usegs). eapply ngn_epilogue; [exact ST5 | exact FR5 | exact Hccs | exact MI5 |].
    intros t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' ST6.
    subst POSTQ. unfold next_packet_post. exists (Z_to_bv 64 (-1)), m5, PB', dw.
    split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
    split; [exact OF|]. split; [exact MI5|]. split; [exact ST6|]. split; [exact AG5|]. split; [exact G5|].
    split; [intros X; exfalso; lia|]. split; [intros _; exact PC5|].
    split; [reflexivity|]. split; [lia|]. split; [intros X; lia|]. split; [intros _; exists hcs'; split; [exact Hh| exact HH]|].
    split; [exact HD| exact Hd].
  Qed.
  End Sz5.
  Lemma ngn_ret_m1 : ltac:(let t := eval cbv delta [ngn_ret_m1__stmt] in ngn_ret_m1__stmt in exact t).
  Proof using BU. intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' m5 ps PB' p' h hcs' dw dj ccs. ltac2:(SecDiet.SzSec.closeP 'ngn_ret_m1__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition ngn_ret_0__stmt : Prop := forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (PB' : list (cblock (hptr:=hptr))) (p' : pcap hptr hptr) (h : pkthdr) (hcs' : list cell) (dw : cell) (dj : list byte) (ccs : list cell),
      stk usegs m5 lo (bv_unsigned sp + -160) ->
      rw_cells usegs m5 (bv_unsigned sp + -160) (ngn_frame dj ccs) -> cells_size ccs = 24%nat -> mem_inv usegs m5 ->
      ngn_final m5 ps PB' p' hcs' dw ->
      implM usegs (mret (0%Z, h, p')) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' (Z_to_bv 64 0) x1 a0' a1' a2' a3' a4' a5' a6' a7'
                 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 NGN_EPILOGUE) fc None m5 (seg_rom usegs)).
  Section Sz6.
  Variables ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' m5 ps PB' p' h hcs' dw dj ccs : ltac2:(SecDiet.SzSec.tyM 'ngn_ret_0__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma ngn_ret_0__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_ret_0__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using BU. pin_using (fun (BU : unit) => tt).
 intros ST5 FR5 Hccs MI5 (G5 & PC5 & AG5 & HH & Hh & HD & Hd & OF).
    apply (implM_ret usegs). eapply ngn_epilogue; [exact ST5 | exact FR5 | exact Hccs | exact MI5 |].
    intros t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' ST6.
    subst POSTQ. unfold next_packet_post. exists (Z_to_bv 64 0), m5, PB', dw.
    split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
    split; [exact OF|]. split; [exact MI5|]. split; [exact ST6|]. split; [exact AG5|]. split; [exact G5|].
    split; [intros _; exact PC5|]. split; [intros X; exfalso; lia|].
    split; [reflexivity|]. split; [lia|]. split; [intros X; lia|]. split; [intros _; exists hcs'; split; [exact Hh| exact HH]|].
    split; [exact HD| exact Hd].
  Qed.
  End Sz6.
  Lemma ngn_ret_0 : ltac:(let t := eval cbv delta [ngn_ret_0__stmt] in ngn_ret_0__stmt in exact t).
  Proof using BU. intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' m5 ps PB' p' h hcs' dw dj ccs. ltac2:(SecDiet.SzSec.closeP 'ngn_ret_0__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition ngn_ret_1__stmt : Prop := forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (PB' : list (cblock (hptr:=hptr))) (p' : pcap hptr hptr) (h : pkthdr) (dw : cell) (dj : list byte) (ccs : list cell),
      stk usegs m5 lo (bv_unsigned sp + -160) ->
      rw_cells usegs m5 (bv_unsigned sp + -160) (ngn_frame dj ccs) -> cells_size ccs = 24%nat -> mem_inv usegs m5 ->
      ngn_final m5 ps PB' p' (hdr_cells h) dw -> (0 <= h_caplen h < 2^32)%Z -> (0 <= h_len h < 2^32)%Z ->
      implM usegs (mret (1%Z, h, p')) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' x0 x1 a0' a1' a2' a3' a4' a5' a6' a7'
                 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 0x18280) fc None m5 (seg_rom usegs)).
  Section Sz7.
  Variables ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' m5 ps PB' p' h dw dj ccs : ltac2:(SecDiet.SzSec.tyM 'ngn_ret_1__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma ngn_ret_1__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_ret_1__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using BU. pin_using (fun (BU : unit) => tt).
 intros ST5 FR5 Hccs MI5 (G5 & PC5 & AG5 & HH & Hh & HD & Hd & OF) HC HL.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    apply (implM_ret usegs). hide HH. hide HD. hide FR5.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl usegs m5) as WM.
    do 2 step. unhide FR5. eapply ngn_epilogue; [exact ST5 | exact FR5 | exact Hccs | exact MI5 |].
    intros t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' ST6. unhide HH. unhide HD.
    subst POSTQ. unfold next_packet_post. exists (Z_to_bv 64 1), m5, PB', dw.
    split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
    split; [exact OF|]. split; [exact MI5|]. split; [exact ST6|]. split; [exact AG5|]. split; [exact G5|].
    split; [intros _; exact PC5|]. split; [intros X; exfalso; lia|].
    split; [reflexivity|]. split; [lia|]. split; [intros _; split; [exact HH| split; [exact HC| exact HL]]|]. split; [intros X; exfalso; lia|].
    split; [exact HD| exact Hd].
  Qed.
  End Sz7.
  Lemma ngn_ret_1 : ltac:(let t := eval cbv delta [ngn_ret_1__stmt] in ngn_ret_1__stmt in exact t).
  Proof using BU. intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' m5 ps PB' p' h dw dj ccs. ltac2:(SecDiet.SzSec.closeP 'ngn_ret_1__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Lemma ngn_CLc_facts : forall ps PB' m5 a, GIo K R ps (CLc ++ PB') FB m5 -> in_block CLc a -> (0 < a < CEILZ)%Z /\ ~ in_block PB' a.
  Proof using Type. pin_using tt. intros. eapply GIo_CLc_facts; eassumption. Qed.

  (* [comment removed for export] *)
  Definition ngn_snp_call__stmt : Prop := forall (RA : Z) (t0' t1' t2' x0 a3' a4' a5' a6' a7' x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (PB' : list (cblock (hptr:=hptr))) (p' : pcap hptr hptr) (hcs' : list cell) (dw : cell) (dj : list byte) (ccs : list cell)
           (FMTA : Z) (fs : string) (args : list farg) (Q : machine_state -> Prop),
      stk usegs m5 lo (bv_unsigned sp + -160) ->
      rw_cells usegs m5 (bv_unsigned sp + -160) (ngn_frame dj ccs) -> cells_size ccs = 24%nat -> mem_inv usegs m5 ->
      ngn_finalC m5 ps PB' p' hcs' dw ->
      fmt_at m5 FMTA fs -> fmt_ok fs args = true -> (length args <= 3)%nat ->
      Forall2 (farg_word R (CLc ++ PB') (bv_unsigned sp + -160) (P + 216) 256 m5) args (firstn (length args) [a3'; a4'; a5']) ->
      (0 <= RA < 2^64)%Z -> (RA mod 2 = 0)%Z ->
      (forall (m6 : mem) (t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' : word),
          stk usegs m6 lo (bv_unsigned sp + -160) -> rw_cells usegs m6 (bv_unsigned sp + -160) (ngn_frame dj ccs) -> mem_inv usegs m6 ->
          (forall e, ngn_finalC m6 ps PB' (set_errbuf e p') hcs' dw) ->
          evt usegs Q (MS (mkR (Z_to_bv 64 RA) (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0'' t1'' t2'' x0 x1 a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7''
                           x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3'' t4'' t5'' t6'') F (Z_to_bv 64 RA) fc None m6 (seg_rom usegs))) ->
      evt usegs Q
        (MS (mkR (Z_to_bv 64 RA) (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' x0 x1
                 (Z_to_bv 64 (P + 216)) (Z_to_bv 64 256) (Z_to_bv 64 FMTA) a3' a4' a5' a6' a7'
                 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 SNPRINTF_ENTRY) fc None m5 (seg_rom usegs)).
  Section Sz9.
  Variables RA t0' t1' t2' x0 a3' a4' a5' a6' a7' x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' m5 ps PB' p' hcs' dw dj ccs FMTA fs args Q : ltac2:(SecDiet.SzSec.tyM 'ngn_snp_call__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RA).
  Lemma ngn_snp_call__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_snp_call__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AD AH ALN BU HFL LO P1 P4 P5 R1 R2 SFL SNPRINTF SPM SPW TP. pin_using (fun (AD AH ALN BU HFL LO P1 P4 P5 R1 R2 SFL SNPRINTF SPM SPW TP : unit) => tt).
 intros ST5 FR5 Hccs MI5 (G5 & PC5 & AG5 & HH & Hh & HD & Hd & OF5) FMT5 FOK LA FW RA64 RAE HK.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof PC5 as (Afx & _ & (Bx & Ix & jx & padx & bsx & EPB & CELLS & _ & _ & _ & _ & WF)).
    pose proof (psize_pos p') as PS.
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G5 ltac:(rewrite EPB; left; reflexivity)) as (K1 & K2 & K3 & K4 & K5 & K6).
    apply pcap_cells_split4 in CELLS as (_ & CE & _ & _); [|reflexivity].
    apply (rw_cells_split_CB usegs m5 _ [] 304 _ [] [256; 48]%nat) in CE; [|reflexivity]. cbn [mk_CB_cells app] in CE.
    destruct (rw_cells_cut _ _ _ 1 CE) as [CE1 _]. clear CE. cbn [firstn skipn cells_size csize Nat.add] in CE1.
    assert (HinP : forall a, (P + 216 <= a < P + 216 + 256)%Z -> in_block (CLc ++ PB') a).
    { intros a Ha. apply in_block_app. right. rewrite EPB. unfold pcap_blocks, in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    name_sp sp (-160)%Z.
    eapply evt_cut.
    { eapply (SNPRINTF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R ps (CLc ++ PB') FB lo (P + 216)%Z 256%Z FMTA fs args (firstn 256 (pj_g jx)));
        [| reflexivity | reflexivity | reflexivity | lia | exact FMT5 | exact FOK | exact LA | rewrite Hsp; exact FW | exact CE1 | left; exact HinP].
      split; [exact G5|]. split; [rewrite Hsp; exact ST5|]. split; [unfold rc_lo; lia|]. split; [unfold STDIO_STACK; rewrite Hsp; lia|].
      split; [rewrite Hsp; lia|]. split; [exact MI5|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
    cbv beta. intros ms' PO. destruct PO as (av & m6 & junk6 & E & MU6 & WM6 & MI6 & ST6 & -> & HEB6).
    unfold hpost_regs in E. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 RA)) with (Z_to_bv 64 RA) by (symmetry; apply ret_pc_even; [exact RA64| exact RAE]).
    unfold STDIO_STACK in MU6.
    assert (AGS : agrees_on (fun a => outside [(bv_unsigned sp + -160 - 65536, bv_unsigned sp + -160); (P + 216, P + 216 + 256)]%Z a) m5 m6)
      by (eapply agrees_on_of_munch; [exact MU6 | exact WM6 | intros a _ Ho; exact Ho]).
    apply (agrees_rw_cells _ _ _ _ _ AGS) in FR5; [| intros a Ha; unfold ngn_frame in Ha; rewrite !cells_size_app in Ha; cbn [outside cells_size csize Nat.add] in *; rewrite Hccs in Ha; unfold rc_lo in LO; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGS) in HH; [| intros a Ha; rewrite Hh in Ha; cbn [outside]; unfold rc_lo in LO; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGS) in HD; [| intros a Ha; cbn [cells_size] in Ha; rewrite Hd in Ha; cbn [outside]; unfold rc_lo in LO; lia].
    assert (G6 : GIo K R ps (CLc ++ PB') FB m6).
    { eapply (GIo_pcap_frame K HFL SFL); [exact G5 | exact MU6 | exact WM6 |].
      apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia|]. apply Forall_cons; [| apply Forall_nil].
      right. rewrite EPB. unfold iv_in_block, pcap_blocks. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    assert (PC6 : forall e, PCAPR_closable (hptr:=hptr) P (set_errbuf e p') PB' FB m6).
    { intros e. eapply (PCAPRC_errbuf _ _ _ _ _ _ _ _ _ _ _ _ G5 PC5 AGS); [| exact HEB6 | pose proof (snprintf_length 256 fs args); cbn [cells_size csize Nat.add]; lia].
      intros a Ha Hn. cbn [outside]. pose proof (in_PB_below K _ _ _ _ _ _ _ G5 Ha). unfold rc_lo in LO. lia. }
    assert (AG6 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m6).
    { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [exact AGS|]. intros a [[Ha|Ha] _]; cbn [outside]; [unfold rc_lo in LO; lia|].
      destruct (ngn_CLc_facts _ _ _ _ G5 Ha) as [Hc Hnb]. split; [unfold rc_lo in LO; lia|]. split; [| exact Logic.I].
      intros Hin. apply Hnb. rewrite EPB. unfold pcap_blocks, in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    apply HK; [exact ST6 | exact FR5 | exact MI6 |].
    intros e. split; [exact G6|]. split; [exact (PC6 e)|]. split; [exact AG6|]. split; [exact HH|]. split; [exact Hh|]. split; [exact HD|]. split; [exact Hd| exact OF5].
  Qed.
  End Sz9.
  Lemma ngn_snp_call : ltac:(let t := eval cbv delta [ngn_snp_call__stmt] in ngn_snp_call__stmt in exact t).
  Proof using AD AH ALN BU HFL LO P1 P4 P5 R1 R2 SFL SNPRINTF SPM SPW TP. intros RA t0' t1' t2' x0 a3' a4' a5' a6' a7' x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' m5 ps PB' p' hcs' dw dj ccs FMTA fs args Q. ltac2:(SecDiet.SzSec.closeP 'ngn_snp_call__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Lemma ngn_snp :
    forall (t0' t1' t2' a3' a4' a5' a6' a7' x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (PB' : list (cblock (hptr:=hptr))) (p' : pcap hptr hptr) (h : pkthdr) (hcs' : list cell) (dw : cell) (dj : list byte) (ccs : list cell)
           (FMTA : Z) (fs : string) (args : list farg) (e : list Z),
      stk usegs m5 lo (bv_unsigned sp + -160) ->
      rw_cells usegs m5 (bv_unsigned sp + -160) (ngn_frame dj ccs) -> cells_size ccs = 24%nat -> mem_inv usegs m5 ->
      ngn_finalC m5 ps PB' p' hcs' dw ->
      fmt_at m5 FMTA fs -> fmt_ok fs args = true -> (length args <= 3)%nat ->
      Forall2 (farg_word R (CLc ++ PB') (bv_unsigned sp + -160) (P + 216) 256 m5) args (firstn (length args) [a3'; a4'; a5']) ->
      implM usegs (mret ((-1)%Z, h, set_errbuf e p')) ps POSTQ
        (MS (mkR (Z_to_bv 64 NGN_EPILOGUE) (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) x1
                 (Z_to_bv 64 (P + 216)) (Z_to_bv 64 256) (Z_to_bv 64 FMTA) a3' a4' a5' a6' a7'
                 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 SNPRINTF_ENTRY) fc None m5 (seg_rom usegs)).
  Proof using AD AH ALN BU HFL LO P1 P4 P5 R1 R2 SFL SNPRINTF SPM SPW TP. pin_using (fun (AD AH ALN BU HFL LO P1 P4 P5 R1 R2 SFL SNPRINTF SPM SPW TP : unit) => tt).
    intros until e. intros ST5 FR5 Hccs MI5 FIN FMT5 FOK LA FW.
    unfold implM. iprefix. unfold NGN_EPILOGUE.
    eapply ngn_snp_call; [exact ST5 | exact FR5 | exact Hccs | exact MI5 | exact FIN | exact FMT5 | exact FOK | exact LA | exact FW | lia | reflexivity |].
    intros m6 t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' ST6 FR6 MI6 FIN6.
    apply evt_done. eapply ngn_ret_m1; [exact ST6 | exact FR6 | exact Hccs | exact MI6 | exact (FIN6 e)].
  Qed.

  (* [comment removed for export] *)
  Definition ngn_mcp__stmt : Prop := forall (ra' t0' t1' t2' a0' a3' a4' a5' a6' a7' x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (PB' : list (cblock (hptr:=hptr))) (p' : pcap hptr hptr) (h : pkthdr) (hcs' : list cell) (dw : cell) (dj : list byte) (ccs : list cell)
           (STR n : Z) (src : list byte) (e : list Z),
      stk usegs m5 lo (bv_unsigned sp + -160) ->
      rw_cells usegs m5 (bv_unsigned sp + -160) (ngn_frame dj ccs) -> cells_size ccs = 24%nat -> mem_inv usegs m5 ->
      ngn_finalC m5 ps PB' p' hcs' dw ->
      bytes_at usegs m5 STR src -> length src = Z.to_nat n -> (0 <= n <= 256)%Z -> (0x10000 <= STR /\ STR + n <= 0x13000)%Z ->
      implM usegs (mret ((-1)%Z, h, set_errbuf e p')) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 (P + 216))
                 a0' (Z_to_bv 64 STR) (Z_to_bv 64 n) a3' a4' a5' a6' a7'
                 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6') F (Z_to_bv 64 0x17d00) fc None m5 (seg_rom usegs)).
  Section Sz11.
  Variables ra' t0' t1' t2' a0' a3' a4' a5' a6' a7' x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' m5 ps PB' p' h hcs' dw dj ccs STR n src e : ltac2:(SecDiet.SzSec.tyM 'ngn_mcp__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma ngn_mcp__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_mcp__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AD AH ALN BU HFL LO P1 P4 P5 P6 R1 R2 SFL SPW. pin_using (fun (AD AH ALN BU HFL LO P1 P4 P5 P6 R1 R2 SFL SPW : unit) => tt).
 intros ST5 FR5 Hccs MI5 (G5 & PC5 & AG5 & HH & Hh & HD & Hd & OF5) SRC LEN Hn HSTR.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof PC5 as (Afx & _ & (Bx & Ix & jx & padx & bsx & EPB & CELLS & _ & _ & _ & _ & WF)).
    pose proof (psize_pos p') as PS.
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G5 ltac:(rewrite EPB; left; reflexivity)) as (K1 & K2 & K3 & K4 & K5 & K6).
    apply pcap_cells_split4 in CELLS as (_ & CE & _ & _); [|reflexivity].
    apply (rw_cells_split_CB usegs m5 _ [] 304 _ [] [Z.to_nat n; 256 - Z.to_nat n; 48]%nat) in CE; [|cbn; lia]. cbn [mk_CB_cells app] in CE.
    destruct (rw_cells_cut _ _ _ 1 CE) as [CE1 CE23]. clear CE. cbn [firstn skipn cells_size csize Nat.add] in CE1, CE23.
    destruct (rw_cells_cut _ _ _ 1 CE23) as [CE2 _]. clear CE23. cbn [firstn skipn cells_size csize Nat.add] in CE2.
    unfold implM. iprefix. hide FR5. hide HH. hide HD. hide CE2.
    pose proof (munch_refl [(P + 216, P + 216 + n)]%Z m5) as MU. pose proof (wmono_refl usegs m5) as WM.
    step. step.
    eapply evt_cut.
    { eapply (memcpy_specZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m5 (P + 216)%Z STR n src (firstn (Z.to_nat n) (pj_g jx)));
        [reflexivity | reflexivity | reflexivity | exact SRC | exact LEN | lia | exact CE1 | lia | lia | lia | exact MI5]. }
    cbv beta. intros ms' PO. destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & m6 & -> & MU6 & WM6 & MI6 & HEB6 & _).
    replace (ret_pc (Z_to_bv 64 0x17d08)) with (Z_to_bv 64 0x17d08) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    unhide FR5. unhide HH. unhide HD. unhide CE2.
    assert (AGS : agrees_on (fun a => outside [(P + 216, P + 216 + n)]%Z a) m5 m6)
      by (eapply agrees_on_of_munch; [exact MU6 | exact WM6 | intros a _ Ho; exact Ho]).
    apply (agrees_rw_cells _ _ _ _ _ AGS) in FR5; [| intros a Ha; unfold ngn_frame in Ha; rewrite !cells_size_app in Ha; cbn [outside cells_size csize Nat.add] in *; rewrite Hccs in Ha; unfold rc_lo in LO; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGS) in HH; [| intros a Ha; rewrite Hh in Ha; cbn [outside]; unfold rc_lo in LO; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGS) in HD; [| intros a Ha; cbn [cells_size] in Ha; rewrite Hd in Ha; cbn [outside]; unfold rc_lo in LO; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGS) in CE2; [| intros a Ha; cbn [outside cells_size csize Nat.add] in *; lia].
    pose proof (agrees_stk _ _ _ _ _ AGS ST5 ltac:(intros a Ha; cbn [outside]; unfold rc_lo in LO; lia)) as ST6.
    pose proof (rw_cells_uncut _ _ _ _ _ HEB6 CE2 ltac:(cbn [cells_size csize Nat.add]; lia)) as HEB. cbn [app] in HEB.
    assert (G6 : GIo K R ps (CLc ++ PB') FB m6).
    { eapply (GIo_pcap_frame K HFL SFL); [exact G5 | exact MU6 | exact WM6 |].
      apply Forall_cons; [| apply Forall_nil].
      right. rewrite EPB. unfold iv_in_block, pcap_blocks. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    assert (PC6 : PCAPR_closable (hptr:=hptr) P (set_errbuf e p') PB' FB m6).
    { eapply (PCAPRC_errbuf _ _ _ _ _ _ _ _ _ _ _ _ G5 PC5 AGS); [| exact HEB | cbn [cells_size csize Nat.add]; lia].
      intros a Ha Hna. cbn [outside]. lia. }
    assert (AG6 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m6).
    { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [exact AGS|]. intros a [[Ha|Ha] _]; cbn [outside]; [unfold rc_lo in LO; lia|].
      destruct (ngn_CLc_facts _ _ _ _ G5 Ha) as [Hc Hnb]. split; [| exact Logic.I].
      intros Hin. apply Hnb. rewrite EPB. unfold pcap_blocks, in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    clear MU WM. pose proof (munch_refl ([] : list (Z * Z)) m6) as MU. pose proof (wmono_refl usegs m6) as WM.
    hide FR5. hide HH. hide HD. hide HEB.
    step. unhide FR5. unhide HH. unhide HD.
    apply evt_done. eapply ngn_ret_m1; [exact ST6 | exact FR5 | exact Hccs | exact MI6 |].
    split; [exact G6|]. split; [exact PC6|]. split; [exact AG6|]. split; [exact HH|]. split; [exact Hh|]. split; [exact HD|]. split; [exact Hd| exact OF5].
  Qed.
  End Sz11.
  Lemma ngn_mcp : ltac:(let t := eval cbv delta [ngn_mcp__stmt] in ngn_mcp__stmt in exact t).
  Proof using AD AH ALN BU HFL LO P1 P4 P5 P6 R1 R2 SFL SPW. intros ra' t0' t1' t2' a0' a3' a4' a5' a6' a7' x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' m5 ps PB' p' h hcs' dw dj ccs STR n src e. ltac2:(SecDiet.SzSec.closeP 'ngn_mcp__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

End NgnCtx.

End WithCeil.
End TwB.
