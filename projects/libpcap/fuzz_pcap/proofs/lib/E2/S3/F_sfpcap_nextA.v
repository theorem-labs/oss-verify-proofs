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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy GI. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GIFacts__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require PcapRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Pcap_iface__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_pcap_err__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_sfpcap_chkA__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.Pcap_iface_pp OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_pure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_small OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_next_ex OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_open OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_fopen OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_sfpcap_chkA__S3.F_sfpcap_chkA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.PP_kit.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac natfold_term t :=
  match t with
  | context C[4136%nat] => let t1 := context C[Z.to_nat 4136] in natfold_term t1
  | _ => t
  end.
Local Ltac natfold_hyp H := let T := type of H in let U := natfold_term T in change U in H.
Local Ltac natfold_concl := lazymatch goal with |- ?G => let U := natfold_term G in change U end.
Local Ltac natfold_lits :=
  repeat match goal with
  | nfH : context [4136%nat] |- _ => natfold_hyp nfH
  end;
  lazymatch goal with
  | |- context [4136%nat] => natfold_concl
  | |- _ => idtac
  end.
(* [comment removed for export] *)
Local Ltac cl_lit_hyps :=
  repeat match goal with
  | H : context [cells_size ?cs] |- _ =>
      tryif (match goal with H' := _ |- _ => constr_eq H' H end) then fail else
      (sl_spine_closed cs;
       let n := eval cbv [cells_size csize Nat.add] in (cells_size cs) in
       change (cells_size cs) with n in H)
  end.
Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac.release_frame FR ST hi ::=
  eapply stk_release in FR; [ | exact ST | lia ];
  clear ST; rename FR into ST;
  sl_lit_sizes_in ST;
  cbn [cells_size csize Nat.add] in ST;
  lazymatch type of ST with
  | stk ?segs ?m ?lo ?hi' => replace hi' with hi in ST by lia
  end.
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
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try gio_ceil_fact; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section WithCeil.
Context {CEILV : CEIL}.
Section NpCtx.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HPL : heap_perm_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis FREAD : fread_stmt_o HO K.
  Hypothesis FERROR : ferror_stmt_o HO K.
  Hypothesis FMT : fmt_errmsg_stmt K.
  Hypothesis SNPRINTF : snprintf_spec_stmt K.
  Hypothesis REALLOC : realloc_stmt_o HO K.
  Hypothesis PP : post_process_stmt.

  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (R : rctx) (CLc FB : list (cblock (hptr:=hptr))) (lo P HA DA B Af : Z) (m : mem) (o : option hptr).
  Variables (self buffer f : hptr) (bufsize bufalloc : Z) (bufdata : list Z) (swapped : bool)
            (vmaj vmin snapshot linktype ltext prec brk : Z) (errbuf : list Z) (header : pkthdr)
            (hdrsize : Z) (lsw : lenswap_t) (scl : sf_scale_t) (j : pcap_junk) (pad bs : list byte).
  Definition p0 : pcap hptr hptr :=
    mkPcap self f bufsize bufalloc buffer bufdata swapped vmaj vmin snapshot linktype ltext prec brk errbuf header (PrivPcap (mkSf hdrsize lsw scl)).
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
  Hypothesis P1 : (0 < P)%Z.  Hypothesis P2 : (P mod 16 = 0)%Z.  Hypothesis P4 : (P + 664 <= CEILZ)%Z.
  Hypothesis P5 : (P + 664 <= 65536 \/ 348160 <= P)%Z.  Hypothesis P6 : (P + 664 <= utp R - 200 \/ utp R - 200 + 4096 <= P)%Z.
  Hypothesis A1 : (0 < Af)%Z.  Hypothesis A4 : (Af + 1264 <= CEILZ)%Z.
  Hypothesis W1 : (1 <= snapshot <= INT_MAX)%Z.  Hypothesis W2 : (0 <= bufsize < 2^32)%Z.
  Hypothesis W5 : brk = 0%Z.  Hypothesis W6 : prec = 0%Z.
  Hypothesis W7 : (0 <= vmaj < 2^16)%Z.  Hypothesis W8 : (0 <= vmin < 2^16)%Z.
  Hypothesis W9 : (0 <= linktype < 2^31)%Z.  Hypothesis W10 : (-2^31 <= ltext < 2^31)%Z.
  Hypothesis WHS : (hdrsize = 16 \/ hdrsize = 24)%Z.

  Let POSTQ := next_packet_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o.

  (* [comment removed for export] *)
  Definition np_cells (bsz Bx : Z) (jx : pcap_junk) : list cell :=
    pcap_cells (set_buffer buffer bsz bsz [] p0) P Bx Af jx.

  (* [comment removed for export] *)
  Definition np_epilogue__stmt : Prop := forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x0 x1 x2 x3 x4 x5 x6 x7 t3' t4' t5' t6' : word) (m5 : mem) (fj : list byte) (Q : machine_state -> Prop),
      stk ssegs m5 lo (bv_unsigned sp + -4208) ->
      rw_cells ssegs m5 (bv_unsigned sp + -4208) [CB 4136 fj; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> mem_inv ssegs m5 ->
      (forall t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'',
          stk ssegs m5 lo (bv_unsigned sp) ->
          Q (MS (mkR ra sp gp tp t0'' t1'' t2'' s0 s1 a0' a1'' a2'' a3'' a4'' a5'' a6'' a7'' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3'' t4'' t5'' t6'')
                F (ret_pc ra) fc None m5 (seg_rom ssegs))) ->
      evt ssegs Q
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -4208)) gp tp t0' t1' t2' x0 x1 a0' a1' a2' a3' a4' a5' a6' a7'
                 x2 x3 x4 x5 x6 x7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x1570c) fc None m5 (seg_rom ssegs)).
  Section Sz1.
  Variables ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x0 x1 x2 x3 x4 x5 x6 x7 t3' t4' t5' t6' m5 fj Q : ltac2:(SecDiet.SzSec.tyM 'np_epilogue__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma np_epilogue__body : ltac2:(SecDiet.SzSec.bodyP 'np_epilogue__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using BU CEILV DA HA P. all: natfold_lits. pin_using (fun (BU CEILV DA HA P : unit) => tt).
    intros ST5 FR5 MI5 HQ.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl ssegs m5) as WM.
    destruct (rw_cells_cut _ _ _ 1 FR5) as [FRJ FRS]. clear FR5. (cbn [firstn skipn] in FRJ, FRS; sl_lit_sizes_in FRJ; sl_lit_sizes_in FRS; cbn [firstn skipn cells_size csize Nat.add] in FRJ, FRS).
    lazymatch type of FRS with rw_cells _ _ ?nfA _ => replace nfA with (bv_unsigned sp + -72)%Z in FRS by lia end.
    do 13 step.
    release_frame FRJ ST5 (bv_unsigned sp + -72)%Z. release_frame FRS ST5 (bv_unsigned sp).
    apply evt_done. apply HQ. exact ST5.
  Qed.
  End Sz1.
  Lemma np_epilogue : ltac:(let t := eval cbv delta [np_epilogue__stmt] in np_epilogue__stmt in exact t).
  Proof using BU CEILV DA HA P. all: natfold_lits. intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x0 x1 x2 x3 x4 x5 x6 x7 t3' t4' t5' t6' m5 fj Q. ltac2:(SecDiet.SzSec.closeP 'np_epilogue__body "vvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition PCAPR_errbuf__stmt : Prop := forall Rx sx CLx Px (p : pcap hptr hptr) PB FBx (mx mx' : mem) (Q : Z -> Prop) cs e,
    GIo K Rx sx (CLx ++ PB) FBx mx -> PCAPR (hptr:=hptr) Px p PB FBx mx -> agrees_on Q mx mx' ->
    (forall a, in_block PB a -> ~ (Px + 216 <= a < Px + 472)%Z -> Q a) ->
    rw_cells ssegs mx' (Px + 216) cs -> cells_size cs = 256%nat ->
    PCAPR (hptr:=hptr) Px (set_errbuf e p) PB FBx mx'.
  Section Sz2.
  Variables Rx sx CLx Px p PB FBx mx mx' Q cs e : ltac2:(SecDiet.SzSec.tyM 'PCAPR_errbuf__stmt "vvvvvvvvvvvv" @Rx).
  Lemma PCAPR_errbuf__body : ltac2:(SecDiet.SzSec.bodyP 'PCAPR_errbuf__stmt "vvvvvvvvvvvv").
  Proof using AD AH ALN BU LO P1 R1 R2 SPW. all: natfold_lits. pin_using (fun (AD AH ALN BU LO P1 R1 R2 SPW : unit) => tt).
    intros G PC AG HQ HCS Hsz.
    destruct PC as (Afx & Hin & (Bx & I & jx & padx & bsx & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    pose proof (psize_pos p) as PS. pose proof (PB_apart K _ _ _ _ _ _ _ _ _ _ G EPB) as [APB API].
    assert (Q1 : forall a, (Px <= a < Px + psize p)%Z -> ~ (Px + 216 <= a < Px + 472)%Z -> Q a).
    { intros a Ha Hn. apply HQ; [|exact Hn]. rewrite EPB. unfold pcap_blocks, in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. exact Ha. }
    apply pcap_cells_split4 in CELLS as (CA & CE & CH & CO); [|reflexivity].
    apply (rw_cells_split_CB ssegs mx _ [] 304 _ [] [256; 48]%nat) in CE; [|reflexivity]. cbn [mk_CB_cells app] in CE.
    destruct (rw_cells_cut _ _ _ 1 CE) as [_ CE2]. clear CE. (cbn [firstn skipn] in CE2; sl_lit_sizes_in CE2; cbn [firstn skipn cells_size csize Nat.add] in CE2).
    replace (Px + 216 + Z.of_nat 256)%Z with (Px + 472)%Z in CE2 by lia.
    apply (agrees_rw_cells _ _ _ _ _ AG) in CA; [| intros a Ha; rewrite (pc_pre_size p Px Bx (C8 (Z_to_bv 64 Afx)) jx eq_refl) in Ha; apply Q1; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG) in CH; [| intros a Ha; (sl_lit_sizes_in Ha; cbn [cells_size csize hdr_cells Nat.add] in Ha); apply Q1; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG) in CO; [| intros a Ha; (sl_lit_sizes_in Ha; cbn [cells_size csize pc_ops Nat.add] in Ha); apply Q1; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG) in CE2; [| intros a Ha; (sl_lit_sizes_in Ha; cbn [cells_size csize Nat.add] in Ha); apply Q1; lia].
    pose proof (rw_cells_uncut _ _ _ _ _ HCS CE2 ltac:(rewrite Hsz; lia)) as CE'.
    pose proof WF as (_ & _ & W3 & _).
    destruct (pcap_aux_agree p Px Bx I padx bsx mx mx' Q AG) as (BUF' & PRIV' & IFS');
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
             unfold pcap_cells. replace (set_header (pc_header p) p) with p in J by (destruct p; reflexivity).
             destruct p; cbn. exact J. }
    split; [destruct p; exact PRIV'|]. split; [destruct p; exact BUF'|]. split; [destruct p; exact PFX|].
    split; [destruct p; exact IFS'|]. destruct p; exact WF.
  Qed.
  End Sz2.
  Lemma PCAPR_errbuf : ltac:(let t := eval cbv delta [PCAPR_errbuf__stmt] in PCAPR_errbuf__stmt in exact t).
  Proof using AD AH ALN BU LO P1 R1 R2 SPW. all: natfold_lits. intros Rx sx CLx Px p PB FBx mx mx' Q cs e. ltac2:(SecDiet.SzSec.closeP 'PCAPR_errbuf__body "vvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition np_final (m5 : mem) (ps : PState H hptr) (PB' : list (cblock (hptr:=hptr))) (p' : pcap hptr hptr) (hcs' : list cell) (dw : cell) : Prop :=
    GIo K R ps (CLc ++ PB') FB m5 /\ PCAPR (hptr:=hptr) P p' PB' FB m5
    /\ agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5
    /\ rw_cells ssegs m5 HA hcs' /\ cells_size hcs' = 24%nat /\ rw_cells ssegs m5 DA [dw] /\ csize dw = 8%nat /\ ps_outfile ps = o.

  (* [comment removed for export] *)
  Definition np_fail_tail__stmt : Prop := forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x0 x1 x2 x3 x4 x5 x6 x7 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (PB' : list (cblock (hptr:=hptr))) (p' : pcap hptr hptr) (h : pkthdr) (hcs' : list cell) (dw : cell) (fj : list byte),
      stk ssegs m5 lo (bv_unsigned sp + -4208) ->
      rw_cells ssegs m5 (bv_unsigned sp + -4208) [CB 4136 fj; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> mem_inv ssegs m5 ->
      np_final m5 ps PB' p' hcs' dw ->
      implM ssegs (mret ((-1)%Z, h, p')) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -4208)) gp tp t0' t1' t2' x0 x1 a0' a1' a2' a3' a4' a5' a6' a7'
                 x2 x3 x4 x5 x6 x7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x15708) fc None m5 (seg_rom ssegs)).
  Section Sz3.
  Variables ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x0 x1 x2 x3 x4 x5 x6 x7 t3' t4' t5' t6' m5 ps PB' p' h hcs' dw fj : ltac2:(SecDiet.SzSec.tyM 'np_fail_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma np_fail_tail__body : ltac2:(SecDiet.SzSec.bodyP 'np_fail_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using BU. all: natfold_lits. pin_using (fun (BU : unit) => tt).
    intros ST5 FR5 MI5 (G5 & PC5 & AG5 & HH & Hh & HD & Hd & OF).
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    apply (implM_ret ssegs). hide HH. hide HD.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl ssegs m5) as WM.
    step. eapply np_epilogue; [exact ST5 | exact FR5 | exact MI5 |].
    intros t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' ST6. unhide HH. unhide HD.
    subst POSTQ. unfold next_packet_post. all: natfold_lits. exists (Z_to_bv 64 (-1)), m5, PB', dw.
    split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
    split; [exact OF|]. split; [exact MI5|]. split; [exact ST6|]. split; [exact AG5|]. split; [exact G5|].
    split; [intros _; exact PC5|]. split; [intros _; apply PCAPR_closable_of; exact PC5|].
    split; [reflexivity|]. split; [lia|]. split; [intros X; lia|]. split; [intros _; exists hcs'; split; [exact Hh| exact HH]|].
    split; [exact HD| exact Hd].
  Qed.
  End Sz3.
  Lemma np_fail_tail : ltac:(let t := eval cbv delta [np_fail_tail__stmt] in np_fail_tail__stmt in exact t).
  Proof using BU. all: natfold_lits. intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x0 x1 x2 x3 x4 x5 x6 x7 t3' t4' t5' t6' m5 ps PB' p' h hcs' dw fj. ltac2:(SecDiet.SzSec.closeP 'np_fail_tail__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition np_ok_tail__stmt : Prop := forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x0 x1 x2 x3 x4 x5 x6 x7 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (PB' : list (cblock (hptr:=hptr))) (p' : pcap hptr hptr) (h : pkthdr) (dw : cell) (fj : list byte),
      stk ssegs m5 lo (bv_unsigned sp + -4208) ->
      rw_cells ssegs m5 (bv_unsigned sp + -4208) [CB 4136 fj; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> mem_inv ssegs m5 ->
      np_final m5 ps PB' p' (hdr_cells h) dw -> (0 <= h_caplen h < 2^32)%Z -> (0 <= h_len h < 2^32)%Z ->
      implM ssegs (mret (1%Z, h, p')) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -4208)) gp tp t0' t1' t2' x0 x1 a0' a1' a2' a3' a4' a5' a6' a7'
                 x2 x3 x4 x5 x6 x7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x157e4) fc None m5 (seg_rom ssegs)).
  Section Sz4.
  Variables ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x0 x1 x2 x3 x4 x5 x6 x7 t3' t4' t5' t6' m5 ps PB' p' h dw fj : ltac2:(SecDiet.SzSec.tyM 'np_ok_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma np_ok_tail__body : ltac2:(SecDiet.SzSec.bodyP 'np_ok_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using BU. all: natfold_lits. pin_using (fun (BU : unit) => tt).
    intros ST5 FR5 MI5 (G5 & PC5 & AG5 & HH & Hh & HD & Hd & OF) HC HL.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    apply (implM_ret ssegs). hide HH. hide HD.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl ssegs m5) as WM.
    do 2 step. eapply np_epilogue; [exact ST5 | exact FR5 | exact MI5 |].
    intros t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' ST6. unhide HH. unhide HD.
    subst POSTQ. unfold next_packet_post. all: natfold_lits. exists (Z_to_bv 64 1), m5, PB', dw.
    split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
    split; [exact OF|]. split; [exact MI5|]. split; [exact ST6|]. split; [exact AG5|]. split; [exact G5|].
    split; [intros _; exact PC5|]. split; [intros _; apply PCAPR_closable_of; exact PC5|].
    split; [reflexivity|]. split; [lia|]. split; [intros _; split; [exact HH| split; [exact HC| exact HL]]|]. split; [intros X; exfalso; lia|].
    split; [exact HD| exact Hd].
  Qed.
  End Sz4.
  Lemma np_ok_tail : ltac:(let t := eval cbv delta [np_ok_tail__stmt] in np_ok_tail__stmt in exact t).
  Proof using BU. all: natfold_lits. intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x0 x1 x2 x3 x4 x5 x6 x7 t3' t4' t5' t6' m5 ps PB' p' h dw fj. ltac2:(SecDiet.SzSec.closeP 'np_ok_tail__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Lemma np_CLc_facts : forall ps PB' m5 a, GIo K R ps (CLc ++ PB') FB m5 -> in_block CLc a -> (0 < a < CEILZ)%Z /\ ~ in_block PB' a.
  Proof using Type. all: natfold_lits. pin_using tt. intros. eapply GIo_CLc_facts; eassumption. Qed.

  (* [comment removed for export] *)
  Definition np_snp__stmt : Prop := forall (t0' t1' t2' a3' a4' a5' a6' a7' x0 x1 x2 x3 x4 x5 x6 x7 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (PB' : list (cblock (hptr:=hptr))) (p' : pcap hptr hptr) (h : pkthdr) (hcs' : list cell) (dw : cell) (fj : list byte)
           (FMTA : Z) (fs : string) (args : list farg),
      stk ssegs m5 lo (bv_unsigned sp + -4208) ->
      rw_cells ssegs m5 (bv_unsigned sp + -4208) [CB 4136 fj; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> mem_inv ssegs m5 ->
      np_final m5 ps PB' p' hcs' dw ->
      fmt_at m5 FMTA fs -> fmt_ok fs args = true -> (length args <= 2)%nat -> Forall2 (farg_word R (CLc ++ PB') (bv_unsigned sp + -4208) (P + 216) 256 m5) args (firstn (length args) [a3'; a4']) ->
      (length (Fmt.snprintf 256 fs args) <= 255)%nat -> items_okb (fmt fs) = true -> Forall arg_ok args ->
      implM ssegs (mret ((-1)%Z, h, set_errbuf (Fmt.snprintf 256 fs args) p')) ps POSTQ
        (MS (mkR (Z_to_bv 64 0x15708) (Z_to_bv 64 (bv_unsigned sp + -4208)) gp tp t0' t1' t2' x0 x1 (Z_to_bv 64 (P + 216)) (Z_to_bv 64 256) (Z_to_bv 64 FMTA) a3' a4' a5' a6' a7'
                 x2 x3 x4 x5 x6 x7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 SNPRINTF_ENTRY) fc None m5 (seg_rom ssegs)).
  Section Sz6.
  Variables t0' t1' t2' a3' a4' a5' a6' a7' x0 x1 x2 x3 x4 x5 x6 x7 t3' t4' t5' t6' m5 ps PB' p' h hcs' dw fj FMTA fs args : ltac2:(SecDiet.SzSec.tyM 'np_snp__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @t0').
  Lemma np_snp__body : ltac2:(SecDiet.SzSec.bodyP 'np_snp__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AD AH ALN BU HFL LO P1 P4 P5 R1 R2 SFL SNPRINTF SPM SPW TP. all: natfold_lits. pin_using (fun (AD AH ALN BU HFL LO P1 P4 P5 R1 R2 SFL SNPRINTF SPM SPW TP : unit) => tt).
    intros ST5 FR5 MI5 (G5 & PC5 & AG5 & HH & Hh & HD & Hd & OF5) FMT5 FOK LA FW LEN IOK AOK.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof PC5 as (Afx & _ & (Bx & Ix & jx & padx & bsx & EPB & CELLS & _ & _ & _ & _ & WF)).
    pose proof (psize_pos p') as PS.
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G5 ltac:(rewrite EPB; left; reflexivity)) as (K1 & K2 & K3 & K4 & K5 & K6).
    apply pcap_cells_split4 in CELLS as (_ & CE & _ & _); [|reflexivity].
    apply (rw_cells_split_CB ssegs m5 _ [] 304 _ [] [256; 48]%nat) in CE; [|reflexivity]. cbn [mk_CB_cells app] in CE.
    destruct (rw_cells_cut _ _ _ 1 CE) as [CE1 _]. clear CE. (cbn [firstn skipn] in CE1; sl_lit_sizes_in CE1; cbn [firstn skipn cells_size csize Nat.add] in CE1).
    assert (HinP : forall a, (P + 216 <= a < P + 216 + 256)%Z -> in_block (CLc ++ PB') a).
    { intros a Ha. apply in_block_app. right. rewrite EPB. unfold pcap_blocks, in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    apply (implM_ret ssegs). name_sp sp (-4208)%Z.
    eapply evt_cut.
    { eapply (SNPRINTF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R ps (CLc ++ PB') FB lo (P + 216)%Z 256%Z FMTA fs args (firstn 256 (pj_g jx)));
        [| reflexivity | reflexivity | reflexivity | lia | exact FMT5 | exact FOK | exact (Nat.le_le_succ_r _ _ LA) | rewrite Hsp; replace (firstn (length args) [a3'; a4'; a5']) with (firstn (length args) [a3'; a4']) by (clear -LA; destruct args as [|? [|? [|? ?]]]; cbn in LA |- *; fastfirst (first [ noevar_assumption |reflexivity | lia])); exact FW | exact CE1 | left; exact HinP].
      split; [exact G5|]. split; [rewrite Hsp; exact ST5|]. split; [unfold rc_lo; lia|]. split; [unfold STDIO_STACK; rewrite Hsp; lia|].
      split; [rewrite Hsp; lia|]. split; [exact MI5|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
    cbv beta. intros ms' PO. destruct PO as (av & m6 & junk6 & E & MU6 & WM6 & MI6 & ST6 & -> & HEB6).
    unfold hpost_regs in E. all: natfold_lits. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 87816)) with (Z_to_bv 64 87816) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    unfold STDIO_STACK in MU6.
    assert (AGS : agrees_on (fun a => outside [(bv_unsigned sp + -4208 - 65536, bv_unsigned sp + -4208); (P + 216, P + 216 + 256)]%Z a) m5 m6)
      by (eapply agrees_on_of_munch; [exact MU6 | exact WM6 | intros a _ Ho; exact Ho]).
    apply (agrees_rw_cells _ _ _ _ _ AGS) in FR5; [| intros a Ha; (cl_lit_hyps; sl_lit_sizes; cbn [outside cells_size csize Nat.add] in *); unfold rc_lo in LO; (keep_hyps CEILV H hptr K sp R CLc FB lo P HA DA m5 ps PB' hcs' dw fs args a LO BU P4 G5 Ha; lia)].
    apply (agrees_rw_cells _ _ _ _ _ AGS) in HH; [| intros a Ha; rewrite Hh in Ha; cbn [outside]; unfold rc_lo in LO; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGS) in HD; [| intros a Ha; cbn [cells_size] in Ha; rewrite Hd in Ha; cbn [outside]; unfold rc_lo in LO; lia].
    assert (G6 : GIo K R ps (CLc ++ PB') FB m6).
    { eapply (GIo_pcap_frame K HFL SFL); [exact G5 | exact MU6 | exact WM6 |].
      apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia|]. apply Forall_cons; [| apply Forall_nil].
      right. rewrite EPB. unfold iv_in_block, pcap_blocks. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    assert (PC6 : PCAPR (hptr:=hptr) P (set_errbuf (Fmt.snprintf 256 fs args) p') PB' FB m6).
    { eapply (PCAPR_errbuf _ _ _ _ _ _ _ _ _ _ _ _ G5 PC5 AGS); [| exact HEB6 | (sl_lit_sizes; cbn [cells_size csize Nat.add]); lia].
      intros a Ha Hn. cbn [outside]. pose proof (in_PB_below K _ _ _ _ _ _ _ G5 Ha). unfold rc_lo in LO. lia. }
    assert (AG6 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m6).
    { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [exact AGS|]. intros a [[Ha|Ha] _]; cbn [outside]; [unfold rc_lo in LO; lia|].
      destruct (np_CLc_facts _ _ _ _ G5 Ha) as [Hc Hnb]. split; [unfold rc_lo in LO; lia|]. split; [| exact Logic.I].
      intros Hin. apply Hnb. rewrite EPB. unfold pcap_blocks, in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    eapply np_fail_tail; [exact ST6 | exact FR5 | exact MI6 |].
    split; [exact G6|]. split; [exact PC6|]. split; [exact AG6|]. split; [exact HH|]. split; [exact Hh|]. split; [exact HD|]. split; [exact Hd| exact OF5].
  Qed.
  End Sz6.
  Lemma np_snp : ltac:(let t := eval cbv delta [np_snp__stmt] in np_snp__stmt in exact t).
  Proof using AD AH ALN BU HFL LO P1 P4 P5 R1 R2 SFL SNPRINTF SPM SPW TP. all: natfold_lits. intros t0' t1' t2' a3' a4' a5' a6' a7' x0 x1 x2 x3 x4 x5 x6 x7 t3' t4' t5' t6' m5 ps PB' p' h hcs' dw fj FMTA fs args. ltac2:(SecDiet.SzSec.closeP 'np_snp__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition np_fmt__stmt : Prop := forall (t0' t1' t2' a4' a5' a6' a7' x0 x1 x2 x3 x4 x5 x6 x7 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (PB' : list (cblock (hptr:=hptr))) (p' : pcap hptr hptr) (h : pkthdr) (hcs' : list cell) (dw : cell) (fj : list byte) (e : Z),
      stk ssegs m5 lo (bv_unsigned sp + -4208) ->
      rw_cells ssegs m5 (bv_unsigned sp + -4208) [CB 4136 fj; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> mem_inv ssegs m5 ->
      np_final m5 ps PB' p' hcs' dw -> (-2^31 <= e < 2^31)%Z -> fmt_at m5 0x108d6 "error reading dump file"%string ->
      implM ssegs (mret ((-1)%Z, h, set_errbuf (fmt_errmsg "error reading dump file"%string [] e) p')) ps POSTQ
        (MS (mkR (Z_to_bv 64 0x15548) (Z_to_bv 64 (bv_unsigned sp + -4208)) gp tp t0' t1' t2' x0 x1 (Z_to_bv 64 (P + 216)) (Z_to_bv 64 256) (Z_to_bv 64 (s32 e)) (Z_to_bv 64 0x108d6) a4' a5' a6' a7'
                 x2 x3 x4 x5 x6 x7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 PCAP_FMT_ERRMSG_ENTRY) fc None m5 (seg_rom ssegs)).
  Section Sz7.
  Variables t0' t1' t2' a4' a5' a6' a7' x0 x1 x2 x3 x4 x5 x6 x7 t3' t4' t5' t6' m5 ps PB' p' h hcs' dw fj e : ltac2:(SecDiet.SzSec.tyM 'np_fmt__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvv" @t0').
  Lemma np_fmt__body : ltac2:(SecDiet.SzSec.bodyP 'np_fmt__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AD AH ALN BU FMT LO P1 P2 P4 R1 R2 SPM SPW TP. all: natfold_lits. pin_using (fun (AD AH ALN BU FMT LO P1 P2 P4 R1 R2 SPM SPW TP : unit) => tt).
    intros ST5 FR5 MI5 (G5 & PC5 & AG5 & HH & Hh & HD & Hd & OF5) HE MSG.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof PC5 as (Afx & _ & (Bx & Ix & jx & padx & bsx & EPB & CELLS & _ & _ & _ & _ & WF)).
    pose proof (psize_pos p') as PS.
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G5 ltac:(rewrite EPB; left; reflexivity)) as (K1 & K2 & K3 & K4 & K5 & K6).
    apply pcap_cells_split4 in CELLS as (_ & CE & _ & _); [|reflexivity].
    apply (rw_cells_split_CB ssegs m5 _ [] 304 _ [] [256; 48]%nat) in CE; [|reflexivity]. cbn [mk_CB_cells app] in CE.
    destruct (rw_cells_cut _ _ _ 1 CE) as [CE1 _]. clear CE. (cbn [firstn skipn] in CE1; sl_lit_sizes_in CE1; cbn [firstn skipn cells_size csize Nat.add] in CE1).
    assert (HinP : forall a, (P + 216 <= a < P + 216 + 256)%Z -> in_block (CLc ++ PB') a).
    { intros a Ha. apply in_block_app. right. rewrite EPB. unfold pcap_blocks, in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    apply (implM_ret ssegs). name_sp sp (-4208)%Z.
    eapply evt_cut.
    { eapply (FMT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R ps (CLc ++ PB') FB lo (P + 216)%Z 0x108d6%Z e "error reading dump file"%string [] (firstn 256 (pj_g jx)));
        [| reflexivity | reflexivity | reflexivity | exact HE | reflexivity | exact MSG | reflexivity | cbn; lia | constructor | exact CE1 | left; exact HinP | apply aligned16_8; [exact P2| reflexivity]].
      split; [exact G5|]. split; [rewrite Hsp; exact ST5|]. split; [unfold rc_lo; lia|]. split; [unfold PCAP_L1_STACK; rewrite Hsp; lia|].
      split; [rewrite Hsp; lia|]. split; [exact MI5|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
    cbv beta. intros ms' PO. destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m6 & junk6 & -> & MI6 & ST6 & AG6 & G6 & HEB6).
    rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 87368)) with (Z_to_bv 64 87368) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    apply (agrees_rw_cells _ _ _ _ _ AG6) in FR5; [| intros a Ha; (sl_lit_sizes_in Ha; cbn [cells_size csize Nat.add] in Ha); split; [left; (keep_hyps CEILV sp R P HA DA hcs' dw a Ha; lia)| unfold rc_lo in LO; (keep_hyps CEILV H hptr K sp R CLc FB lo P HA DA ps PB' hcs' dw m6 a LO BU P4 G6 Ha; lia)]].
    apply (agrees_rw_cells _ _ _ _ _ AG6) in HH; [| intros a Ha; rewrite Hh in Ha; split; [left; lia| unfold rc_lo in LO; lia]].
    apply (agrees_rw_cells _ _ _ _ _ AG6) in HD; [| intros a Ha; cbn [cells_size] in Ha; rewrite Hd in Ha; split; [left; lia| unfold rc_lo in LO; lia]].
    assert (PC6 : PCAPR (hptr:=hptr) P (set_errbuf (fmt_errmsg "error reading dump file" [] e) p') PB' FB m6).
    { pose proof (fmt_errmsg_length "error reading dump file"%string [] e) as LENE.
      eapply (PCAPR_errbuf _ _ _ _ _ _ _ _ _ _ _ _ G5 PC5 AG6); [| exact HEB6 | (sl_lit_sizes; cbn [cells_size csize Nat.add]); lia].
      intros a Ha Hn. split; [right; apply in_block_app; right; exact Ha| lia]. }
    assert (AG06 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m6).
    { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [exact AG6|]. intros a [[Ha|Ha] _]; [split; [left; lia| unfold rc_lo in LO; lia]|].
      destruct (np_CLc_facts _ _ _ _ G5 Ha) as [Hc Hnb]. split; [right; apply in_block_app; left; exact Ha|].
      intros Hin. apply Hnb. rewrite EPB. unfold pcap_blocks, in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    hide HEB6. hide HH. hide HD.
    pose proof (munch_refl ([] : list (Z * Z)) m6) as MU. pose proof (wmono_refl ssegs m6) as WM.
    step.
    unhide HEB6. unhide HH. unhide HD.
    eapply np_fail_tail; [exact ST6 | exact FR5 | exact MI6 |].
    split; [exact G6|]. split; [exact PC6|]. split; [exact AG06|]. split; [exact HH|]. split; [exact Hh|]. split; [exact HD|]. split; [exact Hd| exact OF5].
  Qed.
  End Sz7.
  Lemma np_fmt : ltac:(let t := eval cbv delta [np_fmt__stmt] in np_fmt__stmt in exact t).
  Proof using AD AH ALN BU FMT LO P1 P2 P4 R1 R2 SPM SPW TP. all: natfold_lits. intros t0' t1' t2' a4' a5' a6' a7' x0 x1 x2 x3 x4 x5 x6 x7 t3' t4' t5' t6' m5 ps PB' p' h hcs' dw fj e. ltac2:(SecDiet.SzSec.closeP 'np_fmt__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
  (* [comment removed for export] *)
  Hypothesis PPLEN : forall lt sw hdr d, length (snd (pcapint_post_process lt sw hdr d)) = length d.
  Hypothesis PPSEC : forall lt sw hdr d, h_sec (fst (pcapint_post_process lt sw hdr d)) = h_sec hdr /\ h_usec (fst (pcapint_post_process lt sw hdr d)) = h_usec hdr.
  Hypothesis PPRNG : forall lt sw hdr d, (0 <= h_caplen hdr <= Z.of_nat (length d))%Z -> (0 <= h_len hdr < 2^32)%Z -> (Z.of_nat (length d) < 2^31)%Z ->
     (0 <= h_caplen (fst (pcapint_post_process lt sw hdr d)) < 2^32)%Z /\ (0 <= h_len (fst (pcapint_post_process lt sw hdr d)) < 2^32)%Z.

  (* [comment removed for export] *)
  Definition pv (bq : hptr) (bsz alloc : Z) (data eb : list Z) : pcap hptr hptr :=
    mkPcap self f bsz alloc bq data swapped vmaj vmin snapshot linktype ltext prec brk eb header (PrivPcap (mkSf hdrsize lsw scl)).

  Ltac norm_p :=
    unfold pv in *; unfold pcap_blocks in *; unfold psize in *; unfold is_ng in *;
    cbn [pc_self pc_rfile pc_bufsize pc_bufalloc pc_buffer pc_bufdata pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype
         pc_linktype_ext pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_priv priv_cells
         sf_hdrsize sf_lengths_swapped sf_scale_type ifaces_ok set_bufdata set_errbuf set_buffer] in *;
    unfold PCAP_SF_TOTAL, PCAP_PRIV_OFF in *.

  (* [comment removed for export] *)
  Lemma bytes_wr_rw_cells : forall mx A l, bytes_at ssegs mx A l -> wr_at ssegs mx A (Z.of_nat (length l)) -> rw_cells ssegs mx A [CB (length l) l].
  Proof using Type. all: natfold_lits. pin_using tt. intros mx A l HB HW. split; [split; [cbn; split; [reflexivity| exact Logic.I] | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact HB] | (sl_lit_sizes; cbn [cells_size csize Nat.add]); rewrite Nat.add_0_r; exact HW]. Qed.

  Definition np_finish__stmt : Prop := forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x3 x4 x5 x6 x7 t3' t4' t5' t6' ws wu : word) (m5 : mem) (ps : PState H hptr)
           (bq : hptr) (Bx bsz alloc : Z) (data eb : list Z) (sec usec cap len : Z) (dw : cell) (fj : list byte),
      stk ssegs m5 lo (bv_unsigned sp + -4208) ->
      rw_cells ssegs m5 (bv_unsigned sp + -4208) [CB 4136 fj; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> mem_inv ssegs m5 ->
      GIo K R ps (CLc ++ pcap_blocks (pv bq bsz alloc data eb) P Bx 0) FB m5 ->
      PCAPR (hptr:=hptr) P (pv bq bsz alloc data eb) (pcap_blocks (pv bq bsz alloc data eb) P Bx 0) FB m5 ->
      agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells ssegs m5 HA [C8 ws; C8 wu; C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)] -> rw_cells ssegs m5 DA [dw] -> csize dw = 8%nat ->
      ws = Z_to_bv 64 sec -> wu = Z_to_bv 64 usec -> Forall (fun x => 0 <= x < 256)%Z data ->
      (0 <= cap <= Z.of_nat (length data))%Z -> (Z.of_nat (length data) < 2^31)%Z -> (0 <= len < 2^32)%Z -> ps_outfile ps = o ->
      implM ssegs (let '(hdr, d) := pcapint_post_process linktype swapped (mkHdr sec usec cap len) data in
                   mret (1%Z, hdr, set_bufdata d (pv bq bsz alloc data eb))) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -4208)) gp tp t0' t1' t2' (Z_to_bv 64 P) (Z_to_bv 64 HA) a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 DA) x3 x4 x5 x6 x7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x157cc) fc None m5 (seg_rom ssegs)).
  Section Sz9.
  Variables ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x3 x4 x5 x6 x7 t3' t4' t5' t6' ws wu m5 ps bq Bx bsz alloc data eb sec usec cap len dw fj : ltac2:(SecDiet.SzSec.tyM 'np_finish__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma np_finish__body : ltac2:(SecDiet.SzSec.bodyP 'np_finish__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AD AH BU HFL LO P1 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 SFL SP47 SPM SPW W9. all: natfold_lits. pin_using (fun (AD AH BU HFL LO P1 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 SFL SP47 SPM SPW W9 : unit) => tt).
    intros ST5 FR5 MI5 G5 PC5 AG5 HH HD Hd -> -> DRNG Hcap Hlen Hl32 OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof PC5 as PC5'.
    destruct PC5 as (Afx & Hin & (Bx' & Ix & jx' & padx & bsx' & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    norm_p. unfold sf_cells in PRIV. cbn [sf_hdrsize sf_lengths_swapped sf_scale_type] in PRIV.
    subst Ix. assert (EBX : Bx' = Bx) by congruence. subst Bx'. clear EPB.
    pose proof WF as (W1' & W2' & W3 & W4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & WBB). cbn [pc_bufsize pc_bufalloc pc_bufdata length] in W3, W4, WBB.
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G5 ltac:(right; left; reflexivity)) as (K1 & K2 & K3 & K4 & K5 & K6).
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G5 ltac:(left; reflexivity)) as (L1 & L2 & L3 & L4 & L5 & L6).
    assert (BP' : (Bx + alloc <= P \/ P + 664 <= Bx)%Z).
    { pose proof (PB_apart K _ _ _ _ _ _ (pv bq bsz alloc data eb) P Bx 0 G5 eq_refl) as [APB _]. unfold pv, psize, is_ng in APB. cbn [pc_bufalloc pc_priv] in APB. unfold PCAP_SF_TOTAL in APB. match type of APB with ?t => idtac t end. (keep_hyps CEILV R P HA DA Bx alloc data dw APB; lia). }
    unfold pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF in CELLS.
    cbn [app pc_bufsize pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_header pc_priv pk_next_pcap pk_cleanup_sf PK] in CELLS.
    destruct (rw_cells_forget _ _ _ _ HD) as [dwj HD']. clear HD. cbn [cells_size] in HD'. rewrite Hd in HD'. change (8 + 0)%nat with 8%nat in HD'.
    (* [comment removed for export] *)
    apply (rw_cells_split_CB ssegs m5 _ [] (Z.to_nat alloc) _ [] [length data; Z.to_nat alloc - length data]%nat) in BUF; [| cbn; lia].
    cbn [mk_CB_cells app] in BUF. rewrite PFX in BUF.
    destruct (rw_cells_cut _ _ _ 1 BUF) as [BD BT]. clear BUF. (cbn [firstn skipn] in BD, BT; sl_lit_sizes_in BD; sl_lit_sizes_in BT; cbn [firstn skipn cells_size csize Nat.add] in BD, BT).
    hide BD. hide BT. hide PRIV.
    pose proof (munch_refl [(DA, DA + 8)]%Z m5) as MU. pose proof (wmono_refl ssegs m5) as WM.
    unfold implM. iprefix.
    step. step. rewrite (sx32_small (Z.b2z swapped)) by (destruct swapped; cbn; lia).
    step. rewrite (sx32_small linktype) by lia.
    step. step. step.
    unhide BD. unhide BT. unhide PRIV.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (AGD : agrees_on (fun a => outside [(DA, DA + 8)]%Z a) m5 mm) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]);
      rename mm into m5' end.
    apply (agrees_rw_cells _ _ _ _ _ AGD) in BD; [| intros a Ha; (cl_lit_hyps; sl_lit_sizes; cbn [outside cells_size csize Nat.add] in *); unfold rc_lo in LO; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGD) in BT; [| intros a Ha; (cl_lit_hyps; sl_lit_sizes; cbn [outside cells_size csize Nat.add] in *); unfold rc_lo in LO; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGD) in PRIV; [| intros a Ha; (cl_lit_hyps; sl_lit_sizes; cbn [outside cells_size csize Nat.add] in *); unfold rc_lo in LO; lia].
    assert (G5' : GIo K R ps (CLc ++ [(self, P, 664%Z); (bq, Bx, alloc)]) FB m5').
    { eapply (GIo_pcap_frame K HFL SFL); [exact G5 | exact MU | exact WM |]. apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil]. }
    assert (AG5' : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5').
    { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [exact AGD|]. intros a [_ [_ Hn]]; cbn [outside]; lia. }
    clear MU WM AGD G5 AG5.
    assert (ZA : zarr m5' Bx data).
    { split; [| split; [| exact DRNG]].
      - pose proof (rw_cells_bytes_at _ _ _ _ BD) as X. cbn [cells_bytes cbytes] in X. rewrite app_nil_r in X. exact X.
      - eapply rw_cells_wr_at; [exact BD|]. (sl_lit_sizes; cbn [cells_size csize Nat.add]). lia. }
    change (rw_cells ssegs m5' HA (pkthdr_cells (Z_to_bv 64 sec) (Z_to_bv 64 usec) (mkHdr sec usec cap len))) in HH.
    name_sp sp (-4208)%Z.
    eapply evt_cut.
    { eapply PP; [rewrite Hsp; exact ST5 | unfold PP_FRAME; rewrite Hsp; (keep_hyps CEILV sp R lo P HA DA Bx data dw BU; lia) | exact HH | exact ZA | assumption | reflexivity | reflexivity | reflexivity | reflexivity
                 | (keep_hyps CEILV R P HA DA linktype Bx data dw W9; lia) | cbn [h_caplen]; (keep_hyps CEILV R P HA DA Bx data cap dw Hcap; lia) | (keep_hyps CEILV R P HA DA Bx data dw Hlen; lia) | cbn [h_len]; (keep_hyps CEILV R P HA DA Bx data len dw Hl32; lia) | left; rewrite Hsp; (keep_hyps CEILV sp R P HA DA Bx data dw R1; lia) | right; unfold rc_lo in LO; (keep_hyps CEILV H hptr K sp R CLc FB lo P HA DA self ps bq Bx alloc data dw m5' LO BU R1 W4 K4 G5'; lia) | unfold PP_FRAME; rewrite Hsp; unfold rc_lo in LO; (keep_hyps CEILV H hptr K sp R CLc FB lo P HA DA self ps bq Bx alloc data dw m5' LO BU W4 K4 G5'; lia)
                 | exact AH | clear -K2; Z.div_mod_to_equations; (keep_hyps Bx r0 q r q0 K2 H H0 H4; lia) | unfold rc_spmain in R3; (keep_hyps CEILV R P HA DA Bx data dw R2 R3 SP47; lia) | (keep_hyps CEILV H hptr K sp R CLc FB lo P HA DA self ps bq Bx alloc data dw m5' W4 K4; lia) | unfold rc_lo in LO; (keep_hyps CEILV sp R lo P HA DA Bx data dw LO BU R1 SPW; lia) | (keep_hyps CEILV R P HA DA Bx data dw K1; lia) ]. }
    cbv beta. intros ms' PO. destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m6 & -> & MU6 & WM6 & MI6 & ST6 & HH6 & ZA6).
    rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 88036)) with (Z_to_bv 64 88036) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    cbn [h_caplen] in MU6. unfold PP_FRAME in MU6.
    set (hdr' := fst (pcapint_post_process linktype swapped (mkHdr sec usec cap len) data)) in *.
    set (d' := snd (pcapint_post_process linktype swapped (mkHdr sec usec cap len) data)) in *.
    pose proof (PPLEN linktype swapped (mkHdr sec usec cap len) data) as LEN'. fold d' in LEN'.
    pose proof (PPSEC linktype swapped (mkHdr sec usec cap len) data) as [SEC' USEC']. fold hdr' in SEC', USEC'. cbn [h_sec h_usec] in SEC', USEC'.
    pose proof (PPRNG linktype swapped (mkHdr sec usec cap len) data ltac:(cbn [h_caplen]; lia) ltac:(cbn [h_len]; lia) Hlen) as [RC' RL']. fold hdr' in RC', RL'.
    assert (AGS : agrees_on (fun a => outside [(bv_unsigned sp + -4208 - 32, bv_unsigned sp + -4208); (HA + 20, HA + 24); (Bx, Bx + cap)]%Z a) m5' m6)
      by (eapply agrees_on_of_munch; [exact MU6 | exact WM6 | intros a _ Ho; exact Ho]).
    apply (agrees_rw_cells _ _ _ _ _ AGS) in FR5; [| intros a Ha; (cl_lit_hyps; sl_lit_sizes; cbn [outside cells_size csize Nat.add] in *); unfold rc_lo in LO; (keep_hyps CEILV H hptr K sp R CLc FB lo P HA DA self ps bq Bx alloc data cap dw m5' a LO BU R1 Hcap W4 K4 G5' Ha; lia)].
    apply (agrees_rw_cells _ _ _ _ _ AGS) in HD'; [| intros a Ha; (cl_lit_hyps; sl_lit_sizes; cbn [outside cells_size csize Nat.add] in *); unfold rc_lo in LO; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGS) in CELLS; [| intros a Ha; (cl_lit_hyps; sl_lit_sizes; cbn [outside cells_size csize Nat.add] in *); unfold rc_lo in LO; (keep_hyps CEILV H hptr K sp R CLc FB lo P HA DA self ps bq Bx alloc data cap dw m5' a LO BU R1 Hcap W4 L4 BP' G5' Ha; lia)].
    apply (agrees_rw_cells _ _ _ _ _ AGS) in PRIV; [| intros a Ha; (cl_lit_hyps; sl_lit_sizes; cbn [outside cells_size csize Nat.add] in *); unfold rc_lo in LO; (keep_hyps CEILV H hptr K sp R CLc FB lo P HA DA self ps bq Bx alloc data cap dw m5' a LO BU R1 Hcap W4 L4 BP' G5' Ha; lia)].
    apply (agrees_rw_cells _ _ _ _ _ AGS) in BT; [| intros a Ha; (cl_lit_hyps; sl_lit_sizes; cbn [outside cells_size csize Nat.add] in *); unfold rc_lo in LO; lia].
    (* [comment removed for export] *)
    destruct ZA6 as (ZB & ZW & ZR).
    pose proof (bytes_wr_rw_cells _ _ _ ZB ltac:(rewrite zbytes_length; exact ZW)) as BD6. rewrite zbytes_length in BD6.
    pose proof (rw_cells_uncut _ _ _ _ _ BD6 BT ltac:((sl_lit_sizes; cbn [cells_size csize Nat.add]); rewrite LEN'; lia)) as BUF6.
    merge_all BUF6.
    replace (length d' + (Z.to_nat alloc - length data + 0))%nat with (Z.to_nat alloc) in BUF6 by lia. rewrite app_nil_r in BUF6.
    rewrite (surjective_pairing (pcapint_post_process linktype swapped _ data)). fold hdr' d'. cbn [set_bufdata pc_self pc_rfile pc_bufsize pc_bufalloc pc_buffer pc_swapped
      pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_priv].
    assert (G6 : GIo K R ps (CLc ++ [(self, P, 664%Z); (bq, Bx, alloc)]) FB m6).
    { eapply (GIo_pcap_frame K HFL SFL); [exact G5' | exact MU6 | exact WM6 |].
      apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia|]. apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo, rc_spmain in *; lia|].
      apply Forall_cons; [| apply Forall_nil]. right. unfold iv_in_block. apply Exists_cons_tl, Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    apply evt_done. eapply np_ok_tail; [exact ST6 | exact FR5 | exact MI6 | | exact RC' | exact RL'].
    split; [exact G6|]. split.
    { exists Afx. split; [exact Hin|]. exists Bx, 0%Z, jx', padx, (zbytes d' ++ firstn (Z.to_nat alloc - length data) (skipn (length data) bsx')).
      split; [reflexivity|]. split; [exact CELLS|]. split; [unfold PCAP_PRIV_OFF; exact PRIV|]. split; [cbn [pc_bufalloc]; exact BUF6|].
      split; [cbn [pc_bufdata set_bufdata]; replace (length d') with (length (zbytes d')) by (apply zbytes_length);
              rewrite firstn_app, firstn_all, Nat.sub_diag; cbn [firstn]; rewrite app_nil_r; reflexivity|].
      split; [reflexivity|].
      unfold pcap_wf in *. cbn [set_bufdata pc_snapshot pc_bufsize pc_bufalloc pc_bufdata pc_break_loop pc_tstamp_precision pc_version_major pc_version_minor
                                 pc_linktype pc_linktype_ext pc_header pc_priv sf_hdrsize] in *. rewrite LEN'. exact WF. }
    split. { eapply agrees_on_trans; [exact AG5'|]. eapply agrees_on_weaken; [exact AGS|]. intros a [[Ha|Ha] [Hn1 Hn2]]; cbn [outside]; [unfold rc_lo in LO; (keep_hyps CEILV H hptr K sp R CLc FB lo P HA DA self ps bq Bx alloc data cap dw m6 a LO BU Hcap W4 K4 G6 Ha Hn1; lia)|].
             destruct (np_CLc_facts _ _ _ _ G5' Ha) as [Hc Hnb]. unfold rc_lo in LO. split; [lia|]. split; [lia|]. split; [| exact Logic.I].
             intros Hin'. apply Hnb. unfold in_block. apply Exists_cons_tl, Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    split. { unfold hdr_cells. rewrite SEC', USEC'. exact HH6. }
    split; [reflexivity|]. split; [exact HD'|]. split; [reflexivity| exact OF5].
  Qed.
  End Sz9.
  Lemma np_finish : ltac:(let t := eval cbv delta [np_finish__stmt] in np_finish__stmt in exact t).
  Proof using AD AH BU HFL LO P1 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 SFL SP47 SPM SPW W9. all: natfold_lits. intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x3 x4 x5 x6 x7 t3' t4' t5' t6' ws wu m5 ps bq Bx bsz alloc data eb sec usec cap len dw fj. ltac2:(SecDiet.SzSec.closeP 'np_finish__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Lemma implM_pure_k : forall {St A} (c : @M St A) st Q ms r st1,
    c st = Ret (Ok (r, st1)) -> implM ssegs (mret r) st1 Q ms -> implM ssegs c st Q ms.
  Proof using Type. all: natfold_lits. pin_using tt. intros St A c st Q ms r st1 E Hk. unfold implM in *. rewrite E. exact Hk. Qed.

  (* [comment removed for export] *)
  Definition np_nread__stmt : Prop := forall (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' x3 x4 x5 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (bq : hptr) (Bx bsz alloc : Z) (data eb : list Z) (sec usec cap len : Z) (dw : cell) (fj : list byte),
      stk ssegs m5 lo (bv_unsigned sp + -4208) ->
      rw_cells ssegs m5 (bv_unsigned sp + -4208) [CB 4136 fj; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> mem_inv ssegs m5 ->
      GIo K R ps (CLc ++ pcap_blocks (pv bq bsz alloc data eb) P Bx 0) FB m5 ->
      PCAPR (hptr:=hptr) P (pv bq bsz alloc data eb) (pcap_blocks (pv bq bsz alloc data eb) P Bx 0) FB m5 ->
      agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells ssegs m5 HA [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)] -> rw_cells ssegs m5 DA [dw] -> csize dw = 8%nat ->
      (0 <= cap <= bsz)%Z -> (cap <= snapshot)%Z -> (0 <= len < 2^32)%Z -> ps_outfile ps = o ->
      implM ssegs (np_read_model MOps (prims HO fo_nop sites) f (pv bq bsz alloc data eb) (mkHdr sec usec cap len) cap) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -4208)) gp tp t0' t1' t2' (Z_to_bv 64 P) (Z_to_bv 64 HA) (Z_to_bv 64 Bx) a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 DA) (Z_to_bv 64 Af) (Z_to_bv 64 cap) x3 x4 x5 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x157b0) fc None m5 (seg_rom ssegs)).
  Section Sz11.
  Variables ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' x3 x4 x5 t3' t4' t5' t6' m5 ps bq Bx bsz alloc data eb sec usec cap len dw fj : ltac2:(SecDiet.SzSec.tyM 'np_nread__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma np_nread__body : ltac2:(SecDiet.SzSec.bodyP 'np_nread__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AD AH ALN BU FERROR FMT FREAD HAL HFL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 SFL SNPRINTF SP47 SPM SPW TP W1 W10 W5 W6 W7 W8 W9 WHS. all: natfold_lits. pin_using (fun (AD AH ALN BU FERROR FMT FREAD HAL HFL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 SFL SNPRINTF SP47 SPM SPW TP W1 W10 W5 W6 W7 W8 W9 WHS : unit) => tt).
    intros ST5 FR5 MI5 G5 PC5 AG5 HH HD Hd Hcap Hcs Hl32 OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof PC5 as PC5'.
    destruct PC5 as (Afx & Hin & (Bx' & Ix & jx' & padx & bsx' & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    norm_p. unfold sf_cells in PRIV. cbn [sf_hdrsize sf_lengths_swapped sf_scale_type] in PRIV.
    subst Ix. assert (EBX : Bx' = Bx) by congruence. subst Bx'. clear EPB.
    pose proof WF as (_ & W2' & W3 & W4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & WBB). cbn [pc_bufsize pc_bufalloc pc_bufdata length] in W2', W3, W4, WBB.
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G5 ltac:(right; left; reflexivity)) as (K1 & K2 & K3 & K4 & K5 & K6).
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G5 ltac:(left; reflexivity)) as (L1 & L2 & L3 & L4 & L5 & L6).
    assert (BP' : (Bx + alloc <= P \/ P + 664 <= Bx)%Z).
    { pose proof (PB_apart K _ _ _ _ _ _ (pv bq bsz alloc data eb) P Bx 0 G5 eq_refl) as [APB _]. unfold pv, psize, is_ng in APB. cbn [pc_bufalloc pc_priv] in APB. unfold PCAP_SF_TOTAL in APB. lia. }
    (* [comment removed for export] *)
    apply (rw_cells_split_CB ssegs m5 _ [] (Z.to_nat alloc) _ [] [Z.to_nat cap; Z.to_nat alloc - Z.to_nat cap]%nat) in BUF; [| cbn; lia].
    cbn [mk_CB_cells app] in BUF.
    destruct (rw_cells_cut _ _ _ 1 BUF) as [BD BT]. clear BUF. (cbn [firstn skipn] in BD, BT; sl_lit_sizes_in BD; sl_lit_sizes_in BT; cbn [firstn skipn cells_size csize Nat.add] in BD, BT).
    unfold np_read_model, read_fail_msg, errmsg_for_errno. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_fread e_ferror e_last_errno prims pc_buffer pc_linktype pc_swapped pc_bufdata set_bufdata set_errbuf
      pc_self pc_rfile pc_bufsize pc_bufalloc pc_version_major pc_version_minor pc_snapshot pc_linktype_ext pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_priv].
    hide BT. hide PRIV. hide CELLS. hide HH. hide HD.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl ssegs m5) as WM.
    unfold implM. iprefix.
    do 2 step. rewrite (zext32_shifts_lit cap) by lia. do 3 step.
    name_sp sp (-4208)%Z.
    apply evt_done. eapply (implM_bind ssegs).
    { apply implM_mget. cbn [eval_rdest fo_site fo_nop]. unfold blk_addr.
      rewrite (GIo_addr HO K HAL _ _ _ _ _ _ _ _ G5 ltac:(apply in_or_app; left; apply in_or_app; right; right; left; reflexivity)).
      rewrite Z.add_0_r.
      eapply FREAD; [| exact HinF | reflexivity | reflexivity | reflexivity | reflexivity | lia | exact BD | ].
      { split; [exact G5|]. split; [rewrite Hsp; exact ST5|]. split; [unfold rc_lo; lia|]. split; [unfold STDIO_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [exact MI5|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
      left. intros a Ha. apply in_block_app. right. unfold in_block. apply Exists_cons_tl, Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    intros got ps6 ms6 PO. cbv beta in PO.
    destruct PO as (av & m6 & junk6 & E & OF6 & MI6 & ST6 & AG6 & G6 & -> & GOTL & GOTR & HD6).
    unfold hpost_regs in E. all: natfold_lits. destruct_exs E. subst ms6. rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 88004)) with (Z_to_bv 64 88004) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    unhide BT. unhide PRIV. unhide CELLS. unhide HH. unhide HD.
    assert (KEEP : forall A cs, rw_cells ssegs m5 A cs ->
              ((bv_unsigned sp + -4208 <= A) \/ (P <= A /\ A + Z.of_nat (cells_size cs) <= P + 664) \/ (Bx + cap <= A /\ A + Z.of_nat (cells_size cs) <= Bx + alloc))%Z ->
              rw_cells ssegs m6 A cs).
    { intros A cs HC HX. eapply agrees_rw_cells; [exact AG6 | exact HC |]. intros a Ha. destruct HX as [HX|[HX|HX]].
      - split; [left; lia| unfold rc_lo in LO; lia].
      - split; [| (keep_hyps CEILV sp R lo P HA DA Bx bsz alloc data cap dw A cs a Hcap WBB BP' HX Ha; lia)]. right. apply in_block_app. right. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia.
      - split; [| lia]. right. apply in_block_app. right. unfold in_block. apply Exists_cons_tl, Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    apply KEEP in FR5; [| left; lia]. apply KEEP in HH; [| left; lia]. apply KEEP in HD; [| left; lia].
    apply KEEP in CELLS; [| right; left; rewrite pcap_cells_gen_size by reflexivity; lia]. apply KEEP in PRIV; [| right; left; (sl_lit_sizes; cbn [cells_size csize Nat.add]); lia].
    apply KEEP in BT; [| right; right; (sl_lit_sizes; cbn [cells_size csize Nat.add]); lia]. clear KEEP.
    assert (AG06 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m6).
    { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [exact AG6|]. intros a [[Ha|Ha] _]; [split; [left; lia| unfold rc_lo in LO; lia]|].
      destruct (np_CLc_facts _ _ _ _ G5 Ha) as [Hc Hnb]. split; [right; apply in_block_app; left; exact Ha|].
      intros Hin'. apply Hnb. unfold in_block. apply Exists_cons_tl, Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    clear AG6 MI5 ST5 G5 PC5' AG5 MU WM.
    hide BT. hide PRIV. hide CELLS. hide HD. hide HD6.
    pose proof (munch_refl ([] : list (Z * Z)) m6) as MU. pose proof (wmono_refl ssegs m6) as WM.
    unfold implM. iprefix. step. rewrite (zx32_lit cap) by lia.
    destruct (Z.eq_dec (zlength got) cap) as [LEQ|LNE].
    - (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_eq _ _) LEQ). cbn [negb].
      step. if_cases Kq; try (zify_cond Kq; exfalso; unfold zlength in *; (keep_hyps CEILV R LEQ Kq; lia)).
      unhide BT. unhide PRIV. unhide CELLS. unhide HD. unhide HD6.
      assert (LG : length got = Z.to_nat cap) by (unfold zlength in LEQ; lia).
      pose proof (rw_cells_uncut _ _ _ _ _ HD6 BT ltac:((sl_lit_sizes; cbn [cells_size csize Nat.add]); lia)) as BUF6. cbn [app] in BUF6. merge_all BUF6.
      replace (length got + (Z.to_nat cap - length got + (Z.to_nat alloc - Z.to_nat cap + 0)))%nat with (Z.to_nat alloc) in BUF6 by (keep_hyps CEILV sp R lo P HA DA Bx bsz alloc data cap dw got Hcap WBB LG; lia).
      rewrite app_nil_r in BUF6.
      apply evt_done. eapply (np_finish _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 sec) (Z_to_bv 64 usec) m6 ps6 bq Bx bsz alloc got eb sec usec cap len dw fj);
        [exact ST6 | exact FR5 | exact MI6 | exact G6 | | exact AG06 | exact HH | exact HD | exact Hd | reflexivity | reflexivity | exact GOTR
        | unfold zlength in LEQ; lia | unfold zlength in LEQ; lia | exact Hl32 | congruence].
      exists Afx. split; [exact Hin|]. exists Bx, 0%Z, jx', padx, (map b8 got ++ junk6 ++ firstn (Z.to_nat alloc - Z.to_nat cap) (skipn (Z.to_nat cap) bsx')).
      split; [reflexivity|]. split; [exact CELLS|]. split; [unfold PCAP_PRIV_OFF; exact PRIV|]. split; [unfold pv; cbn [pc_bufalloc]; exact BUF6|].
      split; [unfold pv; cbn [pc_bufdata]; replace (length got) with (length (map b8 got)) by (apply length_map);
              rewrite firstn_app, firstn_all, Nat.sub_diag; cbn [firstn]; rewrite app_nil_r; reflexivity|].
      split; [reflexivity|].
      unfold pcap_wf, pv in *. cbn [set_bufdata pc_snapshot pc_bufsize pc_bufalloc pc_bufdata pc_break_loop pc_tstamp_precision pc_version_major pc_version_minor
                                 pc_linktype pc_linktype_ext pc_header pc_priv sf_hdrsize] in *. rewrite LG. repeat split; try (keep_hyps CEILV sp R P HA DA snapshot Bx data cap dw got W1 bsz W2' alloc W3 lo Hcap WBB brk W5 prec W6 vmaj W7 vmin W8 linktype W9 ltext W10 header hdrsize WF WHS; lia); try tauto.
    - (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_neq _ _) LNE). cbn [negb].
      step. if_cases Kq; try (zify_cond Kq; exfalso; unfold zlength in *; (keep_hyps CEILV R LNE Kq; lia)).
      do 3 step.
      apply evt_done. apply (implM_bind_assoc ssegs). name_sp sp (-4208)%Z. eapply (implM_bind ssegs).
      { eapply FERROR; [| exact HinF | reflexivity].
        split; [exact G6|]. split; [rewrite Hsp; exact ST6|]. split; [unfold rc_lo; lia|]. split; [unfold STDIO_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [exact MI6|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
      intros r ps7 ms7 PO. cbv beta in PO. destruct PO as (av7 & m7 & E & MI7 & ST7 & AG7 & G7 & -> & -> & ERRNO).
      unfold hpost_regs in E. all: natfold_lits. destruct_exs E. subst ms7. rewrite Hsp in *. unname_sp.
      replace (ret_pc (Z_to_bv 64 88092)) with (Z_to_bv 64 88092) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      unhide BT. unhide PRIV. unhide CELLS. unhide HD. unhide HD6.
      assert (KEEP : forall A cs, rw_cells ssegs m6 A cs ->
                ((bv_unsigned sp + -4208 <= A) \/ (P <= A /\ A + Z.of_nat (cells_size cs) <= P + 664) \/ (Bx <= A /\ A + Z.of_nat (cells_size cs) <= Bx + alloc))%Z ->
                rw_cells ssegs m7 A cs).
      { intros A cs HC HX. eapply agrees_rw_cells; [exact AG7 | exact HC |]. intros a Ha. destruct HX as [HX|[HX|HX]]; [left; lia| right | right].
        - apply in_block_app. right. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia.
        - apply in_block_app. right. unfold in_block. apply Exists_cons_tl, Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
      apply KEEP in FR5; [| left; lia]. apply KEEP in HH; [| left; lia]. apply KEEP in HD; [| left; lia].
      apply KEEP in CELLS; [| right; left; rewrite pcap_cells_gen_size by reflexivity; lia]. apply KEEP in PRIV; [| right; left; (sl_lit_sizes; cbn [cells_size csize Nat.add]); lia].
      apply KEEP in BT; [| right; right; (sl_lit_sizes; cbn [cells_size csize Nat.add]); lia]. apply KEEP in HD6; [| right; right; (sl_lit_sizes; cbn [cells_size csize Nat.add]); unfold zlength in GOTL; lia]. clear KEEP.
      assert (AG07 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m7).
      { eapply agrees_on_trans; [exact AG06|]. eapply agrees_on_weaken; [exact AG7|]. intros a [[Ha|Ha] _]; [left; lia| right; apply in_block_app; left; exact Ha]. }
      pose proof (rw_cells_uncut _ _ _ _ _ HD6 BT ltac:((sl_lit_sizes; cbn [cells_size csize Nat.add]); unfold zlength in GOTL; lia)) as BUF7. cbn [app] in BUF7. merge_all BUF7.
      replace (length got + (Z.to_nat cap - length got + (Z.to_nat alloc - Z.to_nat cap + 0)))%nat with (Z.to_nat alloc) in BUF7 by (unfold zlength in GOTL; lia).
      rewrite app_nil_r in BUF7.
      assert (PC7 : PCAPR (hptr:=hptr) P (pv bq bsz alloc got eb) [(self, P, 664%Z); (bq, Bx, alloc)] FB m7).
      { exists Afx. split; [exact Hin|]. exists Bx, 0%Z, jx', padx, (map b8 got ++ junk6 ++ firstn (Z.to_nat alloc - Z.to_nat cap) (skipn (Z.to_nat cap) bsx')).
        split; [reflexivity|]. split; [exact CELLS|]. split; [unfold PCAP_PRIV_OFF; exact PRIV|]. split; [unfold pv; cbn [pc_bufalloc]; exact BUF7|].
        split; [unfold pv; cbn [pc_bufdata]; replace (length got) with (length (map b8 got)) by (apply length_map);
                rewrite firstn_app, firstn_all, Nat.sub_diag; cbn [firstn]; rewrite app_nil_r; reflexivity|].
        split; [reflexivity|].
        unfold pcap_wf, pv in *. cbn [set_bufdata pc_snapshot pc_bufsize pc_bufalloc pc_bufdata pc_break_loop pc_tstamp_precision pc_version_major pc_version_minor
                                   pc_linktype pc_linktype_ext pc_header pc_priv sf_hdrsize] in *. unfold zlength in GOTL. repeat split; try (keep_hyps CEILV sp R P HA DA snapshot Bx data dw got W1 bsz W2' alloc W3 lo cap Hcap WBB GOTL brk W5 prec W6 vmaj W7 vmin W8 linktype W9 ltext W10 header hdrsize WF WHS; lia); try tauto. }
      clear AG7 MU WM. hide BUF7. hide PRIV. hide CELLS. hide HD. hide HH.
      pose proof (munch_refl ([] : list (Z * Z)) m7) as MU. pose proof (wmono_refl ssegs m7) as WM.
      destruct r.
      + (* [comment removed for export] *)
        destruct (ERRNO eq_refl) as [EN ER]. clear ERRNO. unfold utp in EN. rewrite <- TP in EN.
        pose proof (GIo_tls K _ _ _ _ _ G7) as [_ TB]. unfold tls_block_ok, utp in TB. rewrite <- TP in TB.
        eapply implM_pure_k; [reflexivity|]. cbn [fst snd].
        set (e := lc_errno (ps_libc ps6)) in *.
        unfold implM. iprefix. cbn [Z.b2z]. step. step. if_false. do 4 step. step. rewrite (sx32_s32 e) by lia. do 6 step.
        unhide BUF7. unhide PRIV. unhide CELLS. unhide HD. unhide HH.
        apply evt_done. eapply np_fmt; [exact ST7 | exact FR5 | exact MI7 | | lia |].
        { split; [exact G7|]. split; [exact PC7|]. split; [exact AG07|]. split; [exact HH|]. split; [reflexivity|]. split; [exact HD|]. split; [exact Hd| congruence]. }
        split; [|cbn; lia]. exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image ssegs m7 0x108d6 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (list_ascii_of_string "error reading dump file"%string) ++ [Z_to_bv 8 0])
                                   MI7 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia))).
      + (* [comment removed for export] *)
        eapply implM_pure_k; [reflexivity|]. cbn [fst snd].
        unfold implM. iprefix. cbn [Z.b2z]. step. step. if_true. step. rewrite (sextw_small cap) by lia. do 7 step.
        unhide BUF7. unhide PRIV. unhide CELLS. unhide HD. unhide HH.
        apply evt_done. unfold Msg.trunc_captured_u, PCAP_ERRBUF_SIZE.
        eapply np_snp; [exact ST7 | exact FR5 | exact MI7 | | | vm_compute; reflexivity | cbn; lia | | | vm_compute; reflexivity | apply args_ok_ints2].
        { split; [exact G7|]. split; [exact PC7|]. split; [exact AG07|]. split; [exact HH|]. split; [reflexivity|]. split; [exact HD|]. split; [exact Hd| congruence]. }
        { split; [|cbn; lia]. exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image ssegs m7 0x10c8d (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (list_ascii_of_string "truncated dump file; tried to read %u captured bytes, only got %zu"%string) ++ [Z_to_bv 8 0])
                                     MI7 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia))). }
        { cbn [length firstn]. constructor; [reflexivity|]. constructor; [reflexivity| constructor]. }
        pose proof (snprintf_length 256 "truncated dump file; tried to read %u captured bytes, only got %zu"%string [AInt cap; AInt (zlength got)]) as LS.
        change (Z.to_nat (256 - 1)) with 255%nat in LS. exact LS.
  Qed.
  End Sz11.
  Lemma np_nread : ltac:(let t := eval cbv delta [np_nread__stmt] in np_nread__stmt in exact t).
  Proof using AD AH ALN BU FERROR FMT FREAD HAL HFL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 SFL SNPRINTF SP47 SPM SPW TP W1 W10 W5 W6 W7 W8 W9 WHS. all: natfold_lits. intros ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' x3 x4 x5 t3' t4' t5' t6' m5 ps bq Bx bsz alloc data eb sec usec cap len dw fj. ltac2:(SecDiet.SzSec.closeP 'np_nread__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Lemma pfx_realloc : forall (bsx junk : list byte) (d : list Z) (M n : nat),
    firstn (length d) bsx = map b8 d -> (Nat.min n (length d) <= M)%nat -> (M <= length bsx)%nat ->
    firstn (length (firstn n d)) (firstn M bsx ++ junk) = map b8 (firstn n d).
  Proof using BU CEILV LO P1 R1 R2 SPW. all: natfold_lits. pin_using (fun (BU CEILV LO P1 R1 R2 SPW : unit) => tt).
    intros bsx junk d M n PFXd HM HL.
    rewrite length_firstn. rewrite firstn_app. rewrite firstn_firstn by lia.
    replace (Nat.min n (length d) - length (firstn M bsx))%nat with 0%nat by (rewrite length_firstn; lia). cbn [firstn]. rewrite app_nil_r.
    rewrite (Nat.min_l (Nat.min n (length d)) M) by lia.
    rewrite <- firstn_map, <- PFXd, firstn_firstn. reflexivity.
  Qed.

  Definition lor_ge_l__stmt : Prop := forall a b, (0 <= a)%Z -> (0 <= b)%Z -> (a <= Z.lor a b)%Z.
  Section Sz13.
  Variables a b : ltac2:(SecDiet.SzSec.tyM 'lor_ge_l__stmt "vv" @a).
  Lemma lor_ge_l__body : ltac2:(SecDiet.SzSec.bodyP 'lor_ge_l__stmt "vv").
  Proof using CEILV DA HA P sp. all: natfold_lits. pin_using (fun (CEILV DA HA P sp : unit) => tt).
    intros Ha Hb.
    set (c := Z.land b (Z.lnot a)).
    assert (Hc : (0 <= c)%Z) by (subst c; apply Z.land_nonneg; left; lia).
    assert (D : Z.land a c = 0%Z).
    { subst c. rewrite Z.land_comm, <- Z.land_assoc. rewrite (Z.land_comm (Z.lnot a) a), Z.land_lnot_diag, Z.land_0_r. reflexivity. }
    assert (E : Z.lor a b = Z.lor a c).
    { apply Z.bits_inj'. intros n Hn. subst c. rewrite !Z.lor_spec, Z.land_spec, Z.lnot_spec by lia.
      destruct (Z.testbit a n), (Z.testbit b n); reflexivity. }
    rewrite E, <- Z.lxor_lor, <- Z.add_nocarry_lxor by exact D. lia.
  Qed.
  End Sz13.
  Lemma lor_ge_l : ltac:(let t := eval cbv delta [lor_ge_l__stmt] in lor_ge_l__stmt in exact t).
  Proof using CEILV DA HA P sp. all: natfold_lits. intros a b. ltac2:(SecDiet.SzSec.closeP 'lor_ge_l__body "vv"). Qed.

  Lemma zfirstn_length_le' : forall n (l : list Z), (length (zfirstn n l) <= Z.to_nat n)%nat.
  Proof using BU CEILV LO P1 R1 R2 SPW. all: natfold_lits. pin_using (fun (BU CEILV LO P1 R1 R2 SPW : unit) => tt). intros. unfold zfirstn. rewrite length_firstn. lia. Qed.

  Lemma max_snaplen_le : forall d, (max_snaplen_for_dlt d <= 134217728)%Z.
  Proof using CEILV DA HA P sp. all: natfold_lits. pin_using (fun (CEILV DA HA P sp : unit) => tt). intros d. unfold max_snaplen_for_dlt, MAXIMUM_SNAPLEN. repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) end; lia. Qed.

  (* [comment removed for export] *)
  Definition np_normal__stmt : Prop := forall (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' x4 x5 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (sec usec cap len : Z) (dw : cell) (fj : list byte),
      stk ssegs m5 lo (bv_unsigned sp + -4208) ->
      rw_cells ssegs m5 (bv_unsigned sp + -4208) [CB 4136 fj; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> mem_inv ssegs m5 ->
      GIo K R ps (CLc ++ pcap_blocks p0 P B 0) FB m5 ->
      PCAPR (hptr:=hptr) P p0 (pcap_blocks p0 P B 0) FB m5 ->
      agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells ssegs m5 HA [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)] -> rw_cells ssegs m5 DA [dw] -> csize dw = 8%nat ->
      (0 <= cap <= snapshot)%Z -> (cap <= max_snaplen_for_dlt linktype)%Z -> (0 <= len < 2^32)%Z -> ps_outfile ps = o ->
      implM ssegs (np_norm_model MOps (prims HO fo_nop sites) p0 (mkHdr sec usec cap len) cap) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -4208)) gp tp t0' t1' t2' (Z_to_bv 64 P) (Z_to_bv 64 HA) (Z_to_bv 64 snapshot) a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 DA) (Z_to_bv 64 Af) (Z_to_bv 64 cap) (Z_to_bv 64 snapshot) x4 x5 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x15740) fc None m5 (seg_rom ssegs)).
  Section Sz16.
  Variables ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' x4 x5 t3' t4' t5' t6' m5 ps sec usec cap len dw fj : ltac2:(SecDiet.SzSec.tyM 'np_normal__stmt "vvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma np_normal__body : ltac2:(SecDiet.SzSec.bodyP 'np_normal__stmt "vvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AD AH ALN BU FERROR FMT FREAD HAL HFL HPL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 REALLOC SFL SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 WHS. all: natfold_lits. pin_using (fun (AD AH ALN BU FERROR FMT FREAD HAL HFL HPL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 REALLOC SFL SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 WHS : unit) => tt).
    intros ST5 FR5 MI5 G5 PC5 AG5 HH HD Hd Hcap Hcm Hl32 OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. pose proof (max_snaplen_range linktype) as MSR. pose proof W1 as W1'. unfold INT_MAX in MSR, W1'.
    pose proof PC5 as PC5'.
    destruct PC5 as (Afx & Hin & (Bx' & Ix & jx' & padx & bsx' & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    unfold p0 in *. norm_p. unfold sf_cells in PRIV. cbn [sf_hdrsize sf_lengths_swapped sf_scale_type] in PRIV.
    subst Ix. assert (EBX : Bx' = B) by congruence. subst Bx'. clear EPB.
    pose proof WF as (_ & W2' & W3 & W4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & WBB). cbn [pc_bufsize pc_bufalloc pc_bufdata length] in W2', W3, W4, WBB.
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G5 ltac:(right; left; reflexivity)) as (K1 & K2 & K3 & K4 & K5 & K6).
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G5 ltac:(left; reflexivity)) as (L1 & L2 & L3 & L4 & L5 & L6).
    assert (BP' : (B + bufalloc <= P \/ P + 664 <= B)%Z).
    { pose proof (PB_apart K _ _ _ _ _ _ (pv buffer bufsize bufalloc bufdata errbuf) P B 0 G5 eq_refl) as [APB _]. unfold pv, psize, is_ng in APB. cbn [pc_bufalloc pc_priv] in APB. unfold PCAP_SF_TOTAL in APB. lia. }
    unfold pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF in CELLS.
    cbn [app pc_bufsize pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_header pc_priv pk_next_pcap pk_cleanup_sf PK] in CELLS.
    unfold np_norm_model, grow_buffer. cbn [mo_bind mo_ret MOps e_fenter e_fret fo_enter fo_ret fo_nop prims e_realloc prims pc_bufsize pc_snapshot pc_rfile pc_buffer pc_bufdata
      pc_self pc_bufalloc pc_swapped pc_version_major pc_version_minor pc_linktype pc_linktype_ext pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_priv].
    hide BUF. hide PRIV. hide HH. hide HD.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl ssegs m5) as WM.
    unfold implM. iprefix. step. rewrite (sx32_small bufsize) by lia.
    destruct (Z.ltb_spec bufsize cap) as [GROW|NOGROW].
    - (* [comment removed for export] *)
      replace (bufsize <? cap) with true by (symmetry; apply Z.ltb_lt; lia).
      step. if_cases Kb; try (zify_cond Kb; exfalso; (keep_hyps CEILV sp R P HA DA B bufsize bufdata cap dw GROW Kb; lia)).
      (* [comment removed for export] *)
      step.
      pose proof (max_snaplen_le linktype) as MSL. assert (R0 : (0 <= cap - 1 < 2^27)%Z) by lia.
      step. step. rewrite (srliw_or (cap + -1) 1) by lia. pose proof (lor_shr_lt (cap + -1) 1 27 ltac:(lia) ltac:(lia) ltac:(lia)) as R1'.
      set (n1 := Z.lor (cap + -1) (Z.shiftr (cap + -1) 1)) in *.
      step. step. rewrite (srliw_or n1 2) by lia. pose proof (lor_shr_lt n1 2 27 ltac:(lia) ltac:(lia) R1') as R2'.
      set (n2 := Z.lor n1 (Z.shiftr n1 2)) in *.
      step. step. rewrite (srliw_or n2 4) by lia. pose proof (lor_shr_lt n2 4 27 ltac:(lia) ltac:(lia) R2') as R3'.
      set (n3 := Z.lor n2 (Z.shiftr n2 4)) in *.
      step. step. rewrite (srliw_or n3 8) by lia. pose proof (lor_shr_lt n3 8 27 ltac:(lia) ltac:(lia) R3') as R4'.
      set (n4 := Z.lor n3 (Z.shiftr n3 8)) in *.
      step. step. rewrite (srliw_or n4 16) by lia. pose proof (lor_shr_lt n4 16 27 ltac:(lia) ltac:(lia) R4') as R5'.
      set (n5 := Z.lor n4 (Z.shiftr n4 16)) in *.
      step. rewrite (addiw_small n5 1) by lia.
      assert (RU : roundup_pow2_u32 cap = (n5 + 1)%Z).
      { unfold roundup_pow2_u32, u32. rewrite (Z.mod_small (cap - 1)) by lia. replace (cap - 1)%Z with (cap + -1)%Z by lia.
        subst n1 n2 n3 n4 n5. rewrite Z.mod_small; [reflexivity| lia]. }
      rewrite RU.
      assert (GE : (cap <= n5 + 1)%Z).
      { pose proof (lor_ge_l (cap + -1) (Z.shiftr (cap + -1) 1) ltac:(lia) ltac:(apply Z.shiftr_nonneg; lia)) as G1. fold n1 in G1.
        pose proof (lor_ge_l n1 (Z.shiftr n1 2) ltac:(lia) ltac:(apply Z.shiftr_nonneg; lia)) as G2. fold n2 in G2.
        pose proof (lor_ge_l n2 (Z.shiftr n2 4) ltac:(lia) ltac:(apply Z.shiftr_nonneg; lia)) as G3. fold n3 in G3.
        pose proof (lor_ge_l n3 (Z.shiftr n3 8) ltac:(lia) ltac:(apply Z.shiftr_nonneg; lia)) as G4. fold n4 in G4.
        pose proof (lor_ge_l n4 (Z.shiftr n4 16) ltac:(lia) ltac:(apply Z.shiftr_nonneg; lia)) as G5'. fold n5 in G5'. lia. }
      clearbody n1 n2 n3 n4 n5.
      (* [comment removed for export] *)
      assert (K44 : forall (a1'' a2'' : word) (nb : Z) (mx : mem),
        nb = (if snapshot <? n5 + 1 then snapshot else n5 + 1)%Z -> mx = m5 ->
        evt ssegs (fun ms' => impl ssegs (at_node ssegs) (npeek ssegs)
            ((' (ok, p) <- (r <- prealloc HO buffer nb ;;
                            match r with
                            | Some b => mret (true, set_buffer b nb nb (zfirstn nb bufdata) (pv buffer bufsize bufalloc bufdata errbuf))
                            | None => mret (false, set_errbuf Msg.out_of_memory (pv buffer bufsize bufalloc bufdata errbuf))
                            end) ;;
              (if negb ok then mret ((-1)%Z, mkHdr sec usec cap len, p)
               else np_read_model MOps (prims HO fo_nop sites) f p (mkHdr sec usec cap len) cap)) ps)
            (epost (fun p => POSTQ p.1 p.2)) ms')
          (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -4208)) gp tp t0' t1' t2' (Z_to_bv 64 P) (Z_to_bv 64 HA) (Z_to_bv 64 snapshot) a1'' a2'' a3' a4' a5' a6' a7'
                   (Z_to_bv 64 DA) (Z_to_bv 64 Af) (Z_to_bv 64 (cap + -1)) (Z_to_bv 64 nb) x4 x5 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x15780) fc None mx (seg_rom ssegs))).
      2:{ step. if_cases Kc; zify_cond Kc.
          - replace (if snapshot <? n5 + 1 then snapshot else n5 + 1)%Z with (n5 + 1)%Z by (destruct (Z.ltb_spec snapshot (n5 + 1)); lia).
            apply (K44 _ _ (n5 + 1)%Z); [destruct (Z.ltb_spec snapshot (n5 + 1)); lia | reflexivity].
          - step. replace (if snapshot <? n5 + 1 then snapshot else n5 + 1)%Z with snapshot by (destruct (Z.ltb_spec snapshot (n5 + 1)); lia).
            apply (K44 _ _ snapshot); [destruct (Z.ltb_spec snapshot (n5 + 1)); lia | reflexivity]. }
      intros a1'' a2'' nb mx Hnb ->.
      assert (NB1 : (cap <= nb <= snapshot)%Z) by (rewrite Hnb; destruct (Z.ltb_spec snapshot (n5 + 1)); lia).
      assert (NB2 : (nb <= 2^27)%Z) by (rewrite Hnb; destruct (Z.ltb_spec snapshot (n5 + 1)); lia).
      clear Hnb.
      unhide BUF.
      step. do 2 step. rewrite (zext32_shifts_lit nb) by lia. step.
      (* [comment removed for export] *)
      apply evt_done. apply (implM_bind_assoc ssegs). name_sp sp (-4208)%Z. eapply (implM_bind ssegs).
      { replace (CLc ++ [(self, P, 664%Z); (buffer, B, bufalloc)]) with ((CLc ++ [(self, P, 664%Z)]) ++ (buffer, B, bufalloc) :: []) in G5
          by (rewrite <- app_assoc; reflexivity).
        eapply REALLOC; [| reflexivity | reflexivity | lia | exact BUF].
        split; [exact G5|]. split; [rewrite Hsp; exact ST5|]. split; [unfold rc_lo; lia|]. split; [unfold MALLOC_STACK; rewrite Hsp; lia|].
        split; [rewrite Hsp; lia|]. split; [exact MI5|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
      intros [bq'|] ps6 ms6 PO; cbv beta iota in PO.
      + destruct PO as (av & m6 & E & OFr & MI6 & ST6 & AG6 & (A' & junk6 & -> & G6 & NEW)).
        unfold hpost_regs in E. all: natfold_lits. destruct_exs E. subst ms6. rewrite Hsp in *. unname_sp.
        replace (ret_pc (Z_to_bv 64 87952)) with (Z_to_bv 64 87952) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        rewrite app_nil_r in AG6, G6.
        pose proof (GIo_block_ok K _ _ _ _ _ _ G6 ltac:(left; reflexivity)) as (N1 & N2 & N3 & N4 & N5 & N6). cbn [cb_addr cb_size fst snd] in N1, N2, N3, N4, N5, N6.
        assert (LBS : length bsx' = Z.to_nat bufalloc) by (destruct BUF as [[WFB _] _]; cbn in WFB; exact (proj1 WFB)).
        unhide PRIV. unhide HH. unhide HD.
        assert (KEEP : forall A cs, rw_cells ssegs m5 A cs -> ((bv_unsigned sp + -4208 <= A) \/ (P <= A /\ A + Z.of_nat (cells_size cs) <= P + 664))%Z -> rw_cells ssegs m6 A cs).
        { intros A cs HC HX. eapply agrees_rw_cells; [exact AG6 | exact HC |]. intros a Ha. destruct HX as [HX|HX]; [left; lia| right].
          apply in_block_app. right. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
        apply KEEP in FR5; [| left; lia]. apply KEEP in HH; [| left; lia]. apply KEEP in HD; [| left; lia].
        apply KEEP in CELLS; [| right; (sl_lit_sizes; cbn [cells_size csize Nat.add]); lia]. apply KEEP in PRIV; [| right; (sl_lit_sizes; cbn [cells_size csize Nat.add]); lia]. clear KEEP.
        assert (G6' : GIo K R ps6 (CLc ++ [(self, P, 664%Z); (bq', A', nb)]) FB m6).
        { eapply (GIo_perm K HPL); [exact G6|]. rewrite app_comm_cons. change ((self, P, 664%Z) :: [(bq', A', nb)]) with ([(self, P, 664%Z)] ++ [(bq', A', nb)]).
          rewrite app_assoc. apply Permutation.Permutation_cons_append. }
        assert (AG06 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m6).
        { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [exact AG6|]. intros a [[Ha|Ha] _]; [left; lia| right; apply in_block_app; left; exact Ha]. }
        pose proof (PB_apart K _ _ _ _ _ _ (pv bq' nb nb (zfirstn nb bufdata) errbuf) P A' 0 G6' eq_refl) as [APB' _].
        unfold pv, psize, is_ng in APB'. cbn [pc_bufalloc pc_priv] in APB'. unfold PCAP_SF_TOTAL in APB'.
        clear AG6 G6 ST5 MI5 AG5 PC5' G5 BUF MU WM.
        eapply (implM_retb ssegs). cbv beta iota. cbn [negb set_buffer pc_self pc_rfile pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext
                                                    pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_priv].
        hide NEW. hide PRIV. hide HH. hide HD.
        pose proof (munch_refl [(P + 20, P + 32)]%Z m6) as MU. pose proof (wmono_refl ssegs m6) as WM.
        unfold implM. iprefix. step. if_cases Kz; try (zify_cond Kz; exfalso; (keep_hyps CEILV sp R P HA DA B bufalloc bufdata dw bsx' A' N1 Kz; lia)).
        unhide HH. step. rewrite (sx32_small cap) by lia. hide HH. step. step. step.
        unhide NEW. unhide PRIV. unhide HH. unhide HD.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          assert (AGP : agrees_on (fun a => outside [(P + 20, P + 32)]%Z a) m6 mm) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]);
          rename mm into m6' end.
        apply (agrees_rw_cells _ _ _ _ _ AGP) in NEW; [| intros a Ha; (sl_lit_sizes_in Ha; sl_lit_sizes; cbn [outside cells_size csize Nat.add] in Ha |- *); clear - Ha APB' W1' W3; lia].
        apply (agrees_rw_cells _ _ _ _ _ AGP) in HH; [| intros a Ha; (sl_lit_sizes_in Ha; sl_lit_sizes; cbn [outside cells_size csize Nat.add] in Ha |- *); unfold rc_lo in LO; lia].
        apply (agrees_rw_cells _ _ _ _ _ AGP) in HD; [| intros a Ha; cbn [cells_size] in Ha; rewrite Hd in Ha; cbn [outside]; unfold rc_lo in LO; lia].
        apply (agrees_rw_cells _ _ _ _ _ AGP) in PRIV; [| intros a Ha; (sl_lit_sizes_in Ha; sl_lit_sizes; cbn [outside cells_size csize Nat.add] in Ha |- *); lia].
        assert (G6'' : GIo K R ps6 (CLc ++ [(self, P, 664%Z); (bq', A', nb)]) FB m6').
        { eapply (GIo_pcap_frame K HFL SFL); [exact G6' | exact MU | exact WM |].
          apply Forall_cons; [| apply Forall_nil]. right. unfold iv_in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
        assert (AG06' : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m6').
        { eapply agrees_on_trans; [exact AG06|]. eapply agrees_on_weaken; [exact AGP|]. intros a [[Ha|Ha] _]; cbn [outside]; [unfold rc_lo in LO; lia|].
          destruct (np_CLc_facts _ _ _ _ G6' Ha) as [Hc Hnb]. split; [| exact Logic.I]. intros Hin'. apply Hnb. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
        merge_all NEW. replace (Z.to_nat (bufalloc `min` nb) + (Z.to_nat (nb - bufalloc `min` nb) + 0))%nat with (Z.to_nat nb) in NEW by (keep_hyps CEILV sp R lo P HA DA B bufalloc bufdata dw nb A' bsx' K3; lia). rewrite app_nil_r in NEW.
        apply evt_done. eapply (np_nread _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6' ps6 bq' A' nb nb (zfirstn nb bufdata) errbuf sec usec cap len dw fj);
          [exact ST6 | exact FR5 | exact MI6 | exact G6'' | | exact AG06' | exact HH | exact HD | exact Hd | lia | lia | exact Hl32 | congruence].
        exists Afx. split; [exact Hin|]. exists A', 0%Z, jx', padx, (firstn (Z.to_nat (bufalloc `min` nb)) bsx' ++ junk6).
        split; [reflexivity|]. split; [exact CELLS|]. split; [unfold PCAP_PRIV_OFF; exact PRIV|]. split; [unfold pv; cbn [pc_bufalloc]; exact NEW|].
        split; [unfold pv, zfirstn; cbn [pc_bufdata]; apply pfx_realloc; [exact PFX | (keep_hyps CEILV sp R lo P HA DA B bufsize bufalloc bufdata snapshot cap dw nb A' bsx' W4; lia) | (keep_hyps CEILV sp R lo P HA DA B bufalloc bufdata dw nb A' bsx' LBS; lia)]|].
        split; [reflexivity|].
        unfold pcap_wf, pv in *. cbn [pc_snapshot pc_bufsize pc_bufalloc pc_bufdata pc_break_loop pc_tstamp_precision pc_version_major pc_version_minor
                                   pc_linktype pc_linktype_ext pc_header pc_priv sf_hdrsize] in *.
        pose proof (zfirstn_length_le' nb bufdata) as ZL. unfold zfirstn. rewrite length_firstn. repeat split; try (keep_hyps CEILV sp R P HA DA B bufalloc bufdata snapshot dw nb A' bsx' W1 N3 NB2 lo brk W5 prec W6 vmaj W7 vmin W8 linktype W9 ltext W10 bufsize header hdrsize WF WHS; lia); try tauto.
      + (* [comment removed for export] *)
        destruct PO as (av & m6 & E & OFr & MI6 & ST6 & AG6 & -> & G6 & BUF6 & EN6).
        unfold hpost_regs in E. all: natfold_lits. destruct_exs E. subst ms6. rewrite Hsp in *. unname_sp.
        replace (ret_pc (Z_to_bv 64 87952)) with (Z_to_bv 64 87952) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        rewrite app_nil_r in AG6.
        replace ((CLc ++ [(self, P, 664%Z)]) ++ [(buffer, B, bufalloc)]) with (CLc ++ [(self, P, 664%Z); (buffer, B, bufalloc)]) in G6 by (rewrite <- app_assoc; reflexivity).
        unhide PRIV. unhide HH. unhide HD.
        assert (KEEP : forall A cs, rw_cells ssegs m5 A cs -> ((bv_unsigned sp + -4208 <= A) \/ (P <= A /\ A + Z.of_nat (cells_size cs) <= P + 664))%Z -> rw_cells ssegs m6 A cs).
        { intros A cs HC HX. eapply agrees_rw_cells; [exact AG6 | exact HC |]. intros a Ha. destruct HX as [HX|HX]; [left; lia| right].
          apply in_block_app. right. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
        apply KEEP in FR5; [| left; lia]. apply KEEP in HH; [| left; lia]. apply KEEP in HD; [| left; lia].
        apply KEEP in CELLS; [| right; (sl_lit_sizes; cbn [cells_size csize Nat.add]); lia]. apply KEEP in PRIV; [| right; (sl_lit_sizes; cbn [cells_size csize Nat.add]); lia]. clear KEEP.
        assert (AG06 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m6).
        { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [exact AG6|]. intros a [[Ha|Ha] _]; [left; lia| right; apply in_block_app; left; exact Ha]. }
        assert (PC6 : PCAPR (hptr:=hptr) P (pv buffer bufsize bufalloc bufdata errbuf) [(self, P, 664%Z); (buffer, B, bufalloc)] FB m6).
        { exists Afx. split; [exact Hin|]. exists B, 0%Z, jx', padx, bsx'. split; [reflexivity|].
          split; [unfold pv, pcap_cells, pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF;
                  cbn [app pc_bufsize pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_header pc_priv pk_next_pcap pk_cleanup_sf PK]; exact CELLS|].
          split; [unfold PCAP_PRIV_OFF; exact PRIV|]. split; [exact BUF6|]. split; [exact PFX|]. split; [reflexivity| exact WF]. }
        clear AG6 ST5 MI5 AG5 PC5' G5 BUF MU WM.
        (* [comment removed for export] *)
        pose proof PC6 as (Afy & _ & (By & Iy & jy & pady & bsy & EPBy & CELLSy & _ & _ & _ & _ & _)).
        apply pcap_cells_split4 in CELLSy as (_ & CE & _ & _); [|reflexivity].
        apply (rw_cells_split_CB ssegs m6 _ [] 304 _ [] [14; 242; 48]%nat) in CE; [|reflexivity]. cbn [mk_CB_cells app] in CE.
        destruct (rw_cells_cut _ _ _ 1 CE) as [CE1 CE']. (cbn [firstn skipn] in CE1, CE'; sl_lit_sizes_in CE1; sl_lit_sizes_in CE'; cbn [firstn skipn cells_size csize Nat.add] in CE1, CE').
        destruct (rw_cells_cut _ _ _ 1 CE') as [CE2 _]. clear CE CE'. (cbn [firstn skipn] in CE2; sl_lit_sizes_in CE2; cbn [firstn skipn cells_size csize Nat.add] in CE2).
        replace (P + 216 + Z.of_nat 14)%Z with (P + 230)%Z in CE2 by lia.
        eapply (implM_retb ssegs). cbv beta iota. cbn [negb].
        assert (LENM : length (map b8 Msg.out_of_memory ++ [Z_to_bv 8 0]) = 14%nat) by (vm_compute; reflexivity).
        hide PRIV. hide HH. hide HD. hide CELLS. hide CE2. hide BUF6.
        pose proof (munch_refl [(P + 216, P + 216 + 14)]%Z m6) as MU. pose proof (wmono_refl ssegs m6) as WM.
        unfold implM. iprefix. step. if_true. do 5 step.
        call (memcpy_specZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (P + 216)%Z 0x10df2%Z 14%Z (map b8 Msg.out_of_memory ++ [Z_to_bv 8 0]) (firstn 14 (pj_g jy)));
          [reflexivity | reflexivity | reflexivity
          | exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image ssegs m6 0x10df2 (map b8 Msg.out_of_memory ++ [Z_to_bv 8 0]) MI6 ltac:(vm_compute; reflexivity) ltac:((keep_hyps CEILV sp R P HA DA B bufdata dw; lia)) ltac:(rewrite LENM; cbn; (keep_hyps CEILV sp R P HA DA B bufdata dw; lia))))
          | rewrite LENM; reflexivity | (keep_hyps CEILV sp R P HA DA B bufdata dw; lia) | exact CE1 | unfold rc_lo in LO; (keep_hyps CEILV sp R P HA DA B bufdata dw L5; lia) | (keep_hyps CEILV H hptr K sp R CLc FB lo P HA DA B self buffer bufalloc bufdata dw m6 ps6 L4; lia) | (keep_hyps CEILV sp R P HA DA B bufdata dw; lia) | exact MI6 |].
        unhide PRIV. unhide HH. unhide HD. unhide CELLS. unhide CE2. unhide BUF6.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          assert (AGW : agrees_on (fun a => outside [(P + 216, P + 216 + 14)]%Z a) m6 mm) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]);
          rename mm into m7 end.
        apply (agrees_rw_cells _ _ _ _ _ AGW) in HH; [| intros a Ha; (cl_lit_hyps; sl_lit_sizes; cbn [outside cells_size csize Nat.add] in *); unfold rc_lo in LO; lia].
        apply (agrees_rw_cells _ _ _ _ _ AGW) in HD; [| intros a Ha; (cl_lit_hyps; sl_lit_sizes; cbn [outside cells_size csize Nat.add] in *); unfold rc_lo in LO; lia].
        apply (agrees_rw_cells _ _ _ _ _ AGW) in CE2; [| intros a Ha; (cl_lit_hyps; sl_lit_sizes; cbn [outside cells_size csize Nat.add] in *); lia].
        assert (G7 : GIo K R ps6 (CLc ++ [(self, P, 664%Z); (buffer, B, bufalloc)]) FB m7).
        { eapply (GIo_pcap_frame K HFL SFL); [exact G6 | exact MU | exact WM |].
          apply Forall_cons; [| apply Forall_nil]. right. unfold iv_in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
        assert (PC7 : PCAPR (hptr:=hptr) P (pv buffer bufsize bufalloc bufdata Msg.out_of_memory) [(self, P, 664%Z); (buffer, B, bufalloc)] FB m7).
        { lazymatch goal with PCm : rw_cells ssegs m7 (P + 216)%Z _ |- _ =>
            pose proof (rw_cells_uncut _ _ _ _ _ PCm CE2 ltac:(cbn; lia)) as EB7 end.
          change (pv buffer bufsize bufalloc bufdata Msg.out_of_memory) with (set_errbuf Msg.out_of_memory (pv buffer bufsize bufalloc bufdata errbuf)).
          eapply (PCAPR_errbuf _ _ _ _ _ _ _ _ _ _ _ _ G6 PC6 AGW); [| exact EB7 | rewrite cells_size_app; cbn; lia].
          intros a Ha Hn. cbn [outside]. (keep_hyps CEILV sp R P HA DA B bufdata dw a Hn; lia). }
        assert (AG07 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m7).
        { eapply agrees_on_trans; [exact AG06|]. eapply agrees_on_weaken; [exact AGW|]. intros a [[Ha|Ha] _]; cbn [outside]; [unfold rc_lo in LO; lia|].
          destruct (np_CLc_facts _ _ _ _ G6 Ha) as [Hc Hnb]. split; [| exact Logic.I]. intros Hin'. apply Hnb. unfold in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
        step. apply evt_done.
        eapply np_fail_tail; [eassumption | exact FR5 | eassumption | ].
        split; [exact G7|]. split; [unfold pv in PC7; cbn [set_errbuf] ; exact PC7|]. split; [exact AG07|]. split; [exact HH|]. split; [reflexivity|]. split; [exact HD|]. split; [exact Hd| congruence].
    - (* [comment removed for export] *)
      apply evt_done. eapply (implM_retb ssegs). cbv beta iota. cbn [negb].
      unfold implM. iprefix. step. if_cases Kb; try (zify_cond Kb; exfalso; (keep_hyps CEILV sp R P HA DA B bufsize bufdata cap dw NOGROW Kb; lia)). step.
      unhide BUF. unhide PRIV. unhide HH. unhide HD.
      apply evt_done. eapply (np_nread _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 ps buffer B bufsize bufalloc bufdata errbuf sec usec cap len dw fj);
        [exact ST5 | exact FR5 | exact MI5 | exact G5 | exact PC5' | exact AG5 | exact HH | exact HD | exact Hd | lia | lia | exact Hl32 | exact OF5].
  Qed.
  End Sz16.
  Lemma np_normal : ltac:(let t := eval cbv delta [np_normal__stmt] in np_normal__stmt in exact t).
  Proof using AD AH ALN BU FERROR FMT FREAD HAL HFL HPL HinF LO P1 P2 P4 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 REALLOC SFL SNPRINTF SP47 SPM SPW TP W1 W10 W2 W5 W6 W7 W8 W9 WHS. all: natfold_lits. intros ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' x4 x5 t3' t4' t5' t6' m5 ps sec usec cap len dw fj. ltac2:(SecDiet.SzSec.closeP 'np_normal__body "vvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NpCtx.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.GIFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GIFacts__S3.Ifaces.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.PcapRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.Pcap_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.Pcap_iface_pp.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_pure.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_small.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Pcap_iface__S3.F_pcap_next_ex.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_open.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_pcap_err__S3.F_pcap_fopen.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.PP_kit.TwB.
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
(* [comment removed for export] *)
Local Ltac lia ::= clear_unpinned; try gio_ceil_fact; try (ceil_ok; ceil_mentioned; ceil_facts); pinned_lia_core.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section WithCeil.
Context {CEILV : CEIL}.
Section NpCtx.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr) (sites : stack_site -> Z).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.
  Hypothesis HPL : heap_perm_law K.
  Hypothesis HAL : heap_addr_law K HO.
  Hypothesis FREAD : fread_stmt_o HO K.
  Hypothesis FERROR : ferror_stmt_o HO K.
  Hypothesis FMT : fmt_errmsg_stmt K.
  Hypothesis SNPRINTF : snprintf_spec_stmt K.
  Hypothesis REALLOC : realloc_stmt_o HO K.
  Hypothesis PP : post_process_stmt.

  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (R : rctx) (CLc FB : list (cblock (hptr:=hptr))) (lo P HA DA B Af : Z) (m : mem) (o : option hptr).
  Variables (self buffer f : hptr) (bufsize bufalloc : Z) (bufdata : list Z) (swapped : bool)
            (vmaj vmin snapshot linktype ltext prec brk : Z) (errbuf : list Z) (header : pkthdr)
            (hdrsize : Z) (lsw : lenswap_t) (scl : sf_scale_t) (j : pcap_junk) (pad bs : list byte).
  Definition p0 : pcap hptr hptr :=
    mkPcap self f bufsize bufalloc buffer bufdata swapped vmaj vmin snapshot linktype ltext prec brk errbuf header (PrivPcap (mkSf hdrsize lsw scl)).
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
  Hypothesis P1 : (0 < P)%Z.  Hypothesis P2 : (P mod 16 = 0)%Z.  Hypothesis P4 : (P + 664 <= CEILZ)%Z.
  Hypothesis P5 : (P + 664 <= 65536 \/ 352256 <= P)%Z.  Hypothesis P6 : (P + 664 <= utp R - 200 \/ utp R - 200 + 4096 <= P)%Z.
  Hypothesis A1 : (0 < Af)%Z.  Hypothesis A4 : (Af + 1264 <= CEILZ)%Z.
  Hypothesis W1 : (1 <= snapshot <= INT_MAX)%Z.  Hypothesis W2 : (0 <= bufsize < 2^32)%Z.
  Hypothesis W5 : brk = 0%Z.  Hypothesis W6 : prec = 0%Z.
  Hypothesis W7 : (0 <= vmaj < 2^16)%Z.  Hypothesis W8 : (0 <= vmin < 2^16)%Z.
  Hypothesis W9 : (0 <= linktype < 2^31)%Z.  Hypothesis W10 : (-2^31 <= ltext < 2^31)%Z.
  Hypothesis WHS : (hdrsize = 16 \/ hdrsize = 24)%Z.

  Let POSTQ := next_packet_post K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CLc FB lo P HA DA m o.

  (* [comment removed for export] *)
  Definition np_cells (bsz Bx : Z) (jx : pcap_junk) : list cell :=
    pcap_cells (set_buffer buffer bsz bsz [] p0) P Bx Af jx.

  (* [comment removed for export] *)
  Definition np_epilogue__stmt : Prop := forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x0 x1 x2 x3 x4 x5 x6 x7 t3' t4' t5' t6' : word) (m5 : mem) (fj : list byte) (Q : machine_state -> Prop),
      stk usegs m5 lo (bv_unsigned sp + -4208) ->
      rw_cells usegs m5 (bv_unsigned sp + -4208) [CB 4136 fj; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> mem_inv usegs m5 ->
      (forall t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'',
          stk usegs m5 lo (bv_unsigned sp) ->
          Q (MS (mkR ra sp gp tp t0'' t1'' t2'' s0 s1 a0' a1'' a2'' a3'' a4'' a5'' a6'' a7'' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3'' t4'' t5'' t6'')
                F (ret_pc ra) fc None m5 (seg_rom usegs))) ->
      evt usegs Q
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -4208)) gp tp t0' t1' t2' x0 x1 a0' a1' a2' a3' a4' a5' a6' a7'
                 x2 x3 x4 x5 x6 x7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x15cec) fc None m5 (seg_rom usegs)).
  Section Sz1.
  Variables ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x0 x1 x2 x3 x4 x5 x6 x7 t3' t4' t5' t6' m5 fj Q : ltac2:(SecDiet.SzSec.tyM 'np_epilogue__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma np_epilogue__body : ltac2:(SecDiet.SzSec.bodyP 'np_epilogue__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using BU CEILV DA HA P. all: natfold_lits. pin_using (fun (BU CEILV DA HA P : unit) => tt).
 intros ST5 FR5 MI5 HQ.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl usegs m5) as WM.
    destruct (rw_cells_cut _ _ _ 1 FR5) as [FRJ FRS]. clear FR5. (cbn [firstn skipn] in FRJ, FRS; sl_lit_sizes_in FRJ; sl_lit_sizes_in FRS; cbn [firstn skipn cells_size csize Nat.add] in FRJ, FRS).
    lazymatch type of FRS with rw_cells _ _ ?nfA _ => replace nfA with (bv_unsigned sp + -72)%Z in FRS by lia end.
    do 13 step.
    release_frame FRJ ST5 (bv_unsigned sp + -72)%Z. release_frame FRS ST5 (bv_unsigned sp).
    apply evt_done. apply HQ. exact ST5.
  Qed.
  End Sz1.
  Lemma np_epilogue : ltac:(let t := eval cbv delta [np_epilogue__stmt] in np_epilogue__stmt in exact t).
  Proof using BU CEILV DA HA P. all: natfold_lits. intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x0 x1 x2 x3 x4 x5 x6 x7 t3' t4' t5' t6' m5 fj Q. ltac2:(SecDiet.SzSec.closeP 'np_epilogue__body "vvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition PCAPR_errbuf__stmt : Prop := forall Rx sx CLx Px (p : pcap hptr hptr) PB FBx (mx mx' : mem) (Q : Z -> Prop) cs e,
    GIo K Rx sx (CLx ++ PB) FBx mx -> PCAPR (hptr:=hptr) Px p PB FBx mx -> agrees_on Q mx mx' ->
    (forall a, in_block PB a -> ~ (Px + 216 <= a < Px + 472)%Z -> Q a) ->
    rw_cells usegs mx' (Px + 216) cs -> cells_size cs = 256%nat ->
    PCAPR (hptr:=hptr) Px (set_errbuf e p) PB FBx mx'.
  Section Sz2.
  Variables Rx sx CLx Px p PB FBx mx mx' Q cs e : ltac2:(SecDiet.SzSec.tyM 'PCAPR_errbuf__stmt "vvvvvvvvvvvv" @Rx).
  Lemma PCAPR_errbuf__body : ltac2:(SecDiet.SzSec.bodyP 'PCAPR_errbuf__stmt "vvvvvvvvvvvv").
  Proof using AD AH ALN BU LO P1 R1 R2 SPW. all: natfold_lits. pin_using (fun (AD AH ALN BU LO P1 R1 R2 SPW : unit) => tt).
    intros G PC AG HQ HCS Hsz.
    destruct PC as (Afx & Hin & (Bx & I & jx & padx & bsx & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    pose proof (psize_pos p) as PS. pose proof (PB_apart K _ _ _ _ _ _ _ _ _ _ G EPB) as [APB API].
    assert (Q1 : forall a, (Px <= a < Px + psize p)%Z -> ~ (Px + 216 <= a < Px + 472)%Z -> Q a).
    { intros a Ha Hn. apply HQ; [|exact Hn]. rewrite EPB. unfold pcap_blocks, in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. exact Ha. }
    apply pcap_cells_split4 in CELLS as (CA & CE & CH & CO); [|reflexivity].
    apply (rw_cells_split_CB usegs mx _ [] 304 _ [] [256; 48]%nat) in CE; [|reflexivity]. cbn [mk_CB_cells app] in CE.
    destruct (rw_cells_cut _ _ _ 1 CE) as [_ CE2]. clear CE. (cbn [firstn skipn] in CE2; sl_lit_sizes_in CE2; cbn [firstn skipn cells_size csize Nat.add] in CE2).
    replace (Px + 216 + Z.of_nat 256)%Z with (Px + 472)%Z in CE2 by lia.
    apply (agrees_rw_cells _ _ _ _ _ AG) in CA; [| intros a Ha; rewrite (pc_pre_size p Px Bx (C8 (Z_to_bv 64 Afx)) jx eq_refl) in Ha; apply Q1; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG) in CH; [| intros a Ha; (sl_lit_sizes_in Ha; cbn [cells_size csize hdr_cells Nat.add] in Ha); apply Q1; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG) in CO; [| intros a Ha; (sl_lit_sizes_in Ha; cbn [cells_size csize pc_ops Nat.add] in Ha); apply Q1; lia].
    apply (agrees_rw_cells _ _ _ _ _ AG) in CE2; [| intros a Ha; (sl_lit_sizes_in Ha; cbn [cells_size csize Nat.add] in Ha); apply Q1; lia].
    pose proof (rw_cells_uncut _ _ _ _ _ HCS CE2 ltac:(rewrite Hsz; lia)) as CE'.
    pose proof WF as (_ & _ & W3 & _).
    destruct (pcap_aux_agree p Px Bx I padx bsx mx mx' Q AG) as (BUF' & PRIV' & IFS');
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
             unfold pcap_cells. replace (set_header (pc_header p) p) with p in J by (destruct p; reflexivity).
             destruct p; cbn. exact J. }
    split; [destruct p; exact PRIV'|]. split; [destruct p; exact BUF'|]. split; [destruct p; exact PFX|].
    split; [destruct p; exact IFS'|]. destruct p; exact WF.
  Qed.
  End Sz2.
  Lemma PCAPR_errbuf : ltac:(let t := eval cbv delta [PCAPR_errbuf__stmt] in PCAPR_errbuf__stmt in exact t).
  Proof using AD AH ALN BU LO P1 R1 R2 SPW. all: natfold_lits. intros Rx sx CLx Px p PB FBx mx mx' Q cs e. ltac2:(SecDiet.SzSec.closeP 'PCAPR_errbuf__body "vvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition np_final (m5 : mem) (ps : PState H hptr) (PB' : list (cblock (hptr:=hptr))) (p' : pcap hptr hptr) (hcs' : list cell) (dw : cell) : Prop :=
    GIo K R ps (CLc ++ PB') FB m5 /\ PCAPR (hptr:=hptr) P p' PB' FB m5
    /\ agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5
    /\ rw_cells usegs m5 HA hcs' /\ cells_size hcs' = 24%nat /\ rw_cells usegs m5 DA [dw] /\ csize dw = 8%nat /\ ps_outfile ps = o.

  (* [comment removed for export] *)
  Definition np_fail_tail__stmt : Prop := forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x0 x1 x2 x3 x4 x5 x6 x7 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (PB' : list (cblock (hptr:=hptr))) (p' : pcap hptr hptr) (h : pkthdr) (hcs' : list cell) (dw : cell) (fj : list byte),
      stk usegs m5 lo (bv_unsigned sp + -4208) ->
      rw_cells usegs m5 (bv_unsigned sp + -4208) [CB 4136 fj; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> mem_inv usegs m5 ->
      np_final m5 ps PB' p' hcs' dw ->
      implM usegs (mret ((-1)%Z, h, p')) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -4208)) gp tp t0' t1' t2' x0 x1 a0' a1' a2' a3' a4' a5' a6' a7'
                 x2 x3 x4 x5 x6 x7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x15ce8) fc None m5 (seg_rom usegs)).
  Section Sz3.
  Variables ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x0 x1 x2 x3 x4 x5 x6 x7 t3' t4' t5' t6' m5 ps PB' p' h hcs' dw fj : ltac2:(SecDiet.SzSec.tyM 'np_fail_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma np_fail_tail__body : ltac2:(SecDiet.SzSec.bodyP 'np_fail_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using BU. all: natfold_lits. pin_using (fun (BU : unit) => tt).
 intros ST5 FR5 MI5 (G5 & PC5 & AG5 & HH & Hh & HD & Hd & OF).
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    apply (implM_ret usegs). hide HH. hide HD.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl usegs m5) as WM.
    step. eapply np_epilogue; [exact ST5 | exact FR5 | exact MI5 |].
    intros t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' ST6. unhide HH. unhide HD.
    subst POSTQ. unfold next_packet_post. all: natfold_lits. exists (Z_to_bv 64 (-1)), m5, PB', dw.
    split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
    split; [exact OF|]. split; [exact MI5|]. split; [exact ST6|]. split; [exact AG5|]. split; [exact G5|].
    split; [intros _; exact PC5|]. split; [intros _; apply PCAPR_closable_of; exact PC5|].
    split; [reflexivity|]. split; [lia|]. split; [intros X; lia|]. split; [intros _; exists hcs'; split; [exact Hh| exact HH]|].
    split; [exact HD| exact Hd].
  Qed.
  End Sz3.
  Lemma np_fail_tail : ltac:(let t := eval cbv delta [np_fail_tail__stmt] in np_fail_tail__stmt in exact t).
  Proof using BU. all: natfold_lits. intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x0 x1 x2 x3 x4 x5 x6 x7 t3' t4' t5' t6' m5 ps PB' p' h hcs' dw fj. ltac2:(SecDiet.SzSec.closeP 'np_fail_tail__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition np_ok_tail__stmt : Prop := forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x0 x1 x2 x3 x4 x5 x6 x7 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (PB' : list (cblock (hptr:=hptr))) (p' : pcap hptr hptr) (h : pkthdr) (dw : cell) (fj : list byte),
      stk usegs m5 lo (bv_unsigned sp + -4208) ->
      rw_cells usegs m5 (bv_unsigned sp + -4208) [CB 4136 fj; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> mem_inv usegs m5 ->
      np_final m5 ps PB' p' (hdr_cells h) dw -> (0 <= h_caplen h < 2^32)%Z -> (0 <= h_len h < 2^32)%Z ->
      implM usegs (mret (1%Z, h, p')) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -4208)) gp tp t0' t1' t2' x0 x1 a0' a1' a2' a3' a4' a5' a6' a7'
                 x2 x3 x4 x5 x6 x7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x15dbc) fc None m5 (seg_rom usegs)).
  Section Sz4.
  Variables ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x0 x1 x2 x3 x4 x5 x6 x7 t3' t4' t5' t6' m5 ps PB' p' h dw fj : ltac2:(SecDiet.SzSec.tyM 'np_ok_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma np_ok_tail__body : ltac2:(SecDiet.SzSec.bodyP 'np_ok_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using BU. all: natfold_lits. pin_using (fun (BU : unit) => tt).
 intros ST5 FR5 MI5 (G5 & PC5 & AG5 & HH & Hh & HD & Hd & OF) HC HL.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    apply (implM_ret usegs). hide HH. hide HD.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl usegs m5) as WM.
    do 2 step. eapply np_epilogue; [exact ST5 | exact FR5 | exact MI5 |].
    intros t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' ST6. unhide HH. unhide HD.
    subst POSTQ. unfold next_packet_post. all: natfold_lits. exists (Z_to_bv 64 1), m5, PB', dw.
    split; [unfold hpost_regs; repeat (lazymatch goal with |- ex _ => eexists end); reflexivity|].
    split; [exact OF|]. split; [exact MI5|]. split; [exact ST6|]. split; [exact AG5|]. split; [exact G5|].
    split; [intros _; exact PC5|]. split; [intros _; apply PCAPR_closable_of; exact PC5|].
    split; [reflexivity|]. split; [lia|]. split; [intros _; split; [exact HH| split; [exact HC| exact HL]]|]. split; [intros X; exfalso; lia|].
    split; [exact HD| exact Hd].
  Qed.
  End Sz4.
  Lemma np_ok_tail : ltac:(let t := eval cbv delta [np_ok_tail__stmt] in np_ok_tail__stmt in exact t).
  Proof using BU. all: natfold_lits. intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x0 x1 x2 x3 x4 x5 x6 x7 t3' t4' t5' t6' m5 ps PB' p' h dw fj. ltac2:(SecDiet.SzSec.closeP 'np_ok_tail__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Lemma np_CLc_facts : forall ps PB' m5 a, GIo K R ps (CLc ++ PB') FB m5 -> in_block CLc a -> (0 < a < CEILZ)%Z /\ ~ in_block PB' a.
  Proof using Type. all: natfold_lits. pin_using tt. intros. eapply GIo_CLc_facts; eassumption. Qed.

  (* [comment removed for export] *)
  Definition np_snp__stmt : Prop := forall (t0' t1' t2' a3' a4' a5' a6' a7' x0 x1 x2 x3 x4 x5 x6 x7 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (PB' : list (cblock (hptr:=hptr))) (p' : pcap hptr hptr) (h : pkthdr) (hcs' : list cell) (dw : cell) (fj : list byte)
           (FMTA : Z) (fs : string) (args : list farg),
      stk usegs m5 lo (bv_unsigned sp + -4208) ->
      rw_cells usegs m5 (bv_unsigned sp + -4208) [CB 4136 fj; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> mem_inv usegs m5 ->
      np_final m5 ps PB' p' hcs' dw ->
      fmt_at m5 FMTA fs -> fmt_ok fs args = true -> (length args <= 2)%nat -> Forall2 (farg_word R (CLc ++ PB') (bv_unsigned sp + -4208) (P + 216) 256 m5) args (firstn (length args) [a3'; a4']) ->
      (length (Fmt.snprintf 256 fs args) <= 255)%nat -> items_okb (fmt fs) = true -> Forall arg_ok args ->
      implM usegs (mret ((-1)%Z, h, set_errbuf (Fmt.snprintf 256 fs args) p')) ps POSTQ
        (MS (mkR (Z_to_bv 64 0x15ce8) (Z_to_bv 64 (bv_unsigned sp + -4208)) gp tp t0' t1' t2' x0 x1 (Z_to_bv 64 (P + 216)) (Z_to_bv 64 256) (Z_to_bv 64 FMTA) a3' a4' a5' a6' a7'
                 x2 x3 x4 x5 x6 x7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 SNPRINTF_ENTRY) fc None m5 (seg_rom usegs)).
  Section Sz6.
  Variables t0' t1' t2' a3' a4' a5' a6' a7' x0 x1 x2 x3 x4 x5 x6 x7 t3' t4' t5' t6' m5 ps PB' p' h hcs' dw fj FMTA fs args : ltac2:(SecDiet.SzSec.tyM 'np_snp__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @t0').
  Lemma np_snp__body : ltac2:(SecDiet.SzSec.bodyP 'np_snp__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AD AH ALN BU HFL LO P1 P4 P5 R1 R2 SFL SNPRINTF SPM SPW TP. all: natfold_lits. pin_using (fun (AD AH ALN BU HFL LO P1 P4 P5 R1 R2 SFL SNPRINTF SPM SPW TP : unit) => tt).
 intros ST5 FR5 MI5 (G5 & PC5 & AG5 & HH & Hh & HD & Hd & OF5) FMT5 FOK LA FW LEN IOK AOK.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof PC5 as (Afx & _ & (Bx & Ix & jx & padx & bsx & EPB & CELLS & _ & _ & _ & _ & WF)).
    pose proof (psize_pos p') as PS.
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G5 ltac:(rewrite EPB; left; reflexivity)) as (K1 & K2 & K3 & K4 & K5 & K6).
    apply pcap_cells_split4 in CELLS as (_ & CE & _ & _); [|reflexivity].
    apply (rw_cells_split_CB usegs m5 _ [] 304 _ [] [256; 48]%nat) in CE; [|reflexivity]. cbn [mk_CB_cells app] in CE.
    destruct (rw_cells_cut _ _ _ 1 CE) as [CE1 _]. clear CE. (cbn [firstn skipn] in CE1; sl_lit_sizes_in CE1; cbn [firstn skipn cells_size csize Nat.add] in CE1).
    assert (HinP : forall a, (P + 216 <= a < P + 216 + 256)%Z -> in_block (CLc ++ PB') a).
    { intros a Ha. apply in_block_app. right. rewrite EPB. unfold pcap_blocks, in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    apply (implM_ret usegs). name_sp sp (-4208)%Z.
    eapply evt_cut.
    { eapply (SNPRINTF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R ps (CLc ++ PB') FB lo (P + 216)%Z 256%Z FMTA fs args (firstn 256 (pj_g jx)));
        [| reflexivity | reflexivity | reflexivity | lia | exact FMT5 | exact FOK | exact (Nat.le_le_succ_r _ _ LA) | rewrite Hsp; replace (firstn (length args) [a3'; a4'; a5']) with (firstn (length args) [a3'; a4']) by (clear -LA; destruct args as [|? [|? [|? ?]]]; cbn in LA |- *; fastfirst (first [ noevar_assumption |reflexivity | lia])); exact FW | exact CE1 | left; exact HinP].
      split; [exact G5|]. split; [rewrite Hsp; exact ST5|]. split; [unfold rc_lo; lia|]. split; [unfold STDIO_STACK; rewrite Hsp; lia|].
      split; [rewrite Hsp; lia|]. split; [exact MI5|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
    cbv beta. intros ms' PO. destruct PO as (av & m6 & junk6 & E & MU6 & WM6 & MI6 & ST6 & -> & HEB6).
    unfold hpost_regs in E. all: natfold_lits. destruct_exs E. subst ms'. rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 89320)) with (Z_to_bv 64 89320) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    unfold STDIO_STACK in MU6.
    assert (AGS : agrees_on (fun a => outside [(bv_unsigned sp + -4208 - 65536, bv_unsigned sp + -4208); (P + 216, P + 216 + 256)]%Z a) m5 m6)
      by (eapply agrees_on_of_munch; [exact MU6 | exact WM6 | intros a _ Ho; exact Ho]).
    apply (agrees_rw_cells _ _ _ _ _ AGS) in FR5; [| intros a Ha; (cl_lit_hyps; sl_lit_sizes; cbn [outside cells_size csize Nat.add] in *); unfold rc_lo in LO; (keep_hyps CEILV H hptr K sp R CLc FB lo P HA DA m5 ps PB' hcs' dw fs args a LO BU P4 G5 Ha; lia)].
    apply (agrees_rw_cells _ _ _ _ _ AGS) in HH; [| intros a Ha; rewrite Hh in Ha; cbn [outside]; unfold rc_lo in LO; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGS) in HD; [| intros a Ha; cbn [cells_size] in Ha; rewrite Hd in Ha; cbn [outside]; unfold rc_lo in LO; lia].
    assert (G6 : GIo K R ps (CLc ++ PB') FB m6).
    { eapply (GIo_pcap_frame K HFL SFL); [exact G5 | exact MU6 | exact WM6 |].
      apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia|]. apply Forall_cons; [| apply Forall_nil].
      right. rewrite EPB. unfold iv_in_block, pcap_blocks. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    assert (PC6 : PCAPR (hptr:=hptr) P (set_errbuf (Fmt.snprintf 256 fs args) p') PB' FB m6).
    { eapply (PCAPR_errbuf _ _ _ _ _ _ _ _ _ _ _ _ G5 PC5 AGS); [| exact HEB6 | (sl_lit_sizes; cbn [cells_size csize Nat.add]); lia].
      intros a Ha Hn. cbn [outside]. pose proof (in_PB_below K _ _ _ _ _ _ _ G5 Ha). unfold rc_lo in LO. lia. }
    assert (AG6 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m6).
    { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [exact AGS|]. intros a [[Ha|Ha] _]; cbn [outside]; [unfold rc_lo in LO; lia|].
      destruct (np_CLc_facts _ _ _ _ G5 Ha) as [Hc Hnb]. split; [unfold rc_lo in LO; lia|]. split; [| exact Logic.I].
      intros Hin. apply Hnb. rewrite EPB. unfold pcap_blocks, in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    eapply np_fail_tail; [exact ST6 | exact FR5 | exact MI6 |].
    split; [exact G6|]. split; [exact PC6|]. split; [exact AG6|]. split; [exact HH|]. split; [exact Hh|]. split; [exact HD|]. split; [exact Hd| exact OF5].
  Qed.
  End Sz6.
  Lemma np_snp : ltac:(let t := eval cbv delta [np_snp__stmt] in np_snp__stmt in exact t).
  Proof using AD AH ALN BU HFL LO P1 P4 P5 R1 R2 SFL SNPRINTF SPM SPW TP. all: natfold_lits. intros t0' t1' t2' a3' a4' a5' a6' a7' x0 x1 x2 x3 x4 x5 x6 x7 t3' t4' t5' t6' m5 ps PB' p' h hcs' dw fj FMTA fs args. ltac2:(SecDiet.SzSec.closeP 'np_snp__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition np_fmt__stmt : Prop := forall (ra' t0' t1' t2' a1' a4' a5' a6' a7' x0 x1 x2 x3 x4 x5 x6 x7 t3' t4' t5' t6' : word) (m5 : mem) (ps : PState H hptr)
           (PB' : list (cblock (hptr:=hptr))) (p' : pcap hptr hptr) (h : pkthdr) (hcs' : list cell) (dw : cell) (fj : list byte) (e : Z),
      stk usegs m5 lo (bv_unsigned sp + -4208) ->
      rw_cells usegs m5 (bv_unsigned sp + -4208) [CB 4136 fj; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> mem_inv usegs m5 ->
      np_final m5 ps PB' p' hcs' dw -> (-2^31 <= e < 2^31)%Z -> fmt_at m5 0x108d6 "error reading dump file"%string ->
      implM usegs (mret ((-1)%Z, h, set_errbuf (fmt_errmsg "error reading dump file"%string [] e) p')) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -4208)) gp tp t0' t1' t2' x0 x1 (Z_to_bv 64 (P + 216)) a1' (Z_to_bv 64 (s32 e)) (Z_to_bv 64 0x108d6) a4' a5' a6' a7'
                 x2 x3 x4 x5 x6 x7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x15b28) fc None m5 (seg_rom usegs)).
  Section Sz7.
  Variables ra' t0' t1' t2' a1' a4' a5' a6' a7' x0 x1 x2 x3 x4 x5 x6 x7 t3' t4' t5' t6' m5 ps PB' p' h hcs' dw fj e : ltac2:(SecDiet.SzSec.tyM 'np_fmt__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma np_fmt__body : ltac2:(SecDiet.SzSec.bodyP 'np_fmt__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AD AH ALN BU FMT LO P1 P2 P4 R1 R2 SPM SPW TP. all: natfold_lits. pin_using (fun (AD AH ALN BU FMT LO P1 P2 P4 R1 R2 SPM SPW TP : unit) => tt).
 intros ST5 FR5 MI5 (G5 & PC5 & AG5 & HH & Hh & HD & Hd & OF5) HE MSG.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof PC5 as (Afx & _ & (Bx & Ix & jx & padx & bsx & EPB & CELLS & _ & _ & _ & _ & WF)).
    pose proof (psize_pos p') as PS.
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G5 ltac:(rewrite EPB; left; reflexivity)) as (K1 & K2 & K3 & K4 & K5 & K6).
    apply pcap_cells_split4 in CELLS as (_ & CE & _ & _); [|reflexivity].
    apply (rw_cells_split_CB usegs m5 _ [] 304 _ [] [256; 48]%nat) in CE; [|reflexivity]. cbn [mk_CB_cells app] in CE.
    destruct (rw_cells_cut _ _ _ 1 CE) as [CE1 _]. clear CE. (cbn [firstn skipn] in CE1; sl_lit_sizes_in CE1; cbn [firstn skipn cells_size csize Nat.add] in CE1).
    assert (HinP : forall a, (P + 216 <= a < P + 216 + 256)%Z -> in_block (CLc ++ PB') a).
    { intros a Ha. apply in_block_app. right. rewrite EPB. unfold pcap_blocks, in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    apply (implM_ret usegs).
    hide CE1. hide HH. hide HD. hide FR5.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl usegs m5) as WM.
    do 2 step.
    unhide CE1. unhide HH. unhide HD. unhide FR5. clear MU WM.
    name_sp sp (-4208)%Z.
    eapply evt_cut.
    { eapply (FMT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R ps (CLc ++ PB') FB lo (P + 216)%Z 0x108d6%Z e "error reading dump file"%string [] (firstn 256 (pj_g jx)));
        [| reflexivity | reflexivity | reflexivity | exact HE | reflexivity | exact MSG | reflexivity | cbn; lia | constructor | exact CE1 | left; exact HinP | apply aligned16_8; [exact P2| reflexivity]].
      split; [exact G5|]. split; [rewrite Hsp; exact ST5|]. split; [unfold rc_lo; lia|]. split; [unfold PCAP_L1_STACK; rewrite Hsp; lia|].
      split; [rewrite Hsp; lia|]. split; [exact MI5|]. split; [exact TP| rewrite Hsp; apply aln16_add; [exact ALN| reflexivity]]. }
    cbv beta. intros ms' PO. destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m6 & junk6 & -> & MI6 & ST6 & AG6 & G6 & HEB6).
    rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 88880)) with (Z_to_bv 64 88880) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    apply (agrees_rw_cells _ _ _ _ _ AG6) in FR5; [| intros a Ha; (sl_lit_sizes_in Ha; cbn [cells_size csize Nat.add] in Ha); split; [left; (keep_hyps CEILV sp R P HA DA hcs' dw a Ha; lia)| unfold rc_lo in LO; (keep_hyps CEILV H hptr K sp R CLc FB lo P HA DA ps PB' hcs' dw m6 a LO BU P4 G6 Ha; lia)]].
    apply (agrees_rw_cells _ _ _ _ _ AG6) in HH; [| intros a Ha; rewrite Hh in Ha; split; [left; lia| unfold rc_lo in LO; lia]].
    apply (agrees_rw_cells _ _ _ _ _ AG6) in HD; [| intros a Ha; cbn [cells_size] in Ha; rewrite Hd in Ha; split; [left; lia| unfold rc_lo in LO; lia]].
    assert (PC6 : PCAPR (hptr:=hptr) P (set_errbuf (fmt_errmsg "error reading dump file" [] e) p') PB' FB m6).
    { pose proof (fmt_errmsg_length "error reading dump file"%string [] e) as LENE.
      eapply (PCAPR_errbuf _ _ _ _ _ _ _ _ _ _ _ _ G5 PC5 AG6); [| exact HEB6 | (sl_lit_sizes; cbn [cells_size csize Nat.add]); lia].
      intros a Ha Hn. split; [right; apply in_block_app; right; exact Ha| lia]. }
    assert (AG06 : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m6).
    { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [exact AG6|]. intros a [[Ha|Ha] _]; [split; [left; lia| unfold rc_lo in LO; lia]|].
      destruct (np_CLc_facts _ _ _ _ G5 Ha) as [Hc Hnb]. split; [right; apply in_block_app; left; exact Ha|].
      intros Hin. apply Hnb. rewrite EPB. unfold pcap_blocks, in_block. apply Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    hide HEB6. hide HH. hide HD.
    pose proof (munch_refl ([] : list (Z * Z)) m6) as MU. pose proof (wmono_refl usegs m6) as WM.
    step.
    unhide HEB6. unhide HH. unhide HD.
    eapply np_fail_tail; [exact ST6 | exact FR5 | exact MI6 |].
    split; [exact G6|]. split; [exact PC6|]. split; [exact AG06|]. split; [exact HH|]. split; [exact Hh|]. split; [exact HD|]. split; [exact Hd| exact OF5].
  Qed.
  End Sz7.
  Lemma np_fmt : ltac:(let t := eval cbv delta [np_fmt__stmt] in np_fmt__stmt in exact t).
  Proof using AD AH ALN BU FMT LO P1 P2 P4 R1 R2 SPM SPW TP. all: natfold_lits. intros ra' t0' t1' t2' a1' a4' a5' a6' a7' x0 x1 x2 x3 x4 x5 x6 x7 t3' t4' t5' t6' m5 ps PB' p' h hcs' dw fj e. ltac2:(SecDiet.SzSec.closeP 'np_fmt__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
  (* [comment removed for export] *)
  Hypothesis PPLEN : forall lt sw hdr d, length (snd (pcapint_post_process lt sw hdr d)) = length d.
  Hypothesis PPSEC : forall lt sw hdr d, h_sec (fst (pcapint_post_process lt sw hdr d)) = h_sec hdr /\ h_usec (fst (pcapint_post_process lt sw hdr d)) = h_usec hdr.
  Hypothesis PPRNG : forall lt sw hdr d, (0 <= h_caplen hdr <= Z.of_nat (length d))%Z -> (0 <= h_len hdr < 2^32)%Z -> (Z.of_nat (length d) < 2^31)%Z ->
     (0 <= h_caplen (fst (pcapint_post_process lt sw hdr d)) < 2^32)%Z /\ (0 <= h_len (fst (pcapint_post_process lt sw hdr d)) < 2^32)%Z.

  (* [comment removed for export] *)
  Definition pv (bq : hptr) (bsz alloc : Z) (data eb : list Z) : pcap hptr hptr :=
    mkPcap self f bsz alloc bq data swapped vmaj vmin snapshot linktype ltext prec brk eb header (PrivPcap (mkSf hdrsize lsw scl)).

  Ltac norm_p :=
    unfold pv in *; unfold pcap_blocks in *; unfold psize in *; unfold is_ng in *;
    cbn [pc_self pc_rfile pc_bufsize pc_bufalloc pc_buffer pc_bufdata pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype
         pc_linktype_ext pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_priv priv_cells
         sf_hdrsize sf_lengths_swapped sf_scale_type ifaces_ok set_bufdata set_errbuf set_buffer] in *;
    unfold PCAP_SF_TOTAL, PCAP_PRIV_OFF in *.

  (* [comment removed for export] *)
  Lemma bytes_wr_rw_cells : forall mx A l, bytes_at usegs mx A l -> wr_at usegs mx A (Z.of_nat (length l)) -> rw_cells usegs mx A [CB (length l) l].
  Proof using Type. all: natfold_lits. pin_using tt. intros mx A l HB HW. split; [split; [cbn; split; [reflexivity| exact Logic.I] | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact HB] | (sl_lit_sizes; cbn [cells_size csize Nat.add]); rewrite Nat.add_0_r; exact HW]. Qed.

  Definition np_finish__stmt : Prop := forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x3 x4 x5 x6 x7 t3' t4' t5' t6' ws wu : word) (m5 : mem) (ps : PState H hptr)
           (bq : hptr) (Bx bsz alloc : Z) (data eb : list Z) (sec usec cap len : Z) (dw : cell) (fj : list byte),
      stk usegs m5 lo (bv_unsigned sp + -4208) ->
      rw_cells usegs m5 (bv_unsigned sp + -4208) [CB 4136 fj; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> mem_inv usegs m5 ->
      GIo K R ps (CLc ++ pcap_blocks (pv bq bsz alloc data eb) P Bx 0) FB m5 ->
      PCAPR (hptr:=hptr) P (pv bq bsz alloc data eb) (pcap_blocks (pv bq bsz alloc data eb) P Bx 0) FB m5 ->
      agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells usegs m5 HA [C8 ws; C8 wu; C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)] -> rw_cells usegs m5 DA [dw] -> csize dw = 8%nat ->
      ws = Z_to_bv 64 sec -> wu = Z_to_bv 64 usec -> Forall (fun x => 0 <= x < 256)%Z data ->
      (0 <= cap <= Z.of_nat (length data))%Z -> (Z.of_nat (length data) < 2^31)%Z -> (0 <= len < 2^32)%Z -> ps_outfile ps = o ->
      implM usegs (let '(hdr, d) := pcapint_post_process linktype swapped (mkHdr sec usec cap len) data in
                   mret (1%Z, hdr, set_bufdata d (pv bq bsz alloc data eb))) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -4208)) gp tp t0' t1' t2' (Z_to_bv 64 P) (Z_to_bv 64 HA) a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 DA) x3 x4 x5 x6 x7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x15d98) fc None m5 (seg_rom usegs)).
  Section Sz9.
  Variables ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x3 x4 x5 x6 x7 t3' t4' t5' t6' ws wu m5 ps bq Bx bsz alloc data eb sec usec cap len dw fj : ltac2:(SecDiet.SzSec.tyM 'np_finish__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma np_finish__body : ltac2:(SecDiet.SzSec.bodyP 'np_finish__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using AD AH BU HFL LO P1 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 SFL SP47 SPM SPW W9. all: natfold_lits. pin_using (fun (AD AH BU HFL LO P1 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 SFL SP47 SPM SPW W9 : unit) => tt).
 intros ST5 FR5 MI5 G5 PC5 AG5 HH HD Hd -> -> DRNG Hcap Hlen Hl32 OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof PC5 as PC5'.
    destruct PC5 as (Afx & Hin & (Bx' & Ix & jx' & padx & bsx' & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    norm_p. unfold sf_cells in PRIV. cbn [sf_hdrsize sf_lengths_swapped sf_scale_type] in PRIV.
    subst Ix. assert (EBX : Bx' = Bx) by congruence. subst Bx'. clear EPB.
    pose proof WF as (W1' & W2' & W3 & W4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & WBB). cbn [pc_bufsize pc_bufalloc pc_bufdata length] in W3, W4, WBB.
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G5 ltac:(right; left; reflexivity)) as (K1 & K2 & K3 & K4 & K5 & K6).
    pose proof (GIo_PB_block K _ _ _ _ _ _ _ _ _ G5 ltac:(left; reflexivity)) as (L1 & L2 & L3 & L4 & L5 & L6).
    assert (BP' : (Bx + alloc <= P \/ P + 664 <= Bx)%Z).
    { pose proof (PB_apart K _ _ _ _ _ _ (pv bq bsz alloc data eb) P Bx 0 G5 eq_refl) as [APB _]. unfold pv, psize, is_ng in APB. cbn [pc_bufalloc pc_priv] in APB. unfold PCAP_SF_TOTAL in APB. match type of APB with ?t => idtac t end. lia. }
    unfold pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF in CELLS.
    cbn [app pc_bufsize pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_header pc_priv pk_next_pcap pk_cleanup_sf PK] in CELLS.
    destruct (rw_cells_forget _ _ _ _ HD) as [dwj HD']. clear HD. cbn [cells_size] in HD'. rewrite Hd in HD'. change (8 + 0)%nat with 8%nat in HD'.
    (* [comment removed for export] *)
    apply (rw_cells_split_CB usegs m5 _ [] (Z.to_nat alloc) _ [] [length data; Z.to_nat alloc - length data]%nat) in BUF; [| cbn; lia].
    cbn [mk_CB_cells app] in BUF. rewrite PFX in BUF.
    destruct (rw_cells_cut _ _ _ 1 BUF) as [BD BT]. clear BUF. (cbn [firstn skipn] in BD, BT; sl_lit_sizes_in BD; sl_lit_sizes_in BT; cbn [firstn skipn cells_size csize Nat.add] in BD, BT).
    hide BD. hide BT. hide PRIV.
    pose proof (munch_refl [(DA, DA + 8)]%Z m5) as MU. pose proof (wmono_refl usegs m5) as WM.
    unfold implM. iprefix.
    step. if_false_by (eqz_false DA ltac:(unfold rc_lo, rc_spmain in *; lia)). step. rewrite (and7_aligned DA) by (unfold rc_lo, rc_spmain in *; lia). step. if_false.
    step. step. rewrite (sx32_small (Z.b2z swapped)) by (destruct swapped; cbn; lia).
    step. rewrite (sx32_small linktype) by lia.
    step. step. step.
    unhide BD. unhide BT. unhide PRIV.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (AGD : agrees_on (fun a => outside [(DA, DA + 8)]%Z a) m5 mm) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]);
      rename mm into m5' end.
    apply (agrees_rw_cells _ _ _ _ _ AGD) in BD; [| intros a Ha; (cl_lit_hyps; sl_lit_sizes; cbn [outside cells_size csize Nat.add] in *); unfold rc_lo in LO; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGD) in BT; [| intros a Ha; (cl_lit_hyps; sl_lit_sizes; cbn [outside cells_size csize Nat.add] in *); unfold rc_lo in LO; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGD) in PRIV; [| intros a Ha; (cl_lit_hyps; sl_lit_sizes; cbn [outside cells_size csize Nat.add] in *); unfold rc_lo in LO; lia].
    assert (G5' : GIo K R ps (CLc ++ [(self, P, 664%Z); (bq, Bx, alloc)]) FB m5').
    { eapply (GIo_pcap_frame K HFL SFL); [exact G5 | exact MU | exact WM |]. apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia| apply Forall_nil]. }
    assert (AG5' : agrees_on (fun a => client_keeps CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5').
    { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [exact AGD|]. intros a [_ [_ Hn]]; cbn [outside]; lia. }
    clear MU WM AGD G5 AG5.
    assert (ZA : zarr m5' Bx data).
    { split; [| split; [| exact DRNG]].
      - pose proof (rw_cells_bytes_at _ _ _ _ BD) as X. cbn [cells_bytes cbytes] in X. rewrite app_nil_r in X. exact X.
      - eapply rw_cells_wr_at; [exact BD|]. (sl_lit_sizes; cbn [cells_size csize Nat.add]). lia. }
    change (rw_cells usegs m5' HA (pkthdr_cells (Z_to_bv 64 sec) (Z_to_bv 64 usec) (mkHdr sec usec cap len))) in HH.
    name_sp sp (-4208)%Z.
    eapply evt_cut.
    { eapply PP; [rewrite Hsp; exact ST5 | unfold PP_FRAME; rewrite Hsp; (keep_hyps CEILV sp R lo P HA DA Bx data dw BU; lia) | exact HH | exact ZA | assumption | reflexivity | reflexivity | reflexivity | reflexivity
                 | (keep_hyps CEILV R P HA DA linktype Bx data dw W9; lia) | cbn [h_caplen]; (keep_hyps CEILV R P HA DA Bx data cap dw Hcap; lia) | (keep_hyps CEILV R P HA DA Bx data dw Hlen; lia) | cbn [h_len]; (keep_hyps CEILV R P HA DA Bx data len dw Hl32; lia) | left; rewrite Hsp; (keep_hyps CEILV sp R P HA DA Bx data dw R1; lia) | right; unfold rc_lo in LO; (keep_hyps CEILV H hptr K sp R CLc FB lo P HA DA self ps bq Bx alloc data dw m5' LO BU R1 W4 K4 G5'; lia) | unfold PP_FRAME; rewrite Hsp; unfold rc_lo in LO; (keep_hyps CEILV H hptr K sp R CLc FB lo P HA DA self ps bq Bx alloc data dw m5' LO BU W4 K4 G5'; lia)
                 | exact AH | clear -K2; Z.div_mod_to_equations; (keep_hyps Bx r0 q r q0 K2 H H0 H4; lia) | unfold rc_spmain in R3; (keep_hyps CEILV R P HA DA Bx data dw R2 R3 SP47; lia) | (keep_hyps CEILV H hptr K sp R CLc FB lo P HA DA self ps bq Bx alloc data dw m5' W4 K4; lia) | unfold rc_lo in LO; (keep_hyps CEILV sp R lo P HA DA Bx data dw LO BU R1 SPW; lia) | (keep_hyps CEILV R P HA DA Bx data dw K1; lia) ]. }
    cbv beta. intros ms' PO. destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m6 & -> & MU6 & WM6 & MI6 & ST6 & HH6 & ZA6).
    rewrite Hsp in *. unname_sp.
    replace (ret_pc (Z_to_bv 64 89532)) with (Z_to_bv 64 89532) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    cbn [h_caplen] in MU6. unfold PP_FRAME in MU6.
    set (hdr' := fst (pcapint_post_process linktype swapped (mkHdr sec usec cap len) data)) in *.
    set (d' := snd (pcapint_post_process linktype swapped (mkHdr sec usec cap len) data)) in *.
    pose proof (PPLEN linktype swapped (mkHdr sec usec cap len) data) as LEN'. fold d' in LEN'.
    pose proof (PPSEC linktype swapped (mkHdr sec usec cap len) data) as [SEC' USEC']. fold hdr' in SEC', USEC'. cbn [h_sec h_usec] in SEC', USEC'.
    pose proof (PPRNG linktype swapped (mkHdr sec usec cap len) data ltac:(cbn [h_caplen]; lia) ltac:(cbn [h_len]; lia) Hlen) as [RC' RL']. fold hdr' in RC', RL'.
    assert (AGS : agrees_on (fun a => outside [(bv_unsigned sp + -4208 - 32, bv_unsigned sp + -4208); (HA + 20, HA + 24); (Bx, Bx + cap)]%Z a) m5' m6)
      by (eapply agrees_on_of_munch; [exact MU6 | exact WM6 | intros a _ Ho; exact Ho]).
    apply (agrees_rw_cells _ _ _ _ _ AGS) in FR5; [| intros a Ha; (cl_lit_hyps; sl_lit_sizes; cbn [outside cells_size csize Nat.add] in *); unfold rc_lo in LO; (keep_hyps CEILV H hptr K sp R CLc FB lo P HA DA self ps bq Bx alloc data cap dw m5' a LO BU R1 Hcap W4 K4 G5' Ha; lia)].
    apply (agrees_rw_cells _ _ _ _ _ AGS) in HD'; [| intros a Ha; (cl_lit_hyps; sl_lit_sizes; cbn [outside cells_size csize Nat.add] in *); unfold rc_lo in LO; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGS) in CELLS; [| intros a Ha; (cl_lit_hyps; sl_lit_sizes; cbn [outside cells_size csize Nat.add] in *); unfold rc_lo in LO; (keep_hyps CEILV H hptr K sp R CLc FB lo P HA DA self ps bq Bx alloc data cap dw m5' a LO BU R1 Hcap W4 L4 BP' G5' Ha; lia)].
    apply (agrees_rw_cells _ _ _ _ _ AGS) in PRIV; [| intros a Ha; (cl_lit_hyps; sl_lit_sizes; cbn [outside cells_size csize Nat.add] in *); unfold rc_lo in LO; (keep_hyps CEILV H hptr K sp R CLc FB lo P HA DA self ps bq Bx alloc data cap dw m5' a LO BU R1 Hcap W4 L4 BP' G5' Ha; lia)].
    apply (agrees_rw_cells _ _ _ _ _ AGS) in BT; [| intros a Ha; (cl_lit_hyps; sl_lit_sizes; cbn [outside cells_size csize Nat.add] in *); unfold rc_lo in LO; lia].
    (* [comment removed for export] *)
    destruct ZA6 as (ZB & ZW & ZR).
    pose proof (bytes_wr_rw_cells _ _ _ ZB ltac:(rewrite zbytes_length; exact ZW)) as BD6. rewrite zbytes_length in BD6.
    pose proof (rw_cells_uncut _ _ _ _ _ BD6 BT ltac:((sl_lit_sizes; cbn [cells_size csize Nat.add]); rewrite LEN'; lia)) as BUF6.
    merge_all BUF6.
    replace (length d' + (Z.to_nat alloc - length data + 0))%nat with (Z.to_nat alloc) in BUF6 by lia. rewrite app_nil_r in BUF6.
    rewrite (surjective_pairing (pcapint_post_process linktype swapped _ data)). fold hdr' d'. cbn [set_bufdata pc_self pc_rfile pc_bufsize pc_bufalloc pc_buffer pc_swapped
      pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_break_loop pc_errbuf pc_header pc_priv].
    assert (G6 : GIo K R ps (CLc ++ [(self, P, 664%Z); (bq, Bx, alloc)]) FB m6).
    { eapply (GIo_pcap_frame K HFL SFL); [exact G5' | exact MU6 | exact WM6 |].
      apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo; lia|]. apply Forall_cons; [left; cbn [fst snd]; unfold rc_lo, rc_spmain in *; lia|].
      apply Forall_cons; [| apply Forall_nil]. right. unfold iv_in_block. apply Exists_cons_tl, Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    apply evt_done. eapply np_ok_tail; [exact ST6 | exact FR5 | exact MI6 | | exact RC' | exact RL'].
    split; [exact G6|]. split.
    { exists Afx. split; [exact Hin|]. exists Bx, 0%Z, jx', padx, (zbytes d' ++ firstn (Z.to_nat alloc - length data) (skipn (length data) bsx')).
      split; [reflexivity|]. split; [exact CELLS|]. split; [unfold PCAP_PRIV_OFF; exact PRIV|]. split; [cbn [pc_bufalloc]; exact BUF6|].
      split; [cbn [pc_bufdata set_bufdata]; replace (length d') with (length (zbytes d')) by (apply zbytes_length);
              rewrite firstn_app, firstn_all, Nat.sub_diag; cbn [firstn]; rewrite app_nil_r; reflexivity|].
      split; [reflexivity|].
      unfold pcap_wf in *. cbn [set_bufdata pc_snapshot pc_bufsize pc_bufalloc pc_bufdata pc_break_loop pc_tstamp_precision pc_version_major pc_version_minor
                                 pc_linktype pc_linktype_ext pc_header pc_priv sf_hdrsize] in *. rewrite LEN'. exact WF. }
    split. { eapply agrees_on_trans; [exact AG5'|]. eapply agrees_on_weaken; [exact AGS|]. intros a [[Ha|Ha] [Hn1 Hn2]]; cbn [outside]; [unfold rc_lo in LO; (keep_hyps CEILV H hptr K sp R CLc FB lo P HA DA self ps bq Bx alloc data cap dw m6 a LO BU Hcap W4 K4 G6 Ha Hn1; lia)|].
             destruct (np_CLc_facts _ _ _ _ G5' Ha) as [Hc Hnb]. unfold rc_lo in LO. split; [lia|]. split; [lia|]. split; [| exact Logic.I].
             intros Hin'. apply Hnb. unfold in_block. apply Exists_cons_tl, Exists_cons_hd. cbn [cb_addr cb_size fst snd]. lia. }
    split. { unfold hdr_cells. rewrite SEC', USEC'. exact HH6. }
    split; [reflexivity|]. split; [exact HD'|]. split; [reflexivity| exact OF5].
  Qed.
  End Sz9.
  Lemma np_finish : ltac:(let t := eval cbv delta [np_finish__stmt] in np_finish__stmt in exact t).
  Proof using AD AH BU HFL LO P1 P5 P6 PP PPLEN PPRNG PPSEC R1 R2 R3 SFL SP47 SPM SPW W9. all: natfold_lits. intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x3 x4 x5 x6 x7 t3' t4' t5' t6' ws wu m5 ps bq Bx bsz alloc data eb sec usec cap len dw fj. ltac2:(SecDiet.SzSec.closeP 'np_finish__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Lemma implM_pure_k : forall {St A} (c : @M St A) st Q ms r st1,
    c st = Ret (Ok (r, st1)) -> implM usegs (mret r) st1 Q ms -> implM usegs c st Q ms.
  Proof using Type. all: natfold_lits. pin_using tt. intros St A c st Q ms r st1 E Hk. unfold implM in *. rewrite E. exact Hk. Qed.

End NpCtx.

End WithCeil.
End TwB.
