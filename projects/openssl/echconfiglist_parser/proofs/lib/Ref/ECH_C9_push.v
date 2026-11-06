(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec Cells CellsX TacX Frame.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface F_memcpy ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Rep ECH_LibState
     ECH_C1_stmt ECH_C3_stmt ECH_C6_stmt ECH_C7_stmt ECH_C8_stmt ECH_C9_stmt ECH_C7_read ECH_C7_rd ECH_C9_ctrl.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition B64HDR0 : list byte := cells_bytes [C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 1); C4 (wz 1); C4 (wz 0)].
Lemma B64HDR0_len : length B64HDR0 = 32%nat.
Proof. vm_compute. reflexivity. Qed.
Lemma B64HDR0_cont : map bv_unsigned (firstn 4 (skipn 24 B64HDR0)) = map (fun z => z mod 256) [1; 1 / 256; 1 / 65536; 1 / 16777216].
Proof. vm_compute. reflexivity. Qed.

Section HCW.
  Context {HCEIL : HeapCeil}.
  Lemma b64ctx_fresh_used : forall m C enc junk,
    length junk = 2528%nat -> rw_cells rsegs m C (b64ctx_fresh_cells enc junk) -> rw_cells rsegs m C (b64ctx_used_cells enc B64HDR0 junk 0).
  Proof.
    intros m C enc junk LJ HB. unfold b64ctx_fresh_cells in HB. unfold b64ctx_used_cells.
    change ([C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 1); C4 (wz 1); C4 (wz 0); C8 (wz enc); CB 2528 junk; C8 (wz 0); C8 (wz 0)])
      with ([C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 1); C4 (wz 1); C4 (wz 0)] ++ [C8 (wz enc); CB 2528 junk; C8 (wz 0); C8 (wz 0)]) in HB.
    apply rw_cells_app in HB. destruct HB as [H1 H2].
    change ([CB 32 B64HDR0; C8 (wz enc); CB 2528 junk; C8 (wz 0); C8 (wz 0)]) with ([CB 32 B64HDR0] ++ [C8 (wz enc); CB 2528 junk; C8 (wz 0); C8 (wz 0)]).
    apply rw_cells_app. split; [| exact H2].
    destruct H1 as [[W B] R]. split; [split|]; [| exact B| exact R]. cbn. split; [exact B64HDR0_len| exact I].
  Qed.
  (* [comment removed for export] *)
  Lemma MEMBIO_sep_hdr : forall mb M fl nf nx pv, MEMBIO_sep mb (mb_with_hdr M fl nf nx pv) = MEMBIO_sep mb M.
  Proof. intros. reflexivity. Qed.
  Lemma MEMBIO_below_hdr : forall mb M fl nf nx pv lo, MEMBIO_below mb (mb_with_hdr M fl nf nx pv) lo = MEMBIO_below mb M lo.
  Proof. intros. reflexivity. Qed.
End HCW.

Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.

  (* [comment removed for export] *)
  Definition B64F_apart (a : Z) (R : b64frep) : Prop :=
       (a + BIO_SIZE <= bf_ctx R \/ bf_ctx R + B64CTX_SIZE <= a)
    /\ (a + BIO_SIZE <= bf_enc R \/ bf_enc R + ENCCTX_SIZE <= a)
    /\ (bf_ctx R + B64CTX_SIZE <= bf_enc R \/ bf_enc R + ENCCTX_SIZE <= bf_ctx R).
  Definition biopush_stmt' : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list block) (a mb lo : Z) (R : b64frep) (M : membio),
      a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 mb ->
      B64F_fresh LB m a R -> B64F_apart a R -> bf_next R = 0 -> B64F_below a R lo -> MEMBIO LB m mb M -> MEMBIO_below mb M lo -> MEMBIO_sep mb M ->
      Forall (fun b => Forall (fun b' => blk_addr b + blk_size b <= blk_addr b' \/ blk_addr b' + blk_size b' <= blk_addr b) (blocks_MEMBIO mb M)) (blocks_B64F a R) ->
      METH_b64 m -> METH_mem m ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - BIOPUSH_STACK -> mem_inv rsegs m -> bv_unsigned ra mod 2 = 0 ->
      evt rsegs (biopush_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB a R mb M lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_BIO_push) fc None m (seg_rom rsegs)).

  Definition BP_RA : Z := 0x100584.   (* [comment removed for export] *)
  Definition BC_RA : Z := 0xff988.    (* [comment removed for export] *)

  Lemma biopush_spec' : biopush_stmt'.
  Proof.
    unfold biopush_stmt'. intros until M. intros A0 A1 BF BAP NX0 BEL MB MBL MSEP APT METHB METHM ST CEIL LO MI RAE. subst a0 a1.
    pose proof BAP as (BA1 & BA2 & BA3). unfold ENCCTX_SIZE in BA1, BA2, BA3.
    unfold BIOPUSH_STACK, BIOCTRL_B64_STACK, B64CTRL_STACK, BIOCTRL_STACK, MEMCTRL_STACK, FR_BIO_push, FR_BIO_ctrl, FR_b64_ctrl, FR_mem_ctrl in LO.
    unfold P_BIO_push in *. hcb.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof BF as (BC & (junk & LJ & BX) & BLK & NONL & RT0 & NR0).
    pose proof BLK as (I1 & I2 & I3 & RB1 & RB2 & RB3 & FLR & RTR & NRR & NXR & PVR).
    pose proof RB1 as (AP & _ & _ & AH & AI). pose proof RB2 as (CP & _ & _ & CH & CI). pose proof RB3 as (EP & _ & _ & EH & EI).
    pose proof BEL as (BL1 & BL2 & BL3).
    pose proof MB as MB0.
    destruct MB0 as (MC & MBB & MBM & MRP & J1 & J2 & J3 & J4 & RM1 & RM2 & RM3 & RM4 & POSR & LENR & BUFP & BUFH & MFL & RDO & AEOF & NUMR & NRD & NRD2 & MNX & MPV).
    pose proof RM1 as (MP & _ & _ & MH & MI0). pose proof MBL as (ML1 & ML2 & ML3 & ML4).
    (* [comment removed for export] *)
    pose proof (Forall_inv APT) as APT1. pose proof (Forall_inv APT1) as DJ_a_mb. pose proof (Forall_inv (Forall_inv_tail APT1)) as DJ_a_bb.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail APT1))) as DJ_a_bm. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail APT1)))) as DJ_a_rp.
    cbn [blk_addr blk_size fst snd] in DJ_a_mb, DJ_a_bb, DJ_a_bm, DJ_a_rp. clear APT1.
    pose proof (Forall_inv (Forall_inv_tail APT)) as APT2. pose proof (Forall_inv APT2) as DJ_c_mb.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail APT2))) as DJ_c_bm. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail APT2)))) as DJ_c_rp.
    cbn [blk_addr blk_size fst snd] in DJ_c_mb, DJ_c_bm, DJ_c_rp. clear APT2.
    pose proof MSEP as ((SP1 & SP2 & SP3 & SP4 & SP5 & SP6) & _).
    unfold BIO_SIZE, B64CTX_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE, BIO_CTRL_PUSH in *.
    hide AI; hide CI; hide EI; hide MI0. hide BA1; hide BA2; hide BA3. hide DJ_a_mb; hide DJ_a_bb; hide DJ_a_bm; hide DJ_a_rp. hide DJ_c_mb; hide DJ_c_bm; hide DJ_c_rp.
    hide SP1; hide SP2; hide SP3; hide SP4; hide SP5; hide SP6.
    pose proof (munch_refl [(lo, bv_unsigned sp); (a, a + 128); (mb, mb + 128)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    unfold bio_cells, b64f_bio, wz in BC. cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite] in BC.
    unfold A_b64_method in BC. rewrite NX0, RT0, NR0 in BC.
    unfold bio_cells, membio_bio, wz in MC. cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite] in MC.
    unfold A_mem_buf_method in MC. rewrite NUMR in MC.
    pose proof METHB as METHB0. unfold METH_b64, O_METH_BREAD, A_b64_method, P_b64_ctrl, wz in METHB. norm_addr METHB.
    unfold b64ctx_fresh_cells, wz in BX. unfold buf_cells, wz in MBM, MRP. cbn [bm_len bm_data bm_max bm_flags] in MBM, MRP. unfold wz in MBB.
    (* [comment removed for export] *)
    carve_frame 32%nat ST. do 4 st1. step. step. if_cases K0; zify_cond K0; [kill K0|]. clear K0.
    step. step. st1. step. if_false.
    unhide AI; unhide BA1; unhide DJ_a_mb; unhide DJ_a_bb; unhide DJ_a_bm; unhide DJ_a_rp.
    st1.
    hide AI; hide BA1; hide DJ_a_bb; hide DJ_a_bm; hide DJ_a_rp.
    step. if_cases K1; zify_cond K1; [kill K1|]. clear K1.
    unhide MI0; unhide DJ_c_mb; unhide SP1; unhide SP2; unhide SP3.
    st1.
    hide MI0; hide DJ_c_mb; hide SP1; hide SP2; hide SP3; hide DJ_a_mb.
    step. step. step. step.
    (* [comment removed for export] *)
    carve_frame 48%nat ST. do 7 st1. step. step. if_cases K2; zify_cond K2; [kill K2|]. clear K2.
    step. st1. step. if_false. st1. step. if_false. step. step. step. st1. st1.
    step. if_true. step. if_true. step. step. step. step. step.
    (* [comment removed for export] *)
    eapply evt_cut.
    { eapply b64ctrl_spec with (lo := lo) (LB := LB) (a := a) (mb := mb) (cmd := 6) (parg := a)
        (R := bf_with_hdr R (bf_flags R) (bf_retry R) (bf_nread R) mb (bf_prev R)) (M := mb_with_hdr M (mb_flags M) (mb_numf M) (mb_next M) a)
        (hdr := B64HDR0) (junk := junk) (elen := 0) (cont := 1);
        cbn [bf_flags bf_retry bf_nread bf_next bf_prev bf_ctx bf_enc bf_id bf_cid bf_eid bf_with_hdr]; rewrite ?unsigned_lit by lia; try reflexivity.
      all: lazymatch goal with
           | |- rw_cells _ _ _ (bio_cells _) => unfold bio_cells, b64f_bio, wz; cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite
                                       bf_flags bf_retry bf_nread bf_next bf_prev bf_ctx bf_with_hdr]; unfold A_b64_method; rewrite RT0, NR0; exact BC
           | |- rw_cells _ _ _ (b64ctx_used_cells _ _ _ _) => apply b64ctx_fresh_used; [exact LJ| exact BX]
           | |- B64F_blocks _ _ _ => unfold B64F_blocks; cbn [bf_flags bf_retry bf_nread bf_next bf_prev bf_ctx bf_enc bf_id bf_cid bf_eid bf_with_hdr]; unfold BIO_SIZE, B64CTX_SIZE;
                                    repeat (split; [first [assumption| lia]|]); first [assumption| lia]
           | |- B64F_below _ _ _ => unfold B64F_below, BIO_SIZE, B64CTX_SIZE; cbn [bf_ctx bf_enc bf_with_hdr]; lia
           | |- length _ = _ => exact B64HDR0_len
           | |- map _ _ = _ => exact B64HDR0_cont
           | |- _ \/ _ => left; split; [reflexivity|]; split; [| split; [rewrite MEMBIO_below_hdr; exact MBL| split; [rewrite MEMBIO_sep_hdr; exact MSEP|]]]
           | |- stk _ _ _ _ => exact ST
           | |- hceil <= _ => exact CEIL
           | |- mem_inv _ _ => assumption
           | |- _ mod 2 = 0 => unfold BC_RA; rewrite unsigned_lit by lia; reflexivity
           | |- _ => try (unfold B64CTRL_STACK, BIOCTRL_STACK, MEMCTRL_STACK, FR_b64_ctrl, FR_BIO_ctrl, FR_mem_ctrl; lia); try lia
           end.
      - (* [comment removed for export] *)
        unhide SP1; unhide SP2; unhide SP3; unhide SP4; unhide SP5; unhide SP6. unhide MI0.
        membio_tac.
        all: try (unfold bio_cells, membio_bio, wz;
                  cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite
                       mb_buf mb_len mb_pos mb_flags mb_numf mb_nread mb_next mb_prev mb_bb mb_bm mb_rp mb_id mb_bbid mb_bmid mb_rpid];
                  unfold A_mem_buf_method; rewrite ?NUMR; assumption).
        all: match goal with |- ?G => idtac "MB-LEFT:" G end.
      - unfold METH_mem in *. eapply rw_cells_transport; [exact METHM| exact MU| exact WM| unhide AI; unhide MI0; unfold A_mem_buf_method, O_METH_BREAD; cbn; lia].
      all: match goal with |- ?G => idtac "CTRL-LEFT:" G end. }
    cbv beta. landx MU WM.
    (* [comment removed for export] *)
    st1. step. step. if_false. st1. step. if_true. step. do 6 st1. step. release_frame FR0 ST (bv_unsigned sp + -32). step.
    step. step. do 3 st1. step. release_frame FR ST (bv_unsigned sp). step.
    apply evt_done. unfold biopush_post.
    repeat (lazymatch goal with |- ex _ => eexists end). split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
    unhide SP1; unhide SP2; unhide SP3; unhide SP4; unhide SP5; unhide SP6. unhide MI0. unhide AI; unhide CI; unhide EI. unhide BA1; unhide BA2; unhide BA3.
    split.
    - (* [comment removed for export] *)
      unfold B64F_fresh, B64F_blocks. cbn [bf_flags bf_retry bf_nread bf_next bf_prev bf_ctx bf_enc bf_id bf_cid bf_eid bf_with_hdr].
      split.
      { unfold bio_cells, b64f_bio, wz. cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite
          bf_flags bf_retry bf_nread bf_next bf_prev bf_ctx bf_with_hdr]. unfold A_b64_method. rewrite RT0, NR0. assumption. }
      split. { exists junk. split; [exact LJ|]. unfold b64ctx_fresh_cells, wz. assumption. }
      unfold BIO_SIZE, B64CTX_SIZE. split; [| split; [exact NONL| split; [exact RT0| exact NR0]]].
      repeat (split; [first [assumption| lia]|]). first [assumption| lia].
    - (* [comment removed for export] *)
      membio_tac.
      all: try (unfold bio_cells, membio_bio, wz;
                cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite
                     mb_buf mb_len mb_pos mb_flags mb_numf mb_nread mb_next mb_prev mb_bb mb_bm mb_rp mb_id mb_bbid mb_bmid mb_rpid];
                unfold A_mem_buf_method; rewrite ?NUMR; assumption).
      all: match goal with |- ?G => idtac "MB2-LEFT:" G end.
  Qed.

  (* [comment removed for export] *)
End S.
