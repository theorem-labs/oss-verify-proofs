(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec Cells CellsX TacX Frame.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import USegs RMalloc_iface_stmt HeapSR_iface F_memcpy ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Rep ECH_LibState ECH_B64 ECH_C6_stmt ECH_C7_stmt ECH_C8_stmt ECH_C9_stmt ECH_C6_acc ECH_C7_read ECH_C7_rd ECH_C7_rd2 ECH_C9_ctrl ECH_C9_rdfacts ECH_C9_rdseg ECH_C9_rdloop ECH_C9_read ECH_C8_small ECH_C8_blockA ECH_C8_update ECH_C8_final ECH_UbKit.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma clr128_facts : forall x, 0 <= x < 2^31 -> 0 <= Z.land x 18446744073709551487 < 2^31 /\ Z.land (Z.land x 18446744073709551487) 128 = 0.
Proof.
  intros x Hx. split; [apply land_lt_pow2; lia|]. rewrite <- Z.land_assoc. change (Z.land 18446744073709551487 128) with 0. apply Z.land_0_r.
Qed.
Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.
  Local Ltac hide_ors := repeat match goal with H : _ \/ _ |- _ => hide H end.

  (* [comment removed for export] *)
  Lemma bioctrl_b64eof_spec :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list block) (a lo : Z) (R : b64frep) (hdr junk : list byte) (elen c : Z),
      a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 BIO_CTRL_EOF -> a2 = Z_to_bv 64 0 -> a3 = Z_to_bv 64 0 ->
      rw_cells usegs m a (bio_cells (b64f_bio R)) -> B64F_blocks LB a R -> B64F_below a R lo ->
      rw_cells usegs m (bf_ctx R) (b64ctx_used_cells (bf_enc R) hdr junk elen) -> length hdr = 32%nat ->
      map bv_unsigned (firstn 4 (skipn 24 hdr)) = map (fun z => z mod 256) [c; c / 256; c / 65536; c / 16777216] -> - 2^31 <= c <= 0 ->
      METH_b64 m ->
      stk usegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - BIOCTRL_B64_STACK -> mem_inv usegs m -> bv_unsigned ra mod 2 = 0 ->
      evt usegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
                   ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                            F (ret_pc ra) fc None m' (seg_rom usegs)
                   /\ munch [(lo, bv_unsigned sp)] m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_BIO_ctrl) fc None m (seg_rom usegs)).
  Proof.
    intros until c. intros A0 A1 A2 A3 BC BLK BEL CTX LH CONT CR METHB ST CEIL LO MI RAE. subst a0 a1 a2 a3.
    unfold BIOCTRL_B64_STACK, B64CTRL_STACK, BIOCTRL_STACK, MEMCTRL_STACK, FR_BIO_ctrl, FR_b64_ctrl, FR_mem_ctrl in LO.
    unfold P_BIO_ctrl, BIO_CTRL_EOF in *. hcb.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof BLK as (I1 & I2 & I3 & RB1 & RB2 & RB3 & FLR & RTR & NRR & NXR & PVR).
    pose proof RB1 as (AP & AAL & _ & AH & AI). pose proof BEL as (BL1 & BL2 & BL3).
    unfold BIO_SIZE, B64CTX_SIZE in *.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold bio_cells, b64f_bio, wz in BC. unfold b64ctx_used_cells, wz in CTX. cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite] in BC.
    unfold A_b64_method in BC.
    unfold METH_b64, O_METH_BREAD, A_b64_method, P_b64_ctrl, wz in METHB. norm_addr METHB.
    (* [comment removed for export] *)
    carve_frame 48%nat ST. do 7 st1. step. step. if_cases K2; zify_cond K2; [kill K2|]. clear K2.
    step. step. ubal_by AAL. step. if_lit.
    st1. step. if_false.
    step. step. ubal. step. if_lit.
    st1. step. if_false. step. step.
    st1. step. if_false. st1. step. if_true.
    step. if_lit. step. ubal. step. if_lit.
    st1. step. step. step. step. step.
    (* [comment removed for export] *)
    eapply evt_cut.
    { eapply b64ctrl_spec with (lo := lo) (LB := LB) (a := a) (mb := bf_next R) (cmd := 2) (parg := 0) (R := R) (M := mkMB 0 0 0 0 0 0 0 0 0 0 0 (0%N,0,0) (0%N,0,0) (0%N,0,0) (0%N,0,0))
        (hdr := hdr) (junk := junk) (elen := elen) (cont := c); rewrite ?unsigned_lit by lia; try reflexivity.
      all: lazymatch goal with
           | |- rw_cells _ _ _ (bio_cells _) => unfold bio_cells, b64f_bio, wz; cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite]; unfold A_b64_method; exact BC
           | |- rw_cells _ _ _ (b64ctx_used_cells _ _ _ _) => unfold b64ctx_used_cells, wz; exact CTX
           | |- B64F_blocks _ _ _ => exact BLK
           | |- B64F_below _ _ _ => exact BEL
           | |- length _ = _ => exact LH
           | |- map _ _ = _ => exact CONT
           | |- _ \/ _ => right; split; [reflexivity| exact CR]
           | |- stk _ _ _ _ => exact ST
           | |- hceil <= _ => exact CEIL
           | |- mem_inv _ _ => assumption
           | |- _ mod 2 = 0 => unfold BC_RA; rewrite unsigned_lit by lia; reflexivity
           | |- _ => try (unfold B64CTRL_STACK, BIOCTRL_STACK, MEMCTRL_STACK, FR_b64_ctrl, FR_BIO_ctrl, FR_mem_ctrl; lia); try lia
           end.
      all: match goal with |- ?G => idtac "CTRL-LEFT:" G end. }
    cbv beta. landx MU WM.
    unfold b64ctrl_rv, BIO_CTRL_EOF. change (2 =? 2) with true. cbv iota.
    (* [comment removed for export] *)
    st1. step. step. if_false. st1. step. if_true. step. do 6 st1. step. step. release_frame FR ST (bv_unsigned sp).
    finish.
    all: match goal with |- ?G => idtac "BCTRL-LEFT:" G end.
  Qed.

  Local Ltac bio_unf H := unfold bio_cells, b64f_bio, membio_bio, bf_with_hdr, wz in H;
    cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite
         bf_flags bf_retry bf_nread bf_next bf_prev bf_ctx bf_enc bf_id bf_cid bf_eid
         mb_buf mb_len mb_pos mb_flags mb_numf mb_nread mb_next mb_prev mb_bb mb_bm mb_rp mb_id mb_bbid mb_bmid mb_rpid mset] in H;
    unfold A_b64_method, A_mem_buf_method in H.
  Local Ltac bio_unf_goal := unfold bio_cells, b64f_bio, membio_bio, bf_with_hdr, wz;
    cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite
         bf_flags bf_retry bf_nread bf_next bf_prev bf_ctx bf_enc bf_id bf_cid bf_eid
         mb_buf mb_len mb_pos mb_flags mb_numf mb_nread mb_next mb_prev mb_bb mb_bm mb_rp mb_id mb_bbid mb_bmid mb_rpid mset];
    unfold A_b64_method, A_mem_buf_method.

  (* [comment removed for export] *)
  Local Ltac predj H A S :=
    lazymatch type of H with
    | rw_cells _ _ ?A2 ?cs2 => let s2 := dj_size_cells cs2 in
        lazymatch goal with
        | _ : chunk_disj A2 s2 A S |- _ => idtac
        | _ => let DJ := fresh "DJc" in assert (DJ : chunk_disj A2 s2 A S) by (unfold chunk_disj; djs) end
    | bytes_at _ _ ?A2 ?bs2 => let s2 := dj_size_len constr:(Z.of_nat (length bs2)) bs2 in
        lazymatch goal with
        | _ : chunk_disj A2 s2 A S |- _ => idtac
        | _ => let DJ := fresh "DJc" in assert (DJ : chunk_disj A2 s2 A S) by (unfold chunk_disj; djs) end
    end.
  (* [comment removed for export] *)
  Local Ltac fin_b64 m2 fl2 rt c fl' nr' d' hdr cjunk junk' :=
    apply evt_done; unfold b64rd_post;
    eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, m2, fl2, rt, c, fl', nr', d', hdr, cjunk, junk'.
  Definition rd_conv (rv : Z) : Z := if 0 <? rv then 1 else rv.
  Definition rd_rbv (rv : Z) : Z := if 0 <? rv then rv else 0.
  Definition BREADCONV_B64_STACK : Z := FR_bread_conv + Z.max B64READ_STACK BIOCTRL_B64_STACK.
  Definition RC_RA1 : Z := 0x10bfa8.   (* [comment removed for export] *)
  Definition RC_RA2 : Z := 0x10c004.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma breadconv_b64_spec :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list block) (a mb out outl rbp rbv lo : Z) (R : b64frep) (M : membio) (txt junk : list byte),
      a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 out -> a2 = Z_to_bv 64 outl -> a3 = Z_to_bv 64 rbp -> 0 < outl < 2^31 ->
      B64F_fresh LB m a R -> B64F_apart a R -> bf_next R = mb -> B64F_below a R lo -> ENCCTX LB m (bf_enc R) [] (bf_eid R) ->
      MEMBIO LB m mb M -> mb_pos M = 0 -> MEMBIO_below mb M lo -> MEMBIO_sep mb M -> bytes_at usegs m (mb_buf M) txt -> zlength txt = mb_len M ->
      zlength txt <= outl ->
      rw_cells usegs m out [CB (Z.to_nat outl) junk] -> memrd_out mb M out outl lo (bv_unsigned sp) ->
      (out + outl <= A_b64_method + O_METH_BREAD \/ A_b64_method + O_METH_BREAD + 64 <= out) ->
      Forall (fun b => out + outl <= blk_addr b \/ blk_addr b + blk_size b <= out) (blocks_B64F a R) ->
      Forall (fun b => Forall (fun b' => blk_addr b + blk_size b <= blk_addr b' \/ blk_addr b' + blk_size b' <= blk_addr b) (blocks_MEMBIO mb M)) (blocks_B64F a R) ->
      Forall (fun b => mb_buf M + mb_len M <= blk_addr b \/ blk_addr b + blk_size b <= mb_buf M) (blocks_B64F a R) ->
      rw_cells usegs m rbp [C8 (wz rbv)] -> memrd_out mb M rbp 8 lo (bv_unsigned sp) ->
      (rbp + 8 <= A_b64_method + O_METH_BREAD \/ A_b64_method + O_METH_BREAD + 64 <= rbp) ->
      Forall (fun b => rbp + 8 <= blk_addr b \/ blk_addr b + blk_size b <= rbp) (blocks_B64F a R) ->
      (rbp + 8 <= out \/ out + outl <= rbp) -> rbp mod 8 = 0 ->                  (* [comment removed for export] *)
      METH_b64 m -> METH_mem m ->
      bv_unsigned sp mod 16 = 0 -> out + outl < 2^64 ->                         (* [comment removed for export] *)
      stk usegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - BREADCONV_B64_STACK -> mem_inv usegs m -> bv_unsigned ra mod 2 = 0 ->
      let res := b64_read_spec (map bv_unsigned txt) outl in
      evt usegs (b64rd_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB (rd_conv (br_rv res)) a R (bf_nread R) mb M txt
                   out (br_out res) outl (br_used res) (Some (rbp, rd_rbv (br_rv res)))
                   ((out, out + outl) :: (rbp, rbp + 8) :: B64F_foot a R ++ MEMBIO_foot mb M) lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_bread_conv) fc None m (seg_rom usegs)).
  Proof.
    intros until junk. intros A0 A1 A2 A3 OUTL BF BAP NXT BEL ENC MB POS0 MBL MSEP TXT TLEN TLE OUTC MO OUTMB APO APM APT RBC MORB RBMB RBF RBO RBAL METHB METHM SPAL OUTLT ST CEIL LO MI RAE.
    cbv zeta. subst a0 a1 a2 a3.
    unfold P_bread_conv in *. hcb.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (LOS : lo <= bv_unsigned sp + -32 - B64READ_STACK /\ lo <= bv_unsigned sp + -32 - BIOCTRL_B64_STACK).
    { revert LO. unfold BREADCONV_B64_STACK, FR_bread_conv. clear. intros; lia. }
    destruct LOS as [LOSr LOSc].
    assert (LO32 : lo <= bv_unsigned sp + -32).
    { revert LOSr. unfold B64READ_STACK, BIOREAD_STACK, READINTERN_STACK, BREADCONV_STACK, BIOEOF_STACK, MEMREAD_STACK, BIOCTRL_STACK, MEMCTRL_STACK, DECUPDATE_STACK,
        DECFINAL_STACK, DECBLOCK_STACK, DECINIT_STACK, FR_b64_read, FR_BIO_read, FR_bio_read_intern, FR_bread_conv, FR_BIO_eof, FR_mem_read, FR_BIO_ctrl, FR_mem_ctrl,
        FR_EVP_DecodeUpdate, FR_EVP_DecodeFinal, FR_evp_decodeblock_int, FR_EVP_DecodeInit, BIOACC_STACK, FR_BIO_set_data. clear. intros; lia. }
    clear LO.
    pose proof BF as (BC & (bjunk & LJ & BX) & BLK & NONL & RT0 & NR0).
    pose proof BLK as (I1 & I2 & I3 & RB1 & RB2 & RB3 & FLR & RTR & NRR & NXR & PVR).
    pose proof RB1 as (AP & AAL & _ & AH & AI). pose proof RB2 as (CP & _ & _ & CH & CI). pose proof RB3 as (EP & _ & _ & EH & EI).
    pose proof BEL as (BL1 & BL2 & BL3). pose proof BAP as (BA1 & BA2 & BA3).
    pose proof MO as (OUTR & OUTP & OUTH & OUTF & OUTB & OUTM).
    pose proof MORB as (RBR & RBP & RBH & RBFM & RBB & RBM).
    pose proof MB as MBc.
    destruct MBc as (MC & MBB & MBM & MRP & J1 & J2 & J3 & J4 & RM1 & RM2 & RM3 & RM4 & POSR & LENR & BUFP & BUFH & MFL & RDO & AEOF & NUMR & NRD & NRD2 & MNX & MPV).
    pose proof RM1 as (MP & _ & _ & MH & MI0). pose proof RM3 as (_ & _ & _ & _ & BMI). pose proof MBL as (ML1 & ML2 & ML3 & ML4).
    pose proof (Forall_inv APO) as OA1. pose proof (Forall_inv (Forall_inv_tail APO)) as OA2. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail APO))) as OA3.
    cbn [blk_addr blk_size fst snd] in OA1, OA2, OA3.
    pose proof (Forall_inv APM) as APM1. pose proof (Forall_inv APM1) as DJ_a_mb. pose proof (Forall_inv (Forall_inv_tail APM1)) as DJ_a_bb.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail APM1))) as DJ_a_bm. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail APM1)))) as DJ_a_rp.
    cbn [blk_addr blk_size fst snd] in DJ_a_mb, DJ_a_bb, DJ_a_bm, DJ_a_rp. clear APM1.
    pose proof (Forall_inv (Forall_inv_tail APM)) as APM2. pose proof (Forall_inv APM2) as DJ_c_mb. pose proof (Forall_inv (Forall_inv_tail APM2)) as DJ_c_bb.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail APM2))) as DJ_c_bm. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail APM2)))) as DJ_c_rp.
    cbn [blk_addr blk_size fst snd] in DJ_c_mb, DJ_c_bb, DJ_c_bm, DJ_c_rp. clear APM2.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail APM))) as APM3. pose proof (Forall_inv APM3) as DJ_e_mb. pose proof (Forall_inv (Forall_inv_tail APM3)) as DJ_e_bb.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail APM3))) as DJ_e_bm. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail APM3)))) as DJ_e_rp.
    cbn [blk_addr blk_size fst snd] in DJ_e_mb, DJ_e_bb, DJ_e_bm, DJ_e_rp. clear APM3.
    pose proof (Forall_inv APT) as PT1. pose proof (Forall_inv (Forall_inv_tail APT)) as PT2. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail APT))) as PT3.
    cbn [blk_addr blk_size fst snd] in PT1, PT2, PT3.
    pose proof (Forall_inv OUTF) as OF1. pose proof (Forall_inv (Forall_inv_tail OUTF)) as OF2.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail OUTF))) as OF3. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail OUTF)))) as OF4.
    cbn [blk_addr blk_size fst snd] in OF1, OF2, OF3, OF4.
    pose proof (Forall_inv RBFM) as RF1. pose proof (Forall_inv (Forall_inv_tail RBFM)) as RF2.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail RBFM))) as RF3. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail RBFM)))) as RF4.
    cbn [blk_addr blk_size fst snd] in RF1, RF2, RF3, RF4.
    pose proof (Forall_inv RBF) as RA1. pose proof (Forall_inv (Forall_inv_tail RBF)) as RA2. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail RBF))) as RA3.
    cbn [blk_addr blk_size fst snd] in RA1, RA2, RA3.
    pose proof MSEP as ((SP1 & SP2 & SP3 & SP4 & SP5 & SP6) & PS1 & PS2 & PS3 & PS4).
    unfold BIO_SIZE, B64CTX_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE, ENCCTX_SIZE in BL1, BL2, BL3, BA1, BA2, BA3, ML1, ML2, ML3, ML4, AH, CH, EH, MH, OA1, OA2, OA3,
      DJ_a_mb, DJ_a_bb, DJ_a_bm, DJ_a_rp, DJ_c_mb, DJ_c_bb, DJ_c_bm, DJ_c_rp, DJ_e_mb, DJ_e_bb, DJ_e_bm, DJ_e_rp, PT1, PT2, PT3, AI, CI, EI, MI0, BMI,
      OF1, OF2, OF3, OF4, RF1, RF2, RF3, RF4, RA1, RA2, RA3, SP1, SP2, SP3, SP4, SP5, SP6, PS1, PS2, PS3, PS4.
    unfold A_mem_buf_method, O_METH_BREAD in OUTM, RBM. unfold A_b64_method, O_METH_BREAD in OUTMB, RBMB.
    pose proof (rw_cells_bound _ _ _ _ OUTC) as OB. cbn [cells_size csize Nat.add] in OB.
    pose proof (munch_refl ((lo, bv_unsigned sp) :: (out, out + outl) :: (rbp, rbp + 8) :: B64F_foot a R ++ MEMBIO_foot mb M) m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold B64F_foot, MEMBIO_foot, BIO_SIZE, B64CTX_SIZE, BUFMEM_SIZE in MU. cbn [app] in MU.
    bio_unf BC. rewrite NXT, RT0, NR0 in BC. unfold b64ctx_fresh_cells, wz in BX.
    bio_unf MC. rewrite NUMR in MC. unfold buf_cells, wz in MBM, MRP. cbn [bm_len bm_data bm_max bm_flags] in MBM, MRP. unfold wz in MBB. unfold wz in RBC.
    pose proof METHB as METHB0. unfold METH_b64, O_METH_BREAD, A_b64_method, wz in METHB. norm_addr METHB.
    pose proof METHM as METHM0. unfold METH_mem, O_METH_BREAD, A_mem_buf_method, wz in METHM. norm_addr METHM.
    destruct ENC as (raw & line & RAWL & RAWP & EC & LINE & _ & _ & DINV).
    unfold zlength in TLEN, TLE.
    hide_ors.
    (* [comment removed for export] *)
    unhide RBR; unhide OUTR. carve_frame 32%nat ST.
    do 5 st1. hide RBR; hide OUTR. step. step. step. if_cases K0; zify_cond K0; [kill K0|]. clear K0.
    step. step. zstep.
    eapply evt_cut. { eapply br_clamp. exact OUTL. } cbv beta. intros ms' ->.
    step. if_cases K0; zify_cond K0; [kill K0|]. clear K0. step. ubal_by AAL. step. if_lit.   (* [comment removed for export] *)
    st1. step. if_lit. step. ubal. step. if_lit.                                              (* [comment removed for export] *)
    st1. step. unfold P_b64_read. step.
    (* [comment removed for export] *)
    eapply evt_cut.
    { eapply b64read_spec with (lo := lo) (R := R) (LB := LB) (M := M) (junk := junk) (txt := txt) (mb := mb) (a := a) (out := out) (outl := outl);
        rewrite ?unsigned_lit by (clear - SPR LO32 LO0; lia); try reflexivity.
      all: lazymatch goal with
           | |- B64F_fresh _ _ _ _ => split; [bio_unf_goal; rewrite NXT, RT0, NR0; exact BC|]; split; [exists bjunk; split; [exact LJ| unfold b64ctx_fresh_cells, wz; exact BX]|];
                                      exact (conj BLK (conj NONL (conj RT0 NR0)))
           | |- B64F_apart _ _ => exact BAP
           | |- bf_next _ = _ => exact NXT
           | |- 0 < _ < _ => exact OUTL
           | |- B64F_below _ _ _ => exact BEL
           | |- ENCCTX _ _ _ _ _ => exists raw, line; split; [exact RAWL|]; split; [exact RAWP|]; split; [exact EC|]; split; [exact LINE|]; split; [exact I3|]; split; [exact RB3| exact DINV]
           | |- MEMBIO _ _ _ _ => unhide MI0; membio_tac; try (bio_unf_goal; rewrite ?NUMR, ?Z.add_0_r; assumption)
           | |- mb_pos _ = 0 => exact POS0
           | |- MEMBIO_below _ _ _ => exact MBL
           | |- MEMBIO_sep _ _ => exact MSEP
           | |- bytes_at _ _ _ _ => exact TXT
           | |- Z.of_nat (length _) = _ => exact TLEN
           | |- zlength _ = _ => exact TLEN
           | |- Z.of_nat (length _) <= _ => exact TLE
           | |- zlength _ <= _ => exact TLE
           | |- rw_cells _ _ _ [CB _ _] => exact OUTC
           | |- memrd_out _ _ _ _ _ _ => unfold memrd_out; unhide OUTR; unhide OUTB; unhide OUTM; split; [clear - OUTR; lia|]; split; [exact OUTP|]; split; [exact OUTH|]; split; [exact OUTF|]; split; [exact OUTB|]; unfold A_mem_buf_method, O_METH_BREAD; clear - OUTM; lia
           | |- _ \/ _ => unhide OUTMB; unfold A_b64_method, O_METH_BREAD; clear - OUTMB; lia
           | |- Forall _ _ => first [exact APO | exact APM | exact APT]
           | |- METH_b64 _ => unfold METH_b64, O_METH_BREAD, A_b64_method, wz; cbn; exact METHB
           | |- METH_mem _ => unfold METH_mem, O_METH_BREAD, A_mem_buf_method, wz; cbn; exact METHM
           | |- stk _ _ _ _ => exact ST
           | |- hceil <= _ => exact CEIL
           | |- _ <= _ - B64READ_STACK => exact LOSr
           | |- mem_inv _ _ => assumption
           | |- _ mod 16 = 0 => clear - SPAL SPR LO32; lia
           | |- _ + _ < 2 ^ 64 => exact OUTLT
           | |- _ mod 2 = 0 => reflexivity
           | |- _ => idtac
           end.
      all: match goal with |- ?G => idtac "CALL-LEFT:" G end. }
    cbv beta. intros ms' PO. unfold b64rd_post in PO.
    destruct PO as (p0 & p1 & p2 & q1 & q2 & q3 & q4 & q5 & q6 & q7 & p3 & p4 & p5 & p6 & m' & fl & rt & c & fl' & nr' & d' & hdr & cjunk & junk'
                    & -> & MUc & WMc & MIc & STc & BCp & FLp & RTp & LH & LJ' & CTXp & CONT & CR & CZ & RVR & ZLE & ENCp & MBp & TXTp & OUTp & METHBp & METHMp & _).
    rewrite ?unsigned_lit in MUc by (clear - SPR LO32 LO0; lia). rewrite ?unsigned_lit in STc by (clear - SPR LO32 LO0; lia).
    set (res := b64_read_spec (map bv_unsigned txt) outl) in *. clearbody res.
    replace (ret_pc (Z_to_bv 64 1097640)) with (Z_to_bv 64 1097640) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    unfold B64F_foot, MEMBIO_foot, BIO_SIZE, B64CTX_SIZE, BUFMEM_SIZE in MUc. cbn [app] in MUc.
    assert (FR' : rw_cells usegs m' (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply rw_cells_transport; [exact FR| exact MUc| exact WMc|]. cbn. unhide OUTR. clear - OUTR BL1 BL2 BL3 ML1 ML3 SPR LO32. lia. }
    assert (RBC' : rw_cells usegs m' rbp [C8 (Z_to_bv 64 rbv)]).
    { eapply rw_cells_transport; [exact RBC| exact MUc| exact WMc|]. cbn. unhide RBR; unhide RBO; unhide RA1; unhide RA2; unhide RA3; unhide RF1; unhide RF3.
      clear - RBR RBO RA1 RA2 RA3 RF1 RF3 SPR LO32. lia. }
    clear FR RBC BC BX EC MC MBB MBM MRP TXT OUTC METHB METHM ST MI.
    assert (MUf : munch [(lo, bv_unsigned sp); (out, out + outl); (rbp, rbp + 8); (a, a + 128); (bf_ctx R, bf_ctx R + 2584); (bf_enc R, bf_enc R + 92); (mb, mb + 128); (mb_bm M, mb_bm M + 32)] m m').
    { apply (munch_trans _ m m1 m' MU). eapply munch_weaken; [| exact MUc]. clear. unfold sub_fp; cbn [outside]. intros x Hx. lia. }
    pose proof (wmono_trans _ _ _ _ WM WMc) as WMf. clear MU WM MUc WMc. rename MUf into MU. rename WMf into WM. rename STc into ST. rename MIc into MI.
    (* [comment removed for export] *)
    bio_unf BCp. unfold b64ctx_used_cells, wz in CTXp.
    destruct ENCp as (raw2 & line2 & RAWL2 & RAWP2 & ECp & LINE2 & _ & _ & DINV2).
    pose proof MBp as MBp0. destruct MBp0 as (MCp & MBBp & MBMp & MRPp & MBpure). clear MBp. bio_unf MCp. unfold buf_cells, wz in MBMp, MRPp. cbn [bm_len bm_data bm_max bm_flags] in MBMp, MRPp. unfold wz in MBBp.
    pose proof METHBp as METHB1. unfold METH_b64, O_METH_BREAD, A_b64_method, wz in METHB1. norm_addr METHB1.
    pose proof METHMp as METHM1. unfold METH_mem, O_METH_BREAD, A_mem_buf_method, wz in METHM1. norm_addr METHM1.
    clear METHBp METHMp.
    cbn [mb_bb mb_bm mb_rp mb_buf mb_len mb_pos mb_flags mb_nread mset] in MCp, MBBp, MBMp, MRPp.
    (* [comment removed for export] *)
    st1. rewrite ?zx32_lit by (clear - FLp; lia). zstep.
    pose proof (clr128_facts fl FLp) as [FL2 FL3]. set (fl2 := Z.land fl 18446744073709551487) in *.
    unfold zlength in ZLE.
    assert (DJo : chunk_disj out (Z.of_nat (cells_size [CB (length (br_out res)) (map b8 (br_out res)); CB (Z.to_nat outl - length (br_out res)) junk'])) a 128).
    { unfold chunk_disj. cbn [cells_size csize Nat.add]. unhide OA1. clear - OA1 ZLE OUTL. lia. }
    unhide RA1; unhide BA1; unhide BA2; unhide DJ_a_mb; unhide DJ_a_bb; unhide DJ_a_bm; unhide DJ_a_rp; unhide PT1; unhide AI.
    st1.
    hide RA1; hide BA1; hide BA2; hide DJ_a_mb; hide DJ_a_bb; hide DJ_a_bm; hide DJ_a_rp; hide PT1; hide AI.
    change (Z_to_bv 64 fl2) with (wz fl2) in *.
    (* [comment removed for export] *)
    destruct (Z.eq_dec (br_rv res) 0) as [RZ|RNZ].
    - (* [comment removed for export] *)
      rewrite RZ in *. specialize (CZ eq_refl).
      step. if_true. step. step. step. step. step.
      eapply evt_cut.
      { eapply bioctrl_b64eof_spec with (lo := lo) (LB := LB) (a := a) (R := bf_with_hdr R fl2 rt (bf_nread R) mb (bf_prev R)) (hdr := hdr) (junk := cjunk) (elen := 0) (c := c);
          cbn [bf_flags bf_retry bf_nread bf_next bf_prev bf_ctx bf_enc bf_id bf_cid bf_eid bf_with_hdr]; rewrite ?unsigned_lit by (clear - SPR LO32 LO0; lia); try reflexivity.
        all: lazymatch goal with
             | |- rw_cells _ _ _ (bio_cells _) => bio_unf_goal; exact BCp
             | |- rw_cells _ _ _ (b64ctx_used_cells _ _ _ _) => unfold b64ctx_used_cells, wz; exact CTXp
             | |- B64F_blocks _ _ _ => unfold B64F_blocks; cbn [bf_flags bf_retry bf_nread bf_next bf_prev bf_ctx bf_enc bf_id bf_cid bf_eid bf_with_hdr];
                                      split; [exact I1|]; split; [exact I2|]; split; [exact I3|]; split; [exact RB1|]; split; [exact RB2|]; split; [exact RB3|]; split; [exact FL2|]; split; [exact RTp|]; split; [exact NRR|]; split; [clear - MP MH HCEILB; lia| exact PVR]
             | |- B64F_below _ _ _ => exact BEL
             | |- length _ = _ => exact LH
             | |- map _ _ = _ => exact CONT
             | |- - 2 ^ 31 <= _ <= 0 => clear - CR CZ; lia
             | |- METH_b64 _ => unfold METH_b64, O_METH_BREAD, A_b64_method, wz; cbn; exact METHB1
             | |- stk _ _ _ _ => exact ST
             | |- hceil <= _ => exact CEIL
             | |- _ <= _ - BIOCTRL_B64_STACK => exact LOSc
             | |- mem_inv _ _ => exact MI
             | |- _ mod 2 = 0 => reflexivity
             | |- _ => idtac
             end.
        all: match goal with |- ?G => idtac "EOFCALL-LEFT:" G end. }
      cbv beta. intros ms2 (g0 & g1 & g2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & g3 & g4 & g5 & g6 & m2 & -> & MU2 & WM2 & MI2 & ST2).
      rewrite ?unsigned_lit in MU2 by (clear - SPR LO32 LO0; lia). rewrite ?unsigned_lit in ST2 by (clear - SPR LO32 LO0; lia).
      replace (ret_pc (Z_to_bv 64 1097732)) with (Z_to_bv 64 1097732) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
      carryh MU2 WM2. rename ST2 into ST. rename MI2 into MI.
      extm MU WM MU2 WM2.
      (* [comment removed for export] *)
      step. if_lit. step. if_cases K0; zify_cond K0; [kill K0|]. clear K0. step. ubal_by RBAL. step. if_lit. step.
      assert (DJf : chunk_disj (bv_unsigned sp + -32) 32 rbp 8) by (unfold chunk_disj; unhide RBR; clear - RBR LO32; lia).
      assert (DJtb : chunk_disj 3282240 64 rbp 8) by (unfold chunk_disj; unhide RBMB; clear - RBMB; lia).
      assert (DJtm : chunk_disj 3099984 64 rbp 8) by (unfold chunk_disj; unhide RBM; clear - RBM; lia).
      predj BCp rbp 8. predj CTXp rbp 8. predj ECp rbp 8. predj MCp rbp 8. predj MBBp rbp 8. predj MBMp rbp 8. predj MRPp rbp 8. predj TXTp rbp 8.
      assert (DJo2 : chunk_disj out (Z.of_nat (cells_size [CB (length (br_out res)) (map b8 (br_out res)); CB (Z.to_nat outl - length (br_out res)) junk'])) rbp 8).
      { unfold chunk_disj. cbn [cells_size csize Nat.add]. unhide RBO. clear - RBO ZLE OUTL. lia. }
      st1.
      do 4 st1. step. release_frame FR' ST (bv_unsigned sp). step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) => fin_b64 mf fl2 rt c fl' nr' d' hdr cjunk junk' end.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
      split; [bio_unf_goal; exact BCp|]. split; [exact FL2|]. split; [exact RTp|]. split; [exact LH|]. split; [exact LJ'|].
      split; [unfold b64ctx_used_cells, wz; exact CTXp|]. split; [exact CONT|]. split; [exact CR|]. split; [intros _; exact CZ|].
      split; [clear - RVR OUTL; cbn; lia|]. split; [unfold zlength; exact ZLE|].
      split. { exists raw2, line2. split; [exact RAWL2|]. split; [exact RAWP2|]. split; [exact ECp|]. split; [exact LINE2|]. split; [exact I3|]. split; [exact RB3| exact DINV2]. }
      split. { split; [bio_unf_goal; exact MCp|]. split; [unfold wz; cbn [mb_bb mb_bm mb_rp mset]; exact MBBp|].
               split; [unfold buf_cells, wz; cbn [bm_len bm_data bm_max bm_flags mb_bb mb_bm mb_rp mb_buf mb_len mb_pos mset]; exact MBMp|].
               split; [unfold buf_cells, wz; cbn [bm_len bm_data bm_max bm_flags mb_bb mb_bm mb_rp mb_buf mb_len mb_pos mset]; exact MRPp|]. exact MBpure. }
      split; [exact TXTp|]. split; [exact OUTp|].
      split; [unfold METH_b64, O_METH_BREAD, A_b64_method, wz; cbn; exact METHB1|]. split; [unfold METH_mem, O_METH_BREAD, A_mem_buf_method, wz; cbn; exact METHM1|].
      unfold wz; split; [exact RBC'| clear - OUTL; cbn; lia].
    - (* [comment removed for export] *)
      destruct (Z.lt_ge_cases (br_rv res) 0) as [NEG|NNEG].
      + assert (RM : br_rv res = -1) by (clear - NEG RVR; lia). rewrite RM in *.
        step. if_cases K1; zify_cond K1; [clear - K1; lia|]. clear K1.
        zstep. step. ubal_by RBAL. zstep. zstep. ub_b2z.                                      (* [comment removed for export] *)
        step. if_cases K2; zify_cond K2; [| exfalso; clear - K2; lia]. clear K2.              (* [comment removed for export] *)
        step. if_lit. step.                                                                    (* [comment removed for export] *)
        assert (DJf : chunk_disj (bv_unsigned sp + -32) 32 rbp 8) by (unfold chunk_disj; unhide RBR; clear - RBR LO32; lia).
        assert (DJtb : chunk_disj 3282240 64 rbp 8) by (unfold chunk_disj; unhide RBMB; clear - RBMB; lia).
        assert (DJtm : chunk_disj 3099984 64 rbp 8) by (unfold chunk_disj; unhide RBM; clear - RBM; lia).
        predj BCp rbp 8. predj CTXp rbp 8. predj ECp rbp 8. predj MCp rbp 8. predj MBBp rbp 8. predj MBMp rbp 8. predj MRPp rbp 8. predj TXTp rbp 8.
        assert (DJo2 : chunk_disj out (Z.of_nat (cells_size [CB (length (br_out res)) (map b8 (br_out res)); CB (Z.to_nat outl - length (br_out res)) junk'])) rbp 8).
        { unfold chunk_disj. cbn [cells_size csize Nat.add]. unhide RBO. clear - RBO ZLE OUTL. lia. }
        st1.
        do 4 st1. step. release_frame FR' ST (bv_unsigned sp). step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) => fin_b64 mf fl2 rt c fl' nr' d' hdr cjunk junk' end.
        split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
        split; [bio_unf_goal; exact BCp|]. split; [exact FL2|]. split; [exact RTp|]. split; [exact LH|]. split; [exact LJ'|].
        split; [unfold b64ctx_used_cells, wz; exact CTXp|]. split; [exact CONT|]. split; [exact CR|]. split; [intros E; exfalso; clear - E; cbn in E; lia|].
        split; [clear - RVR OUTL; cbn; lia|]. split; [unfold zlength; exact ZLE|].
        split. { exists raw2, line2. split; [exact RAWL2|]. split; [exact RAWP2|]. split; [exact ECp|]. split; [exact LINE2|]. split; [exact I3|]. split; [exact RB3| exact DINV2]. }
        split. { split; [bio_unf_goal; exact MCp|]. split; [unfold wz; cbn [mb_bb mb_bm mb_rp mset]; exact MBBp|].
                 split; [unfold buf_cells, wz; cbn [bm_len bm_data bm_max bm_flags mb_bb mb_bm mb_rp mb_buf mb_len mb_pos mset]; exact MBMp|].
                 split; [unfold buf_cells, wz; cbn [bm_len bm_data bm_max bm_flags mb_bb mb_bm mb_rp mb_buf mb_len mb_pos mset]; exact MRPp|]. exact MBpure. }
        split; [exact TXTp|]. split; [exact OUTp|].
        split; [unfold METH_b64, O_METH_BREAD, A_b64_method, wz; cbn; exact METHB1|]. split; [unfold METH_mem, O_METH_BREAD, A_mem_buf_method, wz; cbn; exact METHM1|].
        unfold wz; split; [exact RBC'| clear - OUTL; cbn; lia].
      + assert (POS : 0 < br_rv res < 2^31) by (clear - RNZ NNEG RVR OUTL; lia). clear RNZ NNEG.
        step. if_cases K1; zify_cond K1; [exfalso; clear - K1 POS; lia|]. clear K1.
        unfold rd_conv, rd_rbv. replace (0 <? br_rv res) with true by (symmetry; apply Z.ltb_lt; clear - POS; lia). cbv iota.
        zstep. step. ubal_by RBAL. zstep. zstep. ub_b2z.                                      (* [comment removed for export] *)
        step. if_cases K2; zify_cond K2; rewrite ?unsigned_lit, ?signed_lit in K2 by (clear - POS; lia); [exfalso; clear - K2 POS; lia|]. clear K2.
        step. if_lit. step. step. step. step.                                                  (* [comment removed for export] *)
        change (Z_to_bv 64 (br_rv res)) with (wz (br_rv res)) at 1.
        assert (DJf : chunk_disj (bv_unsigned sp + -32) 32 rbp 8) by (unfold chunk_disj; unhide RBR; clear - RBR LO32; lia).
        assert (DJtb : chunk_disj 3282240 64 rbp 8) by (unfold chunk_disj; unhide RBMB; clear - RBMB; lia).
        assert (DJtm : chunk_disj 3099984 64 rbp 8) by (unfold chunk_disj; unhide RBM; clear - RBM; lia).
        predj BCp rbp 8. predj CTXp rbp 8. predj ECp rbp 8. predj MCp rbp 8. predj MBBp rbp 8. predj MBMp rbp 8. predj MRPp rbp 8. predj TXTp rbp 8.
        assert (DJo2 : chunk_disj out (Z.of_nat (cells_size [CB (length (br_out res)) (map b8 (br_out res)); CB (Z.to_nat outl - length (br_out res)) junk'])) rbp 8).
        { unfold chunk_disj. cbn [cells_size csize Nat.add]. unhide RBO. clear - RBO ZLE OUTL. lia. }
        st1.
        do 4 st1. step. release_frame FR' ST (bv_unsigned sp). step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) => fin_b64 mf fl2 rt c fl' nr' d' hdr cjunk junk' end.
        split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
        split; [bio_unf_goal; exact BCp|]. split; [exact FL2|]. split; [exact RTp|]. split; [exact LH|]. split; [exact LJ'|].
        split; [unfold b64ctx_used_cells, wz; exact CTXp|]. split; [exact CONT|]. split; [exact CR|]. split; [intros E; exfalso; clear - E POS; lia|].
        split; [clear - RVR OUTL; cbn; lia|]. split; [unfold zlength; exact ZLE|].
        split. { exists raw2, line2. split; [exact RAWL2|]. split; [exact RAWP2|]. split; [exact ECp|]. split; [exact LINE2|]. split; [exact I3|]. split; [exact RB3| exact DINV2]. }
        split. { split; [bio_unf_goal; exact MCp|]. split; [unfold wz; cbn [mb_bb mb_bm mb_rp mset]; exact MBBp|].
                 split; [unfold buf_cells, wz; cbn [bm_len bm_data bm_max bm_flags mb_bb mb_bm mb_rp mb_buf mb_len mb_pos mset]; exact MBMp|].
                 split; [unfold buf_cells, wz; cbn [bm_len bm_data bm_max bm_flags mb_bb mb_bm mb_rp mb_buf mb_len mb_pos mset]; exact MRPp|]. exact MBpure. }
        split; [exact TXTp|]. split; [exact OUTp|].
        split; [unfold METH_b64, O_METH_BREAD, A_b64_method, wz; cbn; exact METHB1|]. split; [unfold METH_mem, O_METH_BREAD, A_mem_buf_method, wz; cbn; exact METHM1|].
        unfold wz; split; [exact RBC'| clear - OUTL RVR POS; cbn; lia].
  Qed.

  Definition BIOEOF_B64_STACK : Z := FR_BIO_eof + BIOCTRL_B64_STACK.

  (* [comment removed for export] *)
  Lemma bioeof_b64_spec :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list block) (a lo : Z) (R : b64frep) (hdr junk : list byte) (elen c : Z),
      a0 = Z_to_bv 64 a ->
      rw_cells usegs m a (bio_cells (b64f_bio R)) -> B64F_blocks LB a R -> B64F_below a R lo ->
      rw_cells usegs m (bf_ctx R) (b64ctx_used_cells (bf_enc R) hdr junk elen) -> length hdr = 32%nat ->
      map bv_unsigned (firstn 4 (skipn 24 hdr)) = map (fun z => z mod 256) [c; c / 256; c / 65536; c / 16777216] -> - 2^31 <= c <= 0 ->
      METH_b64 m ->
      stk usegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - BIOEOF_B64_STACK -> mem_inv usegs m -> bv_unsigned ra mod 2 = 0 ->
      evt usegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
                   ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                            F (ret_pc ra) fc None m' (seg_rom usegs)
                   /\ munch [(lo, bv_unsigned sp)] m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_BIO_eof) fc None m (seg_rom usegs)).
  Proof.
    intros until c. intros A0 BC BLK BEL CTX LH CONT CR METHB ST CEIL LO MI RAE. subst a0.
    unfold BIOEOF_B64_STACK, BIOCTRL_B64_STACK, B64CTRL_STACK, BIOCTRL_STACK, MEMCTRL_STACK, FR_BIO_eof, FR_BIO_ctrl, FR_b64_ctrl, FR_mem_ctrl in LO.
    unfold P_BIO_eof in *. hcb.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof BLK as (I1 & I2 & I3 & RB1 & RB2 & RB3 & FLR & RTR & NRR & NXR & PVR).
    pose proof RB1 as (AP & AAL & _ & AH & AI). pose proof BEL as (BL1 & BL2 & BL3).
    unfold BIO_SIZE, B64CTX_SIZE in *.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof (bio_flags_byte _ _ _ BC) as RD. cbn [bio_flags b64f_bio] in RD.
    unfold bio_cells, b64f_bio, wz in BC. unfold b64ctx_used_cells, wz in CTX.
    cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite] in BC.
    unfold A_b64_method in BC.
    pose proof METHB as METHB0. unfold METH_b64, O_METH_BREAD, A_b64_method, P_b64_ctrl, wz in METHB. norm_addr METHB.
    (* [comment removed for export] *)
    step. if_cases K0; zify_cond K0; [kill K0|]. clear K0. step. ubal_by AAL. step. if_lit.
    st1. clear RD. zstep. rewrite wz_unsigned by (clear - FLR; pose proof (Z.mod_pos_bound (bf_flags R) 256); lia). rewrite land_mod256_128 by (clear - FLR; lia).
    step. if_cases K2; zify_cond K2.
    - (* [comment removed for export] *)
      step. zstep. step.
      try match goal with |- context [Z_to_bv 64 (bv_swrap 32 ?e)] => change (bv_swrap 32 e) with 1 end.
      apply evt_done. do 15 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
    - (* [comment removed for export] *)
      carve_frame 16%nat ST. do 3 st1. step. step. step. step. unfold P_BIO_ctrl. step.
      eapply evt_cut.
      { eapply bioctrl_b64eof_spec with (lo := lo) (LB := LB) (a := a) (R := R) (hdr := hdr) (junk := junk) (elen := elen) (c := c);
          rewrite ?unsigned_lit by (clear - SPR LO LO0; lia); try reflexivity.
        all: lazymatch goal with
             | |- rw_cells _ _ _ (bio_cells _) => unfold bio_cells, b64f_bio, wz; cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite]; unfold A_b64_method; exact BC
             | |- rw_cells _ _ _ (b64ctx_used_cells _ _ _ _) => unfold b64ctx_used_cells, wz; exact CTX
             | |- B64F_blocks _ _ _ => exact BLK
             | |- B64F_below _ _ _ => exact BEL
             | |- length _ = _ => exact LH
             | |- map _ _ = _ => exact CONT
             | |- - 2 ^ 31 <= _ <= 0 => exact CR
             | |- METH_b64 _ => unfold METH_b64, O_METH_BREAD, A_b64_method, wz; cbn; exact METHB
             | |- stk _ _ _ _ => exact ST
             | |- hceil <= _ => exact CEIL
             | |- _ <= _ - BIOCTRL_B64_STACK => unfold BIOCTRL_B64_STACK, B64CTRL_STACK, BIOCTRL_STACK, MEMCTRL_STACK, FR_BIO_ctrl, FR_b64_ctrl, FR_mem_ctrl; clear - LO; lia
             | |- mem_inv _ _ => assumption
             | |- _ mod 2 = 0 => reflexivity
             | |- _ => idtac
             end.
        all: match goal with |- ?G => idtac "EOFU-LEFT:" G end. }
      cbv beta. intros ms2 (g0 & g1 & g2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & g3 & g4 & g5 & g6 & m2 & -> & MU2 & WM2 & MI2 & ST2).
      rewrite ?unsigned_lit in MU2 by (clear - SPR LO LO0; lia). rewrite ?unsigned_lit in ST2 by (clear - SPR LO LO0; lia).
      replace (ret_pc (Z_to_bv 64 1095932)) with (Z_to_bv 64 1095932) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
      carryh MU2 WM2. rename ST2 into ST. rename MI2 into MI.
      extm MU WM MU2 WM2.
      st1. st1. step. step. zstep.
      try match goal with |- context [Z_to_bv 64 (bv_swrap 32 ?e)] => change (bv_swrap 32 e) with 1 end.
      release_frame FR ST (bv_unsigned sp). step.
      apply evt_done. do 15 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
  Qed.

  Definition READINTERN_B64_STACK : Z := FR_bio_read_intern + BREADCONV_B64_STACK.

  (* [comment removed for export] *)
  Lemma readintern_b64_spec :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list block) (a mb out outl rbp rbv lo : Z) (R : b64frep) (M : membio) (txt junk : list byte),
      a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 out -> a2 = Z_to_bv 64 outl -> a3 = Z_to_bv 64 rbp -> 0 < outl < 2^31 ->
      B64F_fresh LB m a R -> B64F_apart a R -> bf_next R = mb -> B64F_below a R lo -> ENCCTX LB m (bf_enc R) [] (bf_eid R) ->
      MEMBIO LB m mb M -> mb_pos M = 0 -> MEMBIO_below mb M lo -> MEMBIO_sep mb M -> bytes_at usegs m (mb_buf M) txt -> zlength txt = mb_len M ->
      zlength txt <= outl ->
      rw_cells usegs m out [CB (Z.to_nat outl) junk] -> memrd_out mb M out outl lo (bv_unsigned sp) ->
      (out + outl <= A_b64_method + O_METH_BREAD \/ A_b64_method + O_METH_BREAD + 64 <= out) ->
      Forall (fun b => out + outl <= blk_addr b \/ blk_addr b + blk_size b <= out) (blocks_B64F a R) ->
      Forall (fun b => Forall (fun b' => blk_addr b + blk_size b <= blk_addr b' \/ blk_addr b' + blk_size b' <= blk_addr b) (blocks_MEMBIO mb M)) (blocks_B64F a R) ->
      Forall (fun b => mb_buf M + mb_len M <= blk_addr b \/ blk_addr b + blk_size b <= mb_buf M) (blocks_B64F a R) ->
      rw_cells usegs m rbp [C8 (wz rbv)] -> memrd_out mb M rbp 8 lo (bv_unsigned sp) ->
      (rbp + 8 <= A_b64_method + O_METH_BREAD \/ A_b64_method + O_METH_BREAD + 64 <= rbp) ->
      Forall (fun b => rbp + 8 <= blk_addr b \/ blk_addr b + blk_size b <= rbp) (blocks_B64F a R) ->
      (rbp + 8 <= out \/ out + outl <= rbp) -> rbp mod 8 = 0 ->                  (* [comment removed for export] *)
      METH_b64 m -> METH_mem m ->
      bv_unsigned sp mod 16 = 0 -> out + outl < 2^64 ->                         (* [comment removed for export] *)
      stk usegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - READINTERN_B64_STACK -> mem_inv usegs m -> bv_unsigned ra mod 2 = 0 ->
      let res := b64_read_spec (map bv_unsigned txt) outl in
      evt usegs (b64rd_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB (rd_conv (br_rv res)) a R (bf_nread R + rd_rbv (br_rv res)) mb M txt
                   out (br_out res) outl (br_used res) (Some (rbp, rd_rbv (br_rv res)))
                   ((out, out + outl) :: (rbp, rbp + 8) :: B64F_foot a R ++ MEMBIO_foot mb M) lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_bio_read_intern) fc None m (seg_rom usegs)).
  Proof.
    intros until junk. intros A0 A1 A2 A3 OUTL BF BAP NXT BEL ENC MB POS0 MBL MSEP TXT TLEN TLE OUTC MO OUTMB APO APM APT RBC MORB RBMB RBF RBO RBAL METHB METHM SPAL OUTLT ST CEIL LO MI RAE.
    cbv zeta. subst a0 a1 a2 a3.
    unfold P_bio_read_intern in *. hcb.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (LOS : lo <= bv_unsigned sp + -80 - BREADCONV_B64_STACK /\ lo <= bv_unsigned sp + -80 - BIOCTRL_B64_STACK).
    { revert LO. unfold READINTERN_B64_STACK, BREADCONV_B64_STACK, FR_bio_read_intern, FR_bread_conv. clear. intros; lia. }
    destruct LOS as [LOSr LOSc].
    assert (LO32 : lo <= bv_unsigned sp + -80).
    { revert LOSc. unfold BIOCTRL_B64_STACK, B64CTRL_STACK, BIOCTRL_STACK, MEMCTRL_STACK, FR_BIO_ctrl, FR_b64_ctrl, FR_mem_ctrl. clear. intros; lia. }
    assert (LO32x : True).
    { revert LOSr. unfold B64READ_STACK, BIOREAD_STACK, READINTERN_STACK, BREADCONV_STACK, BIOEOF_STACK, MEMREAD_STACK, BIOCTRL_STACK, MEMCTRL_STACK, DECUPDATE_STACK,
        DECFINAL_STACK, DECBLOCK_STACK, DECINIT_STACK, FR_b64_read, FR_BIO_read, FR_bio_read_intern, FR_bread_conv, FR_BIO_eof, FR_mem_read, FR_BIO_ctrl, FR_mem_ctrl,
        FR_EVP_DecodeUpdate, FR_EVP_DecodeFinal, FR_evp_decodeblock_int, FR_EVP_DecodeInit, BIOACC_STACK, FR_BIO_set_data. clear. intros; lia. }
    clear LO.
    pose proof BF as (BC & (bjunk & LJ & BX) & BLK & NONL & RT0 & NR0).
    pose proof BLK as (I1 & I2 & I3 & RB1 & RB2 & RB3 & FLR & RTR & NRR & NXR & PVR).
    pose proof RB1 as (AP & AAL & _ & AH & AI). pose proof RB2 as (CP & _ & _ & CH & CI). pose proof RB3 as (EP & _ & _ & EH & EI).
    pose proof BEL as (BL1 & BL2 & BL3). pose proof BAP as (BA1 & BA2 & BA3).
    pose proof MO as (OUTR & OUTP & OUTH & OUTF & OUTB & OUTM).
    pose proof MORB as (RBR & RBP & RBH & RBFM & RBB & RBM).
    pose proof MB as MBc.
    destruct MBc as (MC & MBB & MBM & MRP & J1 & J2 & J3 & J4 & RM1 & RM2 & RM3 & RM4 & POSR & LENR & BUFP & BUFH & MFL & RDO & AEOF & NUMR & NRD & NRD2 & MNX & MPV).
    pose proof RM1 as (MP & _ & _ & MH & MI0). pose proof RM3 as (_ & _ & _ & _ & BMI). pose proof MBL as (ML1 & ML2 & ML3 & ML4).
    pose proof (Forall_inv APO) as OA1. pose proof (Forall_inv (Forall_inv_tail APO)) as OA2. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail APO))) as OA3.
    cbn [blk_addr blk_size fst snd] in OA1, OA2, OA3.
    pose proof (Forall_inv APM) as APM1. pose proof (Forall_inv APM1) as DJ_a_mb. pose proof (Forall_inv (Forall_inv_tail APM1)) as DJ_a_bb.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail APM1))) as DJ_a_bm. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail APM1)))) as DJ_a_rp.
    cbn [blk_addr blk_size fst snd] in DJ_a_mb, DJ_a_bb, DJ_a_bm, DJ_a_rp. clear APM1.
    pose proof (Forall_inv (Forall_inv_tail APM)) as APM2. pose proof (Forall_inv APM2) as DJ_c_mb. pose proof (Forall_inv (Forall_inv_tail APM2)) as DJ_c_bb.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail APM2))) as DJ_c_bm. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail APM2)))) as DJ_c_rp.
    cbn [blk_addr blk_size fst snd] in DJ_c_mb, DJ_c_bb, DJ_c_bm, DJ_c_rp. clear APM2.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail APM))) as APM3. pose proof (Forall_inv APM3) as DJ_e_mb. pose proof (Forall_inv (Forall_inv_tail APM3)) as DJ_e_bb.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail APM3))) as DJ_e_bm. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail APM3)))) as DJ_e_rp.
    cbn [blk_addr blk_size fst snd] in DJ_e_mb, DJ_e_bb, DJ_e_bm, DJ_e_rp. clear APM3.
    pose proof (Forall_inv APT) as PT1. pose proof (Forall_inv (Forall_inv_tail APT)) as PT2. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail APT))) as PT3.
    cbn [blk_addr blk_size fst snd] in PT1, PT2, PT3.
    pose proof (Forall_inv OUTF) as OF1. pose proof (Forall_inv (Forall_inv_tail OUTF)) as OF2.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail OUTF))) as OF3. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail OUTF)))) as OF4.
    cbn [blk_addr blk_size fst snd] in OF1, OF2, OF3, OF4.
    pose proof (Forall_inv RBFM) as RF1. pose proof (Forall_inv (Forall_inv_tail RBFM)) as RF2.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail RBFM))) as RF3. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail RBFM)))) as RF4.
    cbn [blk_addr blk_size fst snd] in RF1, RF2, RF3, RF4.
    pose proof (Forall_inv RBF) as RA1. pose proof (Forall_inv (Forall_inv_tail RBF)) as RA2. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail RBF))) as RA3.
    cbn [blk_addr blk_size fst snd] in RA1, RA2, RA3.
    pose proof MSEP as ((SP1 & SP2 & SP3 & SP4 & SP5 & SP6) & PS1 & PS2 & PS3 & PS4).
    unfold BIO_SIZE, B64CTX_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE, ENCCTX_SIZE in BL1, BL2, BL3, BA1, BA2, BA3, ML1, ML2, ML3, ML4, AH, CH, EH, MH, OA1, OA2, OA3,
      DJ_a_mb, DJ_a_bb, DJ_a_bm, DJ_a_rp, DJ_c_mb, DJ_c_bb, DJ_c_bm, DJ_c_rp, DJ_e_mb, DJ_e_bb, DJ_e_bm, DJ_e_rp, PT1, PT2, PT3, AI, CI, EI, MI0, BMI,
      OF1, OF2, OF3, OF4, RF1, RF2, RF3, RF4, RA1, RA2, RA3, SP1, SP2, SP3, SP4, SP5, SP6, PS1, PS2, PS3, PS4.
    unfold A_mem_buf_method, O_METH_BREAD in OUTM, RBM. unfold A_b64_method, O_METH_BREAD in OUTMB, RBMB.
    pose proof (rw_cells_bound _ _ _ _ OUTC) as OB. cbn [cells_size csize Nat.add] in OB.
    pose proof (munch_refl ((lo, bv_unsigned sp) :: (out, out + outl) :: (rbp, rbp + 8) :: B64F_foot a R ++ MEMBIO_foot mb M) m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold B64F_foot, MEMBIO_foot, BIO_SIZE, B64CTX_SIZE, BUFMEM_SIZE in MU. cbn [app] in MU.
    bio_unf BC. rewrite NXT, RT0, NR0 in BC. unfold b64ctx_fresh_cells, wz in BX.
    bio_unf MC. rewrite NUMR in MC. unfold buf_cells, wz in MBM, MRP. cbn [bm_len bm_data bm_max bm_flags] in MBM, MRP. unfold wz in MBB. unfold wz in RBC.
    pose proof METHB as METHB0. unfold METH_b64, O_METH_BREAD, A_b64_method, wz in METHB. norm_addr METHB.
    pose proof METHM as METHM0. unfold METH_mem, O_METH_BREAD, A_mem_buf_method, wz in METHM. norm_addr METHM.
    destruct ENC as (raw & line & RAWL & RAWP & EC & LINE & _ & _ & DINV).
    unfold zlength in TLEN, TLE.
    hide_ors.
    (* [comment removed for export] *)
    unhide RBR; unhide OUTR. carve_frame 80%nat ST.
    do 10 st1. hide RBR; hide OUTR. step. step. if_cases K0; zify_cond K0; [kill K0|]. clear K0.
    step. step. ubal_by AAL. step. if_lit.
    st1. step. step. step. step. if_false.
    step. step. ubal. step. if_lit.
    st1. step. if_false. step. step.
    st1. step. if_false. st1. step. if_true.
    st1. step. if_false.
    st1. step. if_lit. step. ubal. step. if_lit.
    st1. step. step. step. step. unfold P_bread_conv. step.
    (* [comment removed for export] *)
    eapply evt_cut.
    { eapply breadconv_b64_spec with (lo := lo) (R := R) (LB := LB) (M := M) (junk := junk) (txt := txt) (mb := mb) (a := a) (out := out) (outl := outl) (rbp := rbp) (rbv := rbv);
        rewrite ?unsigned_lit by (clear - SPR LO32 LO0; lia); try reflexivity.
      all: lazymatch goal with
           | |- B64F_fresh _ _ _ _ => split; [bio_unf_goal; rewrite NXT, RT0, NR0; exact BC|]; split; [exists bjunk; split; [exact LJ| unfold b64ctx_fresh_cells, wz; exact BX]|];
                                      exact (conj BLK (conj NONL (conj RT0 NR0)))
           | |- B64F_apart _ _ => exact BAP
           | |- bf_next _ = _ => exact NXT
           | |- 0 < _ < _ => exact OUTL
           | |- B64F_below _ _ _ => exact BEL
           | |- ENCCTX _ _ _ _ _ => exists raw, line; split; [exact RAWL|]; split; [exact RAWP|]; split; [exact EC|]; split; [exact LINE|]; split; [exact I3|]; split; [exact RB3| exact DINV]
           | |- MEMBIO _ _ _ _ => unhide MI0; membio_tac; try (bio_unf_goal; rewrite ?NUMR, ?Z.add_0_r; assumption)
           | |- mb_pos _ = 0 => exact POS0
           | |- MEMBIO_below _ _ _ => exact MBL
           | |- MEMBIO_sep _ _ => exact MSEP
           | |- bytes_at _ _ _ _ => exact TXT
           | |- Z.of_nat (length _) = _ => exact TLEN
           | |- zlength _ = _ => exact TLEN
           | |- Z.of_nat (length _) <= _ => exact TLE
           | |- zlength _ <= _ => exact TLE
           | |- rw_cells _ _ _ [CB _ _] => exact OUTC
           | |- rw_cells _ _ _ [C8 _] => unfold wz; exact RBC
           | |- memrd_out _ _ _ 8 _ _ => unfold memrd_out; unhide RBR; unhide RBB; unhide RBM; split; [clear - RBR; lia|]; split; [exact RBP|]; split; [exact RBH|]; split; [exact RBFM|]; split; [exact RBB|]; unfold A_mem_buf_method, O_METH_BREAD; clear - RBM; lia
           | |- memrd_out _ _ _ _ _ _ => unfold memrd_out; unhide OUTR; unhide OUTB; unhide OUTM; split; [clear - OUTR; lia|]; split; [exact OUTP|]; split; [exact OUTH|]; split; [exact OUTF|]; split; [exact OUTB|]; unfold A_mem_buf_method, O_METH_BREAD; clear - OUTM; lia
           | |- _ + 8 <= A_b64_method + _ \/ _ => exact RBMB
           | |- _ + _ <= A_b64_method + _ \/ _ => exact OUTMB
           | |- _ + 8 <= _ \/ _ => exact RBO
           | |- Forall _ _ => first [exact APO | exact APM | exact APT | exact RBF]
           | |- METH_b64 _ => unfold METH_b64, O_METH_BREAD, A_b64_method, wz; cbn; exact METHB
           | |- METH_mem _ => unfold METH_mem, O_METH_BREAD, A_mem_buf_method, wz; cbn; exact METHM
           | |- stk _ _ _ _ => exact ST
           | |- hceil <= _ => exact CEIL
           | |- _ <= _ - BREADCONV_B64_STACK => exact LOSr
           | |- mem_inv _ _ => assumption
           | |- _ mod 8 = 0 => first [exact RBAL | clear - SPAL SPR LO32; lia]
           | |- _ mod 16 = 0 => clear - SPAL SPR LO32; lia
           | |- _ + _ < 2 ^ 64 => exact OUTLT
           | |- _ mod 2 = 0 => reflexivity
           | |- _ => idtac
           end.
      all: match goal with |- ?G => idtac "CALL-LEFT:" G end. }
    cbv beta. intros ms' PO. unfold b64rd_post in PO.
    destruct PO as (p0 & p1 & p2 & q1 & q2 & q3 & q4 & q5 & q6 & q7 & p3 & p4 & p5 & p6 & m' & fl & rt & c & fl' & nr' & d' & hdr & cjunk & junk'
                    & -> & MUc & WMc & MIc & STc & BCp & FLp & RTp & LH & LJ' & CTXp & CONT & CR & CZ & RVR & ZLE & ENCp & MBp & TXTp & OUTp & METHBp & METHMp & RBCp & RBV).
    rewrite ?unsigned_lit in MUc by (clear - SPR LO32 LO0; lia). rewrite ?unsigned_lit in STc by (clear - SPR LO32 LO0; lia).
    set (res := b64_read_spec (map bv_unsigned txt) outl) in *. clearbody res.
    replace (ret_pc (Z_to_bv 64 1093680)) with (Z_to_bv 64 1093680) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    unfold B64F_foot, MEMBIO_foot, BIO_SIZE, B64CTX_SIZE, BUFMEM_SIZE in MUc. cbn [app] in MUc.
    lazymatch type of FR with rw_cells _ _ _ ?cs => assert (FR' : rw_cells usegs m' (bv_unsigned sp + -80) cs) end.
    { eapply rw_cells_transport; [exact FR| exact MUc| exact WMc|]. cbn. unhide OUTR; unhide RBR. clear - OUTR RBR BL1 BL2 BL3 ML1 ML3 SPR LO32. lia. }
    clear FR RBC BC BX EC MC MBB MBM MRP TXT OUTC METHB METHM ST MI.
    assert (MUf : munch [(lo, bv_unsigned sp); (out, out + outl); (rbp, rbp + 8); (a, a + 128); (bf_ctx R, bf_ctx R + 2584); (bf_enc R, bf_enc R + 92); (mb, mb + 128); (mb_bm M, mb_bm M + 32)] m m').
    { lazymatch type of MU with munch _ _ ?mq => apply (munch_trans _ m mq m' MU) end. eapply munch_weaken; [| exact MUc]. clear. unfold sub_fp; cbn [outside]. intros x Hx. lia. }
    pose proof (wmono_trans _ _ _ _ WM WMc) as WMf. clear MU WM MUc WMc. rename MUf into MU. rename WMf into WM. rename STc into ST. rename MIc into MI.
    pose proof BCp as BCf. bio_unf BCp. unfold b64ctx_used_cells, wz in CTXp.
    destruct ENCp as (raw2 & line2 & RAWL2 & RAWP2 & ECp & LINE2 & _ & _ & DINV2).
    pose proof MBp as MBp0. destruct MBp0 as (MCp & MBBp & MBMp & MRPp & MBpure). clear MBp. bio_unf MCp. unfold buf_cells, wz in MBMp, MRPp. cbn [bm_len bm_data bm_max bm_flags] in MBMp, MRPp. unfold wz in MBBp.
    cbn [mb_bb mb_bm mb_rp mb_buf mb_len mb_pos mb_flags mb_nread mset] in MCp, MBBp, MBMp, MRPp.
    pose proof METHBp as METHB1. unfold METH_b64, O_METH_BREAD, A_b64_method, wz in METHB1. norm_addr METHB1.
    pose proof METHMp as METHM1. unfold METH_mem, O_METH_BREAD, A_mem_buf_method, wz in METHM1. norm_addr METHM1.
    clear METHBp METHMp. unfold wz in RBCp. unfold zlength in ZLE.
    (* [comment removed for export] *)
    step. step. ubal_by RBAL.
    destruct (Z.eq_dec (br_rv res) 0) as [RZ|RNZ].
    - (* [comment removed for export] *)
      rewrite RZ in *. change (rd_conv 0) with 0 in *. change (rd_rbv 0) with 0 in *.
      step. if_true. step. if_cases K1; zify_cond K1; [kill K1|]. clear K1. step. if_false.
      step. unfold P_BIO_eof. step.
      eapply evt_cut.
      { eapply bioeof_b64_spec with (lo := lo) (LB := LB) (a := a) (R := bf_with_hdr R fl rt (bf_nread R) mb (bf_prev R)) (hdr := hdr) (junk := cjunk) (elen := 0) (c := c);
          cbn [bf_flags bf_retry bf_nread bf_next bf_prev bf_ctx bf_enc bf_id bf_cid bf_eid bf_with_hdr]; rewrite ?unsigned_lit by (clear - SPR LO32 LO0; lia); try reflexivity.
        all: lazymatch goal with
             | |- rw_cells _ _ _ (bio_cells _) => bio_unf_goal; exact BCp
             | |- rw_cells _ _ _ (b64ctx_used_cells _ _ _ _) => unfold b64ctx_used_cells, wz; exact CTXp
             | |- B64F_blocks _ _ _ => unfold B64F_blocks; cbn [bf_flags bf_retry bf_nread bf_next bf_prev bf_ctx bf_enc bf_id bf_cid bf_eid bf_with_hdr];
                                      split; [exact I1|]; split; [exact I2|]; split; [exact I3|]; split; [exact RB1|]; split; [exact RB2|]; split; [exact RB3|]; split; [exact FLp|]; split; [exact RTp|]; split; [exact NRR|]; split; [clear - MP MH HCEILB; lia| exact PVR]
             | |- B64F_below _ _ _ => exact BEL
             | |- length _ = _ => exact LH
             | |- map _ _ = _ => exact CONT
             | |- - 2 ^ 31 <= _ <= 0 => specialize (CZ eq_refl); clear - CR CZ; lia
             | |- METH_b64 _ => unfold METH_b64, O_METH_BREAD, A_b64_method, wz; cbn; exact METHB1
             | |- stk _ _ _ _ => exact ST
             | |- hceil <= _ => exact CEIL
             | |- _ <= _ - BIOEOF_B64_STACK => revert LOSr; unfold BIOEOF_B64_STACK, BREADCONV_B64_STACK, FR_BIO_eof, FR_bread_conv; clear; intros; lia
             | |- mem_inv _ _ => exact MI
             | |- _ mod 2 = 0 => reflexivity
             | |- _ => idtac
             end.
        all: match goal with |- ?G => idtac "EOFCALL-LEFT:" G end. }
      cbv beta. intros ms2 (g0 & g1 & g2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & g3 & g4 & g5 & g6 & m2 & -> & MU2 & WM2 & MI2 & ST2).
      rewrite ?unsigned_lit in MU2 by (clear - SPR LO32 LO0; lia). rewrite ?unsigned_lit in ST2 by (clear - SPR LO32 LO0; lia).
      replace (ret_pc (Z_to_bv 64 1093856)) with (Z_to_bv 64 1093856) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
      carryh MU2 WM2. rename ST2 into ST. rename MI2 into MI. clear BCf.
      extm MU WM MU2 WM2.
      zstep. zstep. change (Z.b2z (0 <? 1)) with 1.
      st1. step. if_false. st1. step. if_true. zstep. step. if_true. zstep.
      do 9 st1. step. step. release_frame FR' ST (bv_unsigned sp).
      try match goal with |- context [Z_to_bv 64 (bv_swrap 32 ?e)] => change (bv_swrap 32 e) with 0 end.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) => fin_b64 mf fl rt c fl' nr' d' hdr cjunk junk' end.
        split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
        split; [bio_unf_goal; rewrite ?Z.add_0_r; exact BCp|]. split; [exact FLp|]. split; [exact RTp|]. split; [exact LH|]. split; [exact LJ'|].
        split; [unfold b64ctx_used_cells, wz; exact CTXp|]. split; [exact CONT|]. split; [exact CR|]. split; [exact CZ|].
        split; [exact RVR|]. split; [unfold zlength; exact ZLE|].
        split. { exists raw2, line2. split; [exact RAWL2|]. split; [exact RAWP2|]. split; [exact ECp|]. split; [exact LINE2|]. split; [exact I3|]. split; [exact RB3| exact DINV2]. }
        split. { split; [bio_unf_goal; exact MCp|]. split; [unfold wz; cbn [mb_bb mb_bm mb_rp mset]; exact MBBp|].
                 split; [unfold buf_cells, wz; cbn [bm_len bm_data bm_max bm_flags mb_bb mb_bm mb_rp mb_buf mb_len mb_pos mset]; exact MBMp|].
                 split; [unfold buf_cells, wz; cbn [bm_len bm_data bm_max bm_flags mb_bb mb_bm mb_rp mb_buf mb_len mb_pos mset]; exact MRPp|]. exact MBpure. }
        split; [exact TXTp|]. split; [exact OUTp|].
        split; [unfold METH_b64, O_METH_BREAD, A_b64_method, wz; cbn; exact METHB1|]. split; [unfold METH_mem, O_METH_BREAD, A_mem_buf_method, wz; cbn; exact METHM1|].
        split; [exact RBCp| exact RBV].
    - clear BCf. destruct (Z.lt_ge_cases (br_rv res) 0) as [NEG|NNEG].
      + (* [comment removed for export] *)
        assert (RM : br_rv res = -1). { revert RVR NEG. unfold rd_conv. destruct (0 <? br_rv res) eqn:E; [apply Z.ltb_lt in E| apply Z.ltb_ge in E]; clear - E; intros; lia. }
        rewrite RM in *. change (rd_conv (-1)) with (-1) in *. change (rd_rbv (-1)) with 0 in *.
        step. if_true. step. if_cases K1; zify_cond K1; [kill K1|]. clear K1. step. if_true.
        st1. step. if_false. st1. step. if_true. zstep. step. if_true. zstep.
        do 9 st1. step. step. release_frame FR' ST (bv_unsigned sp).
        try match goal with |- context [Z_to_bv 64 (bv_swrap 32 ?e)] => change (bv_swrap 32 e) with (-1) end.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) => fin_b64 mf fl rt c fl' nr' d' hdr cjunk junk' end.
        split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
        split; [bio_unf_goal; rewrite ?Z.add_0_r; exact BCp|]. split; [exact FLp|]. split; [exact RTp|]. split; [exact LH|]. split; [exact LJ'|].
        split; [unfold b64ctx_used_cells, wz; exact CTXp|]. split; [exact CONT|]. split; [exact CR|]. split; [exact CZ|].
        split; [exact RVR|]. split; [unfold zlength; exact ZLE|].
        split. { exists raw2, line2. split; [exact RAWL2|]. split; [exact RAWP2|]. split; [exact ECp|]. split; [exact LINE2|]. split; [exact I3|]. split; [exact RB3| exact DINV2]. }
        split. { split; [bio_unf_goal; exact MCp|]. split; [unfold wz; cbn [mb_bb mb_bm mb_rp mset]; exact MBBp|].
                 split; [unfold buf_cells, wz; cbn [bm_len bm_data bm_max bm_flags mb_bb mb_bm mb_rp mb_buf mb_len mb_pos mset]; exact MBMp|].
                 split; [unfold buf_cells, wz; cbn [bm_len bm_data bm_max bm_flags mb_bb mb_bm mb_rp mb_buf mb_len mb_pos mset]; exact MRPp|]. exact MBpure. }
        split; [exact TXTp|]. split; [exact OUTp|].
        split; [unfold METH_b64, O_METH_BREAD, A_b64_method, wz; cbn; exact METHB1|]. split; [unfold METH_mem, O_METH_BREAD, A_mem_buf_method, wz; cbn; exact METHM1|].
        split; [exact RBCp| exact RBV].
      + (* [comment removed for export] *)
        assert (POS : 0 < br_rv res <= outl).
        { revert RVR NNEG RNZ RBV. unfold rd_conv, rd_rbv. destruct (0 <? br_rv res) eqn:E; [apply Z.ltb_lt in E| apply Z.ltb_ge in E]; clear - E; intros; lia. }
        unfold rd_conv, rd_rbv in *. replace (0 <? br_rv res) with true in * by (symmetry; apply Z.ltb_lt; clear - POS; lia). cbv iota in RBCp, RBV, RVR, CZ. cbv iota.
        step. if_false. step. if_cases K1; zify_cond K1; [kill K1|]. clear K1. step. if_lit.   (* [comment removed for export] *)
        st1. st1. zstep. rewrite ?unsigned_lit by (clear - POS NRR OUTL; lia).
        (* [comment removed for export] *)
        lazymatch type of FR' with rw_cells _ _ _ ?cs => let s2 := dj_size_cells cs in
          assert (DJf : chunk_disj (bv_unsigned sp + -80) s2 a 128) by (unfold chunk_disj; clear - BL1 LO32; lia) end.
        assert (DJtb : chunk_disj 3282240 64 a 128) by (unfold chunk_disj; unhide AI; clear - AI; lia).
        assert (DJtm : chunk_disj 3099984 64 a 128) by (unfold chunk_disj; unhide AI; clear - AI; lia).
        predj RBCp a 128. predj CTXp a 128. predj ECp a 128. predj MCp a 128. predj MBBp a 128. predj MBMp a 128. predj MRPp a 128. predj TXTp a 128.
        assert (DJo2 : chunk_disj out (Z.of_nat (cells_size [CB (length (br_out res)) (map b8 (br_out res)); CB (Z.to_nat outl - length (br_out res)) junk'])) a 128).
        { unfold chunk_disj. cbn [cells_size csize Nat.add]. unhide OA1. clear - OA1 ZLE OUTL. lia. }
        st1.
        (* [comment removed for export] *)
        step. st1. step. if_false. st1. step. if_true. zstep. step. if_false.
        step. if_cases K1; zify_cond K1; [kill K1|]. clear K1. step. if_lit.
        st1. step. if_cases K3; zify_cond K3; [| exfalso; revert K3; rewrite ?unsigned_lit by (clear - POS OUTL; lia); clear - POS; intros; lia]. clear K3.
        zstep.
        do 9 st1. step. step. release_frame FR' ST (bv_unsigned sp).
        try match goal with |- context [Z_to_bv 64 (bv_swrap 32 ?e)] => change (bv_swrap 32 e) with 1 end.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) => fin_b64 mf fl rt c fl' nr' d' hdr cjunk junk' end.
        split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
        split; [bio_unf_goal; rewrite ?Z.add_0_r; exact BCp|]. split; [exact FLp|]. split; [exact RTp|]. split; [exact LH|]. split; [exact LJ'|].
        split; [unfold b64ctx_used_cells, wz; exact CTXp|]. split; [exact CONT|]. split; [exact CR|]. split; [exact CZ|].
        split; [exact RVR|]. split; [unfold zlength; exact ZLE|].
        split. { exists raw2, line2. split; [exact RAWL2|]. split; [exact RAWP2|]. split; [exact ECp|]. split; [exact LINE2|]. split; [exact I3|]. split; [exact RB3| exact DINV2]. }
        split. { split; [bio_unf_goal; exact MCp|]. split; [unfold wz; cbn [mb_bb mb_bm mb_rp mset]; exact MBBp|].
                 split; [unfold buf_cells, wz; cbn [bm_len bm_data bm_max bm_flags mb_bb mb_bm mb_rp mb_buf mb_len mb_pos mset]; exact MBMp|].
                 split; [unfold buf_cells, wz; cbn [bm_len bm_data bm_max bm_flags mb_bb mb_bm mb_rp mb_buf mb_len mb_pos mset]; exact MRPp|]. exact MBpure. }
        split; [exact TXTp|]. split; [exact OUTp|].
        split; [unfold METH_b64, O_METH_BREAD, A_b64_method, wz; cbn; exact METHB1|]. split; [unfold METH_mem, O_METH_BREAD, A_mem_buf_method, wz; cbn; exact METHM1|].
        split; [exact RBCp| exact RBV].
  Qed.

  (* [comment removed for export] *)
  Theorem bioread_b64_spec : bioread_b64_stmt.
  Proof.
    unfold bioread_b64_stmt. intros until junk. intros A0 A1 A2 OUTL BF BAP NXT BEL ENC MB POS0 MBL MSEP TXT TLEN TLE OUTC MO OUTMB APO APM APT METHB METHM TAB SPAL OUTLT ST CEIL LO MI RAE.
    subst a0 a1 a2.
    unfold P_BIO_read in *. hcb.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (LOSr : lo <= bv_unsigned sp + -32 - READINTERN_B64_STACK).
    { revert LO. unfold BIOREAD_B64_STACK, READINTERN_B64_STACK, BREADCONV_B64_STACK, FR_BIO_read, FR_bio_read_intern, FR_bread_conv. clear. intros; lia. }
    assert (LO32 : lo <= bv_unsigned sp + -32).
    { revert LOSr. unfold READINTERN_B64_STACK, BREADCONV_B64_STACK, BIOCTRL_B64_STACK, B64CTRL_STACK, BIOCTRL_STACK, MEMCTRL_STACK, FR_bio_read_intern, FR_bread_conv, FR_BIO_ctrl, FR_b64_ctrl, FR_mem_ctrl. clear. intros; lia. }
    assert (LO32x : True).
    { revert LOSr. unfold B64READ_STACK, BIOREAD_STACK, READINTERN_STACK, BREADCONV_STACK, BIOEOF_STACK, MEMREAD_STACK, BIOCTRL_STACK, MEMCTRL_STACK, DECUPDATE_STACK,
        DECFINAL_STACK, DECBLOCK_STACK, DECINIT_STACK, FR_b64_read, FR_BIO_read, FR_bio_read_intern, FR_bread_conv, FR_BIO_eof, FR_mem_read, FR_BIO_ctrl, FR_mem_ctrl,
        FR_EVP_DecodeUpdate, FR_EVP_DecodeFinal, FR_evp_decodeblock_int, FR_EVP_DecodeInit, BIOACC_STACK, FR_BIO_set_data. clear. intros; lia. }
    clear LO.
    pose proof BF as (BC & (bjunk & LJ & BX) & BLK & NONL & RT0 & NR0).
    pose proof BLK as (I1 & I2 & I3 & RB1 & RB2 & RB3 & FLR & RTR & NRR & NXR & PVR).
    pose proof RB1 as (AP & AAL & _ & AH & AI). pose proof RB2 as (CP & _ & _ & CH & CI). pose proof RB3 as (EP & _ & _ & EH & EI).
    pose proof BEL as (BL1 & BL2 & BL3). pose proof BAP as (BA1 & BA2 & BA3).
    pose proof MO as (OUTR & OUTP & OUTH & OUTF & OUTB & OUTM).
    pose proof MB as MBc.
    destruct MBc as (MC & MBB & MBM & MRP & J1 & J2 & J3 & J4 & RM1 & RM2 & RM3 & RM4 & POSR & LENR & BUFP & BUFH & MFL & RDO & AEOF & NUMR & NRD & NRD2 & MNX & MPV).
    pose proof RM1 as (MP & _ & _ & MH & MI0). pose proof RM3 as (_ & _ & _ & _ & BMI). pose proof MBL as (ML1 & ML2 & ML3 & ML4).
    pose proof (Forall_inv APO) as OA1. pose proof (Forall_inv (Forall_inv_tail APO)) as OA2. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail APO))) as OA3.
    cbn [blk_addr blk_size fst snd] in OA1, OA2, OA3.
    pose proof (Forall_inv APM) as APM1. pose proof (Forall_inv APM1) as DJ_a_mb. pose proof (Forall_inv (Forall_inv_tail APM1)) as DJ_a_bb.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail APM1))) as DJ_a_bm. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail APM1)))) as DJ_a_rp.
    cbn [blk_addr blk_size fst snd] in DJ_a_mb, DJ_a_bb, DJ_a_bm, DJ_a_rp. clear APM1.
    pose proof (Forall_inv (Forall_inv_tail APM)) as APM2. pose proof (Forall_inv APM2) as DJ_c_mb. pose proof (Forall_inv (Forall_inv_tail APM2)) as DJ_c_bb.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail APM2))) as DJ_c_bm. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail APM2)))) as DJ_c_rp.
    cbn [blk_addr blk_size fst snd] in DJ_c_mb, DJ_c_bb, DJ_c_bm, DJ_c_rp. clear APM2.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail APM))) as APM3. pose proof (Forall_inv APM3) as DJ_e_mb. pose proof (Forall_inv (Forall_inv_tail APM3)) as DJ_e_bb.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail APM3))) as DJ_e_bm. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail APM3)))) as DJ_e_rp.
    cbn [blk_addr blk_size fst snd] in DJ_e_mb, DJ_e_bb, DJ_e_bm, DJ_e_rp. clear APM3.
    pose proof (Forall_inv APT) as PT1. pose proof (Forall_inv (Forall_inv_tail APT)) as PT2. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail APT))) as PT3.
    cbn [blk_addr blk_size fst snd] in PT1, PT2, PT3.
    pose proof (Forall_inv OUTF) as OF1. pose proof (Forall_inv (Forall_inv_tail OUTF)) as OF2.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail OUTF))) as OF3. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail OUTF)))) as OF4.
    cbn [blk_addr blk_size fst snd] in OF1, OF2, OF3, OF4.
    pose proof MSEP as ((SP1 & SP2 & SP3 & SP4 & SP5 & SP6) & PS1 & PS2 & PS3 & PS4).
    unfold BIO_SIZE, B64CTX_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE, ENCCTX_SIZE in BL1, BL2, BL3, BA1, BA2, BA3, ML1, ML2, ML3, ML4, AH, CH, EH, MH, OA1, OA2, OA3,
      DJ_a_mb, DJ_a_bb, DJ_a_bm, DJ_a_rp, DJ_c_mb, DJ_c_bb, DJ_c_bm, DJ_c_rp, DJ_e_mb, DJ_e_bb, DJ_e_bm, DJ_e_rp, PT1, PT2, PT3, AI, CI, EI, MI0, BMI,
      OF1, OF2, OF3, OF4, SP1, SP2, SP3, SP4, SP5, SP6, PS1, PS2, PS3, PS4.
    unfold A_mem_buf_method, O_METH_BREAD in OUTM. unfold A_b64_method, O_METH_BREAD in OUTMB.
    pose proof (rw_cells_bound _ _ _ _ OUTC) as OB. cbn [cells_size csize Nat.add] in OB.
    pose proof (munch_refl ((lo, bv_unsigned sp) :: (out, out + outl) :: B64F_foot a R ++ MEMBIO_foot mb M) m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold B64F_foot, MEMBIO_foot, BIO_SIZE, B64CTX_SIZE, BUFMEM_SIZE in MU. cbn [app] in MU.
    bio_unf BC. rewrite NXT, RT0, NR0 in BC. unfold b64ctx_fresh_cells, wz in BX.
    bio_unf MC. rewrite NUMR in MC. unfold buf_cells, wz in MBM, MRP. cbn [bm_len bm_data bm_max bm_flags] in MBM, MRP. unfold wz in MBB.
    pose proof METHB as METHB0. unfold METH_b64, O_METH_BREAD, A_b64_method, wz in METHB. norm_addr METHB.
    pose proof METHM as METHM0. unfold METH_mem, O_METH_BREAD, A_mem_buf_method, wz in METHM. norm_addr METHM.
    destruct ENC as (raw & line & RAWL & RAWP & EC & LINE & _ & _ & DINV).
    unfold zlength in TLEN, TLE.
    hide_ors.
    carve_frame 32%nat ST.
    (* [comment removed for export] *)
    destruct (rw_cells_CB_split _ _ _ _ 16 _ FR ltac:(clear; lia)) as [FRlo FRhi]. clear FR.
    destruct (rw_cells_CB_split _ _ _ _ 8 _ FRlo ltac:(clear; lia)) as [FR0 FRrb]. clear FRlo.
    cbn [Nat.sub Z.of_nat Pos.of_succ_nat Pos.succ] in FRhi, FR0, FRrb.
    replace (bv_unsigned sp + -32 + 16) with (bv_unsigned sp + -16) in FRhi by (clear; lia).
    replace (bv_unsigned sp + -32 + 8) with (bv_unsigned sp + -24) in FRrb by (clear; lia).
    apply (rw_cells_CB8_C8 _ _ _ [] _ []) in FRrb. cbn [app] in FRrb.
    set (rbv := bytes_le_to_Z (skipn 8 (firstn 16 junk0))) in FRrb.
    unhide OUTR. st1. st1. st1. hide OUTR. step. step. if_cases K0; zify_cond K0; [kill K0|]. clear K0. step. unfold P_bio_read_intern. step.
    (* [comment removed for export] *)
    eapply evt_cut.
    { eapply readintern_b64_spec with (lo := lo) (R := R) (LB := LB) (M := M) (junk := junk) (txt := txt) (mb := mb) (a := a) (out := out) (outl := outl)
                                      (rbp := bv_unsigned sp + -24) (rbv := rbv);
        rewrite ?unsigned_lit by (clear - SPR LO32 LO0; lia); try reflexivity.
      all: try lazymatch goal with
           | |- B64F_fresh _ _ _ _ => split; [bio_unf_goal; rewrite NXT, RT0, NR0; exact BC|]; split; [exists bjunk; split; [exact LJ| unfold b64ctx_fresh_cells, wz; exact BX]|];
                                      exact (conj BLK (conj NONL (conj RT0 NR0)))
           | |- B64F_apart _ _ => exact BAP
           | |- bf_next _ = _ => exact NXT
           | |- 0 < _ < _ => exact OUTL
           | |- B64F_below _ _ _ => exact BEL
           | |- ENCCTX _ _ _ _ _ => exists raw, line; split; [exact RAWL|]; split; [exact RAWP|]; split; [exact EC|]; split; [exact LINE|]; split; [exact I3|]; split; [exact RB3| exact DINV]
           | |- MEMBIO _ _ _ _ => unhide MI0; membio_tac; try (bio_unf_goal; rewrite ?NUMR, ?Z.add_0_r; assumption)
           | |- mb_pos _ = 0 => exact POS0
           | |- MEMBIO_below _ _ _ => exact MBL
           | |- MEMBIO_sep _ _ => exact MSEP
           | |- bytes_at _ _ _ _ => exact TXT
           | |- Z.of_nat (length _) = _ => exact TLEN
           | |- zlength _ = _ => exact TLEN
           | |- Z.of_nat (length _) <= _ => exact TLE
           | |- zlength _ <= _ => exact TLE
           | |- rw_cells _ _ _ [CB _ _] => exact OUTC
           | |- rw_cells _ _ _ [C8 _] => unfold wz; exact FRrb
           | |- memrd_out _ _ _ 8 _ _ => unfold memrd_out, blocks_MEMBIO, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE, A_mem_buf_method, O_METH_BREAD;
                 split; [clear - SPR; lia|]; split; [clear - SPR LO32 LO0; lia|]; split; [clear - SPR; lia|];
                 split; [apply Forall_cons; [cbn [blk_addr blk_size fst snd]; clear - ML1 LO32; lia|]; apply Forall_cons; [cbn [blk_addr blk_size fst snd]; clear - ML2 LO32; lia|];
                         apply Forall_cons; [cbn [blk_addr blk_size fst snd]; clear - ML3 LO32; lia|]; apply Forall_cons; [cbn [blk_addr blk_size fst snd]; clear - ML4 LO32; lia| apply Forall_nil]|];
                 split; [clear - BUFH CEIL LO32; lia| clear - CEIL HCEILB LO32; lia]
           | |- memrd_out _ _ _ _ _ _ => unfold memrd_out; unhide OUTR; unhide OUTB; unhide OUTM; split; [clear - OUTR; lia|]; split; [exact OUTP|]; split; [exact OUTH|]; split; [exact OUTF|]; split; [exact OUTB|]; unfold A_mem_buf_method, O_METH_BREAD; clear - OUTM; lia
           | |- _ + 8 <= A_b64_method + _ \/ _ => unfold A_b64_method, O_METH_BREAD; clear - CEIL HCEILB LO32; lia
           | |- _ + _ <= A_b64_method + _ \/ _ => exact OUTMB
           | |- Forall _ (blocks_B64F _ _) => first [exact APO | exact APT | exact APM | (unfold blocks_B64F, BIO_SIZE, B64CTX_SIZE;
                    apply Forall_cons; [cbn [blk_addr blk_size fst snd]; clear - BL1 LO32; lia|]; apply Forall_cons; [cbn [blk_addr blk_size fst snd]; clear - BL2 LO32; lia|];
                    apply Forall_cons; [cbn [blk_addr blk_size fst snd]; clear - BL3 LO32; lia| apply Forall_nil])]
           | |- Forall _ _ => first [exact APO | exact APM | exact APT]
           | |- _ + 8 <= _ \/ _ => unhide OUTR; clear - OUTR LO32; lia
           | |- METH_b64 _ => unfold METH_b64, O_METH_BREAD, A_b64_method, wz; cbn; exact METHB
           | |- METH_mem _ => unfold METH_mem, O_METH_BREAD, A_mem_buf_method, wz; cbn; exact METHM
           | |- stk _ _ _ _ => exact ST
           | |- hceil <= _ => exact CEIL
           | |- _ <= _ - READINTERN_B64_STACK => exact LOSr
           | |- mem_inv _ _ => assumption
           | |- _ mod 8 = 0 => clear - SPAL SPR LO32; lia
           | |- _ mod 16 = 0 => clear - SPAL SPR LO32; lia
           | |- _ + _ < 2 ^ 64 => exact OUTLT
           | |- _ mod 2 = 0 => reflexivity
           | |- _ => idtac
           end.
      all: match goal with |- ?G => idtac "CALL-LEFT:" G end. }
    cbv beta. intros ms' PO. unfold b64rd_post in PO.
    destruct PO as (p0 & p1 & p2 & q1 & q2 & q3 & q4 & q5 & q6 & q7 & p3 & p4 & p5 & p6 & m' & fl & rt & c & fl' & nr' & d' & hdr & cjunk & junk'
                    & -> & MUc & WMc & MIc & STc & BCp & FLp & RTp & LH & LJ' & CTXp & CONT & CR & CZ & RVR & ZLE & ENCp & MBp & TXTp & OUTp & METHBp & METHMp & RBCp & RBV).
    rewrite ?unsigned_lit in MUc by (clear - SPR LO32 LO0; lia). rewrite ?unsigned_lit in STc by (clear - SPR LO32 LO0; lia).
    set (res := b64_read_spec (map bv_unsigned txt) outl) in *.
    replace (ret_pc (Z_to_bv 64 1093384)) with (Z_to_bv 64 1093384) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    unfold B64F_foot, MEMBIO_foot, BIO_SIZE, B64CTX_SIZE, BUFMEM_SIZE in MUc. cbn [app] in MUc.
    assert (FRhi' : rw_cells usegs m' (bv_unsigned sp + -16) [C8 s0; C8 ra]).
    { eapply rw_cells_transport; [exact FRhi| exact MUc| exact WMc|]. cbn. unhide OUTR. clear - OUTR BL1 BL2 BL3 ML1 ML3 SPR LO32. lia. }
    lazymatch type of FR0 with rw_cells _ _ _ ?cs => assert (FR0' : rw_cells usegs m' (bv_unsigned sp + -32) cs) end.
    { eapply rw_cells_transport; [exact FR0| exact MUc| exact WMc|]. cbn. unhide OUTR. clear - OUTR BL1 BL2 BL3 ML1 ML3 SPR LO32. lia. }
    clear FR0 FRhi FRrb BC BX EC MC MBB MBM MRP TXT OUTC METHB METHM ST MI.
    assert (MUf : munch ((lo, bv_unsigned sp) :: (out, out + outl) :: B64F_foot a R ++ MEMBIO_foot mb M) m m').
    { lazymatch type of MU with munch _ _ ?mq => apply (munch_trans _ m mq m' MU) end. eapply munch_weaken; [| exact MUc]. clear - LO32.
      unfold sub_fp, B64F_foot, MEMBIO_foot, BIO_SIZE, B64CTX_SIZE, BUFMEM_SIZE; cbn [outside app]. intros x Hx. lia. }
    pose proof (wmono_trans _ _ _ _ WM WMc) as WMf. clear MU WM MUc WMc. rename STc into ST. rename MIc into MI.
    unfold wz in RBCp.
    (* [comment removed for export] *)
    assert (RVc : rd_conv (br_rv res) = (if 0 <? br_rv res then 1 else br_rv res)) by reflexivity.
    assert (RBc : rd_rbv (br_rv res) = (if 0 <? br_rv res then br_rv res else 0)) by reflexivity.
    destruct (0 <? br_rv res) eqn:KP; [apply Z.ltb_lt in KP| apply Z.ltb_ge in KP]; rewrite RVc, RBc in *; clear RVc RBc.
    - apply (rw_cells_C8_C4C4 _ _ _ [] _ []) in RBCp; [| clear - RBV OUTL; lia]. cbn [app] in RBCp.
      step. if_false.
      st1. rewrite ?sx32_wz by (clear - RBV OUTL KP; lia). step. st1. st1. step. step.
      release_frame FR0' ST (bv_unsigned sp + -24). release_frame RBCp ST (bv_unsigned sp + -16). release_frame FRhi' ST (bv_unsigned sp).
      apply evt_done. unfold bioread_b64_post. cbv zeta.
      eexists p0, p1, p2, q1, q2, q3, q4, q5, q6, q7, p3, p4, p5, p6, m', (bf_with_hdr R fl rt (bf_nread R + br_rv res) mb (bf_prev R)), d', (mset M (Z.of_nat (br_used res)) fl' nr'), junk'.
      split; [reflexivity|]. split; [exact MUf|]. split; [exact WMf|]. split; [exact MI|]. split; [exact ST|].
      split. { split; [exact BCp|]. split; [exists hdr, cjunk, 0; split; [exact LH|]; split; [exact LJ'|]; split; [clear; lia| exact CTXp]|].
               unfold B64F_blocks; cbn [bf_flags bf_retry bf_nread bf_next bf_prev bf_ctx bf_enc bf_id bf_cid bf_eid bf_with_hdr].
               split; [exact I1|]; split; [exact I2|]; split; [exact I3|]; split; [exact RB1|]; split; [exact RB2|]; split; [exact RB3|]; split; [exact FLp|]; split; [exact RTp|];
               split; [rewrite NR0; clear - RBV OUTL; lia|]; split; [clear - MP MH HCEILB; lia| exact PVR]. }
      split; [reflexivity|]. split; [reflexivity|]. split; [exact ENCp|].
      split; [exact MBp|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].   (* [comment removed for export] *)
      split; [exact TXTp|]. exact OUTp.
    - (* [comment removed for export] *)
      step. if_cases K1; zify_cond K1.
      2:{ exfalso. assert (E : br_rv res = 0 \/ br_rv res = -1) by (clear - KP RVR; lia).
          destruct E as [E|E]; rewrite E in *;
          repeat match goal with H : context [Z.modulo ?x ?y] |- _ => let v := eval vm_compute in (Z.modulo x y) in change (Z.modulo x y) with v in H end; lia. }
      try clear K1.
      st1. st1. step. step.
      release_frame FR0' ST (bv_unsigned sp + -24). release_frame RBCp ST (bv_unsigned sp + -16). release_frame FRhi' ST (bv_unsigned sp).
      apply evt_done. unfold bioread_b64_post. cbv zeta.
      eexists p0, p1, p2, q1, q2, q3, q4, q5, q6, q7, p3, p4, p5, p6, m', (bf_with_hdr R fl rt (bf_nread R + 0) mb (bf_prev R)), d', (mset M (Z.of_nat (br_used res)) fl' nr'), junk'.
      split; [reflexivity|]. split; [exact MUf|]. split; [exact WMf|]. split; [exact MI|]. split; [exact ST|].
      split. { split; [exact BCp|]. split; [exists hdr, cjunk, 0; split; [exact LH|]; split; [exact LJ'|]; split; [clear; lia| exact CTXp]|].
               unfold B64F_blocks; cbn [bf_flags bf_retry bf_nread bf_next bf_prev bf_ctx bf_enc bf_id bf_cid bf_eid bf_with_hdr].
               split; [exact I1|]; split; [exact I2|]; split; [exact I3|]; split; [exact RB1|]; split; [exact RB2|]; split; [exact RB3|]; split; [exact FLp|]; split; [exact RTp|];
               split; [rewrite NR0; clear - RBV OUTL; lia|]; split; [clear - MP MH HCEILB; lia| exact PVR]. }
      split; [reflexivity|]. split; [reflexivity|]. split; [exact ENCp|].
      split; [exact MBp|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].   (* [comment removed for export] *)
      split; [exact TXTp|]. exact OUTp.
  Qed.
End S.
