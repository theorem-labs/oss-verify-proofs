(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface F_memcpy ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Rep ECH_LibState
     ECH_C1_stmt ECH_C3_stmt ECH_C6_stmt ECH_C6_acc ECH_C7_stmt ECH_C7_read.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma zx32_lit : forall x, 0 <= x < 2^32 -> zx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof. intros x Hx. unfold zx32. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma bio_flags_byte : forall m a B, rw_cells rsegs m a (bio_cells B) ->
  ov_read_bytes rsegs m (wa (a + 48)) 1 = Some [b8 (bio_flags B mod 256)].
Proof.
  intros m a B [[_ HB] _].
  rewrite (bytes_at_ov_read rsegs m a (cells_bytes (bio_cells B)) 48 1 HB) by (cbn; lia).
  cbn. f_equal. f_equal. unfold b8. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 8) with 256. change (2 ^ Z.of_N 64) with (256 * 2^56).
  rewrite Z.rem_mul_r by lia. rewrite (Z.mul_comm 256), Z.mod_add, Z.mod_mod by lia. reflexivity.
Qed.
Lemma land_mod256_128 : forall f, 0 <= f -> Z.land (f mod 256) 128 = Z.land f 128.
Proof.
  intros f Hf. change 256 with (2^8). rewrite <- Z.land_ones by lia. rewrite <- Z.land_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma lxor_top : forall n, 0 <= n < 2^63 -> Z.lxor n 9223372036854775808 = n + 9223372036854775808.
Proof.
  intros n Hn. symmetry. apply Z.add_nocarry_lxor. apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.eq_dec k 63) as [->|NE].
  - rewrite (Z.bits_above_log2 n 63); [reflexivity| lia|].
    destruct (Z.eq_dec n 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia.
  - replace (Z.testbit 9223372036854775808 k) with false; [apply Bool.andb_false_r|].
    symmetry. change 9223372036854775808 with (2^63). rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_neq. lia.
Qed.
Lemma sgtz_mask : forall n, 0 < n < 2^63 ->
  Z.land ((0 + - Z.b2z (9223372036854775808 <? Z.lxor n 9223372036854775808)) mod 18446744073709551616) n = n.
Proof.
  intros n Hn. rewrite lxor_top by lia.
  replace (9223372036854775808 <? n + 9223372036854775808) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
  change ((0 + - (1)) mod 18446744073709551616) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.
  (* [comment removed for export] *)
  Lemma memctrl_body : forall (cmd : Z), (cmd = BIO_CTRL_EOF \/ cmd = BIO_CTRL_PUSH) ->
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list block) (a larg parg lo : Z) (R : membio),
      a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 cmd -> a2 = Z_to_bv 64 larg -> a3 = Z_to_bv 64 parg ->
      0 <= larg < 2^63 -> 0 <= parg < 2^64 ->
      MEMBIO LB m a R -> MEMBIO_below a R lo ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 64 -> mem_inv rsegs m -> bv_unsigned ra mod 2 = 0 ->
      evt rsegs (memctrl_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB (mem_ctrl_rv R cmd) a R lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_mem_ctrl) fc None m (seg_rom rsegs)).
  Proof.
    intros cmd CMD. intros until R. intros A0 A1 A2 A3 LR PR MB BL ST CEIL LO MI RAE. subst a0 a1 a2 a3.
    unfold P_mem_ctrl, mem_ctrl_rv, mb_avail in *.
    pose proof MB as MB0.
    destruct MB0 as (BC & BBC & BMC & RPC & I1 & I2 & I3 & I4 & RB1 & RB2 & RB3 & RB4 & POSR & LENR & BUFP & BUFH & FLR & RDO & AEOF & NUMR & NRD & NRD2 & NXT & PRV).
    pose proof RB1 as (AP & _ & _ & AH & _). pose proof RB2 as (BBP & _ & _ & BBH & _). pose proof RB3 as (BMP & _ & _ & BMH & _). pose proof RB4 as (RPP & _ & _ & RPH & _).
    destruct BL as (BL1 & BL2 & BL3 & BL4). unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE, BIO_FLAGS_MEM_RDONLY, BIO_CTRL_EOF, BIO_CTRL_PUSH in *.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption). hcb.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    unfold bio_cells, membio_bio, wz in BC. cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite] in BC.
    unfold A_mem_buf_method in BC.
    unfold wz in BBC. unfold buf_cells, wz in BMC, RPC. cbn [bm_len bm_data bm_max bm_flags] in BMC, RPC.
    carve_frame 64%nat ST.
    do 9 st1. step. step. step.
    st1. rewrite zx32_lit by lia. st1. zstep. rewrite ?(unsigned_lit (mb_flags R)) by lia. rewrite RDO. zstep. change (Z.b2z (512 <? 1)) with 0. zstep. zstep. st1. st1. st1.
    destruct CMD as [-> | ->].
    - (* [comment removed for export] *)
      step. step. if_false. zstep. step. step. if_false. zstep. step. step. zstep. st1. zstep. step.
      change (2 =? 2) with true. cbv iota.
      (* [comment removed for export] *)
      assert (FIN : forall a1v a2v : word,
        evt rsegs (memctrl_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB (if mb_len R - mb_pos R =? 0 then 1 else 0) a R lo m)
          (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 sp s1
                   (Z_to_bv 64 (mb_len R - mb_pos R)) a1v a2v (Z_to_bv 64 512)
                   (Z_to_bv 64 394368) (Z_to_bv 64 (mb_buf R + mb_pos R)) (Z_to_bv 64 113) a7 (Z_to_bv 64 larg) (Z_to_bv 64 a)
                   (Z_to_bv 64 parg) (Z_to_bv 64 (mb_bb R)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x1d5c38) fc None m0 (seg_rom rsegs))).
      { intros a1v a2v. zstep.
        replace (Z.b2z (mb_len R - mb_pos R <? 1)) with (if mb_len R - mb_pos R =? 0 then 1 else 0)
          by (unfold Z.b2z; destruct (Z.ltb_spec (mb_len R - mb_pos R) 1); destruct (Z.eqb_spec (mb_len R - mb_pos R) 0); lia).
        step. step. do 7 st1. step. step.
        release_frame FR ST (bv_unsigned sp). finish. membio_tac. }
      cbv delta [mkR] in FIN.
      zstep. step. if_cases K2; zify_cond K2.
      + apply FIN.
      + st1. rewrite NUMR. step. if_cases K3; zify_cond K3; [| kill K3]. apply FIN.
    - (* [comment removed for export] *)
      step. step. if_false. zstep. step. step. if_false. zstep. step. step. zstep. st1. zstep. step.
      change (6 =? 2) with false. cbv iota.
      step. step. step. do 7 st1. step. step.
      release_frame FR ST (bv_unsigned sp). finish. membio_tac.
  Qed.

  Lemma memctrl_spec : memctrl_stmt.
  Proof.
    unfold memctrl_stmt, memctrl_stmt_at. intros until R. intros A0 A1 A2 A3 CMD LR PR MB BL SEP NM ST CEIL LO MI RAE.
    eapply memctrl_body; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma bioctrl_mem_spec : bioctrl_mem_stmt.
  Proof.
    unfold bioctrl_mem_stmt, memctrl_stmt_at. intros until R. intros A0 A1 A2 A3 CMD LR PR MB BL SEP METH ST CEIL LO MI RAE. subst a0 a1 a2 a3.
    specialize (METH eq_refl). unfold P_BIO_ctrl, BIOCTRL_STACK, MEMCTRL_STACK, FR_BIO_ctrl, FR_mem_ctrl in *.
    pose proof MB as MB0.
    destruct MB0 as (BC & BBC & BMC & RPC & I1 & I2 & I3 & I4 & RB1 & RB2 & RB3 & RB4 & POSR & LENR & BUFP & BUFH & FLR & RDO & AEOF & NUMR & NRD & NRD2 & NXT & PRV).
    pose proof RB1 as (AP & _ & _ & AH & _).
    destruct BL as (BL1 & BL2 & BL3 & BL4). unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in *.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption). hcb.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    unfold bio_cells, membio_bio, wz in BC. cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite] in BC.
    unfold A_mem_buf_method in BC. unfold METH_mem, O_METH_BREAD, A_mem_buf_method, wz in METH. norm_addr METH.
    unfold wz in BBC. unfold buf_cells, wz in BMC, RPC. cbn [bm_len bm_data bm_max bm_flags] in BMC, RPC.
    carve_frame 48%nat ST.
    do 7 st1. step. step. if_cases K0; zify_cond K0; [kill K0|]. clear K0.
    step. st1. step. if_false. st1. step. if_false. step. step. step. st1. st1.
    step. if_true. step. if_true. step. step. step. step. unfold P_mem_ctrl. step.
    eapply evt_cut.
    { eapply (memctrl_body cmd CMD) with (lo := lo) (R := R) (LB := LB); [reflexivity| reflexivity| reflexivity| reflexivity| exact LR| exact PR| membio_tac| | rewrite unsigned_lit by lia; exact ST| exact CEIL| rewrite unsigned_lit by lia; lia| assumption| rewrite unsigned_lit by lia; reflexivity].
      unfold MEMBIO_below, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE. lia. }
    unfold memctrl_post, BIO_SIZE. landx MU WM.
    st1. step. step. if_false. st1. step. if_true. step. do 6 st1. step. step.
    release_frame FR ST (bv_unsigned sp). finish.
  Qed.

  (* [comment removed for export] *)
  Lemma bioeof_mem_spec : bioeof_mem_stmt.
  Proof.
    unfold bioeof_mem_stmt. intros until R. intros A0 MB BL SEP METH ST CEIL LO MI RAE. subst a0.
    unfold P_BIO_eof, BIOEOF_STACK, BIOCTRL_STACK, MEMCTRL_STACK, FR_BIO_eof, FR_BIO_ctrl, FR_mem_ctrl in *.
    pose proof MB as MB0.
    destruct MB0 as (BC & BBC & BMC & RPC & I1 & I2 & I3 & I4 & RB1 & RB2 & RB3 & RB4 & POSR & LENR & BUFP & BUFH & FLR & RDO & AEOF & NUMR & NRD & NRD2 & NXT & PRV).
    pose proof RB1 as (AP & _ & _ & AH & _).
    pose proof BL as (BL1 & BL2 & BL3 & BL4). unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in BL1, BL2, BL3, BL4, AH.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption). hcb.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    unfold bio_cells, membio_bio, wz in BC. cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite] in BC.
    unfold A_mem_buf_method in BC.
    unfold wz in BBC. unfold buf_cells, wz in BMC, RPC. cbn [bm_len bm_data bm_max bm_flags] in BMC, RPC.
    unfold METH_mem, O_METH_BREAD, A_mem_buf_method, wz in METH. norm_addr METH.
    pose proof (bio_flags_byte _ _ _ (proj1 MB)) as RD. cbn [bio_flags membio_bio] in RD. st1. clear RD.
    zstep. rewrite wz_unsigned by lia. rewrite land_mod256_128, AEOF by lia. step. if_false.
    carve_frame 16%nat ST. do 3 st1. step. step. step. step. unfold P_BIO_ctrl. step.
    pose proof bioctrl_mem_spec as BCS. unfold bioctrl_mem_stmt, memctrl_stmt_at, BIOCTRL_STACK, MEMCTRL_STACK, FR_BIO_ctrl, FR_mem_ctrl, P_BIO_ctrl in BCS.
    eapply evt_cut.
    { eapply BCS with (lo := lo) (R := R) (LB := LB) (cmd := BIO_CTRL_EOF); clear BCS;
        [reflexivity| reflexivity| reflexivity| reflexivity| left; reflexivity| lia| lia| membio_tac| exact BL| exact SEP| intros _; exact METH
        | rewrite unsigned_lit by lia; exact ST| exact CEIL| rewrite unsigned_lit by lia; lia| assumption| rewrite unsigned_lit by lia; reflexivity]. }
    clear BCS. unfold memctrl_post, BIO_SIZE. landx MU WM.
    assert (RV : 0 <= mem_ctrl_rv R BIO_CTRL_EOF <= 1) by (unfold mem_ctrl_rv; destruct (BIO_CTRL_EOF =? BIO_CTRL_EOF); [destruct (mb_avail R =? 0)|]; lia).
    st1. st1. step. step. zstep. rewrite swrap32_small by lia. step.
    release_frame FR ST (bv_unsigned sp). finish.
  Qed.

  (* [comment removed for export] *)
  Lemma land_clr7_id : forall x, 0 <= x < 2^31 -> Z.land x 128 = 0 -> Z.land x 18446744073709551487 = x.
  Proof.
    intros x Hx H7. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec.
    destruct (Z.eq_dec n 7) as [->|NE].
    - apply (f_equal (fun z => Z.testbit z 7)) in H7. rewrite Z.land_spec, Z.bits_0 in H7. change (Z.testbit 128 7) with true in H7.
      rewrite Bool.andb_true_r in H7. rewrite H7. reflexivity.
    - destruct (Z.lt_ge_cases n 64) as [L|L].
      + replace (Z.testbit 18446744073709551487 n) with true; [apply Bool.andb_true_r|].
        symmetry. change 18446744073709551487 with (Z.lor (Z.ones 7) (Z.shiftl (Z.ones 56) 8)).
        rewrite Z.lor_spec. destruct (Z.lt_ge_cases n 7) as [L7|L7].
        * rewrite Z.ones_spec_low by lia. reflexivity.
        * rewrite Z.shiftl_spec, (Z.ones_spec_low 56) by lia. apply Bool.orb_true_r.
      + assert (LG : Z.log2 x <= 30) by (change 30 with (Z.log2 2147483647); apply Z.log2_le_mono; lia).
        rewrite (Z.bits_above_log2 x n) by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Definition BR_RA1 : Z := 0x100904.   (* [comment removed for export] *)
  Definition BR_RA2 : Z := 0x100954.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma br_clamp :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (outl : Z),
      0 < outl < 2^31 ->
      evt rsegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 2147483647) a1 (Z_to_bv 64 outl) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                      F (Z_to_bv 64 0x1008f4) fc None m (seg_rom rsegs))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 2147483647) a1 (Z_to_bv 64 outl) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x1008ec) fc None m (seg_rom rsegs)).
  Proof.
    intros until outl. intros OUTL.
    step. if_cases K1; zify_cond K1.
    - apply evt_done. reflexivity.
    - step. apply evt_done. do 2 f_equal. f_equal. lia.
  Qed.

  Lemma breadconv_mem_spec : breadconv_mem_stmt.
  Proof.
    unfold breadconv_mem_stmt. intros until junk; intros A0 A1 A2 A3 OUTL MB BL SEP METH BS LEN OUTC MO RBC MORB RBO ST CEIL LO MI RAE. subst a0 a1 a2 a3.
    unfold P_bread_conv, BREADCONV_STACK, MEMREAD_STACK, BIOCTRL_STACK, MEMCTRL_STACK, FR_bread_conv, FR_mem_read, FR_BIO_ctrl, FR_mem_ctrl, BIOACC_STACK, FR_BIO_set_data in *.
    pose proof MB as MB0.
    destruct MB0 as (BC & BBC & BMC & RPC & I1 & I2 & I3 & I4 & RB1 & RB2 & RB3 & RB4 & POSR & LENR & BUFP & BUFH & FLR & RDO & AEOF & NUMR & NRD & NRD2 & NXT & PRV).
    pose proof RB1 as (AP & _ & _ & AH & RG1). pose proof RB2 as (BBP & _ & _ & BBH & _). pose proof RB3 as (BMP & _ & _ & BMH & RG3). pose proof RB4 as (RPP & _ & _ & RPH & _).
    hide RB1; hide RB2; hide RB3; hide RB4.
    pose proof BL as (BL1 & BL2 & BL3 & BL4). unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in BL1, BL2, BL3, BL4, AH, BBH, BMH, RPH, RG1, RG3. hide RG1; hide RG3.
    pose proof SEP as ((AP1 & AP2 & AP3 & AP4 & AP5 & AP6) & PS1 & PS2 & PS3 & PS4). unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in AP1, AP2, AP3, AP4, AP5, AP6, PS1, PS2, PS3, PS4.
    hide AP1; hide AP2; hide AP3; hide AP4; hide AP5; hide AP6; hide PS1; hide PS2; hide PS3; hide PS4.
    destruct MO as (OUTR & OUTP & OUTH & OUTF & OUTB & OUTM).
    pose proof (Forall_inv OUTF) as OF1. pose proof (Forall_inv (Forall_inv_tail OUTF)) as OF2.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail OUTF))) as OF3. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail OUTF)))) as OF4.
    clear OUTF. cbn [blk_addr blk_size fst snd] in OF1, OF2, OF3, OF4. unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in OF1, OF2, OF3, OF4.
    unfold A_mem_buf_method, O_METH_BREAD in OUTM. hide OF1; hide OF2; hide OF3; hide OF4; hide OUTR; hide OUTB; hide OUTM.
    destruct MORB as (RBR & RBP & RBH & RBF & RBB & RBM). unfold A_mem_buf_method, O_METH_BREAD in RBM.
    pose proof (Forall_inv RBF) as RF1. pose proof (Forall_inv (Forall_inv_tail RBF)) as RF2.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail RBF))) as RF3. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail RBF)))) as RF4.
    clear RBF. cbn [blk_addr blk_size fst snd] in RF1, RF2, RF3, RF4. unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in RF1, RF2, RF3, RF4.
    hide RF1; hide RF2; hide RF3; hide RF4; hide RBR; hide RBB; hide RBO; hide RBM.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption). hcb.
    pose proof (rw_cells_bound _ _ _ _ OUTC) as OB. cbn [cells_size csize Nat.add] in OB.
    pose proof (munch_refl ((lo, bv_unsigned sp) :: (out, out + outl) :: (rbp, rbp + 8) :: MEMBIO_foot a R) m) as MU. pose proof (wmono_refl rsegs m) as WM.
    unfold MEMBIO_foot, BIO_SIZE, BUFMEM_SIZE in MU.
    unfold bio_cells, membio_bio, wz in BC. cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite] in BC.
    unfold A_mem_buf_method in BC. unfold wz in BBC, RBC. unfold buf_cells, wz in BMC, RPC. cbn [bm_len bm_data bm_max bm_flags] in BMC, RPC.
    unfold METH_mem, O_METH_BREAD, A_mem_buf_method, wz in METH. norm_addr METH.
    unhide RBR; unhide OUTR. carve_frame 32%nat ST.
    do 5 st1. hide RBR; hide OUTR. step. step. step. if_cases K0; zify_cond K0; [kill K0|]. clear K0.
    step. step. zstep.
    eapply evt_cut. { eapply br_clamp. exact OUTL. } cbv beta. intros ms' ->.
    st1. st1. step. unfold P_mem_read. step.
    (* [comment removed for export] *)
    pose proof memread_spec as MRS. unfold memread_stmt, MEMREAD_STACK, FR_mem_read, BIOACC_STACK, FR_BIO_set_data, P_mem_read in MRS.
    eapply evt_cut.
    { eapply MRS with (lo := lo) (R := R) (LB := LB) (junk := junk); clear MRS;
        [reflexivity| reflexivity| reflexivity| exact OUTL| membio_tac| exact BL| exact SEP| exact BS| exact LEN| exact OUTC| 
        | rewrite unsigned_lit by lia; exact ST| exact CEIL| rewrite unsigned_lit by lia; lia| assumption| rewrite unsigned_lit by lia; reflexivity].
      unfold memrd_out. rewrite unsigned_lit by lia. unhide OUTR; unhide OUTB; unhide OF1; unhide OF2; unhide OF3; unhide OF4.
      unhide OUTM. split; [lia|]. split; [lia|]. split; [lia|]. split; [| unfold A_mem_buf_method, O_METH_BREAD; lia].
      unfold blocks_MEMBIO, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE. repeat (apply Forall_cons; [cbn [blk_addr blk_size fst snd]; lia|]). apply Forall_nil. }
    clear MRS. unfold memrd_post, MEMBIO_foot, BIO_SIZE, BUFMEM_SIZE.
    unhide OUTR; unhide RBR; unhide RBO; unhide RF1; unhide RF3; unhide OUTM; unhide RG1; unhide RG3. landx MU WM.
    hide OUTR; hide RBR; hide RBO; hide RF1; hide RF3; hide OUTM; hide RG1; hide RG3.
    replace (ret_pc (Z_to_bv 64 1050884)) with (Z_to_bv 64 1050884) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    match goal with H : MEMBIO LB _ a _ |- _ => destruct H as (BC1 & BBC1 & BMC1 & RPC1 & _) end.
    unfold bio_cells, membio_bio, buf_cells, mb_after_bread, wz, A_mem_buf_method, BIO_FLAGS_RETRY_MASK in BC1, BBC1, BMC1, RPC1.
    cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite bm_len bm_data bm_max bm_flags
         mb_buf mb_len mb_pos mb_flags mb_numf mb_nread mb_next mb_prev mb_bb mb_bm mb_rp] in BC1, BBC1, BMC1, RPC1.
    match goal with H : bytes_at rsegs _ (mb_buf _) ds |- _ => cbn [mb_buf mb_after_bread] in H; rename H into BS2 end.
    pose proof (clr_flags_facts (mb_flags R) FLR ltac:(unfold BIO_FLAGS_MEM_RDONLY in RDO; exact RDO) AEOF) as (FL1 & FL2 & FL3).
    step. st1. rewrite zx32_lit by lia. zstep. rewrite (Z.mod_small (Z.land (mb_flags R) (Z.lnot 15))) by lia. rewrite land_clr7_id by lia.
    change (Z_to_bv 64 (Z.land (mb_flags R) (Z.lnot 15))) with (wz (Z.land (mb_flags R) (Z.lnot 15))).
    assert (SL : length (mb_take R ds (mb_rdn R outl)) = Z.to_nat (mb_rdn R outl)).
    { unfold mb_take. rewrite firstn_length_le; [reflexivity|]. rewrite length_skipn. unfold mb_rdn, mb_avail in *. lia. }
    assert (NR : 0 <= mb_rdn R outl <= outl /\ mb_rdn R outl <= mb_len R - mb_pos R) by (unfold mb_rdn, mb_avail in *; lia).
    match goal with H : rw_cells rsegs _ out _ |- _ => rewrite SL in H; rename H into OUTC2 end.
    unhide OF1; unhide RF1; unhide AP1; unhide AP2; unhide AP3; unhide PS1; unhide RG1.
    st1. hide OF1; hide RF1; hide AP1; hide AP2; hide AP3; hide PS1; hide RG1.
    step. if_cases KN; zify_cond KN.
    - (* [comment removed for export] *)
      step. step. step. step. unfold P_BIO_ctrl. step.
      pose proof bioctrl_mem_spec as BCS. unfold bioctrl_mem_stmt, memctrl_stmt_at, BIOCTRL_STACK, MEMCTRL_STACK, FR_BIO_ctrl, FR_mem_ctrl, P_BIO_ctrl in BCS.
      eapply evt_cut.
      { eapply BCS with (lo := lo) (R := mb_after_bread R (mb_rdn R outl)) (LB := LB) (cmd := BIO_CTRL_EOF); clear BCS;
          [reflexivity| reflexivity| reflexivity| reflexivity| left; reflexivity| lia| lia| membio_tac| | exact SEP| intros _; exact METH
          | rewrite unsigned_lit by lia; exact ST| exact CEIL| rewrite unsigned_lit by lia; lia| assumption| rewrite unsigned_lit by lia; reflexivity].
        unfold MEMBIO_below; cbn [mb_bb mb_bm mb_rp mb_after_bread]; exact BL. }
      clear BCS. unfold memctrl_post, BIO_SIZE.
      unhide OUTR; unhide RBR; unhide OUTM; unhide RBM; unhide RG1; unhide OF1; unhide RF1; unhide PS1. landx MU WM.
      hide OUTR; hide RBR; hide OUTM; hide RBM; hide RG1; hide OF1; hide RF1; hide PS1.
      replace (mem_ctrl_rv (mb_after_bread R (mb_rdn R outl)) BIO_CTRL_EOF) with 1.
      2:{ unfold mem_ctrl_rv, mb_avail, mb_after_bread; cbn [mb_len mb_pos]. rewrite Z.eqb_refl.
          replace (mb_len R - (mb_pos R + mb_rdn R outl) =? 0) with true; [reflexivity|]. symmetry; apply Z.eqb_eq. unfold mb_rdn, mb_avail in *. lia. }
      step. step. if_false. step. step.
      change (Z_to_bv 64 0) with (wz 0) at 1.
      unhide RF1; unhide RF2; unhide RF3; unhide RF4; unhide RBB; unhide RBR; unhide RBO; unhide RBM. st1.
      hide RF1; hide RF2; hide RF3; hide RF4; hide RBB; hide RBR; hide RBO; hide RBM.
      do 4 st1. step. step. release_frame FR ST (bv_unsigned sp).
      apply evt_done. unfold rd_ok. rewrite KN in *. cbn [Z.ltb].
      match goal with H : rw_cells rsegs _ out _ |- _ => rename H into OUTCf end.
      match goal with H : rw_cells rsegs _ rbp _ |- _ => rename H into RBCf end.
      do 14 eexists. eexists. eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
      split. { membio_tac. all: match goal with |- ?G => idtac "MBLEFT:" G end. }
      split. { exact BS2. }
      split. { rewrite ?SL in OUTCf |- *. exact OUTCf. }
      exact RBCf.
    - (* [comment removed for export] *)
      assert (NP : 0 < mb_rdn R outl) by lia.
      zstep. zstep. step. step. if_cases K2; zify_cond K2; [kill K2|]. clear K2. step. zstep. rewrite sgtz_mask by lia.
      change (Z_to_bv 64 (mb_rdn R outl)) with (wz (mb_rdn R outl)). step.
      unhide RF1; unhide RF2; unhide RF3; unhide RF4; unhide RBB; unhide RBR; unhide RBO; unhide RBM. st1.
      hide RF1; hide RF2; hide RF3; hide RF4; hide RBB; hide RBR; hide RBO; hide RBM.
      do 4 st1. step. step. release_frame FR ST (bv_unsigned sp).
      apply evt_done. unfold rd_ok. replace (0 <? mb_rdn R outl) with true by (symmetry; apply Z.ltb_lt; lia).
      match goal with H : rw_cells rsegs _ out _ |- _ => rename H into OUTCf end.
      match goal with H : rw_cells rsegs _ rbp _ |- _ => rename H into RBCf end.
      do 14 eexists. eexists. eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
      split. { membio_tac. }
      split. { exact BS2. }
      split. { rewrite SL. exact OUTCf. }
      exact RBCf.
  Qed.
  (* [comment removed for export] *)
  Lemma readintern_body : forall (entry stack : Z), entry = P_bio_read_intern -> stack = READINTERN_STACK -> readintern_mem_stmt_at entry stack.
  Proof.
    intros entry stack -> ->. unfold readintern_mem_stmt_at. intros until junk; intros A0 A1 A2 A3 OUTL MB BL SEP METH BS LEN OUTC MO RBC MORB RBO ST CEIL LO MI RAE. subst a0 a1 a2 a3.
    unfold P_bio_read_intern, READINTERN_STACK, BREADCONV_STACK, BIOEOF_STACK, MEMREAD_STACK, BIOCTRL_STACK, MEMCTRL_STACK, FR_bio_read_intern, FR_bread_conv, FR_BIO_eof, FR_mem_read, FR_BIO_ctrl,
      FR_mem_ctrl, BIOACC_STACK, FR_BIO_set_data in *.
    pose proof MB as MB0.
    destruct MB0 as (BC & BBC & BMC & RPC & I1 & I2 & I3 & I4 & RB1 & RB2 & RB3 & RB4 & POSR & LENR & BUFP & BUFH & FLR & RDO & AEOF & NUMR & NRD & NRD2 & NXT & PRV).
    pose proof RB1 as (AP & _ & _ & AH & RG1). pose proof RB2 as (BBP & _ & _ & BBH & _). pose proof RB3 as (BMP & _ & _ & BMH & RG3). pose proof RB4 as (RPP & _ & _ & RPH & _).
    hide RB1; hide RB2; hide RB3; hide RB4.
    pose proof BL as (BL1 & BL2 & BL3 & BL4). unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in BL1, BL2, BL3, BL4, AH, BBH, BMH, RPH, RG1, RG3. hide RG1; hide RG3.
    pose proof SEP as ((AP1 & AP2 & AP3 & AP4 & AP5 & AP6) & PS1 & PS2 & PS3 & PS4). unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in AP1, AP2, AP3, AP4, AP5, AP6, PS1, PS2, PS3, PS4.
    hide AP1; hide AP2; hide AP3; hide AP4; hide AP5; hide AP6; hide PS1; hide PS2; hide PS3; hide PS4.
    pose proof MO as MO0. destruct MO0 as (OUTR & OUTP & OUTH & OUTF & OUTB & OUTM).
    pose proof (Forall_inv OUTF) as OF1. pose proof (Forall_inv (Forall_inv_tail OUTF)) as OF2.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail OUTF))) as OF3. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail OUTF)))) as OF4.
    clear OUTF. cbn [blk_addr blk_size fst snd] in OF1, OF2, OF3, OF4. unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in OF1, OF2, OF3, OF4.
    unfold A_mem_buf_method, O_METH_BREAD in OUTM. hide OF1; hide OF2; hide OF3; hide OF4; hide OUTR; hide OUTB; hide OUTM.
    pose proof MORB as MORB0. destruct MORB0 as (RBR & RBP & RBH & RBF & RBB & RBM). unfold A_mem_buf_method, O_METH_BREAD in RBM.
    pose proof (Forall_inv RBF) as RF1. pose proof (Forall_inv (Forall_inv_tail RBF)) as RF2.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail RBF))) as RF3. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail RBF)))) as RF4.
    clear RBF. cbn [blk_addr blk_size fst snd] in RF1, RF2, RF3, RF4. unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in RF1, RF2, RF3, RF4.
    hide RF1; hide RF2; hide RF3; hide RF4; hide RBR; hide RBB; hide RBO; hide RBM.
    pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption). hcb.
    pose proof (rw_cells_bound _ _ _ _ OUTC) as OB. cbn [cells_size csize Nat.add] in OB.
    pose proof (munch_refl ((lo, bv_unsigned sp) :: (out, out + outl) :: (rbp, rbp + 8) :: MEMBIO_foot a R) m) as MU. pose proof (wmono_refl rsegs m) as WM.
    unfold MEMBIO_foot, BIO_SIZE, BUFMEM_SIZE in MU.
    unfold bio_cells, membio_bio, wz in BC. cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite] in BC.
    unfold A_mem_buf_method in BC. unfold wz in BBC, RBC. unfold buf_cells, wz in BMC, RPC. cbn [bm_len bm_data bm_max bm_flags] in BMC, RPC.
    unfold METH_mem, O_METH_BREAD, A_mem_buf_method, wz in METH. norm_addr METH.
    unhide RBR; unhide OUTR. carve_frame 80%nat ST.
    do 10 st1. hide RBR; hide OUTR. step. step. if_cases K0; zify_cond K0; [kill K0|]. clear K0.
    step. st1. step. step. step. step. if_false. st1. step. if_false.
    step. step. step. st1. step. if_false. st1. step. if_true.
    st1. step. if_false. st1. st1. step. step. step. step. unfold P_bread_conv. step.
    (* [comment removed for export] *)
    pose proof breadconv_mem_spec as BRS. unfold breadconv_mem_stmt, BREADCONV_STACK, MEMREAD_STACK, BIOCTRL_STACK, MEMCTRL_STACK, FR_bread_conv, FR_mem_read, FR_BIO_ctrl, FR_mem_ctrl,
      BIOACC_STACK, FR_BIO_set_data, P_bread_conv in BRS.
    eapply evt_cut.
    { eapply BRS with (lo := lo) (R := R) (LB := LB) (junk := junk) (rbv := rbv); clear BRS;
        [reflexivity| reflexivity| reflexivity| reflexivity| exact OUTL| membio_tac| exact BL| exact SEP| exact METH| exact BS| exact LEN| exact OUTC| | exact RBC| | exact RBO
        | rewrite unsigned_lit by lia; exact ST| exact CEIL| rewrite unsigned_lit by lia; lia| assumption| rewrite unsigned_lit by lia; reflexivity].
      - unfold memrd_out. rewrite unsigned_lit by lia. unhide OUTR; unhide OUTB; unhide OF1; unhide OF2; unhide OF3; unhide OF4; unhide OUTM.
        split; [lia|]. split; [lia|]. split; [lia|]. split; [| unfold A_mem_buf_method, O_METH_BREAD; lia].
        unfold blocks_MEMBIO, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE. repeat (apply Forall_cons; [cbn [blk_addr blk_size fst snd]; lia|]). apply Forall_nil.
      - unfold memrd_out. rewrite unsigned_lit by lia. unhide RBR; unhide RBB; unhide RF1; unhide RF2; unhide RF3; unhide RF4; unhide RBM.
        split; [lia|]. split; [lia|]. split; [lia|]. split; [| unfold A_mem_buf_method, O_METH_BREAD; lia].
        unfold blocks_MEMBIO, BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE. repeat (apply Forall_cons; [cbn [blk_addr blk_size fst snd]; lia|]). apply Forall_nil. }
    clear BRS. unfold memrd_post, MEMBIO_foot, BIO_SIZE, BUFMEM_SIZE.
    unhide OUTR; unhide RBR; unhide OUTM; unhide RBM; unhide RG1; unhide RG3. landx MU WM. hide OUTR; hide RBR; hide OUTM; hide RBM; hide RG1; hide RG3.
    replace (ret_pc (Z_to_bv 64 1047296)) with (Z_to_bv 64 1047296) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    match goal with H : MEMBIO LB _ a _ |- _ => destruct H as (BC1 & BBC1 & BMC1 & RPC1 & _) end.
    pose proof (bio_flags_byte _ _ _ BC1) as RD.
    unfold bio_cells, membio_bio, buf_cells, mb_after_bread, wz, A_mem_buf_method, BIO_FLAGS_RETRY_MASK in BC1, BBC1, BMC1, RPC1.
    cbn [bio_method bio_init bio_shutdown bio_flags bio_retry bio_numf bio_ptr bio_next bio_prev bio_refs bio_nread bio_nwrite bm_len bm_data bm_max bm_flags
         mb_buf mb_len mb_pos mb_flags mb_numf mb_nread mb_next mb_prev mb_bb mb_bm mb_rp] in BC1, BBC1, BMC1, RPC1.
    cbn [bio_flags membio_bio mb_flags mb_after_bread] in RD. unfold BIO_FLAGS_RETRY_MASK in RD.
    match goal with H : bytes_at rsegs _ (mb_buf _) ds |- _ => cbn [mb_buf mb_after_bread] in H; rename H into BS2 end.
    pose proof (clr_flags_facts (mb_flags R) FLR ltac:(unfold BIO_FLAGS_MEM_RDONLY in RDO; exact RDO) AEOF) as (FL1 & FL2 & FL3).
    assert (SL : length (mb_take R ds (mb_rdn R outl)) = Z.to_nat (mb_rdn R outl)).
    { unfold mb_take. rewrite firstn_length_le; [reflexivity|]. rewrite length_skipn. unfold mb_rdn, mb_avail in *. lia. }
    assert (NR : 0 <= mb_rdn R outl <= outl /\ mb_rdn R outl <= mb_len R - mb_pos R) by (unfold mb_rdn, mb_avail in *; lia).
    match goal with H : rw_cells rsegs _ out _ |- _ => rewrite SL in H; rename H into OUTC2 end.
    match goal with H : rw_cells rsegs _ rbp _ |- _ => rename H into RBC2 end.
    destruct (Z.eq_dec (mb_rdn R outl) 0) as [KN|KN].
    - (* [comment removed for export] *)
      unfold rd_ok. rewrite KN in *. cbn [Z.ltb].
      step. step. if_true. step. if_cases K1; zify_cond K1; [kill K1|]. clear K1. step. if_false.
      st1. clear RD. zstep. rewrite wz_unsigned by lia. rewrite land_mod256_128, FL3 by lia. step. if_false.
      step. step. step. step. unfold P_BIO_ctrl. step.
      pose proof bioctrl_mem_spec as BCS. unfold bioctrl_mem_stmt, memctrl_stmt_at, BIOCTRL_STACK, MEMCTRL_STACK, FR_BIO_ctrl, FR_mem_ctrl, P_BIO_ctrl in BCS.
      eapply evt_cut.
      { eapply BCS with (lo := lo) (R := mb_after_bread R 0) (LB := LB) (cmd := BIO_CTRL_EOF); clear BCS;
          [reflexivity| reflexivity| reflexivity| reflexivity| left; reflexivity| lia| lia| membio_tac| | exact SEP| intros _; exact METH
          | rewrite unsigned_lit by lia; exact ST| exact CEIL| rewrite unsigned_lit by lia; lia| assumption| rewrite unsigned_lit by lia; reflexivity].
        unfold MEMBIO_below; cbn [mb_bb mb_bm mb_rp mb_after_bread]; exact BL. }
      clear BCS. unfold memctrl_post, BIO_SIZE.
      unhide OUTR; unhide RBR; unhide OUTM; unhide RBM; unhide RG1; unhide OF1; unhide RF1; unhide PS1. landx MU WM.
      hide OUTR; hide RBR; hide OUTM; hide RBM; hide RG1; hide OF1; hide RF1; hide PS1.
      replace (mem_ctrl_rv (mb_after_bread R 0) BIO_CTRL_EOF) with 1.
      2:{ unfold mem_ctrl_rv, mb_avail, mb_after_bread; cbn [mb_len mb_pos]. rewrite Z.eqb_refl.
          replace (mb_len R - (mb_pos R + 0) =? 0) with true; [reflexivity|]. symmetry; apply Z.eqb_eq. unfold mb_rdn, mb_avail in *. lia. }
      zstep. zstep. zstep. step. st1. step. if_false. st1. step. if_true. zstep. step. if_true. zstep.
      do 9 st1. step. step. release_frame FR ST (bv_unsigned sp).
      apply evt_done. rewrite ?SL.
      match goal with H : rw_cells rsegs _ out _ |- _ => rename H into OUTCf end.
      match goal with H : rw_cells rsegs _ rbp _ |- _ => rename H into RBCf end.
      do 14 eexists. eexists. eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
      split. { membio_tac. all: match goal with |- ?G => idtac "MBLEFT0:" G end. }
      split. { exact BS2. }
      split. { exact OUTCf. }
      exact RBCf.
    - (* [comment removed for export] *)
      unfold rd_ok. replace (0 <? mb_rdn R outl) with true by (symmetry; apply Z.ltb_lt; lia). clear RD.
      step. step. if_false. st1. st1. zstep.
      change (Z_to_bv 64 (mb_nread R + mb_rdn R outl)) with (wz (mb_nread R + mb_rdn R outl)).
      unhide OF1; unhide RF1; unhide AP1; unhide AP2; unhide AP3; unhide PS1; unhide RG1.
      st1. hide OF1; hide RF1; hide AP1; hide AP2; hide AP3; hide PS1; hide RG1.
      st1. step. if_false. st1. step. if_true. zstep. step. if_false. st1. step. if_cases K5; zify_cond K5; [| kill K5]. clear K5.
      zstep. do 9 st1. step. step. release_frame FR ST (bv_unsigned sp).
      apply evt_done. rewrite SL.
      match goal with H : rw_cells rsegs _ out _ |- _ => rename H into OUTCf end.
      match goal with H : rw_cells rsegs _ rbp _ |- _ => rename H into RBCf end.
      do 14 eexists. eexists. eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
      split. { membio_tac. all: match goal with |- ?G => idtac "MBLEFT:" G end. }
      split. { exact BS2. }
      split. { exact OUTCf. }
      exact RBCf.
  Qed.

  Lemma readintern_mem_spec : readintern_mem_stmt.
  Proof. apply readintern_body; reflexivity. Qed.
End S.
