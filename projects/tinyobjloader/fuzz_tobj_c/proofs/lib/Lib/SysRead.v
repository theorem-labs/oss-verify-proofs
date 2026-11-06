(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "@Corelib.Init.Datatypes"; "option"; "list"; "Some"; "pair"; "length"; "None"; "bool"; "false"; "nat"; "nil"; "cons"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "bv_add"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "FdEntry"; "Model"; "m_fds"; "event"; "fd_lookup"; "FdFile"; "m_fs"; "TASK_SIZE"; "read_bytes_map"; "MAX_RW_COUNT"; "FdDir"; "with_fds"; "EISDIR"; "errno_ret"; "fd_insert"; "fd_remove"; "read_bytes_aux"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "of_nat"; "to_nat"; "lt"; "sub"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "eval"; "reg_sv"; "cell"; "soff"; "sobj"; "sv"; "mkObj"; "ss_next"; "ss_objs"; "DUnknown"; "SVar"; "smatch"; "obj_holds"; "rw"; "ss_pc"; "valuation"; "c_off"; "c_width"; "mkCell"; "rl"; "rm"; "sstate"; "DList"; "SLit"; "enc_bytes"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "jpred"; "ok_frameJ"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "ms_gpr"; "ms_mem"; "ms_writable_byte"; "write_to_mem"; "ms_rom"; "ms_svc_pending"; "wview"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SysRead.WithSegs.ReadFile"; "rd_bs"; "rd_rho'"; "rd_S'"; "rd_md'"; "@LinuxProcessSemantics.LinuxProcessSem.Fs"; "fs_lookup"; "file_read"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "smatch_pending"; "rho_set_rw"; "S_after"; "ok_pframeJ"; "sv_has_rl"; "rho_set_rl"; "state_has_rl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SysRead.WithSegs.ReadBuf"; "rb_bs"; "rb_md'"; "rh_rho'"; "rk_rho'"; "rh_S'"; "rk_S'"; "@LinuxProcessSemantics.LinuxProcessSem.BvBase"; "len_word"; "@Stdlib.PArith.BinPos.Pos"; "succ"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "model_idle"; "etriple"; "triple1"; "world"; "@Corelib.Init.Peano"; "le"; "@Stdlib.Lists.List"; "nth_error"; "@Corelib.Lists.ListDef"; "Forall"; "firstn"; "skipn"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall"; "fd32"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "list_set"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SysRead.WithSegs"; "hdr_val"; "S_after_var"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep"; "after_sys_mem"; "after_sys"; "closed_model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SysRead.WithSegs.Close"; "close_S'"; "close_md'"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SysRead.WithSegs.ReadDir"; "dir_S'"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool PArith.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uaccess Uapi Syscall.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundW
  SymSoundF SymSoundR SymComplete SymCall SymEntail SymExit SymFrame SymBytes Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.

Lemma fd32_3 : fd32 (Z_to_bv 64 3) = Z_to_bv 64 3.
Proof using . vm_compute. reflexivity. Qed.

Lemma errno_EISDIR : ltac2:(tb__ "0|0|
S0S13S10Q40S22S21A1A2S2bS2cZ2Z40A2Z15A2A3").
Proof using . vm_compute. reflexivity. Qed.

Lemma read_bytes_aux_pw : ltac2:(tb__ "0|4|
SfQ40M0A1S4SfQ8A1M1A1M2F_;ScS13S13S1S26Z0R1A2S2aR1S28R3A1A2A2S3S0G2R5S11G0S27R3R2A2A2A1S9G1A1A3A1F_;Fi;S3S0S4S5G1A1M3A1S25R4S11G0R2A2R3A3S9G3A1A3A1F_;Fa;Fk;Ff;").
Proof using .
  intros f k. induction k as [|k IH]; intros a H; [discriminate|].
  cbn [read_bytes_aux].
  pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
  destruct (f (Z_to_bv 64 a)) as [b|]; [|exfalso; exact (H0 eq_refl)].
  rewrite Z_to_bv64_add1.
  specialize (IH (a + 1) ltac:(intros i Hi; replace (a + 1 + i) with (a + (1 + i)) by lia; apply H; lia)).
  destruct (read_bytes_aux f (Z_to_bv 64 (a + 1)) k); [discriminate | exact IH].
Qed.

Lemma writable_range_pw : ltac2:(tb__ "0|4|
S49SfQ40M0A1M1G1S13S1S26Z0R1A2S2aR1S10G0R2A2A2A2S3S0S4SfQ8A1M2A1S50Vsegs;S4bR5A1S11G0S27S10G0R4A2R2A2A2A3S9G2A1A3A1F_;Fi;S3S0S4S5G2A1M3A1S1dS4cVsegs;R4A2R3R2A3S9G3A1A3A1F_;Flen;Fbuf;Fms;").
Proof using .
  intros ms buf len H. pose proof (urange len) as Hl.
  rewrite read_bytes_map_eq; unfold ms_writable_byte, word_to_nat.
  rewrite <- (Z_to_bv_bv_unsigned 64 buf).
  change (fun addr => wview segs (ms_mem ms) addr) with (wview segs (ms_mem ms)).
  apply read_bytes_aux_pw. intros i Hi. apply H. rewrite Z2Nat.id in Hi by lia. exact Hi.
Qed.

Definition S_after_var (S : sstate) (objs : list sobj) : sstate := ltac2:(tb__ "0|1|
S5dVS;S37S34VS;A1M0A1Vobjs;S69G0A1A4").
Definition S_after_lit (S : sstate) (z : Z) : sstate := ltac2:(tb__ "0|0|
S5dVS;S44Vz;A1S35VS;A1S34VS;A1A4").

Lemma list_set_nth_same {A} : ltac2:(tb__ "0|1|
S5VA;A1M0ScVA;S0S4VA;A1S70VA;R3R2A3S6VA;R1A2A3S0G0S76VA;R4R3R2A4R4A3F_;Fx;Fk;Fl;").
Proof using .
  induction l as [|h t IH]; intros [|k] x H; cbn in *; try discriminate.
  - injection H as ->. reflexivity.
  - rewrite (IH k x H). reflexivity.
Qed.

Lemma obj_holds_kwrite_keep : ltac2:(tb__ "0|5|
S3cS49S49S32S32S32S13S13S5S2fA1SfQ40M0A1M1S5SfQ8A1M2A1S13S39Vsegs;RcRbS33R9R8R7R4S36A5A4S0S13S30RdR9A2R7A3S0S13S30ReR9A2R7A3S0G1S4G2A1F_;M3S4eRdA1S4eReA1A3S0G3S4bReA1S4dS4bRfA1R7R6A3A3S0S13S10G0R8A2S27S10G0S2dR11ReA2A2R6A2A3S26RcR7A2S26S27R8S28S8G2R9A2A1A2RcA2S71S2fS2fS26S27S30R15S3dR1A1A2S3eR1A1M4A2RaA2Lc;RcA3S71S2fS2fS1S26Z1G4A2S26G4Z8A2A2Lc;RdA3S39Vsegs;R16R14S33R13R12R11ReS36A5A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fwoff;Fbs;Fbuf;Fcells;Fhi;Flo;Fehi;Felo;Fbase;Fms';Fms;Frho;").
Proof using .
  intros rho ms ms' base elo ehi lo hi cells buf bs woff Ho Helo Hehi Hr Hm Hbuf Hlo Hhi Hcells Hcw.
  pose proof Ho as Ho0.
  unfold obj_holds, obj_lo_of, obj_hi_of in Ho. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in Ho.
  rewrite Helo, Hehi in Ho. destruct Ho as (Hb & Hw & Hc & Hd & _).
  set (B := bv_unsigned (eval rho base)) in *.
  assert (Hnw : bv_unsigned buf + Z.of_nat (length bs) <= 2 ^ 64) by lia.
  assert (Hsame : forall off, ~ (woff <= off < woff + Z.of_nat (length bs)) -> 0 <= B + off < 2 ^ 64 ->
            ms_mem ms' (Z_to_bv 64 (B + off)) = ms_mem ms (Z_to_bv 64 (B + off))).
  { intros off Hno Hrg. rewrite Hm. apply write_to_mem_out; [exact Hnw|]. rewrite Z_to_bv_small by (rewrite two64; lia). lia. }
  unfold obj_holds, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt]. rewrite Helo, Hehi. fold B.
  split; [exact Hb|]. split.
  { intros off Hoff _. eapply wview_mono; [|apply Hw; [exact Hoff | reflexivity]].
    intros y Hy. rewrite Hm. apply write_to_mem_grows. exact Hy. }
  split.
  { apply Forall_forall. intros c Hin.
    pose proof (proj1 (Forall_forall _ _) Hc c Hin) as (C1 & C2 & C3).
    pose proof (proj1 (Forall_forall _ _) Hcells c Hin) as Cw. cbn beta in Cw.
    pose proof (proj1 (Forall_forall _ _) Hcw c Hin) as Cw8. cbn beta in Cw8.
    split; [exact C1|]. split; [exact C2|].
    rewrite <- C3. apply rd_bytes_unchanged; [exact Hr | rewrite oaddr_unsigned by (fold B; lia); fold B; lia |].
    intros j Hj. rewrite oaddr_unsigned by (fold B; lia). fold B.
    replace (B + soff rho (c_off c) + Z.of_nat j) with (B + (soff rho (c_off c) + Z.of_nat j)) by lia.
    apply Hsame; lia. }
  split; [|exact I].
  intros off Hoff Hnc. cbn [dflt_holds].
  destruct (Z_lt_le_dec off woff) as [Hlt|Hge].
  { rewrite (rd_unchanged ms ms'); [exact (Hd off Hoff Hnc) | apply Hsame; lia | exact Hr]. }
  destruct (Z_lt_le_dec off (woff + Z.of_nat (length bs))) as [Hlt2|Hge2].
  2:{ rewrite (rd_unchanged ms ms'); [exact (Hd off Hoff Hnc) | apply Hsame; lia | exact Hr]. }
  unfold rd, ms_read_byte. rewrite Hm.
  replace (B + off) with (bv_unsigned buf + Z.of_nat (Z.to_nat (off - woff))) by lia.
  rewrite write_to_mem_in; [eexists; reflexivity | exact Hnw | lia].
Qed.

Lemma smatch_after_kwrite_keep : ltac2:(tb__ "0|5|
S3cS42S5S18A1M0S49S16G0S16SfQ40M1A1M2ScS32S32S32S13S13S5S2fA1G2S5SfQ8A1M3A1S13S5bVsegs;R12R11S7G0S51R10S52RfReA2A4A4S6bRdA1S0S4S31A1S70S31S35R13A1RcA3S6S31S33RbRaR9R6S36A5A2A3S0S13S30R15RbA2R9A3S0S13S30R16RbA2R9A3S0S13S10G1R8A2S27S10G1S2dR17ReA2A2R6A2A3S26RcR7A2S26S27R8S28S8G3R9A2A1A2RcA2S71S2fS2fS26S27S30R1bS3dR1A1A2S3eR1A1A2RaA2Lc;RcA3S38Vsegs;S5cR1bS34R1aA1M4R14A3S5dR1aS37G4A1S35R1aA1S69G4A1A4S7G0S51R16S52S79R18R14S4dS4bR18A1RcRbA3A3R15A2A4A4F_;F_;F_;F_;F_;F_;F_;F_;F_;Fwoff;Fbs;Fbuf;Fcells;Fhi;Flo;Fehi;Felo;Fbase;Fk;Fr;Fmd';Ftr';Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md tr' md' r k base elo ehi lo hi cells buf bs woff Hsp Hh' Hnth Helo Hehi Hbuf Hlo Hhi Hcells.
  set (nx := ss_next S). set (rho' := rho_set_rw rho nx r).
  assert (Hag : agree_below nx rho rho') by (apply agree_below_set_rw; lia).
  pose proof (smatch_pending_agree segs rho rho' S tr ms md Hag Hsp) as Hsp'.
  pose proof (smatch_pending_swf segs _ _ _ _ _ Hsp) as Hwf.
  pose proof (swf_objs S Hwf) as Hobjwf.
  pose proof (swf_obj_nth _ _ _ Hwf Hnth) as Howf.
  pose proof Howf as Howf0. unfold obj_wf in Howf0. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in Howf0.
  apply andb_prop in Howf0 as [Howf0 _]. apply andb_prop in Howf0 as [Howf0 Hcwf]. apply andb_prop in Howf0 as [Howf0 Hbhi].
  apply andb_prop in Howf0 as [Hbb Hblo].
  assert (Hbase : eval rho' base = eval rho base) by (symmetry; eapply eval_agree; [exact Hag| exact Hbb]).
  assert (Helo' : soff rho' elo = lo) by (unfold soff; rewrite <- (eval_agree nx rho rho' elo Hag Hblo); exact Helo).
  assert (Hehi' : soff rho' ehi = hi) by (unfold soff; rewrite <- (eval_agree nx rho rho' ehi Hag Hbhi); exact Hehi).
  pose proof (smatch_pending_mem segs _ _ _ _ _ Hsp') as Hmm'.
  pose proof (mem_match_nth segs _ _ _ _ _ Hmm' Hnth) as Hoh'.
  rewrite <- (list_set_nth_same (ss_objs S) k _ Hnth).
  eapply smatch_after_sys; [exact Hsp' | exact Hh' | lia | | | | |].
  - cbn. apply Pos.ltb_lt. lia.
  - cbn. rewrite Pos.eqb_refl. reflexivity.
  - apply forallb_list_set.
    + apply forallb_forall. intros o Hino. eapply obj_wf_mono; [|exact (proj1 (forallb_forall _ _) Hobjwf o Hino)]. lia.
    + eapply obj_wf_mono; [|exact Howf]. lia.
  - eapply (mem_match_kwrite segs rho' (ss_objs S) ms _ nx k (mkObj base elo ehi cells DUnknown) _ buf bs woff);
      [reflexivity | reflexivity | exact Hmm' | exact Hobjwf | exact Hnth
      | cbn [ob_base]; rewrite Hbase; exact Hbuf
      | unfold obj_lo_of; cbn [ob_lo]; rewrite Helo'; exact Hlo
      | unfold obj_hi_of; cbn [ob_hi]; rewrite Hehi'; exact Hhi
      | reflexivity |].
    eapply (obj_holds_kwrite_keep rho' ms _ base elo ehi lo hi cells buf bs woff);
      [exact Hoh' | exact Helo' | exact Hehi' | reflexivity | reflexivity | rewrite Hbase; exact Hbuf | exact Hlo | exact Hhi | |].
    + apply Forall_forall. intros c Hin. pose proof (proj1 (Forall_forall _ _) Hcells c Hin) as Cw. cbn beta in Cw.
      pose proof (proj1 (forallb_forall _ _) Hcwf c Hin) as Wc. unfold cell_wf in Wc. apply andb_prop in Wc as [Wc _]. apply andb_prop in Wc as [_ Woff].
      unfold soff. rewrite <- (eval_agree nx rho rho' (c_off c) Hag Woff). exact Cw.
    + apply Forall_forall. intros c Hin.
      pose proof (proj1 (forallb_forall _ _) Hcwf c Hin) as Wc. unfold cell_wf in Wc.
      apply andb_prop in Wc as [Wc _]. apply andb_prop in Wc as [Ww _]. apply andb_prop in Ww as [W1 W2]. apply Z.ltb_lt in W1. apply Z.leb_le in W2. lia.
  - intros a Hro.
    eapply (ro_clear_kwrite segs rho ms (mkObj base elo ehi cells DUnknown) buf bs woff);
      [exact (smatch_pending_ro_clear segs _ _ _ _ _ Hsp) | exact (mem_match_nth segs _ _ _ _ _ (smatch_pending_mem segs _ _ _ _ _ Hsp) Hnth) | reflexivity
      | cbn [ob_base]; exact Hbuf
      | unfold obj_lo_of; cbn [ob_lo]; rewrite Helo; exact Hlo
      | unfold obj_hi_of; cbn [ob_hi]; rewrite Hehi; exact Hhi
      | reflexivity | exact Hro].
Qed.

Definition hdr_val (bs : list byte) : word := Z_to_bv 64 (bytes_le_to_Z (firstn 4 bs)).

Lemma hdr_val_enc : ltac2:(tb__ "0|3|
S5SfQ8A1M0A1M1S6fU4M2S8G0R1A2A2S0G1S45G2S77R2A1A2S72G0G2R2A3A3F_;Fbs;").
Proof using .
  intros bs Hl. unfold enc_bytes, hdr_val.
  assert (L4 : length (firstn 4 bs) = 4%nat) by (rewrite length_firstn; lia).
  pose proof (bytes_le_to_Z_bound (firstn 4 bs)) as B. rewrite L4 in B. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in B.
  rewrite Z_to_bv_small by (rewrite two64; lia).
  rewrite <- L4 at 1. apply Z_to_le_bytes_bytes_le_to_Z.
Qed.

Lemma obj_holds_kwrite_hdr : ltac2:(tb__ "0|5|
S3cS49S49S32S32S32S13S13SfQ40M0A1M1S5SfQ8A1M2A1S14S39Vsegs;RbRaS33R8R7R6SdS2fA1M3S36A5A4S0S13S30RcR8A2R6A3S0S13S30RdR8A2R6A3S0G1S4G2A1F_;M4S4eRcA1S4eRdA1A3S0G4S4bRdA1S4dS4bReA1R7R6A3A3S0S13S10G0R8A2S27S10G0S2dR10RdA2A2RaA2A3S26S27RbS28S8G2R8A2A1A2RaA2S6fU4S8G2R9A2A2S0G1S3aR13R9A2S77RaA1A3S39Vsegs;R14R12S33R11R10RfSeS2fS3fR10Z4S37RaA1A3G3A3S36A5A4F_;F_;F_;F_;F_;F_;F_;F_;F_;Fh;Fbs;Fbuf;Fhi;Flo;Fehi;Felo;Fbase;Fms';Fms;Frho;").
Proof using .
  intros rho ms ms' base elo ehi lo hi buf bs h Ho Helo Hehi Hr Hm Hbuf Hhi H4 Hh.
  pose proof (obj_holds_kwrite_keep rho ms ms' base elo ehi lo hi [] buf bs lo Ho Helo Hehi Hr Hm Hbuf ltac:(lia) Hhi
                ltac:(constructor) ltac:(constructor)) as Ho'.
  unfold obj_holds, obj_lo_of, obj_hi_of in Ho' |- *. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in *.
  rewrite Helo, Hehi in Ho' |- *. destruct Ho' as (Hb & Hw & _ & Hd & _).
  split; [exact Hb|]. split; [exact Hw|]. split.
  { constructor; [|constructor]. unfold cell_holds. cbn [c_off c_width c_val]. rewrite Helo.
    split; [lia|]. split; [lia|].
    cbn [eval]. rewrite Hh. change (Z.to_nat 4) with 4%nat. rewrite (hdr_val_enc bs H4).
    assert (Hnw : bv_unsigned buf + Z.of_nat (length bs) <= 2 ^ 64) by lia.
    apply rd_bytes_of_nth; [rewrite length_firstn; lia | rewrite oaddr_unsigned by lia; lia |].
    intros j Hj. rewrite oaddr_unsigned by lia. rewrite <- Hbuf.
    unfold rd, ms_read_byte. rewrite Hm, write_to_mem_in by (try exact Hnw; lia).
    rewrite nth_firstn. destruct (Nat.ltb_spec j 4); [reflexivity | lia]. }
  split; [|exact I].
  intros off Hoff _. apply Hd; [exact Hoff|]. intros HC. inversion HC.
Qed.

Lemma smatch_after_kwrite_hdr : ltac2:(tb__ "0|7|
S3cS42S5S18A1M0S49S16G0S16SfQ40M1A1M2ScS32S32S32S13S13G2S5SfQ8A1M3A1S5bVsegs;R10RfS7G0S51ReS52RdRcA2A4A4S6bRbA1S0S4S31A1S70S31S35R11A1RaA3S6S31S33R9R8R7SdS2fA1M4S36A5A2A3S0S13S30R13R9A2R7A3S0S13S30R14R9A2R7A3S0S13S10G1R7A2S27S10G1S2dR15RcA2A2R9A2A3S26S27RaS28S8G3R7A2A1A2R9A2S6fU4S8G3R8A2A2S38Vsegs;S5cS5cR18S34R17A1M5S77R9A1A3S69G5A1M6R11A3S5dR17S37G6A1S76S31S35R17A1R10S33RfReRdSeS2fS3fReZ4S37G5A1A3G4A3S36A5A4S69G6A1A4S7G0S51R13S52S79R15R11S4dS4bR15A1RaR9A3A3R12A2A4A4F_;F_;F_;F_;F_;F_;F_;F_;Fbs;Fbuf;Fhi;Flo;Fehi;Felo;Fbase;Fk;Fr;Fmd';Ftr';Fmd;Fms;Ftr;FS;Frho;").
Proof using .
  intros rho S tr ms md tr' md' r k base elo ehi lo hi buf bs Hsp Hh' Hnth Helo Hehi Hbuf Hhi H4.
  set (h := ss_next S) in *. set (rho' := rho_set_rw (rho_set_rw rho h (hdr_val bs)) (Pos.succ h) r).
  assert (Hag : agree_below h rho rho').
  { subst rho'. eapply agree_below_trans; [apply (agree_below_set_rw rho h (hdr_val bs) h); lia | apply (agree_below_set_rw _ (Pos.succ h) r h); lia]. }
  pose proof (smatch_pending_agree segs rho rho' S tr ms md Hag Hsp) as Hsp'.
  pose proof (smatch_pending_swf segs _ _ _ _ _ Hsp) as Hwf.
  pose proof (swf_objs S Hwf) as Hobjwf.
  pose proof (swf_obj_nth _ _ _ Hwf Hnth) as Howf.
  pose proof Howf as Howf0. unfold obj_wf in Howf0. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in Howf0.
  apply andb_prop in Howf0 as [Howf0 _]. apply andb_prop in Howf0 as [Howf0 _]. apply andb_prop in Howf0 as [Howf0 Hbhi].
  apply andb_prop in Howf0 as [Hbb Hblo].
  assert (Hbase : eval rho' base = eval rho base) by (symmetry; eapply eval_agree; [exact Hag| exact Hbb]).
  assert (Helo' : soff rho' elo = lo) by (unfold soff; rewrite <- (eval_agree h rho rho' elo Hag Hblo); exact Helo).
  assert (Hehi' : soff rho' ehi = hi) by (unfold soff; rewrite <- (eval_agree h rho rho' ehi Hag Hbhi); exact Hehi).
  pose proof (smatch_pending_mem segs _ _ _ _ _ Hsp') as Hmm'.
  pose proof (mem_match_nth segs _ _ _ _ _ Hmm' Hnth) as Hoh'.
  eapply smatch_after_sys; [exact Hsp' | exact Hh' | lia | | | | |].
  - cbn. apply Pos.ltb_lt. lia.
  - subst rho'. cbn. rewrite Pos.eqb_refl. reflexivity.
  - apply forallb_list_set.
    + apply forallb_forall. intros o Hino. eapply obj_wf_mono; [|exact (proj1 (forallb_forall _ _) Hobjwf o Hino)]. lia.
    + unfold obj_wf. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt forallb cell_wf c_off c_width c_val dflt_wf andb].
      rewrite (sv_below_mono h (Pos.succ (Pos.succ h)) base ltac:(lia) Hbb), (sv_below_mono h (Pos.succ (Pos.succ h)) elo ltac:(lia) Hblo),
              (sv_below_mono h (Pos.succ (Pos.succ h)) ehi ltac:(lia) Hbhi).
      unfold cell_wf. cbn [c_off c_width c_val sv_below andb Z.ltb Z.leb Z.compare Pos.compare].
      rewrite (sv_below_mono h (Pos.succ (Pos.succ h)) elo ltac:(lia) Hblo). cbn.
      rewrite (proj2 (Pos.ltb_lt h (Pos.succ (Pos.succ h)))) by lia. reflexivity.
  - eapply (mem_match_kwrite segs rho' (ss_objs S) ms _ h k (mkObj base elo ehi [] DUnknown) _ buf bs lo);
      [reflexivity | reflexivity | exact Hmm' | exact Hobjwf | exact Hnth
      | cbn [ob_base]; rewrite Hbase; exact Hbuf
      | unfold obj_lo_of; cbn [ob_lo]; rewrite Helo'; lia
      | unfold obj_hi_of; cbn [ob_hi]; rewrite Hehi'; exact Hhi
      | unfold obj_range, obj_lo_of, obj_hi_of; cbn [ob_base ob_lo ob_hi]; reflexivity |].
    eapply (obj_holds_kwrite_hdr rho' ms _ base elo ehi lo hi buf bs h);
      [exact Hoh' | exact Helo' | exact Hehi' | reflexivity | reflexivity | rewrite Hbase; exact Hbuf | exact Hhi | exact H4 |].
    subst rho'. cbn. rewrite Pos.eqb_refl. destruct (Pos.eqb_spec h (Pos.succ h)); [lia|reflexivity].
  - intros a Hro.
    eapply (ro_clear_kwrite segs rho ms (mkObj base elo ehi [] DUnknown) buf bs lo);
      [exact (smatch_pending_ro_clear segs _ _ _ _ _ Hsp) | exact (mem_match_nth segs _ _ _ _ _ (smatch_pending_mem segs _ _ _ _ _ Hsp) Hnth) | reflexivity
      | cbn [ob_base]; exact Hbuf
      | unfold obj_lo_of; cbn [ob_lo]; rewrite Helo; lia
      | unfold obj_hi_of; cbn [ob_hi]; rewrite Hehi; exact Hhi
      | reflexivity | exact Hro].
Qed.

Section ReadFile.
Variable S : sstate.
Variable rho : valuation.
Variable k : nat.
Variables base elo ehi : sv.
Variable cells : list cell.
Variable d : odefault.
Variables p data : list byte.
Variable off : Z.
Variable l : positive.
Hypothesis Hi : ltac2:(tb__ "0|0|
S0S4S59A1S75Vsegs;S3bVS;A1A2S6S59S5aA2A3").
Hypothesis H17 : reg_sv S 17 = SLit 63.
Hypothesis H10 : reg_sv S 10 = SLit 3.
Hypothesis Hoff : 0 <= off < 2 ^ 64.

Hypothesis Hcnt : ltac2:(tb__ "0|0|
S26S10Q40S2dVrho;S2eVS;ZcA2A2A2S1eA2").
Hypothesis Hov : ltac2:(tb__ "0|1|
S26S27S10Q40M0S2dVrho;S2eVS;ZbA2A2A2S10G0S2dVrho;S2eVS;ZcA2A2A2A2S1cA2").
Hypothesis Hnth : ltac2:(tb__ "0|0|
S0S4S31A1S70S31S35VS;A1Vk;A3S6S31S33Vbase;Velo;Vehi;Vcells;Vd;A5A2A3").
Hypothesis Hdw : dflt_writable d = true.
Hypothesis Hbuf : ltac2:(tb__ "0|1|
S0S13S10Q40M0S2dVrho;S2eVS;ZbA2A2A2S27S10G0S2dVrho;Vbase;A2A2S30Vrho;Velo;A2A2A3").
Definition rd_bs : list byte := ltac2:(tb__ "0|1|
S72SfQ8A1M0S29S10Q40S2dVrho;S2eVS;ZcA2A2A2A1S73G0S29Voff;A1Vdata;A3A3").
Hypothesis Hlen : ltac2:(tb__ "0|0|
S0S13S2bS30Vrho;Vehi;A2S30Vrho;Velo;A2A2S28S8SfQ8A1S53A2A1A3").
Hypothesis Hnorl : ltac2:(tb__ "0|0|
S0SaS61Vl;VS;A2SbA3").
Hypothesis Hnob : ltac2:(tb__ "0|0|
S0SaS5fVl;Vbase;A2SbA3").
Hypothesis Hnolo : ltac2:(tb__ "0|0|
S0SaS5fVl;Velo;A2SbA3").
Hypothesis Hnohi : ltac2:(tb__ "0|0|
S0SaS5fVl;Vehi;A2SbA3").
Hypothesis Hw : ltac2:(tb__ "0|2|
S5S18A1M0S49S16S5bVsegs;Vrho;VS;S7G0S51R3S52R2R1A2A4A4S3S0S4S5SfQ8A1A1M1A1S1dS4cVsegs;R3A2S2dVrho;S2eVS;ZbA2A2S2dVrho;S2eVS;ZcA2A2A3S9G1A1A3A1F_;Fmd;Fms;Ftr;").

Definition rd_rho' : valuation := ltac2:(tb__ "0|0|
S5cS60Vrho;Vl;S53A3S34VS;A1S68SfQ8A1S53A2A3").
Definition rd_S' : sstate := ltac2:(tb__ "0|0|
S78VS;S76S31S35VS;A1Vk;S33Vbase;Velo;Vehi;SdS2fA1S43Vl;A1A5A4A2").
Definition rd_md' (md : Model) : Model := ltac2:(tb__ "0|1|
S20S23S17Vmd;A1S11Q40M0Z3A2S1aVp;S12G0S11G0Voff;A2S68SfQ8A1S53A2A3A2A3Vmd;A2").

Lemma rd_bs_len : ltac2:(tb__ "0|0|
S26S28S8SfQ8A1S53A2A1S10Q40S2dVrho;S2eVS;ZcA2A2A2A2").
Proof using Hoff. unfold rd_bs. rewrite length_firstn. pose proof (bv_unsigned_in_range 64 (eval rho (reg_sv S 12))). lia. Qed.

Lemma rd_rho'_rw : ltac2:(tb__ "0|0|
S14S6aR1S34VS;A1A2S0SfQ40A1S3aS54R2A2S3aVrho;R2A2A3F_;Fi;").
Proof using Hoff. intros i Hi0. unfold rd_rho'. cbn. destruct (Pos.eqb_spec i (ss_next S)); [lia|]. reflexivity. Qed.
Lemma rd_rho'_nx : ltac2:(tb__ "0|0|
S0SfQ40A1S3aS54S34VS;A1A2S68SfQ8A1S53A2A3").
Proof using . unfold rd_rho'. cbn. rewrite Pos.eqb_refl. reflexivity. Qed.
Lemma rd_rho'_rl : ltac2:(tb__ "0|0|
S14S3S0S14R1Vl;A3A1S0S5SfQ8A1A1S40S54R2A2S40Vrho;R2A2A3F_;Fi;").
Proof using . intros i Hi0. unfold rd_rho'. cbn. destruct (Pos.eqb_spec i l); [congruence|reflexivity]. Qed.
Lemma rd_rho'_l : ltac2:(tb__ "0|0|
S0S5SfQ8A1A1S40S54Vl;A2S53A3").
Proof using . unfold rd_rho'. cbn. rewrite Pos.eqb_refl. reflexivity. Qed.
Lemma rd_rho'_rm : ltac2:(tb__ "0|0|
S0SfQ40A1S4SfQ8A1A1F_;S41S54A1S41Vrho;A1A3").
Proof using . reflexivity. Qed.

Lemma read_file_core : ltac2:(tb__ "0|c|
S5S18A1M0S49S16S5bVsegs;Vrho;VS;S7G0S51R3S52R2R1A2A4A4S0S4S15A1M1S19S17R2A1S11Q40M2Z3A2A2S6S15S1aVp;S11G2Voff;A2M3A2A2M4A3S0S4S5SfQ8A1M5A1M6A1M7S57S1bR3A1Vp;A2S6G6Vdata;A2A3S2SfG2A1M8G8S2G6G6S1S0S4G8A1S4fR7A1S6G8R2A2A3S1S0S13S10G2R2A2Z3fA3S1S6bR6A1S1S0G1S19S17R6A1S74S4aR7U0A2A1A2G4A3S1S0G7S1dS4cVsegs;R7A2S4aR7U1A2M9S4aR7U2A2MaA3S6G6R1A2A3S1S26S10G2GaA2MbS1eA2S1S26S27S10G2G9A2GbA2S1cA2S1S0G6S58Vdata;G3GaA3S53A3S38Vsegs;S54S55S7G0S51R8S52S79R7S68G5S53A2S4dS4bR7A1G9S53A3A3S56R6A1A2A4A4A2A2A2A2A2A2A2A2Lwdst;A2Lx8;A2F_;F_;F_;Fmd;Fms;Ftr;").
Proof using H10 H17 Hbuf Hcnt Hdw Hlen Hnob Hnohi Hnolo Hnorl Hnth Hoff Hw Hov.
  intros tr ms md Hsp Hfd Hfs.
  pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pending_gpr segs _ _ _ _ _ 0 Hsp ltac:(lia)) as G0. change (10 + Z.of_nat 0) with 10 in G0. rewrite H10 in G0. cbn [eval] in G0.
  pose proof (smatch_pending_gpr segs _ _ _ _ _ 1 Hsp ltac:(lia)) as G1. change (10 + Z.of_nat 1) with 11 in G1.
  pose proof (smatch_pending_gpr segs _ _ _ _ _ 2 Hsp ltac:(lia)) as G2. change (10 + Z.of_nat 2) with 12 in G2.
  destruct (read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) (ms_gpr ms 2)) as [wdst|] eqn:Ewd.
  2:{ exfalso. apply (Hw tr ms md Hsp). rewrite <- G1, <- G2. exact Ewd. }
  exists (Z_to_bv 64 63), wdst.
  assert (Hbs : file_read data (Z_to_bv 64 off) (ms_gpr ms 2) = rd_bs).
  { unfold rd_bs. rewrite file_read_unguarded. unfold word_to_nat. rewrite G2. f_equal. f_equal. f_equal. apply Z_to_bv_small.
    rewrite two64. exact Hoff. }
  split; [exact Hp|]. split; [reflexivity|]. split; [exact Hh|]. split; [rewrite G0, fd32_3; exact Hfd|]. split; [reflexivity|].
  split; [rewrite G2; lia|]. split; [rewrite G1, G2; exact Hov|]. split; [exact Hbs|].
  unfold rd_S', S_after_var, rd_rho'.
  assert (Hsp' : smatch_pending segs (rho_set_rl rho l rd_bs) S (tr, mkCfg ms md)) by (apply smatch_pending_set_rl; [exact Hnorl | exact Hsp]).
  eapply (smatch_after_kwrite_full segs (rho_set_rl rho l rd_bs) S tr ms md tr _ (len_word rd_bs) k base elo ehi
            (soff rho elo) (soff rho ehi) cells d l (ms_gpr ms 1) rd_bs Hsp');
    [apply with_fds_idle; exact Hh | exact Hnth | exact Hdw | apply soff_set_rl; exact Hnolo | apply soff_set_rl; exact Hnohi | | exact (eq_sym Hlen) | apply rho_set_rl_at].
  rewrite (eval_set_rl rho l rd_bs base Hnob), G1. exact Hbuf.
Qed.

Theorem triple1_read_fileJ : ltac2:(tb__ "0|3|
S6eOF_;S47S47S48Vsegs;R3R2A3S5eVsegs;R4R3A3S5S18A1M0S16R6Vrho;R2R1A3S1S0S4S15A1S19S17R2A1S11Q40M1Z3A2A2S6S15S1aVp;S11G1Voff;A2A2A2A3S0S4S5SfQ8A1A1M2A1S57S1bR2A1Vp;A2S6G2Vdata;A2A3A2F_;Fmd;Ftr;G0S16R7Vrho;R2R1A3R7S54R3S56R2A1A3F_;Fmd;Ftr;S6dVsegs;R7S46Vsegs;R6VS;Vrho;A4S46Vsegs;R5S55S54A4A4F_;F_;F_;F_;FJ';FJ;Fok;").
Proof using H10 H17 Hbuf Hcnt Hdw Hi Hlen Hnob Hnohi Hnolo Hnorl Hnth Hoff Hw Hov.
  intros ok J J' Hokf Hokp HJfd HK.
  apply triple1_ecall_detJ; [exact Hokf | exact Hi |].
  intros tr ms md Hsp Hk. destruct (HJfd tr md Hk) as [Hfd Hfs].
  destruct (read_file_core tr ms md Hsp Hfd Hfs) as (x8 & wdst & Hp & H63 & Hh & Hfd' & Ewd & Hc2 & Hc3 & Hbs & Hsm').
  split.
  - eapply Hokp; [exact Hk | exact Hp |]. exact (@read_file_only_ok segs ms md x8 p (Z_to_bv 64 off) data wdst Hh H63 Hfd' Hfs Ewd Hc2 Hc3).
  - intros w' Hst.
    pose proof (@wstep_read_file_inv segs tr ms md x8 p (Z_to_bv 64 off) data wdst w' Hp Hh H63 Hfd' Hfs Ewd Hc2 Hc3 Hst) as ->.
    cbn zeta. rewrite Hbs. split; [exact Hsm'|].
    cbn [w_tr w_cfg cfg_model fst snd].
    replace (fd32 (ms_gpr ms 0)) with (Z_to_bv 64 3).
    2:{ pose proof (smatch_pending_gpr segs _ _ _ _ _ 0 Hsp ltac:(lia)) as G0. change (10 + Z.of_nat 0) with 10 in G0. rewrite H10 in G0. cbn [eval] in G0. rewrite G0, fd32_3. reflexivity. }
    apply HK. exact Hk.
Qed.

Theorem etriple_read_fileJ : ltac2:(tb__ "0|3|
S47S47S5S18A1M0S16R4Vrho;R2R1A3S1S0S4S15A1S19S17R2A1S11Q40M1Z3A2A2S6S15S1aVp;S11G1Voff;A2A2A2A3S0S4S5SfQ8A1A1M2A1S57S1bR2A1Vp;A2S6G2Vdata;A2A3A2F_;Fmd;Ftr;G0S16R5Vrho;R2R1A3R5S54R3S56R2A1A3F_;Fmd;Ftr;S6cVsegs;S46Vsegs;R4VS;Vrho;A4S46Vsegs;R3S55S54A4A3F_;F_;FJ';FJ;").
Proof using H10 H17 Hbuf Hcnt Hdw Hi Hlen Hnob Hnohi Hnolo Hnorl Hnth Hoff Hw Hov.
  intros J J' HJfd HK.
  apply etriple_ecall_detJ; [exact Hi |].
  intros tr ms md Hsp Hk. destruct (HJfd tr md Hk) as [Hfd Hfs].
  destruct (read_file_core tr ms md Hsp Hfd Hfs) as (x8 & wdst & Hp & H63 & Hh & Hfd' & Ewd & Hc2 & Hc3 & Hbs & Hsm').
  eexists. split; [exact (@wstep_read_file_intro segs tr ms md x8 p (Z_to_bv 64 off) data wdst Hp Hh H63 Hfd' Hfs Ewd Hc2 Hc3)|].
  cbn zeta. rewrite Hbs. split; [exact Hsm'|].
  cbn [w_tr w_cfg cfg_model fst snd].
  replace (fd32 (ms_gpr ms 0)) with (Z_to_bv 64 3).
  2:{ pose proof (smatch_pending_gpr segs _ _ _ _ _ 0 Hsp ltac:(lia)) as G0. change (10 + Z.of_nat 0) with 10 in G0. rewrite H10 in G0. cbn [eval] in G0. rewrite G0, fd32_3. reflexivity. }
  apply HK. exact Hk.
Qed.
End ReadFile.

Section ReadBuf.
Variable S : sstate.
Variable rho : valuation.
Variable k : nat.
Variables base elo ehi : sv.
Variable cells : list cell.
Variables p data : list byte.
Variable off : Z.

Variable woff : Z.
Hypothesis Hi : ltac2:(tb__ "0|0|
S0S4S59A1S75Vsegs;S3bVS;A1A2S6S59S5aA2A3").
Hypothesis H17 : reg_sv S 17 = SLit 63.
Hypothesis H10 : reg_sv S 10 = SLit 3.
Hypothesis Hoff : 0 <= off < 2 ^ 64.

Hypothesis Hcnt : ltac2:(tb__ "0|0|
S26S10Q40S2dVrho;S2eVS;ZcA2A2A2S1eA2").
Hypothesis Hov : ltac2:(tb__ "0|1|
S26S27S10Q40M0S2dVrho;S2eVS;ZbA2A2A2S10G0S2dVrho;S2eVS;ZcA2A2A2A2S1cA2").
Hypothesis Hnth : ltac2:(tb__ "0|0|
S0S4S31A1S70S31S35VS;A1Vk;A3S6S31S33Vbase;Velo;Vehi;Vcells;S36A5A2A3").
Hypothesis Hbuf : ltac2:(tb__ "0|1|
S0S13S10Q40M0S2dVrho;S2eVS;ZbA2A2A2S27S10G0S2dVrho;Vbase;A2A2Vwoff;A2A3").
Definition rb_bs : list byte := ltac2:(tb__ "0|1|
S72SfQ8A1M0S29S10Q40S2dVrho;S2eVS;ZcA2A2A2A1S73G0S29Voff;A1Vdata;A3A3").
Hypothesis Hlo : ltac2:(tb__ "0|0|
S26S30Vrho;Velo;A2Vwoff;A2").

Hypothesis Hhi : ltac2:(tb__ "0|0|
S26S27Vwoff;S10Q40S2dVrho;S2eVS;ZcA2A2A2A2S30Vrho;Vehi;A2A2").
Hypothesis Hcells : ltac2:(tb__ "0|0|
S71S2fS2fS26S27S30Vrho;S3dR1A1A2S3eR1A1A2Vwoff;A2Lc;Vcells;A3").

Definition rb_md' (md : Model) : Model := ltac2:(tb__ "0|1|
S20S23S17Vmd;A1S11Q40M0Z3A2S1aVp;S12G0S11G0Voff;A2S68SfQ8A1S62A2A3A2A3Vmd;A2").

Lemma rb_bs_len : ltac2:(tb__ "0|0|
S26S28S8SfQ8A1S62A2A1S10Q40S2dVrho;S2eVS;ZcA2A2A2A2").
Proof using Hoff. unfold rb_bs. rewrite length_firstn. pose proof (bv_unsigned_in_range 64 (eval rho (reg_sv S 12))). lia. Qed.

Lemma rb_writable : ltac2:(tb__ "0|2|
S5S18A1M0S49S16S5bVsegs;Vrho;VS;S7G0S51R3S52R2R1A2A4A4S3S0S4S5SfQ8A1A1M1A1S1dS4cVsegs;R3A2S2dVrho;S2eVS;ZbA2A2S2dVrho;S2eVS;ZcA2A2A3S9G1A1A3A1F_;Fmd;Fms;Ftr;").
Proof using Hbuf Hhi Hlo Hnth.
  intros tr ms md Hsp.
  pose proof (mem_match_nth segs _ _ _ _ _ (smatch_pending_mem segs _ _ _ _ _ Hsp) Hnth) as Ho.
  apply (writable_range_obj segs rho ms _ _ _ woff Ho eq_refl); [cbn [ob_base]; exact Hbuf | unfold obj_lo_of; cbn; exact Hlo | unfold obj_hi_of; cbn; exact Hhi].
Qed.

Lemma read_buf_core : ltac2:(tb__ "0|d|
S5S18A1M0S49S16S5bVsegs;Vrho;VS;S7G0S51R3S52R2R1A2A4A4S0S4S15A1M1S19S17R2A1S11Q40M2Z3A2M3A2S6S15S1aVp;S11G2Voff;A2M4A2A2M5A3S0S4S5SfQ8A1A1M6A1M7S57S1bR3A1Vp;A2S6G6Vdata;A2A3S2SfG2A1M8G8S2G6G6S1S0S4G8A1S4fR7A1S6G8R2A2A3S1S0S13S10G2R2A2Z3fA3S1S6bR6A1S1S0G1S19S17R6A1S74S4aR7U0A2A1M9A2G5A3S1S0G7S1dS4cVsegs;R7A2S4aR7U1A2MaS4aR7U2A2MbA3S6G6R1A2A3S1S26S10G2GbA2McS1eA2S1S26S27S10G2GaA2GcA2S1cA2S1S0G6S58Vdata;G4GbA3S62A3S1S0G8GaS2dVrho;S2eVS;ZbA2A2A3S0G8G9G3A3A2A2A2A2A2A2A2A2A2Lwdst;A2Lx8;A2F_;F_;F_;Fmd;Fms;Ftr;").
Proof using H10 H17 Hbuf Hcnt Hhi Hlo Hnth Hoff Hov.
  intros tr ms md Hsp Hfd Hfs.
  pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pending_gpr segs _ _ _ _ _ 0 Hsp ltac:(lia)) as G0. change (10 + Z.of_nat 0) with 10 in G0. rewrite H10 in G0. cbn [eval] in G0.
  pose proof (smatch_pending_gpr segs _ _ _ _ _ 1 Hsp ltac:(lia)) as G1. change (10 + Z.of_nat 1) with 11 in G1.
  pose proof (smatch_pending_gpr segs _ _ _ _ _ 2 Hsp ltac:(lia)) as G2. change (10 + Z.of_nat 2) with 12 in G2.
  destruct (read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) (ms_gpr ms 2)) as [wdst|] eqn:Ewd.
  2:{ exfalso. apply (rb_writable tr ms md Hsp). rewrite <- G1, <- G2. exact Ewd. }
  exists (Z_to_bv 64 63), wdst.
  assert (Hbs : file_read data (Z_to_bv 64 off) (ms_gpr ms 2) = rb_bs).
  { unfold rb_bs. rewrite file_read_unguarded. unfold word_to_nat. rewrite G2. f_equal. f_equal. f_equal. apply Z_to_bv_small.
    rewrite two64. exact Hoff. }
  split; [exact Hp|]. split; [reflexivity|]. split; [exact Hh|]. split; [rewrite G0, fd32_3; exact Hfd|]. split; [reflexivity|].
  split; [rewrite G2; lia|]. split; [rewrite G1, G2; exact Hov|]. split; [exact Hbs|]. split; [exact G1 | rewrite G0, fd32_3; reflexivity].
Qed.

Definition rk_rho' : valuation := ltac2:(tb__ "0|0|
S5cVrho;S34VS;A1S68SfQ8A1S62A2A3").
Definition rk_S' : sstate := ltac2:(tb__ "0|0|
S78VS;S35VS;A1A2").

Theorem triple1_read_keepJ : ltac2:(tb__ "0|3|
S6eOF_;S47S47S48Vsegs;R3R2A3S5eVsegs;R4R3A3S5S18A1M0S16R6Vrho;R2R1A3S1S0S4S15A1S19S17R2A1S11Q40M1Z3A2A2S6S15S1aVp;S11G1Voff;A2A2A2A3S0S4S5SfQ8A1A1M2A1S57S1bR2A1Vp;A2S6G2Vdata;A2A3A2F_;Fmd;Ftr;G0S16R7Vrho;R2R1A3R7S65R3S63R2A1A3F_;Fmd;Ftr;S6dVsegs;R7S46Vsegs;R6VS;Vrho;A4S46Vsegs;R5S67S65A4A4F_;F_;F_;F_;FJ';FJ;Fok;").
Proof using H10 H17 Hbuf Hcells Hcnt Hhi Hi Hlo Hnth Hoff Hov.
  intros ok J J' Hokf Hokp HJfd HK.
  apply triple1_ecall_detJ; [exact Hokf | exact Hi |].
  intros tr ms md Hsp Hk. destruct (HJfd tr md Hk) as [Hfd Hfs].
  destruct (read_buf_core tr ms md Hsp Hfd Hfs) as (x8 & wdst & Hp & H63 & Hh & Hfd' & Ewd & Hc2 & Hc3 & Hbs & G1 & G0).
  split.
  - eapply Hokp; [exact Hk | exact Hp |]. exact (@read_file_only_ok segs ms md x8 p (Z_to_bv 64 off) data wdst Hh H63 Hfd' Hfs Ewd Hc2 Hc3).
  - intros w' Hst.
    pose proof (@wstep_read_file_inv segs tr ms md x8 p (Z_to_bv 64 off) data wdst w' Hp Hh H63 Hfd' Hfs Ewd Hc2 Hc3 Hst) as ->.
    cbn zeta. rewrite Hbs, G0. split; [|apply HK; exact Hk].
    unfold rk_S', rk_rho', S_after_var.
    eapply (smatch_after_kwrite_keep rho S tr ms md tr _ (len_word rb_bs) k base elo ehi (soff rho elo) (soff rho ehi) cells (ms_gpr ms 1) rb_bs woff Hsp);
      [apply with_fds_idle; exact Hh | exact Hnth | reflexivity | reflexivity | rewrite G1; exact Hbuf | exact Hlo | pose proof rb_bs_len; lia | exact Hcells].
Qed.

Theorem etriple_read_keepJ : ltac2:(tb__ "0|3|
S47S47S5S18A1M0S16R4Vrho;R2R1A3S1S0S4S15A1S19S17R2A1S11Q40M1Z3A2A2S6S15S1aVp;S11G1Voff;A2A2A2A3S0S4S5SfQ8A1A1M2A1S57S1bR2A1Vp;A2S6G2Vdata;A2A3A2F_;Fmd;Ftr;G0S16R5Vrho;R2R1A3R5S65R3S63R2A1A3F_;Fmd;Ftr;S6cVsegs;S46Vsegs;R4VS;Vrho;A4S46Vsegs;R3S67S65A4A3F_;F_;FJ';FJ;").
Proof using H10 H17 Hbuf Hcells Hcnt Hhi Hi Hlo Hnth Hoff Hov.
  intros J J' HJfd HK.
  apply etriple_ecall_detJ; [exact Hi |].
  intros tr ms md Hsp Hk. destruct (HJfd tr md Hk) as [Hfd Hfs].
  destruct (read_buf_core tr ms md Hsp Hfd Hfs) as (x8 & wdst & Hp & H63 & Hh & Hfd' & Ewd & Hc2 & Hc3 & Hbs & G1 & G0).
  eexists. split; [exact (@wstep_read_file_intro segs tr ms md x8 p (Z_to_bv 64 off) data wdst Hp Hh H63 Hfd' Hfs Ewd Hc2 Hc3)|].
  cbn zeta. rewrite Hbs, G0. split; [|apply HK; exact Hk].
  unfold rk_S', rk_rho', S_after_var.
  eapply (smatch_after_kwrite_keep rho S tr ms md tr _ (len_word rb_bs) k base elo ehi (soff rho elo) (soff rho ehi) cells (ms_gpr ms 1) rb_bs woff Hsp);
    [apply with_fds_idle; exact Hh | exact Hnth | reflexivity | reflexivity | rewrite G1; exact Hbuf | exact Hlo | pose proof rb_bs_len; lia | exact Hcells].
Qed.

Hypothesis Hcells0 : cells = [].
Hypothesis Hwoff : ltac2:(tb__ "0|0|
S0S13Vwoff;S30Vrho;Velo;A2A3").
Definition rh_rho' : valuation := ltac2:(tb__ "0|1|
S5cS5cVrho;S34VS;A1M0S77S62A1A3S69G0A1S68SfQ8A1S62A2A3").
Definition rh_S' : sstate := ltac2:(tb__ "0|2|
S5dVS;S37S69S34VS;A1M0A1M1A1S76S31S35VS;A1Vk;S33Vbase;Velo;Vehi;SeS2fS3fVelo;Z4S37G0A1A3SdS2fA1A3S36A5A4S69G1A1A4").

Theorem triple1_read_hdrJ : ltac2:(tb__ "0|4|
S6eOF_;S47S47S48Vsegs;R3R2A3S5eVsegs;R4R3A3S6fU4S8SfQ8A1M0S62A2A2S5S18A1M1S16R7Vrho;R2R1A3S1S0S4S15A1S19S17R2A1S11Q40M2Z3A2A2S6S15S1aVp;S11G2Voff;A2A2A2A3S0S4S5G0A1M3A1S57S1bR2A1Vp;A2S6G3Vdata;A2A3A2F_;Fmd;Ftr;G1S16R8Vrho;R2R1A3R8S64R3S63R2A1A3F_;Fmd;Ftr;S6dVsegs;R8S46Vsegs;R7VS;Vrho;A4S46Vsegs;R6S66S64A4A4F_;F_;F_;F_;F_;FJ';FJ;Fok;").
Proof using H10 H17 Hbuf Hcells Hcells0 Hcnt Hhi Hi Hlo Hnth Hoff Hwoff Hov.
  intros ok J J' Hokf Hokp H4 HJfd HK.
  apply triple1_ecall_detJ; [exact Hokf | exact Hi |].
  intros tr ms md Hsp Hk. destruct (HJfd tr md Hk) as [Hfd Hfs].
  destruct (read_buf_core tr ms md Hsp Hfd Hfs) as (x8 & wdst & Hp & H63 & Hh & Hfd' & Ewd & Hc2 & Hc3 & Hbs & G1 & G0).
  split.
  - eapply Hokp; [exact Hk | exact Hp |]. exact (@read_file_only_ok segs ms md x8 p (Z_to_bv 64 off) data wdst Hh H63 Hfd' Hfs Ewd Hc2 Hc3).
  - intros w' Hst.
    pose proof (@wstep_read_file_inv segs tr ms md x8 p (Z_to_bv 64 off) data wdst w' Hp Hh H63 Hfd' Hfs Ewd Hc2 Hc3 Hst) as ->.
    cbn zeta. rewrite Hbs, G0. split; [|apply HK; exact Hk].
    unfold rh_S', rh_rho'. subst cells.
    eapply (smatch_after_kwrite_hdr rho S tr ms md tr _ (len_word rb_bs) k base elo ehi (soff rho elo) (soff rho ehi) (ms_gpr ms 1) rb_bs Hsp);
      [apply with_fds_idle; exact Hh | exact Hnth | reflexivity | reflexivity | rewrite G1, <- Hwoff; exact Hbuf | pose proof rb_bs_len; lia | exact H4].
Qed.

Theorem etriple_read_hdrJ : ltac2:(tb__ "0|4|
S47S47S6fU4S8SfQ8A1M0S62A2A2S5S18A1M1S16R5Vrho;R2R1A3S1S0S4S15A1S19S17R2A1S11Q40M2Z3A2A2S6S15S1aVp;S11G2Voff;A2A2A2A3S0S4S5G0A1M3A1S57S1bR2A1Vp;A2S6G3Vdata;A2A3A2F_;Fmd;Ftr;G1S16R6Vrho;R2R1A3R6S64R3S63R2A1A3F_;Fmd;Ftr;S6cVsegs;S46Vsegs;R5VS;Vrho;A4S46Vsegs;R4S66S64A4A3F_;F_;F_;FJ';FJ;").
Proof using H10 H17 Hbuf Hcells Hcells0 Hcnt Hhi Hi Hlo Hnth Hoff Hwoff Hov.
  intros J J' H4 HJfd HK.
  apply etriple_ecall_detJ; [exact Hi |].
  intros tr ms md Hsp Hk. destruct (HJfd tr md Hk) as [Hfd Hfs].
  destruct (read_buf_core tr ms md Hsp Hfd Hfs) as (x8 & wdst & Hp & H63 & Hh & Hfd' & Ewd & Hc2 & Hc3 & Hbs & G1 & G0).
  eexists. split; [exact (@wstep_read_file_intro segs tr ms md x8 p (Z_to_bv 64 off) data wdst Hp Hh H63 Hfd' Hfs Ewd Hc2 Hc3)|].
  cbn zeta. rewrite Hbs, G0. split; [|apply HK; exact Hk].
  unfold rh_S', rh_rho'. subst cells.
  eapply (smatch_after_kwrite_hdr rho S tr ms md tr _ (len_word rb_bs) k base elo ehi (soff rho elo) (soff rho ehi) (ms_gpr ms 1) rb_bs Hsp);
    [apply with_fds_idle; exact Hh | exact Hnth | reflexivity | reflexivity | rewrite G1, <- Hwoff; exact Hbuf | pose proof rb_bs_len; lia | exact H4].
Qed.
End ReadBuf.

Section ReadDir.
Variable S : sstate.
Variable rho : valuation.
Hypothesis Hi : ltac2:(tb__ "0|0|
S0S4S59A1S75Vsegs;S3bVS;A1A2S6S59S5aA2A3").
Hypothesis H17 : reg_sv S 17 = SLit 63.
Hypothesis H10 : reg_sv S 10 = SLit 3.

Hypothesis Hov : ltac2:(tb__ "0|1|
S26S27S10Q40M0S2dVrho;S2eVS;ZbA2A2A2S10G0S2dVrho;S2eVS;ZcA2A2A2A2S1cA2").

Definition dir_S' : sstate := S_after_lit S (2 ^ 64 - 21).

Lemma read_dir_core : ltac2:(tb__ "0|5|
S5S18A1M0S49S16S5bVsegs;Vrho;VS;S7G0S51R3S52R2R1A2A4A4S0S4S15A1M1S19S17R2A1S11Q40M2Z3A2A2S6S15S1fA2M3A3S2SfG2A1M4G4S1S0S4G4A1S4fR5A1S6G4R1A2A3S1S0S13S10G2R1A2Z3fA3S1S6bR4A1S1S0G1S19S17R4A1S74S4aR5U0A2A1A2G3A3S1S26S27S10G2S4aR5U1A2A2S10G2S4aR5U2A2A2A2S1cA2S38Vsegs;Vrho;S7eS7G0S51R6S52S7aR5S22S21A1A2R4A2A4A4A2A2A2A2A2Lx8;A2F_;F_;Fmd;Fms;Ftr;").
Proof using H10 H17 Hov.
  intros tr ms md Hsp Hfd.
  pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pending_gpr segs _ _ _ _ _ 0 Hsp ltac:(lia)) as G0. change (10 + Z.of_nat 0) with 10 in G0. rewrite H10 in G0. cbn [eval] in G0.
  pose proof (smatch_pending_gpr segs _ _ _ _ _ 1 Hsp ltac:(lia)) as G1. change (10 + Z.of_nat 1) with 11 in G1.
  pose proof (smatch_pending_gpr segs _ _ _ _ _ 2 Hsp ltac:(lia)) as G2. change (10 + Z.of_nat 2) with 12 in G2.
  exists (Z_to_bv 64 63).
  split; [exact Hp|]. split; [reflexivity|]. split; [exact Hh|]. split; [rewrite G0, fd32_3; exact Hfd|].
  split; [rewrite G1, G2; exact Hov|].
  unfold dir_S', S_after_lit. rewrite <- errno_EISDIR. apply (smatch_after_ret_lit segs rho S tr ms md); [exact Hsp | exact Hh].
Qed.

Theorem triple1_read_dirJ : ltac2:(tb__ "0|1|
S6eOF_;S47S47S48Vsegs;R3R2A3S5eVsegs;R4R3A3S5S18A1M0S16R6Vrho;R2R1A3S0S4S15A1S19S17R2A1S11Q40Z3A2A2S6S15S1fA2A3F_;Fmd;Ftr;G0S16R7Vrho;R2R1A3R7Vrho;R3R2A3F_;Fmd;Ftr;S6dVsegs;R7S46Vsegs;R6VS;Vrho;A4S46Vsegs;R5S7eVrho;A4A4F_;F_;F_;F_;FJ';FJ;Fok;").
Proof using H10 H17 Hi Hov.
  intros ok J J' Hokf Hokp HJfd HK.
  apply triple1_ecall_detJ; [exact Hokf | exact Hi |].
  intros tr ms md Hsp Hk.
  destruct (read_dir_core tr ms md Hsp (HJfd tr md Hk)) as (x8 & Hp & H63 & Hh & Hfd' & Hc3 & Hsm').
  split.
  - eapply Hokp; [exact Hk | exact Hp |]. exact (@read_dir_only_ok segs ms md x8 Hh H63 Hfd' Hc3).
  - intros w' Hst.
    pose proof (@wstep_read_dir_inv segs tr ms md x8 w' Hp Hh H63 Hfd' Hc3 Hst) as ->.
    split; [exact Hsm' | apply HK; exact Hk].
Qed.

Theorem etriple_read_dirJ : ltac2:(tb__ "0|1|
S47S47S5S18A1M0S16R4Vrho;R2R1A3S0S4S15A1S19S17R2A1S11Q40Z3A2A2S6S15S1fA2A3F_;Fmd;Ftr;G0S16R5Vrho;R2R1A3R5Vrho;R3R2A3F_;Fmd;Ftr;S6cVsegs;S46Vsegs;R4VS;Vrho;A4S46Vsegs;R3S7eVrho;A4A3F_;F_;FJ';FJ;").
Proof using H10 H17 Hi Hov.
  intros J J' HJfd HK.
  apply etriple_ecall_detJ; [exact Hi |].
  intros tr ms md Hsp Hk.
  destruct (read_dir_core tr ms md Hsp (HJfd tr md Hk)) as (x8 & Hp & H63 & Hh & Hfd' & Hc3 & Hsm').
  eexists. split; [exact (@wstep_read_dir_intro segs tr ms md x8 Hp Hh H63 Hfd' Hc3)|].
  split; [exact Hsm' | apply HK; exact Hk].
Qed.
End ReadDir.

Section Close.
Variable S : sstate.
Variable rho : valuation.
Hypothesis Hi : ltac2:(tb__ "0|0|
S0S4S59A1S75Vsegs;S3bVS;A1A2S6S59S5aA2A3").
Hypothesis H17 : reg_sv S 17 = SLit 57.
Hypothesis H10 : reg_sv S 10 = SLit 3.

Definition close_S' : sstate := S_after_lit S 0.
Definition close_md' (md : Model) : Model := ltac2:(tb__ "0|0|
S20S24S17Vmd;A1S11Q40Z3A2A2Vmd;A2").

Lemma close_core : ltac2:(tb__ "0|5|
S5S18A1M0S49S16S15S5bVsegs;Vrho;VS;S7G0S51R4S52R3R2A2A4A4S0S4S15A1M1S19S17R3A1S11Q40M2Z3A2A2S6S15R2A2A3S2SfG2A1M3G3S1S0S4G3A1S4fR6A1S6G3R1A2A3S1S0S13S10G2R1A2Z39A3S1S6bR5A1S1S0G1S19S17R5A1S74S4aR6U0A2A1A2S6S15R4A2A3S1S0S16S7bR6R5A2S7dR5A1M4A3S38Vsegs;Vrho;S7cS7G0S51R7S52S7aR6S11G2Z0A2A2G4A2A4A4A2A2A2A2A2Lx8;A2F_;F_;Fe;Fmd;Fms;Ftr;").
Proof using H10 H17.
  intros tr ms md e Hsp Hfd.
  pose proof (smatch_pending_pending segs _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pending_halted segs _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pending_gpr segs _ _ _ _ _ 0 Hsp ltac:(lia)) as G0. change (10 + Z.of_nat 0) with 10 in G0. rewrite H10 in G0. cbn [eval] in G0.
  exists (Z_to_bv 64 57).
  split; [exact Hp|]. split; [reflexivity|]. split; [exact Hh|]. split; [rewrite G0, fd32_3; exact Hfd|].
  split; [unfold closed_model, close_md'; rewrite G0, fd32_3; reflexivity|].
  unfold close_S', S_after_lit. change 0 with (bv_unsigned (Z_to_bv 64 0)).
  apply (smatch_after_ret_lit segs rho S tr ms md); [exact Hsp | apply with_fds_idle; exact Hh].
Qed.

Theorem triple1_closeJ : ltac2:(tb__ "0|1|
S6eOF_;S47S47S48Vsegs;R3R2A3S5eVsegs;R4R3A3S5S18A1M0S16R6Vrho;R2R1A3S2S15S15S0S4S15A1S19S17R3A1S11Q40Z3A2A2S6S15R1A2A3Le;A2F_;Fmd;Ftr;G0S16R7Vrho;R2R1A3R7Vrho;R3S7dR2A1A3F_;Fmd;Ftr;S6dVsegs;R7S46Vsegs;R6VS;Vrho;A4S46Vsegs;R5S7cVrho;A4A4F_;F_;F_;F_;FJ';FJ;Fok;").
Proof using H10 H17 Hi.
  intros ok J J' Hokf Hokp HJfd HK.
  apply triple1_ecall_detJ; [exact Hokf | exact Hi |].
  intros tr ms md Hsp Hk. destruct (HJfd tr md Hk) as [e Hfd].
  destruct (close_core tr ms md e Hsp Hfd) as (x8 & Hp & H57 & Hh & Hfd' & Hcm & Hsm').
  split.
  - eapply Hokp; [exact Hk | exact Hp |]. exact (@close_only_ok segs ms md x8 e Hh H57 Hfd').
  - intros w' Hst.
    pose proof (@wstep_close_inv segs tr ms md x8 e w' Hp Hh H57 Hfd' Hst) as ->. rewrite Hcm.
    split; [exact Hsm' | apply HK; exact Hk].
Qed.

Theorem etriple_closeJ : ltac2:(tb__ "0|1|
S47S47S5S18A1M0S16R4Vrho;R2R1A3S2S15S15S0S4S15A1S19S17R3A1S11Q40Z3A2A2S6S15R1A2A3Le;A2F_;Fmd;Ftr;G0S16R5Vrho;R2R1A3R5Vrho;R3S7dR2A1A3F_;Fmd;Ftr;S6cVsegs;S46Vsegs;R4VS;Vrho;A4S46Vsegs;R3S7cVrho;A4A3F_;F_;FJ';FJ;").
Proof using H10 H17 Hi.
  intros J J' HJfd HK.
  apply etriple_ecall_detJ; [exact Hi |].
  intros tr ms md Hsp Hk. destruct (HJfd tr md Hk) as [e Hfd].
  destruct (close_core tr ms md e Hsp Hfd) as (x8 & Hp & H57 & Hh & Hfd' & Hcm & Hsm').
  eexists. split; [exact (@wstep_close_intro segs tr ms md x8 e Hp Hh H57 Hfd')|]. rewrite Hcm.
  split; [exact Hsm' | apply HK; exact Hk].
Qed.
End Close.

End WithSegs.
