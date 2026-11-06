(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Stdio/WMseek.v, with its module paths, module names, addresses and numbers changed; 195 of its 272 lines of code are new or changed and 250 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A (the asan build, pin 059dae63e07c): the walk of musl mseek 0x96dd4 (frame 48) at
   whence = SEEK_SET on link's memory FILE: LinkRwDefs.v amseek_set_realizes at LA_MSEEK for MS = link_amf.

   THE BODY (neutral listing (internal path) (internal record, sha256 9d30009753d4), 39
   instructions), at a2 = 0 (a literal in the symbolic state):
     +0x00..+0x08  addi sp,-48; sd ra,40(sp); sd s0,32(sp)
     +0x0c..+0x1c  s0 = *0xa2658 (the .got cell of the stack guard: 0x651c50); 24(sp) = *s0
     +0x20         bgeu a2,3 -> +0x60: not taken (0 < 3)
     +0x24..+0x2c  a3 = f->cookie (f + 152 holds f + 232); a0 = c->pos (f + 232); a4 = c->len (f + 240)
     +0x34..+0x48  base[] = {0, pos, len} at 0(sp), 8(sp), 16(sp); a0 = base[0] = 0
     +0x50         blt a1,-0 -> +0x60: not taken (entry fact 0 <= off, signed)
     +0x54..+0x5c  a2 = c->size (f + 248 holds 4096) - 0; bge a2,a1 -> +0x8c: taken (entry fact off <= 4096, signed)
     +0x8c..+0x94  a0 = 0 + off; sd a0,0(a3): c->pos = off (the one store outside the frame); j +0x70
     +0x70..+0x78  the guard re-check: both operands are the atom read from 0x651c50 (the cell is read twice, and
                   24(sp) holds the first read), so the engine decides the bne by syntax: not taken
     +0x7c..+0x88  ld ra; ld s0; addi sp,48; ret
   So the EINVAL arm (+0x60 jal ___errno_location 0x90a7c) and the guard-failure call (+0x98 jal __stack_chk_fail
   0x90a74) are not reached: the engine runs from 0x96dd4 to the ret at 0x96e5c with no branch left open
   (ms_run). The engine's stop points without the two facts were read from a probe run: the blt reaches the
   engine as (BC_LT (SOff 11 0) (SLit 0)) at 0x96e24, the bge as (BC_GE (SLit 4096) (SOff 11 0)) at 0x96e30.

   THE STATE. Atoms 0..31 are the registers (a2 pinned to 0), 32 / 33 / 34 the words c->pos, c->len and the
   stack guard (each modulo 2^64: the premises fix them only so). Regions: the 48-byte frame (writable); the
   FILE's words +152..+256 off f, with only c->pos (+232..+240) writable; the .got cell and the guard object
   (read-only). The FILE block [f, f + 1304) is present, not the runtime's and off the image (AMemFile.v
   amf_block_facts), so the cookie cell is writable, the block ends below alloc_ceiling <= ly_stk_lo (apart from
   the stack window), and it lies below 0x10000 or above 0x654000 (apart from the two image cells).

   Copied verbatim from pcap's released A walk of this code, relocated to link's image by a Theorem Labs lane
   (internal path (internal record, sha256 5332f18fa29b)), names changed wms_ -> ms_ and
   msegs -> tfibsegs: ms_seg_table, ms_img_full, ms_blk_off_img, ms_bge. ms_phase is lib/A/AE2y.v icpt_phase over
   this file's code table. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AE2y AE7f.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AMemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMfDefs LinkRwDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* The image: segments and code table.                                                             *)
(* ---------------------------------------------------------------------------------------------- *)
Definition ms_tbl : ctable := build_table tfibsegs LA_MSEEK 39 TEmpty.
Lemma ms_tbl_ok : table_ok tfibsegs ms_tbl.
Proof. apply build_table_ok0. unfold LA_MSEEK. lia. Qed.

(* donor WMseek.v wms_seg_table: four contiguous loaded segments [0x10000, 0x654000) *)
Lemma ms_seg_table :
  map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) tfibsegs =
  [(65536, 135168); (200704, 458752); (659456, 8192); (667648, 5967872)].
Proof. vm_compute. reflexivity. Qed.

(* donor WMseek.v wms_img_full *)
Lemma ms_img_full : forall x, 0x10000 <= x < 0x654000 -> in_img tfibsegs x.
Proof.
  intros x Hx. pose proof ms_seg_table as Hm. unfold in_img.
  destruct tfibsegs as [|s0 [|s1 [|s2 [|s3 [|s4 l]]]]]; cbn [map] in Hm; try discriminate Hm.
  injection Hm as E0 F0 E1 F1 E2 F2 E3 F3.
  destruct (Z_lt_le_dec x 200704).
  { exists s0. split; [left; reflexivity | lia]. }
  destruct (Z_lt_le_dec x 659456).
  { exists s1. split; [right; left; reflexivity | lia]. }
  destruct (Z_lt_le_dec x 667648).
  { exists s2. split; [right; right; left; reflexivity | lia]. }
  exists s3. split; [right; right; right; left; reflexivity | lia].
Qed.

(* donor WMseek.v wms_blk_off_img: a byte range none of whose bytes is in the image lies wholly below or wholly
   above it *)
Lemma ms_blk_off_img : forall p n, 0 < n -> (forall a, p <= a < p + n -> ~ in_img tfibsegs a) ->
  p + n <= 0x10000 \/ 0x654000 <= p.
Proof.
  intros p n Hn H. destruct (Z_le_gt_dec (p + n) 0x10000) as [L|L]; [left; exact L|].
  destruct (Z_le_gt_dec 0x654000 p) as [L2|L2]; [right; exact L2|]. exfalso.
  apply (H (Z.max p 0x10000)); [lia|]. apply ms_img_full. lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Value helpers.                                                                                  *)
(* ---------------------------------------------------------------------------------------------- *)
(* donor WMseek.v wms_bge *)
Lemma ms_bge : forall E a b, Sg E b <= Sg E a -> branch_taken BC_GE (sv_denot E a) (sv_denot E b) = true.
Proof.
  intros E a b H. cbn [branch_taken]. unfold bv_lts. apply negb_true_iff. apply Z.ltb_ge.
  unfold Sg in H. exact H.
Qed.

Lemma ms_sg_lit : forall E z, 0 <= z < 2 ^ 63 -> Sg E (SLit z) = z.
Proof. intros E z Hz. rewrite S_SLit. apply swrap64_id. unfold half64. lia. Qed.

Lemma ms_sg_atom : forall E n z, ew E n = Z_to_bv 64 z -> 0 <= z < 2 ^ 63 -> Sg E (SOff n 0) = z.
Proof.
  intros E n z He Hz. rewrite S_SOff, He, unsigned_lit_small by lia. rewrite Z.add_0_r.
  apply swrap64_id. unfold half64. lia.
Qed.

(* an 8-byte word in memory fixes its value only modulo 2^64 *)
Lemma ms_val_mem8_mod : forall (m : word -> option byte) a v,
  val_mem tfibsegs m a 8 v -> val_mem tfibsegs m a 8 (v mod 2 ^ 64).
Proof.
  intros m a v H k Hk. rewrite (H k Hk). do 2 f_equal.
  cbv [YO0f.le_byte YG0f.le_byte]. change (8 * Z.of_nat 8) with 64. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma ms_denot_atom : forall E n v, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n 0) = Z_to_bv 64 (v mod 2 ^ 64).
Proof.
  intros E n v He. cbn [sv_denot]. rewrite He, Z.add_0_r, Z_to_bv_bv_unsigned. symmetry. apply Z_to_bv64_of_mod.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The symbolic entry state and the run.                                                           *)
(*   atoms 0..31: the registers (a2 = 0); 32: c->pos; 33: c->len; 34: the stack guard.             *)
(* ---------------------------------------------------------------------------------------------- *)
Definition R_stk : YP09.region := YP09.mkRegion (Some 2%nat) (-48) 0 (-48) 0 [].
Definition R_file : YP09.region :=
  YP09.mkRegion (Some 10%nat) 152 256 232 240
    [YP09.mkChunk 152 (CVal 8 (SOff 10 232)); YP09.mkChunk 232 (CVal 8 (SOff 32 0));
     YP09.mkChunk 240 (CVal 8 (SOff 33 0)); YP09.mkChunk 248 (CVal 8 (SLit 4096))].
Definition R_got : YP09.region :=
  YP09.mkRegion None 0xa2658 0xa2660 0xa2658 0xa2658 [YP09.mkChunk 0xa2658 (CVal 8 (SLit 0x651c50))].
Definition R_grd : YP09.region :=
  YP09.mkRegion None 0x651c50 0x651c58 0x651c50 0x651c50 [YP09.mkChunk 0x651c50 (CVal 8 (SOff 34 0))].
Definition ms_atoms : list (nat * afact) := [(2%nat, mkAF (2 ^ 44) (2 ^ 47) 4); (10%nat, mkAF 4096 (2 ^ 47) 4)].
(* the blt at +0x50 and the bge at +0x5c, in the form the engine reaches them *)
Definition ms_c1 : acond := mkAC BC_GE (SOff 11 0) (SLit 0).
Definition ms_c2 : acond := mkAC BC_GE (SLit 4096) (SOff 11 0).
Definition ss_ms : sstate :=
  mkSS LA_MSEEK (sr_set sr_atoms 12%bv (SLit 0)) [R_stk; R_file; R_got; R_grd] None
    (mkFacts ms_atoms [ms_c1; ms_c2] []).
Definition ms_st : sstate := Eval vm_compute in fst (sym_runN tfibsegs ms_tbl FUEL ss_ms).
Lemma ms_run : sym_runN tfibsegs ms_tbl FUEL ss_ms = (ms_st, RS_stopped (SR_jalr (SOff 1 0))).
Proof. vm_compute. reflexivity. Qed.

Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* lib/A/AE2y.v icpt_phase over ms_tbl *)
Lemma ms_phase : forall (W : world tfibsegs) E ss ss' st ms md,
  st_ok tfibsegs E ss (restrict (w_H W) ms) ->
  sym_runN tfibsegs ms_tbl FUEL ss = (ss', st) ->
  SRr tfibsegs W (mkCfg ms md)
    (fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
       match st with RS_ecall => st_ok_ecall tfibsegs E ss' (restrict (w_H W) ms1)
       | _ => st_ok tfibsegs E ss' (restrict (w_H W) ms1) end /\
       frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\
       frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
  intros W E ss ss' st ms md HS Hrun.
  eapply (SRr_run_gen tfibsegs ms_tbl ms_tbl_ok AF0x.Hwx_tfa W FUEL E ss ss' st ms md _ HS Hrun).
  intros ms1 mat1 HS1 HF HFr. apply SRr_ret. split; [reflexivity|]. exists ms1, mat1. split; [reflexivity|].
  split; [exact HS1|]. split; [exact HF | exact HFr].
Qed.
End h.

(* ---------------------------------------------------------------------------------------------- *)
(* amseek_set_realizes at mseek's entry.                                                           *)
(* ---------------------------------------------------------------------------------------------- *)
Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
(* The walk takes the .got cell from the premise rdword .. LA_GOT_GUARD = Some LA_GUARD and the FILE's words from
   the val_mem premises, so it uses no field of PcapSyms B: TB is not a hypothesis of the closed theorem. *)
Hypothesis TB : PcapSyms B.

Theorem link_amseek_set : amseek_set_realizes tfibsegs B link_amf LA_MSEEK.
Proof.
  intros ly S W regs mem md f off pos len HPRE H10 H11 H12 Hoff _ Hblk Hck Hpos Hlen Hsize Hgot [g Hg].
  change (amf_size link_amf) with 4096 in Hoff, Hsize.
  unfold AMF_COOKIE in Hck, Hpos, Hlen, Hsize |- *. unfold AMS_STK.
  replace (f + 232 + 8) with (f + 240) in Hlen by lia.
  replace (f + 232 + 16) with (f + 248) in Hsize by lia.
  pose proof (YG0q.AR_laws_ok tfibsegs B) as LAWS.
  pose proof HPRE as (HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp).
  pose proof Hwx_tfa as Hwx.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HES : ESTACK = 4096) by reflexivity.
  pose proof (am_layout B ly S _ (proj1 HAR)) as HLY.
  pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
  pose proof (lo_stk_ceil ly HLY) as Lceil. unfold ASAN_CEIL in Lceil.
  (* the FILE block: present, not the runtime's, off the image, below the stack *)
  pose proof (amf_block_facts tfibsegs B LAWS ly S W mem md f HAR Hblk) as (Hf16 & Hf4096 & Hfceil & _ & Hfby & _ & _).
  unfold AMF_BLOCK in Hfceil, Hfby.
  assert (Hfimg : f + 1304 <= 0x10000 \/ 0x654000 <= f).
  { apply (ms_blk_off_img f 1304); [lia|]. intros a Ha. exact (proj2 (proj2 (Hfby a Ha))). }
  unfold cfg_at. change (w64 LA_MSEEK) with (Z_to_bv 64 LA_MSEEK).
  set (sp0 := spZ regs) in *.
  (* the words the body reads, as atoms *)
  pose proof (ms_val_mem8_mod _ _ _ Hpos) as Hposv.
  pose proof (ms_val_mem8_mod _ _ _ Hlen) as Hlenv.
  pose proof (ms_val_mem8_mod _ _ _ (val_mem_of_rdword (w_H W) mem _ _ Hg)) as Hgv.
  set (extra := [Z_to_bv 64 pos; Z_to_bv 64 len; Z_to_bv 64 g]).
  set (E := Ereg regs extra).
  assert (E1 : ew E 1 = getr regs 1) by exact (ew_Ereg_nat regs extra 1 1%bv eq_refl).
  assert (E2 : ew E 2 = getr regs 2) by exact (ew_Ereg_nat regs extra 2 2%bv eq_refl).
  assert (E10 : ew E 10 = w64 f) by (rewrite <- H10; exact (ew_Ereg_nat regs extra 10 10%bv eq_refl)).
  assert (E11 : ew E 11 = w64 off) by (rewrite <- H11; exact (ew_Ereg_nat regs extra 11 11%bv eq_refl)).
  assert (E32 : ew E 32 = Z_to_bv 64 pos) by exact (ew_Ereg_extra regs extra 0).
  assert (E33 : ew E 33 = Z_to_bv 64 len) by exact (ew_Ereg_extra regs extra 1).
  assert (E34 : ew E 34 = Z_to_bv 64 g) by exact (ew_Ereg_extra regs extra 2).
  assert (Usp : bv_unsigned (ew E 2) = sp0) by (rewrite E2; reflexivity).
  assert (Uf : bv_unsigned (ew E 10) = f) by (rewrite E10; unfold w64; apply unsigned_lit_small; lia).
  (* the entry state *)
  assert (HS : st_ok tfibsegs E ss_ms (restrict (w_H W) (mkst regs (Z_to_bv 64 LA_MSEEK) mem (seg_rom tfibsegs)))).
  { rewrite restrict_mkst_fx. unfold ss_ms. apply (entry_st_ok_full tfibsegs); fold E.
    - apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X | exact H12].
    - vm_compute. reflexivity.
    - unfold R_stk, R_file, R_got, R_grd. repeat apply Forall_cons; try apply Forall_nil.
      + apply (region_ok_stack tfibsegs E _ 2 sp0 (-48) Usp); [lia | lia |].
        intros a Ha. apply apresent_writable. apply HpresE. lia.
      + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite Uf. split; [lia|]. split; [lia|]. split.
        { intros o Ho. apply apresent_writable. apply (proj1 (Hfby (f + o) ltac:(lia))). }
        repeat apply Forall_cons; try apply Forall_nil.
        * apply (chunk_ok_val tfibsegs E _ f 152 8 (SOff 10 232) (f + 232));
            [cbn [sv_denot]; rewrite Uf; reflexivity | cbn; lia | cbn; lia | exact Hck].
        * apply (chunk_ok_val tfibsegs E _ f 232 8 (SOff 32 0) (pos mod 2 ^ 64));
            [exact (ms_denot_atom E 32 pos E32) | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply Z.mod_pos_bound; lia
            | cbn; lia | exact Hposv].
        * apply (chunk_ok_val tfibsegs E _ f 240 8 (SOff 33 0) (len mod 2 ^ 64));
            [exact (ms_denot_atom E 33 len E33) | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply Z.mod_pos_bound; lia
            | cbn; lia | exact Hlenv].
        * apply (chunk_ok_val tfibsegs E _ f 248 8 (SLit 4096) 4096); [reflexivity | cbn; lia | cbn; lia | exact Hsize].
      + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val tfibsegs E _ 0 0xa2658 8 (SLit 0x651c50) 0x651c50);
          [reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_l; apply val_mem_of_rdword; exact Hgot].
      + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val tfibsegs E _ 0 0x651c50 8 (SOff 34 0) (g mod 2 ^ 64));
          [exact (ms_denot_atom E 34 g E34) | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply Z.mod_pos_bound; lia
          | cbn; lia | rewrite Z.add_0_l; exact Hgv].
    - apply pairwise_disjoint_of_extents. unfold R_stk, R_file, R_got, R_grd, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, Uf.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
    - split; [|split; [|exact I]].
      + cbn [ms_atoms atoms_ok f_atoms]. unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite Usp, Uf. change (2 ^ 4) with 16. repeat split; lia.
      + cbn [f_conds conds_ok acond_ok]. unfold ms_c1, ms_c2. cbn [ac_c ac_a ac_b]. split; [|split; [|exact I]].
        * apply ms_bge. change (Sg E (SLit 0) <= Sg E (SOff 11 0)).
          rewrite (ms_sg_lit E 0), (ms_sg_atom E 11 off E11) by lia. lia.
        * apply ms_bge. change (Sg E (SOff 11 0) <= Sg E (SLit 4096)).
          rewrite (ms_sg_lit E 4096), (ms_sg_atom E 11 off E11) by lia. lia. }
  (* the run: 0x96dd4 .. the ret at 0x96e5c, straight through *)
  eapply SRr_bind; [apply (ms_phase W E ss_ms ms_st _ _ md HS ms_run)|].
  cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1).
  change (st_ok tfibsegs E ms_st (restrict (w_H W) ms1)) in HS1.
  cbn [ms_mem mkst] in HF1, HFr1.
  eapply (SRr_ret_at tfibsegs ms_tbl ms_tbl_ok Hwx W E); [exact HS1 | reflexivity | vm_compute; reflexivity |].
  intros mat'. rewrite wvb_wvb.
  (* what the run wrote: the frame and c->pos *)
  assert (Hnw : forall a, in_wrange E (ss_mem ss_ms) a -> (sp0 - 48 <= a < sp0) \/ (f + 232 <= a < f + 240)).
  { intros a (r & Hin & Hr). unfold ss_ms, R_stk, R_file, R_got, R_grd in Hin. cbn [ss_mem In] in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
      rewrite ?Usp, ?Uf in Hr; lia. }
  assert (W1 : forall x : word, ~ (sp0 - 48 <= bv_unsigned x < sp0) -> ~ (f + 232 <= bv_unsigned x < f + 240) ->
    ms_mem ms1 x = mem x).
  { intros x Hx1 Hx2. apply HF1. intros Hin. destruct (Hnw _ Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 Hw)]. }
  assert (W1r : forall x : word, ~ (sp0 - 48 <= bv_unsigned x < sp0) -> ~ (f + 232 <= bv_unsigned x < f + 240) ->
    mrestrict (w_H W) (ms_mem ms1) x = mrestrict (w_H W) mem x).
  { intros x Hx1 Hx2. apply HFr1. intros Hin. destruct (Hnw _ Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 Hw)]. }
  assert (AV : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 48 <= a < sp0) -> ~ (f + 232 <= a < f + 240) ->
    aview tfibsegs (w_H W) (ms_mem ms1) a = aview tfibsegs (w_H W) mem a).
  { intros a Hr Ha1 Ha2. apply aview_eq_of. apply W1r; rewrite unsigned_lit_small by lia; assumption. }
  (* the regions the run left *)
  pose proof (st_ok_mem_ok tfibsegs E ms_st _ HS1) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs.
  lazymatch type of Hrs with Forall _ (ss_mem ?s) =>
    let l := eval vm_compute in (ss_mem s) in change (ss_mem s) with l in Hrs end.
  pose proof (Forall_inv Hrs) as HR0. pose proof (Forall_inv (Forall_inv_tail Hrs)) as HR1.
  unfold region_ok in HR0, HR1.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in HR0, HR1.
  destruct HR0 as (_ & _ & Hw0 & _). destruct HR1 as (_ & _ & Hw1 & Hcs).
  rewrite Usp in Hw0. rewrite Uf in Hw1, Hcs.
  assert (PRS : forall a, sp0 - 48 <= a < sp0 -> apresent (w_H W) (ms_mem ms1) a).
  { intros a Ha. apply (apresent_of_writable (w_H W) (ms_mem ms1) a ltac:(lia) (high_not_img a ltac:(lia))).
    replace a with (sp0 + (a - sp0)) by lia. apply Hw0. lia. }
  assert (PRC : forall a, f + 232 <= a < f + 240 -> apresent (w_H W) (ms_mem ms1) a).
  { intros a Ha. apply (apresent_of_writable (w_H W) (ms_mem ms1) a ltac:(lia) (proj2 (proj2 (Hfby a ltac:(lia))))).
    replace a with (f + (a - f)) by lia. apply Hw1. lia. }
  assert (Dp : sv_denot E (SOff 11 0) = Z_to_bv 64 off).
  { cbn [sv_denot]. rewrite E11, Z.add_0_r. unfold w64. apply Z_to_bv_bv_unsigned. }
  pose proof (val_of_chunk_ok tfibsegs E _ f 232 8 (SOff 11 0) off (Forall_inv Hcs) Dp ltac:(cbn; lia) ltac:(cbn; lia))
    as Hcookie.
  assert (PV : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W) mem a <> None ->
    aview tfibsegs (w_H W) (ms_mem ms1) a <> None).
  { intros a Hr Hv.
    assert (C : (sp0 - 48 <= a < sp0) \/ (f + 232 <= a < f + 240) \/
      (~ (sp0 - 48 <= a < sp0) /\ ~ (f + 232 <= a < f + 240))) by lia.
    destruct C as [C|[C|[N1 N2]]].
    - apply aview_some_of_apresent. apply PRS. exact C.
    - apply aview_some_of_apresent. apply PRC. exact C.
    - rewrite AV by assumption. exact Hv. }
  assert (PP : forall a, 0 <= a < 2 ^ 64 -> apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms1) a).
  { intros a Hr Hp.
    assert (C : (sp0 - 48 <= a < sp0) \/ (f + 232 <= a < f + 240) \/
      (~ (sp0 - 48 <= a < sp0) /\ ~ (f + 232 <= a < f + 240))) by lia.
    destruct C as [C|[C|[N1 N2]]].
    - apply PRS. exact C.
    - apply PRC. exact C.
    - destruct Hp as [Hh [b Hb]]. split; [exact Hh|]. exists b.
      rewrite W1; [exact Hb | rewrite unsigned_lit_small by lia; exact N1 | rewrite unsigned_lit_small by lia; exact N2]. }
  (* the registers at the ret *)
  rreg HS1 (1%bv : bv 5) Q1. rewrite E1 in Q1.
  rreg HS1 (10%bv : bv 5) Q10. rewrite E11 in Q10.
  replace (v_jalr (getr (ms_regs ms1) 1) 0) with (w64 (raZ regs))
    by (rewrite Q1; unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; symmetry; exact Hra).
  split; [reflexivity|]. exists (ms_regs ms1), (ms_mem ms1), (with_vm_backing (m_vm_lazy md) mat' md).
  pose proof (same_but_materialized_frame md _ (with_vm_backing_same md mat')) as MF.
  split; [reflexivity|].
  split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
  - apply (al_frame _ _ LAWS ly S W mem md (ms_mem ms1) _ HAR).
    + intros a Hr Hown. apply AV; [exact Hr | intros Hs; exact (al_stack _ _ LAWS ly S W mem md a HAR ltac:(lia) Hown)
        | intros Hc; exact (proj1 (proj2 (Hfby a ltac:(lia))) Hown)].
    + intros a Hv. rewrite (aview_mod _ (ms_mem ms1) a). apply PV; [apply Z.mod_pos_bound; lia | rewrite <- aview_mod; exact Hv].
    + apply MF. + apply MF. + apply MF.
    + intros a Ha Hh. unfold YG0d.w64 in Hh |- *. pose proof (in_band_rw_u64 a Ha) as Hr.
      assert (C : (sp0 - 48 <= a < sp0) \/ (f + 232 <= a < f + 240) \/
        (~ (sp0 - 48 <= a < sp0) /\ ~ (f + 232 <= a < f + 240))) by lia.
      destruct C as [C|[C|[N1 N2]]].
      * exfalso. destruct (HpresE a ltac:(lia)) as [Hf _]. rewrite Hf in Hh. discriminate Hh.
      * exfalso. destruct (proj1 (Hfby a ltac:(lia))) as [Hf _]. rewrite Hf in Hh. discriminate Hh.
      * apply W1; rewrite unsigned_lit_small by lia; assumption.
  - exact (aregs_preserved_of_st_ok _ E _ _ regs extra HS1 ltac:(split; [intros i Hi; reflexivity | reflexivity])
      ltac:(vm_compute; reflexivity)).
  - apply with_vm_backing_same.
  - exact Q10.
  - exact Hcookie.
  - intros a Hr Hs Hc. apply AV; [exact Hr | lia | lia].
  - intros a Hp. rewrite apresent_mod. apply PP; [apply Z.mod_pos_bound; lia | rewrite <- apresent_mod; exact Hp].
  - intros a Ha. apply PRS. exact Ha.
Qed.

End W.

About link_amseek_set.
Print Assumptions link_amseek_set.
