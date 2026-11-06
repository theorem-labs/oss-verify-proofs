(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ge_achain adapted from proofs/cgif/cgif_file_fuzzer/lib/A/ACf5.v (rt_chain) for the call chain of libreac/fuzz_grant's entry function; the rest of the file is written for fuzz_grant's entry walk. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntrySeat.v, with its module paths and module names changed; 662 of its 760 lines of code are new or changed and 833 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/B/Prog/BoxBLxCase0Kit.v, with its module names changed; 365 of its 451 lines of code are new or changed and 674 lines of the source are left out. *)
(* Case op & 3 = 0 of the B walk of fuzz_boxreg's LLVMFuzzerTestOneInput, piece W: from C0_W (0x80584, want in the
   slot 0x20, s3 = the name) the arguments of reac_boxreg_declare (r, nch, given, base): 0x80584 andi s8, s7, 8;
   0x80588 srli a0, s8, 3; 0x8058c addi a0, a0, -1; 0x80590 and a2, a0, s3 (given = the name when op & 8 = 0, else
   NULL); 0x80594 mv a0, s4; 0x80598 mv a1, s9; 0x8059c mv a3, s10; then the call jal reac_boxreg_declare at 0x805a0
   (lx_hyps' lh_declare, BoxBReacBoxregDeclare.v tbreac_boxreg_declare_spec), and the landing on the cut C0_D at its
   return 0x805a4. No branch, no shadow check, no store in the piece.
   The proof has three parts: c0w_run (the seven instructions, up to the callee's entry), c0w_call (the only use of
   lh_declare: the contract at the callee's entry and its post) and c0w_land (a machine state at 0x805a4 with the
   post's registers and bytes and the entry's kept bytes is in C0_D).
   FP state: declare's post (BoxBase.v apost_baseF) returns at SOME fx' with lx_fxr fx fx' (BoxBLxDefs.v), so the
   piece lands on C0_D taken at fx' (c0_w's premise is for every such fx'); c0w_call binds the post and passes fx' on,
   c0w_swap restates the entry's facts at fx', and c0w_land lands at fx'. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0s YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaRun PaShadow PaJournal BoxBase BoxRo YC4b.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import BoxTailVis.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBSyms BoxBList BoxBPa BoxBPaLib BoxBFrame.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Rt Require Import SnprintfDefB.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBReacBoxregInit BoxBReacBoxregDeclare.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBLxDefs BoxBLxSeat BoxBLxCase0Defs BoxBLxCase0Kit.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Boxreg BoxregUpd read_name_c range_free_c
  lowest_free_c reac_boxreg_declare_c LLVMFuzzerTestOneInput_case0 LLVMFuzzerTestOneInput_rn.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the given name: (((op & 8) >> 3) - 1) & nm ---- *)
Lemma c0w_and8 : forall op, 0 <= op < 256 -> alu64 ALU_AND (Z_to_bv 64 op) (Z_to_bv 64 8) = w64 (Z.land op 8).
Proof.
  intros op Hop. apply bv_eq. unfold alu64, alu, w64. rewrite bv_and_unsigned, !Z_to_bv_unsigned.
  pose proof (LLVMFuzzerTestOneInput_case0.c0_op8 op) as H8.
  rewrite (bv_wrap_small 64 op) by (change (bv_modulus 64) with (2 ^ 64); lia).
  rewrite (bv_wrap_small 64 8) by (change (bv_modulus 64) with (2 ^ 64); lia).
  rewrite (bv_wrap_small 64 (Z.land op 8)) by (change (bv_modulus 64) with (2 ^ 64); lia).
  reflexivity.
Qed.

Lemma c0w_a2 : forall op nm, 0 <= op < 256 -> 0 <= nm < 2 ^ 64 ->
  alu64 ALU_AND (alu64 ALU_ADD (alu64 ALU_SRL (alu64 ALU_AND (Z_to_bv 64 op) (Z_to_bv 64 8)) (Z_to_bv 64 3))
    (Z_to_bv 64 (-1))) (Z_to_bv 64 nm) = w64 (c0_given op nm).
Proof.
  intros op nm Hop Hnm. rewrite (c0w_and8 op Hop). unfold c0_given.
  destruct (LLVMFuzzerTestOneInput_case0.c0_op8 op) as [E|E]; rewrite E; cbv [Z.eqb].
  - assert (C : alu64 ALU_ADD (alu64 ALU_SRL (w64 0) (Z_to_bv 64 3)) (Z_to_bv 64 (-1)) = Z_to_bv 64 (Z.ones 64))
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite C. apply bv_eq. unfold alu64, alu, w64. rewrite bv_and_unsigned, !Z_to_bv_unsigned.
    rewrite (bv_wrap_small 64 (Z.ones 64)) by (change (bv_modulus 64) with (2 ^ 64); vm_compute; split; congruence).
    rewrite (bv_wrap_small 64 nm) by (change (bv_modulus 64) with (2 ^ 64); lia).
    rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
  - assert (C : alu64 ALU_ADD (alu64 ALU_SRL (w64 8) (Z_to_bv 64 3)) (Z_to_bv 64 (-1)) = Z_to_bv 64 0)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite C. apply bv_eq. unfold alu64, alu, w64. rewrite bv_and_unsigned, !Z_to_bv_unsigned. reflexivity.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg boxb_listing}.
#[local] Notation SEGS := (@pa_segs _ boxb_listing PI).
#[local] Notation VAL := (@pa_val _ boxb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ boxb_listing PI).
#[local] Notation BASE := (@pa_val _ boxb_listing PI A_TEXT).
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis HY : lx_hyps B MT.
Let LAWS := lh_laws B MT HY.
Let RUN := paj_run B LAWS.

(* ---- the run 0x80584 .. 0x805a0: the callee's entry with its arguments ---- *)
Lemma c0w_run : forall cx fp k (W3 : world SEGS) (ms3 : machine_state) ly3 S3 md3 op nm (Q : world SEGS -> config -> Prop),
  ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
    [(LX_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  ms_pc_val ms3 = w64 (BASE + C0P_W) -> ms_resv ms3 = None -> ms_svc_pending ms3 = None ->
  ms_rom ms3 = seg_rom SEGS -> ms_fregs ms3 = fp_regs -> ms_fcsr ms3 = fp_csr ->
  getr (ms_regs ms3) 23 = w64 op -> 0 <= op < 256 -> getr (ms_regs ms3) 19 = w64 nm -> 0 <= nm < 2 ^ 64 ->
  (forall (ms : machine_state) md,
     ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
       [(LX_CID, fp)] ly3 S3 W3 (ms_mem ms) md k ->
     (forall x, ms_mem ms x = ms_mem ms3 x) ->
     (forall n, In n [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 25; 26; 27] ->
        getr (ms_regs ms) (Z_to_bv 5 n) = getr (ms_regs ms3) (Z_to_bv 5 n)) ->
     getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + C0P_D) ->
     getr (ms_regs ms) 10 = getr (ms_regs ms3) 20 -> getr (ms_regs ms) 11 = getr (ms_regs ms3) 25 ->
     getr (ms_regs ms) 12 = w64 (c0_given op nm) -> getr (ms_regs ms) 13 = getr (ms_regs ms3) 26 ->
     getr (ms_regs ms) 24 = w64 (Z.land op 8) ->
     SRr SEGS W3 (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 (SIGMA BB_reac_boxreg_declare)) (ms_mem ms) (seg_rom SEGS)) md) Q) ->
  SRr SEGS W3 (mkCfg ms3 md3) Q.
Proof.
  intros cx fp k W3 ms3 ly3 S3 md3 op nm Q HJ Hpc Hresv Hsvc Hrom Hfreg Hfcsr R23 Hop R19 Hnm K.
  remember (lx_env cx fp (ms_regs ms3) []) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply lx_env_img).
  assert (ER : forall nn (rr : bv 5), Z.of_nat nn = bv_unsigned rr -> ew E nn = getr (ms_regs ms3) rr)
    by (intros nn rr Hnn; rewrite HE; apply lx_env_reg; exact Hnn).
  assert (HS : st_ok_pi SEGS VAL E (c0k_ss C0P_W [] (mkFacts [] [] [])) (restrict (w_H W3) ms3)).
  { rewrite HE. apply c0k_seat; try assumption; [reflexivity | apply Forall_nil | exact I | split; [exact I | split; exact I]]. }
  assert (SHOK : sh_ok SEGS C0K_BX [] E (mrestrict (w_H W3) (ms_mem ms3))) by apply Forall_nil.
  paj_run_tok RUN HS HJ SHOK C0K_BSPAN; [apply awr_ok_nil |].
  assert (HM : forall x, ms_mem ms x = ms_mem ms3 x) by (intros x; apply HF; intros (rg & Hin & _); destruct Hin).
  c0k_clean.
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
  prreg HS (12%bv : bv 5) Q12. prreg HS (13%bv : bv 5) Q13. prreg HS (24%bv : bv 5) Q24.
  apply K.
  - exact HJ.
  - exact HM.
  - intros n Hn.
    pose proof (regs_kept_of_st_ok SEGS E _ (restrict (w_H W3) ms) (ms_regs ms3) (lx_xatoms cx fp ++ [])
      (map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 25; 26; 27]) HS) as KR.
    cbn [restrict ms_regs] in KR. apply KR; [| reflexivity | apply in_map; exact Hn].
    rewrite HE. split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
  - rewrite Q1. reflexivity.
  - rewrite Q10. exact (ER 20%nat 20%bv eq_refl).
  - rewrite Q11. exact (ER 25%nat 25%bv eq_refl).
  - rewrite Q12, (ER 23%nat 23%bv eq_refl), (ER 19%nat 19%bv eq_refl), R23, R19. exact (c0w_a2 op nm Hop Hnm).
  - rewrite Q13. exact (ER 26%nat 26%bv eq_refl).
  - rewrite Q24, (ER 23%nat 23%bv eq_refl), R23. exact (c0w_and8 op Hop).
Qed.

(* The format "%s" (A_OBJ 10) is a registered global: its shadow byte is its size 3 (lh_glob's cells). *)
Lemma c0w_globs : globs_marked SEGS B [(AB_declare_fmtP, 3)].
Proof.
  intros ly S W mem md q sz Hin HAR. destruct Hin as [Eq | []]. injection Eq as <- <-.
  pose proof (lh_glob B MT HY) as GL.
  pose proof (blx_al _ GL (10%nat, 3) ltac:(cbn; tauto)) as Hal. cbn [fst] in Hal.
  unfold block_shadow, AB_declare_fmtP. split.
  { apply Z.mod_divide in Hal; [|lia]. apply Z.mod_divide; [lia|]. destruct Hal as [x Hx]. exists (4 * x). lia. }
  split; [lia|]. intros i Hi. change ((3 + 7) / 8) with 1 in Hi. assert (i = 0) as -> by lia.
  change (0 <? 3 / 8) with false. cbv iota. change (3 mod 8) with 3. rewrite Z.add_0_r.
  destruct HAR as (M & _).
  pose proof (am_const _ _ _ _ M) as C. rewrite Forall_forall in C.
  specialize (C (z1 (ANum (shadow_addr (VAL (A_OBJ 10)))) 3)
    (blx_cells _ GL ly _ ltac:(unfold lx_glob_cells; cbn [flat_map LX_GLOBS fst snd app];
                               do 12 right; left; reflexivity))).
  specialize (C 0%nat ltac:(cbn; lia)). cbn [aeval c_at c_val c_w z1 c1] in C. rewrite Z.add_0_r in C.
  unfold shadow_of_addr. unfold shadow_addr in C. rewrite C. reflexivity.
Qed.

(* ---- where the registry block lies: apart from every byte the cut keeps, and not a block of the caller ---- *)
Lemma c0w_geo : forall cx fp (W3 : world SEGS) (ms3 : machine_state) ly3 S3 md3 k r nm nn,
  lx_base B MT cx ->
  ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
    [(LX_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  frames S3 = [(LX_CID, fp)] ->
  ablocks B ly3 S3 = ablocks B (lc_ly cx) (lc_S cx) ++ [(r, LX_REG); (nm, nn)] -> 1 <= nn ->
  (forall a, lx_keep_at cx fp [(nm, nn)] a -> ~ inFP [(r, r + REG_SIZEB)] a) /\
  ~ In (r, REG_SIZEB) (ablocks B (lc_ly cx) (lc_S cx)) /\
  (nm + nn <= r \/ r + REG_SIZEB <= nm).
Proof.
  intros cx fp W3 ms3 ly3 S3 md3 k r nm nn HB HJ HFR HBL Hnn.
  pose proof HJ as (HAR & _).
  pose proof (lx_sp_facts B MT cx HB) as (Hsp0al & Hsp0lo & Hsp0hi & Hsp1 & Hsp1al).
  pose proof (lx_F_facts B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR) as (HF0 & HFc & HFapp & _ & HFal & HSHeq).
  pose proof (lx_frame_addr_eq B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ) as EFA.
  pose proof asan_consts as (C1a & C2a & C3a & C4a & C5a).
  assert (Hinr : In (r, LX_REG) (ablocks B ly3 S3)) by (rewrite HBL; apply in_or_app; right; left; reflexivity).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ r LX_REG HAR Hinr) as (_ & Hr0 & Hr1 & Hrapp & _).
  change (req_size LX_REG) with 288 in Hr1, Hrapp.
  assert (Hrnm : zdisjoint (block_rng (r, LX_REG)) (block_rng (nm, nn))).
  { apply (sep_blocks_pos SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 (r, LX_REG) (nm, nn)
      (ablocks B (lc_ly cx) (lc_S cx)) [] [] HAR). rewrite HBL. reflexivity. }
  unfold zdisjoint, block_rng in Hrnm. cbn [fst snd] in Hrnm. change (req_size LX_REG) with 288 in Hrnm.
  assert (Ennn : req_size nn = nn) by (unfold req_size; destruct (Z.eqb_spec nn 0); lia).
  rewrite Ennn in Hrnm.
  split; [|split; [|unfold REG_SIZEB; lia]].
  - intros a Ha (q & Hq & Hqa). destruct Hq as [<- | []]. cbn [fst snd] in Hqa. unfold REG_SIZEB in Hqa.
    destruct Ha as [H|[H|[H|[H|H]]]].
    + lia.
    + pose proof HB as (_ & _ & _ & Hpn & _).
      destruct Hpn as [(Hn0 & _) | (Hn & Hinp)]; [lia|].
      apply in_split in Hinp as (a1 & a2 & Ea).
      pose proof (sep_blocks_pos SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 (lc_p cx, lc_n cx) (r, LX_REG) a1 a2 [(nm, nn)]
        HAR ltac:(rewrite HBL, Ea, <- app_assoc; reflexivity)) as D.
      unfold zdisjoint, block_rng in D. cbn [fst snd] in D. change (req_size LX_REG) with 288 in D.
      pose proof (req_size_pos (lc_n cx) ltac:(lia)) as [_ Hq]. lia.
    + pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 r LX_REG LX_CID fp HAR Hinr
        ltac:(rewrite HFR; left; reflexivity)) as D.
      unfold zdisjoint in D. cbn [fst snd] in D. rewrite EFA in D. change (req_size LX_REG) with 288 in D.
      change (fs_frame_bytes LX_CID) with 512 in D, H. lia.
    + change (fs_frame_bytes LX_CID / 8) with 64 in H. rewrite HSHeq in H.
      assert (Hd0 : 0 <= lF cx fp / 8) by (apply Z.div_pos; lia).
      assert (Hd1 : lF cx fp / 8 <= 0xFFFFFF00000) by (apply Z.div_le_upper_bound; lia).
      unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
    + apply Exists_exists in H as (q & Hq & Hqa'). destruct Hq as [<- | []]. cbn [fst snd] in Hqa'. lia.
  - intros Hin. apply in_split in Hin as (a1 & a2 & Ea).
    pose proof (sep_blocks_pos SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 (r, LX_REG) (r, LX_REG) a1 a2 [(nm, nn)]
      HAR ltac:(rewrite HBL, Ea, <- app_assoc; reflexivity)) as D.
    unfold zdisjoint, block_rng in D. cbn [fst snd] in D. change (req_size LX_REG) with 288 in D. lia.
Qed.

(* ---- declare's name argument: NULL when op & 8, else the name block with its C string ---- *)
Lemma c0w_name_ok : forall i cx k acc ly3 S3 (W3 : world SEGS) (ms : machine_state) (m : word -> option byte) pos r nm op,
  c0_nm B MT i cx k acc ly3 S3 W3 ms pos r nm ->
  (forall a, aview SEGS (w_H W3) m a = aview SEGS (w_H W3) (ms_mem ms) a) ->
  (nm + (c0_nk (lc_pl cx) pos + 1) <= r \/ r + REG_SIZEB <= nm) ->
  tbdecl_name_ok B ly3 S3 W3 m r (c0_given op nm) (c0_gs (lc_pl cx) pos op).
Proof.
  intros i cx k acc ly3 S3 W3 ms m pos r nm op (Hk & Hacc & HBLK & Haf & Hnm4 & Hname & Hcur) Hm Hdisj.
  pose proof (LLVMFuzzerTestOneInput_rn.rn_k_range (c0_pl2 (lc_pl cx) pos)) as Hnk.
  pose proof (LLVMFuzzerTestOneInput_rn.rn_name_len (c0_pl2 (lc_pl cx) pos)) as Hlen.
  assert (HNB : c0_nb (lc_pl cx) pos =
    printf_facts_c.pf_bytes (c0_s (lc_pl cx) pos ++ [0]) ++ LLVMFuzzerTestOneInput_rn.nm_rest (c0_nb (lc_pl cx) pos))
    by (unfold c0_s, c0_nb, c0_nk; apply LLVMFuzzerTestOneInput_rn.nm_split).
  assert (HL : Z.of_nat (length (c0_nb (lc_pl cx) pos)) = c0_nk (lc_pl cx) pos + 1).
  { unfold c0_nb, c0_nk. rewrite length_app. cbn [length]. lia. }
  pose proof (LLVMFuzzerTestOneInput_rn.nm_len (c0_s (lc_pl cx) pos)
    (LLVMFuzzerTestOneInput_rn.nm_rest (c0_nb (lc_pl cx) pos))) as HL2.
  rewrite <- HNB, HL in HL2.
  assert (Hs : Forall (fun c => 0 < c < 256) (c0_s (lc_pl cx) pos)) by apply LLVMFuzzerTestOneInput_rn.nm_str_ok.
  unfold c0_nk in *.
  unfold c0_given, c0_gs. destruct (Z.land op 8 =? 0); [right | left; split; reflexivity].
  split; [lia|]. split; [exact Hs|]. split; [lia|].
  exists (read_name_c.rn_k (c0_pl2 (lc_pl cx) pos) + 1).
  split; [rewrite HBLK; apply in_or_app; right; right; left; reflexivity|].
  split; [lia|]. split; [exact Hdisj|].
  intros j Hj. pose proof (Hname j ltac:(lia)) as Hv. unfold lview in Hv. rewrite Hm, Hv. f_equal.
  rewrite HNB. rewrite app_nth1 by (unfold printf_facts_c.pf_bytes; rewrite length_map, length_app; cbn [length]; lia).
  unfold printf_facts_c.pf_bytes. rewrite map_nth.
  assert (Hc : 0 <= nth (Z.to_nat j) (c0_s (lc_pl cx) pos ++ [0]) 0 < 256).
  { destruct (Nat.lt_ge_cases (Z.to_nat j) (length (c0_s (lc_pl cx) pos))) as [Hlt | Hge].
    - rewrite app_nth1 by exact Hlt. rewrite Forall_forall in Hs.
      pose proof (Hs _ (nth_In (c0_s (lc_pl cx) pos) 0 Hlt)). lia.
    - rewrite app_nth2 by exact Hge. replace (Z.to_nat j - length (c0_s (lc_pl cx) pos))%nat with 0%nat by lia.
      cbn [nth]. lia. }
  rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. exact Hc.
Qed.

(* ---- the call reac_boxreg_declare (r, nch, given, base) at 0x805a0: lh_declare at the callee's entry ----
   The callee's footprint is the registry block r (a block of the walk, not of the caller); its journal keeps every
   byte of rs (lx_keep_call_fp) when no byte of rs is in r. Declare's post is BoxBase.v apost_baseF: the callee
   returns at SOME FP state fx' with lx_fxr fx fx' (f registers but f10 kept; fcsr kept or rounding mode 0), and the
   continuation runs at fx'. The post is bound directly (SRr_bind, as YC85.v cl_callS binds a callee's apost_base
   post). FMsnprintfSx.v srr_fx_continue does not take this post: its premise asks rounding mode 0 of fx' alone
   (snprintf's post), while apost_baseF's clause is `fcsr kept \/ rounding mode 0` (declare's refusals return at
   fx' = fx, whose fcsr is any). *)
Lemma c0w_call : forall cx fp k ly3 S3 (W3 : world SEGS) (ms : machine_state) md rs r nm nch b0 bs s
  (Q : world SEGS -> config -> Prop),
  lx_base B MT cx ->
  ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
    [(LX_CID, fp)] ly3 S3 W3 (ms_mem ms) md k ->
  frames S3 = [(LX_CID, fp)] ->
  (forall p n, In (p, n) (ablocks B (lc_ly cx) (lc_S cx)) -> In (p, n) (ablocks B ly3 S3)) ->
  Forall (fun q => exists n, In (fst q, n) (ablocks B ly3 S3) /\ 0 <= snd q <= req_size n) rs ->
  (forall a, lx_keep_at cx fp rs a -> ~ inFP [(r, r + REG_SIZEB)] a) ->
  In (r, REG_SIZEB) (ablocks B ly3 S3) -> ~ In (r, REG_SIZEB) (ablocks B (lc_ly cx) (lc_S cx)) ->
  getr (ms_regs ms) 2 = w64 (lsp1 cx) -> getr (ms_regs ms) 8 = w64 (lsp0 cx) ->
  getr (ms_regs ms) 3 = getr (lc_regs cx) 3 -> getr (ms_regs ms) 4 = getr (lc_regs cx) 4 ->
  YK0s.ret_ok (getr (ms_regs ms) 1) -> 4096 <= bv_unsigned (getr (ms_regs ms) 1) ->
  getr (ms_regs ms) 10 = w64 r -> getr (ms_regs ms) 11 = w64 nch ->
  getr (ms_regs ms) 12 = w64 nm -> getr (ms_regs ms) 13 = w64 b0 ->
  -2 ^ 31 <= nch < 2 ^ 31 -> -2 ^ 31 <= b0 < 2 ^ 31 ->
  lsaved cx W3 ms -> tbdecl_reg_bytes W3 (ms_mem ms) r bs -> Boxreg.boxreg_inv bs ->
  tbdecl_name_ok B ly3 S3 W3 (ms_mem ms) r nm s ->
  Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
  (forall (fx' : YK11.FPState) (regs2 : bvmap 5 word) mem2 md2, lx_fxr fx fx' ->
     ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
       [(LX_CID, fp)] ly3 S3 W3 mem2 md2 k ->
     aregs_preserved (ms_regs ms) regs2 -> lx_keep cx fp W3 rs (ms_mem ms) mem2 ->
     ((reac_boxreg_declare_c.declare_refused bs nch b0 /\ getr regs2 10 = w64 (-1) /\
         tbdecl_reg_bytes W3 mem2 r bs) \/
        (exists b p, reac_boxreg_declare_c.declare_placed bs nch b0 b p /\ getr regs2 10 = w64 (Boxreg.bx_n bs) /\
         tbdecl_reg_bytes W3 mem2 r (BoxregUpd.new_row_bytes bs (reac_boxreg_declare_c.decl_row b nch p s)))) ->
     SRr SEGS W3 (mkCfg (@mkst fx' regs2 (getr (ms_regs ms) 1) mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS W3 (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 (SIGMA BB_reac_boxreg_declare)) (ms_mem ms) (seg_rom SEGS)) md) Q.
Proof.
  intros cx fp k ly3 S3 W3 ms md rs r nm nch b0 bs s Q HB HJ HFR Hbl Hrs Hfp Hin Hnin G2 G8 G3 G4 Hra Hra4
    H10 H11 H12 H13 Hk Hb HSAVED HREG HINV HNAME HRM HK.
  pose proof (lx_sp_facts B MT cx HB) as (Hsp0al & Hsp0lo & Hsp0hi & Hsp1 & Hsp1al).
  pose proof asan_consts as (C1a & C2a & C3a & C4a & C5a).
  pose proof (lh_glob B MT HY) as GL.
  pose proof HB as (HPRE0 & _ & _ & _ & _ & _ & _ & _ & HRO0 & _).
  pose proof HPRE0 as (HAR0 & Hra0 & Hra40 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT0).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof HJ as (HARc & Hlyc & _).
  assert (HRO : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W3) (ms_mem ms)))
    by exact (lx_arodata_kept B _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HRO0).
  assert (ESPc : spZ (ms_regs ms) = lsp0 cx + (lsp1 cx - lsp0 cx)).
  { unfold spZ. rewrite G2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
  assert (ES0c : s0Z (ms_regs ms) = lsp0 cx).
  { unfold s0Z. rewrite G8. unfold w64. apply unsigned_lit_small. lia. }
  pose proof HSAVED as (HRA8 & HSJ).
  pose proof (HSJ 0 ltac:(lia)) as HS016. cbn [Z.ltb Z.compare] in HS016.
  replace (lsp0 cx - 16 - 8 * 0) with (lsp0 cx - 16) in HS016 by lia.
  assert (HCH : achain ly3 (aview SEGS (w_H W3) (ms_mem ms)) (spZ (ms_regs ms)) (s0Z (ms_regs ms)) (lch cx)).
  { rewrite ESPc. replace (lsp0 cx + (lsp1 cx - lsp0 cx)) with (lsp1 cx) by lia.
    rewrite ES0c. apply (c0k_achain_ly (lc_ly cx)); [exact (c0k_layout_top _ _ _ Hlyc)|].
    apply (lx_achain cx _ (lsp1 cx)); [exact Hch | lia | lia | apply c0k_mod8; exact Hal16 | exact Hra40
      | intros a Ha; exact (aview_above_of_journal B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ a Ha)
      | unfold lview in HRA8; exact HRA8 | unfold lview in HS016; exact HS016 | lia]. }
  pose proof (blx_marg B GL (10%nat, 3) ltac:(cbn; tauto)) as (HM1 & HM2). cbn [fst snd] in HM1, HM2.
  assert (WS : REAC_BOXREG_DECLARE_STKB = 8272) by reflexivity.
  assert (HPRE : afn_pre SEGS B REAC_BOXREG_DECLARE_STKB ly3 S3 W3 (ms_regs ms) (ms_mem ms) md (lch cx)).
  { apply (afn_pre_at SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
      [(LX_CID, fp)] ly3 S3 W3 (ms_mem ms) md k (ms_regs ms) REAC_BOXREG_DECLARE_STKB (lsp1 cx - lsp0 cx) (lch cx)
      HJ ESPc).
    - pose proof (proj1 (Z.mod_divide (lsp1 cx) 32 ltac:(lia)) Hsp1al) as [q1 Hq1].
      pose proof (proj1 (Z.mod_divide (lsp0 cx) 16 ltac:(lia)) Hsp0al) as [q2 Hq2].
      rewrite Hq1, Hq2. replace (q1 * 32 - q2 * 16) with ((2 * q1 - q2) * 16) by lia. apply Z_mod_mult.
    - lia.
    - rewrite WS. lia.
    - rewrite WS. unfold LX_STK. lia.
    - exact Hra.
    - unfold raZ. exact Hra4.
    - rewrite G3. exact Hgp.
    - rewrite G4. exact Htp.
    - exact HCH. }
  pose proof (lh_declare B MT HY ly3 S3 W3 (ms_regs ms) (ms_mem ms) md (lch cx) r nch nm b0 bs s [(AB_declare_fmtP, 3)]
    HPRE HRO H10 H11 H12 H13 Hk Hb Hin HREG HINV HNAME (absn_blk_tail_vis_ok SEGS B) (blx_isv B GL) c0w_globs
    (blx_rom_bytes B GL (10%nat, [37; 115; 0]) ltac:(cbn; tauto)) (or_introl eq_refl) HM1 HM2 (blx_fmt_got B GL) HRM)
    as HDC.
  rewrite pa_sigma_reac_boxreg_declare.
  eapply SRr_bind; [exact HDC|].
  intros W2 c2 _ (fx' & ly2 & S2 & regs2 & mem2 & md2 & -> & Hf & Hc & HJ1 & HP & (-> & -> & -> & _ & HRES)).
  rewrite ESPc in HJ1.
  assert (HJ2 : ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
    [(LX_CID, fp)] ly3 S3 W3 mem2 md2 k).
  { change [(LX_CID, fp)] with ([] ++ [(LX_CID, fp)]). replace k with (k + 0) by lia.
    eapply (ajournal_sub_tok SEGS B LAWS pa_segs_low); [exact HJ | exact HJ1 | rewrite WS; unfold LX_STK; lia | lia |].
    intros a (q & Hq & Ha). destruct Hq as [<- | []]. cbn [fst snd] in Ha. right.
    exists r, REG_SIZEB. split; [exact Hin|]. split; [exact Hnin|].
    change (req_size REG_SIZEB) with 288. unfold REG_SIZEB in Ha. lia. }
  apply (HK fx' regs2 mem2 md2 (conj Hf Hc) HJ2 HP); [|exact HRES].
  eapply (lx_keep_call_fp B MT LAWS cx fp W3 ms ly3 S3 md k HB HJ HFR rs [(r, r + REG_SIZEB)] REAC_BOXREG_DECLARE_STKB).
  - lia.
  - exact Hbl.
  - exact Hrs.
  - exact Hfp.
  - replace (lsp1 cx) with (lsp0 cx + (lsp1 cx - lsp0 cx)) by lia. exact HJ1.
Qed.

(* ---- the entry's facts at the FP state the callee returns at ----
   The cut's facts at the entry state ms3 (FP state fx) hold of the same registers and bytes rebuilt at any FP state
   fx' (lx_body asks only that the machine's f registers and fcsr are the FP state's own). *)
Lemma c0w_swap : forall (fx' : YK11.FPState) i cx fp k acc ly3 S3 (W3 : world SEGS) (ms3 : machine_state)
  pos r fab op nm bs,
  c0_from (fx := fx) B MT i cx fp k acc ly3 S3 W3 ms3 C0P_W pos r fab op nm bs ->
  c0_from (fx := fx') B MT i cx fp k acc ly3 S3 W3
    (@mkst fx' (ms_regs ms3) (Z_to_bv 64 (BASE + C0P_W)) (ms_mem ms3) (seg_rom SEGS)) C0P_W pos r fab op nm bs.
Proof.
  intros fx' i cx fp k acc ly3 S3 W3 ms3 pos r fab op nm bs (HC & HN & HA).
  destruct HC as (HBD & Hrest). destruct HBD as (_ & _ & _ & _ & _ & _ & HBrest).
  split; [split; [|exact Hrest] | exact (conj HN HA)].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. exact HBrest.
Qed.

(* ---- the landing at C0_D (0x805a4), at the FP state fx' the callee returned at: the entry's facts carried over by
   the kept bytes, the post's registers and registry bytes ---- *)
Lemma c0w_land : forall (fx' : YK11.FPState) POST i cx fp k acc ly3 S3 (W3 : world SEGS) (ms3 : machine_state)
  (regs2 : bvmap 5 word) mem2 md2 pos r fab op nm want bs,
  lx_from B MT POST (C0_D (fx := fx') B MT i) -> lx_base B MT cx ->
  ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
    [(LX_CID, fp)] ly3 S3 W3 mem2 md2 k ->
  frames S3 = [(LX_CID, fp)] -> mo_le MT (lc_S cx) S3 acc ->
  c0_from (fx := fx) B MT i cx fp k acc ly3 S3 W3 ms3 C0P_W pos r fab op nm bs ->
  lslot cx W3 ms3 0x60 nm -> lslot cx W3 ms3 0x20 (want mod 2 ^ 64) ->
  LLVMFuzzerTestOneInput_case0.c0_want bs (c0_nchv (lc_pl cx) pos) (c0_basev (lc_pl cx) pos) want ->
  -1 <= want <= 40 ->
  c0_kept cx fp W3 [] [(nm, c0_nk (lc_pl cx) pos + 1)] (ms_mem ms3) mem2 ->
  c0_regs cx fp regs2 r fab op pos -> getr regs2 24 = w64 (Z.land op 8) ->
  ((reac_boxreg_declare_c.declare_refused bs (c0_nchv (lc_pl cx) pos) (c0_basev (lc_pl cx) pos) /\
    getr regs2 10 = w64 (-1) /\ tbdecl_reg_bytes W3 mem2 r bs) \/
   (exists b p, reac_boxreg_declare_c.declare_placed bs (c0_nchv (lc_pl cx) pos) (c0_basev (lc_pl cx) pos) b p /\
    getr regs2 10 = w64 (Boxreg.bx_n bs) /\
    tbdecl_reg_bytes W3 mem2 r (BoxregUpd.new_row_bytes bs
      (reac_boxreg_declare_c.decl_row b (c0_nchv (lc_pl cx) pos) p (c0_gs (lc_pl cx) pos op))))) ->
  SRr SEGS W3 (mkCfg (@mkst fx' regs2 (Z_to_bv 64 (BASE + C0P_D)) mem2 (seg_rom SEGS)) md2) (POST cx).
Proof.
  intros fx' POST i cx fp k acc ly3 S3 W3 ms3 regs2 mem2 md2 pos r fab op nm want bs
    HD HB HJ2 HFR HMO HF S60 S20 HW Hw HK HR R24 HRES.
  set (ms0 := @mkst fx' (ms_regs ms3) (Z_to_bv 64 (BASE + C0P_W)) (ms_mem ms3) (seg_rom SEGS)).
  set (ms2 := @mkst fx' regs2 (Z_to_bv 64 (BASE + C0P_D)) mem2 (seg_rom SEGS)).
  apply (HD cx fp k acc ly3 S3 W3 ms2 md2 HB HJ2 HFR HMO).
  pose proof (c0w_swap fx' i cx fp k acc ly3 S3 W3 ms3 pos r fab op nm bs HF) as HF'.
  destruct (c0_land_all (fx := fx') B MT i cx fp k acc ly3 S3 W3 ms0 mem2 regs2 C0P_W C0P_D pos r fab op nm bs []
    [(nm, c0_nk (lc_pl cx) pos + 1)] HB HF' (Forall_nil _) (or_introl eq_refl) HK HR) as (HC & HNM & HARG).
  pose proof (lx_sp_facts B MT cx HB) as (_ & Hsp0lo & Hsp0hi & Hsp1 & _).
  pose proof asan_consts as (C1a & _).
  assert (Hsp : 0 <= lsp1 cx /\ lsp1 cx + 256 <= lsp0 cx <= 2 ^ 47) by lia.
  exists pos, r, fab, op, nm, want, bs.
  split; [exact HC|]. split; [exact HNM|]. split; [exact HARG|].
  split; [exact (c0_slot_keep cx fp W3 [] _ ms0 ms2 HK Hsp 0x60 nm ltac:(lia) ltac:(lia) (Forall_nil _) S60)|].
  split; [exact HW|]. split; [exact Hw|].
  split; [exact (c0_slot_keep cx fp W3 [] _ ms0 ms2 HK Hsp 0x20 _ ltac:(lia) ltac:(lia) (Forall_nil _) S20)|].
  split; [exact R24|].
  destruct HRES as [(Hrf & R10 & HRB) | (b & p & Hpl & R10 & HRB)].
  - left. split; [exact Hrf|]. split; [intros q Hq; exact (HRB q Hq) | exact R10].
  - right. exists b, p. split; [exact Hpl|]. split; [intros q Hq; exact (HRB q Hq) | exact R10].
Qed.

(* ---- the piece: C0_W -> (run, call, landing) -> C0_D ---- *)
Theorem c0_w : forall (POST : lxcx -> world SEGS -> config -> Prop) i,
  Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
  (forall fx', lx_fxr fx fx' -> lx_from B MT POST (C0_D (fx := fx') B MT i)) -> lx_from B MT POST (C0_W B MT i).
Proof.
  intros POST i HRM HD cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HGI.
  destruct HGI as (pos & r & fab & op & nm & want & bs & HCOM & HNM & HREG & HARG & R19 & S60 & HW & Hw & S20).
  pose proof HCOM as (HBODY & Hi64 & HPREV & HINV & HFAB & Hpos & Hop & Hop3 & HSLL & S58 & S48 & R20 & R21 & R27).
  pose proof HBODY as (Hpc & Hresv & Hsvc & Hrom & Hfreg & Hfcsr & HREGS & HSAVED & HSHD & HFLAG
    & HS10 & HS18 & HS80 & HINP).
  pose proof HARG as (R23 & R25 & R26 & S50).
  pose proof HREGS as (G2 & G8 & G9 & G3 & G4 & G18 & G22).
  pose proof (lx_sp_facts B MT cx HB) as (Hsp0al & Hsp0lo & Hsp0hi & Hsp1 & Hsp1al).
  pose proof asan_consts as (C1a & C2a & C3a & C4a & C5a).
  pose proof HNM as (Hk & Hacc & HBLK & Haf & Hnm4 & Hname & Hcur).
  pose proof HJ as (HAR & _).
  pose proof (LLVMFuzzerTestOneInput_rn.rn_k_range (c0_pl2 (lc_pl cx) pos)) as Hnk. fold (c0_nk (lc_pl cx) pos) in Hnk.
  assert (Hop8 : 0 <= op < 256).
  { pose proof (bv_unsigned_in_range 8 (nth pos (lc_pl cx) (Z_to_bv 8 0))) as R. change (bv_modulus 8) with 256 in R.
    rewrite Hop. exact R. }
  assert (Hinn : In (nm, c0_nk (lc_pl cx) pos + 1) (ablocks B ly3 S3))
    by (rewrite HBLK; apply in_or_app; right; right; left; reflexivity).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ nm _ HAR Hinn) as (_ & _ & Hnmc & _).
  pose proof (req_size_pos (c0_nk (lc_pl cx) pos + 1) ltac:(lia)) as [_ Hrq].
  destruct (c0w_geo cx fp W3 ms3 ly3 S3 md3 k r nm (c0_nk (lc_pl cx) pos + 1) HB HJ HFR HBLK ltac:(lia))
    as (Hfp & Hnin & Hdisj).
  assert (HF0 : c0_from B MT i cx fp k acc ly3 S3 W3 ms3 C0P_W pos r fab op nm bs) by exact (conj HCOM (conj HNM HARG)).
  pose proof (LLVMFuzzerTestOneInput_case0.c0_nch_range (c0_pl0 (lc_pl cx) pos)) as Hnch.
  pose proof (LLVMFuzzerTestOneInput_case0.c0_base_range (c0_pl0 (lc_pl cx) pos)) as Hbase.
  fold (c0_nchv (lc_pl cx) pos) in Hnch. fold (c0_basev (lc_pl cx) pos) in Hbase.
  assert (Hsp : 0 <= lsp1 cx /\ lsp1 cx + 256 <= lsp0 cx <= 2 ^ 47) by lia.
  apply (c0w_run cx fp k W3 ms3 ly3 S3 md3 op nm (POST cx) HJ Hpc Hresv Hsvc Hrom Hfreg Hfcsr R23 Hop8 R19 ltac:(lia)).
  intros ms md HJm HM KR R1 R10 R11 R12 R13 R24.
  assert (KA : forall a, aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) (ms_mem ms3) a)
    by (intros a; unfold aview, mbyte, mrestrict; rewrite HM; reflexivity).
  assert (K0 : c0_kept cx fp W3 [] [(nm, c0_nk (lc_pl cx) pos + 1)] (ms_mem ms3) (ms_mem ms)) by (intros a _; exact (KA a)).
  apply (c0w_call cx fp k ly3 S3 W3 ms md [(nm, c0_nk (lc_pl cx) pos + 1)] r (c0_given op nm)
    (c0_nchv (lc_pl cx) pos) (c0_basev (lc_pl cx) pos) bs (c0_gs (lc_pl cx) pos op) (POST cx) HB HJm HFR).
  - intros pp nn Hin. rewrite HBLK. apply in_or_app. left. exact Hin.
  - apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. exists (c0_nk (lc_pl cx) pos + 1).
    split; [exact Hinn | lia].
  - exact Hfp.
  - rewrite HBLK. apply in_or_app. right. left. reflexivity.
  - exact Hnin.
  - exact (eq_trans (KR 2 ltac:(cbn; tauto)) G2).
  - exact (eq_trans (KR 8 ltac:(cbn; tauto)) G8).
  - exact (eq_trans (KR 3 ltac:(cbn; tauto)) G3).
  - exact (eq_trans (KR 4 ltac:(cbn; tauto)) G4).
  - rewrite R1. apply ret_ok_codeptr_v; [unfold C0P_D; lia | reflexivity].
  - rewrite R1. pose proof pa_base_lo. pose proof (pa_B_ok (L := boxb_listing)) as (HB0 & HB1b & _).
    rewrite unsigned_lit_small by (unfold C0P_D; lia). unfold C0P_D. lia.
  - rewrite R10. exact R20.
  - rewrite R11. exact R25.
  - exact R12.
  - rewrite R13. exact R26.
  - lia.
  - lia.
  - exact (c0_saved_keep cx fp W3 [] _ ms3 ms K0 (Forall_nil _) Hsp HSAVED).
  - intros q Hq. rewrite KA. exact (HREG q Hq).
  - exact HINV.
  - exact (c0w_name_ok i cx k acc ly3 S3 W3 ms3 (ms_mem ms) pos r nm op HNM KA Hdisj).
  - exact HRM.
  - (* back at 0x805a4, at the FP state fx' declare returned at *)
    intros fx' regs2 mem2 md2 Hfx HJ2 HP HK HRES.
    rewrite R1.
    assert (PR : forall n, In n [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 25; 26; 27] ->
      getr regs2 (Z_to_bv 5 n) = getr (ms_regs ms3) (Z_to_bv 5 n)).
    { intros n Hn. rewrite (HP n) by (unfold acallee_saved; cbn in Hn; lia). exact (KR n Hn). }
    apply (c0w_land fx' POST i cx fp k acc ly3 S3 W3 ms3 regs2 mem2 md2 pos r fab op nm want bs (HD fx' Hfx) HB HJ2
      HFR HMO HF0 S60 S20 HW Hw).
    + exact (c0_kept_trans cx fp W3 [] _ _ _ _ K0 (c0_kept_lx cx fp W3 [] _ _ _ HK)).
    + split; [exact (eq_trans (PR 2 ltac:(cbn; tauto)) G2)|].
      split; [exact (eq_trans (PR 8 ltac:(cbn; tauto)) G8)|].
      split; [exact (eq_trans (PR 9 ltac:(cbn; tauto)) G9)|].
      split; [exact (eq_trans (PR 3 ltac:(cbn; tauto)) G3)|].
      split; [exact (eq_trans (PR 4 ltac:(cbn; tauto)) G4)|].
      split; [exact (eq_trans (PR 18 ltac:(cbn; tauto)) G18)|].
      split; [exact (eq_trans (PR 22 ltac:(cbn; tauto)) G22)|].
      split; [exact (eq_trans (PR 20 ltac:(cbn; tauto)) R20)|].
      split; [exact (eq_trans (PR 21 ltac:(cbn; tauto)) R21)|].
      split; [exact (eq_trans (PR 27 ltac:(cbn; tauto)) R27)|].
      split; [exact (eq_trans (PR 23 ltac:(cbn; tauto)) R23)|].
      split; [exact (eq_trans (PR 25 ltac:(cbn; tauto)) R25)|].
      exact (eq_trans (PR 26 ltac:(cbn; tauto)) R26).
    + exact (eq_trans (HP 24 ltac:(unfold acallee_saved; lia)) R24).
    + exact HRES.
Qed.

End a.
