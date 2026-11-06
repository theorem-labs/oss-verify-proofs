(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: check_reply's ASan walk (fuzz_command.asan, 0x86d78) assembled from its
   segments, as proofs/cgif/cgif_file_fuzzer/lib/A/ACh5.v assembles cgif_close's (pb_cgif_closeX):
     s1 the entry to the memchr call, s2 memchr / check_reply_answer / sup_reply_code, s3 the code's split,
     s4 snprintf, s4b rec_code_declared, s5 strcmp, s6 strlen / rec_shape_of, s7 syntax_reply_matches twice,
     s8 the frame's release and the return.
   snprintf is the only call that changes the FP state, so s4b, s5 and s8 (the segments after it) are taken at every
   FP state and s4 uses them at the state the wrapper returns.
   `pb_check_reply` is tcheck_reply_spec (lib/A/Prog/check_reply_c.v). The walk's facts at the entry that the
   statement no longer states come from its premises: the record's cells (replace_str flag byte, stack guard, errno)
   from CmdRecCells' cmd_rec_cells, the recorder's GOT words from cmd_ro_ok's RO_ptr_a70xx bytes, the read-only
   ranges from CmdRecRo's cmd_ro_in_img, and the words' shadow from AR's zshadow_ok of the stack window
   [ly_stk_lo, ly_stk_hi) (the words lie in it: spZ regs <= w and w + WORDS_W + 12 <= ly_stk_hi ly). The kit lemmas
   take the image facts IMG (cmd_img_facts); the segments take CmdRecImg's cmd_heap_tail_vis, and its
   cmd_prog_unowned and cmd_rom_view_on at IMG, so no record fact is a Section hypothesis (the walk hypotheses keep
   cgif's names; the record facts are lemmas of lib/A/Prog/CmdRecFacts.v). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply.v, with its module names changed; 206 of its 240 lines of code are new or changed and 118 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/sup_host_setting.v, with its module paths and module names changed; 307 of its 340 lines of code are new or changed and 207 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput's case 0 (fuzz_boxreg.c:217, :226) on the ASan build: from the cut W (0x8093c,
   BoxLxCase0Defs.v) `andi s9, s6, 8; srli a0, s9, 3; addi a0, a0, -1; sd s7, 0x58(s1); and a2, a0, s7` keeps the name
   in the slot 0x58 and computes given = c0_given op nm (NULL when op & 8, else the name), `mv a0, s4; mv a1, s3;
   mv a3, s11` pass r, nch and base, and `jal reac_boxreg_declare` (0x8095c) calls the function under
   treac_boxreg_declare_spec (ReacBoxregDeclare.v), composed by c0d_callF (YC85.v cl_callS with the callee's
   FP-existential return, BoxBase.v apost_baseF; callee footprint: the registry block r, a block of this turn). The
   function returns at some FP state fx' with lx_fxr fx fx' (BoxLxDefs.v: the f registers but f10 and the fcsr's
   rounding mode as the post says), so the piece's next cut is taken at fx': its continuation is
   `forall fx', lx_fxr fx fx' -> gb_from ... (C0_D (fx := fx') ...)`. The run stops at the return slot 0x80960, where
   C0_D holds: refused (a0 = -1, the table as before) or placed (a0 = n, the new row); the case's slots, the frame,
   the input and the name block are kept by the run's frame_of and the callee's journal. The piece has no branch. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YI16 YC5d YM05 YG0s YImgTop.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal BoxSyms BoxList BoxPa BoxPaLib BoxBase.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import YC4b YC1g YC1h YC85 BoxFrame BoxCJ BoxRo.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import ReacBoxregInit BoxLxDefs ReadName.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Boxreg BoxregUpd LLVMFuzzerTestOneInput_inv.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require LLVMFuzzerTestOneInput_case0 LLVMFuzzerTestOneInput_rn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require read_name_c reac_boxreg_declare_c.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import BoxLxCase0Defs.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import ReacBoxregDeclare.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require Import SnprintfDef.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* The shadow base for the runner; the slot 0x58 (the name), the one window the walk writes; s1's range (sp1 is above
   alloc_ceiling, below 2^47, 32-aligned), which places that window apart from the shadow span. *)
Definition C0D_SB : Z := 0x7fff8000.
Definition C0D_R58 : YP09.region := YP09.mkRegion (Some 9%nat) 0x58 0x60 0x58 0x60 [].
Definition C0D_AF : list (nat * afact) := [(9%nat, mkAF 140735332483072 (2 ^ 47) 5)].

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg box_listing}.
Context {RO : ro_below_ofl (@pa_segs _ box_listing PI) pa_relro_lo pa_relro_hi}.
#[local] Notation SEGS := (@pa_segs _ box_listing PI).
#[local] Notation VAL := (@pa_val _ box_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ box_listing PI).
#[local] Notation BASE := (@pa_val _ box_listing PI A_TEXT).

(* The C string of the name block: its characters and NUL are the block's first bytes. *)
Lemma c0d_nm_str : forall l0 : list byte,
  Z.of_nat (length (LLVMFuzzerTestOneInput_rn.nm_str (l0 ++ [Z_to_bv 8 0]))) <= Z.of_nat (length l0) /\
  forall j, 0 <= j <= Z.of_nat (length (LLVMFuzzerTestOneInput_rn.nm_str (l0 ++ [Z_to_bv 8 0]))) ->
    nth (Z.to_nat j) (LLVMFuzzerTestOneInput_rn.nm_str (l0 ++ [Z_to_bv 8 0]) ++ [0]) 0 =
    bv_unsigned (nth (Z.to_nat j) (l0 ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)).
Proof.
intros l0. set (s := LLVMFuzzerTestOneInput_rn.nm_str (l0 ++ [Z_to_bv 8 0])).
pose proof (LLVMFuzzerTestOneInput_rn.nm_split l0) as ES. fold s in ES.
set (t := LLVMFuzzerTestOneInput_rn.nm_rest (l0 ++ [Z_to_bv 8 0])) in ES.
assert (HL : length (l0 ++ [Z_to_bv 8 0]) = length (printf_facts_c.pf_bytes (s ++ [0]) ++ t)) by (rewrite <- ES; reflexivity).
unfold printf_facts_c.pf_bytes in HL. rewrite !length_app, length_map, length_app in HL. cbn [length] in HL.
split; [lia|].
intros j Hj. rewrite ES. unfold printf_facts_c.pf_bytes.
rewrite (app_nth1 (map (Z_to_bv 8) (s ++ [0])) t) by (rewrite length_map, length_app; cbn [length]; lia).
rewrite (map_nth (Z_to_bv 8) (s ++ [0]) 0 (Z.to_nat j)).
assert (HF : Forall (fun c => 0 <= c < 256) (s ++ [0])).
{ apply Forall_app. split; [|repeat constructor; lia].
  eapply Forall_impl; [|exact (LLVMFuzzerTestOneInput_rn.nm_str_ok _)]. cbv beta. intros c Hc. lia. }
assert (Hin : 0 <= nth (Z.to_nat j) (s ++ [0]) 0 < 256).
{ rewrite Forall_forall in HF. apply HF. apply nth_In. rewrite length_app. cbn [length]. lia. }
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. symmetry. apply Z.mod_small. exact Hin.
Qed.

(* The pointer `and a2, a0, s7` passes: given = c0_given op nm. *)
Lemma c0d_given : forall op nm, 0 <= op < 256 -> 0 <= nm < 2 ^ 64 ->
  alu64 ALU_AND (alu64 ALU_ADD (alu64 ALU_SRL (alu64 ALU_AND (w64 op) (Z_to_bv 64 8)) (Z_to_bv 64 3)) (Z_to_bv 64 (-1))) (w64 nm) =
  w64 (c0_given op nm).
Proof.
intros op nm Hop Hnm. unfold alu64, w64, c0_given. cbn [alu].
assert (Eop : bv_and (Z_to_bv 64 op) (Z_to_bv 64 8) = Z_to_bv 64 (Z.land op 8)).
{ apply bv_eq. rewrite bv_and_unsigned, !unsigned_lit_small by lia. rewrite unsigned_lit_small; [reflexivity|].
  pose proof (LLVMFuzzerTestOneInput_case0.c0_op8 op) as [-> | ->]; lia. }
assert (E3 : bv_and (Z_to_bv 64 3) (Z_to_bv 64 63) = Z_to_bv 64 3) by (apply bv_eq; reflexivity).
rewrite Eop, E3.
destruct (LLVMFuzzerTestOneInput_case0.c0_op8 op) as [H0 | H8]; rewrite ?H0, ?H8; cbn [Z.eqb].
- assert (Ea : (Z_to_bv 64 0 ≫ Z_to_bv 64 3 + Z_to_bv 64 (-1))%bv = Z_to_bv 64 (2 ^ 64 - 1)) by (apply bv_eq; reflexivity).
  rewrite Ea. apply bv_eq. rewrite bv_and_unsigned, !unsigned_lit_small by lia.
  replace (2 ^ 64 - 1) with (Z.ones 64) by reflexivity. rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
- assert (Ea : (Z_to_bv 64 8 ≫ Z_to_bv 64 3 + Z_to_bv 64 (-1))%bv = Z_to_bv 64 0) by (apply bv_eq; reflexivity).
  rewrite Ea. apply bv_eq. rewrite bv_and_unsigned, !unsigned_lit_small by lia. reflexivity.
Qed.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TDECL : treac_boxreg_declare_spec B.
Hypothesis HTAIL : asn_blk_tail_vis SEGS B.
Hypothesis HISV : img_shadow_vis SEGS B.
Hypothesis HGLOB : globs_marked SEGS B BX_G.
Hypothesis HMRG : Forall (fun g => IMG_LO + 64 <= fst g /\ fst g + snd g + 64 <= IMG_HI) BX_G.
Hypothesis HFMT : asn_rom_bytes SEGS B (VAL (A_OBJ 10)) ASN_FMT.
(* R2: the format below the image's GOT canary slot, which declare's spec asks for its snprintf call (P2) *)
Hypothesis HFMTg : VAL (A_OBJ 10) + 3 <= 0x99b40.
(* YC85.v cl_callS for a callee whose return configuration carries an FP state fx' of its own, related to the
   caller's by FX (the post of BoxBase.v apost_baseF). The journals take no FP state, so the proof is cl_callS's. *)
Lemma c0d_callF : forall (FX : YK11.FPState -> Prop) W (regsc : bvmap 5 word) memc pc STK sp0 FP ly S W0 mem md own lyc Sc
  mdc k STK1 FP1 EV1 (o : Z) raw ch1
  (K : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
  spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  achain lyc (aview SEGS (w_H W) memc) (sp0 + o) (s0Z regsc) ch1 ->
  (afn_pre SEGS B STK1 lyc Sc W regsc memc mdc ch1 ->
   SRr SEGS W (mkCfg (mkst regsc pc memc (seg_rom SEGS)) mdc)
   (fun W2 c2 => exists (fx' : YK11.FPState) ly2 S2 regs2 mem2 md2,
      c2 = mkCfg (@mkst fx' regs2 raw mem2 (seg_rom SEGS)) md2 /\ FX fx' /\
      ajournal SEGS B STK1 (spZ regsc) FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 EV1 /\
      aregs_preserved regsc regs2 /\ K ly2 S2 W2 regs2 mem2 md2)) ->
  (forall a, inFP FP1 a -> inFP FP a \/ in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
  SRr SEGS W (mkCfg (mkst regsc pc memc (seg_rom SEGS)) mdc)
  (fun W2 c2 => exists (fx' : YK11.FPState) ly2 S2 regs2 mem2 md2,
     c2 = mkCfg (@mkst fx' regs2 raw mem2 (seg_rom SEGS)) md2 /\ FX fx' /\
     ajournal SEGS B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + EV1) /\
     ajournal SEGS B STK1 (sp0 + o) FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 EV1 /\
     aregs_preserved regsc regs2 /\ K ly2 S2 W2 regs2 mem2 md2).
Proof.
intros FX W regsc memc pc STK sp0 FP ly S W0 mem md own lyc Sc mdc k STK1 FP1 EV1 o raw ch1 K
  HJ Hsp' Hal Hneg Hstk1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
eapply SRr_mono.
{ apply Hcallee. eapply (afn_pre_at SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k regsc STK1 o ch1);
  try eassumption.
  - rewrite Hra. exact Hraw.
  - unfold raZ. rewrite Hra. exact Hra4.
  - rewrite Hsp'. exact Hch. }
cbv beta. intros W2 c2 _ (fx' & ly2 & S2 & regs2 & mem2 & md2 & -> & HFX & HJ1 & HP & HK).
exists fx', ly2, S2, regs2, mem2, md2. split; [reflexivity|]. split; [exact HFX|]. rewrite Hsp' in HJ1.
split; [| split; [exact HJ1 | split; [exact HP | exact HK]]].
change own with ([] ++ own). eapply (ajournal_sub_tok SEGS B LAWS pa_segs_low); [exact HJ | exact HJ1 | lia | lia | exact HF].
Qed.

Theorem c0_decl : forall i POST,
  Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
  (forall fx' : YK11.FPState, lx_fxr fx fx' -> gb_from B MT POST (C0_D (fx := fx') B MT i)) ->
  gb_from B MT POST (C0_W B MT i).
Proof.
intros i POST HRM0 HD cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HI.
destruct HI as (r & bs & pos & op & nm & want & HMS & HTURN & HREG & HWANT & Hwr & H30 & R23 & R19 & R22 & R25 & R26 & R27).
destruct HTURN as (HMF & Hi & Hk & Hacc & HBL & HINV & Hpos & HCUR & Hnm & HNAME & Hop & Hop3 & R20).
pose proof HMS as (_ & _ & _ & _ & _ & _ & (G2 & G8 & G9 & G3 & G4 & G18 & G24)).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBok.
pose proof (pa_base_lo (PL := PL_box) (PI := PI)) as HBLO.
pose proof (c0_sp cx HB) as (Hsp & Hsp1 & Hsp32 & Hsp16). unfold GB_STK in Hsp.
pose proof asan_consts as (C1 & _).
set (E := Eimg (Ereg (ms_regs ms3) [])).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall q (r : bv 5), Z.of_nat q = bv_unsigned r -> ew E q = getr (ms_regs ms3) r)
  by (intros q r0 Hq; subst E; apply ew_Eimg_Ereg_nat; exact Hq).
assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx) by (rewrite (EE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; lia).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
assert (HS : st_ok_pi SEGS VAL E (mkSS GC_W sr_atoms [C0D_R58] None (mkFacts C0D_AF [] [])) (restrict (w_H W3) ms3)).
{ rewrite (c0_mkst cx fp GC_W ms3 (w_H W3) HMS). apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, C0D_R58. cbv zeta.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
    split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. apply (apresent_writable SEGS). apply HJpres. unfold GB_STK. lia.
  - cbn. repeat split.
  - split; [|split; exact I]. unfold C0D_AF. cbn [f_atoms atoms_ok]. split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9. split; [lia|]. split; [|lia]. change (2 ^ 5) with 32. exact Hsp32. }
assert (SHOK : sh_ok SEGS (SLit C0D_SB) [] E (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
paj_run_tok (paj_run B LAWS) HS HJ SHOK (C0D_SB, C0D_SB + 2 ^ 44 - 1).
{ cbn [ss_mem]. eapply (awr_ok_cons_stack_off E C0D_R58 [] GB_STK (spZ (c_regs cx)) [] _ _ ly3 [(GB_CID, fp)] 9%nat (c_sp1 cx - spZ (c_regs cx)));
  [reflexivity | rewrite U9; lia | cbn; unfold GB_STK; lia | cbn; lia | apply awr_ok_nil]. }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
prreg HS (13%bv : bv 5) Q13. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20.
prreg HS (22%bv : bv 5) Q22. prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26.
prreg HS (27%bv : bv 5) Q27.
pose proof HJ as (HAR3 & _).
assert (Hrin3 : In (r, REG_SIZE) (ablocks B ly3 S3)) by (rewrite HBL; apply in_or_app; right; left; reflexivity).
assert (Hnmin : In (nm, c0_nk cx pos + 1) (ablocks B ly3 S3)) by (rewrite HBL; apply in_or_app; right; right; left; reflexivity).
pose proof (LLVMFuzzerTestOneInput_rn.rn_k_range (c0_pl2 cx pos)) as Hnk. fold (c0_nk cx pos) in Hnk.
destruct (al_blocks _ _ LAWS _ _ _ _ _ r REG_SIZE HAR3 Hrin3) as (_ & Hr4096 & Hrceil & _). change (req_size REG_SIZE) with 288 in Hrceil.
destruct (al_blocks _ _ LAWS _ _ _ _ _ nm (c0_nk cx pos + 1) HAR3 Hnmin) as (_ & _ & Hnceil & _).
pose proof (req_size_pos (c0_nk cx pos + 1) ltac:(lia)) as Hrq.
assert (Hrnm : (r, REG_SIZE) <> (nm, c0_nk cx pos + 1)).
{ intros Ec. injection Ec as Er En. unfold REG_SIZE in En. lia. }
pose proof (sep_blocks SEGS B LAWS ly3 S3 W3 _ _ r REG_SIZE nm (c0_nk cx pos + 1) HAR3 Hrin3 Hnmin Hrnm) as Drn.
unfold zdisjoint in Drn. cbn [fst snd] in Drn. change (req_size REG_SIZE) with 288 in Drn.
assert (M1 : forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx + 0x58 <= a < c_sp1 cx + 0x60) ->
  aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha Hn. apply (c0_keep_outside E _ _ _ (w_H W3) a HF Ha). unfold in_wrange. cbn [ss_mem]. intros (rr & [<- | []] & Hb). unfold C0D_R58 in Hb. cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Hb. rewrite U9 in Hb. lia. }
assert (S58 : rdword (aview SEGS (w_H W3) (ms_mem ms)) (c_sp1 cx + 0x58) = Some nm).
{ pose proof (st_ok_region_nth E _ _ 0 _ HS eq_refl) as HR58. cbn [ms_mem restrict] in HR58.
  pose proof (field_of_region_any E _ 9%nat (c_sp1 cx) _ _ _ _ _ 0x58 8%N (SOff 23 0) HR58 U9 ltac:(left; reflexivity) ltac:(cbn; lia)) as V.
  rewrite c0_denot_off0, (EE 23%nat 23%bv eq_refl), R23 in V. unfold w64 in V. rewrite unsigned_lit_small in V by lia.
  apply (rdword_of_val_mem SEGS). rewrite Z.mod_small in V by (cbn; lia). exact V. lia. }
rewrite pa_sigma_reac_boxreg_declare.
assert (Usp : spZ (ms_regs ms) = c_sp1 cx) by (unfold spZ; rewrite Q2, (EE 2%nat 2%bv eq_refl), G2; unfold w64; apply unsigned_lit_small; lia).
pose proof HB as (HPRE0 & _ & _ & _ & _ & _ & _ & _ & HARO & _).
pose proof HPRE0 as (_ & _ & _ & Hgp & Htp & _).
pose proof (c0_geo LAWS cx fp k ly3 S3 W3 _ _ HB HJ HFR) as (Hinp & _ & HF0 & HF1 & _ & HSH).
assert (ZR : forall a, c0_zone cx fp a -> 0 <= a < 2 ^ 64) by (intros a; apply c0_zone_range; first [exact Hinp | lia | exact HSH]).
assert (ZN : forall a, c0_zone cx fp a -> ~ (c_sp1 cx + 0x58 <= a < c_sp1 cx + 0x60)).
{ intros a Ha. pose proof (ZR a Ha) as Ha64. destruct Ha as [Ha|[Ha|[Ha|Ha]]]; [lia | destruct Hinp; lia | lia |].
  rewrite HSH in Ha. unfold SHADOW_OFF in *.
  pose proof (Z.div_le_upper_bound (gF cx fp) 8 (2 ^ 44) ltac:(lia) ltac:(lia)). lia. }
assert (HMF1 : c0_mf i cx fp W3 ms r bs).
{ apply (c0_mf_keep i cx fp W3 ms3 ms r bs HB); [intros a Ha; apply M1; [exact (ZR a Ha) | exact (ZN a Ha)] | exact HMF]. }
assert (HCH : achain ly3 (aview SEGS (w_H W3) (ms_mem ms)) (c_sp1 cx) (spZ (c_regs cx)) (gch cx)).
{ apply (c0_achain cx fp k ly3 S3 W3 _ _ _ HB HJ); [| lia]. exact (proj1 HMF1). }
assert (HARO1 : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W3) (ms_mem ms)))
  by exact (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HARO).
eapply SRr_bind.
{ eapply (c0d_callF (lx_fxr fx) W3 (ms_regs ms) (ms_mem ms) _ GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GB_CID, fp)] ly3 S3 _ k REAC_BOXREG_DECLARE_STK [(r, r + REG_SIZE)] 0 (c_sp1 cx - spZ (c_regs cx))
    (Z_to_bv 64 (BASE + 2580)) (gch cx) _ HJ).
  - rewrite Usp. lia.
  - apply c0_sub_mod16; [exact Hsp32 | exact Hsp16].
  - lia.
  - change REAC_BOXREG_DECLARE_STK with 8288. lia.
  - change REAC_BOXREG_DECLARE_STK with 8288. unfold GB_STK. lia.
  - rewrite Q3, (EE 3%nat 3%bv eq_refl), G3. exact Hgp.
  - rewrite Q4, (EE 4%nat 4%bv eq_refl), G4. exact Htp.
  - exact Q1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite unsigned_lit_small by lia. lia.
  - replace (spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx))) with (c_sp1 cx) by lia.
    replace (s0Z (ms_regs ms)) with (spZ (c_regs cx)); [exact HCH|].
    unfold s0Z. rewrite Q8, (EE 8%nat 8%bv eq_refl), G8. unfold w64. symmetry. apply unsigned_lit_small. lia.
  - intros HPRE1.
    assert (HNOK : tdecl_name_ok B ly3 S3 W3 (ms_mem ms) r (c0_given op nm) (c0_gs cx pos op)).
    { unfold c0_given, c0_gs. destruct (LLVMFuzzerTestOneInput_case0.c0_op8 op) as [H0 | H8]; rewrite ?H0, ?H8; cbn [Z.eqb].
      - right. unfold c0_s.
        pose proof (LLVMFuzzerTestOneInput_rn.rn_name_len (c0_pl2 cx pos)) as Hbl. fold (c0_nk cx pos) in Hbl.
        unfold c0_nb. destruct (c0d_nm_str (Boxreg.bsub (c0_pl2 cx pos) 1 (c0_nk cx pos))) as (Hsl & Hsb).
        split; [lia|]. split; [apply LLVMFuzzerTestOneInput_rn.nm_str_ok|]. split; [lia|].
        exists (c0_nk cx pos + 1). split; [exact Hnmin|]. split; [lia|]. split; [unfold REG_SIZE; lia|].
        intros j Hj. rewrite M1 by lia. rewrite (HNAME j) by lia. unfold c0_nb. rewrite (Hsb j Hj). reflexivity.
      - left. split; reflexivity. }
    eapply SRr_mono.
    { pose proof (TDECL ly3 S3 W3 (ms_regs ms) (ms_mem ms) _ (gch cx) r (c0_nch cx pos) (c0_given op nm) (c0_base cx pos) bs (c0_gs cx pos op) BX_G HPRE1) as HC.
      unfold cfg_at, A_reac_boxreg_declareP, w64 in HC. eapply HC.
      - exact HARO1.
      - rewrite Q10, (EE 20%nat 20%bv eq_refl), R20. reflexivity.
      - rewrite Q11, (EE 19%nat 19%bv eq_refl), R19. reflexivity.
      - rewrite Q12, (EE 22%nat 22%bv eq_refl), (EE 23%nat 23%bv eq_refl), R22, R23. apply c0d_given; lia.
      - rewrite Q13, (EE 27%nat 27%bv eq_refl), R27. reflexivity.
      - pose proof (LLVMFuzzerTestOneInput_case0.c0_nch_range (c0_pl cx pos)). unfold c0_nch. lia.
      - pose proof (LLVMFuzzerTestOneInput_case0.c0_base_range (c0_pl cx pos)). unfold c0_base. lia.
      - exact Hrin3.
      - intros j Hj. destruct HREG as (_ & _ & HRB). rewrite M1 by (unfold REG_SIZE in Hj; lia). exact (HRB j Hj).
      - exact HINV.
      - exact HNOK.
      - exact HTAIL.
      - exact HISV.
      - exact HGLOB.
      - unfold A_declare_fmtP. exact HFMT.
      - unfold A_declare_fmtP, BX_G. cbn [In]. tauto.
      - rewrite Forall_forall in HMRG. pose proof (HMRG (VAL (A_OBJ 10), 3) ltac:(unfold BX_G; cbn [In]; tauto)) as Hm. cbn [fst snd] in Hm.
        unfold A_declare_fmtP. lia.
      - rewrite Forall_forall in HMRG. pose proof (HMRG (VAL (A_OBJ 10), 3) ltac:(unfold BX_G; cbn [In]; tauto)) as Hm. cbn [fst snd] in Hm.
        unfold A_declare_fmtP. lia.
      - unfold A_declare_fmtP. exact HFMTg.
      - exact HRM0. }
    cbv beta. intros W2 c2 _ (fxr & ly2 & S2 & regs2 & mem2 & md2 & -> & HFRr & HFCr & HJ1 & HP & HQ).
    exists fxr, ly2, S2, regs2, mem2, md2. split; [rewrite Q1; reflexivity|].
    split; [unfold lx_fxr; exact (conj HFRr HFCr)|]. split; [exact HJ1|]. split; [exact HP|]. exact HQ.
  - intros a ((lo & hi) & [Ef | []] & Ha). injection Ef as <- <-. cbn [fst snd] in Ha. right.
    exists r, REG_SIZE. split; [exact Hrin3|]. split; [|change (req_size REG_SIZE) with 288; unfold REG_SIZE in Ha; lia].
    intros Hc. apply in_split in Hc as (l1 & l2 & El).
    apply (c0_blk_twice LAWS ly3 S3 W3 _ _ l1 l2 [(nm, c0_nk cx pos + 1)] (r, REG_SIZE) HAR3); [|cbn [snd]; unfold REG_SIZE; lia].
    rewrite HBL, El. rewrite <- !app_assoc. reflexivity. }
cbv beta. intros W2 c2 Hwle2 (fx2 & ly2 & S2 & regs2 & mem2 & md2 & -> & HFX & HJ2 & HJc & HP2 & (-> & -> & -> & HPERM & HRES)).
rewrite Z.add_0_r in HJ2.
replace (spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx))) with (c_sp1 cx) in HJc by lia.
assert (KP2 : forall r0 : bv 5, acallee_saved (bv_unsigned r0) -> getr regs2 r0 = getr (ms_regs ms) r0)
  by (intros r0 Hr; pose proof (HP2 (bv_unsigned r0) Hr) as X; rewrite Z_to_bv_bv_unsigned in X; exact X).
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & K1 & K2 & _ & K4 & _).
assert (Hrnot : ~ In (r, REG_SIZE) (ablocks B (c_ly cx) (c_S cx))).
{ intros Hc. apply in_split in Hc as (l1 & l2 & El).
  apply (c0_blk_twice LAWS ly3 S3 W3 _ _ l1 l2 [(nm, c0_nk cx pos + 1)] (r, REG_SIZE) HAR3); [|cbn [snd]; unfold REG_SIZE; lia].
  rewrite HBL, El. rewrite <- !app_assoc. reflexivity. }
assert (Hsub3 : forall p n, In (p, n) (ablocks B (c_ly cx) (c_S cx)) -> In (p, n) (ablocks B ly3 S3))
  by (intros p n Hp; rewrite HBL; apply in_or_app; left; exact Hp).
assert (HNB : c0_newblk B cx ly3 S3 (fun a => r <= a < r + req_size REG_SIZE)).
{ intros a Ha. exists r, REG_SIZE. split; [exact Hrin3|]. split; [exact Hrnot | exact Ha]. }
assert (NFP : forall a, ~ (r <= a < r + req_size REG_SIZE) -> ~ inFP [(r, r + REG_SIZE)] a).
{ intros a Hn ((lo & hi) & [Ef | []] & Hx). injection Ef as <- <-. cbn [fst snd] in Hx. apply Hn.
  change (req_size REG_SIZE) with 288. unfold REG_SIZE in Hx. lia. }
assert (KZ : forall a, c0_zone cx fp a -> aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) (ms_mem ms) a).
{ apply (c0_zone_blocks LAWS cx fp k ly3 S3 W3 (ms_mem ms) _ (fun a => r <= a < r + req_size REG_SIZE)
    (fun a => aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) (ms_mem ms) a) HB HJ HFR Hsub3 HNB).
  - intros a Ha Hs. apply K1; [lia | change REAC_BOXREG_DECLARE_STK with 8288; lia].
  - intros b m j Hb Hj He. apply (K2 b m j Hb Hb Hj). apply NFP. exact He.
  - intros a Hz He. apply (K4 GB_CID fp a); [rewrite HFR; left; reflexivity | exact Hz | apply NFP; exact He]. }
assert (KZall : forall a, c0_zone cx fp a -> aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha. rewrite KZ by exact Ha. apply M1; [exact (ZR a Ha) | exact (ZN a Ha)]. }
set (ms2 := @mkst fx2 regs2 (Z_to_bv 64 (BASE + 2580)) mem2 (seg_rom SEGS)).
assert (HMF2 : c0_mf i cx fp W3 ms2 r bs) by exact (c0_mf_keep2 i cx fp W3 W3 ms3 ms2 r bs HB KZall HMF).
assert (KHI : forall a, c_sp1 cx <= a < 2 ^ 64 -> aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) (ms_mem ms) a)
  by (intros a Ha; apply K1; [lia | change REAC_BOXREG_DECLARE_STK with 8288; lia]).
assert (KS : forall off v, 0 <= off < 0x98 -> (off + 8 <= 0x58 \/ 0x60 <= off) -> gslot cx W3 ms3 off v -> gslot cx W3 ms2 off v).
{ intros off v Hoff Hw Hv. unfold gslot in *. subst ms2. cbn [ms_mem mkst]. rewrite <- Hv. apply rdword_ext. intros j Hj.
  rewrite KHI by lia. apply M1; lia. }
assert (S58' : gslot cx W3 ms2 0x58 nm).
{ unfold gslot. subst ms2. cbn [ms_mem mkst]. rewrite <- S58. apply rdword_ext. intros j Hj. apply KHI. lia. }
assert (HNAME2 : c0_name cx W3 ms2 pos nm).
{ intros j Hj. subst ms2. cbn [ms_mem mkst].
  rewrite (K2 nm (c0_nk cx pos + 1) j Hnmin Hnmin) by (first [lia | apply NFP; change (req_size REG_SIZE) with 288; lia]).
  rewrite M1 by lia. exact (HNAME j Hj). }
assert (KR : forall (q : nat) (r0 : bv 5) v, acallee_saved (bv_unsigned r0) -> Z.of_nat q = bv_unsigned r0 ->
  getr (ms_regs ms) r0 = ew E q -> getr (ms_regs ms3) r0 = v -> getr regs2 r0 = v).
{ intros q r0 v Hcs Hq HQ HV. rewrite KP2 by exact Hcs. rewrite HQ, (EE q r0 Hq). exact HV. }
eapply (HD fx2 HFX cx fp k acc ly3 S3 W3 ms2 md2 HB HJ2 HFR HMO).
unfold C0_D. exists r, bs, pos, op, nm, want.
pose proof HREG as (_ & HL & _).
split.
{ apply (c0_ms_mkst cx fp GC_D regs2 regs2 mem2 (Z_to_bv 64 0)); [|intros; reflexivity].
  unfold gregs. cbn [ms_regs mkst].
  split; [exact (KR 2%nat 2%bv _ ltac:(c0_cs) eq_refl Q2 G2)|].
  split; [exact (KR 8%nat 8%bv _ ltac:(c0_cs) eq_refl Q8 G8)|].
  split; [exact (KR 9%nat 9%bv _ ltac:(c0_cs) eq_refl Q9 G9)|].
  split; [exact (KR 3%nat 3%bv _ ltac:(c0_cs) eq_refl Q3 G3)|].
  split; [exact (KR 4%nat 4%bv _ ltac:(c0_cs) eq_refl Q4 G4)|].
  split; [exact (KR 18%nat 18%bv _ ltac:(c0_cs) eq_refl Q18 G18)|].
  exact (KR 24%nat 24%bv _ ltac:(c0_cs) eq_refl Q24 G24). }
split.
{ split; [exact HMF2|]. split; [exact Hi|]. split; [exact Hk|]. split; [exact Hacc|]. split; [exact HBL|].
  split; [exact HINV|]. split; [exact Hpos|].
  split; [destruct HCUR as (Hp & C88 & C90); split; [exact Hp|]; split; [apply KS; [lia | lia | exact C88] | apply KS; [lia | lia | exact C90]]|].
  split; [exact Hnm|]. split; [exact HNAME2|]. split; [exact Hop|]. split; [exact Hop3|].
  exact (KR 20%nat 20%bv _ ltac:(c0_cs) eq_refl Q20 R20). }
split; [exact HWANT|]. split; [exact Hwr|].
split; [apply KS; [lia | lia | exact H30]|].
split; [exact S58'|].
split; [exact (KR 19%nat 19%bv _ ltac:(c0_cs) eq_refl Q19 R19)|].
split; [exact (KR 22%nat 22%bv _ ltac:(c0_cs) eq_refl Q22 R22)|].
split.
{ subst ms2. cbn [ms_regs mkst]. rewrite KP2 by c0_cs. rewrite Q25, (EE 22%nat 22%bv eq_refl), R22.
  unfold alu64, w64. cbn [alu]. apply bv_eq. rewrite bv_and_unsigned, !unsigned_lit_small by lia.
  rewrite unsigned_lit_small; [reflexivity|]. pose proof (LLVMFuzzerTestOneInput_case0.c0_op8 op) as [-> | ->]; lia. }
split; [exact (KR 26%nat 26%bv _ ltac:(c0_cs) eq_refl Q26 R26)|].
split; [exact (KR 27%nat 27%bv _ ltac:(c0_cs) eq_refl Q27 R27)|].
destruct HRES as [(Href & Ha0 & Hbytes) | (b & p & Hpl & Ha0 & Hbytes)].
- left. split; [exact Href|]. split; [split; [exact Hrin3|]; split; [exact HL | exact Hbytes]|]. exact Ha0.
- right. exists b, p. split; [exact Hpl|]. split; [|exact Ha0].
  split; [exact Hrin3|]. split; [|exact Hbytes].
  pose proof HINV as ((_ & HB1 & _) & _). unfold Boxreg.boxreg_B1 in HB1. pose proof Hpl as (_ & Hn5 & _).
  exact (LLVMFuzzerTestOneInput_case0.c0_decl_length bs b (c0_nch cx pos) p (c0_gs cx pos op) HL ltac:(lia)).
Qed.

End c.
End b.
End a.
