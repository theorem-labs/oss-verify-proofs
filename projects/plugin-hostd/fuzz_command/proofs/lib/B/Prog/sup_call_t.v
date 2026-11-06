(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of descriptors_get (plugin-hostd/fuzz_command.asan) from the join of
   record()'s arms to the tail jump into answer, after proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v and ACh2.v (a walk
   segment: run, call out by cl_callS, resume) over fuzz_command's listing. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/descriptors_get_s3.v, with its module paths and module names changed; 464 of its 502 lines of code are new or changed and 975 lines of the source are left out. *)
(* sup_call's walk on the ASan+UBSan build of plugin-hostd/fuzz_command (fuzz_command.asan-ubsan, entry 0x8af34),
   part t (sup_call_s3.v SC_L_stmt): from answer's entry (the `jal answer` at 0x8b08c taken, sc_at_l) to sup_call's
   post. answer(c, "resp 0", 1) runs through its contract (answer_c.v tanswer_spec at the walk's FP state) by PaFx.v's
   cl_callS_pgF: g_rec.answer and g_rec.state are program statics of the image inside SC_FP, the old answer's block
   is one of the recorder's blocks, so a block of O or a block new since the entry (in_tmp_block). answer returns at
   0x8b090 at some FP state fx2 (srr_after_callF_base); the rest is the segment sc_t_rel, proved at its own ambient
   FP state and applied at fx2: the frame state sc_mid_ss (sup_call_s1.v sc_seed, from sc_live after answer: the
   journal k + EV_ANSWER, the callee-saved registers, and the saves and the flag-byte word F + 56 that answer's
   journal keeps), with s2 := s8 (both are F, sc_regs) and the flag byte FL as a region of its own; one run of the
   flag-store executor (PaLibF.v aj_flag_store_pi) through 0x8b090 .. 0x8b120: the magic 0x45e0360e at F, `beqz s2`
   not taken, the shadow f5 x 8, `ld a1,56(s2)` (= FL), `sb zero,0(a1)` (the frame (0, fpos) is released), `j`,
   the epilogue `addi sp,s0,-96` and the 11 reloads, `addi sp,sp,96`; then `ret` (paj_ret_at) and the post.

   The post (sup_call_s3.v sc_post): the journal ends at stack_free_state 0 fpos with no own frame, the
   callee-saved registers are the saves' (the entry's) or the entry's own (sp, gp, tp, s10, s11), and sc_Q's
   recorder and block facts come from answer's post and sc_blk (as the A walk's tail, an earlier version of
   lib/A/Prog/sup_call_t.v, lines 294-331); the release writes only the frame header, the frame's shadow and the flag
   byte, which no recorder byte and no live block meets (sc_t_apart); the recorder, live-block and shape helpers are the kit's CmdRecAns.v. The answer step is the B twin of
   the sup_remove_all B walk's sup_remove_all_s3.v (sra_tail); the release is the twin of A's sup_resp
   walk (an earlier version of lib/A/Prog/sup_resp.v, lines 618-747). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI09 YG0s YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v YI0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdList CmdPa CmdPaLib PaLibG PaDenot PaLibF PaLibH.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaSB PaCallRun PaCall PaCallPg PaFx RecBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh CmdChk.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import xmalloc_c hand_back_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import record_c arg_s_c arg_line_c answer_c sup_call_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import sup_call_s3 sup_call_s0 sup_call_s1.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecBase CmdRecRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecAns.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* after each symbolic run the model is left as `with_vm_backing (m_vm_lazy md) mat md` (sup_resp.v:50-54) *)
Ltac sc_t_collapse_md :=
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdl) _ =>
first [ is_var mdl | let mdv := fresh "mdv" in set (mdv := mdl) in *; clearbody mdv ] end.

(* ---- the recorder's representation: CmdRecAns.v's rca_* (the kit's text of sup_remove_all_s1.v:33-91 at 721a33d7c2d) ---- *)
(* the recorder's blocks are live blocks *)
Lemma sc_t_rep_live : forall B ly S rd R O pn, rec_repA B ly S rd R O -> In pn O -> In pn (ablocks B ly S).
Proof. intros B ly S rd R O pn (Q & HQ & HO) Hin. exact (rca_rep_blocks _ _ _ _ _ _ pn HQ (proj1 (HO pn) Hin)). Qed.


(* ---- the release segment, at its own ambient FP state ---- *)
Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* a byte outside a run's write windows keeps its view (sup_resp.v:66-69) *)
Lemma sc_t_frame_kept : forall E rs H (m m' : word -> option byte) a,
  frame_of E rs (mrestrict H m) (mrestrict H m') -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a ->
  aview SEGS H m' a = aview SEGS H m a.
Proof. intros E rs H m m' a Hf Ha Hw. apply aview_eq_of. apply Hf. rewrite unsigned_lit_small by lia. exact Hw. Qed.

Section e.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.

(* a byte of a live block or of the image is none of the bytes the release writes: the frame (0, fpos) (AR's
   separation; frames lie off the image), its 8 shadow bytes (blocks and the image lie in application memory) and
   the flag byte (owned by the allocator, off the image) *)
Lemma sc_t_apart : forall ly2 S2 (W2 : world SEGS) mem2 md2 fpos F FL a,
  AR SEGS B ly2 S2 W2 mem2 md2 -> In (0, fpos) (frames S2) -> frame_addr ly2 0 fpos = F -> flag_addr ly2 0 fpos = FL ->
  ((exists p n, In (p, n) (ablocks B ly2 S2) /\ p <= a < p + req_size n) \/ in_img SEGS a) ->
  0 <= a < 2 ^ 64 /\ ~ (F <= a < F + 64) /\ ~ (SB + F / 8 <= a < SB + F / 8 + 8) /\ a <> FL.
Proof.
intros ly2 S2 W2 mem2 md2 fpos F FL a HAR Hfin EF EFL Ha.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 0 fpos HAR Hfin) as (HF4096 & HFceil & HFhigh).
destruct (FFL ly2 S2 W2 mem2 md2 0 fpos HAR Hfin) as (HFLpres & HFLown & (HFLapp & HFLni) & HFL4096 & HFLz & HFLceil).
rewrite EF in HF4096, HFceil, HFhigh. rewrite EFL in HFLpres, HFLown, HFLapp, HFLni, HFL4096, HFLz, HFLceil.
change (fs_frame_bytes 0) with 64 in *.
assert (HF8hi : F / 8 < 0x0fffffff0000) by (apply Z.div_lt_upper_bound; lia).
assert (HF8lo : 0 <= F / 8) by (apply Z.div_pos; lia).
destruct Ha as [(p & n & Hin & Hr) | Himg].
- destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & Hp4k & Hpceil & Hpapp & Hpown & _ & Hn0).
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ 0 fpos HAR Hin Hfin) as Hsep.
  rewrite EF in Hsep. unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. change (fs_frame_bytes 0) with 64 in Hsep.
  assert (Happ : p + req_size n <= kLowShadowBeg \/ kHighMemBeg <= p) by (unfold in_app in Hpapp; lia).
  unfold kLowShadowBeg, kHighMemBeg in Happ.
  split; [lia|]. split; [lia|]. split; [unfold SB; lia|].
  intros Ha. subst a. exact (proj2 (Hpown FL Hr) HFLown).
- pose proof (pa_segs_low a Himg) as Hlo.
  split; [lia|].
  split; [intros Hf; exact (frm_img SEGS B LAWS _ _ _ _ _ 0 fpos a HAR Hfin
    ltac:(rewrite EF; change (fs_frame_bytes 0) with 64; lia) Himg)|].
  split; [unfold SB; lia|].
  intros Ha. subst a. exact (HFLni Himg).
Qed.

(* 0x8b090 .. 0x8b124: the release of the frame and the return, from the frame state after answer; Q is the post
   predicate, which the caller proves at the released state from its own facts: a0 kept, and every byte off the
   frame, its shadow and the flag byte kept *)
Lemma sc_t_rel : forall ly S (W : world SEGS) (regs : bvmap 5 word) mem md (O : list (Z * Z)) fpos F FL
  ly2 S2 (W2 : world SEGS) (regs2 : bvmap 5 word) mem2 md2 k
  (Q : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
YK0s.ret_ok (getr regs 1) ->
sc_live B ly S W regs mem md O fpos F FL ly2 S2 W2 regs2 mem2 md2 k ->
(forall (regs' : bvmap 5 word) mem' md', getr regs' 10 = getr regs2 10 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (F <= a < F + 64) -> ~ (SB + F / 8 <= a < SB + F / 8 + 8) -> a <> FL ->
    rdW W2 mem' a = rdW W2 mem2 a) ->
  Q ly2 (stack_free_state 0 fpos S2) W2 regs' mem' md') ->
SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + (AF_sup_call + SC_PC_R))) mem2 (seg_rom SEGS)) md2)
  (apost_base SEGS B SUP_CALL_STK (SC_FP O) regs ly S W mem md k Q).
Proof.
intros ly S W regs mem md O fpos F FL ly2 S2 W2 regs2 mem2 md2 k Q Hra HL HQ.
pose proof pa_B_ok as HBASE. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (aj_flag_store_pi (PL := PL_cmd) (PI := PI) B LAWS ML ASF FFL) as RUNF.
pose proof (paj_ret_at (PL := PL_cmd) (PI := PI)) as RET.
(* the frame state at 0x8b090: no shadow byte known, the shadow window [0, 8) *)
pose proof (sc_seed B LAWS FFL SC_PC_R ly S W regs mem md O fpos F FL ly2 S2 W2 regs2 mem2 md2 k [] 0 8 HL
  (Forall_nil _) eq_refl ltac:(lia) ltac:(lia) ltac:(lia)) as HS0.
destruct HL as (HJ & EF & EFL & HRG & HFR & HFLW).
destruct HRG as (Esp & E8 & E18 & E24 & E19 & E20 & E21 & E23 & E25 & E3 & E4 & E26 & E27).
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (Hfin : In (0, fpos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HAR Hfin) as (HFal & [HFhi _] & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 0 fpos HAR Hfin) as (HF4096 & HFceil & HFhigh).
destruct (FFL ly2 S2 W2 mem2 md2 0 fpos HAR Hfin) as (HFLpres & HFLown & HFLrng).
change (fs_frame_bytes 0) with 64 in HFpres, HFSpres, HF4096, HFceil, HFhigh.
rewrite EF in HFpres, HFSpres, HF4096, HFceil, HFhigh. rewrite EFL in HFLpres, HFLown, HFLrng.
unfold shadow_addr in HFSpres. rewrite <- SB_SHADOW_OFF in HFSpres. change (64 / 8) with 8 in HFSpres.
pose proof HFLrng as ((HFLapp & HFLni) & HFL4096 & HFLz & HFLceil).
pose proof (sc_sp1_bounds (spZ regs)) as (Hsp1 & Hsp1al).
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
assert (HF8m : 8 * (F / 8) <= F) by (apply Z.mul_div_le; lia).
assert (FFS : SUP_CALL_STK = ltac:(let v := eval vm_compute in SUP_CALL_STK in exact v)) by reflexivity.
(* the frame state's environment: atoms 0 .. 31 the registers at 0x8b090, 32 the flag address, 33 .. 43 the saves *)
set (E := sc_mid_E regs regs2 FL) in HS0.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold sc_mid_E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
  by (intros n r Hn; subst E; unfold sc_mid_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 FL)
  by (subst E; unfold sc_mid_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (EX : forall j r, nth_error sc_saved j = Some r -> ew E (33 + j) = getr regs (Z_to_bv 5 r)).
{ intros j r Hj. subst E. unfold sc_mid_E.
  assert (Hj11 : (j < length sc_saved)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
  change (length sc_saved) with 11%nat in Hj11.
  rewrite Eimg_low by (unfold A_TEXT; lia).
  replace (33 + j)%nat with (32 + Datatypes.S j)%nat by lia. rewrite ew_Ereg_extra. unfold sc_mid_extra. cbn [nth].
  apply nth_error_nth. rewrite nth_error_map, Hj. reflexivity. }
clearbody E.
assert (U8 : bv_unsigned (ew E 8) = spZ regs) by (rewrite (EE 8%nat 8%bv eq_refl), E8; reflexivity).
assert (U23 : bv_unsigned (ew E 23) = SB + F / 8)
  by (rewrite (EE 23%nat 23%bv eq_refl), E23; unfold w64; apply unsigned_lit_small; unfold SB; lia).
assert (U24 : bv_unsigned (ew E 24) = F)
  by (rewrite (EE 24%nat 24%bv eq_refl), E24; unfold w64; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = FL) by (rewrite E32; apply unsigned_lit_small; lia).
(* s2 := s8: both registers hold F (sc_regs), so the release's `beqz s2` and `ld a1,56(s2)` see the header's base *)
pose proof (ast_ok_pi_set_reg_fp E _ _ 18%bv (SOff 24 0) HS0 eq_refl
  ltac:(cbn [ms_regs restrict mkst]; rewrite sv_denot_SOff0, (EE 24%nat 24%bv eq_refl), E24, E18; reflexivity)) as HS1.
clear HS0.
(* the flag byte FL (atom 32) is a region of its own: present, owned by the allocator, so outside the frame and its
   shadow, and below the stack *)
assert (HnoF : FL < F \/ F + 64 <= FL).
{ destruct (Z_lt_ge_dec FL F) as [Hl|Hl]; [left; exact Hl|].
  destruct (Z_lt_ge_dec FL (F + 64)) as [Hh|Hh]; [exfalso | right; lia].
  exact (proj2 (HFpres FL ltac:(lia)) HFLown). }
assert (HnoS : FL < SB + F / 8 \/ SB + F / 8 + 8 <= FL).
{ destruct (Z_lt_ge_dec FL (SB + F / 8)) as [Hl|Hl]; [left; exact Hl|].
  destruct (Z_lt_ge_dec FL (SB + F / 8 + 8)) as [Hh|Hh]; [exfalso | right; lia].
  pose proof (proj2 (HFSpres (FL - (SB + F / 8)) ltac:(lia))) as Hn.
  replace (SB + F / 8 + (FL - (SB + F / 8))) with FL in Hn by lia. exact (Hn HFLown). }
assert (HFLsp : FL + 1 <= spZ regs - 88) by (rewrite FFS in Hslo; lia).
assert (HRF : region_ok SEGS E (ms_mem (restrict (w_H W2)
    (mkst regs2 (Z_to_bv 64 (BASE + (AF_sup_call + SC_PC_R))) mem2 (seg_rom SEGS))))
  (YP09.mkRegion (Some 32%nat) 0 1 0 1 [])).
{ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst].
  rewrite U32. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
  intros o Ho. apply (apresent_writable SEGS). replace (FL + o) with FL by lia. exact HFLpres. }
assert (HDF : all_disjoint E (YP09.mkRegion (Some 32%nat) 0 1 0 1 []) (sc_mid_regions [] 0 8)).
{ unfold sc_mid_regions, sc_mid_shadow, sc_mid_hdr, sc_mid_flagw, sc_mid_saves.
  cbn [all_disjoint]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite U32, U23, U24, U8.
  clear - HnoF HnoS HFLsp HF8m HF8lo.
  repeat match goal with |- _ /\ _ => split | |- True => exact I end; lia. }
pose proof (st_ok_pi_add_region E _ _ (YP09.mkRegion (Some 32%nat) 0 1 0 1 []) HS1 eq_refl HRF HDF) as HS2.
clear HS1 HRF HDF.
norm_ssp HS2.
(* 0x8b090 .. 0x8b120: the magic, `beqz s2` falls through (F <> 0), the frame's shadow f5, the flag byte := 0 (the
   frame is released), `j`, the epilogue, up to `ret` *)
paj_run_flag_sh RUNF HS2 HJ.
- lia.
- intros a (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [<- | Hin];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U32, ?U23, ?U24, ?U8 in Hr;
      first [ exfalso; clear - Hr; lia
            | right; rewrite EFL; lia
            | left; right; right; right; left; exists 0, fpos; split; [left; reflexivity|]; rewrite EF;
              first [ left; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 0) with 64; lia
                    | right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite <- SB_SHADOW_OFF;
                      change (fs_frame_bytes 0 / 8) with 8; lia ] ] | ]).
  destruct Hin.
- intros msr HSr. rewrite EFL.
  lazymatch type of HSr with st_ok_pi _ _ ?Ex ?ssx _ =>
  pose proof (st_ok_pi_region_nth Ex ssx msr 0 _ HSr eq_refl) as HR;
  lazymatch type of HR with region_ok _ _ _ (YP09.mkRegion (Some ?n) ?lo ?hi ?wlo ?whi ?cs) =>
  pose proof (field_of_region Ex (ms_mem msr) n FL cs lo hi wlo whi 0 1%N (SLit 0) 0 HR U32
    ltac:(cbn [In]; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V end end.
  rewrite Z.add_0_r in V. pose proof (V 0%nat ltac:(lia)) as V0. cbn [Z.of_nat] in V0. rewrite Z.add_0_r in V0.
  exact V0.
- sc_t_collapse_md.
  lazymatch goal with |- SRr _ _ (mkCfg ?msX _) _ => rename msX into msF end.
  lazymatch goal with HFx : frame_of _ _ (mrestrict _ _) (mrestrict _ (ms_mem msF)) |- _ => rename HFx into HFrF end.
  cbn [ms_mem mkst] in HFrF.
  (* 0x8b124: ret *)
  prreg HS2 (1%bv : bv 5) F1. prreg HS2 (2%bv : bv 5) F2. prreg HS2 (3%bv : bv 5) F3. prreg HS2 (4%bv : bv 5) F4.
  prreg HS2 (8%bv : bv 5) F8. prreg HS2 (9%bv : bv 5) F9. prreg HS2 (10%bv : bv 5) F10.
  prreg HS2 (18%bv : bv 5) F18. prreg HS2 (19%bv : bv 5) F19. prreg HS2 (20%bv : bv 5) F20.
  prreg HS2 (21%bv : bv 5) F21. prreg HS2 (22%bv : bv 5) F22. prreg HS2 (23%bv : bv 5) F23.
  prreg HS2 (24%bv : bv 5) F24. prreg HS2 (25%bv : bv 5) F25. prreg HS2 (26%bv : bv 5) F26.
  prreg HS2 (27%bv : bv 5) F27.
  assert (X1 : ew E 33 = getr regs 1) by exact (EX 0%nat 1 eq_refl).
  assert (HPF : aregs_preserved regs (ms_regs msF)).
  { apply aregs_preserved_eqs.
    - rewrite F2, (EE 8%nat 8%bv eq_refl). exact E8.
    - rewrite F3, (EE 3%nat 3%bv eq_refl). exact E3.
    - rewrite F4, (EE 4%nat 4%bv eq_refl). exact E4.
    - rewrite F8. exact (EX 1%nat 8 eq_refl).
    - rewrite F9. exact (EX 2%nat 9 eq_refl).
    - rewrite F18. exact (EX 3%nat 18 eq_refl).
    - rewrite F19. exact (EX 4%nat 19 eq_refl).
    - rewrite F20. exact (EX 5%nat 20 eq_refl).
    - rewrite F21. exact (EX 6%nat 21 eq_refl).
    - rewrite F22. exact (EX 7%nat 22 eq_refl).
    - rewrite F23. exact (EX 8%nat 23 eq_refl).
    - rewrite F24. exact (EX 9%nat 24 eq_refl).
    - rewrite F25. exact (EX 10%nat 25 eq_refl).
    - rewrite F26, (EE 26%nat 26%bv eq_refl). exact E26.
    - rewrite F27, (EE 27%nat 27%bv eq_refl). exact E27. }
  eapply (RET W2 _ _ _ _ _ HS2 eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'. unfold apost_base.
  lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ =>
    exists ly2, (stack_free_state 0 fpos S2), r, m, d end.
  split; [rewrite F1, X1; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
  split; [apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ|].
  split; [exact HPF|].
  apply HQ.
  + rewrite F10. exact (EE 10%nat 10%bv eq_refl).
  + intros a Ha HnF HnS HnFL.
    apply (sc_t_frame_kept E _ (w_H W2) mem2 (ms_mem msF) a HFrF Ha).
    intros (r & Hin & Hr).
    lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
    cbn [In] in Hin.
    repeat (destruct Hin as [<- | Hin];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U32, ?U23, ?U24, ?U8 in Hr; lia | ]).
    destruct Hin.
Qed.
End e.
End f.
End r.

(* ---- part t ---- *)
Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the statement's Section hypotheses (sup_call_c.v:87-93) and the walk hypotheses, with cgif's names,
   that this part uses, word for word as sup_call.v states them *)
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis IMG : CmdRecBase.cmd_img_facts SEGS B.

(* the live-block, program-static and shape helpers are CmdRecAns.v's rca_blk / rca_same_start / rca_prog /
   rca_shape_arg *)
Lemma sc_stage_t : SC_L_stmt B MT.
Proof.
unfold SC_L_stmt.
intros ly S W regs mem md ch id pl line R O fpos F FL lyc Sc Wc regsc memc mdc.
cbv zeta. intros HFRM HPRE HAT.
remember (snd (sup_call_m R id line)) as t eqn:Ht0 in *.
assert (Et : snd (rec_answer (rec_record R REC_CALL (sc_args id line)) (REC_CALL, sc_args id line)
  REC_MOD_HOST_SHAPE true) = t) by (rewrite Ht0; reflexivity).
unfold sc_pre in HPRE. unfold sc_at_l in HAT.
destruct HPRE as (HPRE0 & HFR7 & HROD0 & HRO0 & H10e & Hid & H11e & Hpl & HLINE & HREP0 & HEV & HLV & HMOK).
destruct HAT as (HL & H22 & H1 & H10 & H11 & H12 & O2 & HREP2 & HBLK & HBB & HMLE).
unfold sc_blk in HBLK. destruct HBLK as (HBLK1 & HBLK2 & HBLK3).
pose proof HPRE0 as (HAR0 & Hra0 & Hra40 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HL as (HJ & EF & EFL & HRG & HFRc & HFLc).
pose proof HRG as (Esp & E8 & E18 & E24 & E19 & E20 & E21 & E23 & E25 & E3 & E4 & E26 & E27).
pose proof HJ as (HARc & Hlyc & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk0 & F1 & F2 & F3 & F4 & F5 & Hpresc & Hstkc & F6 & HQTc).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof (pa_base_lo (PL := PL_cmd) (PI := PI)) as HBLO.
assert (FFS : SUP_CALL_STK = ltac:(let v := eval vm_compute in SUP_CALL_STK in exact v)) by reflexivity.
assert (FAS : ANSWER_STK = ltac:(let v := eval vm_compute in ANSWER_STK in exact v)) by reflexivity.
assert (Hfinc : In (0, fpos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
(* a0: the slot record() returned, in answer's form (RecBridge.v's rec_slot_entry) *)
assert (Hcb : 0 <= rec_slot R < 2 ^ 64).
{ unfold rec_slot. destruct (Nat.ltb_spec (length (r_calls R)) 16) as [Hl | Hl];
  unfold A_G_REC, A_REC_SPILL, OFF_CALLS, CALL_SIZE; lia. }
pose proof (rec_slot_entry R REC_CALL (sc_args id line)) as HSLOT.
(* the recorder's blocks are live blocks *)
assert (HO : forall pn, In pn O -> In pn (ablocks B ly S)) by (intros pn Hp; exact (sc_t_rep_live B _ _ _ _ _ pn HREP0 Hp)).
assert (HO2 : forall pn, In pn O2 -> In pn (ablocks B lyc Sc)) by (intros pn Hp; exact (sc_t_rep_live B _ _ _ _ _ pn HREP2 Hp)).
(* the realigned sp: 96 or 112 bytes below the entry sp *)
pose proof (sc_sp1_bounds (spZ regs)) as (Hsp1 & Hsp1al).
assert (Hsp1lo : spZ regs - 112 <= sc_sp1 (spZ regs)).
{ unfold sc_sp1. clear - Hal16. Z.div_mod_to_equations. lia. }
assert (Halo : (sc_sp1 (spZ regs) - spZ regs) mod 16 = 0).
{ clear - Hal16 Hsp1al. Z.div_mod_to_equations. lia. }
(* the read-only bytes at answer's entry *)
assert (HRODc : arodata_okP SEGS RLO RHI B (rdW Wc memc))
  by exact (sc_aro B HB LAWS IMG ly S W mem md O SUP_CALL_STK (spZ regs) [(0, fpos)] lyc Sc Wc memc mdc _ HAR0 HO HJ HROD0).
assert (HROKc : cmd_ro_ok (rdW Wc memc))
  by exact (CmdRecRo.cmd_ro_ok_of_aro SEGS B LAWS HB IMG lyc Sc Wc memc mdc HARc HRODc).
(* the frame chain at answer's entry: afn_pre's chain pushed at the frame pointer s0 = sp0 *)
destruct (sc_chain B LAWS ly S W regs mem md ch O fpos F FL lyc Sc Wc regsc memc mdc _ HPRE0 HO HL) as (ch1 & Hch1).
assert (Hch1' : achain lyc (rdW Wc memc) (spZ regs + (sc_sp1 (spZ regs) - spZ regs)) (s0Z regsc) ch1)
  by (replace (spZ regs + (sc_sp1 (spZ regs) - spZ regs)) with (sc_sp1 (spZ regs)) by lia; exact Hch1).
(* the old answer: 0 or the start of one of the recorder's blocks *)
pose proof HREP2 as (Q2 & HQ2 & HQ2O).
destruct (rca_answer_cell _ _ _ _ HQ2) as (old & Hold & Hold').
assert (OLD : old = 0 \/ exists pn0, In pn0 O2 /\ old = fst pn0).
{ destruct Hold' as [(_ & E0) | (pn0 & Ea & E0)]; [left; exact E0|]. right. exists pn0. split; [|exact E0].
  apply HQ2O. apply rca_in_answer. rewrite Ea. cbn [oblk]. left. reflexivity. }
assert (Hob : 0 <= old < 2 ^ 64).
{ destruct OLD as [-> | ([p a] & Hp & ->)]; [lia|]. cbn [fst].
  destruct (rca_blk B LAWS lyc Sc Wc memc mdc p a HARc (HO2 _ Hp)) as (B1 & B2 & _ & B4). lia. }
assert (Hsh : 0 <= 0x21d20 < 2 ^ 64) by lia.
pose proof (rca_shape_arg B HB lyc Sc Wc memc mdc O2 HARc HROKc (CmdRecRo.cmd_ro_in_img SEGS B LAWS HB IMG)) as HARG.
(* the premises of answer's contract at its entry *)
assert (P1 : Z.of_nat (length (frames Sc)) <= 8) by (rewrite Hfrs; cbn [app length]; lia).
assert (P7 : true = negb (bv_unsigned (getr regsc 12) =? 0)) by (rewrite H12; vm_compute; reflexivity).
assert (P10 : r_refuse (rec_record R REC_CALL (sc_args id line)) = 0 ->
  astr_argA B lyc Sc (rdW Wc memc) (in_roP SEGS RLO RHI) O2 0x21d20 (Some REC_MOD_HOST_SHAPE) /\ fits REC_MOD_HOST_SHAPE)
  by (intros _; exact HARG).
assert (P11 : r_refuse (rec_record R REC_CALL (sc_args id line)) = 0 -> true = true ->
  (exists k, nth_error (r_calls (rec_record R REC_CALL (sc_args id line))) k = Some (REC_CALL, sc_args id line) /\
    rec_slot R = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat k) \/
  (rec_slot R = A_REC_SPILL /\ (REC_CALL, sc_args id line) = r_spill (rec_record R REC_CALL (sc_args id line))))
  by (intros _ _; exact HSLOT).
assert (P12 : st_nev Sc + EV_ANSWER <= EV_MAX) by (unfold EV_SUP_CALL in HEV; lia).
assert (P13 : blocks_bytes Sc + LIVE_ANSWER t <= LIVE_MAX) by (unfold LIVE_SUP_CALL in HLV; lia).
assert (HXA : 0 <= XM_ANSWER MT t).
{ unfold XM_ANSWER, XM_HAND_BACK, XM_XMALLOC, LIVE_XMALLOC. pose proof (mo_free_nonneg MT MTL).
  pose proof (mo_malloc_nonneg MT MTL (Z.max (Z.of_nat (length t) + 1) 1) ltac:(lia)). lia. }
assert (P14 : mo_ok MT Sc (XM_ANSWER MT t)).
{ apply (mok_station MT S Sc (XM_SUP_CALL MT R id line t)
    (XM_RECORD MT R + XM_ARG_S MT (Some (dec id)) + XM_ARG_LINE MT line) (XM_ANSWER MT t) MTL HMOK HMLE HXA).
  unfold XM_SUP_CALL. lia. }
(* answer's contract at its entry, with its footprint FPa and its post-condition Qa *)
pose proof (TANSWER fx lyc Sc Wc regsc memc mdc ch1 (rec_slot R) 0x21d20 old (REC_CALL, sc_args id line)
  REC_MOD_HOST_SHAPE true (rec_record R REC_CALL (sc_args id line)) O2) as HANS.
cbv zeta in HANS. rewrite Et in HANS.
lazymatch type of HANS with
| context [apost_baseF _ _ _ ?FPx _ _ _ _ _ _ _ ?QX] =>
  remember FPx as FPa eqn:EFPa in HANS; remember QX as Qa eqn:EQa in HANS
end.
(* answer's footprint: g_rec.answer and g_rec.state (program statics of the image), and the old answer's block
   (one of O2) *)
assert (HFPc : forall a, inFP FPa a ->
  (Exists (in_zr a) (as_prog_static B) /\ in_img SEGS a) \/ (exists p n, In (p, n) O2 /\ p <= a < p + req_size n)).
{ intros a Ha. rewrite EFPa in Ha. rewrite !inFP_cons in Ha.
  destruct Ha as [Ha | [Ha | Ha]].
  - left. apply (rca_prog B HB IMG). exists (A_G_REC, A_G_REC + 960). split; [unfold cmd_PG; apply in_eq|].
    cbn [fst snd] in *. unfold OFF_ANSWER in Ha. lia.
  - left. apply (rca_prog B HB IMG). exists (A_G_REC, A_G_REC + 960). split; [unfold cmd_PG; apply in_eq|].
    cbn [fst snd] in *. unfold OFF_STATE in Ha. lia.
  - right. destruct (inFP_ablocks_fp_inv _ a Ha) as (p & n & Hin & Hr). exists p, n.
    split; [exact (rca_filter_in _ _ _ Hin) | exact Hr]. }
assert (HFPlow : forall a, inFP FPa a -> a < alloc_ceiling).
{ intros a Ha. destruct (HFPc a Ha) as [(_ & Himg) | (p & n & Hin & Hr)].
  - pose proof (pa_segs_low a Himg). lia.
  - destruct (rca_blk B LAWS lyc Sc Wc memc mdc p n HARc (HO2 _ Hin)) as (_ & B2 & _). lia. }
assert (HFPnf : forall a, F <= a < F + 64 -> ~ inFP FPa a).
{ intros a Ha Hf. destruct (HFPc a Hf) as [(_ & Himg) | (p & n & Hin & Hr)].
  - apply (frm_img SEGS B LAWS lyc Sc Wc memc mdc 0 fpos a HARc Hfinc); [|exact Himg].
    rewrite EF. change (fs_frame_bytes 0) with 64. lia.
  - pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc p n 0 fpos HARc (HO2 _ Hin) Hfinc) as Hd.
    rewrite EF in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 0) with 64 in Hd. lia. }
(* every byte of answer's footprint is in sup_call's, a byte of a live block or a program static, or of a block
   new since the entry (cl_callS_pgF's footprint premise) *)
assert (HF : forall a, inFP FPa a ->
  (inFP (SC_FP O) a /\ ((exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
    (Exists (in_zr a) (as_prog_static B) /\ in_img SEGS a))) \/
  in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a).
{ intros a Ha. pose proof (HFPc a Ha) as Hc. rewrite EFPa in Ha. rewrite !inFP_cons in Ha.
  destruct Ha as [Ha | [Ha | Ha]].
  - left. split; [|destruct Hc as [Hc | (p & n & Hin & Hr)]; [right; exact Hc|]].
    + unfold SC_FP. rewrite !inFP_cons. right; left. cbn [fst snd] in *. unfold OFF_CALLS, OFF_ANSWER in *. lia.
    + left. exists p, n. split; [exact (HO2 _ Hin) | exact Hr].
  - left. split; [|destruct Hc as [Hc | (p & n & Hin & Hr)]; [right; exact Hc|]].
    + unfold SC_FP. rewrite !inFP_cons. right; right; left. exact Ha.
    + left. exists p, n. split; [exact (HO2 _ Hin) | exact Hr].
  - destruct (inFP_ablocks_fp_inv _ a Ha) as (p & n & Hin & Hr). apply rca_filter_in in Hin.
    destruct (HBLK1 _ Hin) as [HinO | HnB].
    + left. split.
      * unfold SC_FP. rewrite !inFP_cons. right; right; right; right.
        replace a with (p + (a - p)) by lia. apply (inFP_ablocks_fp O p n (a - p)); [exact HinO | lia].
      * left. exists p, n. split; [exact (HO2 _ Hin) | exact Hr].
    + right. exists p, n. split; [exact (HO2 _ Hin)|]. split; [exact HnB | exact Hr]. }
(* the call's premises in cl_callS_pgF's form *)
assert (Hspo : spZ regsc = spZ regs + (sc_sp1 (spZ regs) - spZ regs)) by (rewrite Esp; lia).
assert (Hnego : sc_sp1 (spZ regs) - spZ regs <= 0) by lia.
assert (WA0 : 0 <= ANSWER_STK) by (rewrite FAS; lia).
assert (Hbudo : ANSWER_STK - (sc_sp1 (spZ regs) - spZ regs) <= SUP_CALL_STK) by (rewrite FAS, FFS; lia).
assert (Hgpc : getr regsc 3 = w64 (as_gp B)) by (rewrite E3; exact Hgp).
assert (Htpc : getr regsc 4 = w64 (as_tp B)) by (rewrite E4; exact Htp).
assert (Hrawc : YK0s.ret_ok (getr regsc 1)).
{ rewrite H1. unfold w64. rewrite <- Z.add_assoc. apply ret_ok_codeptr_v; [|vm_compute; reflexivity].
  unfold AF_sup_call, SC_PC_R. lia. }
assert (Hra4c : 4096 <= bv_unsigned (getr regsc 1)).
{ rewrite H1. unfold w64. rewrite unsigned_lit_small; unfold AF_sup_call, SC_PC_R; lia. }
unfold sc_post.
eapply (srr_after_callF_base (fx := fx) SEGS).
{ refine (cl_callS_pgF B LAWS Wc regsc memc (w64 (BASE + AF_answer)) SUP_CALL_STK (spZ regs) (SC_FP O)
    ly S W mem md [(0, fpos)] lyc Sc mdc (EV_RECORD R + EV_ARG_S + EV_ARG_LINE) ANSWER_STK FPa EV_ANSWER
    (sc_sp1 (spZ regs) - spZ regs) (getr regsc 1) ch1 Qa
    HJ Hspo Halo Hnego WA0 Hbudo Hgpc Htpc eq_refl Hrawc Hra4c Hch1'
    (fun HP => HANS HP HFRM P1 HRODc HROKc H10 Hcb H11 Hsh P7 HREP2 Hold Hob P10 P11 P12 P13 P14) HF). }
(* answer returned at 0x8b090, at its FP state fx1 *)
intros fx1 ly2 S2 W2 regs2 mem2 md2 Hle Hfx (HJo & HJi & HP2 & HK).
rewrite EQa in HK. cbv beta in HK.
destruct HK as (p1 & p2 & O' & G10 & G4096 & Gne & Gfr & GBL & GREP & GO & GSTR & GBB & GMLE).
pose proof HJi as (HAR2 & Hly2 & _ & _ & _ & Hfrs2 & _ & _ & F1i & _ & _ & F4i & _ & _ & _ & _ & _).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly2 HARc Hly2) as (_ & Efa2 & _).
assert (EF2 : frame_addr ly2 0 fpos = F) by (rewrite Efa2; exact EF).
assert (EFL2 : flag_addr ly2 0 fpos = FL)
  by (pose proof (Efa2 0 fpos) as Ee; rewrite <- EFL; unfold frame_addr, flag_addr in *; lia).
assert (Hfin2 : In (0, fpos) (frames S2)) by (rewrite Hfrs2; exact Hfinc).
(* the callee-saved registers after answer are the ones at its entry *)
assert (R2 : getr regs2 2 = getr regsc 2) by exact (HP2 2 ltac:(unfold acallee_saved; lia)).
assert (R3 : getr regs2 3 = getr regsc 3) by exact (HP2 3 ltac:(unfold acallee_saved; lia)).
assert (R4 : getr regs2 4 = getr regsc 4) by exact (HP2 4 ltac:(unfold acallee_saved; lia)).
assert (R8 : getr regs2 8 = getr regsc 8) by exact (HP2 8 ltac:(unfold acallee_saved; lia)).
assert (R18 : getr regs2 18 = getr regsc 18) by exact (HP2 18 ltac:(unfold acallee_saved; lia)).
assert (R19 : getr regs2 19 = getr regsc 19) by exact (HP2 19 ltac:(unfold acallee_saved; lia)).
assert (R20 : getr regs2 20 = getr regsc 20) by exact (HP2 20 ltac:(unfold acallee_saved; lia)).
assert (R21 : getr regs2 21 = getr regsc 21) by exact (HP2 21 ltac:(unfold acallee_saved; lia)).
assert (R23 : getr regs2 23 = getr regsc 23) by exact (HP2 23 ltac:(unfold acallee_saved; lia)).
assert (R24 : getr regs2 24 = getr regsc 24) by exact (HP2 24 ltac:(unfold acallee_saved; lia)).
assert (R25 : getr regs2 25 = getr regsc 25) by exact (HP2 25 ltac:(unfold acallee_saved; lia)).
assert (R26 : getr regs2 26 = getr regsc 26) by exact (HP2 26 ltac:(unfold acallee_saved; lia)).
assert (R27 : getr regs2 27 = getr regsc 27) by exact (HP2 27 ltac:(unfold acallee_saved; lia)).
(* the frame after answer (sc_live at k + EV_ANSWER): the saves and the flag-byte word are above answer's window
   and outside its footprint, which lies below alloc_ceiling and off the frame *)
assert (HL2 : sc_live B ly S W regs mem md O fpos F FL ly2 S2 W2 regs2 mem2 md2 (EV_SUP_CALL R)).
{ unfold sc_live. split; [unfold EV_SUP_CALL; exact HJo|].
  split; [exact EF2|]. split; [exact EFL2|].
  split.
  { unfold sc_regs. split; [unfold spZ at 1; rewrite R2; exact Esp|].
    split; [rewrite R8; exact E8|]. split; [rewrite R18; exact E18|]. split; [rewrite R24; exact E24|].
    split; [rewrite R19; exact E19|]. split; [rewrite R20; exact E20|]. split; [rewrite R21; exact E21|].
    split; [rewrite R23; exact E23|]. split; [rewrite R25; exact E25|]. split; [rewrite R3; exact E3|].
    split; [rewrite R4; exact E4|]. split; [rewrite R26; exact E26 | rewrite R27; exact E27]. }
  split.
  { apply (sc_frame_ext (rdW Wc memc) (rdW W2 mem2) (spZ regs) regs); [|exact HFRc].
    intros a Ha. rewrite FFS in Hslo. apply F1i; [lia | lia |].
    intros Hf. pose proof (HFPlow a Hf). lia. }
  apply (sc_rdword_ext (rdW Wc memc)); [|exact HFLc].
  intros x Hx. apply (F4i 0 fpos x Hfinc).
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF. change (fs_frame_bytes 0) with 64. lia.
  - apply HFPnf. lia. }
(* sup_call's post predicate at the released state, from answer's post and sc_blk *)
assert (DEC : forall x y : Z * Z, {x = y} + {x <> y}) by (intros x y; decide equality; apply Z.eq_dec).
assert (HNOLD : forall pn, In pn (ablocks B ly S) -> ~ In pn O -> fst pn <> old).
{ intros [pp pk] Hb Hno Hfst. pose proof (HBLK3 _ Hb Hno) as HbT. cbn [fst] in Hfst.
  destruct OLD as [Eo | ([ap ak] & Hpa0 & Hpa0f)].
  - destruct (rca_blk B LAWS lyc Sc Wc memc mdc pp pk HARc HbT) as (B1 & _). lia.
  - cbn [fst] in Hpa0f. assert (Ep : ap = pp) by lia. rewrite Ep in Hpa0.
    pose proof (HO2 _ Hpa0) as HaB.
    pose proof (rca_same_start B LAWS lyc Sc Wc memc mdc pp pk ak HARc HbT HaB) as Ek. rewrite <- Ek in Hpa0.
    destruct (HBLK1 _ Hpa0) as [HO1 | HN1]; [exact (Hno HO1) | exact (HN1 Hb)]. }
assert (HQF : forall (regs' : bvmap 5 word) mem' md', getr regs' 10 = getr regs2 10 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (F <= a < F + 64) -> ~ (SB + F / 8 <= a < SB + F / 8 + 8) -> a <> FL ->
    rdW W2 mem' a = rdW W2 mem2 a) ->
  sc_Q B MT ly S W mem id line R O t ly2 (stack_free_state 0 fpos S2) W2 regs' mem' md').
{ intros regs' mem' md' H10' HKP.
  assert (EabF : ablocks B ly2 (stack_free_state 0 fpos S2) = ablocks B ly2 S2)
    by (unfold ablocks; rewrite blocks_stack_free_state; reflexivity).
  assert (HKB : forall a, ((exists p n, In (p, n) (ablocks B ly2 S2) /\ p <= a < p + req_size n) \/ in_img SEGS a) ->
    rdW W2 mem' a = rdW W2 mem2 a).
  { intros a Ha. destruct (sc_t_apart B LAWS FFL ly2 S2 W2 mem2 md2 fpos F FL a HAR2 Hfin2 EF2 EFL2 Ha) as (A1 & A2 & A3 & A4).
    exact (HKP a A1 A2 A3 A4). }
  unfold sc_Q. exists (fst (sup_call_m R id line)), O', p2.
  split; [rewrite Ht0; apply surjective_pairing|].
  cbv zeta. rewrite EabF.
  split; [rewrite H10'; exact G10|].
  split; [exact G4096|].
  split.
  { apply (rec_repA_kept B ly2 S2 (rdW W2 mem2) ly2 (stack_free_state 0 fpos S2) (rdW W2 mem') _ O' GREP).
    - intros pn Hpn. rewrite EabF. exact (sc_t_rep_live B _ _ _ _ _ pn GREP Hpn).
    - intros a Ha. apply HKB. destruct Ha as [Ha | [Ha | Ha]].
      + right. apply (CmdRecBase.cif_prog_img _ _ IMG). exists (A_G_REC, A_G_REC + 960).
        split; [unfold cmd_PG; apply in_eq | cbn [fst snd]; unfold REC_SIZE in Ha; lia].
      + right. apply (CmdRecBase.cif_prog_img _ _ IMG). exists (A_REC_SPILL, A_REC_SPILL + 56).
        split; [unfold cmd_PG; apply in_cons, in_eq | cbn [fst snd]; unfold SC_SIZE in Ha; lia].
      + left. destruct (inFP_ablocks_fp_inv O' a Ha) as (p & n & Hin & Hr). exists p, n.
        split; [exact (sc_t_rep_live B _ _ _ _ _ _ GREP Hin) | exact Hr]. }
  split.
  { intros pn Hpn. apply GO in Hpn as [[HpnO2 _] | ->]; [exact (HBLK1 pn HpnO2)|].
    destruct (in_dec DEC (p1, Z.of_nat (length t) + 1) O) as [Hin | Hnin]; [left; exact Hin|].
    right. intros Hb. exact (proj1 (Gfr _ (HBLK3 _ Hb Hnin) (HNOLD _ Hb Hnin)) eq_refl). }
  split.
  { intros pn Hpn. apply GBL in Hpn as [[Hb Hne] | [-> | ->]].
    - destruct (HBLK2 pn Hb) as [X | HpnO2]; [left; exact X|].
      right. left. apply GO. left. split; [exact HpnO2 | exact Hne].
    - right. left. apply GO. right. reflexivity.
    - right. right. reflexivity. }
  split.
  { intros pn Hb Hno. apply GBL. left. split; [exact (HBLK3 _ Hb Hno) | exact (HNOLD _ Hb Hno)]. }
  split; [apply GBL; right; right; reflexivity|].
  split; [intros pn Hb Hno; exact (proj2 (Gfr _ (HBLK3 _ Hb Hno) (HNOLD _ Hb Hno)))|].
  split.
  { intros Hin. apply in_map_iff in Hin as ([pp pk] & Hf & Hpn). cbn [fst] in Hf. subst pp.
    apply GO in Hpn as [[HpnO2 Hne] | Heq].
    - pose proof (HO2 _ HpnO2) as HbT.
      assert (Hb2 : In (p2, pk) (ablocks B ly2 S2)) by (apply GBL; left; split; [exact HbT | exact Hne]).
      assert (Hq2 : In (p2, Z.of_nat (length t) + 1) (ablocks B ly2 S2)) by (apply GBL; right; right; reflexivity).
      pose proof (rca_same_start B LAWS ly2 S2 W2 mem2 md2 p2 pk _ HAR2 Hb2 Hq2) as Ek. subst pk.
      exact (proj2 (Gfr _ HbT Hne) eq_refl).
    - injection Heq as E1 _. exact (Gne (eq_sym E1)). }
  split.
  { apply (astr_atR_kept_r (rdW W2 mem2)); [|exact GSTR].
    intros x Hx. apply HKB. left. exists p2, (Z.of_nat (length t) + 1).
    split; [apply GBL; right; right; reflexivity|].
    split; [lia|]. unfold req_size. destruct (Z.eqb_spec (Z.of_nat (length t) + 1) 0); lia. }
  split; [change (blocks_bytes (stack_free_state 0 fpos S2)) with (blocks_bytes S2); unfold LIVE_SUP_CALL; lia|].
  unfold stack_free_state. apply (mo_le_set_fs_r MT MTFL). unfold XM_SUP_CALL.
  exact (mle_station MT S Sc S2 _ _ MTL HMLE GMLE). }
(* 0x8b090 .. 0x8b124: the release segment at fx1 *)
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ ?rw _ _) _) _ =>
  replace rw with (Z_to_bv 64 (BASE + (AF_sup_call + SC_PC_R))) by (rewrite H1; unfold w64; f_equal; lia) end.
exact (sc_t_rel (fx := fx1) B LAWS ML ASF FFL ly S W regs mem md O fpos F FL ly2 S2 W2 regs2 mem2 md2
  (EV_SUP_CALL R) (sc_Q B MT ly S W mem id line R O t) Hra0 HL2 HQF).
Qed.
End e.
End f.
End w.
