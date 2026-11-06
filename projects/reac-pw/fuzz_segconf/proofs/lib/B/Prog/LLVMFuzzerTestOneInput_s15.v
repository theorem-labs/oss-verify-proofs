(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of check_round_trip on the ASan build of plugin-hostd/fuzz_command
   (0x87fd8, 286 instructions), proving tcheck_round_trip_spec (check_round_trip_c.v), in the shape of cgif_file_fuzzer's
   walks (lib/A/AChc.v, ACh1..ACh8.v, AChf.v): one statement per point between two calls (ST_B .. ST_EPI below), each
   segment proved by a run of the symbolic executor over the position-abstract listing (CmdPaLib.v) from a fresh seed,
   the inline checks removed by the shadow tokens (PaShadow.v), and the call at its end composed into the journal:
   the class-5 side-stack frame by aj_stack_malloc_atS (PaCall.v) and, from check_round_trip_k.v, aj_set_shadow_atS
   (__asan_set_shadow_f8/_00) and aj_stack_free_cls_atS (__asan_stack_free_5); the strdup wrapper by crts4_strdup_sub,
   the free wrapper by afree04_sub (PaCall.v), the strcmp wrapper by aj_art_at (PaArt.v); the program callees
   rec_calls_copy, joined, send_message and rec_calls_free by cl_callS_wide and rec_calls_equal by cl_callS_na
   (PaNoChain.v), each with its contract as a Section hypothesis. The skip path (no word, or the daemon did not act)
   joins the epilogue at 0x88314; the abort edges (0x8838c) are excluded by rt_okA and the callees' posts.
   Re-fit to statement passes 4, 4b and 5: the callee and runtime hypotheses hold at every
   FP state (forall fx0) and the segments use them at the ambient fx. send_message reaches the printf wrappers, so the
   points before its return (ST_B .. ST_F) prove the FP-existential post crt_postF (apost_baseF); crt_s6 calls
   send_message by PaFx.v's cl_callS_wideF with the rounding-mode premise HFRM and goes on at the FP state fx1 it
   returns (srr_after_callF_base). The points after it (ST_G .. ST_EPI) prove apost_base at the ambient FP state, so
   once the sections close they hold at fx1 (crt_G, used so by tcheck_round_trip_spec_holds). The skip path lifts
   ST_EPI's post by apost_baseF_of_base (crts3_skip). Pass 5 removed astack_pres: s0 is the frame pointer sp0 at every
   call, so each call's frame chain is the prologue's frame record (ra at sp0 - 8, the entry s0 at sp0 - 16, from
   crt_frame) on afn_pre's chain (achain_push, crt_chain), and chain_pre for the runtime allocation entries is
   achain_chain_pre of it. joined's new premises at its call: len's 8 bytes present (the journal's window), and
   (pass 5b) the stack from len - 16 present, from the statement's astack_pres kept by astack_pres_journal. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_round_trip.v, with its module paths and module names changed; 5000 of its 5273 lines of code are new or changed and 4780 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan+UBSan image B (fuzz_segconf.asan-ubsan, pin sha256 c3796c0b38f3): segment S05 of the
   walk of the test harness's entry function LLVMFuzzerTestOneInput (0x84dc0): from the cut
   K85210 (0x85210) to K85338 (0x85338, the last turn) or K85530 (0x85530), the statement lt_seg_S05_stmt of
   LLVMFuzzerTestOneInput_defs.v, proved exactly as `lt_seg_S05` at the end of this file.

   proves function LLVMFuzzerTestOneInput (reuse search, rule 24: released units, the earlier proof delivery and working
   heads; the result is recorded with the commissioning brief; none: written new)

   THE FORM: plugin-hostd/fuzz_command's image-B harness walk (origin/ossv/recipes 3abc3740de97,
   lib/B/Prog/LLVMFuzzerTestOneInput_s*.v) in this stream's segconf vocabulary (image B's closed S00, S01 / S02 and
   S21 / ret walks in this walk's integration; image A's S00, S01 / S02 and S21 / ret walks and its S05 kit). The
   walk of S05 is cut at the four inner points the kit LLVMFuzzerTestOneInput_s15k.v states, into five pieces, each
   one section below:

     L1 s5_head   0x85210 K85210 f -> 0x8526c S5_LB f    the abort edge (t >= 4096), checked_memcpy, the UBSan trap
                                                          0x85230 (t + n + 1 <= alloc_ceiling), check 7, the NUL,
                                                          the label's five shadow stores (the plain runner)
     L2 s5_label  0x8526c S5_LB f -> 0x852c8 S5_OTH f     the three label arms (snprintf into the frame's label[40],
                               or 0x85324 S5_LST f        checked_memset of longl, none), the join, the last-turn test
     L3 s5_last   0x85324 S5_LST f -> 0x85338 K85338 f    144(s1) := P1 + NP, m_file(m, text, NULL)
     L4 s5_calls  0x852c8 S5_OTH f -> 0x852e4 S5_CK f     m_file(m, text, label), reac_segconf_parse_file(c, text,
                                                          label)
     L5 s5_tail   0x852e4 S5_CK f -> 0x85530 K85530 f     the UBSan trap 0x852e8 (s5 = M & 3 = 0), check 8 on m->n,
                                                          the latch of `returned` in 176(s1), s4 := N1 - NP,
                                                          free(text)

   The five pieces share one Section header word for word (the same variables and hypotheses in the same
   order), and every piece lemma is `Proof using All`, so each closed lemma takes one fixed argument list.
   snprintf, m_file and reac_segconf_parse_file return at an FP state of their own, so S5_OTH, S5_LST and S5_CK
   are taken at every FP state (the kit's S5A_OTH, S5A_LST, S5A_CK); `lt_seg_S05` composes the five closed
   lemmas, instantiating L3, L4 and L5 at every FP state.

   The Section hypotheses (discharged by the close at image B's instance): the meter laws MTL / MTFL, the
   listing's runtime cells and wrappers PALib / PALibF, the model laws ML, prog_rw, the listing's object and call
   targets seg_val_objs / seg_sig_prog, image B's per-image record seg_img_facts (lib/B/Prog/SegRecBase.v), the
   allocator record's symbols SegBSyms (lib/B/YF0m.v; with AR it gives the stack-protector cells at every state,
   SegRecCells.seg_rec_cells), the three facts about longl HPGS / HPG_RO / HPG_PTR, the runtime rows
   __asan_memcpy / __asan_memset
   (aintrin_realizes), snprintf row 4 (RtPFSeg.seg_asnprintf_realizes) with its five HSNP_ bounds, free
   (afree04_rule), and the two program callees' contracts (image B's copies lib/B/Prog/m_file_c.v,
   reac_segconf_parse_file_c.v). AR's laws are YG0q.AR_laws_ok, a theorem. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI08 YI09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq YG0p YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtPFPf RtPFShared RtPFSx RtPFCmd RtPFSeg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaCall PaDenot PaSB
PaArt PaFx PaLibG SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaLibF.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase SegObj.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegRo SegRecBase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YF0m.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegRecCells.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c reac_segconf_parse_file_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import LLVMFuzzerTestOneInput_c SegInstB
  LLVMFuzzerTestOneInput_inst LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_s15k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0d_tail.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YI67.

(* ============================================== piece L1 (a) ============================================== *)
(* reac-pw/fuzz_segconf, ASan+UBSan image B (fuzz_segconf.asan-ubsan, pin sha256 c3796c0b38f3): piece L1 of the walk
   of segment S05 of the test harness's entry function LLVMFuzzerTestOneInput (0x84dc0): `s5_head`, from the cut
   K85210 (0x85210) to the kit's inner cut S5_LB (0x8526c) of LLVMFuzzerTestOneInput_s15k.v.

   THE FORM: plugin-hostd/fuzz_command's image-B harness walk lib/B/Prog/LLVMFuzzerTestOneInput_s42.v
   (origin/ossv/recipes 3abc3740de97: a token run to the copy's call, the call through aj_intrin_atS, a fresh seed
   after it with the text's last byte as an atom and its shadow entry, a token run through the instrumented check and
   the NUL store), and image A's S07 / S08 walk (image A's S07 / S08 commit 6b130104f652: the label's five shadow
   stores by the plain runner through SH(FR)). The code (dis/LLVMFuzzerTestOneInput.fuzz_segconf.asan-ubsan.s
   lines 278-300, SegList.v slots 276-299):
   - 0x85210 .. 0x85218, token run A: `beqz a0` (the abort edge) decided by t >= 4096 (lt_hblk), s7 := t; it stops at
     `beqz s4` (0x85218), split on n = 0;
   - n <> 0: a0 = t, a1 = P1, a2 = n and the jal of checked_memcpy (0x85228), by aj_intrin_atS with AMEMCPY;
   - 0x8522c .. 0x8524c, token run B from a fresh seed: `not a0,s7; bltu a0,s4` (the UBSan trap 0x85230: t + n would
     wrap) split, its trap side refuted by t + n + 1 <= alloc_ceiling (al_blocks); a0 := t + n (the alias of atom 32),
     check 7 (0x85244, slow block 0x85558) a token with no obligation (the shadow entry of t + n), the NUL store;
   - 0x85250 .. 0x85268, plain run C from a fresh seed: a1 := SH(FR) from 184(s1), the label's five shadow bytes
     SH(FR) + 12 .. 16 := 0 (LFO0 -> LFO_L), a0 := lb << 56; then the kit's S5_LB at 0x8526c. *)
(* ============================ the symbolic states, and the helpers no Section needs ============================ *)
(* the shadow base the instrumented check adds (the frame slot 200(s1): a literal chunk of the seed) and the band *)
Definition s5a_x : sv := SLit SHADOW_OFF.
Definition s5a_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* A, at 0x85210: every register its own atom, no region, t (atom 10, a0) at 4096 or above *)
Definition s5a_ssA : sstate := mkSS LO_K85210 sr_atoms [] None (mkFacts [(10%nat, mkAF 4096 (2 ^ 47 - 1) 0)] [] []).
(* B, at 0x8522c: atom 32 = t + n (the value `add a0,s7,s4` computes, given to the engine as the alias), the slot
   200(s1) (the shadow base), and the byte t + n, a write window without a chunk, with its shadow entry *)
Definition s5a_rs1 : YP09.region :=
  YP09.mkRegion (Some 9%nat) 200 208 0 0 [YP09.mkChunk 200 (CVal 8 (SLit SHADOW_OFF))].
Definition s5a_rtx : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 1 [].
Definition s5a_ssB : sstate := mkSS 0x46c sr_atoms [s5a_rs1; s5a_rtx] None
  (mkFacts [(32%nat, mkAF 4096 (2 ^ 47 - 1) 0)] [] [(SAlu ALU_ADD (SOff 23 0) (SOff 20 0), SOff 32 0)]).
Definition s5a_SHB : list shent := [mkSHE 32 0 1].
(* C, at 0x85250: atom 32 = SH(FR), the slot 184(s1) that holds it, and the label's five shadow bytes SH(FR) + 12 ..
   16 a write window *)
Definition s5a_rsh : YP09.region := YP09.mkRegion (Some 32%nat) 12 17 12 17 [].
Definition s5a_rsl : YP09.region := YP09.mkRegion (Some 9%nat) 184 192 0 0 [YP09.mkChunk 184 (CVal 8 (SOff 32 0))].
Definition s5a_ssC : sstate := mkSS 0x490 sr_atoms [s5a_rsh; s5a_rsl] None (mkFacts [] [] []).

Lemma s5a_word_kept : forall (rd rd' : reader) a v,
  (forall x, a <= x < a + 8 -> rd' x = rd x) -> rdword rd a = Some v -> rdword rd' a = Some v.
Proof. intros rd rd' a v HK H. rewrite (rdword_ext rd rd' a); [exact H|]. intros k Hk. apply HK. lia. Qed.
Lemma s5a_rdword_some : forall (rd : reader) a, (forall k, 0 <= k < 8 -> rd (a + k) <> None) ->
  exists v, rdword rd a = Some v.
Proof.
intros rd a H. unfold rdword.
pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
pose proof (H 1 ltac:(lia)) as H1. pose proof (H 2 ltac:(lia)) as H2. pose proof (H 3 ltac:(lia)) as H3.
pose proof (H 4 ltac:(lia)) as H4. pose proof (H 5 ltac:(lia)) as H5. pose proof (H 6 ltac:(lia)) as H6.
pose proof (H 7 ltac:(lia)) as H7.
destruct (rd a) as [b0|]; [|congruence]. destruct (rd (a + 1)) as [b1|]; [|congruence].
destruct (rd (a + 2)) as [b2|]; [|congruence]. destruct (rd (a + 3)) as [b3|]; [|congruence].
destruct (rd (a + 4)) as [b4|]; [|congruence]. destruct (rd (a + 5)) as [b5|]; [|congruence].
destruct (rd (a + 6)) as [b6|]; [|congruence]. destruct (rd (a + 7)) as [b7|]; [|congruence].
eexists; reflexivity.
Qed.
Lemma s5a_pres_reg : forall regs regs' (r : bv 5) z,
  aregs_preserved regs regs' -> acallee_saved z -> Z_to_bv 5 z = r -> getr regs' r = getr regs r.
Proof. intros regs regs' r z HP Hz <-. exact (HP z Hz). Qed.
Lemma s5a_req : forall n, 0 < n -> req_size n = n.
Proof. intros n Hn. unfold req_size. destruct (Z.eqb_spec n 0); lia. Qed.
Lemma s5a_nth_firstn : forall (l : list Z) L i d, (i < L)%nat -> nth i (firstn L l) d = nth i l d.
Proof.
induction l as [|b l IH]; intros [|L] [|i] d Hi; cbn [firstn nth]; try reflexivity; try lia. apply IH. lia.
Qed.
(* a shadow byte of a frame is not an application byte *)
Lemma s5a_sh_not_app {rc : YM05.RunCeil} : forall F k p n a, 4096 <= F -> F + 8 * k <= 2 ^ 47 -> in_app p n ->
  2147450880 + F / 8 <= a < 2147450880 + F / 8 + k -> p <= a < p + n -> False.
Proof. intros F k p n a HF Hk Hin Ha Hp. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hin. lia. Qed.
(* the frame's 36 shadow bytes: the five stores make the label usable, nothing else changes *)
Lemma s5a_fsh_same : forall i, (i < 36)%nat -> ~ (12 <= i < 17)%nat ->
  nth i (lt_fsh LFO_L) 0 = nth i (lt_fsh LFO0) 0.
Proof. intros i Hi Hn. do 36 (destruct i as [|i]; [first [reflexivity | lia] |]). lia. Qed.
Lemma s5a_fsh_L : forall i, (12 <= i < 17)%nat -> nth i (lt_fsh LFO_L) 0 = 0.
Proof. intros i Hi. do 17 (destruct i as [|i]; [first [reflexivity | lia] |]). lia. Qed.
(* facts carried from one reader to another that agrees on their bytes (image A's S07 / S08 walk's s17_*_xfer) *)
Lemma s5a_bytes_xfer : forall (rd rd' : reader) a bs,
  (forall i, 0 <= i < Z.of_nat (length bs) -> rd' (a + i) = rd (a + i)) -> sa_bytes rd a bs -> sa_bytes rd' a bs.
Proof. intros rd rd' a bs K H i Hi. rewrite K by lia. exact (H i Hi). Qed.
Lemma s5a_rconf_xfer : forall (rd rd' : reader) c rc,
  (forall i, 0 <= i < seg_spec.SEG_C_SIZE -> rd' (c + i) = rd (c + i)) -> sa_rconf rd c rc -> sa_rconf rd' c rc.
Proof.
intros rd rd' c rc K (bs & Hb & He). exists bs. split; [|exact He].
apply (s5a_bytes_xfer rd rd' c bs); [|exact Hb]. destruct He as [Hl _]. intros i Hi. apply K. lia.
Qed.
Lemma s5a_mconf_xfer : forall (rd rd' : reader) a mc,
  (forall i, 0 <= i < seg_spec.SEG_M_SIZE -> rd' (a + i) = rd (a + i)) -> sa_mconf rd a mc -> sa_mconf rd' a mc.
Proof.
intros rd rd' a mc K (bs & Hb & He). exists bs. split; [|exact He].
apply (s5a_bytes_xfer rd rd' a bs); [|exact Hb]. destruct He as [Hl _]. intros i Hi. apply K. lia.
Qed.
(* the word a register holds is the value of its term *)
Lemma s5a_denot : forall E e v, U E e = v -> sv_denot E e = Z_to_bv 64 v.
Proof. intros E e v H. unfold U in H. rewrite <- H. symmetry. apply Z_to_bv_bv_unsigned. Qed.
(* `not a0,s7` (xori a0,s7,-1 at 0x8522c) *)
Lemma s5a_not_U : forall E (q : nat) x z, ew E q = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> zcanon z = 2 ^ 64 - 1 ->
  U E (SAlu ALU_XOR (SOff q 0) (SLit z)) = 2 ^ 64 - 1 - x.
Proof.
intros E q x z Hq Hx Hz. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E q x Hq Hx), U_SLit, Hz.
rewrite lxor_allones by lia. apply zcanon_id. unfold M64. lia.
Qed.
(* `slli a0,s10,0x38` (0x85264): a0 = lb << 56 *)
Lemma s5a_sll56 : forall E (q : nat) z, ew E q = Z_to_bv 64 z ->
  sv_denot E (SAlu ALU_SLL (SOff q 0) (SLit 56)) = Z_to_bv 64 (Z.shiftl z 56).
Proof.
intros E q z Hq. rewrite <- (Z_to_bv64_canon (Z.shiftl z 56)). apply s5a_denot.
rewrite U_SAlu, U_SLit, U_SOff, Hq. cbn [zalu_raw].
change (Z.land (zcanon 56) 63) with 56. rewrite Z.add_0_r.
rewrite Z_to_bv_unsigned. unfold bv_wrap, zcanon, M64. change (bv_modulus 64) with (2 ^ 64).
rewrite !Z.shiftl_mul_pow2 by lia. rewrite !Z.mul_mod_idemp_l by lia. reflexivity.
Qed.
(* byte i of turn f's text is the input's byte at the turn's cursor P1 + i *)
Lemma s5a_txt_byte : forall pl f i, Z.of_nat f < seg_spec.seg_nfiles pl ->
  (i < length (seg_spec.seg_txt pl f))%nat ->
  nth i (seg_spec.seg_txt pl f) 0 =
    nth (length pl - length (seg_spec.seg_turn_tail pl f) + i) (map (fun b : byte => bv_unsigned b) pl) 0 /\
  (length pl - length (seg_spec.seg_turn_tail pl f) + i < length pl)%nat /\
  (length (seg_spec.seg_turn_tail pl f) <= length pl)%nat.
Proof.
intros pl f i Hf Hi.
destruct (s5_txt_firstn pl f Hf) as (Hfn & Hle1 & Hle2).
pose proof (s5_tail_sfx pl f) as Hsfx.
pose proof (s5_sfx_len _ _ Hsfx) as Hlen.
assert (Hin : length (seg_spec.seg_in pl) = length pl) by (unfold seg_spec.seg_in, seg_spec.zs; apply length_map).
rewrite Hin in Hlen.
assert (Hit : (i < length (seg_spec.seg_turn_tail pl f))%nat) by lia.
split; [|split; lia].
pose proof (f_equal (fun l => nth i l 0) Hfn) as E. cbv beta in E.
rewrite s5a_nth_firstn in E by exact Hi. rewrite E.
rewrite (s5_sfx_nth _ _ Hsfx i Hit). rewrite Hin. reflexivity.
Qed.
(* the text is no longer than the input *)
Lemma s5a_txt_len : forall pl f, Z.of_nat f < seg_spec.seg_nfiles pl ->
  (length (seg_spec.seg_txt pl f) <= length pl)%nat.
Proof.
intros pl f Hf. destruct (s5_txt_firstn pl f Hf) as (_ & Hle1 & Hle2).
pose proof (s5_sfx_len _ _ (s5_tail_sfx pl f)) as Hlen.
assert (Hin : length (seg_spec.seg_in pl) = length pl) by (unfold seg_spec.seg_in, seg_spec.zs; apply length_map).
lia.
Qed.

Section da. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section fa.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section ea.
Variable B : asyms.
Variable MT : ameter_ops.
(* the image range the snprintf row's dest_off_globals uses, and the read-only ranges it reads; the S11 walk
   (the probe snprintf) takes the same three names and the same five HSNP_ hypotheses *)
Variable snp_lo snp_hi : Z.
Variable snp_cr : list (Z * Z).
(* AR's laws are a theorem of image B's kit, not a hypothesis *)
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis PRW : prog_rw SEGS B.
Hypothesis VOBJS : seg_val_objs.
Hypothesis SIGP : seg_sig_prog.
(* image B's per-image record (lib/B/Prog/SegRecBase.v, the image-B listing owner's commit c4abdaee306f, merged into
   this walk's integration commit da997fa1859d): the image facts lt_img needs at a reader after a call, each a field.
   It SUPERSEDES the three hypotheses IMG_RELRO / IMG_GOTW / IMG_GUARD an earlier version of this brief had.
   Never weaken lt_img instead. *)
Hypothesis IMGF : seg_img_facts SEGS B.
(* the allocator record's symbols at image B's values (lib/B/YF0m.v): with AR it gives the stack-protector
   cells at every state (SegRecCells.seg_rec_cells), since the runtime owns the .got word gotwA *)
Hypothesis HBS : YF0m.SegBSyms B.
(* longl's bytes are the program's own writable static, in the image and outside RELRO (the memset arm writes
   them), and no model-table pointer reaches within 65536 of longl (image A's S05 header takes the same
   three; they are what the longl arm and the literals' survival need) *)
Hypothesis HPGS : forall a, inFP (ltoi_PG longlA) a ->
  Exists (in_zr a) (as_prog_static B) /\ in_img SEGS a.
Hypothesis HPG_RO : forall a, inFP (ltoi_PG longlA) a -> ~ in_roP SEGS RLO_A RHI_A a.
Hypothesis HPG_PTR : forall a p,
  ((exists i, (i < 5)%nat /\ a = wordsA + 8 * Z.of_nat i) \/
   (exists i, (i < pin_spec.CAT_N)%nat /\ a = pin_spec.row_addr catA i)) ->
  rdword (fun x => option_map (fun b : byte => bv_unsigned b) (seg_rom SEGS (Z_to_bv 64 x))) a = Some p ->
  p + 65536 <= longlA.
(* the runtime entries S05 calls *)
Hypothesis AMEMCPY : forall fx0 : YK11.FPState, aintrin_realizes (fx := fx0) SEGS B OCpy (SIG SS___asan_memcpy).
Hypothesis AMEMSET : forall fx0 : YK11.FPState, aintrin_realizes (fx := fx0) SEGS B OSet (SIG SS___asan_memset).
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState,
  RtPFSeg.seg_asnprintf_realizes (fx := fx0) SEGS B snp_lo snp_hi snp_cr
    (SIG SS___interceptor_trampoline_snprintf) gotwA guardA.
Hypothesis AFREE4 : forall fx0 : YK11.FPState, afree04_rule (fx := fx0) SEGS B MT.
(* what image B's close shows of snp_lo / snp_hi / snp_cr; each is a computation there *)
Hypothesis HSNP_LIT : forall x, In x LLVMFuzzerTestOneInput_c.LTOI_LITS ->
  snp_lo <= seg_litA_fz x /\ seg_litA_fz x + Z.of_nat (length x) + 1 <= gotwA.
Hypothesis HSNP_CR : Forall (fun r => snp_lo <= fst r /\ 0 <= snd r /\ fst r + snd r <= snp_hi) snp_cr.
Hypothesis HSNP_LO : 0 <= snp_lo.
Hypothesis HSNP_CEIL : snp_hi <= alloc_ceiling.
Hypothesis HSNP_FAKE : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> snp_hi <= ly_F ly.
(* the two program callees, at every FP state *)
Hypothesis HM_FILE : forall fx0 : YK11.FPState,
  m_file_c.m_file_contract (fx := fx0) SEGS B (BASE + AF_m_file) STK_m_file RLO_A RHI_A seg_litA_fz
    wordsA rolesA catA gotwA guardA.
Hypothesis HPARSE_FILE : forall fx0 : YK11.FPState,
  reac_segconf_parse_file_c.reac_segconf_parse_file_contract (fx := fx0) SEGS B
    (BASE + AF_reac_segconf_parse_file) STK_reac_segconf_parse_file RLO_A RHI_A seg_litA_rc catA gotwA guardA.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* the three image facts lt_img needs at a reader after a call, each from a field of IMGF (image A's S00 walk
   takes the same three as its record s10_img); this text compiled on the VM, log build-20261030T183150Z.log.
   Rename `s5a_` to `s5a_` in your file. *)
Lemma s5a_relro : forall a, RLO_A <= a < RHI_A -> in_img SEGS a.
Proof. exact (cif_relro_img _ _ IMGF). Qed.

(* ================================== the facts of a point of the walk ================================== *)
(* the entry sp and the realigned base S1 (andi sp,sp,-32 after addi sp,sp,-352); the S01 / S02 walk's lk_sp *)
Lemma s5a_sp : forall cx, lt_base B MT cx ->
  x_sp0 cx mod 16 = 0 /\ alloc_ceiling + STK_LLVMFuzzerTestOneInput <= x_sp0 cx /\ x_sp0 cx <= 2 ^ 47 /\
  x_s1 cx mod 32 = 0 /\ x_sp0 cx - LTOI_FRAME_MAX <= x_s1 cx /\ x_s1 cx <= x_sp0 cx - 352.
Proof using All.
intros cx HB. destruct HB as (HPRE & _). destruct HPRE as (_ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal & _ & Hceil & Hslo & Hshi & H47 & _).
unfold x_s1, x_sp0, LT_FRAME, LTOI_FRAME_MAX in *.
set (s := spZ (x_regs cx)) in *. clearbody s.
repeat split; lia.
Qed.
(* the class-3 frame of a journal state: where it and its shadow lie, and the shadow's bytes are present *)
Lemma s5a_frame : forall cx ly S (W : world SEGS) mem md k,
  lt_base B MT cx ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem md k ->
  In (LT_FCLS, x_fpos cx) (frames S) /\ frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx /\
  4096 <= x_fr cx /\ x_fr cx + 512 <= alloc_ceiling /\ in_app (x_fr cx) 512 /\
  x_sh cx = 2147450880 + x_fr cx / 8 /\
  (forall i, 0 <= i < 64 -> apresent (w_H W) mem (x_sh cx + i)).
Proof using All.
intros cx ly S W mem md k HB HJ.
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hfr0 & _).
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _).
assert (Hin : In (LT_FCLS, x_fpos cx) (frames S)) by (rewrite Hfrs, Hfr0; left; reflexivity).
assert (EF : frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx).
{ destruct Hly as (_ & _ & _ & _ & _ & EF & _). unfold x_fr, frame_addr. rewrite EF. reflexivity. }
destruct (al_frames _ _ LAWS ly S W mem md LT_FCLS (x_fpos cx) HAR Hin) as (_ & Happ & _ & Hsh).
destruct (frames_bounds SEGS B LAWS ly S W mem md LT_FCLS (x_fpos cx) HAR Hin) as (Hf0 & Hfc & _).
rewrite EF in Happ, Hsh, Hf0, Hfc.
change (fs_frame_bytes LT_FCLS) with 512 in Happ, Hsh, Hfc. change (512 / 8) with 64 in Hsh.
split; [exact Hin|]. split; [exact EF|]. split; [lia|]. split; [lia|]. split; [exact Happ|].
split; [unfold x_sh, shadow_addr, SHADOW_OFF; reflexivity|].
intros i Hi. unfold x_sh. exact (proj1 (Hsh i Hi)).
Qed.
(* a live block of a state is a harness block of that state (the S01 / S02 walk's lk_hblk) *)
Lemma s5a_hblk : forall ly S (W : world SEGS) mem md a n,
  AR SEGS B ly S W mem md -> In (a, n) (ablocks B ly S) -> lt_hblk B ly S (rdW W mem) a n.
Proof using All.
intros ly S W mem md a n HAR Hin.
destruct (al_blocks _ _ LAWS ly S W mem md a n HAR Hin) as (H16 & H4096 & Hceil & _ & _ & _ & Hn).
pose proof (req_size_pos n ltac:(lia)) as [_ Hreq].
pose proof asan_consts as (C1 & _).
split; [exact Hin|]. split; [exact H4096|]. split; [exact H16|].
split; [lia|]. split; [lia|].
split; [exact (amem_range_of_block SEGS B LAWS ly S W mem md a n a n HAR Hin ltac:(lia) ltac:(lia))|].
split; [exact (range_addressable_of_block SEGS B LAWS ly S W mem md a n a n HAR Hin ltac:(lia) ltac:(lia))|].
intros Hn0. exact (shadow_hull_vis_of_block SEGS B LAWS ly S W mem md a n a n HAR Hin ltac:(lia) ltac:(lia) Hn0).
Qed.
(* a block apart from the others of the state (AR_sep_law) *)
Lemma s5a_sep : forall ly S (W : world SEGS) mem md x l y,
  AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) (x :: l) -> In y l ->
  zdisjoint (block_rng x) (block_rng y).
Proof using All.
intros ly S W mem md x l y HAR HP Hy.
apply in_split in Hy as (l1 & l2 & ->).
apply (sep_blocks_perm SEGS B LAWS ly S W mem md x y (l1 ++ l2) HAR).
eapply Permutation_trans; [exact HP|]. apply perm_skip. apply Permutation_sym, Permutation_middle.
Qed.
Lemma s5a_notin : forall ly S (W : world SEGS) mem md x l l0,
  AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) (x :: l ++ l0) -> 0 <= snd x -> ~ In x l0.
Proof using All.
intros ly S W mem md x l l0 HAR HP Hn Hin.
pose proof (s5a_sep ly S W mem md x (l ++ l0) x HAR HP (in_or_app _ _ _ (or_intror Hin))) as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. pose proof (req_size_pos (snd x) Hn). lia.
Qed.
(* the image facts carried to a reader that agrees on the image bytes the runtime does not own (the S01 / S02 walk's
   lk_img_kept, with the header's s5a_relro, IMGF's guard field, and the stack-protector cells re-derived from AR
   at the later state by SegRecCells.seg_rec_cells, since the runtime owns the .got word gotwA) *)
Lemma s5a_rom_view_some : forall (H : word -> bool) mem a, seg_rom SEGS (Z_to_bv 64 a) <> None ->
  aview SEGS H mem a <> None.
Proof using All.
intros H mem a Hr. unfold aview, mbyte. destruct (mrestrict H mem (Z_to_bv 64 a)) as [b|]; [cbn; discriminate|].
destruct (seg_rom SEGS (Z_to_bv 64 a)) as [b|] eqn:E; [cbn; discriminate | congruence].
Qed.
Lemma s5a_lit_kept : forall (W W' : world SEGS) mem mem' a s,
  (forall x, a <= x < a + (Z.of_nat (length s) + 1) -> rdW W' mem' x = rdW W mem x) ->
  sa_lit SEGS B (rdW W mem) a s -> sa_lit SEGS B (rdW W' mem') a s.
Proof using All.
intros W W' mem mem' a s HK (Ha & ((Hzs & Hn0) & _) & Hpin & Hrt & Himg).
split; [exact Ha|]. split; [split; [split; [|exact Hn0] | exact (sa_tail_of_romtail SEGS (w_H W') mem' _ Hrt)]|].
- intros i Hi. rewrite HK; [exact (Hzs i Hi)|]. rewrite length_app in Hi. cbn [length] in Hi. lia.
- split; [exact Hpin|]. split; [exact Hrt | exact Himg].
Qed.
Lemma s5a_img_kept : forall cx (W W' : world SEGS) mem mem' ly' S' md',
  AR SEGS B ly' S' W' mem' md' ->
  lt_img B cx (rdW W mem) ->
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     rdW W' mem' a = rdW W mem a) ->
  lt_img B cx (rdW W' mem').
Proof using All.
intros cx W W' mem mem' ly' S' md' HAR' (HRO & HIMG & HGI) HK.
assert (KI : forall q n, sa_img SEGS B q n -> forall x, q <= x < q + n -> rdW W' mem' x = rdW W mem x).
{ intros q n Hq x Hx. destruct (Hq x Hx) as (H1 & H2 & H3). exact (HK x H1 H2 H3). }
assert (KL : forall a s, sa_lit SEGS B (rdW W mem) a s -> sa_lit SEGS B (rdW W' mem') a s).
{ intros a s Hl. apply (s5a_lit_kept W W' mem mem' a s); [|exact Hl].
  destruct Hl as (_ & _ & _ & _ & Himg). exact (KI _ _ Himg). }
destruct HIMG as (Hm40 & Hm40i & Hfz & Hrc & Hcat & Hcata & Hw & Hrl & Hssp & Hpin & Hrt & Hli & Hd1 & Hd2 & Hd3).
split; [|split].
- intros a Hro Ho He. rewrite (HK a); [exact (HRO a Hro Ho He) | | exact Ho | exact He].
  destruct Hro as [(s & Hs & _ & Hr) | Hrr]; [exists s; split; [exact Hs | exact Hr] | exact (s5a_relro a Hrr)].
- split; [intros k Hk; rewrite (KI _ 8 Hm40i) by lia; exact (Hm40 k Hk)|].
  split; [exact Hm40i|].
  split; [intros s Hs; destruct (Hfz s Hs) as [H1 H2]; exact (conj (KL _ _ H1) H2)|].
  split; [intros s Hs; destruct (Hrc s Hs) as [H1 H2]; exact (conj (KL _ _ H1) H2)|].
  split.
  { destruct Hcat as (Hcp & Hci & Hrows). split; [exact Hcp|]. split; [exact Hci|].
    intros i Hi. destruct (Hrows i Hi) as (tp & Htp & Hl). exists tp. split; [|exact (KL _ _ Hl)].
    apply (s5a_word_kept (rdW W mem)); [|exact Htp]. intros x Hx. apply (KI _ _ Hci).
    unfold pin_spec.row_addr, pin_spec.CAT_ROW, pin_spec.CAT_BYTES, pin_spec.CAT_N in *. lia. }
  split; [exact Hcata|].
  split.
  { destruct Hw as (Hwp & Hwi & Hws). split; [exact Hwp|]. split; [exact Hwi|].
    intros i Hi. destruct (Hws i Hi) as (wp & Hwp' & Hl). exists wp. split; [|exact (KL _ _ Hl)].
    apply (s5a_word_kept (rdW W mem)); [|exact Hwp']. intros x Hx. apply (KI _ _ Hwi). lia. }
  split.
  { destruct Hrl as (Hrp & Hri & Hrs). split; [exact Hrp|]. split; [exact Hri|].
    intros i Hi k Hk. rewrite (KI _ _ Hri) by lia. exact (Hrs i Hi k Hk). }
  split.
  { exact (proj1 (proj2 (SegRecCells.seg_rec_cells SEGS B LAWS HBS IMGF ly' S' W' mem' md' HAR'))). }
  split; [exact Hpin|]. split; [exact Hrt|]. split; [exact Hli|].
  split; [exact Hd1|]. split; [exact Hd2 | exact Hd3].
- intros i Hi. rewrite (KI _ _ Hli) by (unfold LONGL_W, LONGL_N; lia). exact (HGI i Hi).
Qed.

Lemma s5a_slots_off : forall cx c m f o v, In (o, v) (S5_slots cx c m f) -> 16 <= o <= 216.
Proof using All.
intros cx c m f o v Hin. unfold S5_slots, LT_L in Hin. cbn [app In] in Hin.
repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- _; lia|]). destruct Hin.
Qed.
(* the core of a point carried to a state of the same journal count whose memory differs only in the block t, the
   callee's window below S1 and the label's five shadow bytes, these as o' says *)
Lemma s5a_keep : forall cx ly S (W : world SEGS) regs mem md k acc rem o o' t tn c m regs' mem' md',
  lt_base B MT cx ->
  lt_core B MT cx ly S W regs mem md k acc rem o [(t, tn); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem' md' k ->
  0 <= tn ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (t <= a < t + req_size tn) -> ~ (x_s1 cx - 4096 <= a < x_s1 cx) ->
     ~ (x_sh cx + 12 <= a < x_sh cx + 17) -> rdW W mem' a = rdW W mem a) ->
  (forall i, (i < 36)%nat -> ~ (12 <= i < 17)%nat -> nth i (lt_fsh o') 0 = nth i (lt_fsh o) 0) ->
  (forall i, (12 <= i < 17)%nat -> rdW W mem' (x_sh cx + Z.of_nat i) = Some (nth i (lt_fsh o') 0)) ->
  lt_core B MT cx ly S W regs' mem' md' k acc rem o' [(t, tn); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)].
Proof using All.
intros cx ly S W regs mem md k acc rem o o' t tn c m regs' mem' md' HB HC HJ' Htn P2 P3 P4 P8 P9 HK Hsame Hnew.
pose proof (s5a_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
unfold STK_LLVMFuzzerTestOneInput, LTOI_FRAME_MAX in Hsp0, Hs1lo.
destruct HC as (HF & HI & HBL & HBUD).
destruct HF as (HJ & R2 & R3 & R4 & R8 & R9 & HSV & HH0 & HH8 & HH16 & HFL & H200 & HSH & H184).
pose proof (proj1 HJ) as HAR.
destruct (s5a_frame cx ly S W mem md k HB HJ) as (HinF & EF & F4096 & Fceil & Fapp & Esh & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HtIn : In (t, tn) (ablocks B ly S))
  by (unfold lt_blocks in HBL; apply (Permutation_in _ (Permutation_sym HBL)); left; reflexivity).
destruct (al_blocks _ _ LAWS ly S W mem md t tn HAR HtIn) as (_ & Ht4096 & Htceil & Htapp & _).
pose proof (req_size_pos tn Htn) as [Hq1 Hq2].
pose proof (sep_block_frame SEGS B LAWS ly S W mem md t tn LT_FCLS (x_fpos cx) HAR HtIn HinF) as Hsep.
rewrite EF in Hsep. change (fs_frame_bytes LT_FCLS) with 512 in Hsep. unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
assert (KS : forall a, x_s1 cx <= a < 2 ^ 64 -> rdW W mem' a = rdW W mem a)
  by (intros a Ha; apply HK; rewrite ?Esh; lia).
assert (KF : forall a, x_fr cx <= a < x_fr cx + 512 -> rdW W mem' a = rdW W mem a).
{ intros a Ha. apply HK; [lia | lia | lia |].
  intros Hw. apply (s5a_sh_not_app (x_fr cx) 64 (x_fr cx) 512 a); [lia | lia | exact Fapp | rewrite Esh in Hw; lia | lia]. }
assert (KH : forall i, 0 <= i < 64 -> ~ (12 <= i < 17) -> rdW W mem' (x_sh cx + i) = rdW W mem (x_sh cx + i)).
{ intros i Hi Hn. apply HK; [rewrite Esh; lia | | rewrite Esh; lia | lia].
  intros Hw. apply (s5a_sh_not_app (x_fr cx) 64 t (req_size tn) (x_sh cx + i));
    [lia | lia | exact Htapp | rewrite Esh; lia | lia]. }
assert (KI : forall a, in_img SEGS a -> rdW W mem' a = rdW W mem a).
{ intros a Ha. pose proof (pa_img_range a Ha) as Hr. unfold kImgEnd in Hr.
  apply HK; [lia | | lia | rewrite Esh; lia].
  intros Hw. exact (blk_img SEGS B LAWS ly S W mem md t tn a HAR HtIn Hw Ha). }
split; [|split; [|split]].
- split; [exact HJ'|].
  rewrite P2, P3, P4, P8, P9.
  split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R8|]. split; [exact R9|].
  split.
  { intros i r Hi. assert (Hi13 : (i < length LT_SAVED)%nat) by (apply nth_error_Some; congruence).
    change (length LT_SAVED) with 13%nat in Hi13.
    apply (s5a_word_kept (rdW W mem)); [|exact (HSV i r Hi)]. intros x Hx. apply KS. lia. }
  split; [apply (s5a_word_kept (rdW W mem)); [|exact HH0]; intros x Hx; apply KF; lia|].
  split; [apply (s5a_word_kept (rdW W mem)); [|exact HH8]; intros x Hx; apply KF; lia|].
  split; [apply (s5a_word_kept (rdW W mem)); [|exact HH16]; intros x Hx; apply KF; lia|].
  split; [apply (s5a_word_kept (rdW W mem)); [|exact HFL]; intros x Hx; apply KF; unfold LT_FLAGW in *; lia|].
  split; [apply (s5a_word_kept (rdW W mem)); [|exact H200]; intros x Hx; apply KS; lia|].
  split; [|apply (s5a_word_kept (rdW W mem)); [|exact H184]; intros x Hx; apply KS; lia].
  intros i Hi. rewrite lt_fsh_len in Hi.
  destruct (Nat.ltb_spec i 12) as [Hlo|Hlo]; [|destruct (Nat.ltb_spec i 17) as [Hhi|Hhi]].
  + rewrite KH by lia. rewrite (Hsame i Hi ltac:(lia)). apply HSH. rewrite lt_fsh_len. exact Hi.
  + apply Hnew. lia.
  + rewrite KH by lia. rewrite (Hsame i Hi ltac:(lia)). apply HSH. rewrite lt_fsh_len. exact Hi.
- apply (s5a_img_kept cx W W mem mem' ly S md' (proj1 HJ') HI). intros a Ha _ _. exact (KI a Ha).
- exact HBL.
- exact HBUD.
Qed.
(* the reader state, the model state and the slots of a point carried the same way *)
Lemma s5a_aux_keep : forall cx ly S (W : world SEGS) mem md k t tn c m st L mem',
  lt_base B MT cx ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem md k ->
  lt_blocks B cx ly S [(t, tn); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (t <= a < t + req_size tn) -> ~ (x_s1 cx - 4096 <= a < x_s1 cx) ->
     ~ (x_sh cx + 12 <= a < x_sh cx + 17) -> rdW W mem' a = rdW W mem a) ->
  (forall o v, In (o, v) L -> 16 <= o <= 216) ->
  lt_cm (rdW W mem) c m st -> lt_slots cx (rdW W mem) L ->
  lt_cm (rdW W mem') c m st /\ lt_slots cx (rdW W mem') L.
Proof using All.
intros cx ly S W mem md k t tn c m st L mem' HB HJ HBL HK HL (HRC & HMC) HSL.
pose proof (s5a_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
unfold STK_LLVMFuzzerTestOneInput, LTOI_FRAME_MAX in Hsp0, Hs1lo.
pose proof (proj1 HJ) as HAR.
destruct (s5a_frame cx ly S W mem md k HB HJ) as (HinF & EF & F4096 & Fceil & Fapp & Esh & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold lt_blocks in HBL. cbn [app] in HBL.
assert (HtIn : In (t, tn) (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym HBL)); left; reflexivity).
assert (HmIn : In (m, seg_spec.SEG_M_SIZE) (ablocks B ly S))
  by (apply (Permutation_in _ (Permutation_sym HBL)); right; left; reflexivity).
assert (HcIn : In (c, seg_spec.SEG_C_SIZE) (ablocks B ly S))
  by (apply (Permutation_in _ (Permutation_sym HBL)); right; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ t _ HAR HtIn) as (_ & Ht4 & Htc & _ & _ & _ & Htn).
destruct (al_blocks _ _ LAWS _ _ _ _ _ m _ HAR HmIn) as (_ & Hm4 & Hmc & Hmapp & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ c _ HAR HcIn) as (_ & Hc4 & Hcc & Hcapp & _).
pose proof (req_size_pos tn ltac:(lia)) as [Hq1 Hq2].
pose proof (s5a_sep ly S W mem md (t, tn) _ (m, seg_spec.SEG_M_SIZE) HAR HBL ltac:(left; reflexivity)) as Dm.
pose proof (s5a_sep ly S W mem md (t, tn) _ (c, seg_spec.SEG_C_SIZE) HAR HBL ltac:(right; left; reflexivity)) as Dc.
unfold zdisjoint, block_rng in Dm, Dc. cbn [fst snd] in Dm, Dc.
change (req_size seg_spec.SEG_C_SIZE) with seg_spec.SEG_C_SIZE in Hcc, Hcapp, Dc.
change (req_size seg_spec.SEG_M_SIZE) with seg_spec.SEG_M_SIZE in Hmc, Hmapp, Dm.
unfold seg_spec.SEG_C_SIZE, seg_spec.SEG_M_SIZE in Hcc, Hcapp, Dc, Hmc, Hmapp, Dm.
split; [split|].
- apply (s5a_rconf_xfer (rdW W mem)); [|exact HRC]. unfold seg_spec.SEG_C_SIZE.
  intros i Hi. apply HK; [lia | lia | lia |].
  intros Hw. apply (s5a_sh_not_app (x_fr cx) 64 c 16616 (c + i)); [lia | lia | exact Hcapp | rewrite Esh in Hw; lia | lia].
- apply (s5a_mconf_xfer (rdW W mem)); [|exact HMC]. unfold seg_spec.SEG_M_SIZE.
  intros i Hi. apply HK; [lia | lia | lia |].
  intros Hw. apply (s5a_sh_not_app (x_fr cx) 64 m 9236 (m + i)); [lia | lia | exact Hmapp | rewrite Esh in Hw; lia | lia].
- intros o v Hin. pose proof (HL o v Hin) as Ho.
  apply (s5a_word_kept (rdW W mem)); [|exact (HSL o v Hin)]. intros x Hx. apply HK; rewrite ?Esh; lia.
Qed.
(* the turn's text bytes at the cursor P1 of the payload, at any state of the journal (the payload is the entry's
   block, which the function does not write, ajournal's 10th conjunct, and the entry's bytes, lt_base's garr8) *)
Lemma s5a_pay : forall cx ly S (W : world SEGS) mem md k O f i,
  lt_base B MT cx -> Z.of_nat f < x_nf cx ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem md k ->
  lt_blocks B cx ly S O ->
  (i < length (seg_spec.seg_txt (x_pl cx) f))%nat ->
  0 < x_n cx /\ In (x_p cx, x_n cx) (ablocks B ly S) /\ In (x_p cx, x_n cx) (x_bl0 B cx) /\
  x_p cx <= x_at cx f /\ x_at cx f + Z.of_nat (length (seg_spec.seg_txt (x_pl cx) f)) <= x_p cx + x_n cx /\
  rdW W mem (x_at cx f + Z.of_nat i) = Some (nth i (seg_spec.seg_txt (x_pl cx) f) 0).
Proof using All.
intros cx ly S W mem md k O f i HB Hf HJ HBL Hi.
pose proof HB as (_ & _ & _ & _ & _ & _ & Hpn & Hlen & HG8 & _).
destruct (s5a_txt_byte (x_pl cx) f i Hf Hi) as (Eb & Hj & Htl).
destruct (s5_txt_firstn (x_pl cx) f Hf) as (_ & Hle1 & Hle2).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & KB0 & _).
assert (HN : 0 < x_n cx) by (rewrite Hlen; lia).
destruct Hpn as [[Hn0 _] | [Hn Hp]]; [lia|].
assert (HpIn : In (x_p cx, x_n cx) (ablocks B ly S)).
{ unfold lt_blocks in HBL. apply (Permutation_in _ (Permutation_sym HBL)). apply in_or_app. right. exact Hp. }
assert (Hat : x_at cx f = x_p cx + Z.of_nat (length (x_pl cx)) - Z.of_nat (length (seg_spec.seg_turn_tail (x_pl cx) f)))
  by reflexivity.
split; [exact HN|]. split; [exact HpIn|]. split; [exact Hp|].
split; [rewrite Hat; lia|]. split; [rewrite Hat, Hlen; lia|].
set (j := (length (x_pl cx) - length (seg_spec.seg_turn_tail (x_pl cx) f) + i)%nat) in *.
assert (Ea : x_at cx f + Z.of_nat i = x_p cx + Z.of_nat j) by (rewrite Hat; unfold j; lia).
rewrite Ea, Eb.
assert (Hj' : (j < length (map (fun b : byte => bv_unsigned b) (x_pl cx)))%nat) by (rewrite length_map; exact Hj).
destruct (HG8 j Hj') as [Hv Hr].
rewrite (KB0 (x_p cx) (x_n cx) (Z.of_nat j) Hp HpIn).
- exact (aview_of_val_mem1 SEGS (w_H (x_W cx)) (x_mem cx) _ _ Hv Hr).
- rewrite s5a_req by lia. rewrite Hlen. lia.
- intros Hfp. destruct (HPGS _ Hfp) as [_ Himg].
  exact (blk_img SEGS B LAWS ly S W mem md (x_p cx) (x_n cx) (x_p cx + Z.of_nat j) HAR HpIn
    ltac:(rewrite s5a_req by lia; rewrite Hlen; lia) Himg).
Qed.
(* a byte the plain run stored as the chunk 0 *)
Lemma s5a_rd_zero1 : forall (W : world SEGS) mem E base off e,
  YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) base (YP09.mkChunk off (CVal 1 e)) ->
  sv_denot E e = Z_to_bv 64 0 -> rdW W mem (base + off) = Some 0.
Proof using All.
intros W mem E base off e Hc He. destruct (Hc 0 ltac:(cbn; lia)) as (b & Hb1 & Hb2).
cbn [YP09.c_off YP09.c_val YP09.cbyte] in Hb1, Hb2. rewrite He in Hb1. injection Hb1 as <-.
unfold aview. rewrite Z.add_0_r in Hb2. rewrite Hb2. cbn [option_map].
vm_compute. reflexivity.
Qed.

(* ================ 0x8522c .. 0x8526c: the trap, check 7 and the NUL (token run B), the label (plain run C) ================ *)
Lemma s5a_tail : forall f, S5_LB_stmt B MT f ->
  forall cx ly S W regs mem md k acc (c m t : Z),
  lt_base B MT cx -> sa_frm0 -> Z.of_nat f < x_nf cx ->
  S5_body B MT cx ly S W regs mem md k acc LFO0 c m t f ->
  lt_cm (rdW W mem) c m (x_st cx f) ->
  (forall i, (i < length (s5_txt (x_pl cx) f))%nat ->
     rdW W mem (t + Z.of_nat i) = Some (nth i (s5_txt (x_pl cx) f) 0)) ->
  getr regs 18 = w64 (x_nf cx) -> getr regs 20 = w64 (seg_spec.seg_txt_n (x_pl cx) f) -> getr regs 21 = w64 0 ->
  getr regs 22 = w64 m -> getr regs 23 = w64 t -> getr regs 24 = w64 (x_at cx f + x_np cx f) ->
  getr regs 25 = w64 (Z.of_nat f) -> getr regs 26 = w64 (seg_spec.seg_lb (x_pl cx) f) ->
  lt_slots cx (rdW W mem) (S5_slots cx c m f) ->
  SRr SEGS W (cfg_at SEGS (BASE + 0x46c) regs mem md) (lt_post B MT cx).
Proof using All.
intros f HK cx ly S W regs mem md k acc c m t HB HFRM Hf (HC & HcB & HmB & Ht & HCNT) HCM HTX
  R18 R20 R21 R22 R23 R24 R25 R26 HSL.
set (n := seg_spec.seg_txt_n (x_pl cx) f) in *.
assert (Hn0 : 0 <= n) by (unfold n, seg_spec.seg_txt_n; lia).
assert (Htn : x_tn cx f = n + 1) by reflexivity.
assert (HnL : n = Z.of_nat (length (s5_txt (x_pl cx) f))) by reflexivity.
assert (HnL' : n = Z.of_nat (length (seg_spec.seg_txt (x_pl cx) f))) by reflexivity.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (s5a_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
unfold STK_LLVMFuzzerTestOneInput, LTOI_FRAME_MAX in Hsp0, Hs1lo.
pose proof HC as (HF & HI & HBL & HBUD).
pose proof HF as (HJ & Rsp & Rgp & Rtp & Rs0 & Rs1 & HSV & HH0 & HH8 & HH16 & HFL & H200 & HSH & H184).
pose proof (proj1 HJ) as HAR.
pose proof HJ as HJ0.
destruct (s5a_frame cx ly S W mem md k HB HJ) as (HinF & EF & F4096 & Fceil & Fapp & Esh & SHP).
pose proof Ht as (HtIn & Ht4096 & _ & _).
destruct (al_blocks _ _ LAWS ly S W mem md t (x_tn cx f) HAR HtIn) as (_ & _ & Htceil & Htapp & Htpres & _ & _).
rewrite Htn, s5a_req in Htceil, Htapp, Htpres by lia.
unfold lt_blocks in HBL. cbn [app] in HBL.
assert (Htnot : ~ In (t, x_tn cx f) (x_bl0 B cx))
  by exact (s5a_notin ly S W mem md (t, x_tn cx f) [(m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] (x_bl0 B cx)
    HAR HBL ltac:(cbn [snd]; lia)).
assert (NSH : forall a, t <= a < t + n + 1 -> ~ (x_sh cx + 12 <= a < x_sh cx + 17)).
{ intros a Ha Hw. apply (s5a_sh_not_app (x_fr cx) 64 t (n + 1) a); [lia | lia | exact Htapp | rewrite Esh in Hw; lia | lia]. }
(* ---- seed B at 0x8522c ---- *)
set (E := Eimg (Ereg regs [Z_to_bv 64 (t + n)])).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall q (r : bv 5), Z.of_nat q = bv_unsigned r -> ew E q = getr regs r)
  by (intros q r Hq; subst E; apply ew_Eimg_Ereg_nat; exact Hq).
assert (E32 : ew E 32 = Z_to_bv 64 (t + n))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 (t + n)]) E)
  by (split; [intros q Hq; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]).
assert (U9 : bv_unsigned (ew E 9) = x_s1 cx)
  by (rewrite (EE 9%nat 9%bv eq_refl), Rs1; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = t + n) by (rewrite E32; apply unsigned_lit_small; lia).
assert (E23 : ew E 23 = Z_to_bv 64 t) by (rewrite (EE 23%nat 23%bv eq_refl); exact R23).
assert (E20 : ew E 20 = Z_to_bv 64 n) by (rewrite (EE 20%nat 20%bv eq_refl); exact R20).
assert (U23 : bv_unsigned (ew E 23) = t) by (rewrite E23; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E 20) = n) by (rewrite E20; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E s5a_ssB
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0x46c)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok;
      cbn [s5a_rs1 s5a_rtx YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ _ 200 8 (SLit SHADOW_OFF) SHADOW_OFF);
        [reflexivity | cbn; unfold SHADOW_OFF; lia | cbn; lia | exact (val_mem_of_rdword SEGS _ _ _ _ H200)].
    + rewrite U32. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). exact (proj1 (Htpres (t + n + o) ltac:(lia))).
  - apply pairwise_disjoint_of_extents. unfold extent_of_region.
    cbn [map s5a_rs1 s5a_rtx YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U32.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - split; [|split].
    + cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U32.
      change (2 ^ 0) with 1. rewrite Z.mod_1_r. repeat split; lia.
    + exact I.
    + cbn [f_alias alias_ok]. split; [|exact I].
      apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U23, U20, U32, !Z.add_0_r.
      rewrite (zcanon_small t), (zcanon_small n), (zcanon_small (t + n)) by lia. reflexivity. }
assert (SHOK : sh_ok SEGS s5a_x s5a_SHB E (mrestrict (w_H W) mem)).
{ unfold sh_ok, s5a_SHB. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) mem E s5a_x 32 (t + n) 1 (t + n) 0 1).
  + exact (range_addressable_of_block SEGS B LAWS ly S W mem md t (x_tn cx f) (t + n) 1 HAR HtIn
      ltac:(lia) ltac:(rewrite Htn, s5a_req by lia; lia)).
  + unfold U, s5a_x. cbn [sv_denot]. apply unsigned_lit_small. unfold SHADOW_OFF. lia.
  + rewrite U_SOff, U32, Z.add_0_r. apply zcanon_small. lia.
  + lia.
  + lia.
  + intros x Hx. change (Z.min 0 1) with 0 in Hx. change (Z.max 0 1) with 1 in Hx.
    unfold in_app, kLowShadowBeg in Htapp. rewrite C3 in Htapp. unfold SHADOW_OFF. lia. }
assert (AWRB : awr_ok SEGS B E (ss_mem s5a_ssB) STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA)
  (ablocks B (x_ly cx) (x_S cx)) (ablocks B ly S) (frames (x_S cx)) ly [(LT_FCLS, x_fpos cx)]).
{ cbn [s5a_ssB ss_mem].
  eapply awr_ok_cons_gen; [reflexivity | exact U9 | | ].
  { intros a Ha. cbn [s5a_rs1 YP09.r_wlo YP09.r_whi] in Ha. lia. }
  eapply awr_ok_cons_gen; [reflexivity | exact U32 | | apply awr_ok_nil].
  intros a Ha. cbn [s5a_rtx YP09.r_wlo YP09.r_whi] in Ha.
  right; right; left. exists t, (x_tn cx f). split; [exact HtIn | split; [exact Htnot | rewrite Htn, s5a_req by lia; lia]]. }
unfold cfg_at, w64.
(* 0x8522c: `not a0,s7`; it stops at `bltu a0,s4` (0x85230) *)
paj_run_tok RUN HS HJ SHOK s5a_span.
{ exact AWRB. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md1 := d) in *; clearbody md1 end.
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (t + n <= a < t + n + 1) -> rdW W (ms_mem ms) a = rdW W mem a).
{ intros a Ha Hna.
  apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => t + n <= a < t + n + 1) HFr); [|exact Ha | exact Hna].
  intros b wlo whi a' Hin Hrr. vm_compute in Hin.
  destruct Hin as [Hq0 | [Hq0 | []]]; injection Hq0 as <- <- <-; cbn [base_val] in Hrr; [lia|].
  rewrite U32 in Hrr. cbv beta. lia. }
clear HF HFr HG.
rename ms into ms1.
psrr_branch_tok RUN BR HS SHOK s5a_span.
- (* the trap (0x85ff8): t + n would wrap; it does not, t + n + 1 <= alloc_ceiling (al_blocks) *)
  exfalso. rewrite branch_ltu_U in Hc.
  rewrite (s5a_not_U E 23 t _ E23 ltac:(lia)) in Hc; [|reflexivity].
  rewrite (U_atom E 20 n E20 ltac:(lia)) in Hc.
  apply Z.ltb_lt in Hc. lia.
- (* t + n: a0 := t + n, check 7 (a token covered by the shadow entry), text[n] := 0; stop at 0x85250 *)
  paj_run_to_tok RUNTO HS HJ SHOK s5a_span 0x490.
  { exact AWRB. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md2 := d) in *; clearbody md2 end.
  assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (t + n <= a < t + n + 1) ->
    rdW W (ms_mem ms) a = rdW W (ms_mem ms1) a).
  { intros a Ha Hna.
    apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => t + n <= a < t + n + 1) HFr); [|exact Ha | exact Hna].
    intros b wlo whi a' Hin Hrr. vm_compute in Hin.
    destruct Hin as [Hq0 | [Hq0 | []]]; injection Hq0 as <- <- <-; cbn [base_val] in Hrr; [lia|].
    rewrite U32 in Hrr. cbv beta. lia. }
  clear HF HFr HG.
  lazymatch type of HS with st_ok_pi _ _ ?E4 _ _ =>
    assert (U32' : bv_unsigned (ew E4 32) = t + n) by (cbn [ew ewset Nat.eqb]; exact U32);
    assert (HAE4 : env_agree 32 (Ereg regs [Z_to_bv 64 (t + n)]) E4) end.
  { pose proof HAE as [HA1 HA2]. split.
    - intros q Hq32. cbn [ew ewset].
      repeat match goal with |- context [Nat.eqb ?a ?b] => destruct (Nat.eqb_spec a b); [lia|] end.
      exact (HA1 q Hq32).
    - cbn [ed ewset]. exact HA2. }
  (* text[n] = 0, from the byte's chunk *)
  assert (HZ : rdW W (ms_mem ms) (t + n) = Some 0).
  { pose proof (st_ok_mem_ok SEGS _ _ _ HS) as HM. cbn [abs_ss setpc ss_mem restrict ms_mem] in HM.
    pose proof (mem_ok_region SEGS _ _ _ _ HM (in_cons _ _ _ (in_eq _ _))) as HR3.
    pose proof (region_ok_chunk SEGS _ _ _ _ HR3 (in_eq _ _)) as HCk.
    cbn [YP09.r_base YP09.r_chunks base_val] in HCk. rewrite U32' in HCk.
    pose proof (val_of_chunk_ok SEGS _ _ _ 0 1 (SLit 0) 0 HCk eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as HV.
    rewrite Z.add_0_r in HV. exact (aview_of_val_mem1 SEGS _ _ _ _ HV ltac:(lia)). }
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs [Z_to_bv 64 (t + n)]
    [2; 3; 4; 8; 9; 18; 20; 21; 22; 23; 24; 25; 26]%bv HS HAE4 ltac:(vm_compute; reflexivity)) as HKR.
  cbn [ms_regs restrict] in HKR.
  pmkst HS.
  rename ms into ms2.
  (* ---- seed C at 0x85250 ---- *)
  destruct (s5a_frame cx ly S W (ms_mem ms2) md2 k HB HJ) as (_ & _ & _ & _ & _ & _ & SHP2).
  assert (H184' : rdword (rdW W (ms_mem ms2)) (x_s1 cx + 184) = Some (x_sh cx)).
  { apply (s5a_word_kept (rdW W mem)); [|exact H184]. intros x Hx.
    rewrite (K2 x ltac:(lia) ltac:(lia)). exact (K1 x ltac:(lia) ltac:(lia)). }
  set (E3 := Eimg (Ereg (ms_regs ms2) [Z_to_bv 64 (x_sh cx)])).
  assert (HEI3 : img_env VAL A_LIM E3) by (subst E3; apply Eimg_env).
  assert (EE3 : forall q (r : bv 5), Z.of_nat q = bv_unsigned r -> ew E3 q = getr (ms_regs ms2) r)
    by (intros q r Hq; subst E3; apply ew_Eimg_Ereg_nat; exact Hq).
  assert (E3_32 : ew E3 32 = Z_to_bv 64 (x_sh cx))
    by (subst E3; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra (ms_regs ms2) _ 0)).
  assert (HAE3 : env_agree 32 (Ereg (ms_regs ms2) [Z_to_bv 64 (x_sh cx)]) E3)
    by (split; [intros q Hq; subst E3; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]).
  assert (V9 : bv_unsigned (ew E3 9) = x_s1 cx)
    by (rewrite (EE3 9%nat 9%bv eq_refl), (HKR 9%bv ltac:(cbn; tauto)), Rs1; apply unsigned_lit_small; lia).
  assert (V32 : bv_unsigned (ew E3 32) = x_sh cx) by (rewrite E3_32; apply unsigned_lit_small; rewrite Esh; lia).
  assert (HS3 : st_ok_pi SEGS VAL E3 s5a_ssC
    (restrict (w_H W) (mkst (ms_regs ms2) (Z_to_bv 64 (BASE + 0x490)) (ms_mem ms2) (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
    - subst E3. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok;
        cbn [s5a_rsh s5a_rsl YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      + rewrite V32. split; [lia|]. split; [rewrite Esh; lia|]. split; [|constructor].
        intros o Ho. apply (apresent_writable SEGS). apply SHP2. lia.
      + rewrite V9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val SEGS E3 _ _ 184 8 (SOff 32 0) (x_sh cx));
          [cbn [sv_denot]; rewrite E3_32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; rewrite Esh; lia | cbn; lia
          | exact (val_mem_of_rdword SEGS _ _ _ _ H184')].
    - apply pairwise_disjoint_of_extents. unfold extent_of_region.
      cbn [map s5a_rsh s5a_rsl YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite V9, V32.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. rewrite Esh. repeat split; lia.
    - unfold facts_ok; cbn; repeat split; first [exact I | apply Forall_nil | constructor]. }
  assert (AWRC : awr_ok SEGS B E3 (ss_mem s5a_ssC) STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA)
    (ablocks B (x_ly cx) (x_S cx)) (ablocks B ly S) (frames (x_S cx)) ly [(LT_FCLS, x_fpos cx)]).
  { cbn [s5a_ssC ss_mem].
    eapply awr_ok_cons_gen; [reflexivity | exact V32 | | ].
    { intros a Ha. cbn [s5a_rsh YP09.r_wlo YP09.r_whi] in Ha.
      right; right; right; left. exists LT_FCLS, (x_fpos cx). split; [left; reflexivity|]. right.
      unfold in_zr. cbn [fst snd]. rewrite EF. change (fs_frame_bytes LT_FCLS / 8) with 64. unfold x_sh in Ha. lia. }
    eapply awr_ok_cons_gen; [reflexivity | exact V9 | | apply awr_ok_nil].
    intros a Ha. cbn [s5a_rsl YP09.r_wlo YP09.r_whi] in Ha. lia. }
  clear HS SHOK.
  (* 0x85250 .. 0x85268: a1 := 184(s1) = SH(FR), SH(FR) + 12 .. 16 := 0, a0 := lb << 56; stop at 0x8526c *)
  paj_run_to_sh (SRr_run_to_pi_AJ (fx := fx) B LAWS) HS3 HJ LO_S5LB.
  { exact AWRC. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md3 := d) in *; clearbody md3 end.
  cbn [ms_mem mkst] in HFr.
  assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (x_sh cx + 12 <= a < x_sh cx + 17) ->
    rdW W (ms_mem ms) a = rdW W (ms_mem ms2) a).
  { intros a Ha Hna.
    apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => x_sh cx + 12 <= a < x_sh cx + 17) HFr);
      [|exact Ha | exact Hna].
    intros b wlo whi a' Hin Hrr. vm_compute in Hin.
    destruct Hin as [Hq0 | [Hq0 | []]]; injection Hq0 as <- <- <-; cbn [base_val] in Hrr;
      [rewrite V32 in Hrr; cbv beta; lia | lia]. }
  assert (W5 : forall o, 12 <= o < 17 -> rdW W (ms_mem ms) (x_sh cx + o) = Some 0).
  { pose proof (st_ok_pi_region_nth E3 _ _ 0 _ HS3 eq_refl) as RG. cbn [ms_mem restrict] in RG.
    destruct RG as (_ & _ & _ & RGc). cbn [YP09.r_base base_val YP09.r_chunks] in RGc. rewrite V32 in RGc.
    intros o Ho. assert (Ho' : o = 12 \/ o = 13 \/ o = 14 \/ o = 15 \/ o = 16) by lia.
    destruct Ho' as [-> | [-> | [-> | [-> | ->]]]];
      (eapply s5a_rd_zero1;
       [apply (proj1 (Forall_forall _ _) RGc); cbn [In]; repeat (first [left; reflexivity | right]) | reflexivity]). }
  pose proof (regs_kept_of_st_ok_pi _ _ _ (ms_regs ms2) [Z_to_bv 64 (x_sh cx)]
    [2; 3; 4; 8; 9; 18; 20; 21; 22; 23; 24; 25; 26]%bv HS3 HAE3 ltac:(vm_compute; reflexivity)) as HKR3.
  cbn [ms_regs restrict] in HKR3.
  pose proof (st_ok_pi_restrict_reg (w_H W) E3 _ _ 10%bv HS3) as P10.
  lazymatch type of P10 with context [sr_get (ss_regs ?ssx) _] =>
    let e := eval vm_compute in (sr_get (ss_regs ssx) 10%bv) in change (sr_get (ss_regs ssx) 10%bv) with e in P10 end.
  cbn [ms_regs restrict] in P10.
  rewrite (s5a_sll56 E3 26 (seg_spec.seg_lb (x_pl cx) f)) in P10
    by (rewrite (EE3 26%nat 26%bv eq_refl), (HKR 26%bv ltac:(cbn; tauto)); exact R26).
  pmkst HS3.
  (* ---- the cut S5_LB ---- *)
  assert (KALL : forall a, 0 <= a < 2 ^ 64 -> ~ (t + n <= a < t + n + 1) -> ~ (x_sh cx + 12 <= a < x_sh cx + 17) ->
    rdW W (ms_mem ms) a = rdW W mem a).
  { intros a Ha H1 H2. rewrite (K3 a Ha H2), (K2 a Ha H1). exact (K1 a Ha H1). }
  assert (KT : forall a, 0 <= a < 2 ^ 64 -> ~ (t <= a < t + req_size (x_tn cx f)) -> ~ (x_s1 cx - 4096 <= a < x_s1 cx) ->
    ~ (x_sh cx + 12 <= a < x_sh cx + 17) -> rdW W (ms_mem ms) a = rdW W mem a).
  { intros a Ha H1 _ H3. apply KALL; [exact Ha | rewrite Htn, s5a_req in H1 by lia; lia | exact H3]. }
  pose proof (proj1 HJ) as HAR3.
  destruct (s5a_aux_keep cx ly S W mem md k t (x_tn cx f) c m (x_st cx f) (S5_slots cx c m f) (ms_mem ms)
    HB HJ0 HBL KT (s5a_slots_off cx c m f) HCM HSL) as (HCM3 & HSL3).
  apply (HK cx ly S W (ms_regs ms) (ms_mem ms) md3 k acc c m t HB HFRM Hf).
  + split; [|split; [|split; [|split]]].
    * apply (s5a_keep cx ly S W regs mem md k acc _ LFO0 LFO_L t (x_tn cx f) c m (ms_regs ms) (ms_mem ms) md3
        HB HC HJ ltac:(lia)).
      -- rewrite (HKR3 2%bv ltac:(cbn; tauto)), (HKR 2%bv ltac:(cbn; tauto)). reflexivity.
      -- rewrite (HKR3 3%bv ltac:(cbn; tauto)), (HKR 3%bv ltac:(cbn; tauto)). reflexivity.
      -- rewrite (HKR3 4%bv ltac:(cbn; tauto)), (HKR 4%bv ltac:(cbn; tauto)). reflexivity.
      -- rewrite (HKR3 8%bv ltac:(cbn; tauto)), (HKR 8%bv ltac:(cbn; tauto)). reflexivity.
      -- rewrite (HKR3 9%bv ltac:(cbn; tauto)), (HKR 9%bv ltac:(cbn; tauto)). reflexivity.
      -- exact KT.
      -- exact s5a_fsh_same.
      -- intros i Hi. rewrite s5a_fsh_L by exact Hi. apply W5. lia.
    * exact (s5a_hblk ly S W (ms_mem ms) md3 c _ HAR3 (proj1 HcB)).
    * exact (s5a_hblk ly S W (ms_mem ms) md3 m _ HAR3 (proj1 HmB)).
    * exact (s5a_hblk ly S W (ms_mem ms) md3 t _ HAR3 HtIn).
    * exact HCNT.
  + exact HCM3.
  + (* the text: the copied bytes, the NUL at t + n, the slack inside t's chunk *)
    split; [split|].
    * intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
      destruct (Nat.lt_ge_cases i (length (s5_txt (x_pl cx) f))) as [Hlt | Hge].
      -- rewrite app_nth1 by exact Hlt.
         rewrite KALL by (try apply NSH; lia). exact (HTX i Hlt).
      -- assert (Hi' : i = length (s5_txt (x_pl cx) f)) by lia. subst i.
         rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth]. rewrite <- HnL.
         rewrite (K3 (t + n) ltac:(lia) ltac:(apply NSH; lia)). exact HZ.
    * unfold s5_txt. rewrite (s5_txt_eq (x_pl cx) f Hf). apply s5_cut_nul_nulfree.
    * intros x Hx. rewrite <- HnL in Hx.
      apply (AR_block_word_vis SEGS B ly S W (ms_mem ms) md3 t (x_tn cx f) (t + n) x HAR3 HtIn);
        [rewrite Htn, s5a_req by lia; lia | lia].
  + exact P10.
  + rewrite (HKR3 18%bv ltac:(cbn; tauto)), (HKR 18%bv ltac:(cbn; tauto)). exact R18.
  + rewrite (HKR3 21%bv ltac:(cbn; tauto)), (HKR 21%bv ltac:(cbn; tauto)). exact R21.
  + rewrite (HKR3 22%bv ltac:(cbn; tauto)), (HKR 22%bv ltac:(cbn; tauto)). exact R22.
  + rewrite (HKR3 23%bv ltac:(cbn; tauto)), (HKR 23%bv ltac:(cbn; tauto)). exact R23.
  + rewrite (HKR3 24%bv ltac:(cbn; tauto)), (HKR 24%bv ltac:(cbn; tauto)). exact R24.
  + rewrite (HKR3 25%bv ltac:(cbn; tauto)), (HKR 25%bv ltac:(cbn; tauto)). exact R25.
  + rewrite (HKR3 26%bv ltac:(cbn; tauto)), (HKR 26%bv ltac:(cbn; tauto)). exact R26.
  + exact HSL3.
Qed.

(* ======================= S05, piece L1: 0x85210 .. 0x8526c (K85210 f -> S5_LB f) ======================= *)
Lemma s5_head : forall f, S5_LB_stmt B MT f -> LT_K85210_stmt B MT f.
Proof using All.
intros f HK. unfold LT_K85210_stmt.
intros cx ly S W regs mem md k acc c m t HB HFRM Hf HC HcB HmB Ht R10 R18 R19 R20 R21 R22 R24 R25 R26 HSL HCM HCNT.
set (n := seg_spec.seg_txt_n (x_pl cx) f) in *.
assert (Hn0 : 0 <= n) by (unfold n, seg_spec.seg_txt_n; lia).
assert (Htn : x_tn cx f = n + 1) by reflexivity.
assert (HnL : n = Z.of_nat (length (s5_txt (x_pl cx) f))) by reflexivity.
assert (HnL' : n = Z.of_nat (length (seg_spec.seg_txt (x_pl cx) f))) by reflexivity.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (s5a_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
unfold STK_LLVMFuzzerTestOneInput, LTOI_FRAME_MAX in Hsp0, Hs1lo.
pose proof HB as (HPRE0 & _ & _ & _ & _ & _ & Hpn & Hlen & _).
pose proof HPRE0 as (_ & _ & _ & Hgp0 & Htp0 & _).
pose proof HC as (HF & HI & HBL & HBUD).
pose proof HF as (HJ & Rsp & Rgp & Rtp & Rs0 & Rs1 & HSV & HH0 & HH8 & HH16 & HFL & H200 & HSH & H184).
pose proof (proj1 HJ) as HAR.
pose proof HJ as HJ0.
destruct (s5a_frame cx ly S W mem md k HB HJ) as (HinF & EF & F4096 & Fceil & Fapp & Esh & SHP).
pose proof Ht as (HtIn & Ht4096 & _ & _).
destruct (al_blocks _ _ LAWS ly S W mem md t (x_tn cx f) HAR HtIn) as (_ & _ & Htceil & Htapp & Htpres & _ & _).
rewrite Htn, s5a_req in Htceil, Htapp, Htpres by lia.
pose proof HBL as HBL0. unfold lt_blocks in HBL0. cbn [app] in HBL0.
assert (Htnot : ~ In (t, x_tn cx f) (x_bl0 B cx))
  by exact (s5a_notin ly S W mem md (t, x_tn cx f) [(m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] (x_bl0 B cx)
    HAR HBL0 ltac:(cbn [snd]; lia)).
assert (Hnpl : n <= x_n cx).
{ rewrite Hlen. unfold n, seg_spec.seg_txt_n. pose proof (s5a_txt_len (x_pl cx) f Hf). lia. }
assert (HN26 : x_n cx < 2 ^ 26) by (destruct Hpn as [[H0 _] | [Hn _]]; lia).
assert (NSH : forall a, t <= a < t + n + 1 -> ~ (x_sh cx + 12 <= a < x_sh cx + 17)).
{ intros a Ha Hw. apply (s5a_sh_not_app (x_fr cx) 64 t (n + 1) a); [lia | lia | exact Htapp | rewrite Esh in Hw; lia | lia]. }
(* ---- seed A at 0x85210 ---- *)
set (E := Eimg (Ereg regs [])).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall q (r : bv 5), Z.of_nat q = bv_unsigned r -> ew E q = getr regs r)
  by (intros q r Hq; subst E; apply ew_Eimg_Ereg_nat; exact Hq).
assert (HAE : env_agree 32 (Ereg regs []) E)
  by (split; [intros q Hq; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]).
assert (U10 : bv_unsigned (ew E 10) = t) by (rewrite (EE 10%nat 10%bv eq_refl), R10; apply unsigned_lit_small; lia).
assert (E20 : ew E 20 = Z_to_bv 64 n) by (rewrite (EE 20%nat 20%bv eq_refl); exact R20).
assert (HS : st_ok_pi SEGS VAL E s5a_ssA
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO_K85210)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - exact I.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U10.
    change (2 ^ 0) with 1. rewrite Z.mod_1_r. repeat split; lia. }
assert (SHOK : sh_ok SEGS s5a_x [] E (mrestrict (w_H W) mem)) by apply Forall_nil.
unfold cfg_at, w64.
(* 0x85210 .. 0x85214: `beqz a0` (the abort edge, decided by t >= 4096), s7 := t; it stops at `beqz s4` *)
paj_run_tok RUN HS HJ SHOK s5a_span.
{ apply awr_ok_nil. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md1 := d) in *; clearbody md1 end.
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms) a = rdW W mem a).
{ intros a Ha. apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun _ => False) HFr); [|exact Ha | intros []].
  intros b wlo whi a' Hin Hrr. vm_compute in Hin. destruct Hin. }
clear HF HFr HG.
rename ms into ms1.
psrr_branch_tok RUN BR HS SHOK s5a_span.
- (* n = 0: on to 0x8522c with no copy *)
  assert (Hn00 : n = 0).
  { rewrite branch_eq_U, (U_atom E 20 n E20 ltac:(lia)), U_SLit in Hc. apply Z.eqb_eq in Hc.
    change (zcanon 0) with 0 in Hc. exact Hc. }
  paj_run_to_tok RUNTO HS HJ SHOK s5a_span 0x46c.
  { apply awr_ok_nil. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md2 := d) in *; clearbody md2 end.
  assert (K2 : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms) a = rdW W mem a).
  { intros a Ha. rewrite <- (K1 a Ha).
    apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun _ => False) HFr); [|exact Ha | intros []].
    intros b wlo whi a' Hin Hrr. vm_compute in Hin. destruct Hin. }
  clear HF HFr HG.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs []
    [2; 3; 4; 8; 9; 18; 20; 21; 22; 24; 25; 26]%bv HS HAE ltac:(vm_compute; reflexivity)) as HKR.
  cbn [ms_regs restrict] in HKR.
  prreg HS (23%bv : bv 5) P23.
  pmkst HS.
  apply (s5a_tail f HK cx ly S W (ms_regs ms) (ms_mem ms) md2 k acc c m t HB HFRM Hf).
  + split; [|split; [|split; [|split]]].
    * apply (s5a_keep cx ly S W regs mem md k acc _ LFO0 LFO0 t (x_tn cx f) c m (ms_regs ms) (ms_mem ms) md2
        HB HC HJ ltac:(lia)).
      -- exact (HKR 2%bv ltac:(cbn; tauto)).
      -- exact (HKR 3%bv ltac:(cbn; tauto)).
      -- exact (HKR 4%bv ltac:(cbn; tauto)).
      -- exact (HKR 8%bv ltac:(cbn; tauto)).
      -- exact (HKR 9%bv ltac:(cbn; tauto)).
      -- intros a Ha _ _ _. exact (K2 a Ha).
      -- intros i _ _. reflexivity.
      -- intros i Hi. rewrite K2 by (rewrite Esh; lia). apply HSH. rewrite lt_fsh_len. lia.
    * exact (s5a_hblk ly S W (ms_mem ms) md2 c _ (proj1 HJ) (proj1 HcB)).
    * exact (s5a_hblk ly S W (ms_mem ms) md2 m _ (proj1 HJ) (proj1 HmB)).
    * exact (s5a_hblk ly S W (ms_mem ms) md2 t _ (proj1 HJ) HtIn).
    * exact HCNT.
  + exact (proj1 (s5a_aux_keep cx ly S W mem md k t (x_tn cx f) c m (x_st cx f) (S5_slots cx c m f) (ms_mem ms)
      HB HJ0 HBL (fun a Ha _ _ _ => K2 a Ha) (s5a_slots_off cx c m f) HCM HSL)).
  + intros i Hi. exfalso. lia.
  + rewrite (HKR 18%bv ltac:(cbn; tauto)). exact R18.
  + rewrite (HKR 20%bv ltac:(cbn; tauto)). exact R20.
  + rewrite (HKR 21%bv ltac:(cbn; tauto)). exact R21.
  + rewrite (HKR 22%bv ltac:(cbn; tauto)). exact R22.
  + rewrite P23, (EE 10%nat 10%bv eq_refl). exact R10.
  + rewrite (HKR 24%bv ltac:(cbn; tauto)). exact R24.
  + rewrite (HKR 25%bv ltac:(cbn; tauto)). exact R25.
  + rewrite (HKR 26%bv ltac:(cbn; tauto)). exact R26.
  + exact (proj2 (s5a_aux_keep cx ly S W mem md k t (x_tn cx f) c m (x_st cx f) (S5_slots cx c m f) (ms_mem ms)
      HB HJ0 HBL (fun a Ha _ _ _ => K2 a Ha) (s5a_slots_off cx c m f) HCM HSL)).
- (* n <> 0: a0 = t, a1 = P1, a2 = n, the jal of checked_memcpy (0x85228) *)
  assert (Hnz : n <> 0).
  { rewrite branch_eq_U, (U_atom E 20 n E20 ltac:(lia)), U_SLit in Hc. apply Z.eqb_neq in Hc.
    change (zcanon 0) with 0 in Hc. exact Hc. }
  assert (Hnpos : (0 < length (seg_spec.seg_txt (x_pl cx) f))%nat) by (unfold n, seg_spec.seg_txt_n in Hnz; lia).
  destruct (s5a_pay cx ly S W mem md k _ f 0 HB Hf HJ0 HBL Hnpos) as (HNp & HpIn & Hp0 & Hpat & Hpend & _).
  paj_run_tok RUN HS HJ SHOK s5a_span.
  { apply awr_ok_nil. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md2 := d) in *; clearbody md2 end.
  assert (K2 : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms) a = rdW W mem a).
  { intros a Ha. rewrite <- (K1 a Ha).
    apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun _ => False) HFr); [|exact Ha | intros []].
    intros b wlo whi a' Hin Hrr. vm_compute in Hin. destruct Hin. }
  clear HF HFr HG.
  assert (KR : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 20; 21; 22; 24; 25; 26]%bv -> getr (ms_regs ms) r = getr regs r).
  { intros r Hr. cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr];
      [ let P := fresh "P" in lazymatch goal with |- getr _ ?rr = _ => prreg HS rr P end;
        rewrite P; apply EE; reflexivity | ]).
    destruct Hr. }
  prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
  prreg HS (12%bv : bv 5) P12. prreg HS (23%bv : bv 5) P23.
  pmkst HS.
  pose proof (proj1 HJ) as HAR1.
  destruct (al_blocks _ _ LAWS ly S W (ms_mem ms) md2 (x_p cx) (x_n cx) HAR1 HpIn) as (_ & Hp4096 & Hpceil & _ & Hppres & _ & _).
  rewrite s5a_req in Hpceil, Hppres by lia.
  pose proof (s5a_sep ly S W (ms_mem ms) md2 (t, x_tn cx f) _ (x_p cx, x_n cx) HAR1 HBL0
    ltac:(right; right; exact Hp0)) as Dtp.
  unfold zdisjoint, block_rng in Dtp. cbn [fst snd] in Dtp. rewrite Htn, !s5a_req in Dtp by lia.
  assert (Hes : ESTACK = 4096) by reflexivity.
  assert (HspT : spZ (ms_regs ms) = x_sp0 cx + (x_s1 cx - x_sp0 cx)).
  { unfold spZ. rewrite (KR 2%bv ltac:(cbn; tauto)), Rsp. unfold w64. rewrite unsigned_lit_small by lia. lia. }
  assert (P10' : getr (ms_regs ms) 10 = w64 t) by (rewrite P10, (EE 10%nat 10%bv eq_refl); exact R10).
  assert (P11' : getr (ms_regs ms) 11 = w64 (x_at cx f)) by (rewrite P11, (EE 19%nat 19%bv eq_refl); exact R19).
  assert (P12' : getr (ms_regs ms) 12 = w64 n) by (rewrite P12, (EE 20%nat 20%bv eq_refl); exact R20).
  assert (P3' : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite (KR 3%bv ltac:(cbn; tauto)), Rgp; exact Hgp0).
  assert (P4' : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite (KR 4%bv ltac:(cbn; tauto)), Rtp; exact Htp0).
  assert (HraT : YK0s.ret_ok (Z_to_bv 64 (BASE + 1132))) by (apply ret_ok_codeptr_v; [lia | reflexivity]).
  eapply SRr_bind.
  { apply (aj_intrin_atS SEGS B LAWS pa_segs_low OCpy (SIG SS___asan_memcpy) (AMEMCPY fx) W (ms_regs ms) (ms_mem ms)
      STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx)
      [(LT_FCLS, x_fpos cx)] ly S md2 k t (x_at cx f) n (x_s1 cx - x_sp0 cx) (Z_to_bv 64 (BASE + 1132))
      HJ P10' P11' P12' ltac:(lia) ltac:(lia) ltac:(lia) HspT ltac:(lia) ltac:(lia)
      ltac:(rewrite Hes; unfold STK_LLVMFuzzerTestOneInput; lia) P3' P4' P1 HraT).
    - intros a Ha. split.
      + right; right; left. exists t, (x_tn cx f).
        split; [exact HtIn | split; [exact Htnot | rewrite Htn, s5a_req by lia; lia]].
      + rewrite Hes. lia.
    - intros a Ha Hfp. exfalso. destruct (HPGS a Hfp) as [_ Himg].
      exact (blk_img SEGS B LAWS ly S W (ms_mem ms) md2 t (x_tn cx f) a HAR1 HtIn
        ltac:(rewrite Htn, s5a_req by lia; lia) Himg).
    - exact (amem_range_of_block SEGS B LAWS ly S W (ms_mem ms) md2 t (x_tn cx f) t n HAR1 HtIn
        ltac:(lia) ltac:(rewrite Htn, s5a_req by lia; lia)).
    - exact (range_addressable_of_block SEGS B LAWS ly S W (ms_mem ms) md2 t (x_tn cx f) t n HAR1 HtIn
        ltac:(lia) ltac:(rewrite Htn, s5a_req by lia; lia)).
    - intros Hpos. exact (shadow_hull_vis_of_block SEGS B LAWS ly S W (ms_mem ms) md2 t (x_tn cx f) t n HAR1 HtIn
        ltac:(lia) ltac:(rewrite Htn, s5a_req by lia; lia) Hpos).
    - split; [lia|]. split; [lia|]. split.
      { intros a Ha. split.
        - apply (aview_some_of_apresent SEGS). exact (proj1 (Hppres a ltac:(lia))).
        - rewrite HspT, Hes. lia. }
      split; [lia|].
      split; [exact (amem_range_of_block SEGS B LAWS ly S W (ms_mem ms) md2 (x_p cx) (x_n cx) (x_at cx f) n HAR1 HpIn
                ltac:(lia) ltac:(rewrite s5a_req by lia; lia))|].
      split; [exact (range_addressable_of_block SEGS B LAWS ly S W (ms_mem ms) md2 (x_p cx) (x_n cx) (x_at cx f) n
                HAR1 HpIn ltac:(lia) ltac:(rewrite s5a_req by lia; lia))|].
      intros Hpos. exact (shadow_hull_vis_of_block SEGS B LAWS ly S W (ms_mem ms) md2 (x_p cx) (x_n cx) (x_at cx f) n
        HAR1 HpIn ltac:(lia) ltac:(rewrite s5a_req by lia; lia) Hpos). }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md3 & -> & HJ2 & HP2 & H10b & HCPY & HKC & HPRS & HSAME).
  cbv iota in HCPY.
  replace (x_sp0 cx + (x_s1 cx - x_sp0 cx)) with (x_s1 cx) in HKC by ring.
  assert (PR : forall (r : bv 5) z, acallee_saved z -> Z_to_bv 5 z = r -> getr regs2 r = getr (ms_regs ms) r)
    by (intros r z Hz Hr; exact (s5a_pres_reg _ _ r z HP2 Hz Hr)).
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (t <= a < t + req_size (x_tn cx f)) -> ~ (x_s1 cx - 4096 <= a < x_s1 cx) ->
    rdW W mem2 a = rdW W mem a).
  { intros a Ha H1 H2. rewrite Htn, s5a_req in H1 by lia.
    rewrite (HKC a Ha ltac:(lia) ltac:(rewrite Hes; lia)). exact (K2 a Ha). }
  change (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + 1132)) mem2 (seg_rom SEGS)) md3)
    with (cfg_at SEGS (BASE + 0x46c) regs2 mem2 md3).
  apply (s5a_tail f HK cx ly S W regs2 mem2 md3 k acc c m t HB HFRM Hf).
  + split; [|split; [|split; [|split]]].
    * apply (s5a_keep cx ly S W regs mem md k acc _ LFO0 LFO0 t (x_tn cx f) c m regs2 mem2 md3 HB HC HJ2 ltac:(lia)).
      -- rewrite (PR 2%bv 2 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
         exact (KR 2%bv ltac:(cbn; tauto)).
      -- rewrite (PR 3%bv 3 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
         exact (KR 3%bv ltac:(cbn; tauto)).
      -- rewrite (PR 4%bv 4 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
         exact (KR 4%bv ltac:(cbn; tauto)).
      -- rewrite (PR 8%bv 8 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
         exact (KR 8%bv ltac:(cbn; tauto)).
      -- rewrite (PR 9%bv 9 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
         exact (KR 9%bv ltac:(cbn; tauto)).
      -- intros a Ha H1 H2 _. exact (KM a Ha H1 H2).
      -- intros i _ _. reflexivity.
      -- intros i Hi. rewrite (KM (x_sh cx + Z.of_nat i)).
         ++ apply HSH. rewrite lt_fsh_len. lia.
         ++ rewrite Esh. lia.
         ++ rewrite Htn, s5a_req by lia. intros Hq. apply (NSH (x_sh cx + Z.of_nat i) ltac:(lia)). lia.
         ++ rewrite Esh. lia.
    * exact (s5a_hblk ly S W mem2 md3 c _ (proj1 HJ2) (proj1 HcB)).
    * exact (s5a_hblk ly S W mem2 md3 m _ (proj1 HJ2) (proj1 HmB)).
    * exact (s5a_hblk ly S W mem2 md3 t _ (proj1 HJ2) HtIn).
    * exact HCNT.
  + exact (proj1 (s5a_aux_keep cx ly S W mem md k t (x_tn cx f) c m (x_st cx f) (S5_slots cx c m f) mem2
      HB HJ0 HBL (fun a Ha H1 H2 _ => KM a Ha H1 H2) (s5a_slots_off cx c m f) HCM HSL)).
  + intros i Hi.
    rewrite HCPY by lia. rewrite K2 by lia.
    exact (proj2 (proj2 (proj2 (proj2 (proj2 (s5a_pay cx ly S W mem md k _ f i HB Hf HJ0 HBL Hi)))))).
  + rewrite (PR 18%bv 18 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)),
      (KR 18%bv ltac:(cbn; tauto)). exact R18.
  + rewrite (PR 20%bv 20 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)),
      (KR 20%bv ltac:(cbn; tauto)). exact R20.
  + rewrite (PR 21%bv 21 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)),
      (KR 21%bv ltac:(cbn; tauto)). exact R21.
  + rewrite (PR 22%bv 22 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)),
      (KR 22%bv ltac:(cbn; tauto)). exact R22.
  + rewrite (PR 23%bv 23 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)),
      P23, (EE 10%nat 10%bv eq_refl). exact R10.
  + rewrite (PR 24%bv 24 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)),
      (KR 24%bv ltac:(cbn; tauto)). exact R24.
  + rewrite (PR 25%bv 25 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)),
      (KR 25%bv ltac:(cbn; tauto)). exact R25.
  + rewrite (PR 26%bv 26 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)),
      (KR 26%bv ltac:(cbn; tauto)). exact R26.
  + exact (proj2 (s5a_aux_keep cx ly S W mem md k t (x_tn cx f) c m (x_st cx f) (S5_slots cx c m f) mem2
      HB HJ0 HBL (fun a Ha H1 H2 _ => KM a Ha H1 H2) (s5a_slots_off cx c m f) HCM HSL)).
Qed.

End ea.
End fa.
End da.

(* ============================================== piece L2 (b) ============================================== *)
(* ======================================================================================================
   reac-pw/fuzz_segconf, ASan+UBSan image B (fuzz_segconf.asan-ubsan, pin sha256 c3796c0b38f3): segment S05 piece L2,
   s5_label: 0x8526c .. 0x852c8 / 0x85324 of the test harness's entry function LLVMFuzzerTestOneInput.
   The kit's S5_LB f (lib/B/Prog/LLVMFuzzerTestOneInput_s15k.v) to S5_OTH f / S5_LST f, taken at every FP state:
     0x8526c bltz a0 (a0 = lb << 56)   bit 7 of lb: the longl arm 0x85294 .. 0x852ac,
                                       checked_memset(longl, 'L', 120) (PaCall.aj_intrin_atS, AMEMSET)
     0x85270 beqz s10 (s10 = lb)       lb = 0: s3 := 0 at 0x852b0
     0x85274 .. 0x8528c                else snprintf(label, 40, "reac-pw.conf.d/%u-x.conf", lb) into the class-3
                                       frame's label[40] (row 4, RtPFSeg.seg_asnprintf_realizes, ASNPRINTF), the
                                       FP state it returns at (PaFx.srr_after_artF)
     0x852b4 .. 0x852c0                the join: s9 := f + 1, s10 := (m + 0x2000) >> 3 from 216(s1), bgeu s9,s2
     0x852c4                           a0 := m, to S5_OTH at 0x852c8; or, the last turn, S5_LST at 0x85324.
   Each arm ends with the kit's S5_label for the pointer it leaves in s3.
   THE FORM: image A's S01 / S02 walk (seeds, paj_run_tok, prreg; its kit's lk_hblk / lk_core_run / lk_img_kept, here
   s5b_hblk / s5b_kept / s5b_img_kept with longl[0 .. 120) as the one image range a call may change), fuzz_command's
   PaRt.v cwc_aj_snprintf_atSF (origin/ossv/recipes 3abc3740de97) restated at this call as s5b_snp_call, its
   RtPFDog.v pa_dest_off_globals_frame as s5b_frame's kImgEnd / snp_hi <= FR.
   Code: dis/LLVMFuzzerTestOneInput.fuzz_segconf.asan-ubsan.s lines 301-323 and 347 (SegList.v slots 299-321 and 345,
   lines 350-372 and 396; slot k is line 51 + k). *)
(* the token runner's shadow base (no instrumented check in this piece) and band *)
Definition s5b_X : sv := SLit SHADOW_OFF.
Definition s5b_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* a read-only region at the s1 atom (atom 9) holding one 8-byte word, atom 32, at offset off *)
Definition s5b_rg (off : Z) : smem :=
  [YP09.mkRegion (Some 9%nat) off (off + 8) off off [YP09.mkChunk off (CVal 8 (SOff 32 0))]].
Definition s5b_ss (pc off : Z) (G : facts) : sstate := mkSS pc sr_atoms (s5b_rg off) None G.

(* two readers that agree on a word's bytes agree on the word *)
Lemma s5b_word_kept : forall (rd rd' : reader) a v,
  (forall x, a <= x < a + 8 -> rd' x = rd x) -> rdword rd a = Some v -> rdword rd' a = Some v.
Proof. intros rd rd' a v HK H. rewrite (rdword_ext rd rd' a); [exact H|]. intros k Hk. apply HK. lia. Qed.
(* a word all 8 bytes of which a reader shows *)
Lemma s5b_rdword_some : forall (rd : reader) a, (forall k, 0 <= k < 8 -> rd (a + k) <> None) ->
  exists v, rdword rd a = Some v.
Proof.
intros rd a H. unfold rdword.
pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
pose proof (H 1 ltac:(lia)) as H1. pose proof (H 2 ltac:(lia)) as H2. pose proof (H 3 ltac:(lia)) as H3.
pose proof (H 4 ltac:(lia)) as H4. pose proof (H 5 ltac:(lia)) as H5. pose proof (H 6 ltac:(lia)) as H6.
pose proof (H 7 ltac:(lia)) as H7.
destruct (rd a) as [b0|]; [|congruence]. destruct (rd (a + 1)) as [b1|]; [|congruence].
destruct (rd (a + 2)) as [b2|]; [|congruence]. destruct (rd (a + 3)) as [b3|]; [|congruence].
destruct (rd (a + 4)) as [b4|]; [|congruence]. destruct (rd (a + 5)) as [b5|]; [|congruence].
destruct (rd (a + 6)) as [b6|]; [|congruence]. destruct (rd (a + 7)) as [b7|]; [|congruence].
eexists; reflexivity.
Qed.
(* a callee-saved register a call keeps *)
Lemma s5b_pres_reg : forall regs regs' (r : bv 5) z,
  aregs_preserved regs regs' -> acallee_saved z -> Z_to_bv 5 z = r -> getr regs' r = getr regs r.
Proof. intros regs regs' r z HP Hz <-. exact (HP z Hz). Qed.
(* nfiles is 1 + in[2] % 4 *)
Lemma s5b_nf_range : forall pl, 1 <= seg_spec.seg_nfiles pl <= 4.
Proof.
intros pl. unfold seg_spec.seg_nfiles, seg_spec.seg_files, seg_spec.seg_pay, SegModel.decode.
destruct (SegModel.fuzz_u8 (seg_spec.seg_in pl)) as [b0 i1].
destruct (SegModel.fuzz_u8 i1) as [fl i2]. destruct (SegModel.fuzz_u8 i2) as [b2 i3].
cbn [SegModel.p_files]. rewrite s5_dec_files_length.
pose proof (Z.mod_pos_bound b2 4 ltac:(lia)) as H. rewrite Z2Nat.id by lia. lia.
Qed.
(* the label byte is a byte of the input *)
Lemma s5b_sfx_forall : forall (P : Z -> Prop) a b, s5_sfx a b -> Forall P b -> Forall P a.
Proof.
intros P a b (j & _ & ->) H. revert b H. induction j as [|j IH]; intros b H; [exact H|].
destruct b as [|x b]; [exact H|]. cbn [skipn]. apply IH. inversion H; assumption.
Qed.
Lemma s5b_lb_range : forall pl f, Z.of_nat f < seg_spec.seg_nfiles pl -> 0 <= seg_spec.seg_lb pl f < 256.
Proof.
intros pl f Hf. rewrite (s5_lb_eq pl f Hf).
assert (HS : s5_sfx (seg_spec.seg_cur pl f) (seg_spec.seg_in pl)).
{ unfold seg_spec.seg_cur.
  apply (s5_sfx_trans _ (seg_spec.seg_hdr pl)); [apply s5_skip_sfx|].
  unfold seg_spec.seg_hdr.
  apply (s5_sfx_trans _ (snd (SegModel.fuzz_u8 (snd (SegModel.fuzz_u8 (seg_spec.seg_in pl)))))); [apply s5_u8_sfx|].
  apply (s5_sfx_trans _ (snd (SegModel.fuzz_u8 (seg_spec.seg_in pl)))); [apply s5_u8_sfx | apply s5_u8_sfx]. }
assert (HF : Forall (fun z => 0 <= z < 256) (seg_spec.seg_in pl)).
{ unfold seg_spec.seg_in, seg_spec.zs. rewrite Forall_map. apply Forall_forall. intros b _.
  pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R. lia. }
pose proof (s5b_sfx_forall _ _ _ HS HF) as HC.
destruct (seg_spec.seg_cur pl f) as [|z l]; cbn [SegModel.fuzz_u8 fst]; [lia|]. inversion HC; assumption.
Qed.
(* the bltz at 0x8526c on a0 = lb << 56: taken iff lb has bit 7, for every byte lb (checked on the 256 bytes) *)
Definition s5b_bltz_b (z : Z) : bool :=
  Bool.eqb (branch_taken BC_LT (Z_to_bv 64 (Z.shiftl z 56)) (Z_to_bv 64 0)) (negb (Z.land z 128 =? 0)).
Lemma s5b_bltz_all : forallb s5b_bltz_b (map Z.of_nat (seq 0 256)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma s5b_bltz : forall z, 0 <= z < 256 ->
  branch_taken BC_LT (Z_to_bv 64 (Z.shiftl z 56)) (Z_to_bv 64 0) = negb (Z.land z 128 =? 0).
Proof.
intros z Hz. pose proof (proj1 (forallb_forall _ _) s5b_bltz_all z) as H.
assert (Hin : In z (map Z.of_nat (seq 0 256))).
{ apply in_map_iff. exists (Z.to_nat z). split; [lia|]. apply in_seq. lia. }
specialize (H Hin). unfold s5b_bltz_b in H. apply Bool.eqb_prop in H. exact H.
Qed.
(* the label format's pieces (row 4's grammar, RtPFSeg.seg_parse) *)
Definition s5b_qs : list RtPFSeg.seg_piece :=
  match RtPFSeg.seg_parse LLVMFuzzerTestOneInput_c.LIT_LABEL with Some q => q | None => [] end.
Lemma s5b_parse : RtPFSeg.seg_parse LLVMFuzzerTestOneInput_c.LIT_LABEL = Some s5b_qs.
Proof. vm_compute. reflexivity. Qed.
Lemma s5b_qs_pk : Forall RtPFSeg.seg_pk s5b_qs.
Proof. apply Forall_forall. intros q _. destruct q; exact I. Qed.
(* THE GLUE: row 4's text of the label format at AInt lb is SegModel's, for 1 <= lb <= 127 (checked on each of
   the 127 values, the digits of lb exposed); shorter than 39 bytes, so snprintf(label, 40, ...) writes it whole,
   and every byte of it in 1 .. 255 *)
Definition s5b_glue_b (z : Z) : bool :=
  match RtPFSeg.seg_text s5b_qs [RtPFPf.AInt z] with
  | Some T =>
      (if list_eq_dec Z.eq_dec T (SegModel.fmt SegModel.F_label [SegModel.AI z]) then true else false) &&
      Nat.ltb (length T) 39 && forallb (fun b => (0 <? b) && (b <? 256)) T
  | None => false
  end.
Lemma s5b_glue_all : forallb s5b_glue_b (map Z.of_nat (seq 1 127)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma s5b_glue : forall lb, 1 <= lb <= 127 ->
  RtPFSeg.seg_text s5b_qs [RtPFPf.AInt lb] = Some (SegModel.fmt SegModel.F_label [SegModel.AI lb]) /\
  (length (SegModel.fmt SegModel.F_label [SegModel.AI lb]) < 39)%nat /\
  Forall (fun b => 0 < b < 256) (SegModel.fmt SegModel.F_label [SegModel.AI lb]).
Proof.
intros lb Hlb. pose proof (proj1 (forallb_forall _ _) s5b_glue_all lb) as H.
assert (Hin : In lb (map Z.of_nat (seq 1 127))).
{ apply in_map_iff. exists (Z.to_nat lb). split; [lia|]. apply in_seq. lia. }
specialize (H Hin). unfold s5b_glue_b in H.
destruct (RtPFSeg.seg_text s5b_qs [RtPFPf.AInt lb]) as [T|]; [|discriminate H].
destruct (list_eq_dec Z.eq_dec T (SegModel.fmt SegModel.F_label [SegModel.AI lb])) as [<-|]; [|discriminate H].
apply andb_prop in H as [H H3]. apply andb_prop in H as [_ H2].
split; [reflexivity|]. split; [apply Nat.ltb_lt; exact H2|].
apply Forall_forall. intros b Hb. rewrite forallb_forall in H3. specialize (H3 b Hb).
apply andb_prop in H3 as [Ha Hb']. apply Z.ltb_lt in Ha. apply Z.ltb_lt in Hb'. lia.
Qed.
(* the model's label in the snprintf arm is that text *)
Lemma s5b_snprintf_s : forall lb, 1 <= lb <= 127 ->
  SegModel.snprintf_s 40 SegModel.F_label [SegModel.AI lb] = SegModel.fmt SegModel.F_label [SegModel.AI lb].
Proof.
intros lb Hlb. destruct (s5b_glue lb Hlb) as (_ & Hl & _). unfold SegModel.snprintf_s.
apply firstn_all2. change (Z.to_nat (40 - 1)) with 39%nat. lia.
Qed.

(* the catalogue's tokens and m_key's role words: each a short literal (checked on each) *)
Lemma s5b_tok_len : forall i, (i < pin_spec.CAT_N)%nat -> Z.of_nat (length (seg_spec.zs (pin_spec.tok_bytes i))) < 65535.
Proof.
intros i Hi. change pin_spec.CAT_N with 11%nat in Hi.
do 11 (destruct i as [|i]; [apply Z.ltb_lt; vm_compute; reflexivity|]). lia.
Qed.
Lemma s5b_word_len : forall i, (i < 5)%nat -> Z.of_nat (length (nth i m_file_c.MF_ROLE_WORDS [])) < 65535.
Proof.
intros i Hi. do 5 (destruct i as [|i]; [apply Z.ltb_lt; vm_compute; reflexivity|]). lia.
Qed.
(* a range apart from longl's 121 bytes is apart from its 120 written bytes *)
Lemma s5b_apart : forall a n, sa_apart_all a n (ltoi_PG longlA) -> a + n <= longlA \/ longlA + LONGL_W <= a.
Proof. intros a n H. apply Forall_inv in H. cbn [fst snd] in H. unfold LONGL_N, LONGL_W in *. lia. Qed.

(* a byte without bit 7 is below 128 (checked on the 256 bytes) *)
Definition s5b_land_b (z : Z) : bool := implb (Z.land z 128 =? 0) (z <? 128).
Lemma s5b_land_all : forallb s5b_land_b (map Z.of_nat (seq 0 256)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma s5b_land128 : forall z, 0 <= z < 256 -> Z.land z 128 = 0 -> z < 128.
Proof.
intros z Hz H0. pose proof (proj1 (forallb_forall _ _) s5b_land_all z) as H.
assert (Hin : In z (map Z.of_nat (seq 0 256))).
{ apply in_map_iff. exists (Z.to_nat z). split; [lia|]. apply in_seq. lia. }
specialize (H Hin). unfold s5b_land_b in H. rewrite H0 in H. cbn [Z.eqb implb] in H. apply Z.ltb_lt in H. exact H.
Qed.
Lemma s5b_nth_repeat : forall (x d : Z) n i, (i < n)%nat -> nth i (repeat x n) d = x.
Proof.
intros x d n. induction n as [|n IH]; intros i Hi; [lia|].
destruct i as [|i]; [reflexivity|]. cbn [repeat nth]. apply IH. lia.
Qed.
(* label[40]'s shadow bytes: 12 .. 16 of the frame's 36 (lt_fsh LFO_L) are 0 *)
Lemma s5b_fsh_label : forall j, 12 <= j < 17 -> nth (Z.to_nat j) (lt_fsh LFO_L) 0 = 0.
Proof.
intros j Hj. assert (Hc : j = 12 \/ j = 13 \/ j = 14 \/ j = 15 \/ j = 16) by lia.
destruct Hc as [-> | [-> | [-> | [-> | ->]]]]; reflexivity.
Qed.
Lemma s5b_label_shadow : forall (rd : reader) fr x, sa_zs rd (shadow_addr fr) (lt_fsh LFO_L) -> fr mod 8 = 0 -> 0 <= fr ->
  fr + 96 <= x < fr + 136 -> rd (shadow_of_addr SHADOW_OFF x) = Some 0.
Proof.
intros rd fr x HZ Hfr Hfr0 Hx.
assert (Hj : 12 <= x / 8 - fr / 8 < 17) by lia.
pose proof (HZ (Z.to_nat (x / 8 - fr / 8)) ltac:(rewrite lt_fsh_len; lia)) as H.
rewrite Z2Nat.id in H by lia. rewrite (s5b_fsh_label _ Hj) in H.
unfold shadow_of_addr. unfold shadow_addr in H. replace (SHADOW_OFF + x / 8) with (SHADOW_OFF + fr / 8 + (x / 8 - fr / 8)) by lia.
exact H.
Qed.
Lemma s5b_label_hull : forall (rd : reader) fr q n, sa_zs rd (shadow_addr fr) (lt_fsh LFO_L) -> fr mod 32 = 0 -> 0 <= fr ->
  fr + 96 <= q -> q + n <= fr + 136 -> 0 < n -> shadow_hull_vis rd q n.
Proof.
intros rd fr q n HZ Hfr Hfr0 Hq1 Hq2 Hn s Hs. unfold shadow_addr, SHADOW_OFF in *.
assert (Hi : 0 <= s - (2147450880 + fr / 8) < 36) by lia.
pose proof (HZ (Z.to_nat (s - (2147450880 + fr / 8))) ltac:(rewrite lt_fsh_len; lia)) as H.
rewrite Z2Nat.id in H by lia. replace (2147450880 + fr / 8 + (s - (2147450880 + fr / 8))) with s in H by lia.
rewrite H. discriminate.
Qed.

Section db. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section fb.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section eb.
Variable B : asyms.
Variable MT : ameter_ops.
(* the image range the snprintf row's dest_off_globals uses, and the read-only ranges it reads; the S11 walk
   (the probe snprintf) takes the same three names and the same five HSNP_ hypotheses *)
Variable snp_lo snp_hi : Z.
Variable snp_cr : list (Z * Z).
(* AR's laws are a theorem of image B's kit, not a hypothesis *)
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis PRW : prog_rw SEGS B.
Hypothesis VOBJS : seg_val_objs.
Hypothesis SIGP : seg_sig_prog.
(* image B's per-image record (lib/B/Prog/SegRecBase.v, the image-B listing owner's commit c4abdaee306f, merged into
   this walk's integration commit da997fa1859d): the image facts lt_img needs at a reader after a call, each a field.
   It SUPERSEDES the three hypotheses IMG_RELRO / IMG_GOTW / IMG_GUARD an earlier version of this brief had.
   Never weaken lt_img instead. *)
Hypothesis IMGF : seg_img_facts SEGS B.
(* the allocator record's symbols at image B's values (lib/B/YF0m.v): with AR it gives the stack-protector
   cells at every state (SegRecCells.seg_rec_cells), since the runtime owns the .got word gotwA *)
Hypothesis HBS : YF0m.SegBSyms B.
(* longl's bytes are the program's own writable static, in the image and outside RELRO (the memset arm writes
   them), and no model-table pointer reaches within 65536 of longl (image A's S05 header takes the same
   three; they are what the longl arm and the literals' survival need) *)
Hypothesis HPGS : forall a, inFP (ltoi_PG longlA) a ->
  Exists (in_zr a) (as_prog_static B) /\ in_img SEGS a.
Hypothesis HPG_RO : forall a, inFP (ltoi_PG longlA) a -> ~ in_roP SEGS RLO_A RHI_A a.
Hypothesis HPG_PTR : forall a p,
  ((exists i, (i < 5)%nat /\ a = wordsA + 8 * Z.of_nat i) \/
   (exists i, (i < pin_spec.CAT_N)%nat /\ a = pin_spec.row_addr catA i)) ->
  rdword (fun x => option_map (fun b : byte => bv_unsigned b) (seg_rom SEGS (Z_to_bv 64 x))) a = Some p ->
  p + 65536 <= longlA.
(* the runtime entries S05 calls *)
Hypothesis AMEMCPY : forall fx0 : YK11.FPState, aintrin_realizes (fx := fx0) SEGS B OCpy (SIG SS___asan_memcpy).
Hypothesis AMEMSET : forall fx0 : YK11.FPState, aintrin_realizes (fx := fx0) SEGS B OSet (SIG SS___asan_memset).
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState,
  RtPFSeg.seg_asnprintf_realizes (fx := fx0) SEGS B snp_lo snp_hi snp_cr
    (SIG SS___interceptor_trampoline_snprintf) gotwA guardA.
Hypothesis AFREE4 : forall fx0 : YK11.FPState, afree04_rule (fx := fx0) SEGS B MT.
(* what image B's close shows of snp_lo / snp_hi / snp_cr; each is a computation there *)
Hypothesis HSNP_LIT : forall x, In x LLVMFuzzerTestOneInput_c.LTOI_LITS ->
  snp_lo <= seg_litA_fz x /\ seg_litA_fz x + Z.of_nat (length x) + 1 <= gotwA.
Hypothesis HSNP_CR : Forall (fun r => snp_lo <= fst r /\ 0 <= snd r /\ fst r + snd r <= snp_hi) snp_cr.
Hypothesis HSNP_LO : 0 <= snp_lo.
Hypothesis HSNP_CEIL : snp_hi <= alloc_ceiling.
Hypothesis HSNP_FAKE : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> snp_hi <= ly_F ly.
(* the two program callees, at every FP state *)
Hypothesis HM_FILE : forall fx0 : YK11.FPState,
  m_file_c.m_file_contract (fx := fx0) SEGS B (BASE + AF_m_file) STK_m_file RLO_A RHI_A seg_litA_fz
    wordsA rolesA catA gotwA guardA.
Hypothesis HPARSE_FILE : forall fx0 : YK11.FPState,
  reac_segconf_parse_file_c.reac_segconf_parse_file_contract (fx := fx0) SEGS B
    (BASE + AF_reac_segconf_parse_file) STK_reac_segconf_parse_file RLO_A RHI_A seg_litA_rc catA gotwA guardA.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* the three image facts lt_img needs at a reader after a call, each from a field of IMGF (image A's S00 walk
   takes the same three as its record s10_img); this text compiled on the VM, log build-20261030T183150Z.log.
   Rename `s5b_` to `s5b_` in your file. *)
Lemma s5b_relro : forall a, RLO_A <= a < RHI_A -> in_img SEGS a.
Proof. exact (cif_relro_img _ _ IMGF). Qed.


(* ======================================== segment S05 piece L2 ======================================== *)
Definition s5b_E (regs : bvmap 5 word) (extra : list word) : env := Eimg (Ereg regs extra).
Lemma s5b_E_reg : forall regs extra n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (s5b_E regs extra) n = getr regs r.
Proof using All.
intros regs extra n r H. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
unfold s5b_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact H.
Qed.
Lemma s5b_E_32 : forall regs v rest, ew (s5b_E regs (v :: rest)) 32 = v.
Proof using All.
intros regs v rest. unfold s5b_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs (v :: rest) 0).
Qed.
(* the seed: every register its own atom, the word at s1 + off as atom 32, the facts G, at any FP state *)
Lemma s5b_seed : forall (fx1 : YK11.FPState) pc off G (W : world SEGS) (regs : bvmap 5 word) mem s1 v,
  regions_wf (s5b_rg off) = true -> facts_ok (s5b_E regs [Z_to_bv 64 v]) G ->
  getr regs 9 = w64 s1 -> 0 <= s1 -> 0 <= off -> s1 + off + 8 <= 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
  rdword (rdW W mem) (s1 + off) = Some v ->
  st_ok_pi (fx := fx1) SEGS VAL (s5b_E regs [Z_to_bv 64 v]) (s5b_ss pc off G)
    (restrict (w_H W) (@mkst fx1 regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof using All.
intros fx1 pc off G W regs mem s1 v Hwf HG R9 H1 H2 H3 Hv Wv.
assert (E9 : ew (s5b_E regs [Z_to_bv 64 v]) 9 = Z_to_bv 64 s1)
  by (rewrite (s5b_E_reg regs _ 9 9%bv eq_refl); exact R9).
pose proof (s5b_E_32 regs (Z_to_bv 64 v) []) as E32.
unfold s5b_ss. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- unfold s5b_E. apply regs_ok_Eimg_Ereg.
- exact Hwf.
- unfold s5b_rg. constructor; [|constructor]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E9, unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS _ _ s1 off 8 (SOff 32 0) v);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | change (8 * Z.of_N 8) with 64; lia | cbn; lia | exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Wv)].
- unfold s5b_rg. cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- exact HG.
Qed.
(* an atom's value, a literal's value *)
Lemma s5b_denot_atom : forall E n (v : word), ew E n = v -> sv_denot E (SOff n 0) = v.
Proof using All. intros E n v H. cbn [sv_denot]. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.
Lemma s5b_denot_U : forall E e v, U E e = v -> sv_denot E e = Z_to_bv 64 v.
Proof using All. intros E e v H. unfold U in H. rewrite <- H. symmetry. apply Z_to_bv_bv_unsigned. Qed.

(* a reader reads its address mod 2 ^ 64, so agreement on [0, 2 ^ 64) is agreement everywhere *)
Lemma s5b_rd_mod : forall (H : word -> bool) mem a, aview SEGS H mem a = aview SEGS H mem (a mod 2 ^ 64).
Proof using All.
intros H mem a. unfold aview, mbyte.
replace (Z_to_bv 64 (a mod 2 ^ 64)) with (Z_to_bv 64 a); [reflexivity|].
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma s5b_full : forall (W : world SEGS) mem mem',
  (forall a, 0 <= a < 2 ^ 64 -> rdW W mem' a = rdW W mem a) -> forall a, rdW W mem' a = rdW W mem a.
Proof using All.
intros W mem mem' HK a. rewrite (s5b_rd_mod (w_H W) mem' a), (s5b_rd_mod (w_H W) mem a).
apply HK. apply Z.mod_pos_bound. lia.
Qed.
(* a run whose regions have no write window keeps every byte *)
Lemma s5b_nowin_kept : forall E (rs : smem) (W : world SEGS) (m m' : word -> option byte),
  frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true ->
  forall a, rdW W m' a = rdW W m a.
Proof using All.
intros E rs W m m' HF Hro. apply s5b_full. intros a Ha.
apply (kept_of_frame (segs:=SEGS) E rs (w_H W) m m' (fun _ => False) HF); [|exact Ha|tauto].
intros b wlo whi a' Hin Ha'. unfold windows in Hin. apply in_map_iff in Hin. destruct Hin as (r & Heq & Hr).
rewrite forallb_forall in Hro. specialize (Hro r Hr). apply Z.leb_le in Hro.
injection Heq as Hb Hl Hh. subst. lia.
Qed.
(* a ROM byte is shown by every reader *)
Lemma s5b_rom_some : forall (H : word -> bool) mem a, seg_rom SEGS (Z_to_bv 64 a) <> None -> aview SEGS H mem a <> None.
Proof using All.
intros H mem a Hr. unfold aview, mbyte. destruct (mrestrict H mem (Z_to_bv 64 a)) as [b|]; [cbn; discriminate|].
destruct (seg_rom SEGS (Z_to_bv 64 a)) as [b|] eqn:E; [cbn; discriminate | congruence].
Qed.

(* the entry sp and the realigned base S1 (andi sp,sp,-32 at 0x84e00 after addi sp,sp,-352) *)
Lemma s5b_sp : forall cx, lt_base B MT cx ->
  x_sp0 cx mod 16 = 0 /\ alloc_ceiling + 32768 <= x_sp0 cx /\ x_sp0 cx <= 2 ^ 47 /\
  x_s1 cx mod 32 = 0 /\ x_sp0 cx - 368 <= x_s1 cx /\ x_s1 cx <= x_sp0 cx - 352 /\
  0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000.
Proof using All.
intros cx HB. destruct HB as (HPRE & _). destruct HPRE as (_ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
unfold x_s1, x_sp0, LT_FRAME, STK_LLVMFuzzerTestOneInput in *.
set (s := spZ (x_regs cx)) in *. clearbody s.
repeat split; lia.
Qed.
(* the class-3 frame of a point: live, at frame_addr = FR, in the application memory, 32-aligned, above the image
   and above snp_hi (the fake stack lies above the image's hull: fuzz_command's RtPFDog.v pa_frame_above_img, with
   HSNP_FAKE for its pa_fake_above_img), its bytes present, apart from every block *)
Lemma s5b_frame : forall cx ly S (W : world SEGS) regs mem md k o,
  lt_frame B cx ly S W regs mem md k o ->
  In (LT_FCLS, x_fpos cx) (frames S) /\ frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx /\
  4096 <= x_fr cx /\ x_fr cx + 512 <= alloc_ceiling /\ x_fr cx mod 32 = 0 /\ in_app (x_fr cx) 512 /\
  kImgEnd <= x_fr cx /\ snp_hi <= x_fr cx /\
  (forall a, x_fr cx <= a < x_fr cx + 512 -> apresent (w_H W) mem a /\ ~ aowned B ly S a) /\
  (forall b n, In (b, n) (ablocks B ly S) -> b + req_size n <= x_fr cx \/ x_fr cx + 512 <= b).
Proof using All.
intros cx ly S W regs mem md k o HF.
destruct HF as (HJ & _).
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _).
assert (HinF : In (LT_FCLS, x_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (EFF : ly_F ly = ly_F (x_ly cx)) by (destruct Hly as (_ & _ & _ & _ & _ & EF & _); exact EF).
assert (EF : frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx) by (unfold x_fr, frame_addr; rewrite EFF; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ LT_FCLS (x_fpos cx) HAR HinF) as (Hal & Happ & HFp & _).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ LT_FCLS (x_fpos cx) HAR HinF) as (H4096 & Hceil & _).
pose proof (HSNP_FAKE ly S W mem md HAR) as HFk.
pose proof HAR as (M & LG & _).
pose proof (pa_img_cover ly S md LG) as [_ C2].
pose proof (OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.YG0t.hull_below_F ly (am_layout _ _ _ _ M)) as HHF.
pose proof (frame_facts B ly S _ LT_FCLS (x_fpos cx) M HinF) as (Fc & _ & _ & _ & _ & P1 & _).
change (fs_frame_bytes LT_FCLS) with 512 in *.
rewrite EF in *.
assert (HFA : ly_F ly <= x_fr cx).
{ rewrite <- EF. unfold frame_addr, LT_FCLS, kFakeFramesOff in *. lia. }
split; [exact HinF|]. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [exact Hal|]. split; [exact Happ|].
split; [lia|]. split; [lia|]. split; [exact HFp|].
intros b n Hbn. pose proof (sep_block_frame SEGS B LAWS ly S W mem md b n LT_FCLS (x_fpos cx) HAR Hbn HinF) as Hd.
rewrite EF in Hd. change (fs_frame_bytes LT_FCLS) with 512 in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.
(* a live block of a state is a harness block of that state *)
Lemma s5b_hblk : forall ly S (W : world SEGS) mem md a n,
  AR SEGS B ly S W mem md -> In (a, n) (ablocks B ly S) -> lt_hblk B ly S (rdW W mem) a n.
Proof using All.
intros ly S W mem md a n HAR Hin.
destruct (al_blocks _ _ LAWS ly S W mem md a n HAR Hin) as (H16 & H4096 & Hceil & _ & _ & _ & Hn).
pose proof (req_size_pos n ltac:(lia)) as [_ Hreq].
pose proof asan_consts as (C1 & _).
split; [exact Hin|]. split; [exact H4096|]. split; [exact H16|].
split; [lia|]. split; [lia|].
split; [exact (amem_range_of_block SEGS B LAWS ly S W mem md a n a n HAR Hin ltac:(lia) ltac:(lia))|].
split; [exact (range_addressable_of_block SEGS B LAWS ly S W mem md a n a n HAR Hin ltac:(lia) ltac:(lia))|].
intros Hn0. exact (shadow_hull_vis_of_block SEGS B LAWS ly S W mem md a n a n HAR Hin ltac:(lia) ltac:(lia) Hn0).
Qed.

(* lt_img at a later reader that agrees on every image byte but longl[0 .. 120), the one image range this segment
   writes (memset at 0x852a8): image A's S01 / S02 walk's lk_img_kept (A_s12k.v:191-228) with the image facts from IMGF
   (s5b_relro, cif_guard_rom), the stack-protector cells re-derived from AR at the later state
   (SegRecCells.seg_rec_cells: the runtime owns the .got word gotwA), longl's own (HPG_RO: longl is no read-only
   byte) and the pointers the
   catalogue rows and m_key.words hold (HPG_PTR: each at least 65536 below longl) *)
Lemma s5b_img_kept : forall cx (W W' : world SEGS) mem mem' ly' S' md',
  AR SEGS B ly' S' W' mem' md' ->
  lt_img B cx (rdW W mem) ->
  (forall a, in_img SEGS a -> ~ (longlA <= a < longlA + LONGL_W) -> rdW W' mem' a = rdW W mem a) ->
  lt_img B cx (rdW W' mem').
Proof using All.
intros cx W W' mem mem' ly' S' md' HAR' (HRO & HIMG & HGI) HK.
destruct HIMG as (Hm40 & Hm40i & Hfz & Hrc & Hcat & Hcata & Hw & Hrl & Hssp & Hpin & Hrt & Hli & Hd1 & Hd2 & Hd3).
assert (KI : forall q n, sa_img SEGS B q n -> (q + n <= longlA \/ longlA + LONGL_W <= q) ->
  forall x, q <= x < q + n -> rdW W' mem' x = rdW W mem x).
{ intros q n Hq Hd x Hx. apply HK; [exact (proj1 (Hq x Hx)) | lia]. }
assert (KL : forall a s, sa_lit SEGS B (rdW W mem) a s ->
  (a + (Z.of_nat (length s) + 1) <= longlA \/ longlA + LONGL_W <= a) -> sa_lit SEGS B (rdW W' mem') a s).
{ intros a s Hl Hd. destruct Hl as (Ha & ((Hzs & Hn0) & _) & Hpin' & Hrt' & Himg').
  split; [exact Ha|]. split; [split; [split; [|exact Hn0] | exact (sa_tail_of_romtail SEGS (w_H W') mem' _ Hrt')]|].
  - intros i Hi. rewrite (KI a (Z.of_nat (length s) + 1) Himg' Hd); [exact (Hzs i Hi)|].
    rewrite length_app in Hi. cbn [length] in Hi. lia.
  - split; [exact Hpin'|]. split; [exact Hrt' | exact Himg']. }
assert (KRO : forall x, in_roP SEGS RLO_A RHI_A x -> in_img SEGS x).
{ intros x [(s & Hs & _ & Hr) | Hrr]; [exists s; split; [exact Hs | exact Hr] | exact (s5b_relro x Hrr)]. }
assert (KNL : forall x, in_roP SEGS RLO_A RHI_A x -> ~ (longlA <= x < longlA + LONGL_W)).
{ intros x Hro Hx. apply (HPG_RO x); [|exact Hro]. exists (longlA, longlA + LONGL_N).
  split; [left; reflexivity|]. cbn [fst snd]. unfold LONGL_N, LONGL_W in *. lia. }
assert (KPTR : forall a p,
  ((exists i, (i < 5)%nat /\ a = wordsA + 8 * Z.of_nat i) \/
   (exists i, (i < pin_spec.CAT_N)%nat /\ a = pin_spec.row_addr catA i)) ->
  (forall x, a <= x < a + 8 -> in_roP SEGS RLO_A RHI_A x /\ ~ Exists (in_zr x) (as_owned_static B) /\
     ~ (as_errno B <= x < as_errno B + 4)) ->
  rdword (rdW W mem) a = Some p -> p + 65536 <= longlA).
{ intros a p Ha Hx Hwd. apply (HPG_PTR a p Ha). rewrite <- Hwd. apply rdword_ext. intros kk Hk.
  destruct (Hx (a + kk) ltac:(lia)) as (H1 & H2 & H3). symmetry. exact (HRO (a + kk) H1 H2 H3). }
split; [|split].
- intros a Hro Ho He. rewrite (HK a (KRO a Hro) (KNL a Hro)). exact (HRO a Hro Ho He).
- assert (HD3 : mod40A + 8 <= longlA \/ longlA + LONGL_W <= mod40A)
    by (unfold sa_disj in Hd3; unfold LONGL_N, LONGL_W in *; lia).
  split; [intros kk Hk; rewrite (KI _ 8 Hm40i HD3) by lia; exact (Hm40 kk Hk)|].
  split; [exact Hm40i|].
  split; [intros s Hs; destruct (Hfz s Hs) as [H1 H2]; exact (conj (KL _ _ H1 (s5b_apart _ _ H2)) H2)|].
  split; [intros s Hs; destruct (Hrc s Hs) as [H1 H2]; exact (conj (KL _ _ H1 (s5b_apart _ _ H2)) H2)|].
  split.
  { destruct Hcat as (Hcp & Hci & Hrows). pose proof (s5b_apart _ _ Hcata) as Hcd.
    split; [exact Hcp|]. split; [exact Hci|].
    intros i Hi. destruct (Hrows i Hi) as (tp & Htp & Hl). exists tp.
    assert (Hrow : catA <= pin_spec.row_addr catA i /\ pin_spec.row_addr catA i + 8 <= catA + pin_spec.CAT_BYTES)
      by (unfold pin_spec.row_addr, pin_spec.CAT_ROW, pin_spec.CAT_BYTES, pin_spec.CAT_N in *; lia).
    split.
    - apply (s5b_word_kept (rdW W mem)); [|exact Htp]. intros x Hx. apply (KI _ _ Hci Hcd). lia.
    - apply (KL _ _ Hl).
      assert (Hp : tp + 65536 <= longlA).
      { apply (KPTR (pin_spec.row_addr catA i) tp); [right; exists i; split; [exact Hi | reflexivity] | | exact Htp].
        intros x Hx. destruct (Hci x ltac:(lia)) as (_ & Ho & He). split; [|split; [exact Ho | exact He]].
        right. unfold RLO_A, RHI_A, SEG_RLO, SEG_RHI, catA in *.
        unfold pin_spec.row_addr, pin_spec.CAT_ROW, pin_spec.CAT_BYTES, pin_spec.CAT_N in *. lia. }
      pose proof (s5b_tok_len i Hi) as Htl. clear - Hp Htl. lia. }
  split; [exact Hcata|].
  split.
  { destruct Hw as (Hwp & Hwi & Hws).
    assert (Hwd : wordsA + 40 <= longlA \/ longlA + LONGL_W <= wordsA)
      by (unfold wordsA, longlA, A_LONGL, LONGL_W; lia).
    split; [exact Hwp|]. split; [exact Hwi|].
    intros i Hi. destruct (Hws i Hi) as (wp & Hwp' & Hl). exists wp. split.
    - apply (s5b_word_kept (rdW W mem)); [|exact Hwp']. intros x Hx. apply (KI _ _ Hwi Hwd). lia.
    - apply (KL _ _ Hl).
      assert (Hp : wp + 65536 <= longlA).
      { apply (KPTR (wordsA + 8 * Z.of_nat i) wp); [left; exists i; split; [exact Hi | reflexivity] | | exact Hwp'].
        intros x Hx. destruct (Hwi x ltac:(lia)) as (_ & Ho & He). split; [|split; [exact Ho | exact He]].
        right. unfold RLO_A, RHI_A, SEG_RLO, SEG_RHI, wordsA in *. lia. }
      pose proof (s5b_word_len i Hi) as Htl. clear - Hp Htl. lia. }
  split.
  { destruct Hrl as (Hrp & Hri & Hrs).
    assert (Hrd : rolesA + 20 <= longlA \/ longlA + LONGL_W <= rolesA)
      by (unfold rolesA, longlA, A_LONGL, LONGL_W; lia).
    split; [exact Hrp|]. split; [exact Hri|].
    intros i Hi kk Hk. rewrite (KI _ _ Hri Hrd) by lia. exact (Hrs i Hi kk Hk). }
  split.
  { exact (proj1 (proj2 (SegRecCells.seg_rec_cells SEGS B LAWS HBS IMGF ly' S' W' mem' md' HAR'))). }
  split; [exact Hpin|]. split; [exact Hrt|]. split; [exact Hli|].
  split; [exact Hd1|]. split; [exact Hd2 | exact Hd3].
- intros i Hi. rewrite (HK (longlA + LONGL_W + i)); [exact (HGI i Hi) | | unfold LONGL_W; lia].
  exact (proj1 (Hli (longlA + LONGL_W + i) ltac:(unfold LONGL_W, LONGL_N; lia))).
Qed.

(* what a step of this piece may change: bytes below S1 that are not the frame's header and flag words, not its
   36 shadow bytes, no image byte but longl[0 .. 120), and no byte of a live block or of the 8-byte granule its
   end lies in *)
Definition s5b_avoid (cx : lcx) (ly : alayout) (S : astate) (E : Z -> Prop) : Prop :=
  forall a, E a ->
  a < x_s1 cx /\ ~ (x_fr cx <= a < x_fr cx + 24) /\ ~ (x_fr cx + LT_FLAGW <= a < x_fr cx + LT_FLAGW + 8) /\
  ~ (x_sh cx <= a < x_sh cx + 36) /\ (in_img SEGS a -> longlA <= a < longlA + LONGL_W) /\
  (forall b n, In (b, n) (ablocks B ly S) -> ~ (b <= a < (b + n + 7) / 8 * 8)).
(* the facts of S5_LB / S5_OTH / S5_LST but the registers and the label, carried to a later state that keeps the
   journal at the same count and every byte outside such a set E (image A's S01 / S02 walk's lk_core_run, for this
   piece's steps: the runs, which write nothing, the snprintf call, the memset) *)
Lemma s5b_kept : forall cx ly S (W : world SEGS) regs mem md k acc c m t f regs' mem' md' (E : Z -> Prop),
  lt_base B MT cx ->
  S5_body B MT cx ly S W regs mem md k acc LFO_L c m t f ->
  lt_cm (rdW W mem) c m (x_st cx f) -> sa_str (rdW W mem) t (s5_txt (x_pl cx) f) ->
  lt_slots cx (rdW W mem) (S5_slots cx c m f) ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem' md' k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ E a -> rdW W mem' a = rdW W mem a) ->
  s5b_avoid cx ly S E ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
  S5_body B MT cx ly S W regs' mem' md' k acc LFO_L c m t f /\ lt_cm (rdW W mem') c m (x_st cx f) /\
  sa_str (rdW W mem') t (s5_txt (x_pl cx) f) /\ lt_slots cx (rdW W mem') (S5_slots cx c m f).
Proof using All.
intros cx ly S W regs mem md k acc c m t f regs' mem' md' E HB HBODY HCM HSTR HSL HJ' HK HAV P2 P3 P4 P8 P9.
pose proof (s5b_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi & Hceil0).
destruct HBODY as (HC & HHc & HHm & HHt & HCNT).
destruct HC as (HF & HI & HBL & HBUD).
pose proof (s5b_frame cx ly S W regs mem md k LFO_L HF) as (HinF & EF & Hf4096 & Hfceil & Hfal & Hfapp & _).
destruct HF as (HJ & R2 & R3 & R4 & R8 & R9 & HSV & HH0 & HH8 & HH16 & HFL & H200 & HSH & H184).
pose proof (proj1 HJ) as HAR. pose proof (proj1 HJ') as HAR'.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof ltoi_stk_room as HSR. unfold LTOI_FRAME_MAX in *.
assert (K1 : forall a, x_s1 cx <= a < 2 ^ 64 -> rdW W mem' a = rdW W mem a).
{ intros a Ha. apply HK; [lia|]. intros He. destruct (HAV a He) as (Hlt & _). lia. }
assert (KF : forall a, x_fr cx <= a < x_fr cx + 24 \/ x_fr cx + LT_FLAGW <= a < x_fr cx + LT_FLAGW + 8 ->
  rdW W mem' a = rdW W mem a).
{ intros a Ha. apply HK; [unfold LT_FLAGW in *; lia|]. intros He. destruct (HAV a He) as (_ & Hn1 & Hn2 & _).
  destruct Ha as [Ha | Ha]; [exact (Hn1 Ha) | exact (Hn2 Ha)]. }
assert (KH : forall i, 0 <= i < 36 -> rdW W mem' (x_sh cx + i) = rdW W mem (x_sh cx + i)).
{ intros i Hi. apply HK; [unfold x_sh, shadow_addr, SHADOW_OFF; lia|]. intros He.
  destruct (HAV _ He) as (_ & _ & _ & Hsh & _). apply Hsh. lia. }
assert (KI : forall a, in_img SEGS a -> ~ (longlA <= a < longlA + LONGL_W) -> rdW W mem' a = rdW W mem a).
{ intros a Ha Hn. pose proof (pa_segs_low a Ha). apply HK; [lia|]. intros He.
  destruct (HAV _ He) as (_ & _ & _ & _ & Himg & _). exact (Hn (Himg Ha)). }
assert (KB : forall b n, In (b, n) (ablocks B ly S) -> forall a, b <= a < (b + n + 7) / 8 * 8 ->
  rdW W mem' a = rdW W mem a).
{ intros b n Hbn a Ha. destruct (al_blocks _ _ LAWS ly S W mem md b n HAR Hbn) as (_ & H4096 & Hceil & _ & _ & _ & Hn).
  pose proof (req_size_pos n ltac:(lia)) as [_ Hreq].
  apply HK; [lia|]. intros He. destruct (HAV _ He) as (_ & _ & _ & _ & _ & Hblk). exact (Hblk b n Hbn Ha). }
split; [|split; [|split]].
- split; [|split; [|split; [|split]]].
  + split; [|split; [|split]].
    * split; [exact HJ'|]. rewrite P2, P3, P4, P8, P9.
      split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R8|]. split; [exact R9|].
      split.
      { intros i r Hi. assert (Hi13 : (i < length LT_SAVED)%nat) by (apply nth_error_Some; congruence).
        change (length LT_SAVED) with 13%nat in Hi13.
        apply (s5b_word_kept (rdW W mem)); [|exact (HSV i r Hi)]. intros x Hx. apply K1. lia. }
      split; [apply (s5b_word_kept (rdW W mem)); [|exact HH0]; intros x Hx; apply KF; left; lia|].
      split; [apply (s5b_word_kept (rdW W mem)); [|exact HH8]; intros x Hx; apply KF; left; lia|].
      split; [apply (s5b_word_kept (rdW W mem)); [|exact HH16]; intros x Hx; apply KF; left; lia|].
      split; [apply (s5b_word_kept (rdW W mem)); [|exact HFL]; intros x Hx; apply KF; right; lia|].
      split; [apply (s5b_word_kept (rdW W mem)); [|exact H200]; intros x Hx; apply K1; lia|].
      split.
      { intros i Hi. rewrite (lt_fsh_len LFO_L) in Hi. rewrite KH by lia. exact (HSH i ltac:(rewrite lt_fsh_len; exact Hi)). }
      apply (s5b_word_kept (rdW W mem)); [|exact H184]; intros x Hx; apply K1; lia.
    * exact (s5b_img_kept cx W W mem mem' ly S md' HAR' HI KI).
    * exact HBL.
    * exact HBUD.
  + exact (s5b_hblk ly S W mem' md' c _ HAR' (proj1 HHc)).
  + exact (s5b_hblk ly S W mem' md' m _ HAR' (proj1 HHm)).
  + exact (s5b_hblk ly S W mem' md' t _ HAR' (proj1 HHt)).
  + exact HCNT.
- unfold lt_cm, sa_rconf, sa_mconf, sa_mconfp in *.
  destruct HCM as ((bc & Hbc & Hec) & (bm & Hbm & Hem)).
  pose proof (proj1 Hec) as Hlc. pose proof (proj1 Hem) as Hlm.
  split.
  + exists bc. split; [|exact Hec]. intros i Hi. rewrite (KB c _ (proj1 HHc)) by (unfold seg_spec.SEG_C_SIZE in *; lia).
    exact (Hbc i Hi).
  + exists bm. split; [|exact Hem]. intros i Hi. rewrite (KB m _ (proj1 HHm)) by (unfold seg_spec.SEG_M_SIZE in *; lia).
    exact (Hbm i Hi).
- destruct HSTR as ((Hzs & Hn0) & Htl).
  assert (Htn : x_tn cx f = Z.of_nat (length (s5_txt (x_pl cx) f)) + 1) by reflexivity.
  split; [split; [|exact Hn0]|].
  + intros i Hi. rewrite (KB t _ (proj1 HHt)); [exact (Hzs i Hi)|].
    rewrite length_app in Hi. cbn [length] in Hi. rewrite Htn. lia.
  + intros x Hx. rewrite (KB t _ (proj1 HHt)); [exact (Htl x Hx)|]. rewrite Htn. lia.
- intros o v Hin. specialize (HSL o v Hin).
  assert (Ho : 0 <= o <= 216).
  { unfold S5_slots, LT_L in Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin]; cbn [In] in Hin;
      repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- _; lia|]); destruct Hin. }
  apply (s5b_word_kept (rdW W mem)); [|exact HSL]. intros x Hx. apply K1. lia.
Qed.

(* the label at a reader that agrees everywhere *)
Lemma s5b_label_full : forall ly S (rd rd' : reader) cx f lp c m, (forall x, rd' x = rd x) ->
  S5_label B ly S rd cx f lp c m -> S5_label B ly S rd' cx f lp c m.
Proof using All.
intros ly S rd rd' cx f lp c m HK HL. unfold S5_label in *. destruct HL as (H0 & Hos & Hm). split; [exact H0|].
assert (KS : forall p s, sa_str rd p s -> sa_str rd' p s).
{ intros p s ((Hzs & Hn0) & Htl). split; [split; [|exact Hn0]|].
  - intros i Hi. rewrite HK. exact (Hzs i Hi).
  - intros x Hx. rewrite HK. exact (Htl x Hx). }
assert (KA : forall q n, sa_addr rd q n -> sa_addr rd' q n).
{ intros q n (A1 & A2 & A3 & A4 & A5). split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split.
  - intros x Hx. destruct (A4 x Hx) as (s & Hs & Hok). exists s. rewrite HK. split; [exact Hs | exact Hok].
  - intros Hn s Hs. rewrite HK. exact (A5 Hn s Hs). }
destruct (s5_lab (x_pl cx) f) as [l|].
- destruct Hos as [Hp Hs]. split; [split; [exact Hp | exact (KS _ _ Hs)]|].
  destruct Hm as (Hlen & Hloc & Had & Hd1 & Hd2). split; [exact Hlen|]. split; [exact Hloc|].
  split; [exact (KA _ _ Had)|]. split; [exact Hd1 | exact Hd2].
- split; [exact Hos | exact I].
Qed.

(* a present byte is shown by its reader *)
Lemma s5b_present_some : forall (H : word -> bool) mem a, apresent H mem a -> aview SEGS H mem a <> None.
Proof using All.
intros H mem a (Hh & b & Hb). unfold aview, mbyte, mrestrict. rewrite Hh, Hb. cbn. discriminate.
Qed.
(* the two image objects the label arms load through the listing (SegAddr.seg_objs, image B): A_OBJ 6 = atom 247 =
   longl 0x5dee40, A_OBJ 5 = atom 246 = the label format 0x20fe0 *)
Lemma s5b_obj : forall E, img_env VAL A_LIM E ->
  ew E 247 = w64 longlA /\ ew E 246 = w64 (seg_litA_fz LLVMFuzzerTestOneInput_c.LIT_LABEL).
Proof using All.
intros E HE. pose proof (VOBJS 6%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)) as V6.
pose proof (VOBJS 5%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)) as V5.
split; apply bv_eq.
- rewrite (HE 247%nat ltac:(unfold A_TEXT, A_LIM; lia)). change 247%nat with (A_OBJ 6). rewrite V6.
  vm_compute. reflexivity.
- rewrite (HE 246%nat ltac:(unfold A_TEXT, A_LIM; lia)). change 246%nat with (A_OBJ 5). rewrite V5.
  vm_compute. reflexivity.
Qed.
(* what each label arm's call may write is a set the facts of this piece avoid *)
Lemma s5b_avoid_snp : forall cx ly S (W : world SEGS) regs mem md k o,
  lt_base B MT cx -> lt_frame B cx ly S W regs mem md k o ->
  s5b_avoid cx ly S (fun a => (x_fr cx + FO_LABEL <= a < x_fr cx + FO_LABEL + 40) \/ (x_s1 cx - 2 * ESTACK <= a < x_s1 cx)).
Proof using All.
intros cx ly S W regs mem md k o HB HF a Ha.
pose proof (s5b_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi & Hceil0).
pose proof (s5b_frame cx ly S W regs mem md k o HF) as (HinF & EF & Hf4096 & Hfceil & Hfal & Hfapp & Himgf & _ & _ & Hsep).
pose proof (proj1 (proj1 HF)) as HAR.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold LTOI_FRAME_MAX, STK_LLVMFuzzerTestOneInput, FO_LABEL, ESTACK, LT_FLAGW, x_sh, shadow_addr, SHADOW_OFF in *.
destruct Hfapp as [_ Hfapp]. unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hfapp. unfold kImgEnd in Himgf.
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split.
- intros Hi. pose proof (pa_img_range a Hi) as Hr. unfold kImgEnd in Hr. lia.
- intros b n Hbn Hb. destruct (al_blocks _ _ LAWS ly S W mem md b n HAR Hbn) as (_ & H4096 & Hceil & _ & _ & _ & Hn).
  pose proof (req_size_pos n ltac:(lia)) as [_ Hreq]. pose proof (Hsep b n Hbn) as Hs. lia.
Qed.
Lemma s5b_avoid_set : forall cx ly S (W : world SEGS) regs mem md k o,
  lt_base B MT cx -> lt_frame B cx ly S W regs mem md k o ->
  s5b_avoid cx ly S (fun a => (longlA <= a < longlA + 120) \/ (x_s1 cx - ESTACK <= a < x_s1 cx)).
Proof using All.
intros cx ly S W regs mem md k o HB HF a Ha.
pose proof (s5b_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi & Hceil0).
pose proof (s5b_frame cx ly S W regs mem md k o HF) as (HinF & EF & Hf4096 & Hfceil & Hfal & Hfapp & Himgf & _ & _ & Hsep).
pose proof (proj1 (proj1 HF)) as HAR.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold LTOI_FRAME_MAX, STK_LLVMFuzzerTestOneInput, ESTACK, LT_FLAGW, x_sh, shadow_addr, SHADOW_OFF, LONGL_W,
  longlA, A_LONGL in *.
unfold kImgEnd in Himgf.
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split.
- intros Hi. pose proof (pa_img_range a Hi) as Hr. unfold kImgEnd in Hr. lia.
- intros b n Hbn Hb. destruct (al_blocks _ _ LAWS ly S W mem md b n HAR Hbn) as (_ & H4096 & Hceil & _ & _ & _ & Hn).
  pose proof (req_size_pos n ltac:(lia)) as [_ Hreq]. pose proof (blk_off_imgP B ly S W mem md b n HAR Hbn) as Ho.
  unfold off_img in Ho. lia.
Qed.

(* ---------------- the label each arm leaves in s3 (the kit's S5_label) ---------------- *)
(* lb = 0: no label, s3 = 0 *)
Lemma s5b_label_none : forall ly S rd cx f c m, s5_lab (x_pl cx) f = None -> S5_label B ly S rd cx f 0 c m.
Proof using All.
intros ly S rd cx f c m Hl. unfold S5_label. rewrite Hl. split; [lia|]. split; [reflexivity | exact I].
Qed.
(* the snprintf arm: label[40] of the class-3 frame holds the text and its NUL *)
Lemma s5b_label_snp : forall cx ly S (W : world SEGS) regs mem md k acc c m t f (lb : Z),
  lt_base B MT cx -> S5_body B MT cx ly S W regs mem md k acc LFO_L c m t f ->
  1 <= lb <= 127 -> s5_lab (x_pl cx) f = Some (SegModel.fmt SegModel.F_label [SegModel.AI lb]) ->
  (forall i, 0 <= i <= Z.of_nat (length (SegModel.fmt SegModel.F_label [SegModel.AI lb])) ->
     rdW W mem (x_fr cx + FO_LABEL + i) =
     Some (nth (Z.to_nat i) (SegModel.fmt SegModel.F_label [SegModel.AI lb] ++ [0]) 0)) ->
  S5_label B ly S (rdW W mem) cx f (x_fr cx + FO_LABEL) c m.
Proof using All.
intros cx ly S W regs mem md k acc c m t f lb HB HBODY Hlb Hl Hbytes.
destruct (s5b_glue lb Hlb) as (_ & HTlen & HTb).
set (T := SegModel.fmt SegModel.F_label [SegModel.AI lb]) in *.
pose proof HBODY as ((HF & _) & HHc & HHm & _).
pose proof (s5b_frame cx ly S W regs mem md k LFO_L HF) as (HinF & EF & Hf4096 & Hfceil & Hfal & Hfapp & _ & _ & HFp & Hsep).
pose proof HF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSH & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTl : Z.of_nat (length T) < 39) by lia.
unfold S5_label. rewrite Hl.
split; [unfold FO_LABEL; lia|]. split.
{ split; [unfold FO_LABEL; lia|]. split; [split|].
  - intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
    rewrite (Hbytes (Z.of_nat i)) by lia. rewrite Nat2Z.id. reflexivity.
  - intros H0. rewrite Forall_forall in HTb. pose proof (HTb 0 H0). lia.
  - intros x Hx. apply s5b_present_some. apply (proj1 (HFp x ltac:(unfold FO_LABEL in *; lia))). }
split; [lia|]. split.
{ right; left. exists LT_FCLS, (x_fpos cx). split; [exact HinF|]. split; [unfold LT_FCLS; lia|].
  rewrite EF. change (fs_frame_bytes LT_FCLS) with 512. unfold FO_LABEL. lia. }
split.
{ split; [unfold FO_LABEL; lia|]. split; [unfold FO_LABEL; lia|].
  split; [apply (a3_amem_slack (x_fr cx) 512); [exact Hfapp | unfold FO_LABEL; lia | lia | unfold FO_LABEL; lia]|].
  split.
  - intros x Hx. exists 0. split; [|left; reflexivity].
    apply (s5b_label_shadow _ (x_fr cx) x HSH); [lia | lia | unfold FO_LABEL in Hx; lia].
  - intros Hn. apply (s5b_label_hull _ (x_fr cx) _ _ HSH Hfal); unfold FO_LABEL; lia. }
assert (Hspan : seg_spec.cstr_span (x_fr cx + FO_LABEL) T <= Z.of_nat (length T) + 8).
{ unfold seg_spec.cstr_span. pose proof (Z.mod_pos_bound (- (x_fr cx + FO_LABEL + Z.of_nat (length T) + 1)) 8 ltac:(lia)). lia. }
pose proof (Hsep m _ (proj1 HHm)) as Hm. pose proof (Hsep c _ (proj1 HHc)) as Hc.
pose proof (req_size_pos seg_spec.SEG_M_SIZE ltac:(unfold seg_spec.SEG_M_SIZE; lia)) as [_ Rm].
pose proof (req_size_pos seg_spec.SEG_C_SIZE ltac:(unfold seg_spec.SEG_C_SIZE; lia)) as [_ Rc].
unfold sa_disj. unfold FO_LABEL in *. split; lia.
Qed.
(* the longl arm: longl holds 120 bytes 'L' (the memset) and its NUL (ltoi_GI) *)
Lemma s5b_label_longl : forall cx ly S (W : world SEGS) regs mem md k acc c m t f,
  S5_body B MT cx ly S W regs mem md k acc LFO_L c m t f ->
  s5_lab (x_pl cx) f = Some SegModel.longl ->
  (forall i, 0 <= i < 120 -> rdW W mem (longlA + i) = Some 76) ->
  S5_label B ly S (rdW W mem) cx f longlA c m.
Proof using All.
intros cx ly S W regs mem md k acc c m t f HBODY Hl Hset.
pose proof HBODY as ((HF & HI & _) & HHc & HHm & _).
pose proof (proj1 (proj1 HF)) as HAR.
pose proof HI as (_ & HIMG & HGI).
destruct HIMG as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpin & Hrt & Hli & _).
pose proof s5_longl_len as HL.
unfold S5_label. rewrite Hl. rewrite HL.
assert (EN : Z.of_nat 120 + 1 = LONGL_N) by reflexivity.
split; [unfold longlA, A_LONGL; lia|]. split.
{ split; [unfold longlA, A_LONGL; lia|]. split; [split|].
  - intros i Hi. rewrite length_app, HL in Hi. cbn [length] in Hi.
    destruct (Nat.lt_ge_cases i 120) as [Hi1 | Hi1].
    + rewrite app_nth1 by lia. unfold SegModel.longl. rewrite s5b_nth_repeat by lia. apply Hset. lia.
    + assert (i = 120%nat) by lia. subst i. rewrite app_nth2 by lia. rewrite HL. cbn [Nat.sub nth].
      pose proof (HGI 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0. exact H0.
  - unfold SegModel.longl. intros H0. apply repeat_spec in H0. lia.
  - rewrite HL. exact (sa_tail_of_romtail SEGS (w_H W) mem _ Hrt). }
split; [lia|]. split.
{ right; right. rewrite EN. split; [exact Hli|]. split; [exact Hpin|].
  apply sa_pinned_tail_of_romtail. exact Hrt. }
split; [rewrite EN; exact (Hpin ly S W mem md HAR)|].
replace (seg_spec.cstr_span longlA SegModel.longl) with 128 by (vm_compute; reflexivity).
pose proof (blk_off_imgP B ly S W mem md m _ HAR (proj1 HHm)) as Hm.
pose proof (blk_off_imgP B ly S W mem md c _ HAR (proj1 HHc)) as Hc.
pose proof (req_size_pos seg_spec.SEG_M_SIZE ltac:(unfold seg_spec.SEG_M_SIZE; lia)) as [_ Rm].
pose proof (req_size_pos seg_spec.SEG_C_SIZE ltac:(unfold seg_spec.SEG_C_SIZE; lia)) as [_ Rc].
unfold off_img in Hm, Hc. unfold sa_disj, longlA, A_LONGL, seg_spec.SEG_M_SIZE, seg_spec.SEG_C_SIZE in *. split; lia.
Qed.

(* after a run of this piece: name the model, and the reader agreement of the run (no write window) *)
Ltac s5b_after_run KM :=
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ =>
    let md' := fresh "md" in set (md' := d) in *; clearbody md' end;
  match goal with H : frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) |- _ =>
    pose proof (s5b_nowin_kept _ _ _ m0 m1 H eq_refl) as KM end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
(* the registers of the list L that the run kept: each is the seed's (its symbolic value its own atom) *)
Ltac s5b_kreg HS EE regs0 L K :=
  lazymatch type of HS with
  | context [restrict _ ?ms] =>
    assert (K : forall r : bv 5, In r L -> getr (ms_regs ms) r = getr regs0 r);
    [ intros r Hr; cbn [In] in Hr;
      repeat (destruct Hr as [<- | Hr];
        [ let P := fresh "P" in lazymatch goal with |- getr _ ?rr = _ => prreg HS rr P end;
          rewrite P; apply EE; reflexivity | ]);
      destruct Hr | ]
  end.
(* a register's symbolic value, without prreg's normalization *)
Ltac s5b_rreg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  end.
Ltac s5b_inl := solve [cbn [In]; tauto].
Ltac s5b_cs := first [unfold acallee_saved; lia | apply bv_eq; reflexivity].

(* ---------------- the snprintf call at 0x8528c (row 4 at this call site) ----------------
   fuzz_command's PaRt.v cwc_aj_snprintf_atSF (origin/ossv/recipes 3abc3740de97) restated at this call: snprintf(label,
   40, "reac-pw.conf.d/%u-x.conf", lb) through the trampoline, row 4 (RtPFSeg.seg_asnprintf_realizes, the window
   RtPFSeg.SEG_SNP_K = 2 * ESTACK, the family RtPFSeg.FR_seg snp_lo gotwA) built from the walk's facts: the
   destination label[40] of the class-3 frame (in_frames of the journal's own frame; its shadow bytes 0 by LFO_L;
   above the image and above snp_hi, s5b_frame), the format the literal seg_litA_fz LIT_LABEL (seg_himg's sa_lit,
   HSNP_LIT), the read-only bytes by arodata_okP, the stack-protector cells by seg_himg's sa_ssp. The post comes back
   at the FP state fx1 the call left (fxrel fx fx1), with the journal rebuilt by ajournal_after_write over the
   destination and the window *)
Lemma s5b_snp_call : forall cx ly S (W : world SEGS) regsT memT md k (lb : Z) (raw : word),
  lt_base B MT cx -> sa_frm0 -> lt_frame B cx ly S W regsT memT md k LFO_L -> lt_img B cx (rdW W memT) ->
  1 <= lb <= 127 ->
  getr regsT 10 = w64 (x_fr cx + FO_LABEL) -> getr regsT 11 = w64 40 ->
  getr regsT 12 = w64 (seg_litA_fz LLVMFuzzerTestOneInput_c.LIT_LABEL) -> getr regsT 13 = w64 lb ->
  getr regsT 1 = raw -> YK0s.ret_ok raw ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (SIG SS___interceptor_trampoline_snprintf)) memT (seg_rom SEGS)) md)
    (fun W2 c2 => W2 = W /\ exists (fx1 : YK11.FPState) regs2 mem2 md2, fxrel fx fx1 /\
       c2 = mkCfg (@mkst fx1 regs2 raw mem2 (seg_rom SEGS)) md2 /\
       ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
         (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem2 md2 k /\
       aregs_preserved regsT regs2 /\
       (forall i, 0 <= i <= Z.of_nat (length (SegModel.fmt SegModel.F_label [SegModel.AI lb])) ->
          rdW W mem2 (x_fr cx + FO_LABEL + i) =
          Some (nth (Z.to_nat i) (SegModel.fmt SegModel.F_label [SegModel.AI lb] ++ [0]) 0)) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (x_fr cx + FO_LABEL <= a < x_fr cx + FO_LABEL + 40) ->
          ~ (x_s1 cx - 2 * ESTACK <= a < x_s1 cx) -> rdW W mem2 a = rdW W memT a)).
Proof using All.
intros cx ly S W regsT memT md k lb raw HB Hfrm HF HI Hlb R10 R11 R12 R13 Hra Hraw.
pose proof (s5b_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi & Hceil0). unfold LTOI_FRAME_MAX in Hs1lo.
pose proof (s5b_frame cx ly S W regsT memT md k LFO_L HF)
  as (HinF & EF & Hf4096 & Hfceil & Hfal & Hfapp & Himgf & Hsnpf & HFp & _).
pose proof HF as (HJ & R2 & R3 & R4 & R8 & R9 & _ & _ & _ & _ & _ & _ & HSH & _).
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
pose proof HB as (HPRE0 & _).
pose proof HPRE0 as (_ & _ & _ & Hgp0 & Htp0 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HI as (HRO & HIMG & _).
pose proof HIMG as (_ & _ & Hfz & _ & _ & _ & _ & _ & Hssp & _).
destruct Hssp as (Hg1 & cval & Hg2).
destruct (s5b_glue lb Hlb) as (Htext & HTlen & HTb).
destruct (Hfz LLVMFuzzerTestOneInput_c.LIT_LABEL ltac:(apply in_or_app; left; left; reflexivity)) as (Hlit & _).
pose proof (HSNP_LIT LLVMFuzzerTestOneInput_c.LIT_LABEL ltac:(left; reflexivity)) as (Hfl1 & Hfl2).
assert (Hfl : seg_litA_fz LLVMFuzzerTestOneInput_c.LIT_LABEL = 0x20fe0) by (vm_compute; reflexivity).
assert (HLL : Z.of_nat (length LLVMFuzzerTestOneInput_c.LIT_LABEL) = 24) by (vm_compute; reflexivity).
set (T := SegModel.fmt SegModel.F_label [SegModel.AI lb]) in *.
set (d := x_fr cx + FO_LABEL) in *.
set (fl := seg_litA_fz LLVMFuzzerTestOneInput_c.LIT_LABEL) in *.
assert (Hdd : d = x_fr cx + 96) by reflexivity.
assert (HTl : Z.of_nat (length T) < 39) by lia.
assert (Hsb : RtPFShared.sn_bytes (40 - 1) T = T ++ [0]).
{ unfold RtPFShared.sn_bytes. rewrite firstn_all2; [reflexivity|]. change (Z.to_nat (40 - 1)) with 39%nat. lia. }
assert (Hsn : RtPFShared.sn_len (40 - 1) T = Z.of_nat (length T) + 1).
{ unfold RtPFShared.sn_len. rewrite Hsb, length_app. cbn [length]. lia. }
assert (Hsp1 : spZ regsT = x_s1 cx) by (unfold spZ; rewrite R2; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
assert (Hsp : spZ regsT = x_sp0 cx + (x_s1 cx - x_sp0 cx)) by lia.
assert (Hgp : getr regsT 3 = w64 (as_gp B)) by (rewrite R3; exact Hgp0).
assert (Htp : getr regsT 4 = w64 (as_tp B)) by (rewrite R4; exact Htp0).
assert (Hawr : forall a, d <= a < d + 40 -> awr_byte SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA)
  (ablocks B (x_ly cx) (x_S cx)) (ablocks B ly S) (frames (x_S cx)) ly [(LT_FCLS, x_fpos cx)] a).
{ intros a Ha. right; right; right; left. exists LT_FCLS, (x_fpos cx). split; [left; reflexivity|].
  left. unfold in_zr. cbn [fst snd]. rewrite EF. change (fs_frame_bytes LT_FCLS) with 512. unfold d, FO_LABEL in *. lia. }
assert (Hnfp : forall a, d <= a < d + 40 -> ~ inFP (ltoi_PG longlA) a).
{ intros a Ha (r & Hr & Hra'). destruct Hr as [<- | []]. cbn [fst snd] in Hra'.
  unfold d, FO_LABEL, kImgEnd, longlA, A_LONGL, LONGL_N in *. lia. }
destruct (ecall_pre_stk_at SEGS B RtPFSeg.SEG_SNP_K STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx)
  (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W memT md k regsT (x_s1 cx - x_sp0 cx) HJ Hsp
  ltac:(lia) ltac:(lia) ltac:(unfold RtPFSeg.SEG_SNP_K, ESTACK; lia)
  ltac:(unfold RtPFSeg.SEG_SNP_K, ESTACK, STK_LLVMFuzzerTestOneInput; lia)
  ltac:(rewrite Hra; exact Hraw) Hgp Htp) as (HPRE & Hstklo & Hwin).
pose proof (ASNPRINTF fx) as AP.
unfold RtPFSeg.seg_asnprintf_realizes, RtPFCmd.cmd_asnprintf_realizes in AP.
assert (Hd0 : kImgEnd + 96 <= d) by (unfold d, FO_LABEL; lia).
unfold kImgEnd in Hd0, Himgf.
eapply SRr_mono.
{ apply (AP ly S W regsT memT md d 40 fl [] (map (argZ regsT) [3; 4; 5; 6; 7]) T cval HPRE Hstklo Hwin R10 R11 R12);
    clear AP; rewrite ?Hsn, ?Hsp1; unfold RtPFSeg.SEG_SNP_K, ESTACK in *.
  - (* the unowned read-only bytes: arodata_okP over the read-only segments *)
    intros a Ha Ho He. apply HRO; [left; exact Ha | exact Ho | exact He].
  - apply Forall_forall. intros r Hr. pose proof (proj1 (Forall_forall _ _) HSNP_CR r Hr) as Hq.
    cbv beta in Hq |- *. lia.
  - apply Forall_forall. intros r Hr. pose proof (proj1 (Forall_forall _ _) HSNP_CR r Hr) as Hq. cbv beta in Hq |- *.
    unfold RtPFShared.snp_out. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
      unfold zdisjoint; cbn [fst snd]; lia.
  - exact Hg1.
  - exact Hg2.
  - unfold gotwA. lia.
  - unfold gotwA. lia.
  - unfold guardA. lia.
  - unfold guardA. lia.
  - unfold RtPFShared.snp_out. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
      unfold zdisjoint, gotwA; cbn [fst snd]; lia.
  - unfold RtPFShared.snp_out. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
      unfold zdisjoint, guardA; cbn [fst snd]; lia.
  - split; [rewrite app_nil_r; reflexivity | intros i Hi; cbn [length] in Hi; lia].
  - cbn [length]. lia.
  - unfold RtPFShared.snp_out. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
      unfold zdisjoint; cbn [fst snd length]; lia.
  - (* the format family: the literal, its pieces, the int argument in a3, the text *)
    unfold RtPFSeg.FR_seg, RtPFSeg.seg_fam.
    exists LLVMFuzzerTestOneInput_c.LIT_LABEL, s5b_qs, [RtPFPf.AInt lb].
    destruct Hlit as (Hf0 & ((Hzs & _) & _) & Hpin & _ & _).
    pose proof (Hpin ly S W memT md HAR) as (_ & _ & _ & HRA & HHV).
    split.
    { split; [lia|]. split.
      { intros i Hi. pose proof (Hzs (Z.to_nat i) ltac:(rewrite length_app; cbn [length]; lia)) as Hz.
        rewrite Z2Nat.id in Hz by lia. exact Hz. }
      split.
      { unfold RtPFShared.snp_out. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
          unfold zdisjoint; cbn [fst snd]; unfold gotwA in Hfl2; lia. }
      split; [apply a3_amem_img; unfold kImgEnd, gotwA in *; lia|].
      split; [exact HRA | apply HHV; lia]. }
    split; [exact s5b_parse|]. split; [exact s5b_qs_pk|].
    split.
    { cbn [map RtPFShared.pf_args_asan RtPFShared.pf_arg_asan]. split; [|exact I]. split; [lia|].
      unfold argZ. replace (Z_to_bv 5 (10 + 3)) with (13%bv : bv 5) by (apply bv_eq; reflexivity).
      rewrite R13. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
    split; [exact Htext|]. split; [vm_compute; exact I|].
    split; [exact Hfl1|]. split; [exact Hfl2|]. split; [exact I|]. split; [discriminate | exact I].
  - lia.
  - lia.
  - unfold d, FO_LABEL in *. lia.
  - lia.
  - unfold RtPFShared.snp_out. cbn [pairwise]. split; [apply Forall_cons; [|apply Forall_nil] | split; [apply Forall_nil | exact I]];
      unfold zdisjoint; cbn [fst snd]; lia.
  - (* dest_ok: label bytes the journal lets the walk write *)
    intros a Ha. assert (Ha' : d <= a < d + 40) by lia.
    destruct (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ (Hawr a Ha')
      (fun Hfp => False_ind _ (Hnfp a Ha' Hfp))) as [Hp Hno].
    split; [exact Hp|]. split; [exact Hno|]. rewrite Hsp1. unfold ESTACK. lia.
  - apply (a3_amem_slack (x_fr cx) 512); [exact Hfapp | unfold d, FO_LABEL; lia | lia | unfold d, FO_LABEL; lia].
  - intros x Hx. exists 0. split; [|left; reflexivity].
    apply (s5b_label_shadow _ (x_fr cx) x HSH); [lia | lia | unfold d, FO_LABEL in Hx; lia].
  - apply (s5b_label_hull _ (x_fr cx) _ _ HSH Hfal); unfold d, FO_LABEL; lia.
  - unfold zdisjoint. cbn [fst snd]. lia.
  - exact Hfrm. }
cbv beta. intros W2 c2 _ (-> & fx1 & regs2 & mem2 & md2 & -> & Hf1 & Hf2 & HAR2 & HP & Hsame & Hres & Hbytes & Hfr & Hpres2).
split; [reflexivity|]. exists fx1, regs2, mem2, md2.
split; [exact (fxrel_of_frm0 fx fx1 Hf1 Hf2)|].
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write SEGS B LAWS pa_segs_low STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx)
    (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W memT md k mem2 md2
    (fun a => (d <= a < d + 40) \/ (x_s1 cx - 2 * ESTACK <= a < x_s1 cx)) S [(LT_FCLS, x_fpos cx)] HJ).
  - intros a Ha Hna. apply (Hfr a Ha); intros H'; apply Hna.
    + left. rewrite Hsn in H'. lia.
    + right. rewrite Hsp1 in H'. unfold RtPFSeg.SEG_SNP_K in H'. exact H'.
  - exact Hpres2.
  - exact Hsame.
  - intros a [Ha | Ha]; left; [exact (Hawr a Ha) | left].
    unfold ESTACK, STK_LLVMFuzzerTestOneInput in *. lia.
  - exact HAR2.
  - reflexivity.
  - reflexivity.
  - lia.
  - exact Hfrs.
  - exact HQT. }
split; [exact HP|]. split.
{ intros i Hi. rewrite <- Hsb. apply Hbytes. rewrite Hsn. lia. }
intros a Ha H1 H2. apply (Hfr a Ha).
- intros H'. apply H1. rewrite Hsn in H'. lia.
- rewrite Hsp1. unfold RtPFSeg.SEG_SNP_K. exact H2.
Qed.

(* ---------------- the join 0x852b4 .. 0x852c4 and the two exits, at any FP state ----------------
   s9 := f + 1 (addiw), a0 := 216(s1) = m + 0x2000, s10 := a0 >> 3, bgeu s9,s2: taken on the last turn (f + 1 =
   nfiles) to S5_LST at 0x85324, else a0 := m and S5_OTH at 0x852c8. The seed takes the word 216(s1) as atom 32 and
   f <= 3 for s9 (atom 25), so the addiw is s9 + 1 and the test is decided by the split *)
Lemma s5b_join : forall (fx1 : YK11.FPState) (f : nat), S5A_OTH B MT f -> S5A_LST B MT f ->
  forall cx ly S (W : world SEGS) regs mem md k acc (c m t lp : Z),
  lt_base B MT cx -> sa_frm0 (fx := fx1) -> Z.of_nat f < x_nf cx ->
  S5_body B MT cx ly S W regs mem md k acc LFO_L c m t f ->
  lt_cm (rdW W mem) c m (x_st cx f) -> sa_str (rdW W mem) t (s5_txt (x_pl cx) f) ->
  S5_label B ly S (rdW W mem) cx f lp c m ->
  getr regs 18 = w64 (x_nf cx) -> getr regs 19 = w64 lp -> getr regs 21 = w64 0 -> getr regs 22 = w64 m ->
  getr regs 23 = w64 t -> getr regs 24 = w64 (x_at cx f + x_np cx f) -> getr regs 25 = w64 (Z.of_nat f) ->
  lt_slots cx (rdW W mem) (S5_slots cx c m f) ->
  SRr SEGS W (@cfg_at fx1 SEGS (BASE + 0x4f4) regs mem md) (lt_post (fx := fx1) B MT cx).
Proof using All.
intros fx1 f HOTH HLST cx ly S W regs mem md k acc c m t lp HB Hfrm Hf HBODY HCM HSTR HLAB
  R18 R19 R21 R22 R23 R24 R25 HSL.
pose proof (s5b_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi & Hceil0). unfold LTOI_FRAME_MAX in Hs1lo.
assert (Hnf : 1 <= x_nf cx <= 4) by exact (s5b_nf_range (x_pl cx)).
pose proof HBODY as ((HF & _) & HHc & HHm & _).
pose proof (proj1 HF) as HJ. pose proof HF as (_ & R2 & R3 & R4 & R8 & R9 & _).
pose proof (proj1 HJ) as HAR.
destruct (al_blocks _ _ LAWS ly S W mem md m _ HAR (proj1 HHm)) as (_ & Hm4096 & Hmceil & _).
pose proof (req_size_pos seg_spec.SEG_M_SIZE ltac:(unfold seg_spec.SEG_M_SIZE; lia)) as [_ Hreqm].
unfold seg_spec.SEG_M_SIZE in Hreqm, Hmceil.
pose proof asan_consts as (C1 & _).
assert (W216 : rdword (rdW W mem) (x_s1 cx + 216) = Some (m + seg_spec.MC_N)).
{ apply HSL. unfold S5_slots, LT_L. apply in_or_app. left. cbn [In]. repeat (first [left; reflexivity | right]). }
assert (EE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr ->
  ew (s5b_E regs [Z_to_bv 64 (m + seg_spec.MC_N)]) n = getr regs rr)
  by (intros n rr Hn; exact (s5b_E_reg regs _ n rr Hn)).
pose proof (s5b_E_32 regs (Z_to_bv 64 (m + seg_spec.MC_N)) []) as E32.
pose proof (s5b_seed fx1 0x4f4 216 (mkFacts [(25%nat, mkAF 0 3 0)] [] []) W regs mem (x_s1 cx) (m + seg_spec.MC_N)
  ltac:(vm_compute; reflexivity)) as HS.
specialize (HS ltac:(split; [|split; [exact I | exact I]];
  cbn [f_atoms atoms_ok]; unfold afact_ok; cbn [af_lo af_hi af_al2];
  rewrite (EE 25%nat 25%bv eq_refl), R25; unfold w64; rewrite !unsigned_lit_small by lia;
  rewrite !Z.pow_0_r, !Z.mod_1_r; repeat match goal with |- _ /\ _ => split end; first [exact I | lia])).
specialize (HS R9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold seg_spec.MC_N; lia) W216).
assert (SHOK : sh_ok SEGS s5b_X [] (s5b_E regs [Z_to_bv 64 (m + seg_spec.MC_N)]) (mrestrict (w_H W) mem))
  by apply Forall_nil.
assert (HEI : img_env VAL A_LIM (s5b_E regs [Z_to_bv 64 (m + seg_spec.MC_N)])) by (unfold s5b_E; apply Eimg_env).
remember (s5b_E regs [Z_to_bv 64 (m + seg_spec.MC_N)]) as E eqn:HE. clear HE.
unfold cfg_at, w64.
pose (RUN1 := paj_run (fx := fx1) B LAWS). pose (RUNTO1 := paj_run_to (fx := fx1) B LAWS).
pose (BR1 := paj_branch (fx := fx1) (PI := PI)).
(* 0x852b4 .. 0x852c0: s9 := f + 1, a0 := m + 0x2000, s10 := a0 >> 3; then bgeu s9,s2 *)
paj_run_tok RUN1 HS HJ SHOK s5b_span.
{ apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
s5b_after_run KM1.
psrr_branch_tok RUN1 BR1 HS SHOK s5b_span.
- (* taken: f + 1 >= nfiles, the last turn; to 0x85324 *)
  assert (Hlast : Z.of_nat f + 1 = x_nf cx).
  { rewrite branch_geu_U in Hc.
    rewrite (U_atom_off E 25 (Z.of_nat f) 1) in Hc by first [rewrite (EE 25%nat 25%bv eq_refl); exact R25 | lia].
    rewrite (U_atom E 18 (x_nf cx)) in Hc by first [rewrite (EE 18%nat 18%bv eq_refl); exact R18 | lia].
    apply negb_true_iff, Z.ltb_ge in Hc. lia. }
  clear Hc.
  paj_run_to_tok RUNTO1 HS HJ SHOK s5b_span 0x564.
  { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
  s5b_after_run KM2.
  assert (KM : forall a, rdW W (ms_mem ms0) a = rdW W mem a) by (intros a; rewrite KM2; apply KM1).
  pmkst HS.
  s5b_kreg HS EE regs ([2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 24]%bv : list (bv 5)) K.
  destruct (s5b_kept cx ly S W regs mem md k acc c m t f (ms_regs ms0) (ms_mem ms0) _ (fun _ => False)
    HB HBODY HCM HSTR HSL HJ ltac:(intros a _ _; apply KM) ltac:(intros a [])
    (K 2%bv ltac:(s5b_inl)) (K 3%bv ltac:(s5b_inl)) (K 4%bv ltac:(s5b_inl)) (K 8%bv ltac:(s5b_inl)) (K 9%bv ltac:(s5b_inl))) as (HB2 & HCM2 & HSTR2 & HSL2).
  apply (HLST fx1 cx ly S W (ms_regs ms0) (ms_mem ms0) _ k acc c m t HB Hfrm Hlast HB2 HCM2 HSTR2).
  + rewrite (K 21%bv ltac:(s5b_inl)). exact R21.
  + rewrite (K 22%bv ltac:(s5b_inl)). exact R22.
  + rewrite (K 23%bv ltac:(s5b_inl)). exact R23.
  + rewrite (K 24%bv ltac:(s5b_inl)). exact R24.
  + prreg HS (25%bv : bv 5) P25. rewrite P25, (EE 25%nat 25%bv eq_refl), R25. unfold w64.
    rewrite unsigned_lit_small by lia. reflexivity.
  + s5b_rreg HS (26%bv : bv 5) P26. rewrite P26. apply s5b_denot_U.
    rewrite U_SAlu, (U_atom _ 32 (m + seg_spec.MC_N)) by first [exact E32 | unfold seg_spec.MC_N; lia].
    rewrite U_lit by lia. cbn [zalu_raw]. change (Z.land 3 63) with 3.
    rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. apply zcanon_id. unfold M64, seg_spec.MC_N in *.
    pose proof (Z.div_le_upper_bound (m + 8192) 8 (m + 8192) ltac:(lia) ltac:(lia)). pose proof (Z.div_pos (m + 8192) 8 ltac:(lia) ltac:(lia)). lia.
  + exact HSL2.
- (* not taken: f + 1 < nfiles; 0x852c4 a0 := m, to 0x852c8 *)
  assert (Hmore : Z.of_nat f + 1 < x_nf cx).
  { rewrite branch_geu_U in Hc.
    rewrite (U_atom_off E 25 (Z.of_nat f) 1) in Hc by first [rewrite (EE 25%nat 25%bv eq_refl); exact R25 | lia].
    rewrite (U_atom E 18 (x_nf cx)) in Hc by first [rewrite (EE 18%nat 18%bv eq_refl); exact R18 | lia].
    apply negb_false_iff, Z.ltb_lt in Hc. lia. }
  clear Hc.
  paj_run_to_tok RUNTO1 HS HJ SHOK s5b_span 0x508.
  { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
  s5b_after_run KM2.
  assert (KM : forall a, rdW W (ms_mem ms0) a = rdW W mem a) by (intros a; rewrite KM2; apply KM1).
  pmkst HS.
  s5b_kreg HS EE regs ([2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 24]%bv : list (bv 5)) K.
  destruct (s5b_kept cx ly S W regs mem md k acc c m t f (ms_regs ms0) (ms_mem ms0) _ (fun _ => False)
    HB HBODY HCM HSTR HSL HJ ltac:(intros a _ _; apply KM) ltac:(intros a [])
    (K 2%bv ltac:(s5b_inl)) (K 3%bv ltac:(s5b_inl)) (K 4%bv ltac:(s5b_inl)) (K 8%bv ltac:(s5b_inl)) (K 9%bv ltac:(s5b_inl))) as (HB2 & HCM2 & HSTR2 & HSL2).
  apply (HOTH fx1 cx ly S W (ms_regs ms0) (ms_mem ms0) _ k acc c m t lp HB Hfrm Hmore HB2 HCM2 HSTR2
    (s5b_label_full ly S _ _ cx f lp c m KM HLAB)).
  + prreg HS (10%bv : bv 5) P10. rewrite P10, (EE 22%nat 22%bv eq_refl). exact R22.
  + rewrite (K 18%bv ltac:(s5b_inl)). exact R18.
  + rewrite (K 19%bv ltac:(s5b_inl)). exact R19.
  + rewrite (K 21%bv ltac:(s5b_inl)). exact R21.
  + rewrite (K 22%bv ltac:(s5b_inl)). exact R22.
  + rewrite (K 23%bv ltac:(s5b_inl)). exact R23.
  + rewrite (K 24%bv ltac:(s5b_inl)). exact R24.
  + prreg HS (25%bv : bv 5) P25. rewrite P25, (EE 25%nat 25%bv eq_refl), R25. unfold w64.
    rewrite unsigned_lit_small by lia. reflexivity.
  + s5b_rreg HS (26%bv : bv 5) P26. rewrite P26. apply s5b_denot_U.
    rewrite U_SAlu, (U_atom _ 32 (m + seg_spec.MC_N)) by first [exact E32 | unfold seg_spec.MC_N; lia].
    rewrite U_lit by lia. cbn [zalu_raw]. change (Z.land 3 63) with 3.
    rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. apply zcanon_id. unfold M64, seg_spec.MC_N in *.
    pose proof (Z.div_le_upper_bound (m + 8192) 8 (m + 8192) ltac:(lia) ltac:(lia)). pose proof (Z.div_pos (m + 8192) 8 ltac:(lia) ltac:(lia)). lia.
  + exact HSL2.
Qed.

(* the jumps `j 0x852b4` at 0x85290 (after snprintf) and at 0x852ac (after memset), at any FP state *)
Lemma s5b_jump : forall (fx1 : YK11.FPState) (f : nat), S5A_OTH B MT f -> S5A_LST B MT f ->
  forall pc cx ly S (W : world SEGS) regs mem md k acc (c m t lp : Z),
  pc = 0x4d0 \/ pc = 0x4ec ->
  lt_base B MT cx -> sa_frm0 (fx := fx1) -> Z.of_nat f < x_nf cx ->
  S5_body B MT cx ly S W regs mem md k acc LFO_L c m t f ->
  lt_cm (rdW W mem) c m (x_st cx f) -> sa_str (rdW W mem) t (s5_txt (x_pl cx) f) ->
  S5_label B ly S (rdW W mem) cx f lp c m ->
  getr regs 18 = w64 (x_nf cx) -> getr regs 19 = w64 lp -> getr regs 21 = w64 0 -> getr regs 22 = w64 m ->
  getr regs 23 = w64 t -> getr regs 24 = w64 (x_at cx f + x_np cx f) -> getr regs 25 = w64 (Z.of_nat f) ->
  lt_slots cx (rdW W mem) (S5_slots cx c m f) ->
  SRr SEGS W (@cfg_at fx1 SEGS (BASE + pc) regs mem md) (lt_post (fx := fx1) B MT cx).
Proof using All.
intros fx1 f HOTH HLST pc cx ly S W regs mem md k acc c m t lp Hpc HB Hfrm Hf HBODY HCM HSTR HLAB
  R18 R19 R21 R22 R23 R24 R25 HSL.
pose proof (s5b_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi & Hceil0). unfold LTOI_FRAME_MAX in Hs1lo.
pose proof HBODY as ((HF & _) & HHc & HHm & _).
pose proof (proj1 HF) as HJ. pose proof HF as (_ & R2 & R3 & R4 & R8 & R9 & _).
pose proof (proj1 HJ) as HAR.
destruct (al_blocks _ _ LAWS ly S W mem md m _ HAR (proj1 HHm)) as (_ & Hm4096 & Hmceil & _).
pose proof (req_size_pos seg_spec.SEG_M_SIZE ltac:(unfold seg_spec.SEG_M_SIZE; lia)) as [_ Hreqm].
unfold seg_spec.SEG_M_SIZE in Hreqm, Hmceil.
pose proof asan_consts as (C1 & _).
assert (W216 : rdword (rdW W mem) (x_s1 cx + 216) = Some (m + seg_spec.MC_N)).
{ apply HSL. unfold S5_slots, LT_L. apply in_or_app. left. cbn [In]. repeat (first [left; reflexivity | right]). }
assert (EE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr ->
  ew (s5b_E regs [Z_to_bv 64 (m + seg_spec.MC_N)]) n = getr regs rr)
  by (intros n rr Hn; exact (s5b_E_reg regs _ n rr Hn)).
pose proof (s5b_seed fx1 pc 216 (mkFacts [] [] []) W regs mem (x_s1 cx) (m + seg_spec.MC_N)
  ltac:(vm_compute; reflexivity) ltac:(split; [exact I | split; [exact I | exact I]]) R9 ltac:(lia) ltac:(lia)
  ltac:(lia) ltac:(unfold seg_spec.MC_N; lia) W216) as HS.
assert (SHOK : sh_ok SEGS s5b_X [] (s5b_E regs [Z_to_bv 64 (m + seg_spec.MC_N)]) (mrestrict (w_H W) mem))
  by apply Forall_nil.
assert (HEI : img_env VAL A_LIM (s5b_E regs [Z_to_bv 64 (m + seg_spec.MC_N)])) by (unfold s5b_E; apply Eimg_env).
remember (s5b_E regs [Z_to_bv 64 (m + seg_spec.MC_N)]) as E eqn:HE. clear HE.
unfold cfg_at, w64.
pose (RUNTO1 := paj_run_to (fx := fx1) B LAWS).
destruct Hpc as [-> | ->].
- (* 0x85290: j 0x852b4 *)
  paj_run_to_tok RUNTO1 HS HJ SHOK s5b_span 0x4f4.
  { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
  s5b_after_run KM.
  pmkst HS.
  s5b_kreg HS EE regs ([2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 24; 25]%bv : list (bv 5)) K.
  destruct (s5b_kept cx ly S W regs mem md k acc c m t f (ms_regs ms) (ms_mem ms) _ (fun _ => False)
    HB HBODY HCM HSTR HSL HJ ltac:(intros a _ _; apply KM) ltac:(intros a [])
    (K 2%bv ltac:(s5b_inl)) (K 3%bv ltac:(s5b_inl)) (K 4%bv ltac:(s5b_inl)) (K 8%bv ltac:(s5b_inl)) (K 9%bv ltac:(s5b_inl))) as (HB2 & HCM2 & HSTR2 & HSL2).
  apply (s5b_join fx1 f HOTH HLST cx ly S W (ms_regs ms) (ms_mem ms) _ k acc c m t lp HB Hfrm Hf HB2 HCM2 HSTR2
    (s5b_label_full ly S _ _ cx f lp c m KM HLAB)).
  + rewrite (K 18%bv ltac:(s5b_inl)). exact R18.
  + rewrite (K 19%bv ltac:(s5b_inl)). exact R19.
  + rewrite (K 21%bv ltac:(s5b_inl)). exact R21.
  + rewrite (K 22%bv ltac:(s5b_inl)). exact R22.
  + rewrite (K 23%bv ltac:(s5b_inl)). exact R23.
  + rewrite (K 24%bv ltac:(s5b_inl)). exact R24.
  + rewrite (K 25%bv ltac:(s5b_inl)). exact R25.
  + exact HSL2.
- (* 0x852ac: j 0x852b4 *)
  paj_run_to_tok RUNTO1 HS HJ SHOK s5b_span 0x4f4.
  { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
  s5b_after_run KM.
  pmkst HS.
  s5b_kreg HS EE regs ([2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 24; 25]%bv : list (bv 5)) K.
  destruct (s5b_kept cx ly S W regs mem md k acc c m t f (ms_regs ms) (ms_mem ms) _ (fun _ => False)
    HB HBODY HCM HSTR HSL HJ ltac:(intros a _ _; apply KM) ltac:(intros a [])
    (K 2%bv ltac:(s5b_inl)) (K 3%bv ltac:(s5b_inl)) (K 4%bv ltac:(s5b_inl)) (K 8%bv ltac:(s5b_inl)) (K 9%bv ltac:(s5b_inl))) as (HB2 & HCM2 & HSTR2 & HSL2).
  apply (s5b_join fx1 f HOTH HLST cx ly S W (ms_regs ms) (ms_mem ms) _ k acc c m t lp HB Hfrm Hf HB2 HCM2 HSTR2
    (s5b_label_full ly S _ _ cx f lp c m KM HLAB)).
  + rewrite (K 18%bv ltac:(s5b_inl)). exact R18.
  + rewrite (K 19%bv ltac:(s5b_inl)). exact R19.
  + rewrite (K 21%bv ltac:(s5b_inl)). exact R21.
  + rewrite (K 22%bv ltac:(s5b_inl)). exact R22.
  + rewrite (K 23%bv ltac:(s5b_inl)). exact R23.
  + rewrite (K 24%bv ltac:(s5b_inl)). exact R24.
  + rewrite (K 25%bv ltac:(s5b_inl)). exact R25.
  + exact HSL2.
Qed.

(* ================================ the piece: S5_LB f to S5_OTH f / S5_LST f ================================ *)
Lemma s5_label : forall f, S5A_OTH B MT f -> S5A_LST B MT f -> S5_LB_stmt B MT f.
Proof using All.
intros f HOTH HLST. unfold S5_LB_stmt.
intros cx ly S W regs mem md k acc c m t HB Hfrm Hf HBODY HCM HSTR R10 R18 R21 R22 R23 R24 R25 R26 HSL.
pose proof (s5b_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi & Hceil0). unfold LTOI_FRAME_MAX in Hs1lo.
pose proof HBODY as ((HF & HI & _) & _).
pose proof (proj1 HF) as HJ. pose proof HF as (_ & R2 & R3 & R4 & R8 & R9 & _).
pose proof (s5b_frame cx ly S W regs mem md k LFO_L HF) as (_ & _ & Hf4096 & Hfceil & _).
pose proof HB as (HPRE0 & _). pose proof HPRE0 as (_ & _ & _ & Hgp0 & Htp0 & _).
pose proof asan_consts as (C1 & _).
pose proof (s5b_lb_range (x_pl cx) f Hf) as Hlb.
pose proof (s5_label_cases (x_pl cx) f) as Hcases.
set (lb := seg_spec.seg_lb (x_pl cx) f) in *.
assert (W88 : rdword (rdW W mem) (x_s1 cx + 88) = Some (x_fr cx + FO_LABEL)).
{ apply HSL. unfold S5_slots, LT_L. apply in_or_app. left. cbn [In]. repeat (first [left; reflexivity | right]). }
assert (EE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr ->
  ew (s5b_E regs [Z_to_bv 64 (x_fr cx + FO_LABEL)]) n = getr regs rr)
  by (intros n rr Hn; exact (s5b_E_reg regs _ n rr Hn)).
pose proof (s5b_E_32 regs (Z_to_bv 64 (x_fr cx + FO_LABEL)) []) as E32.
pose proof (s5b_seed fx LO_S5LB 88 (mkFacts [] [] []) W regs mem (x_s1 cx) (x_fr cx + FO_LABEL)
  ltac:(vm_compute; reflexivity) ltac:(split; [exact I | split; [exact I | exact I]]) R9 ltac:(lia) ltac:(lia)
  ltac:(lia) ltac:(unfold FO_LABEL; lia) W88) as HS.
assert (SHOK : sh_ok SEGS s5b_X [] (s5b_E regs [Z_to_bv 64 (x_fr cx + FO_LABEL)]) (mrestrict (w_H W) mem))
  by apply Forall_nil.
assert (HEI : img_env VAL A_LIM (s5b_E regs [Z_to_bv 64 (x_fr cx + FO_LABEL)])) by (unfold s5b_E; apply Eimg_env).
pose proof (s5b_obj _ HEI) as (E247 & E246).
remember (s5b_E regs [Z_to_bv 64 (x_fr cx + FO_LABEL)]) as E eqn:HE. clear HE.
unfold cfg_at, w64.
(* 0x8526c: bltz a0 on a0 = lb << 56 *)
psrr_branch_tok RUN BR HS SHOK s5b_span.
- (* taken: lb has bit 7; the longl arm *)
  assert (Hb7 : Z.land lb 128 <> 0).
  { rewrite (s5b_denot_atom E 10 _ (eq_trans (EE 10%nat 10%bv eq_refl) R10)) in Hc. cbn [sv_denot] in Hc.
    unfold w64 in Hc. rewrite s5b_bltz in Hc by exact Hlb. apply negb_true_iff, Z.eqb_neq in Hc. exact Hc. }
  clear Hc.
  assert (Hlab : s5_lab (x_pl cx) f = Some SegModel.longl)
    by (destruct Hcases as [(_ & H) | [(H & _) | (H & _)]]; [exact H | contradiction | contradiction]).
  (* 0x85294 .. 0x852a8: s3 := longl, a1 := 'L', a2 := 120, a0 := s3; jal checked_memset *)
  paj_run_tok RUN HS HJ SHOK s5b_span.
  { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
  s5b_after_run KM1.
  pmkst HS.
  prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
  prreg HS (12%bv : bv 5) P12. prreg HS (19%bv : bv 5) P19.
  s5b_kreg HS EE regs ([2; 3; 4; 8; 9; 18; 21; 22; 23; 24; 25; 26]%bv : list (bv 5)) K.
  destruct (s5b_kept cx ly S W regs mem md k acc c m t f (ms_regs ms) (ms_mem ms) _ (fun _ => False)
    HB HBODY HCM HSTR HSL HJ ltac:(intros a _ _; apply KM1) ltac:(intros a [])
    (K 2%bv ltac:(s5b_inl)) (K 3%bv ltac:(s5b_inl)) (K 4%bv ltac:(s5b_inl)) (K 8%bv ltac:(s5b_inl)) (K 9%bv ltac:(s5b_inl))) as (HB1 & HCM1 & HSTR1 & HSL1).
  pose proof HB1 as ((HF1 & HI1 & _) & _).
  pose proof (proj1 HJ) as HAR1.
  pose proof HI1 as (_ & HIMG1 & _).
  destruct HIMG1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpin1 & _ & _ & _).
  pose proof (Hpin1 ly S W (ms_mem ms) _ HAR1) as (_ & _ & _ & HRA1 & HHV1).
  assert (Hsp1 : spZ (ms_regs ms) = x_s1 cx).
  { unfold spZ. rewrite (K 2%bv ltac:(s5b_inl)), R2. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
  assert (HinL : forall a, longlA <= a < longlA + 120 -> inFP (ltoi_PG longlA) a).
  { intros a Ha. exists (longlA, longlA + LONGL_N). split; [left; reflexivity|]. cbn [fst snd]. unfold LONGL_N. lia. }
  eapply SRr_bind.
  { apply (aj_intrin_atS SEGS B LAWS pa_segs_low OSet (SIG SS___asan_memset) (AMEMSET fx) W (ms_regs ms) (ms_mem ms)
      STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx)
      [(LT_FCLS, x_fpos cx)] ly S _ k longlA 76 120 (x_s1 cx - x_sp0 cx) (Z_to_bv 64 (BASE + 1260)) HJ
      ltac:(rewrite P10; exact E247) P11 P12 ltac:(lia) ltac:(unfold longlA, A_LONGL; lia)
      ltac:(unfold longlA, A_LONGL; lia) ltac:(rewrite Hsp1; lia) ltac:(lia) ltac:(lia)
      ltac:(unfold ESTACK, STK_LLVMFuzzerTestOneInput; lia)
      ltac:(rewrite (K 3%bv ltac:(s5b_inl)), R3; exact Hgp0) ltac:(rewrite (K 4%bv ltac:(s5b_inl)), R4; exact Htp0)
      P1 (ret_ok_codeptr_v 1260 ltac:(lia) eq_refl)).
    - intros a Ha. split.
      + right; right; right; right. left. split; [exact (HinL a Ha) | exact (HPGS a (HinL a Ha))].
      + unfold longlA, A_LONGL, ESTACK in *. lia.
    - intros a Ha Hfp _. apply PRW. exact (proj1 (HPGS a Hfp)).
    - apply a3_amem_img; unfold longlA, A_LONGL, kImgEnd; lia.
    - intros x Hx. apply HRA1. unfold LONGL_N. lia.
    - intros _ s Hs. apply (HHV1 ltac:(unfold LONGL_N; lia)). split; [lia|].
      pose proof (shadow_mono (longlA + 120 - 1) (longlA + LONGL_N - 1) ltac:(unfold LONGL_N; lia)) as Hm.
      assert (shadow_addr (longlA + 120 - 1) / 8 * 8 <= shadow_addr (longlA + LONGL_N - 1) / 8 * 8).
      { apply Z.mul_le_mono_nonneg_r; [lia | apply Z.div_le_mono; lia]. }
      lia.
    - exact I. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HPr & _ & Hset & Hkeep & _ & _).
  assert (PR : forall r z, acallee_saved z -> Z_to_bv 5 z = r -> getr regs2 r = getr (ms_regs ms) r)
    by (intros r z Hz Hr; exact (s5b_pres_reg _ _ r z HPr Hz Hr)).
  destruct (s5b_kept cx ly S W (ms_regs ms) (ms_mem ms) _ k acc c m t f regs2 mem2 md2
    (fun a => (longlA <= a < longlA + 120) \/ (x_s1 cx - ESTACK <= a < x_s1 cx)) HB HB1 HCM1 HSTR1 HSL1 HJ2
    ltac:(intros a Ha Hn; apply Hkeep; [exact Ha | intros H'; apply Hn; left; exact H' |
      intros H'; apply Hn; right; unfold ESTACK in *; lia])
    (s5b_avoid_set cx ly S W (ms_regs ms) (ms_mem ms) _ k LFO_L HB HF1)
    (PR 2%bv 2 ltac:(s5b_cs) ltac:(s5b_cs)) (PR 3%bv 3 ltac:(s5b_cs) ltac:(s5b_cs))
    (PR 4%bv 4 ltac:(s5b_cs) ltac:(s5b_cs)) (PR 8%bv 8 ltac:(s5b_cs) ltac:(s5b_cs))
    (PR 9%bv 9 ltac:(s5b_cs) ltac:(s5b_cs))) as (HB3 & HCM3 & HSTR3 & HSL3).
  assert (HLAB3 : S5_label B ly S (rdW W mem2) cx f longlA c m).
  { apply (s5b_label_longl cx ly S W regs2 mem2 md2 k acc c m t f HB3 Hlab).
    intros i Hi. rewrite (Hset i Hi). reflexivity. }
  apply (s5b_jump fx f HOTH HLST 0x4ec cx ly S W regs2 mem2 md2 k acc c m t longlA (or_intror eq_refl)
    HB Hfrm Hf HB3 HCM3 HSTR3 HLAB3).
  + rewrite (PR 18%bv 18) by s5b_cs. rewrite (K 18%bv ltac:(s5b_inl)). exact R18.
  + rewrite (PR 19%bv 19) by s5b_cs. rewrite P19. exact E247.
  + rewrite (PR 21%bv 21) by s5b_cs. rewrite (K 21%bv ltac:(s5b_inl)). exact R21.
  + rewrite (PR 22%bv 22) by s5b_cs. rewrite (K 22%bv ltac:(s5b_inl)). exact R22.
  + rewrite (PR 23%bv 23) by s5b_cs. rewrite (K 23%bv ltac:(s5b_inl)). exact R23.
  + rewrite (PR 24%bv 24) by s5b_cs. rewrite (K 24%bv ltac:(s5b_inl)). exact R24.
  + rewrite (PR 25%bv 25) by s5b_cs. rewrite (K 25%bv ltac:(s5b_inl)). exact R25.
  + exact HSL3.
- (* not taken: lb < 128 *)
  assert (Hb7 : Z.land lb 128 = 0).
  { rewrite (s5b_denot_atom E 10 _ (eq_trans (EE 10%nat 10%bv eq_refl) R10)) in Hc. cbn [sv_denot] in Hc.
    unfold w64 in Hc. rewrite s5b_bltz in Hc by exact Hlb. apply negb_false_iff, Z.eqb_eq in Hc. exact Hc. }
  clear Hc.
  (* 0x8526c, not taken: to the beqz s10 at 0x85270 *)
  paj_run_tok RUN HS HJ SHOK s5b_span.
  { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
  s5b_after_run KM1.
  psrr_branch_tok RUN BR HS SHOK s5b_span.
  + (* lb = 0: s3 := 0 at 0x852b0, to the join at 0x852b4 *)
    assert (Hz : lb = 0).
    { rewrite branch_eq_U in Hc.
      rewrite (U_atom E 26 lb) in Hc by first [rewrite (EE 26%nat 26%bv eq_refl); exact R26 | lia].
      rewrite U_lit in Hc by lia. apply Z.eqb_eq in Hc. exact Hc. }
    clear Hc.
    assert (Hlab : s5_lab (x_pl cx) f = None)
      by (destruct Hcases as [(H & _) | [(_ & _ & H) | (_ & H & _)]]; [contradiction | exact H | contradiction]).
    paj_run_to_tok RUNTO HS HJ SHOK s5b_span 0x4f4.
    { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
    s5b_after_run KM2.
    assert (KM : forall a, rdW W (ms_mem ms0) a = rdW W mem a) by (intros a; rewrite KM2; apply KM1).
    pmkst HS.
    prreg HS (19%bv : bv 5) P19.
    s5b_kreg HS EE regs ([2; 3; 4; 8; 9; 18; 21; 22; 23; 24; 25]%bv : list (bv 5)) K.
    destruct (s5b_kept cx ly S W regs mem md k acc c m t f (ms_regs ms0) (ms_mem ms0) _ (fun _ => False)
      HB HBODY HCM HSTR HSL HJ ltac:(intros a _ _; apply KM) ltac:(intros a [])
      (K 2%bv ltac:(s5b_inl)) (K 3%bv ltac:(s5b_inl)) (K 4%bv ltac:(s5b_inl)) (K 8%bv ltac:(s5b_inl)) (K 9%bv ltac:(s5b_inl))) as (HB2 & HCM2 & HSTR2 & HSL2).
    apply (s5b_join fx f HOTH HLST cx ly S W (ms_regs ms0) (ms_mem ms0) _ k acc c m t 0 HB Hfrm Hf HB2 HCM2 HSTR2
      (s5b_label_none ly S _ cx f c m Hlab)).
    * rewrite (K 18%bv ltac:(s5b_inl)). exact R18.
    * rewrite P19. reflexivity.
    * rewrite (K 21%bv ltac:(s5b_inl)). exact R21.
    * rewrite (K 22%bv ltac:(s5b_inl)). exact R22.
    * rewrite (K 23%bv ltac:(s5b_inl)). exact R23.
    * rewrite (K 24%bv ltac:(s5b_inl)). exact R24.
    * rewrite (K 25%bv ltac:(s5b_inl)). exact R25.
    * exact HSL2.
  + (* lb in 1 .. 127: the snprintf arm *)
    assert (Hnz : lb <> 0).
    { rewrite branch_eq_U in Hc.
      rewrite (U_atom E 26 lb) in Hc by first [rewrite (EE 26%nat 26%bv eq_refl); exact R26 | lia].
      rewrite U_lit in Hc by lia. apply Z.eqb_neq in Hc. exact Hc. }
    clear Hc.
    pose proof (s5b_land128 lb Hlb Hb7) as Hlt.
    assert (Hlb' : 1 <= lb <= 127) by lia.
    assert (Hlab : s5_lab (x_pl cx) f = Some (SegModel.fmt SegModel.F_label [SegModel.AI lb])).
    { destruct Hcases as [(H & _) | [(_ & H & _) | (_ & _ & H)]]; [contradiction | contradiction |].
      rewrite H. f_equal. exact (s5b_snprintf_s lb Hlb'). }
    (* 0x85274 .. 0x8528c: a2 := the format, a1 := 40, s3 := 88(s1) = &label, a0 := s3, a3 := lb; jal snprintf *)
    paj_run_tok RUN HS HJ SHOK s5b_span.
    { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
    s5b_after_run KM2.
    assert (KM : forall a, rdW W (ms_mem ms0) a = rdW W mem a) by (intros a; rewrite KM2; apply KM1).
    pmkst HS.
    prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
    prreg HS (12%bv : bv 5) P12. prreg HS (13%bv : bv 5) P13. prreg HS (19%bv : bv 5) P19.
    s5b_kreg HS EE regs ([2; 3; 4; 8; 9; 18; 21; 22; 23; 24; 25; 26]%bv : list (bv 5)) K.
    destruct (s5b_kept cx ly S W regs mem md k acc c m t f (ms_regs ms0) (ms_mem ms0) _ (fun _ => False)
      HB HBODY HCM HSTR HSL HJ ltac:(intros a _ _; apply KM) ltac:(intros a [])
      (K 2%bv ltac:(s5b_inl)) (K 3%bv ltac:(s5b_inl)) (K 4%bv ltac:(s5b_inl)) (K 8%bv ltac:(s5b_inl)) (K 9%bv ltac:(s5b_inl))) as (HB2 & HCM2 & HSTR2 & HSL2).
    pose proof HB2 as ((HF2 & HI2 & _) & _).
    eapply SRr_bind.
    { exact (s5b_snp_call cx ly S W (ms_regs ms0) (ms_mem ms0) _ k lb (Z_to_bv 64 (BASE + 1232)) HB Hfrm HF2 HI2 Hlb'
        ltac:(rewrite P10; exact E32) P11 ltac:(rewrite P12; exact E246)
        ltac:(rewrite P13, (EE 26%nat 26%bv eq_refl); exact R26) P1 (ret_ok_codeptr_v 1232 ltac:(lia) eq_refl)). }
    cbv beta. intros W2 c2 _ (-> & fx1 & regs2 & mem2 & md2 & Hfx & -> & HJ2 & HPr & Hbytes & Hkeep).
    assert (PR : forall r z, acallee_saved z -> Z_to_bv 5 z = r -> getr regs2 r = getr (ms_regs ms0) r)
      by (intros r z Hz Hr; exact (s5b_pres_reg _ _ r z HPr Hz Hr)).
    destruct (s5b_kept cx ly S W (ms_regs ms0) (ms_mem ms0) _ k acc c m t f regs2 mem2 md2
      (fun a => (x_fr cx + FO_LABEL <= a < x_fr cx + FO_LABEL + 40) \/ (x_s1 cx - 2 * ESTACK <= a < x_s1 cx))
      HB HB2 HCM2 HSTR2 HSL2 HJ2
      ltac:(intros a Ha Hn; apply Hkeep; [exact Ha | intros H'; apply Hn; left; exact H' |
        intros H'; apply Hn; right; exact H'])
      (s5b_avoid_snp cx ly S W (ms_regs ms0) (ms_mem ms0) _ k LFO_L HB HF2)
      (PR 2%bv 2 ltac:(s5b_cs) ltac:(s5b_cs)) (PR 3%bv 3 ltac:(s5b_cs) ltac:(s5b_cs))
      (PR 4%bv 4 ltac:(s5b_cs) ltac:(s5b_cs)) (PR 8%bv 8 ltac:(s5b_cs) ltac:(s5b_cs))
      (PR 9%bv 9 ltac:(s5b_cs) ltac:(s5b_cs))) as (HB3 & HCM3 & HSTR3 & HSL3).
    pose proof (s5b_label_snp cx ly S W regs2 mem2 md2 k acc c m t f lb HB HB3 Hlb' Hlab Hbytes) as HLAB3.
    unfold lt_post. apply (srr_apost_baseF_lift SEGS fx1); [exact Hfx|].
    apply (s5b_jump fx1 f HOTH HLST 0x4d0 cx ly S W regs2 mem2 md2 k acc c m t (x_fr cx + FO_LABEL) (or_introl eq_refl)
      HB (fxrel_frm0 fx fx1 Hfrm Hfx) Hf HB3 HCM3 HSTR3 HLAB3).
    * rewrite (PR 18%bv 18) by s5b_cs. rewrite (K 18%bv ltac:(s5b_inl)). exact R18.
    * rewrite (PR 19%bv 19) by s5b_cs. rewrite P19. exact E32.
    * rewrite (PR 21%bv 21) by s5b_cs. rewrite (K 21%bv ltac:(s5b_inl)). exact R21.
    * rewrite (PR 22%bv 22) by s5b_cs. rewrite (K 22%bv ltac:(s5b_inl)). exact R22.
    * rewrite (PR 23%bv 23) by s5b_cs. rewrite (K 23%bv ltac:(s5b_inl)). exact R23.
    * rewrite (PR 24%bv 24) by s5b_cs. rewrite (K 24%bv ltac:(s5b_inl)). exact R24.
    * rewrite (PR 25%bv 25) by s5b_cs. rewrite (K 25%bv ltac:(s5b_inl)). exact R25.
    * exact HSL3.
Qed.


End eb.
End fb.
End db.

(* ============================================== piece L3 (c) ============================================== *)
(* reac-pw/fuzz_segconf, ASan+UBSan image B (fuzz_segconf.asan-ubsan, pin sha256 c3796c0b38f3): piece L3 of
   segment S05 of the test harness's entry function LLVMFuzzerTestOneInput (0x84dc0):
     s5_last : forall f, LTA_K85338 B MT f -> S5_LST_stmt B MT f
   (the kit LLVMFuzzerTestOneInput_s15k.v states S5_LST_stmt; the defs file LTA_K85338).

   The code (dis/LLVMFuzzerTestOneInput.fuzz_segconf.asan-ubsan.s lines 347-351, listing SegList.v slots 345-349):
     85324 sd   s8,144(s1)     144(s1) := P1 + NP          (slot 345, PW 0x984b823)
     85328 mv   a0,s6          a0 := m                     (slot 346, PW 0xb0513)
     8532c mv   a1,s7          a1 := t                     (slot 347, PW 0xb8593)
     85330 li   a2,0           a2 := 0, no label           (slot 348, PW 0x613)
     85334 jal  m_file         m_file(m, text, NULL)       (slot 349, PCall SS_m_file; m_file at 0x86140 =
                                                            BASE + AF_m_file, AF_m_file = 0x1380)
     85338 = K85338 f          (LO_K85338 = 0x578)

   THE FORM: one token run (paj_run_tok) from the cut to the jal, with one write window 144(s1) .. 152(s1) based at
   the s1 atom; then the program call through PaFx.cl_callSF with image B's m_file contract (Section hypothesis
   HM_FILE, lib/B/Prog/m_file_c.v) at the segment's FP state, lifted by PaFx.srr_after_callF; the caller's facts
   carried past the call by the callee's journal (its keep clauses: the stack above S1, the class-3 frame and its
   shadow, the image bytes, the live blocks outside M_FILE_FP, which lies inside the mconf block m), and the
   counters of K85338 from m_file_c.v's m_file_gen / m_file_refused / m_file_overflow. The carrying lemmas are the
   image-B twins of the S01 / S02 walk's (image B's S01 / S02 commit c9accd8a8a50, LLVMFuzzerTestOneInput_s12k.v:
   lk_sp, lk_hblk, lk_img_kept, lk_core_run) and the S03 walk's of image A (image A's S03 commit efe4db8b7b60:
   s13_not_entry, s13_chunk_word, s13_U_atom); the program call is METHOD.md section 4.6's pattern. *)
(* ======================================== pure facts ======================================== *)
(* nfiles is 1 .. 4 (the _s02.v lemma lt_nfiles_range, which this file does not Require) *)
Lemma s5c_nfiles_range : forall pl, 1 <= seg_spec.seg_nfiles pl <= 4.
Proof.
intros pl. unfold seg_spec.seg_nfiles, seg_spec.seg_files, seg_spec.seg_pay, SegModel.decode.
destruct (SegModel.fuzz_u8 (seg_spec.seg_in pl)) as [b0 i1].
destruct (SegModel.fuzz_u8 i1) as [fl i2]. destruct (SegModel.fuzz_u8 i2) as [b2 i3].
cbn [SegModel.p_files]. rewrite s5_dec_files_length.
pose proof (Z.mod_pos_bound b2 4 ltac:(lia)) as H. rewrite Z2Nat.id by lia. lia.
Qed.

(* the bounds the mconf encoding asks (seg_spec.mconf_encp): at most 32 entries and 8 kept refusals *)
Definition s5c_mok (c : SegModel.mconf) : Prop :=
  (length (SegModel.mc_seg c) <= 32)%nat /\ (length (SegModel.mc_kept c) <= 8)%nat.
Lemma s5c_upd_nth_len : forall {A : Type} (i : nat) (g : A -> A) (l : list A),
  length (SegModel.upd_nth i g l) = length l.
Proof.
intros A i g l. revert i. induction l as [|x r IH]; intros [|i]; cbn [SegModel.upd_nth length]; try reflexivity.
rewrite IH. reflexivity.
Qed.
Lemma s5c_refuse_ok : forall c line knock, s5c_mok c -> s5c_mok (SegModel.m_refuse c line knock).
Proof.
intros c line knock [H1 H2]. unfold s5c_mok, SegModel.m_refuse. cbv zeta.
cbn [SegModel.mc_seg SegModel.mc_kept]. split; [exact H1|].
destruct (Z.of_nat (length (SegModel.mc_kept c)) <? 8) eqn:E; cbv beta iota.
- apply Z.ltb_lt in E. rewrite length_app. cbn [length]. lia.
- exact H2.
Qed.
Lemma s5c_upd_ok : forall c i g, s5c_mok c -> s5c_mok (SegModel.m_upd c i g).
Proof.
intros c i g [H1 H2]. unfold s5c_mok, SegModel.m_upd, SegModel.m_set_segs.
cbn [SegModel.mc_seg SegModel.mc_kept]. rewrite s5c_upd_nth_len. split; assumption.
Qed.
Lemma s5c_header_ok : forall c l line, s5c_mok c -> s5c_mok (fst (SegModel.m_header c l line)).
Proof.
intros c l line Hc. unfold SegModel.m_header. cbv zeta.
destruct (SegModel.memchr l SegModel.RBR) as [ci|]; cbv beta iota; [|cbn [fst]; apply s5c_refuse_ok; exact Hc].
repeat match goal with
  | |- context [if ?b then _ else _] => let E := fresh "E" in destruct b eqn:E; cbv beta iota
  | |- context [SegModel.m_find ?a ?b] => destruct (SegModel.m_find a b); cbv beta iota
  end; cbn [fst];
first
  [ apply s5c_refuse_ok; exact Hc
  | apply s5c_upd_ok; apply s5c_refuse_ok; exact Hc
  | apply s5c_upd_ok; exact Hc
  | match goal with E : (32 <=? _)%nat = false |- _ => apply Nat.leb_gt in E end;
    destruct Hc as [H1 H2]; unfold s5c_mok, SegModel.m_set_segs; cbn [SegModel.mc_seg SegModel.mc_kept];
    rewrite length_app; cbn [length]; split; lia ].
Qed.
Lemma s5c_key_ok : forall c g l line, s5c_mok c -> s5c_mok (SegModel.m_key c g l line).
Proof.
intros c g l line Hc. unfold SegModel.m_key. cbv zeta.
destruct (SegModel.memchr l SegModel.EQ) as [ei|]; destruct g as [gi|]; cbv beta iota;
  try (apply s5c_refuse_ok; exact Hc).
repeat match goal with
  | |- context [if ?b then _ else _] => let E := fresh "E" in destruct b eqn:E; cbv beta iota
  | |- context [SegModel.h_role_word ?a] => destruct (SegModel.h_role_word a); cbv beta iota
  | |- context [SegModel.cat_row ?a] => destruct (SegModel.cat_row a); cbv beta iota
  end;
first [apply s5c_upd_ok; exact Hc | apply s5c_refuse_ok; exact Hc].
Qed.
Lemma s5c_line_ok : forall st line l, s5c_mok (fst st) -> s5c_mok (fst (SegModel.m_line st line l)).
Proof.
intros [c cur] line l Hc. cbn [fst] in Hc. unfold SegModel.m_line. cbv beta iota zeta.
destruct (512 <=? length l)%nat; cbv beta iota; [cbn [fst]; apply s5c_refuse_ok; exact Hc|].
destruct (SegModel.h_strip (SegModel.h_cut_comment l)) as [|b s]; cbv beta iota; [cbn [fst]; exact Hc|].
destruct (b =? SegModel.LBR); cbv beta iota; [apply s5c_header_ok; exact Hc | cbn [fst]; apply s5c_key_ok; exact Hc].
Qed.
Lemma s5c_lines_ok : forall ls st n, s5c_mok (fst st) -> s5c_mok (fst (SegModel.m_lines st n ls)).
Proof.
induction ls as [|l r IH]; intros st n Hs; cbn [SegModel.m_lines]; [exact Hs|].
apply IH. apply s5c_line_ok. exact Hs.
Qed.
Lemma s5c_mfile_ok : forall c s lab, s5c_mok c -> s5c_mok (SegModel.m_file c s lab).
Proof. intros c s lab Hc. unfold SegModel.m_file. cbv zeta. apply s5c_lines_ok. exact Hc. Qed.

(* m_file's footprint lies in the mconf block when the final model has the encoding's bounds *)
Lemma s5c_mfp_in : forall m k0 mc, s5c_mok mc ->
  forall a, inFP (M_FILE_FP m k0 mc) a -> m <= a < m + seg_spec.SEG_M_SIZE.
Proof.
intros m k0 mc [L1 L2] a (r & Hr & Ha). unfold M_FILE_FP in Hr. cbn [In] in Hr.
unfold seg_spec.mseg_addr, seg_spec.kept_addr, seg_spec.MSEG_SIZE, seg_spec.MC_N, seg_spec.MC_REFUSED,
  seg_spec.MC_KEPT, seg_spec.MC_KEPT_LEN, seg_spec.MC_KNOCK, seg_spec.MC_NKEPT, seg_spec.MC_READING,
  seg_spec.SEG_M_SIZE in *.
repeat (destruct Hr as [Hr | Hr]; [subst r; cbn [fst snd] in Ha; lia |]). destruct Hr.
Qed.

(* the turn's text is at most 65535 bytes (the u16 of its length) *)
Lemma s5c_land16 : forall x, Z.land x 65535 <= 65535.
Proof.
intros x. pose proof (Z.land_ones x 16 ltac:(lia)) as E. change (Z.ones 16) with 65535 in E. rewrite E.
change (2 ^ 16) with 65536. pose proof (Z.mod_pos_bound x 65536 ltac:(lia)) as Hm. lia.
Qed.
Lemma s5c_txt_len : forall pl f, Z.of_nat f < seg_spec.seg_nfiles pl ->
  Z.of_nat (length (seg_spec.seg_txt pl f)) <= 65535.
Proof.
intros pl f Hf. destruct (s5_txt_firstn pl f Hf) as (_ & H1 & _).
assert (Hnp : (Z.to_nat (seg_spec.seg_turn_np pl f) <= Z.to_nat (seg_spec.seg_turn_len pl f))%nat).
{ unfold seg_spec.seg_turn_np. rewrite s5_take_fst, length_firstn, Nat2Z.id. lia. }
assert (Hl : seg_spec.seg_turn_len pl f <= 65535).
{ unfold seg_spec.seg_turn_len, SegModel.fuzz_u16.
  destruct (SegModel.fuzz_u8 (snd (SegModel.fuzz_u8 (seg_spec.seg_cur pl f)))) as [lo i1].
  destruct (SegModel.fuzz_u8 i1) as [hi i2]. cbn [fst]. apply s5c_land16. }
lia.
Qed.

(* lists, words, registers, readers *)
Lemma s5c_perm_dup : forall {A : Type} (o1 o2 l1 l2 : list A) x,
  Permutation (x :: x :: (o1 ++ o2 ++ l1 ++ l2)) ((o1 ++ x :: o2) ++ l1 ++ x :: l2).
Proof.
intros A o1 o2 l1 l2 x. rewrite <- app_assoc. cbn [app].
apply Permutation_cons_app.
replace (o1 ++ o2 ++ l1 ++ x :: l2) with ((o1 ++ o2 ++ l1) ++ x :: l2) by (rewrite <- !app_assoc; reflexivity).
apply Permutation_cons_app. rewrite <- !app_assoc. reflexivity.
Qed.
Lemma s5c_pres_reg : forall regs regs' (r : bv 5) z,
  aregs_preserved regs regs' -> acallee_saved z -> Z_to_bv 5 z = r -> getr regs' r = getr regs r.
Proof. intros regs regs' r z HP Hz <-. exact (HP z Hz). Qed.
Lemma s5c_word_kept : forall (rd rd' : reader) a v,
  (forall x, a <= x < a + 8 -> rd' x = rd x) -> rdword rd a = Some v -> rdword rd' a = Some v.
Proof. intros rd rd' a v HK H. rewrite (rdword_ext rd rd' a); [exact H|]. intros k Hk. apply HK. lia. Qed.
Lemma s5c_rdword_some : forall (rd : reader) a, (forall k, 0 <= k < 8 -> rd (a + k) <> None) ->
  exists v, rdword rd a = Some v.
Proof.
intros rd a H. unfold rdword.
pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
pose proof (H 1 ltac:(lia)) as H1. pose proof (H 2 ltac:(lia)) as H2. pose proof (H 3 ltac:(lia)) as H3.
pose proof (H 4 ltac:(lia)) as H4. pose proof (H 5 ltac:(lia)) as H5. pose proof (H 6 ltac:(lia)) as H6.
pose proof (H 7 ltac:(lia)) as H7.
destruct (rd a) as [b0|]; [|congruence]. destruct (rd (a + 1)) as [b1|]; [|congruence].
destruct (rd (a + 2)) as [b2|]; [|congruence]. destruct (rd (a + 3)) as [b3|]; [|congruence].
destruct (rd (a + 4)) as [b4|]; [|congruence]. destruct (rd (a + 5)) as [b5|]; [|congruence].
destruct (rd (a + 6)) as [b6|]; [|congruence]. destruct (rd (a + 7)) as [b7|]; [|congruence].
eexists; reflexivity.
Qed.
Lemma s5c_rconf_xfer : forall (rd rd' : reader) c rc,
  (forall i, 0 <= i < seg_spec.SEG_C_SIZE -> rd' (c + i) = rd (c + i)) -> sa_rconf rd c rc -> sa_rconf rd' c rc.
Proof.
intros rd rd' c rc K (bs & Hb & He). exists bs. split; [|exact He].
intros i Hi. destruct He as (HL & _). rewrite K by lia. exact (Hb i Hi).
Qed.
Lemma s5c_mconf_xfer : forall (rd rd' : reader) a mc,
  (forall i, 0 <= i < seg_spec.SEG_M_SIZE -> rd' (a + i) = rd (a + i)) -> sa_mconf rd a mc -> sa_mconf rd' a mc.
Proof.
intros rd rd' a mc K (bs & Hb & He). exists bs. split; [|exact He].
intros i Hi. destruct He as (HL & _). rewrite K by lia. exact (Hb i Hi).
Qed.
Lemma s5c_strz_xfer : forall (rd rd' : reader) p s,
  (forall i, 0 <= i <= Z.of_nat (length s) -> rd' (p + i) = rd (p + i)) -> sa_strz rd p s -> sa_strz rd' p s.
Proof.
intros rd rd' p s K (HZ & HN). split; [|exact HN].
intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. rewrite K by lia. exact (HZ i ltac:(rewrite length_app; cbn [length]; lia)).
Qed.

(* the run's write window: the slot 144(s1) *)
Definition s5c_w (s1 a : Z) : Prop := s1 + 144 <= a < s1 + 152.
Definition s5c_X : sv := SOff 5 0.
Definition s5c_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition s5c_rg : smem := [YP09.mkRegion (Some 9%nat) 144 152 144 152 []].
(* the s1 atom's range and alignment: the token runner's static check keeps the write window apart from the shadow
   band with it (image A's S03 walk's s13_fa2) *)
Definition s5c_fa : facts := mkFacts [ (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5) ] [] [].
Definition s5c_ss : sstate := mkSS LO_S5LST sr_atoms s5c_rg None s5c_fa.

Section dc. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section fc.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section ec.
Variable B : asyms.
Variable MT : ameter_ops.
(* the image range the snprintf row's dest_off_globals uses, and the read-only ranges it reads; the S11 walk
   (the probe snprintf) takes the same three names and the same five HSNP_ hypotheses *)
Variable snp_lo snp_hi : Z.
Variable snp_cr : list (Z * Z).
(* AR's laws are a theorem of image B's kit, not a hypothesis *)
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis PRW : prog_rw SEGS B.
Hypothesis VOBJS : seg_val_objs.
Hypothesis SIGP : seg_sig_prog.
(* image B's per-image record (lib/B/Prog/SegRecBase.v, the image-B listing owner's commit c4abdaee306f, merged into
   this walk's integration commit da997fa1859d): the image facts lt_img needs at a reader after a call, each a field.
   It SUPERSEDES the three hypotheses IMG_RELRO / IMG_GOTW / IMG_GUARD an earlier version of this brief had.
   Never weaken lt_img instead. *)
Hypothesis IMGF : seg_img_facts SEGS B.
(* the allocator record's symbols at image B's values (lib/B/YF0m.v): with AR it gives the stack-protector
   cells at every state (SegRecCells.seg_rec_cells), since the runtime owns the .got word gotwA *)
Hypothesis HBS : YF0m.SegBSyms B.
(* longl's bytes are the program's own writable static, in the image and outside RELRO (the memset arm writes
   them), and no model-table pointer reaches within 65536 of longl (image A's S05 header takes the same
   three; they are what the longl arm and the literals' survival need) *)
Hypothesis HPGS : forall a, inFP (ltoi_PG longlA) a ->
  Exists (in_zr a) (as_prog_static B) /\ in_img SEGS a.
Hypothesis HPG_RO : forall a, inFP (ltoi_PG longlA) a -> ~ in_roP SEGS RLO_A RHI_A a.
Hypothesis HPG_PTR : forall a p,
  ((exists i, (i < 5)%nat /\ a = wordsA + 8 * Z.of_nat i) \/
   (exists i, (i < pin_spec.CAT_N)%nat /\ a = pin_spec.row_addr catA i)) ->
  rdword (fun x => option_map (fun b : byte => bv_unsigned b) (seg_rom SEGS (Z_to_bv 64 x))) a = Some p ->
  p + 65536 <= longlA.
(* the runtime entries S05 calls *)
Hypothesis AMEMCPY : forall fx0 : YK11.FPState, aintrin_realizes (fx := fx0) SEGS B OCpy (SIG SS___asan_memcpy).
Hypothesis AMEMSET : forall fx0 : YK11.FPState, aintrin_realizes (fx := fx0) SEGS B OSet (SIG SS___asan_memset).
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState,
  RtPFSeg.seg_asnprintf_realizes (fx := fx0) SEGS B snp_lo snp_hi snp_cr
    (SIG SS___interceptor_trampoline_snprintf) gotwA guardA.
Hypothesis AFREE4 : forall fx0 : YK11.FPState, afree04_rule (fx := fx0) SEGS B MT.
(* what image B's close shows of snp_lo / snp_hi / snp_cr; each is a computation there *)
Hypothesis HSNP_LIT : forall x, In x LLVMFuzzerTestOneInput_c.LTOI_LITS ->
  snp_lo <= seg_litA_fz x /\ seg_litA_fz x + Z.of_nat (length x) + 1 <= gotwA.
Hypothesis HSNP_CR : Forall (fun r => snp_lo <= fst r /\ 0 <= snd r /\ fst r + snd r <= snp_hi) snp_cr.
Hypothesis HSNP_LO : 0 <= snp_lo.
Hypothesis HSNP_CEIL : snp_hi <= alloc_ceiling.
Hypothesis HSNP_FAKE : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> snp_hi <= ly_F ly.
(* the two program callees, at every FP state *)
Hypothesis HM_FILE : forall fx0 : YK11.FPState,
  m_file_c.m_file_contract (fx := fx0) SEGS B (BASE + AF_m_file) STK_m_file RLO_A RHI_A seg_litA_fz
    wordsA rolesA catA gotwA guardA.
Hypothesis HPARSE_FILE : forall fx0 : YK11.FPState,
  reac_segconf_parse_file_c.reac_segconf_parse_file_contract (fx := fx0) SEGS B
    (BASE + AF_reac_segconf_parse_file) STK_reac_segconf_parse_file RLO_A RHI_A seg_litA_rc catA gotwA guardA.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* the three image facts lt_img needs at a reader after a call, each from a field of IMGF (image A's S00 walk
   takes the same three as its record s10_img); this text compiled on the VM, log build-20261030T183150Z.log. *)
Lemma s5c_relro : forall a, RLO_A <= a < RHI_A -> in_img SEGS a.
Proof. exact (cif_relro_img _ _ IMGF). Qed.

(* the slot offsets of the statements S5_LST and K85338 *)
Lemma s5c_slots_off : forall cx c m f o v, In (o, v) (S5_slots cx c m f) ->
  16 <= o <= 216 /\ (o + 8 <= 144 \/ 152 <= o).
Proof using All.
intros cx c m f o v H. unfold S5_slots, LT_L in H. cbn [In app] in H.
repeat (destruct H as [H | H]; [injection H as <- _; lia |]). destruct H.
Qed.
Lemma s5c_slots_off2 : forall cx c m o v w1 w2 w3 w4,
  In (o, v) (LT_L cx c m ++ [(144, w1); (152, w2); (160, w3); (176, w4)]) -> 16 <= o <= 216.
Proof using All.
intros cx c m o v w1 w2 w3 w4 H. unfold LT_L in H. cbn [In app] in H.
repeat (destruct H as [H | H]; [injection H as <- _; lia |]). destruct H.
Qed.

(* ---------------------------------- the walk's own frame and blocks ---------------------------------- *)
(* the entry sp and the realigned base S1 (andi sp,sp,-32 at 0x84e00 after addi sp,sp,-352) *)
Lemma s5c_sp : forall cx, lt_base B MT cx ->
  x_sp0 cx mod 16 = 0 /\ alloc_ceiling + STK_LLVMFuzzerTestOneInput <= x_sp0 cx /\ x_sp0 cx <= 2 ^ 47 /\
  x_s1 cx mod 32 = 0 /\ x_sp0 cx - LTOI_FRAME_MAX <= x_s1 cx /\ x_s1 cx <= x_sp0 cx - 352.
Proof using All.
intros cx HB. destruct HB as (HPRE & _). destruct HPRE as (_ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal & _ & Hceil & Hslo & Hshi & H47 & _).
unfold x_s1, x_sp0, LT_FRAME, LTOI_FRAME_MAX in *.
set (s := spZ (x_regs cx)) in *. clearbody s.
repeat split; lia.
Qed.
(* the frame address of a journal's target layout is the entry's *)
Lemma s5c_frame_addr : forall STK sp0 FP ly0 S0 W0 mem0 md0 own ly S (W : world SEGS) mem md k,
  ajournal SEGS B STK sp0 FP ly0 S0 W0 mem0 md0 own ly S W mem md k ->
  forall cid pos, frame_addr ly cid pos = frame_addr ly0 cid pos.
Proof using All.
intros STK sp0 FP ly0 S0 W0 mem0 md0 own ly S W mem md k HJ cid pos.
destruct HJ as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & EF & _). unfold frame_addr. rewrite EF. reflexivity.
Qed.
(* a live block of a state is a harness block of that state *)
Lemma s5c_hblk : forall ly S (W : world SEGS) mem md a n,
  AR SEGS B ly S W mem md -> In (a, n) (ablocks B ly S) -> lt_hblk B ly S (rdW W mem) a n.
Proof using All.
intros ly S W mem md a n HAR Hin.
destruct (al_blocks _ _ LAWS ly S W mem md a n HAR Hin) as (H16 & H4096 & Hceil & _ & _ & _ & Hn).
pose proof (req_size_pos n ltac:(lia)) as [_ Hreq].
pose proof asan_consts as (C1 & _).
split; [exact Hin|]. split; [exact H4096|]. split; [exact H16|].
split; [lia|]. split; [lia|].
split; [exact (amem_range_of_block SEGS B LAWS ly S W mem md a n a n HAR Hin ltac:(lia) ltac:(lia))|].
split; [exact (range_addressable_of_block SEGS B LAWS ly S W mem md a n a n HAR Hin ltac:(lia) ltac:(lia))|].
intros Hn0. exact (shadow_hull_vis_of_block SEGS B LAWS ly S W mem md a n a n HAR Hin ltac:(lia) ltac:(lia) Hn0).
Qed.
(* a block the harness made is not one of the entry's *)
Lemma s5c_not_entry : forall ly S (W : world SEGS) mem md O x l, AR SEGS B ly S W mem md ->
  Permutation (ablocks B ly S) (O ++ l) -> In x O -> 0 < req_size (snd x) -> ~ In x l.
Proof using All.
intros ly S W mem md O x l HAR HP HO Hr Hl.
apply in_split in HO as (o1 & o2 & ->). apply in_split in Hl as (l1 & l2 & ->).
pose proof (sep_blocks_perm SEGS B LAWS ly S W mem md x x _ HAR
  (Permutation_trans HP (Permutation_sym (s5c_perm_dup o1 o2 l1 l2 x)))) as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. lia.
Qed.
(* a ROM byte is shown by every reader *)
Lemma s5c_rom_view_some : forall (H : word -> bool) mem a, seg_rom SEGS (Z_to_bv 64 a) <> None -> aview SEGS H mem a <> None.
Proof using All.
intros H mem a Hr. unfold aview, mbyte. destruct (mrestrict H mem (Z_to_bv 64 a)) as [b|]; [cbn; discriminate|].
destruct (seg_rom SEGS (Z_to_bv 64 a)) as [b|] eqn:E; [cbn; discriminate | congruence].
Qed.

(* ------------------------------------- the image facts carried ------------------------------------- *)
Lemma s5c_lit_kept : forall (W W' : world SEGS) mem mem' a s,
  (forall x, a <= x < a + (Z.of_nat (length s) + 1) -> rdW W' mem' x = rdW W mem x) ->
  sa_lit SEGS B (rdW W mem) a s -> sa_lit SEGS B (rdW W' mem') a s.
Proof using All.
intros W W' mem mem' a s HK (Ha & ((Hzs & Hn0) & _) & Hpin & Hrt & Himg).
split; [exact Ha|]. split; [split; [split; [|exact Hn0] | exact (sa_tail_of_romtail SEGS (w_H W') mem' _ Hrt)]|].
- intros i Hi. rewrite HK; [exact (Hzs i Hi)|]. rewrite length_app in Hi. cbn [length] in Hi. lia.
- split; [exact Hpin|]. split; [exact Hrt | exact Himg].
Qed.
(* the stack-protector cells at a later reader: re-derived from AR at that state by SegRecCells.seg_rec_cells
   (owner's brief decision 12; the runtime owns the .got word gotwA, so image B's SegRo no longer lists it and
   no agreement on unowned image bytes reaches it). The two earlier-state premises are kept so the callers do
   not change. *)
Lemma s5c_ssp_kept : forall (W W' : world SEGS) mem mem' ly' S' md',
  AR SEGS B ly' S' W' mem' md' ->
  sa_ssp (rdW W mem) gotwA guardA ->
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     rdW W' mem' a = rdW W mem a) ->
  sa_ssp (rdW W' mem') gotwA guardA.
Proof using All.
intros W W' mem mem' ly' S' md' HAR' _ _.
exact (proj1 (proj2 (SegRecCells.seg_rec_cells SEGS B LAWS HBS IMGF ly' S' W' mem' md' HAR'))).
Qed.
(* lt_img at a later reader that keeps every image byte the runtime does not own (the S01 / S02 walk's lk_img_kept; the
   stack-protector cells by s5c_ssp_kept, the guard's ROM bytes by cif_guard_rom) *)
Lemma s5c_img_kept : forall cx (W W' : world SEGS) mem mem' ly' S' md',
  AR SEGS B ly' S' W' mem' md' ->
  lt_img B cx (rdW W mem) ->
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     rdW W' mem' a = rdW W mem a) ->
  lt_img B cx (rdW W' mem').
Proof using All.
intros cx W W' mem mem' ly' S' md' HAR' (HRO & HIMG & HGI) HK.
assert (KI : forall q n, sa_img SEGS B q n -> forall x, q <= x < q + n -> rdW W' mem' x = rdW W mem x).
{ intros q n Hq x Hx. destruct (Hq x Hx) as (H1 & H2 & H3). exact (HK x H1 H2 H3). }
assert (KL : forall a s, sa_lit SEGS B (rdW W mem) a s -> sa_lit SEGS B (rdW W' mem') a s).
{ intros a s Hl. apply (s5c_lit_kept W W' mem mem' a s); [|exact Hl].
  destruct Hl as (_ & _ & _ & _ & Himg). exact (KI _ _ Himg). }
destruct HIMG as (Hm40 & Hm40i & Hfz & Hrc & Hcat & Hcata & Hw & Hrl & Hssp & Hpin & Hrt & Hli & Hd1 & Hd2 & Hd3).
split; [|split].
- intros a Hro Ho He. rewrite (HK a); [exact (HRO a Hro Ho He) | | exact Ho | exact He].
  destruct Hro as [(s & Hs & _ & Hr) | Hrr]; [exists s; split; [exact Hs | exact Hr] | exact (s5c_relro a Hrr)].
- split; [intros k Hk; rewrite (KI _ 8 Hm40i) by lia; exact (Hm40 k Hk)|].
  split; [exact Hm40i|].
  split; [intros s Hs; destruct (Hfz s Hs) as [H1 H2]; exact (conj (KL _ _ H1) H2)|].
  split; [intros s Hs; destruct (Hrc s Hs) as [H1 H2]; exact (conj (KL _ _ H1) H2)|].
  split.
  { destruct Hcat as (Hcp & Hci & Hrows). split; [exact Hcp|]. split; [exact Hci|].
    intros i Hi. destruct (Hrows i Hi) as (tp & Htp & Hl). exists tp. split; [|exact (KL _ _ Hl)].
    apply (s5c_word_kept (rdW W mem)); [|exact Htp]. intros x Hx. apply (KI _ _ Hci).
    unfold pin_spec.row_addr, pin_spec.CAT_ROW, pin_spec.CAT_BYTES, pin_spec.CAT_N in *. lia. }
  split; [exact Hcata|].
  split.
  { destruct Hw as (Hwp & Hwi & Hws). split; [exact Hwp|]. split; [exact Hwi|].
    intros i Hi. destruct (Hws i Hi) as (wp & Hwp' & Hl). exists wp. split; [|exact (KL _ _ Hl)].
    apply (s5c_word_kept (rdW W mem)); [|exact Hwp']. intros x Hx. apply (KI _ _ Hwi). lia. }
  split.
  { destruct Hrl as (Hrp & Hri & Hrs). split; [exact Hrp|]. split; [exact Hri|].
    intros i Hi k Hk. rewrite (KI _ _ Hri) by lia. exact (Hrs i Hi k Hk). }
  split; [exact (s5c_ssp_kept W W' mem mem' ly' S' md' HAR' Hssp HK)|].
  split; [exact Hpin|]. split; [exact Hrt|]. split; [exact Hli|].
  split; [exact Hd1|]. split; [exact Hd2 | exact Hd3].
- intros i Hi. rewrite (KI _ _ Hli) by (unfold LONGL_W, LONGL_N; lia). exact (HGI i Hi).
Qed.

(* --------------------------------------- the core across a run --------------------------------------- *)
(* the facts of a point carried across a run of the walk that writes at most the s1 slots [S1 + lo, S1 + hi) below
   184(s1) (the S01 / S02 walk's lk_core_run) *)
Lemma s5c_core_run : forall cx ly S (W : world SEGS) regs mem md k acc rem o O regs' mem' md' lo hi,
  lt_base B MT cx -> lt_core B MT cx ly S W regs mem md k acc rem o O ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem' md' k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 cx + lo <= a < x_s1 cx + hi) -> rdW W mem' a = rdW W mem a) ->
  0 <= lo <= hi -> hi <= 184 ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
  lt_core B MT cx ly S W regs' mem' md' k acc rem o O.
Proof using All.
intros cx ly S W regs mem md k acc rem o O regs' mem' md' lo hi HB HC HJ' HK Hlo Hhi P2 P3 P4 P8 P9.
pose proof (s5c_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hfr0 & _).
destruct HC as (HF & HI & HBL & HBUD).
destruct HF as (HJ & R2 & R3 & R4 & R8 & R9 & HSV & HH0 & HH8 & HH16 & HFL & H200 & HSH & H184).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof ltoi_stk_room as HSR. unfold LTOI_FRAME_MAX in HSR, Hs1lo.
assert (HSTK : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity.
assert (HinF : In (LT_FCLS, x_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (EF : frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx) by exact (s5c_frame_addr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ _ _).
assert (F512 : fs_frame_bytes LT_FCLS = 512) by (vm_compute; reflexivity).
destruct (frames_bounds SEGS B LAWS ly S W mem md LT_FCLS (x_fpos cx) HAR HinF) as (Hf0 & Hfc & _).
rewrite EF in Hf0. rewrite EF, F512 in Hfc.
assert (KA : forall a, 0 <= a < x_s1 cx + lo \/ x_s1 cx + hi <= a < 2 ^ 64 -> rdW W mem' a = rdW W mem a).
{ intros a Ha. apply HK.
  - destruct Ha as [Ha | Ha]; split; lia.
  - intros [Hc1 Hc2]. destruct Ha as [Ha | Ha]; lia. }
split; [|split; [|split]].
- split; [exact HJ'|].
  rewrite P2, P3, P4, P8, P9.
  split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R8|]. split; [exact R9|].
  split.
  { intros i r Hi. assert (Hi13 : (i < length LT_SAVED)%nat) by (apply nth_error_Some; congruence).
    change (length LT_SAVED) with 13%nat in Hi13.
    apply (s5c_word_kept (rdW W mem)); [|exact (HSV i r Hi)]. intros x Hx. apply KA. right. lia. }
  split; [apply (s5c_word_kept (rdW W mem)); [|exact HH0]; intros x Hx; apply KA; left; lia|].
  split; [apply (s5c_word_kept (rdW W mem)); [|exact HH8]; intros x Hx; apply KA; left; lia|].
  split; [apply (s5c_word_kept (rdW W mem)); [|exact HH16]; intros x Hx; apply KA; left; lia|].
  split; [apply (s5c_word_kept (rdW W mem)); [|exact HFL]; intros x Hx; apply KA; left; unfold LT_FLAGW in *; lia|].
  split; [apply (s5c_word_kept (rdW W mem)); [|exact H200]; intros x Hx; apply KA; right; lia|].
  split.
  { intros i Hi. rewrite KA; [exact (HSH i Hi)|]. left. rewrite (lt_fsh_len o) in Hi.
    unfold x_sh, shadow_addr, SHADOW_OFF. lia. }
  apply (s5c_word_kept (rdW W mem)); [|exact H184]; intros x Hx; apply KA; right; lia.
- apply (s5c_img_kept cx W W mem mem' ly S md' (proj1 HJ') HI).
  intros a Ha _ _. apply KA. left. pose proof (pa_segs_low a Ha). lia.
- exact HBL.
- exact HBUD.
Qed.

(* -------------------------------------- the core across m_file -------------------------------------- *)
(* the facts of a point carried across a program call at sp = S1 whose footprint lies inside the live block m and
   which allocates nothing (sa_noalloc): the caller's journal at the same count, the callee's journal keeps the
   stack above S1, the class-3 frame and its shadow and the image *)
Lemma s5c_core_call : forall cx ly S (W : world SEGS) regs mem md k acc rem o O
  fsf (W2 : world SEGS) regs2 mem2 md2 STK1 FP1 EV1 m,
  lt_base B MT cx -> lt_core B MT cx ly S W regs mem md k acc rem o O ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly (set_fs fsf S) W2 mem2 md2 k ->
  ajournal SEGS B STK1 (x_s1 cx) FP1 ly S W mem md [] ly (set_fs fsf S) W2 mem2 md2 EV1 ->
  0 <= STK1 -> LTOI_FRAME_MAX + STK1 <= STK_LLVMFuzzerTestOneInput ->
  In (m, seg_spec.SEG_M_SIZE) (ablocks B ly S) ->
  (forall a, inFP FP1 a -> m <= a < m + seg_spec.SEG_M_SIZE) ->
  aregs_preserved regs regs2 ->
  Permutation (ablocks B ly (set_fs fsf S)) (ablocks B ly S) ->
  lt_core B MT cx ly (set_fs fsf S) W2 regs2 mem2 md2 k acc rem o O.
Proof using All.
intros cx ly S W regs mem md k acc rem o O fsf W2 regs2 mem2 md2 STK1 FP1 EV1 m HB HC HJ2 HJc HS0 HS1 HMin HFP HP HPm.
pose proof (s5c_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
destruct HC as (HF & HI & HBL & HBUD).
destruct HF as (HJ & R2 & R3 & R4 & R8 & R9 & HSV & HH0 & HH8 & HH16 & HFL & H200 & HSH & H184).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & K1 & _ & K3 & K4 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof ASAN_CEIL_range as (CR & _).
unfold LTOI_FRAME_MAX in HS1, Hs1lo.
assert (HSTK : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity.
assert (HinF : In (LT_FCLS, x_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (EF : frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx) by exact (s5c_frame_addr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ _ _).
assert (F512 : fs_frame_bytes LT_FCLS = 512) by (vm_compute; reflexivity).
destruct (frames_bounds SEGS B LAWS ly S W mem md LT_FCLS (x_fpos cx) HAR HinF) as (Hf0 & Hfc & _).
rewrite EF in Hf0. rewrite EF, F512 in Hfc.
destruct (al_blocks _ _ LAWS ly S W mem md m _ HAR HMin) as (_ & Hm4 & Hmc & Hmapp & _).
assert (HRM : req_size seg_spec.SEG_M_SIZE = seg_spec.SEG_M_SIZE) by reflexivity.
assert (HMS : seg_spec.SEG_M_SIZE = 9236) by reflexivity.
rewrite HRM in Hmc, Hmapp.
pose proof (sep_block_frame SEGS B LAWS ly S W mem md m _ LT_FCLS (x_fpos cx) HAR HMin HinF) as Hsep.
rewrite EF, F512, HRM in Hsep. unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
pose proof (blk_off_imgP B ly S W mem md m _ HAR HMin) as Hmoff. rewrite HRM in Hmoff. unfold off_img in Hmoff.
assert (NF : forall a, ~ (m <= a < m + seg_spec.SEG_M_SIZE) -> ~ inFP FP1 a)
  by (intros a Ha Hi; exact (Ha (HFP a Hi))).
(* the stack above S1 *)
assert (KS : forall a, x_s1 cx <= a < 2 ^ 64 -> rdW W2 mem2 a = rdW W mem a).
{ intros a Ha. apply K1; [lia | lia | apply NF; lia]. }
(* the frame's bytes *)
assert (KF : forall a, x_fr cx <= a < x_fr cx + 512 -> rdW W2 mem2 a = rdW W mem a).
{ intros a Ha. apply (K4 LT_FCLS (x_fpos cx) a HinF).
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF, F512. lia.
  - apply NF. lia. }
(* the frame's shadow bytes *)
assert (KH : forall i, 0 <= i < 64 -> rdW W2 mem2 (x_sh cx + i) = rdW W mem (x_sh cx + i)).
{ intros i Hi. apply (K4 LT_FCLS (x_fpos cx) _ HinF).
  - right. unfold in_zr. cbn [fst snd]. rewrite EF, F512. unfold x_sh. lia.
  - apply NF. unfold in_app, kLowShadowBeg, ASAN_CEIL in Hmapp. unfold x_sh, shadow_addr, SHADOW_OFF.
    lia. }
split; [|split; [|split]].
- (* the frame *)
  split; [exact HJ2|].
  rewrite (s5c_pres_reg _ _ 2%bv 2 HP ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (s5c_pres_reg _ _ 3%bv 3 HP ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (s5c_pres_reg _ _ 4%bv 4 HP ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (s5c_pres_reg _ _ 8%bv 8 HP ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (s5c_pres_reg _ _ 9%bv 9 HP ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R8|]. split; [exact R9|].
  split.
  { intros i r Hi. assert (Hi13 : (i < length LT_SAVED)%nat) by (apply nth_error_Some; congruence).
    change (length LT_SAVED) with 13%nat in Hi13.
    apply (s5c_word_kept (rdW W mem)); [|exact (HSV i r Hi)]. intros x Hx. apply KS. lia. }
  split; [apply (s5c_word_kept (rdW W mem)); [|exact HH0]; intros x Hx; apply KF; lia|].
  split; [apply (s5c_word_kept (rdW W mem)); [|exact HH8]; intros x Hx; apply KF; lia|].
  split; [apply (s5c_word_kept (rdW W mem)); [|exact HH16]; intros x Hx; apply KF; unfold LT_FLAGW; lia|].
  split; [apply (s5c_word_kept (rdW W mem)); [|exact HFL]; intros x Hx; apply KF; unfold LT_FLAGW in *; lia|].
  split; [apply (s5c_word_kept (rdW W mem)); [|exact H200]; intros x Hx; apply KS; lia|].
  split.
  { intros i Hi. rewrite (lt_fsh_len o) in Hi. rewrite KH by lia. exact (HSH i ltac:(rewrite lt_fsh_len; exact Hi)). }
  apply (s5c_word_kept (rdW W mem)); [|exact H184]; intros x Hx; apply KS; lia.
- (* the image facts *)
  apply (s5c_img_kept cx W W2 mem mem2 ly (set_fs fsf S) md2 (proj1 HJ2) HI).
  intros a Ha Ho He. apply K3; [exact Ha | exact Ho | exact He |].
  pose proof (pa_img_range a Ha) as Hai. unfold kImgEnd in Hai.
  apply fp_spares_closed.
  + intros Hs. pose proof (HFP 0 Hs) as H0. lia.
  + apply NF. lia.
- (* the blocks *)
  unfold lt_blocks in *. exact (Permutation_trans HPm HBL).
- (* the budget *)
  destruct HBUD as (B1 & B2 & B3 & B4 & B5 & B6).
  split; [exact B1|]. split; [exact B2|]. split; [exact B3|].
  split; [exact (mo_le_set_fs_r MT MTFL _ _ fsf _ B4)|]. split; [exact B5 | exact B6].
Qed.

(* ------------------------------------------- small arithmetic ------------------------------------------- *)
(* the turn's cursor past its take, P1 + NP, is an address of the input block (or the empty object) *)
Lemma s5c_at_np : forall cx f, lt_base B MT cx -> 0 <= x_at cx f + x_np cx f < 2 ^ 64.
Proof using All.
intros cx f HB.
pose proof HB as (HPRE0 & _ & _ & _ & _ & _ & Hpn & Hlen & _).
pose proof HPRE0 as (HAR0 & _).
pose proof (s5_np_le (x_pl cx) f) as H1. pose proof (s5_np_nat (x_pl cx) f) as H2.
pose proof (s5_sfx_len _ _ (s5_tail_sfx (x_pl cx) f)) as H3.
assert (H4 : length (seg_spec.seg_in (x_pl cx)) = length (x_pl cx))
  by (unfold seg_spec.seg_in, seg_spec.zs; apply length_map).
pose proof asan_consts as (C1 & _).
unfold x_at, x_np, seg_spec.seg_turn_at.
destruct Hpn as [(Hn0 & Hp) | (Hn & Hin)].
- rewrite Hp. unfold emptyA. lia.
- destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hin) as (_ & H4096 & Hceil & _).
  pose proof (req_size_pos (x_n cx) ltac:(lia)) as [_ Hq]. lia.
Qed.
Lemma s5c_U_atom : forall E n x v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + x < 2 ^ 64 ->
  U E (SOff n x) = v + x.
Proof using All.
intros E n x v H Hv Hvx. rewrite U_SOff, H, unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia.
Qed.
(* a word of a chunk of the symbolic state, read through the reader (image A's S03 walk's s13_chunk_word) *)
Lemma s5c_chunk_word : forall (W : world SEGS) E ss ms i rg p off e a v,
  st_ok SEGS E ss (restrict (w_H W) ms) -> nth_error (ss_mem ss) i = Some rg -> YP09.r_base rg = Some p ->
  In (YP09.mkChunk off (CVal 8 e)) (YP09.r_chunks rg) -> bv_unsigned (ew E p) = a ->
  U E e = v -> 0 <= v < 2 ^ 64 ->
  rdword (rdW W (ms_mem ms)) (a + off) = Some v.
Proof using All.
intros W E ss ms i rg p off e a v HS Hi Hb Hc Ha HU Hv.
assert (He : sv_denot E e = Z_to_bv 64 v).
{ apply bv_eq. rewrite unsigned_lit_small by lia. exact HU. }
pose proof (YI67.st_chunk_val SEGS E ss (restrict (w_H W) ms) i rg p off 8 e a v HS Hi Hb Hc Ha He
  ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)) as HV.
cbn [ms_mem restrict] in HV.
exact (PaLibF.rdword_of_val_mem SEGS (w_H W) (ms_mem ms) (a + off) v HV Hv).
Qed.

(* ---------------------------------------------- the seed ---------------------------------------------- *)
Definition s5c_E (regs : bvmap 5 word) : env := Eimg (Ereg regs []).
(* the seed at 0x85324: every register its own atom, the slot 144(s1) writable *)
Lemma s5c_seed : forall (W : world SEGS) (regs : bvmap 5 word) mem s1,
  getr regs 9 = w64 s1 -> 2 ^ 46 <= s1 -> s1 + 152 <= 2 ^ 47 -> s1 mod 32 = 0 ->
  (forall a, s1 + 144 <= a < s1 + 152 -> apresent (w_H W) mem a) ->
  st_ok_pi SEGS VAL (s5c_E regs) s5c_ss
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO_S5LST)) mem (seg_rom SEGS))).
Proof using All.
intros W regs mem s1 R9 Hs1a Hs1b Hs1c Hpres.
assert (E9 : ew (s5c_E regs) 9 = Z_to_bv 64 s1).
{ unfold s5c_E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl). exact R9. }
assert (VB : base_val (s5c_E regs) (Some 9%nat) = s1) by (cbn [base_val]; rewrite E9; apply unsigned_lit_small; lia).
unfold s5c_ss. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- unfold s5c_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold s5c_rg. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite VB.
  split; [lia|]. split; [lia|].
  split; [intros o Ho; apply (apresent_writable SEGS); apply Hpres; lia | constructor].
- split; exact I.
- split; [|split; [exact I | exact I]].
  cbn [s5c_fa f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E9, unsigned_lit_small by lia. change (2 ^ 5) with 32.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.

(* ------------------------------------- the call of m_file (0x85334) ------------------------------------- *)
(* from the jal's target (m_file's entry, ra = BASE + 0x578) with the caller's facts at the call, through the
   callee's contract at the segment's FP state, to K85338 at the FP state m_file returns *)
Lemma s5c_call : forall f cx ly S (W : world SEGS) regs mem md k acc (c m t : Z),
  lt_base B MT cx -> sa_frm0 -> Z.of_nat f + 1 = x_nf cx ->
  lt_core B MT cx ly S W regs mem md k acc (5 + 2 * (x_nf cx - Z.of_nat f)) LFO_L
    [(t, x_tn cx f); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] ->
  lt_hblk B ly S (rdW W mem) c seg_spec.SEG_C_SIZE -> lt_hblk B ly S (rdW W mem) m seg_spec.SEG_M_SIZE ->
  lt_hblk B ly S (rdW W mem) t (x_tn cx f) ->
  lt_cm (rdW W mem) c m (x_st cx f) -> sa_str (rdW W mem) t (seg_spec.seg_txt (x_pl cx) f) ->
  lt_cnt f (seg_spec.seg_rc (x_st cx f)) (seg_spec.seg_mc (x_st cx f)) ->
  getr regs 1 = Z_to_bv 64 (BASE + LO_K85338) -> getr regs 10 = w64 m -> getr regs 11 = w64 t ->
  getr regs 12 = w64 0 ->
  getr regs 21 = w64 0 -> getr regs 23 = w64 t -> getr regs 25 = w64 (Z.of_nat f + 1) ->
  getr regs 26 = w64 ((m + seg_spec.MC_N) / 8) ->
  lt_slots cx (rdW W mem) (LT_L cx c m ++
    [(144, x_at cx f + x_np cx f); (152, x_np cx f); (160, x_n1 cx f);
     (176, seg_spec.b2z (seg_spec.seg_ret (x_st cx f)))]) ->
  LTA_K85338 B MT f ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_m_file)) mem (seg_rom SEGS)) md) (lt_post B MT cx).
Proof using All.
intros f cx ly S W regs mem md k acc c m t HB Hfrm Hlast HC HHc HHm HHt HCM HSTR HCNT
  R1 R10 R11 R12 R21 R23 R25 R26 HSL HKA.
pose proof (s5c_nfiles_range (x_pl cx)) as Hnf.
assert (Hlast' : Z.of_nat f + 1 = seg_spec.seg_nfiles (x_pl cx)) by exact Hlast.
pose proof (s5c_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
pose proof HB as (HPRE0 & HAP0 & _ & _ & _ & _ & _ & _ & _ & Hfr0 & _ & Hev0 & _).
pose proof HPRE0 as (_ & _ & _ & Hgp0 & Htp0 & _).
pose proof HC as (HF & HI & HBL & HBUD).
pose proof HF as (HJ & R2 & R3 & R4 & R8 & R9 & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & Hnev & _).
pose proof HBUD as (Bk & Brem & Bev & _).
pose proof HI as (HRO & HIMG & _).
pose proof HIMG as (_ & _ & Hfz & _ & Hcat & _ & Hwords & Hroles & Hssp & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
assert (HSTK : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity.
pose proof (ltoi_callee_stks STK_m_file ltac:(unfold LTOI_CALLEE_STKS; cbn [In]; right; left; reflexivity))
  as (HSI0 & HSI1).
unfold LTOI_FRAME_MAX in HSI1, Hs1lo.
pose proof HHc as (HCin & Hc4 & Hc16 & HCad).
pose proof HHm as (HMin & Hm4 & Hm16 & HMad).
pose proof HHt as (HTin & Ht4 & Ht16 & HTad).
set (s := seg_spec.seg_txt (x_pl cx) f) in *.
assert (Hs : Z.of_nat (length s) <= 65535) by (apply s5c_txt_len; lia).
assert (Htn : x_tn cx f = Z.of_nat (length s) + 1) by reflexivity.
rewrite Htn in HTin, HTad.
destruct (al_blocks _ _ LAWS ly S W mem md m _ HAR HMin) as (_ & _ & Hmc & Hmapp & _).
destruct (al_blocks _ _ LAWS ly S W mem md t _ HAR HTin) as (_ & _ & Htc & Htapp & _).
destruct (al_blocks _ _ LAWS ly S W mem md c _ HAR HCin) as (_ & _ & Hcc & Hcapp & _).
assert (HRM : req_size seg_spec.SEG_M_SIZE = seg_spec.SEG_M_SIZE) by reflexivity.
assert (HRC : req_size seg_spec.SEG_C_SIZE = seg_spec.SEG_C_SIZE) by reflexivity.
assert (HRT : req_size (Z.of_nat (length s) + 1) = Z.of_nat (length s) + 1)
  by (unfold req_size; rewrite (proj2 (Z.eqb_neq _ 0)) by lia; reflexivity).
rewrite HRM in Hmc, Hmapp. rewrite HRC in Hcc, Hcapp. rewrite HRT in Htc, Htapp.
assert (HMS : seg_spec.SEG_M_SIZE = 9236) by reflexivity.
assert (HCS : seg_spec.SEG_C_SIZE = 16616) by reflexivity.
(* the three blocks apart, and m none of the entry's *)
pose proof HBL as HBL0. unfold lt_blocks in HBL, HBL0. cbn [app] in HBL.
pose proof (sep_blocks_perm SEGS B LAWS ly S W mem md _ _ _ HAR HBL) as Dtm.
pose proof (sep_blocks_perm SEGS B LAWS ly S W mem md _ _ _ HAR
  (Permutation_trans HBL (perm_skip _ (perm_swap _ _ _)))) as Dtc.
pose proof (sep_blocks SEGS B LAWS ly S W mem md m _ c _ HAR HMin HCin
  ltac:(intros Hq; apply (f_equal snd) in Hq; cbn [snd] in Hq; rewrite HMS, HCS in Hq; lia)) as Dmc.
unfold zdisjoint, block_rng in Dtm, Dtc, Dmc. cbn [fst snd] in Dtm, Dtc, Dmc.
rewrite Htn, HRT, HRM in Dtm. rewrite Htn, HRT, HRC in Dtc. rewrite HRM, HRC in Dmc.
assert (HMn : ~ In (m, seg_spec.SEG_M_SIZE) (x_bl0 B cx)).
{ apply (s5c_not_entry ly S W mem md [(t, x_tn cx f); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] _ _
    HAR HBL0); [right; left; reflexivity | cbn [snd]; rewrite HRM, HMS; lia]. }
(* the frame chain at the call's sp: s0 = SP0, the stack from S1 to the top present *)
assert (HRD : astack_rd ly (rdW W mem) (x_s1 cx)).
{ apply (astack_rd_mono ly _ (x_sp0 cx - STK_LLVMFuzzerTestOneInput)); [lia|].
  apply astack_rd_of_pres.
  apply (astack_pres_journal SEGS B pa_segs_low STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA)
    (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem md k HJ HAP0).
  intros a (r & Hr & Ha) Ha2. exfalso. unfold ltoi_PG in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  unfold longlA, A_LONGL, LONGL_N in Ha. lia. }
destruct (achain_any ly (rdW W mem) (x_s1 cx) (x_sp0 cx) HRD ltac:(right; right; right; lia)) as (ch1 & Hch).
assert (Hsp' : spZ regs = x_sp0 cx + (x_s1 cx - x_sp0 cx)).
{ unfold spZ. rewrite R2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (Hal : (x_s1 cx - x_sp0 cx) mod 16 = 0) by lia.
assert (Hch' : achain ly (rdW W mem) (x_sp0 cx + (x_s1 cx - x_sp0 cx)) (s0Z regs) ch1).
{ replace (x_sp0 cx + (x_s1 cx - x_sp0 cx)) with (x_s1 cx) by lia.
  unfold s0Z. rewrite R8. unfold w64. rewrite unsigned_lit_small by lia. exact Hch. }
assert (Hraw : YK0s.ret_ok (getr regs 1)) by (rewrite R1; apply ret_ok_codeptr_v; unfold LO_K85338; lia).
assert (Hra4 : 4096 <= bv_unsigned (getr regs 1)).
{ rewrite R1. rewrite unsigned_lit_small by (unfold LO_K85338; lia). unfold LO_K85338. lia. }
(* m_file_pre at this site *)
set (mc := seg_spec.seg_mc (x_st cx f)) in *.
set (rc0 := seg_spec.seg_rc (x_st cx f)) in *.
pose proof HCM as (HRC0 & HMC0).
assert (Hmok : s5c_mok mc).
{ destruct HMC0 as (bs & _ & (_ & L1 & _ & _ & _ & _ & L2 & _)). split; assumption. }
pose proof HCNT as (G1 & G2 & G3 & G4 & G5 & G6).
change (2 ^ 20) with 1048576 in G2, G3, G5, G6.
pose proof HSTR as ((HZ & HN0) & HTL).
assert (HPRE : m_file_pre SEGS B ly S (rdW W mem) m t 0 mc s None).
{ unfold m_file_pre.
  split; [lia|]. split; [exact Hm16|]. split; [exact HMC0|].
  split; [exists m, seg_spec.SEG_M_SIZE; split; [exact HMin | lia]|].
  split; [exact HMad|].
  split.
  { intros x Hx. apply (OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.YG0d_tail.AR_block_word_vis
      SEGS B ly S W mem md m seg_spec.SEG_M_SIZE (m + seg_spec.SEG_M_SIZE - 1) x HAR HMin); rewrite ?HRM; lia. }
  change (2 ^ 31) with 2147483648. change (2 ^ 17) with 131072. change (2 ^ 32) with 4294967296.
  split; [lia|]. split; [lia|]. split; [lia|].
  split; [lia|]. split; [exact HSTR|]. split; [lia|].
  split; [exists t, (Z.of_nat (length s) + 1); split; [exact HTin | lia]|].
  split; [exact HTad|].
  split; [apply (a3_amem_slack t (Z.of_nat (length s) + 1)); [exact Htapp | lia | lia | lia]|].
  split; [unfold sa_disj, seg_spec.cstr_span; lia|].
  split; [reflexivity | exact I]. }
assert (Hroom : sa_room S) by (unfold sa_room; rewrite Hfrs, Hfr0; cbn; lia).
assert (HEV : st_nev S + EV_m_file <= EV_MAX) by (unfold EV_m_file; lia).
assert (HLITS : forall x, In x M_FILE_LITS -> sa_lit SEGS B (rdW W mem) (seg_litA_fz x) x).
{ intros x Hx. apply (proj1 (Hfz x ltac:(unfold LTOI_FZ_LITS; apply in_or_app; right; apply in_or_app; right;
    apply in_or_app; right; exact Hx))). }
assert (Hmok' : s5c_mok (SegModel.m_file mc s None)) by (apply s5c_mfile_ok; exact Hmok).
pose proof (s5c_mfp_in m (length (SegModel.mc_kept mc)) _ Hmok') as HFP.
(* the call *)
unfold lt_post.
eapply (srr_after_callF (fx := fx) SEGS).
{ apply (cl_callSF B LAWS W regs mem (Z_to_bv 64 (BASE + AF_m_file)) STK_LLVMFuzzerTestOneInput (x_sp0 cx)
    (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [(LT_FCLS, x_fpos cx)] ly S md k
    STK_m_file (M_FILE_FP m (length (SegModel.mc_kept mc)) (SegModel.m_file mc s None)) EV_m_file
    (x_s1 cx - x_sp0 cx) (getr regs 1) ch1
    (fun ly' S' (W' : world SEGS) (regs' : bvmap 5 word) mem' md' =>
       sa_mconf (rdW W' mem') m (SegModel.m_file mc s None) /\ sa_noalloc B ly S ly' S')
    HJ Hsp' Hal ltac:(lia) HSI0 ltac:(lia) ltac:(rewrite R3; exact Hgp0) ltac:(rewrite R4; exact Htp0)
    eq_refl Hraw Hra4 Hch').
  - intros HPRE1. eapply SRr_mono.
    + exact (HM_FILE fx ly S W regs mem md ch1 m t 0 mc s None HPRE1 Hfrm Hroom HRO HLITS Hwords Hroles Hcat Hssp
        R10 ltac:(lia) R11 ltac:(lia) R12 ltac:(lia) HPRE HEV).
    + intros W3 c3 _ H3. exact H3.
  - intros a Ha. right. exists m, seg_spec.SEG_M_SIZE. split; [exact HMin|]. split; [exact HMn|].
    rewrite HRM. exact (HFP a Ha). }
(* the return at 0x85338 *)
intros fx1 ly2 S2 W2 regs2 mem2 md2 Hle Hfx (HJ2 & HJc & HP & HMC2 & (HPm & -> & (fsf & ->))).
replace (k + EV_m_file) with k in HJ2 by (unfold EV_m_file; lia).
replace (x_sp0 cx + (x_s1 cx - x_sp0 cx)) with (x_s1 cx) in HJc by lia.
pose proof (s5c_core_call cx ly S W regs mem md k acc _ LFO_L _ fsf W2 regs2 mem2 md2 STK_m_file _ EV_m_file m
  HB HC HJ2 HJc HSI0 ltac:(unfold LTOI_FRAME_MAX; lia) HMin HFP HP HPm) as HC2.
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & K1 & K2 & _).
assert (HAR2 : AR SEGS B ly (set_fs fsf S) W2 mem2 md2) by exact (proj1 HJ2).
assert (HCin2 : In (c, seg_spec.SEG_C_SIZE) (ablocks B ly (set_fs fsf S)))
  by exact (Permutation_in _ (Permutation_sym HPm) HCin).
assert (HMin2 : In (m, seg_spec.SEG_M_SIZE) (ablocks B ly (set_fs fsf S)))
  by exact (Permutation_in _ (Permutation_sym HPm) HMin).
assert (HTin2 : In (t, Z.of_nat (length s) + 1) (ablocks B ly (set_fs fsf S)))
  by exact (Permutation_in _ (Permutation_sym HPm) HTin).
assert (KC : forall i, 0 <= i < seg_spec.SEG_C_SIZE -> rdW W2 mem2 (c + i) = rdW W mem (c + i)).
{ intros i Hi. apply (K2 c _ i HCin HCin2); [rewrite HRC; lia|]. intros Hx. pose proof (HFP _ Hx). lia. }
assert (KT : forall i, 0 <= i < Z.of_nat (length s) + 1 -> rdW W2 mem2 (t + i) = rdW W mem (t + i)).
{ intros i Hi. apply (K2 t _ i HTin HTin2); [rewrite HRT; lia|]. intros Hx. pose proof (HFP _ Hx). lia. }
assert (KS2 : forall a, x_s1 cx <= a < 2 ^ 64 -> rdW W2 mem2 a = rdW W mem a).
{ intros a Ha. apply K1; [lia | lia |]. intros Hx. pose proof (HFP _ Hx). lia. }
assert (HPr : forall (r : bv 5) z, acallee_saved z -> Z_to_bv 5 z = r -> getr regs2 r = getr regs r)
  by (intros r z Hz Hr; exact (s5c_pres_reg _ _ r z HP Hz Hr)).
replace (getr regs 1) with (w64 (BASE + LO_K85338)) by (rewrite R1; reflexivity).
apply (HKA fx1 cx ly (set_fs fsf S) W2 regs2 mem2 md2 k acc c m t HB (fxrel_frm0 fx fx1 Hfrm Hfx) Hlast HC2).
- exact (s5c_hblk ly (set_fs fsf S) W2 mem2 md2 c _ HAR2 HCin2).
- exact (s5c_hblk ly (set_fs fsf S) W2 mem2 md2 m _ HAR2 HMin2).
- rewrite Htn. exact (s5c_hblk ly (set_fs fsf S) W2 mem2 md2 t _ HAR2 HTin2).
- rewrite (HPr 21%bv 21) by (first [unfold acallee_saved; lia | apply bv_eq; reflexivity]). exact R21.
- rewrite (HPr 23%bv 23) by (first [unfold acallee_saved; lia | apply bv_eq; reflexivity]). exact R23.
- rewrite (HPr 25%bv 25) by (first [unfold acallee_saved; lia | apply bv_eq; reflexivity]). exact R25.
- rewrite (HPr 26%bv 26) by (first [unfold acallee_saved; lia | apply bv_eq; reflexivity]). exact R26.
- intros o v Hin. pose proof (s5c_slots_off2 _ _ _ _ _ _ _ _ _ Hin) as Ho.
  apply (s5c_word_kept (rdW W mem)); [|exact (HSL o v Hin)]. intros x Hx. apply KS2. lia.
- exact (s5c_rconf_xfer _ _ c rc0 KC HRC0).
- exact HMC2.
- change (seg_spec.seg_txt (x_pl cx) f) with s. split; [|].
  + apply (s5c_strz_xfer (rdW W mem)); [|exact (conj HZ HN0)]. intros i Hi. apply KT.
    change (seg_spec.seg_txt (x_pl cx) f) with s in Hi. lia.
  + intros x Hx. change (seg_spec.seg_txt (x_pl cx) f) with s in Hx.
    apply (OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.YG0d_tail.AR_block_word_vis
      SEGS B ly (set_fs fsf S) W2 mem2 md2 t _ (t + Z.of_nat (length s)) x HAR2 HTin2); rewrite ?HRT; lia.
- pose proof (m_file_gen mc s None) as Mg. pose proof (m_file_refused mc s None HN0) as Mr.
  pose proof (m_file_overflow mc s None HN0) as Mo.
  unfold lt_cnt. change (seg_spec.seg_txt (x_pl cx) f) with s.
  change (seg_spec.seg_mc (x_st cx f)) with mc. change (seg_spec.seg_rc (x_st cx f)) with rc0.
  change (2 ^ 20) with 1048576. lia.
Qed.

(* ------------------------------------------ the piece: S5_LST -> K85338 ------------------------------------------ *)
Lemma s5_last : forall f, LTA_K85338 B MT f -> S5_LST_stmt B MT f.
Proof using All.
intros f HKA. unfold S5_LST_stmt.
intros cx ly S W regs mem md k acc c m t HB Hfrm Hlast HBODY HCM HSTR R21 R22 R23 R24 R25 R26 HSL.
destruct HBODY as (HC & HHc & HHm & HHt & HCNT).
pose proof (s5c_nfiles_range (x_pl cx)) as Hnf.
pose proof (s5c_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
pose proof HC as (HF & _).
pose proof HF as (HJ & R2 & R3 & R4 & R8 & R9 & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity.
unfold LTOI_FRAME_MAX in Hs1lo.
pose proof (s5c_seed W regs mem (x_s1 cx) R9 ltac:(lia) ltac:(lia) Hs1al (fun a Ha => Hpres a ltac:(lia))) as HS.
assert (SHOK : sh_ok SEGS s5c_X [] (s5c_E regs) (mrestrict (w_H W) mem)) by apply Forall_nil.
assert (HEI : img_env VAL A_LIM (s5c_E regs)) by (unfold s5c_E; apply Eimg_env).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew (s5c_E regs) n = getr regs rr).
{ intros n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  unfold s5c_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (Usp9 : bv_unsigned (ew (s5c_E regs) 9) = x_s1 cx).
{ rewrite (EEo 9%nat 9%bv eq_refl), R9. unfold w64. apply unsigned_lit_small. lia. }
remember (s5c_E regs) as E eqn:HE. clear HE.
unfold cfg_at, w64.
(* 0x85324 .. 0x85334: 144(s1) := s8, a0 := s6, a1 := s7, a2 := 0, jal m_file *)
paj_run_tok RUN HS HJ SHOK s5c_span.
{ lazymatch goal with |- awr_ok _ _ _ ?rs _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
  repeat first
    [ apply awr_ok_nil
    | apply awr_ok_cons_ro; [cbn; lia|]
    | apply awr_ok_cons_stack_off with (n := 9%nat) (d := x_s1 cx - x_sp0 cx);
        [reflexivity | rewrite Usp9; lia | cbn; lia | cbn; lia |] ]. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md1 := d) in *; clearbody md1 end.
lazymatch goal with Hfr : frame_of E _ (mrestrict _ _) (mrestrict _ _) |- _ =>
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ s5c_w (x_s1 cx) a -> rdW W (ms_mem ms) a = rdW W mem a)
by (intros a Ha Hn; apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (s5c_w (x_s1 cx)) Hfr); [
   intros b wlo whi a' Hin Hrr; cbn [windows map In YP09.r_base YP09.r_wlo YP09.r_whi] in Hin;
   repeat (destruct Hin as [Hq0 | Hin];
     [injection Hq0 as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp9 in Hrr; unfold s5c_w; lia|]);
   destruct Hin
 | exact Ha | exact Hn ]) end.
(* the slot the run wrote *)
assert (W144 : rdword (rdW W (ms_mem ms)) (x_s1 cx + 144) = Some (x_at cx f + x_np cx f)).
{ pose proof (s5c_at_np cx f HB) as Hrg.
  pose proof HS as HSo. try unfold st_ok_pi in HSo.
  lazymatch type of HSo with
  | st_ok _ _ ?ss _ =>
    let l := eval vm_compute in (nth_error (ss_mem ss) 0) in
    lazymatch l with Some ?rg =>
      let cs := eval vm_compute in (YP09.r_chunks rg) in
      lazymatch cs with context [YP09.mkChunk 144 (CVal 8 ?e)] =>
        apply (s5c_chunk_word W E ss ms 0 rg 9%nat 144 e (x_s1 cx) _ HSo);
        [ vm_compute; reflexivity | reflexivity | cbn [YP09.r_chunks]; repeat (first [left; reflexivity | right])
        | exact Usp9 | | exact Hrg ]
      end
    end
  end.
  rewrite (s5c_U_atom E 24 0 (x_at cx f + x_np cx f)); [lia | | lia | lia].
  rewrite (EEo 24%nat 24%bv eq_refl). exact R24. }
(* the call *)
pmkst HS.
rewrite (SIGP SS_m_file ltac:(unfold seg_prog_syms; cbn [In]; left; reflexivity)).
replace (seg_af SS_m_file) with AF_m_file by (vm_compute; reflexivity).
prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
prreg HS (12%bv : bv 5) P12.
assert (KR : forall r : bv 5, In r [2; 3; 4; 8; 9; 21; 23; 25; 26]%bv -> getr (ms_regs ms) r = getr regs r).
{ intros r Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr];
    [ let P := fresh "P" in lazymatch goal with |- getr _ ?rr = _ => prreg HS rr P end;
      rewrite P; apply EEo; reflexivity | ]).
  destruct Hr. }
pose proof (s5c_core_run cx ly S W regs mem md k acc _ LFO_L _ (ms_regs ms) (ms_mem ms) md1 144 152 HB HC HJ
  ltac:(intros a Ha Hn; exact (KEEP1 a Ha ltac:(unfold s5c_w; exact Hn))) ltac:(lia) ltac:(lia)
  (KR 2%bv ltac:(cbn; tauto)) (KR 3%bv ltac:(cbn; tauto)) (KR 4%bv ltac:(cbn; tauto))
  (KR 8%bv ltac:(cbn; tauto)) (KR 9%bv ltac:(cbn; tauto))) as HC1.
pose proof HHc as (HCin & _). pose proof HHm as (HMin & _). pose proof HHt as (HTin & _).
destruct (al_blocks _ _ LAWS ly S W mem md c _ HAR HCin) as (_ & Hc4 & Hcc & _).
destruct (al_blocks _ _ LAWS ly S W mem md m _ HAR HMin) as (_ & Hm4 & Hmc & _).
destruct (al_blocks _ _ LAWS ly S W mem md t _ HAR HTin) as (_ & Ht4 & Htc & _).
pose proof (req_size_pos seg_spec.SEG_C_SIZE ltac:(unfold seg_spec.SEG_C_SIZE; lia)) as [_ QC].
pose proof (req_size_pos seg_spec.SEG_M_SIZE ltac:(unfold seg_spec.SEG_M_SIZE; lia)) as [_ QM].
assert (Htn1 : x_tn cx f = Z.of_nat (length (seg_spec.seg_txt (x_pl cx) f)) + 1) by reflexivity.
pose proof (req_size_pos (x_tn cx f) ltac:(lia)) as [_ QT].
assert (KH1 : forall a, 0 <= a < alloc_ceiling -> rdW W (ms_mem ms) a = rdW W mem a).
{ intros a Ha. apply KEEP1; [lia | unfold s5c_w; lia]. }
assert (HCM1 : lt_cm (rdW W (ms_mem ms)) c m (x_st cx f)).
{ destruct HCM as (HR0 & HM0). split.
  - apply (s5c_rconf_xfer (rdW W mem)); [|exact HR0]. intros i Hi. apply KH1. lia.
  - apply (s5c_mconf_xfer (rdW W mem)); [|exact HM0]. intros i Hi. apply KH1. lia. }
assert (HSTR1 : sa_str (rdW W (ms_mem ms)) t (seg_spec.seg_txt (x_pl cx) f)).
{ destruct HSTR as (HZ & _). split.
  - apply (s5c_strz_xfer (rdW W mem)); [|exact HZ]. intros i Hi. apply KH1. lia.
  - intros x Hx. apply (OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.YG0d_tail.AR_block_word_vis
      SEGS B ly S W (ms_mem ms) md1 t (x_tn cx f) (t + Z.of_nat (length (seg_spec.seg_txt (x_pl cx) f))) x
      (proj1 HJ) HTin); lia. }
assert (HSL1 : lt_slots cx (rdW W (ms_mem ms)) (LT_L cx c m ++
    [(144, x_at cx f + x_np cx f); (152, x_np cx f); (160, x_n1 cx f);
     (176, seg_spec.b2z (seg_spec.seg_ret (x_st cx f)))])).
{ intros o v Hin.
  assert (Hin' : (o, v) = (144, x_at cx f + x_np cx f) \/ In (o, v) (S5_slots cx c m f)).
  { unfold S5_slots. apply in_app_or in Hin as [Hin | Hin]; [right; apply in_or_app; left; exact Hin|].
    cbn [In] in Hin. destruct Hin as [Hq | Hin]; [left; symmetry; exact Hq | right; apply in_or_app; right; exact Hin]. }
  destruct Hin' as [Hq | Hin'].
  - injection Hq as -> ->. exact W144.
  - pose proof (s5c_slots_off _ _ _ _ _ _ Hin') as Ho.
    apply (s5c_word_kept (rdW W mem)); [|exact (HSL o v Hin')].
    intros x Hx. apply KEEP1; [lia | unfold s5c_w; lia]. }
apply (s5c_call f cx ly S W (ms_regs ms) (ms_mem ms) md1 k acc c m t HB Hfrm Hlast HC1
  (s5c_hblk ly S W (ms_mem ms) md1 c _ (proj1 HJ) HCin) (s5c_hblk ly S W (ms_mem ms) md1 m _ (proj1 HJ) HMin)
  (s5c_hblk ly S W (ms_mem ms) md1 t _ (proj1 HJ) HTin) HCM1 HSTR1 HCNT).
- rewrite P1. reflexivity.
- rewrite P10, (EEo 22%nat 22%bv eq_refl). exact R22.
- rewrite P11, (EEo 23%nat 23%bv eq_refl). exact R23.
- rewrite P12. first [reflexivity | rewrite (EEo 0%nat 0%bv eq_refl); reflexivity].
- rewrite (KR 21%bv ltac:(cbn; tauto)). exact R21.
- rewrite (KR 23%bv ltac:(cbn; tauto)). exact R23.
- rewrite (KR 25%bv ltac:(cbn; tauto)). exact R25.
- rewrite (KR 26%bv ltac:(cbn; tauto)). exact R26.
- exact HSL1.
- exact HKA.
Qed.

End ec.
End fc.
End dc.

(* ============================================== piece L4 (d) ============================================== *)
(* reac-pw/fuzz_segconf, ASan+UBSan image B (fuzz_segconf.asan-ubsan, pin sha256 c3796c0b38f3): piece L4 of segment
   S05 of the walk of the test harness's entry function LLVMFuzzerTestOneInput (0x84dc0).

   s5_calls : forall f, S5A_CK B MT f -> S5_OTH_stmt B MT f
   covers 0x852c8 .. 0x852e0 (dis/LLVMFuzzerTestOneInput.fuzz_segconf.asan-ubsan.s lines 324-330, listing SegList.v
   slots 322-328 = lines 373-379; slot = (pc - 0x84dc0) / 4, line = slot + 51; m_file at 0x86140 = BASE + AF_m_file
   0x1380, reac_segconf_parse_file at 0x87e38 = BASE + AF_reac_segconf_parse_file 0x3078, both lib/B/Prog/SegList.v):
     852c8 mv a1,s7 ; 852cc mv a2,s3 ; 852d0 jal m_file                  m_file(m, text, label)
     852d4 ld a0,168(s1) ; 852d8 mv a1,s7 ; 852dc mv a2,s3
     852e0 jal reac_segconf_parse_file                                   parse_file(c, text, label)
   to the kit's inner cut S5_CK at 0x852e4. Each straight stretch is one token run (paj_run_tok); the two calls
   are taken with the Section hypotheses HM_FILE and HPARSE_FILE through PaFx.cl_callSF and PaFx.srr_after_callF
   (METHOD.md section 4.6), so the piece's continuation is the kit's S5A_CK, at every FP state.

   THE FORM: image B's own closed walks (lib/B/Prog/LLVMFuzzerTestOneInput_s12.v / _s12k.v, S01 + S02) and this
   segment's piece L5 (s5_tail): the same seeds, the same lt_core carry across a run (s5d_core_run) and the same
   image-facts carry (s5d_img_kept, with the stack-protector cells in ONE lemma s5d_ssp_kept, owner's brief
   decision 12). *)
(* ======================================== the two call sites ======================================== *)
(* the nat literal 65535 is a unary term the arithmetic decision procedure cannot read (a bare `lia` on a goal
   or hypothesis holding it answers "No applicable tactic", measured on the image-B build VM, log
   build-20261030T192909Z.log), so the two forms of the text's length bound are bridged once, here. *)
Lemma s5d_nat65535 : Z.of_nat 65535 = 65535.
Proof. vm_compute. reflexivity. Qed.
Lemma s5d_le_nat : forall n, Z.of_nat n <= 65535 -> (n <= 65535)%nat.
Proof.
intros n H. destruct (Nat.le_gt_cases n 65535) as [Hle|Hgt]; [exact Hle | exfalso].
apply (proj1 (Nat2Z.inj_lt 65535 n)) in Hgt. rewrite s5d_nat65535 in Hgt. clear - H Hgt. lia.
Qed.
(* the return address of the call of m_file: 0x852d4 = BASE + 0x514 (slot 325, `ld a0,168(s1)`, PW 0xa84b503);
   the return of the call of reac_segconf_parse_file is the kit's inner cut LO_S5CK = 0x524 *)
Definition s5d_ra1 : Z := 0x514.
(* run 2 (0x852d4 .. 0x852e0) reads c at 168(s1) (LT_L's slot 168) and writes nothing; atom 32 is c *)
Definition s5d_X : sv := SLit SHADOW_OFF.
Definition s5d_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition s5d_rg2 : smem := [YP09.mkRegion (Some 9%nat) 168 176 168 168 [YP09.mkChunk 168 (CVal 8 (SOff 32 0))]].
Definition s5d_fa2 : facts := mkFacts [ (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (32%nat, mkAF 4096 (2 ^ 47) 4) ] [] [].
Definition s5d_ss2 : sstate := mkSS s5d_ra1 sr_atoms s5d_rg2 None s5d_fa2.

(* ============================== L4's pure facts (SegModel and seg_spec only) ============================== *)
Lemma s5d_req : forall n, 0 < n -> req_size n = n.
Proof. intros n H. unfold req_size. destruct (Z.eqb_spec n 0); lia. Qed.

(* the turn count is at most 4 (decode builds 1 + in[2] % 4 files) *)
Lemma s5d_nfiles : forall pl, seg_spec.seg_nfiles pl <= 4.
Proof.
intros pl. unfold seg_spec.seg_nfiles, seg_spec.seg_files, seg_spec.seg_pay, SegModel.decode.
destruct (SegModel.fuzz_u8 (seg_spec.seg_in pl)) as [b0 i1].
destruct (SegModel.fuzz_u8 i1) as [fl i2]. destruct (SegModel.fuzz_u8 i2) as [b2 i3].
cbn [SegModel.p_files]. rewrite s5_dec_files_length.
pose proof (Z.mod_pos_bound b2 4 ltac:(lia)) as H. rewrite Z2Nat.id by lia. lia.
Qed.

(* the turn's text: NUL-free and at most 65535 bytes (SegModel.decode_ok over the input's bytes) *)
Lemma s5d_txt_ok : forall pl f,
  ~ In 0 (s5_txt pl f) /\ Z.of_nat (length (s5_txt pl f)) <= 65535.
Proof.
intros pl f.
assert (HB : Forall SegModel.byte_ok (seg_spec.seg_in pl)).
{ unfold seg_spec.seg_in, seg_spec.zs. apply Forall_map. apply Forall_forall. intros b _.
  unfold SegModel.byte_ok. pose proof (bv_unsigned_in_range 8 b) as H.
  change (bv_modulus 8) with 256 in H. lia. }
destruct (SegModel.decode_ok _ HB) as [HF _].
unfold s5_txt, seg_spec.seg_txt, seg_spec.seg_file, seg_spec.seg_files, seg_spec.seg_pay.
destruct (Nat.lt_ge_cases f (length (SegModel.p_files (SegModel.decode (seg_spec.seg_in pl))))) as [Hlt|Hge].
- rewrite Forall_forall in HF.
  destruct (HF _ (nth_In _ (SegModel.File 0 []) Hlt)) as (H1 & H2 & _). exact (conj H1 H2).
- rewrite nth_overflow by lia. cbn [SegModel.f_text length]. split; [intros [] | lia].
Qed.

(* ---- m_file keeps the model's two tables inside their arrays (seg[32], kept[8]) ---- *)
Lemma s5d_upd_nth_len : forall {A : Type} (i : nat) (g : A -> A) (l : list A),
  length (SegModel.upd_nth i g l) = length l.
Proof.
intros A i g l. revert i. induction l as [|x r IH]; intros [|i]; cbn [SegModel.upd_nth length];
  try reflexivity. rewrite IH. reflexivity.
Qed.
Definition s5d_mwf (c : SegModel.mconf) : Prop :=
  (length (SegModel.mc_seg c) <= 32)%nat /\ (length (SegModel.mc_kept c) <= 8)%nat.
Ltac s5d_wf_leaf :=
  unfold s5d_mwf, SegModel.m_refuse, SegModel.m_upd, SegModel.m_set_segs in *;
  cbv zeta; cbn [fst snd SegModel.mc_seg SegModel.mc_kept] in *;
  repeat match goal with |- context [if ?b then _ else _] => let E := fresh "E" in destruct b eqn:E end;
  cbn [SegModel.mc_seg SegModel.mc_kept] in *;
  rewrite ?s5d_upd_nth_len, ?length_app in *; cbn [length] in *;
  repeat match goal with
  | H : Nat.leb _ _ = true |- _ => apply Nat.leb_le in H
  | H : Nat.leb _ _ = false |- _ => apply Nat.leb_gt in H
  | H : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in H
  | H : Z.ltb _ _ = false |- _ => apply Z.ltb_ge in H
  end; lia.
Lemma s5d_header_wf : forall c l n, s5d_mwf c -> s5d_mwf (fst (SegModel.m_header c l n)).
Proof.
intros c l n Hc. unfold SegModel.m_header. cbv zeta.
repeat match goal with |- context [match ?x with _ => _ end] => let E := fresh "E" in destruct x eqn:E end;
  s5d_wf_leaf.
Qed.
Lemma s5d_key_wf : forall c g l n, s5d_mwf c -> s5d_mwf (SegModel.m_key c g l n).
Proof.
intros c g l n Hc. unfold SegModel.m_key. cbv zeta.
repeat match goal with |- context [match ?x with _ => _ end] => let E := fresh "E" in destruct x eqn:E end;
  s5d_wf_leaf.
Qed.
Lemma s5d_line_wf : forall st n l, s5d_mwf (fst st) -> s5d_mwf (fst (SegModel.m_line st n l)).
Proof.
intros [c cur] n l Hc. cbn [fst] in Hc. unfold SegModel.m_line. cbv beta iota zeta.
destruct (512 <=? length l)%nat; [s5d_wf_leaf|].
destruct (SegModel.h_strip (SegModel.h_cut_comment l)) as [|b s]; [exact Hc|].
match goal with |- context [if ?x then _ else _] => destruct x end;
  [apply s5d_header_wf; exact Hc | cbn [fst]; apply s5d_key_wf; exact Hc].
Qed.
Lemma s5d_lines_wf : forall ls st n, s5d_mwf (fst st) -> s5d_mwf (fst (SegModel.m_lines st n ls)).
Proof.
induction ls as [|l r IH]; intros st n H; cbn [SegModel.m_lines]; [exact H|].
apply IH. apply s5d_line_wf. exact H.
Qed.
Lemma s5d_file_wf : forall c s lab, s5d_mwf c -> s5d_mwf (SegModel.m_file c s lab).
Proof.
intros c s lab H. unfold SegModel.m_file. cbv zeta. apply s5d_lines_wf. cbn [fst].
unfold s5d_mwf in *. cbn [SegModel.mc_seg SegModel.mc_kept]. exact H.
Qed.
(* m_file's footprint lies in the mconf block; reac_segconf_parse_file's in the reader's block *)
Lemma s5d_mfp_in : forall m k0 mc', s5d_mwf mc' ->
  forall a, inFP (M_FILE_FP m k0 mc') a -> m <= a < m + seg_spec.SEG_M_SIZE.
Proof.
intros m k0 mc' (H1 & H2) a (r & Hr & Ha). unfold M_FILE_FP in Hr. cbn [In] in Hr.
unfold seg_spec.mseg_addr, seg_spec.kept_addr, seg_spec.MSEG_SIZE, seg_spec.MC_N, seg_spec.MC_REFUSED,
  seg_spec.MC_KEPT, seg_spec.MC_KEPT_LEN, seg_spec.MC_KNOCK, seg_spec.MC_NKEPT, seg_spec.MC_READING,
  seg_spec.SEG_M_SIZE in *.
repeat (destruct Hr as [<- | Hr]; [cbn [fst snd] in Ha; lia|]). destruct Hr.
Qed.
Lemma s5d_pfp_in : forall c a, inFP (seg_spec.RC_PARSE_W c) a -> c <= a < c + seg_spec.SEG_C_SIZE.
Proof.
intros c a (r & Hr & Ha). unfold seg_spec.RC_PARSE_W in Hr. cbn [In] in Hr.
unfold seg_spec.RC_N, seg_spec.RC_REFUSAL, seg_spec.RC_OVERFLOW, seg_spec.RC_READING, seg_spec.RC_GEN,
  seg_spec.SEG_C_SIZE in *.
repeat (destruct Hr as [<- | Hr]; [cbn [fst snd] in Ha; lia|]). destruct Hr.
Qed.

(* ---- the reader's counters across reac_segconf_parse_file: gen + 1, refused / overflow at most one a line ---- *)
Lemma s5d_refuse_cnt : forall c line fm a,
  SegModel.rc_gen (SegModel.refuse c line fm a) = SegModel.rc_gen c /\
  SegModel.rc_overflow (SegModel.refuse c line fm a) = SegModel.rc_overflow c /\
  SegModel.rc_refused (SegModel.refuse c line fm a) = SegModel.rc_refused c + 1.
Proof.
intros c line fm a. unfold SegModel.refuse. cbv zeta.
repeat match goal with |- context [if ?b then _ else _] => destruct b end;
  cbn [SegModel.rc_gen SegModel.rc_overflow SegModel.rc_refused]; lia.
Qed.
Lemma s5d_seg_get_cnt : forall c nm,
  SegModel.rc_gen (fst (SegModel.seg_get c nm)) = SegModel.rc_gen c /\
  SegModel.rc_refused (fst (SegModel.seg_get c nm)) = SegModel.rc_refused c /\
  SegModel.rc_overflow c <= SegModel.rc_overflow (fst (SegModel.seg_get c nm)) <= SegModel.rc_overflow c + 1.
Proof.
intros c nm. unfold SegModel.seg_get.
repeat match goal with |- context [match ?x with _ => _ end] => destruct x end;
  cbn [fst SegModel.rc_gen SegModel.rc_overflow SegModel.rc_refused SegModel.r_set_segs]; lia.
Qed.
Ltac s5d_rcnt :=
  repeat match goal with
  | |- context [SegModel.seg_get ?c0 ?nm] =>
      let G := fresh "G" in pose proof (s5d_seg_get_cnt c0 nm) as G; revert G;
      destruct (SegModel.seg_get c0 nm) as [? [[? ?]|]]; cbn [fst]; intros G
  | |- context [SegModel.refuse ?c0 ?l0 ?f0 ?a0] =>
      let R := fresh "R" in pose proof (s5d_refuse_cnt c0 l0 f0 a0) as R; revert R;
      generalize (SegModel.refuse c0 l0 f0 a0); intros ? R
  | |- context [match ?x with _ => _ end] => destruct x
  end;
  cbn [fst snd SegModel.r_upd SegModel.r_set_segs SegModel.rc_gen SegModel.rc_overflow SegModel.rc_refused] in *;
  lia.
Lemma s5d_r_header_cnt : forall c cn n line,
  SegModel.rc_gen (fst (fst (SegModel.r_header c cn n line))) = SegModel.rc_gen c /\
  SegModel.rc_refused c <= SegModel.rc_refused (fst (fst (SegModel.r_header c cn n line))) <=
    SegModel.rc_refused c + 1 /\
  SegModel.rc_overflow c <= SegModel.rc_overflow (fst (fst (SegModel.r_header c cn n line))) <=
    SegModel.rc_overflow c + 1.
Proof. intros c cn n line. unfold SegModel.r_header. cbv zeta. s5d_rcnt. Qed.
Lemma s5d_r_key_cnt : forall c cur cn n line,
  SegModel.rc_gen (fst (fst (SegModel.r_key c cur cn n line))) = SegModel.rc_gen c /\
  SegModel.rc_refused c <= SegModel.rc_refused (fst (fst (SegModel.r_key c cur cn n line))) <=
    SegModel.rc_refused c + 1 /\
  SegModel.rc_overflow c <= SegModel.rc_overflow (fst (fst (SegModel.r_key c cur cn n line))) <=
    SegModel.rc_overflow c + 1.
Proof. intros c cur cn n line. unfold SegModel.r_key. cbv zeta. s5d_rcnt. Qed.
Lemma s5d_r_line_cnt : forall c cur cn n l,
  SegModel.rc_gen (fst (fst (SegModel.r_line c cur cn n l))) = SegModel.rc_gen c /\
  SegModel.rc_refused c <= SegModel.rc_refused (fst (fst (SegModel.r_line c cur cn n l))) <=
    SegModel.rc_refused c + 1 /\
  SegModel.rc_overflow c <= SegModel.rc_overflow (fst (fst (SegModel.r_line c cur cn n l))) <=
    SegModel.rc_overflow c + 1.
Proof.
intros c cur cn n l. unfold SegModel.r_line. cbv zeta.
destruct (512 <=? length l)%nat.
- cbn [fst].
  match goal with |- context [SegModel.refuse ?a ?b ?c0 ?d] => pose proof (s5d_refuse_cnt a b c0 d) end. lia.
- repeat match goal with |- context [if ?x then _ else _] => destruct x end; cbn [fst];
    first [lia | apply s5d_r_header_cnt | apply s5d_r_key_cnt].
Qed.
Lemma s5d_r_lines_cnt : forall ls st n,
  SegModel.rc_gen (fst (fst (SegModel.r_lines st n ls))) = SegModel.rc_gen (fst (fst st)) /\
  SegModel.rc_refused (fst (fst st)) <= SegModel.rc_refused (fst (fst (SegModel.r_lines st n ls))) <=
    SegModel.rc_refused (fst (fst st)) + Z.of_nat (length ls) /\
  SegModel.rc_overflow (fst (fst st)) <= SegModel.rc_overflow (fst (fst (SegModel.r_lines st n ls))) <=
    SegModel.rc_overflow (fst (fst st)) + Z.of_nat (length ls).
Proof.
induction ls as [|l r IH]; intros [[c cur] nm] n; cbn [SegModel.r_lines fst length]; [lia|].
pose proof (IH (SegModel.r_line c cur nm (n + 1) l) (n + 1)) as H1.
pose proof (s5d_r_line_cnt c cur nm (n + 1) l) as H2. lia.
Qed.
Lemma s5d_r_parse_cnt : forall c s lab,
  SegModel.rc_gen (fst (SegModel.r_parse_file c s lab)) = SegModel.rc_gen c + 1 /\
  SegModel.rc_refused c <= SegModel.rc_refused (fst (SegModel.r_parse_file c s lab)) <=
    SegModel.rc_refused c + Z.of_nat (length (SegModel.lines s)) /\
  SegModel.rc_overflow c <= SegModel.rc_overflow (fst (SegModel.r_parse_file c s lab)) <=
    SegModel.rc_overflow c + Z.of_nat (length (SegModel.lines s)).
Proof.
intros c s lab. unfold SegModel.r_parse_file. cbv zeta.
match goal with |- context [SegModel.r_lines ?st ?n ?ls] =>
  pose proof (s5d_r_lines_cnt ls st n) as H; revert H; destruct (SegModel.r_lines st n ls) as [[c2 cur] nm] end.
intros H. cbn [fst SegModel.rc_gen SegModel.rc_refused SegModel.rc_overflow] in H |- *. lia.
Qed.
(* the counters after turn f: one gen more, at most 2 ^ 20 refused / overflow more, on both sides *)
Lemma s5d_cnt_S : forall f rc0 mc0 s lab, lt_cnt f rc0 mc0 -> ~ In 0 s -> Z.of_nat (length s) <= 65535 ->
  lt_cnt (Datatypes.S f) (fst (SegModel.r_parse_file rc0 s lab)) (SegModel.m_file mc0 s lab).
Proof.
intros f rc0 mc0 s lab (C1 & C2 & C3 & C4 & C5 & C6) Hn Hl.
destruct (SegModel.lines_props s Hn) as [_ HL].
apply (proj1 (Nat2Z.inj_le _ _)) in HL.
pose proof (s5d_r_parse_cnt rc0 s lab) as (P1 & P2 & P3).
pose proof (m_file_gen mc0 s lab) as M1. pose proof (m_file_refused mc0 s lab Hn) as M2.
pose proof (m_file_overflow mc0 s lab Hn) as M3.
unfold lt_cnt. rewrite Nat2Z.inj_succ.
change (2 ^ 20) with 1048576 in C2, C3, C5, C6 |- *.
clear - C1 C2 C3 C4 C5 C6 HL Hl P1 P2 P3 M1 M2 M3. lia.
Qed.

(* ---- arithmetic ---- *)
Lemma s5d_round8 : forall e b, e < b -> b mod 8 = 0 -> e - e mod 8 + 8 <= b.
Proof.
intros e b H1 H2. pose proof (Z.div_mod e 8 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound e 8 ltac:(lia)) as B1. pose proof (Z.div_mod b 8 ltac:(lia)) as D2. lia.
Qed.
Lemma s5d_roundup : forall e b, e <= b -> b mod 8 = 0 -> e + (- e) mod 8 <= b.
Proof.
intros e b H1 H2. pose proof (Z.div_mod (- e) 8 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (- e) 8 ltac:(lia)) as B1. pose proof (Z.div_mod b 8 ltac:(lia)) as D2. lia.
Qed.
Lemma s5d_span_le : forall a l b, a + Z.of_nat (length l) + 1 <= b -> b mod 8 = 0 ->
  a + seg_spec.cstr_span a l <= b.
Proof.
intros a l b H1 H2. unfold seg_spec.cstr_span.
pose proof (s5d_roundup (a + Z.of_nat (length l) + 1) b H1 H2). lia.
Qed.
(* a list without two overlapping members has no duplicate (image B's piece L5) *)
Lemma s5d_pzd_nodup : forall l, (forall x, In x l -> 0 < snd x) -> pairwise zdisjoint l -> List.NoDup l.
Proof.
induction l as [|x l IH]; intros Hp Hd; [constructor|]. destruct Hd as [Hx Hl]. constructor.
- intros Hin. rewrite Forall_forall in Hx. specialize (Hx x Hin). pose proof (Hp x (or_introl eq_refl)).
  unfold zdisjoint in Hx. lia.
- apply IH; [intros y Hy; apply Hp; right; exact Hy | exact Hl].
Qed.
Lemma s5d_span_ge : forall a l, Z.of_nat (length l) + 1 <= seg_spec.cstr_span a l.
Proof.
intros a l. unfold seg_spec.cstr_span.
pose proof (Z.mod_pos_bound (- (a + Z.of_nat (length l) + 1)) 8 ltac:(lia)). lia.
Qed.
Lemma s5d_fsb8 : forall cid, 0 <= cid -> fs_frame_bytes cid mod 8 = 0.
Proof.
intros cid H. unfold fs_frame_bytes. rewrite Z.shiftl_mul_pow2 by lia.
replace (64 * 2 ^ cid) with ((8 * 2 ^ cid) * 8) by ring. apply Z.mod_mul. lia.
Qed.
(* a word every byte of which two readers agree on *)
Lemma s5d_word_kept : forall (rd rd' : reader) a v,
  (forall x, a <= x < a + 8 -> rd' x = rd x) -> rdword rd a = Some v -> rdword rd' a = Some v.
Proof. intros rd rd' a v HK H. rewrite (rdword_ext rd rd' a); [exact H|]. intros k Hk. apply HK. lia. Qed.
(* a word all 8 bytes of which a reader shows *)
Lemma s5d_rdword_some : forall (rd : reader) a, (forall k, 0 <= k < 8 -> rd (a + k) <> None) ->
  exists v, rdword rd a = Some v.
Proof.
intros rd a H. unfold rdword.
pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
pose proof (H 1 ltac:(lia)) as H1. pose proof (H 2 ltac:(lia)) as H2. pose proof (H 3 ltac:(lia)) as H3.
pose proof (H 4 ltac:(lia)) as H4. pose proof (H 5 ltac:(lia)) as H5. pose proof (H 6 ltac:(lia)) as H6.
pose proof (H 7 ltac:(lia)) as H7.
destruct (rd a) as [b0|]; [|congruence]. destruct (rd (a + 1)) as [b1|]; [|congruence].
destruct (rd (a + 2)) as [b2|]; [|congruence]. destruct (rd (a + 3)) as [b3|]; [|congruence].
destruct (rd (a + 4)) as [b4|]; [|congruence]. destruct (rd (a + 5)) as [b5|]; [|congruence].
destruct (rd (a + 6)) as [b6|]; [|congruence]. destruct (rd (a + 7)) as [b7|]; [|congruence].
eexists; reflexivity.
Qed.
(* a callee-saved register a call keeps *)
Lemma s5d_pres_reg : forall regs regs' (r : bv 5) z,
  aregs_preserved regs regs' -> acallee_saved z -> Z_to_bv 5 z = r -> getr regs' r = getr regs r.
Proof. intros regs regs' r z HP Hz <-. exact (HP z Hz). Qed.
(* the bytes of a struct two readers agree on *)
Lemma s5d_rconf_kept : forall (rd rd' : reader) c rc,
  (forall i, 0 <= i < seg_spec.SEG_C_SIZE -> rd' (c + i) = rd (c + i)) -> sa_rconf rd c rc -> sa_rconf rd' c rc.
Proof.
intros rd rd' c rc HK (bs & Hb & He). exists bs. split; [|exact He].
intros i Hi. rewrite HK; [exact (Hb i Hi)|]. destruct He as (HL & _). unfold seg_spec.SEG_C_SIZE in *. lia.
Qed.
Lemma s5d_mconf_kept : forall (rd rd' : reader) m mc,
  (forall i, 0 <= i < seg_spec.SEG_M_SIZE -> rd' (m + i) = rd (m + i)) -> sa_mconf rd m mc -> sa_mconf rd' m mc.
Proof.
intros rd rd' m mc HK (bs & Hb & He). exists bs. split; [|exact He].
intros i Hi. rewrite HK; [exact (Hb i Hi)|]. destruct He as (HL & _). unfold seg_spec.SEG_M_SIZE in *. lia.
Qed.
(* the model's two bounds, from the block's encoding *)
Lemma s5d_mwf_of : forall (rd : reader) a mc, sa_mconf rd a mc -> s5d_mwf mc.
Proof.
intros rd a mc H. unfold sa_mconf, sa_mconfp in H. destruct H as (bs & _ & E).
destruct E as (_ & H1 & _ & _ & _ & _ & H2 & _). split; [exact H1 | exact H2].
Qed.

(* ======================================== the walk ======================================== *)
Section dd. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section fd.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section ed.
Variable B : asyms.
Variable MT : ameter_ops.
(* the image range the snprintf row's dest_off_globals uses, and the read-only ranges it reads; the S11 walk
   (the probe snprintf) takes the same three names and the same five HSNP_ hypotheses *)
Variable snp_lo snp_hi : Z.
Variable snp_cr : list (Z * Z).
(* AR's laws are a theorem of image B's kit, not a hypothesis *)
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis PRW : prog_rw SEGS B.
Hypothesis VOBJS : seg_val_objs.
Hypothesis SIGP : seg_sig_prog.
(* image B's per-image record (lib/B/Prog/SegRecBase.v, the image-B listing owner's commit c4abdaee306f, merged into
   this walk's integration commit da997fa1859d): the image facts lt_img needs at a reader after a call, each a field.
   It SUPERSEDES the three hypotheses IMG_RELRO / IMG_GOTW / IMG_GUARD an earlier version of this brief had.
   Never weaken lt_img instead. *)
Hypothesis IMGF : seg_img_facts SEGS B.
(* the allocator record's symbols at image B's values (lib/B/YF0m.v): with AR it gives the stack-protector
   cells at every state (SegRecCells.seg_rec_cells), since the runtime owns the .got word gotwA *)
Hypothesis HBS : YF0m.SegBSyms B.
(* longl's bytes are the program's own writable static, in the image and outside RELRO (the memset arm writes
   them), and no model-table pointer reaches within 65536 of longl (image A's S05 header takes the same
   three; they are what the longl arm and the literals' survival need) *)
Hypothesis HPGS : forall a, inFP (ltoi_PG longlA) a ->
  Exists (in_zr a) (as_prog_static B) /\ in_img SEGS a.
Hypothesis HPG_RO : forall a, inFP (ltoi_PG longlA) a -> ~ in_roP SEGS RLO_A RHI_A a.
Hypothesis HPG_PTR : forall a p,
  ((exists i, (i < 5)%nat /\ a = wordsA + 8 * Z.of_nat i) \/
   (exists i, (i < pin_spec.CAT_N)%nat /\ a = pin_spec.row_addr catA i)) ->
  rdword (fun x => option_map (fun b : byte => bv_unsigned b) (seg_rom SEGS (Z_to_bv 64 x))) a = Some p ->
  p + 65536 <= longlA.
(* the runtime entries S05 calls *)
Hypothesis AMEMCPY : forall fx0 : YK11.FPState, aintrin_realizes (fx := fx0) SEGS B OCpy (SIG SS___asan_memcpy).
Hypothesis AMEMSET : forall fx0 : YK11.FPState, aintrin_realizes (fx := fx0) SEGS B OSet (SIG SS___asan_memset).
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState,
  RtPFSeg.seg_asnprintf_realizes (fx := fx0) SEGS B snp_lo snp_hi snp_cr
    (SIG SS___interceptor_trampoline_snprintf) gotwA guardA.
Hypothesis AFREE4 : forall fx0 : YK11.FPState, afree04_rule (fx := fx0) SEGS B MT.
(* what image B's close shows of snp_lo / snp_hi / snp_cr; each is a computation there *)
Hypothesis HSNP_LIT : forall x, In x LLVMFuzzerTestOneInput_c.LTOI_LITS ->
  snp_lo <= seg_litA_fz x /\ seg_litA_fz x + Z.of_nat (length x) + 1 <= gotwA.
Hypothesis HSNP_CR : Forall (fun r => snp_lo <= fst r /\ 0 <= snd r /\ fst r + snd r <= snp_hi) snp_cr.
Hypothesis HSNP_LO : 0 <= snp_lo.
Hypothesis HSNP_CEIL : snp_hi <= alloc_ceiling.
Hypothesis HSNP_FAKE : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> snp_hi <= ly_F ly.
(* the two program callees, at every FP state *)
Hypothesis HM_FILE : forall fx0 : YK11.FPState,
  m_file_c.m_file_contract (fx := fx0) SEGS B (BASE + AF_m_file) STK_m_file RLO_A RHI_A seg_litA_fz
    wordsA rolesA catA gotwA guardA.
Hypothesis HPARSE_FILE : forall fx0 : YK11.FPState,
  reac_segconf_parse_file_c.reac_segconf_parse_file_contract (fx := fx0) SEGS B
    (BASE + AF_reac_segconf_parse_file) STK_reac_segconf_parse_file RLO_A RHI_A seg_litA_rc catA gotwA guardA.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* the three image facts lt_img needs at a reader after a call, each from a field of IMGF (image A's S00 walk
   takes the same three as its record s10_img); this text compiled on the VM, log build-20261030T183150Z.log.
   Rename `hdr_` to `s5<X>_` in your file. *)
Lemma s5d_relro : forall a, RLO_A <= a < RHI_A -> in_img SEGS a.
Proof. exact (cif_relro_img _ _ IMGF). Qed.

(* a ROM byte is shown by every reader *)
Lemma s5d_rom_view_some : forall (H : word -> bool) mem a,
  seg_rom SEGS (Z_to_bv 64 a) <> None -> aview SEGS H mem a <> None.
Proof using All.
intros H mem a Hr. unfold aview, mbyte. destruct (mrestrict H mem (Z_to_bv 64 a)) as [b|]; [cbn; discriminate|].
destruct (seg_rom SEGS (Z_to_bv 64 a)) as [b|] eqn:E; [cbn; discriminate | congruence].
Qed.
(* the stack-protector cells of seg_himg (the .got word gotwA holding guardA, and guardA's word shown) at a later
   reader, re-derived from AR at that state by SegRecCells.seg_rec_cells (owner's brief decision 12: the runtime
   owns the .got word gotwA, so image B's SegRo no longer lists it). ONE lemma on purpose; the agreement premise
   is kept so its callers do not change. *)
Lemma s5d_ssp_kept : forall ly' S' (W W' : world SEGS) mem mem' md',
  AR SEGS B ly' S' W' mem' md' ->
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     rdW W' mem' a = rdW W mem a) ->
  sa_ssp (rdW W mem) gotwA guardA -> sa_ssp (rdW W' mem') gotwA guardA.
Proof using All.
intros ly' S' W W' mem mem' md' HAR' _ _.
exact (proj1 (proj2 (SegRecCells.seg_rec_cells SEGS B LAWS HBS IMGF ly' S' W' mem' md' HAR'))).
Qed.
(* the image facts of a point carried to a later reader that agrees on every image byte the runtime does not own *)
Lemma s5d_lit_kept : forall (W W' : world SEGS) mem mem' a s,
  (forall x, a <= x < a + (Z.of_nat (length s) + 1) -> rdW W' mem' x = rdW W mem x) ->
  sa_lit SEGS B (rdW W mem) a s -> sa_lit SEGS B (rdW W' mem') a s.
Proof using All.
intros W W' mem mem' a s HK (Ha & ((Hzs & Hn0) & _) & Hpin & Hrt & Himg).
split; [exact Ha|]. split; [split; [split; [|exact Hn0] | exact (sa_tail_of_romtail SEGS (w_H W') mem' _ Hrt)]|].
- intros i Hi. rewrite HK; [exact (Hzs i Hi)|]. rewrite length_app in Hi. cbn [length] in Hi. lia.
- split; [exact Hpin|]. split; [exact Hrt | exact Himg].
Qed.
Lemma s5d_img_kept : forall cx ly' S' (W W' : world SEGS) mem mem' md',
  AR SEGS B ly' S' W' mem' md' ->
  lt_img B cx (rdW W mem) ->
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     rdW W' mem' a = rdW W mem a) ->
  lt_img B cx (rdW W' mem').
Proof using All.
intros cx ly' S' W W' mem mem' md' HAR' (HRO & HIMG & HGI) HK.
assert (KI : forall q n, sa_img SEGS B q n -> forall x, q <= x < q + n -> rdW W' mem' x = rdW W mem x).
{ intros q n Hq x Hx. destruct (Hq x Hx) as (H1 & H2 & H3). exact (HK x H1 H2 H3). }
assert (KL : forall a s, sa_lit SEGS B (rdW W mem) a s -> sa_lit SEGS B (rdW W' mem') a s).
{ intros a s Hl. apply (s5d_lit_kept W W' mem mem' a s); [|exact Hl].
  destruct Hl as (_ & _ & _ & _ & Himg). exact (KI _ _ Himg). }
destruct HIMG as (Hm40 & Hm40i & Hfz & Hrc & Hcat & Hcata & Hw & Hrl & Hssp & Hpin & Hrt & Hli & Hd1 & Hd2 & Hd3).
split; [|split].
- intros a Hro Ho He. rewrite (HK a); [exact (HRO a Hro Ho He) | | exact Ho | exact He].
  destruct Hro as [(s & Hs & _ & Hr) | Hrr]; [exists s; split; [exact Hs | exact Hr] | exact (s5d_relro a Hrr)].
- split; [intros k Hk; rewrite (KI _ 8 Hm40i) by lia; exact (Hm40 k Hk)|].
  split; [exact Hm40i|].
  split; [intros s Hs; destruct (Hfz s Hs) as [H1 H2]; exact (conj (KL _ _ H1) H2)|].
  split; [intros s Hs; destruct (Hrc s Hs) as [H1 H2]; exact (conj (KL _ _ H1) H2)|].
  split.
  { destruct Hcat as (Hcp & Hci & Hrows). split; [exact Hcp|]. split; [exact Hci|].
    intros i Hi. destruct (Hrows i Hi) as (tp & Htp & Hl). exists tp. split; [|exact (KL _ _ Hl)].
    apply (s5d_word_kept (rdW W mem)); [|exact Htp]. intros x Hx. apply (KI _ _ Hci).
    unfold pin_spec.row_addr, pin_spec.CAT_ROW, pin_spec.CAT_BYTES, pin_spec.CAT_N in *. lia. }
  split; [exact Hcata|].
  split.
  { destruct Hw as (Hwp & Hwi & Hws). split; [exact Hwp|]. split; [exact Hwi|].
    intros i Hi. destruct (Hws i Hi) as (wp & Hwp' & Hl). exists wp. split; [|exact (KL _ _ Hl)].
    apply (s5d_word_kept (rdW W mem)); [|exact Hwp']. intros x Hx. apply (KI _ _ Hwi). lia. }
  split.
  { destruct Hrl as (Hrp & Hri & Hrs). split; [exact Hrp|]. split; [exact Hri|].
    intros i Hi k Hk. rewrite (KI _ _ Hri) by lia. exact (Hrs i Hi k Hk). }
  split; [exact (s5d_ssp_kept ly' S' W W' mem mem' md' HAR' HK Hssp)|].
  split; [exact Hpin|]. split; [exact Hrt|]. split; [exact Hli|].
  split; [exact Hd1|]. split; [exact Hd2 | exact Hd3].
- intros i Hi. rewrite (KI _ _ Hli) by (unfold LONGL_W, LONGL_N; lia). exact (HGI i Hi).
Qed.

(* the entry sp and the realigned base S1 (andi sp,sp,-32 at 0x84e00 after addi sp,sp,-352) *)
Lemma s5d_sp : forall cx, lt_base B MT cx ->
  x_sp0 cx mod 16 = 0 /\ alloc_ceiling + 32768 <= x_sp0 cx /\ x_sp0 cx <= 2 ^ 47 /\
  x_s1 cx mod 32 = 0 /\ x_sp0 cx - 368 <= x_s1 cx /\ x_s1 cx <= x_sp0 cx - 352.
Proof using All.
intros cx HB. destruct HB as (HPRE & _). destruct HPRE as (_ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal & _ & Hceil & Hslo & Hshi & H47 & _).
unfold x_s1, x_sp0, LT_FRAME, STK_LLVMFuzzerTestOneInput in *.
set (s := spZ (x_regs cx)) in *. clearbody s.
repeat split; lia.
Qed.
(* a live block of a state is a harness block of that state *)
Lemma s5d_hblk : forall ly S (W : world SEGS) mem md a n,
  AR SEGS B ly S W mem md -> In (a, n) (ablocks B ly S) -> lt_hblk B ly S (rdW W mem) a n.
Proof using All.
intros ly S W mem md a n HAR Hin.
destruct (al_blocks _ _ LAWS ly S W mem md a n HAR Hin) as (H16 & H4096 & Hceil & _ & _ & _ & Hn).
pose proof (req_size_pos n ltac:(lia)) as [_ Hreq].
pose proof asan_consts as (C1 & _).
split; [exact Hin|]. split; [exact H4096|]. split; [exact H16|].
split; [lia|]. split; [lia|].
split; [exact (amem_range_of_block SEGS B LAWS ly S W mem md a n a n HAR Hin ltac:(lia) ltac:(lia))|].
split; [exact (range_addressable_of_block SEGS B LAWS ly S W mem md a n a n HAR Hin ltac:(lia) ltac:(lia))|].
intros Hn0. exact (shadow_hull_vis_of_block SEGS B LAWS ly S W mem md a n a n HAR Hin ltac:(lia) ltac:(lia) Hn0).
Qed.
(* the live blocks of a state are distinct (image B's piece L5) *)
Lemma s5d_nodup : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> List.NoDup (ablocks B ly S).
Proof using All.
intros ly S W mem md HAR.
destruct (ablocks B ly S) as [|[p0 n0] bl] eqn:Eb; [constructor|].
assert (Hin0 : In (p0, n0) (ablocks B ly S)) by (rewrite Eb; left; reflexivity).
destruct (al_blocks _ _ LAWS ly S W mem md p0 n0 HAR Hin0) as (_ & _ & _ & _ & _ & Hpw & _).
rewrite <- Eb. apply (NoDup_map_inv (fun b : Z * Z => (fst b, req_size (snd b)))).
apply s5d_pzd_nodup; [|exact Hpw].
intros [a q] Hx. apply in_map_iff in Hx as ([pb nb] & Hq & Hpb). cbn in Hq. injection Hq as <- <-.
destruct (al_blocks _ _ LAWS ly S W mem md pb nb HAR Hpb) as (_ & _ & _ & _ & _ & _ & Hn).
cbn [snd]. pose proof (req_size_pos nb ltac:(lia)). lia.
Qed.
(* the frame address of a journal's target layout is the entry's *)
Lemma s5d_frame_addr : forall STK sp0 FP ly0 S0 W0 mem0 md0 own ly S (W : world SEGS) mem md k,
  ajournal SEGS B STK sp0 FP ly0 S0 W0 mem0 md0 own ly S W mem md k ->
  forall cid pos, frame_addr ly cid pos = frame_addr ly0 cid pos.
Proof using All.
intros STK sp0 FP ly0 S0 W0 mem0 md0 own ly S W mem md k HJ cid pos.
destruct HJ as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & EF & _). unfold frame_addr. rewrite EF.
reflexivity.
Qed.
(* a shadow byte of the harness's frame is no byte of a live block *)
Lemma s5d_sh_app : forall fr b n i, 4096 <= fr -> fr + 512 <= alloc_ceiling -> in_app b n ->
  0 <= i < 64 -> ~ (b <= shadow_addr fr + i < b + n).
Proof using All.
intros fr b n i H1 H2 (Hb & Hb2) Hi Hx. pose proof asan_consts as (HAC & _).
unfold shadow_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
destruct Hb2 as [Hb2 | (Hb2 & Hb3)]; lia.
Qed.
(* the facts of a point carried across a run of the walk that writes at most the s1 slots [S1 + lo, S1 + hi)
   below 184(s1), keeps sp, gp, tp, s0, s1 and the allocator state (image B's piece L5) *)
Lemma s5d_core_run : forall cx ly S (W : world SEGS) regs mem md k acc rem o O regs' mem' md' lo hi,
  lt_base B MT cx -> lt_core B MT cx ly S W regs mem md k acc rem o O ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem' md' k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 cx + lo <= a < x_s1 cx + hi) -> rdW W mem' a = rdW W mem a) ->
  0 <= lo <= hi -> hi <= 184 ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
  lt_core B MT cx ly S W regs' mem' md' k acc rem o O.
Proof using All.
intros cx ly S W regs mem md k acc rem o O regs' mem' md' lo hi HB HC HJ' HK Hlo Hhi P2 P3 P4 P8 P9.
pose proof (s5d_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hfr0 & _).
destruct HC as (HF & HI & HBL & HBUD).
destruct HF as (HJ & R2 & R3 & R4 & R8 & R9 & HSV & HH0 & HH8 & HH16 & HFL & H200 & HSH & H184).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof ltoi_stk_room as HSR. unfold LTOI_FRAME_MAX in HSR.
assert (HSTK : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity.
assert (HinF : In (LT_FCLS, x_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (EF : frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx)
  by exact (s5d_frame_addr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ _ _).
assert (F512 : fs_frame_bytes LT_FCLS = 512) by (vm_compute; reflexivity).
destruct (frames_bounds SEGS B LAWS ly S W mem md LT_FCLS (x_fpos cx) HAR HinF) as (Hf0 & Hfc & _).
rewrite EF in Hf0. rewrite EF, F512 in Hfc.
assert (KA : forall a, 0 <= a < x_s1 cx + lo \/ x_s1 cx + hi <= a < 2 ^ 64 -> rdW W mem' a = rdW W mem a).
{ intros a Ha. apply HK.
  - destruct Ha as [Ha | Ha]; split; lia.
  - intros [Hc1 Hc2]. destruct Ha as [Ha | Ha]; lia. }
split; [|split; [|split]].
- split; [exact HJ'|].
  rewrite P2, P3, P4, P8, P9.
  split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R8|]. split; [exact R9|].
  split.
  { intros i r Hi. assert (Hi13 : (i < length LT_SAVED)%nat) by (apply nth_error_Some; congruence).
    change (length LT_SAVED) with 13%nat in Hi13.
    apply (s5d_word_kept (rdW W mem)); [|exact (HSV i r Hi)]. intros x Hx. apply KA. right. lia. }
  split; [apply (s5d_word_kept (rdW W mem)); [|exact HH0]; intros x Hx; apply KA; left; lia|].
  split; [apply (s5d_word_kept (rdW W mem)); [|exact HH8]; intros x Hx; apply KA; left; lia|].
  split; [apply (s5d_word_kept (rdW W mem)); [|exact HH16]; intros x Hx; apply KA; left; lia|].
  split; [apply (s5d_word_kept (rdW W mem)); [|exact HFL]; intros x Hx; apply KA; left;
          unfold LT_FLAGW in *; lia|].
  split; [apply (s5d_word_kept (rdW W mem)); [|exact H200]; intros x Hx; apply KA; right; lia|].
  split.
  { intros i Hi. rewrite KA; [exact (HSH i Hi)|]. left. rewrite (lt_fsh_len o) in Hi.
    unfold x_sh, shadow_addr, SHADOW_OFF. lia. }
  apply (s5d_word_kept (rdW W mem)); [|exact H184]; intros x Hx; apply KA; right; lia.
- apply (s5d_img_kept cx ly S W W mem mem' md' (proj1 HJ') HI).
  intros a Ha _ _. apply KA. left. pose proof (pa_segs_low a Ha). lia.
- exact HBL.
- exact HBUD.
Qed.

(* ---- what a call of a program function of the harness keeps, from its inner journal ---- *)
Lemma s5d_jkeep : forall cx ly S (W : world SEGS) mem md STKc FP1 ev ly2 S2 (W2 : world SEGS) mem2 md2 bm nm,
  lt_base B MT cx ->
  AR SEGS B ly S W mem md -> In (LT_FCLS, x_fpos cx) (frames S) ->
  ajournal SEGS B STKc (x_s1 cx) FP1 ly S W mem md [] ly2 S2 W2 mem2 md2 ev ->
  In (bm, nm) (ablocks B ly S) -> 0 < nm -> req_size nm = nm ->
  (forall a, inFP FP1 a -> bm <= a < bm + nm) ->
  Permutation (ablocks B ly2 S2) (ablocks B ly S) ->
  frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx ->
  (forall a, x_s1 cx <= a < 2 ^ 64 -> rdW W2 mem2 a = rdW W mem a) /\
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) ->
     ~ (as_errno B <= a < as_errno B + 4) -> rdW W2 mem2 a = rdW W mem a) /\
  (forall a, x_fr cx <= a < x_fr cx + 512 \/ x_sh cx <= a < x_sh cx + 64 -> rdW W2 mem2 a = rdW W mem a) /\
  (forall b n i, In (b, n) (ablocks B ly S) -> 0 <= i < req_size n ->
     ~ (bm <= b + i < bm + nm) -> rdW W2 mem2 (b + i) = rdW W mem (b + i)).
Proof using All.
intros cx ly S W mem md STKc FP1 ev ly2 S2 W2 mem2 md2 bm nm HB HAR HinF HJc HinB Hnm Hreq HFP HPm EF.
pose proof (s5d_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
pose proof HJc as (HAR2 & _ & _ & _ & _ & Hfr1 & _ & _ & K1 & K2 & K3 & K4 & _ & _ & _ & _ & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof ASAN_CEIL_range as (CR & _).
assert (F512 : fs_frame_bytes LT_FCLS = 512) by (vm_compute; reflexivity).
destruct (frames_bounds SEGS B LAWS ly S W mem md LT_FCLS (x_fpos cx) HAR HinF) as (Hf0 & Hfc & _).
rewrite EF in Hf0. rewrite EF, F512 in Hfc.
destruct (al_blocks _ _ LAWS ly S W mem md bm nm HAR HinB) as (_ & Hb4096 & Hbceil & Hbapp & _ & _ & _).
rewrite Hreq in Hbceil, Hbapp.
pose proof (sep_block_frame SEGS B LAWS ly S W mem md bm nm LT_FCLS (x_fpos cx) HAR HinB HinF) as Hsep.
rewrite EF, F512, Hreq in Hsep. unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
assert (HnoF : forall a, bm + nm <= a \/ a < bm -> ~ inFP FP1 a)
  by (intros a Ha Hin; pose proof (HFP a Hin); lia).
split; [|split; [|split]].
- intros a Ha. apply K1; [lia | | ].
  + intros [_ Hc]. lia.
  + apply HnoF. lia.
- intros a Ha Ho He. apply K3; [exact Ha | exact Ho | exact He |].
  apply fp_spares_closed.
  + intros (r & Hr & H0). pose proof (HFP 0 (ex_intro _ r (conj Hr H0))). lia.
  + apply HnoF. pose proof (pa_img_range a Ha) as Hr.
    unfold off_img in *. pose proof (blk_off_imgP B ly S W mem md bm nm HAR HinB) as Hoff.
    rewrite Hreq in Hoff. unfold off_img, kImgEnd in *. lia.
- intros a Ha. apply (K4 LT_FCLS (x_fpos cx) a HinF).
  + destruct Ha as [Ha | Ha]; [left | right]; unfold in_zr, frame_rng; cbn [fst snd]; rewrite EF, F512;
      unfold x_sh in *; lia.
  + cbv beta. apply HnoF. destruct Ha as [Ha | Ha]; [lia|].
    unfold x_sh in Ha.
    pose proof (s5d_sh_app (x_fr cx) bm nm (a - shadow_addr (x_fr cx)) Hf0 Hfc Hbapp ltac:(lia)) as Hno.
    replace (shadow_addr (x_fr cx) + (a - shadow_addr (x_fr cx))) with a in Hno by ring. lia.
- intros b n i Hb Hi Hne. apply (K2 b n i Hb); [|exact Hi|].
  + apply (Permutation_in _ (Permutation_sym HPm)). exact Hb.
  + cbv beta. apply HnoF. lia.
Qed.

(* ---- lt_core across a call that allocates nothing: the journal goes on at the same count ---- *)
Lemma s5d_carry : forall cx ly S (W : world SEGS) regsT memT md k acc rem o O
  ly2 S2 (W2 : world SEGS) regs2 mem2 md2,
  lt_base B MT cx -> lt_core B MT cx ly S W regsT memT md k acc rem o O ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly2 S2 W2 mem2 md2 k ->
  aregs_preserved regsT regs2 ->
  Permutation (ablocks B ly2 S2) (ablocks B ly S) -> mo_le MT (x_S cx) S2 acc ->
  (forall a, x_s1 cx <= a < 2 ^ 64 -> rdW W2 mem2 a = rdW W memT a) ->
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) ->
     ~ (as_errno B <= a < as_errno B + 4) -> rdW W2 mem2 a = rdW W memT a) ->
  (forall a, x_fr cx <= a < x_fr cx + 512 \/ x_sh cx <= a < x_sh cx + 64 -> rdW W2 mem2 a = rdW W memT a) ->
  lt_core B MT cx ly2 S2 W2 regs2 mem2 md2 k acc rem o O.
Proof using All.
intros cx ly S W regsT memT md k acc rem o O ly2 S2 W2 regs2 mem2 md2 HB HC HJ2 HP HPm MLE KS KI KF.
pose proof (s5d_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
destruct HC as (HF & HI & HBL & HBUD).
destruct HF as (HJ & R2 & R3 & R4 & R8 & R9 & HSV & HH0 & HH8 & HH16 & HFL & H200 & HSH & H184).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof ltoi_stk_room as HSR. unfold LTOI_FRAME_MAX in HSR.
assert (HSTK : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity.
split; [|split; [|split]].
- split; [exact HJ2|].
  rewrite (s5d_pres_reg _ _ 2%bv 2 HP ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (s5d_pres_reg _ _ 3%bv 3 HP ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (s5d_pres_reg _ _ 4%bv 4 HP ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (s5d_pres_reg _ _ 8%bv 8 HP ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (s5d_pres_reg _ _ 9%bv 9 HP ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R8|]. split; [exact R9|].
  split.
  { intros i r Hi. assert (Hi13 : (i < length LT_SAVED)%nat) by (apply nth_error_Some; congruence).
    change (length LT_SAVED) with 13%nat in Hi13.
    apply (s5d_word_kept (rdW W memT)); [|exact (HSV i r Hi)]. intros x Hx. apply KS. lia. }
  split; [apply (s5d_word_kept (rdW W memT)); [|exact HH0]; intros x Hx; apply KF; left; lia|].
  split; [apply (s5d_word_kept (rdW W memT)); [|exact HH8]; intros x Hx; apply KF; left; lia|].
  split; [apply (s5d_word_kept (rdW W memT)); [|exact HH16]; intros x Hx; apply KF; left; unfold LT_FLAGW; lia|].
  split; [apply (s5d_word_kept (rdW W memT)); [|exact HFL]; intros x Hx; apply KF; left;
          unfold LT_FLAGW in *; lia|].
  split; [apply (s5d_word_kept (rdW W memT)); [|exact H200]; intros x Hx; apply KS; lia|].
  split.
  { intros i Hi. rewrite (lt_fsh_len o) in Hi. rewrite KF by (right; unfold x_sh in *; lia).
    exact (HSH i ltac:(rewrite lt_fsh_len; exact Hi)). }
  apply (s5d_word_kept (rdW W memT)); [|exact H184]; intros x Hx; apply KS; lia.
- exact (s5d_img_kept cx ly2 S2 W W2 memT mem2 md2 (proj1 HJ2) HI KI).
- unfold lt_blocks in *. exact (Permutation_trans HPm HBL).
- destruct HBUD as (B1 & B2 & B3 & B4 & B5 & B6).
  split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact MLE|]. split; [exact B5 | exact B6].
Qed.

(* ---- the label survives a call whose footprint lies in the block bm ---- *)
Lemma s5d_lab_kept : forall cx ly S (W : world SEGS) mem S2 (W2 : world SEGS) mem2 md2 f lp c m bm nm,
  AR SEGS B ly S2 W2 mem2 md2 ->
  In (bm, nm) (ablocks B ly S) -> 0 < nm -> req_size nm = nm ->
  Permutation (ablocks B ly S2) (ablocks B ly S) -> frames S2 = frames S ->
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) ->
     ~ (as_errno B <= a < as_errno B + 4) -> rdW W2 mem2 a = rdW W mem a) ->
  (forall cid pos a, In (cid, pos) (frames S) ->
     (frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid \/
      shadow_addr (frame_addr ly cid pos) <= a < shadow_addr (frame_addr ly cid pos) + fs_frame_bytes cid / 8) ->
     rdW W2 mem2 a = rdW W mem a) ->
  (forall b n i, In (b, n) (ablocks B ly S) -> 0 <= i < req_size n ->
     ~ (bm <= b + i < bm + nm) -> rdW W2 mem2 (b + i) = rdW W mem (b + i)) ->
  (forall a, bm <= a < bm + nm -> ~ (lp <= a < lp + seg_spec.cstr_span lp
     (match s5_lab (x_pl cx) f with Some l => l | None => [] end))) ->
  S5_label B ly S (rdW W mem) cx f lp c m ->
  S5_label B ly S2 (rdW W2 mem2) cx f lp c m.
Proof using All.
intros cx ly S W mem S2 W2 mem2 md2 f lp c m bm nm HAR2 HinB Hnm Hreq HPm Hfr KI KF KB Hdisj HL.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HL as (Hlp & HO & HM).
split; [exact Hlp|].
revert HO HM Hdisj. destruct (s5_lab (x_pl cx) f) as [l|] eqn:El; intros HO HM Hdisj;
  [|split; [exact HO | exact I]].
destruct HO as (Hlp0 & Hstr). destruct HM as (Hlen & Hwh & Haddr & Hdm & Hdc).
pose proof (s5d_span_ge lp l) as Hspan.
(* the string's own bytes are outside the footprint *)
assert (HKS : forall i, 0 <= i < Z.of_nat (length l) + 1 -> rdW W2 mem2 (lp + i) = rdW W mem (lp + i)).
{ intros i Hi.
  destruct Hwh as [Hhp | [Hfp | (Himg & Hpin & Hpt)]].
  - destruct Hhp as (b & n & Hb & Hb1 & Hb2).
    replace (lp + i) with (b + (lp + i - b)) by ring.
    apply (KB b n (lp + i - b) Hb).
    + pose proof (req_size_pos n) as Hq.
      destruct (al_blocks _ _ LAWS ly S2 W2 mem2 md2 b n HAR2
                  (Permutation_in _ (Permutation_sym HPm) Hb)) as (_ & _ & _ & _ & _ & _ & Hn).
      pose proof (proj2 (Hq ltac:(lia))). lia.
    + replace (b + (lp + i - b)) with (lp + i) by ring. intros Hc. exact (Hdisj (lp + i) Hc ltac:(lia)).
  - destruct Hfp as (cid & pos & Hin & Hcid & Hf1 & Hf2).
    apply (KF cid pos (lp + i) Hin). left. lia.
  - apply KI; [apply (proj1 (Himg (lp + i) ltac:(lia))) | apply (proj1 (proj2 (Himg (lp + i) ltac:(lia))))
    | apply (proj2 (proj2 (Himg (lp + i) ltac:(lia))))]. }
assert (HSTRZ : sa_strz (rdW W2 mem2) lp l).
{ destruct Hstr as (Hzs & Htl). destruct Hzs as (Hz & Hn0). split; [|exact Hn0].
  intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
  rewrite (HKS (Z.of_nat i) ltac:(lia)). exact (Hz i ltac:(rewrite length_app; cbn [length]; lia)). }
split.
- split; [exact Hlp0|]. split; [exact HSTRZ|].
  (* the tail: the bytes after the NUL up to the 8-byte boundary *)
  destruct Hwh as [Hhp | [Hfp | (Himg & Hpin & Hpt)]].
  + destruct Hhp as (b & n & Hb & Hb1 & Hb2).
    assert (HbB : In (b, n) (ablocks B ly S2)) by exact (Permutation_in _ (Permutation_sym HPm) Hb).
    destruct (al_blocks _ _ LAWS ly S2 W2 mem2 md2 b n HAR2 HbB) as (_ & _ & _ & _ & _ & _ & Hn).
    pose proof (req_size_pos n ltac:(lia)) as [Hq1 Hq2].
    intros x Hx Hnone.
    exact (YG0d_tail.AR_block_word_vis SEGS B ly S2 W2 mem2 md2 b n (lp + Z.of_nat (length l)) x
             HAR2 HbB ltac:(lia) ltac:(lia) Hnone).
  + destruct Hfp as (cid & pos & Hin & Hcid & Hf1 & Hf2).
    assert (HinF2 : In (cid, pos) (frames S2)) by (rewrite Hfr; exact Hin).
    destruct (al_frames _ _ LAWS ly S2 W2 mem2 md2 cid pos HAR2 HinF2) as (Hal32 & _ & Hpres & _).
    intros x Hx Hnone.
    pose proof (s5d_fsb8 cid Hcid) as H8.
    pose proof (s5d_round8 (lp + Z.of_nat (length l)) (frame_addr ly cid pos + fs_frame_bytes cid)
                  ltac:(lia) ltac:(lia)) as HR.
    apply (aview_some_of_apresent SEGS (w_H W2) mem2 x); [|exact Hnone].
    apply (proj1 (Hpres x ltac:(lia))).
  + intros x Hx. pose proof (Hpt ly S2 W2 mem2 md2 HAR2) as Ht. exact (Ht x Hx).
- split; [exact Hlen|]. split.
  + destruct Hwh as [Hhp | [Hfp | (Himg & Hpin & Hpt)]].
    * destruct Hhp as (b & n & Hb & Hb1 & Hb2). left. exists b, n.
      split; [exact (Permutation_in _ (Permutation_sym HPm) Hb) | split; [exact Hb1 | exact Hb2]].
    * destruct Hfp as (cid & pos & Hin & Hcid & Hf1 & Hf2). right; left. exists cid, pos.
      split; [rewrite Hfr; exact Hin|]. split; [exact Hcid|].
      split; [exact Hf1 | exact Hf2].
    * right; right. split; [exact Himg | split; [exact Hpin | exact Hpt]].
  + split; [|split; [exact Hdm | exact Hdc]].
    (* the label's addressability at the new state *)
    destruct Hwh as [Hhp | [Hfp | (Himg & Hpin & Hpt)]].
    * destruct Hhp as (b & n & Hb & Hb1 & Hb2).
      assert (HbB : In (b, n) (ablocks B ly S2)) by exact (Permutation_in _ (Permutation_sym HPm) Hb).
      destruct (al_blocks _ _ LAWS ly S2 W2 mem2 md2 b n HAR2 HbB) as (_ & _ & _ & _ & _ & _ & Hn).
      pose proof (req_size_pos n ltac:(lia)) as [Hq1 Hq2].
      destruct Haddr as (A1 & A2 & A3 & _).
      split; [exact A1|]. split; [exact A2|]. split; [exact A3|].
      split; [exact (range_addressable_of_block SEGS B LAWS ly S2 W2 mem2 md2 b n lp
                       (Z.of_nat (length l) + 1) HAR2 HbB ltac:(lia) ltac:(lia))|].
      intros Hn0. exact (shadow_hull_vis_of_block SEGS B LAWS ly S2 W2 mem2 md2 b n lp
                           (Z.of_nat (length l) + 1) HAR2 HbB ltac:(lia) ltac:(lia) Hn0).
    * destruct Hfp as (cid & pos & Hin & Hcid & Hf1 & Hf2).
      assert (HinF2 : In (cid, pos) (frames S2)) by (rewrite Hfr; exact Hin).
      pose proof (s5d_fsb8 cid Hcid) as H8.
      destruct (al_frames _ _ LAWS ly S2 W2 mem2 md2 cid pos HAR2 HinF2) as (Hal32 & _ & _ & _).
      destruct Haddr as (A1 & A2 & A3 & A4 & A5).
      split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split.
      { intros x Hx. rewrite (KF cid pos (shadow_of_addr SHADOW_OFF x) Hin).
        - exact (A4 x Hx).
        - right. unfold shadow_of_addr, shadow_addr.
          pose proof (Z.div_mod (frame_addr ly cid pos) 8 ltac:(lia)) as D1.
          pose proof (Z.div_mod x 8 ltac:(lia)) as D2.
          pose proof (Z.div_mod (fs_frame_bytes cid) 8 ltac:(lia)) as D3.
          pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
          assert (frame_addr ly cid pos / 8 <= x / 8) by (apply Z.div_le_mono; lia).
          assert (x / 8 < frame_addr ly cid pos / 8 + fs_frame_bytes cid / 8) by
            (apply (Z.div_lt_upper_bound x 8 (frame_addr ly cid pos / 8 + fs_frame_bytes cid / 8)); lia).
          lia. }
      intros Hn0. exact (shadow_hull_vis_of_frame SEGS B LAWS ly S2 W2 mem2 md2 cid pos lp
                           (Z.of_nat (length l) + 1) HAR2 HinF2 ltac:(lia) ltac:(lia) ltac:(lia)).
    * exact (Hpin ly S2 W2 mem2 md2 HAR2).
Qed.

(* ---- the text's C string at a later reader: the bytes from the block, the tail from AR ---- *)
Lemma s5d_str_blk : forall ly S (W : world SEGS) mem md p (s : list Z) (rd : reader),
  AR SEGS B ly S W mem md -> In (p, Z.of_nat (length s) + 1) (ablocks B ly S) ->
  sa_strz rd p s -> (forall i, 0 <= i < Z.of_nat (length s) + 1 -> rdW W mem (p + i) = rd (p + i)) ->
  sa_str (rdW W mem) p s.
Proof using All.
intros ly S W mem md p s rd HAR Hin (Hz & Hn0) HK.
assert (Hreq : req_size (Z.of_nat (length s) + 1) = Z.of_nat (length s) + 1) by (apply s5d_req; lia).
split.
- split; [|exact Hn0]. intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
  rewrite (HK (Z.of_nat i) ltac:(lia)). exact (Hz i ltac:(rewrite length_app; cbn [length]; lia)).
- intros x Hx Hnone.
  exact (YG0d_tail.AR_block_word_vis SEGS B ly S W mem md p (Z.of_nat (length s) + 1)
           (p + Z.of_nat (length s)) x HAR Hin ltac:(lia) ltac:(lia) Hnone).
Qed.

(* ---- the readers of two states that agree on every address ---- *)
Definition s5d_eqv (rd rd' : reader) : Prop := forall a, 0 <= a < 2 ^ 64 -> rd' a = rd a.
Lemma s5d_eqv_addr : forall rd rd' q n, s5d_eqv rd rd' -> sa_addr rd q n -> sa_addr rd' q n.
Proof using All.
intros rd rd' q n HK (A1 & A2 & A3 & A4 & A5). pose proof asan_consts as (C1 & _).
split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split.
- intros x Hx. rewrite HK; [exact (A4 x Hx)|]. unfold shadow_of_addr, SHADOW_OFF. lia.
- intros Hn x Hx. rewrite HK; [exact (A5 Hn x Hx)|]. unfold shadow_addr, SHADOW_OFF in Hx.
  pose proof (Z.div_mod q 8 ltac:(lia)). pose proof (Z.div_mod (q + n - 1) 8 ltac:(lia)).
  pose proof (Z.div_mod (2147483648 + q / 8) 8 ltac:(lia)).
  pose proof (Z.div_mod (2147483648 + (q + n - 1) / 8) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (2147483648 + (q + n - 1) / 8) 8 ltac:(lia)).
  assert (q / 8 <= (q + n - 1) / 8) by (apply Z.div_le_mono; lia).
  assert ((q + n - 1) / 8 <= q + n) by (pose proof (Z.div_le_upper_bound (q + n - 1) 8 (q + n)); lia).
  lia.
Qed.
Lemma s5d_eqv_str : forall rd rd' p s, s5d_eqv rd rd' -> 0 <= p -> p + Z.of_nat (length s) + 8 <= 2 ^ 64 ->
  sa_str rd p s -> sa_str rd' p s.
Proof using All.
intros rd rd' p s HK Hp0 Hp1 ((Hz & Hn0) & Ht). split.
- split; [|exact Hn0]. intros i Hi. rewrite HK; [exact (Hz i Hi)|].
  rewrite length_app in Hi. cbn [length] in Hi. lia.
- intros x Hx. rewrite HK; [exact (Ht x Hx)|].
  pose proof (Z.mod_pos_bound (p + Z.of_nat (length s)) 8 ltac:(lia)). lia.
Qed.
Lemma s5d_eqv_ostr : forall rd rd' p (o : option (list Z)), s5d_eqv rd rd' -> 0 <= p ->
  (forall l, o = Some l -> p + Z.of_nat (length l) + 8 <= 2 ^ 64) -> sa_ostr rd p o -> sa_ostr rd' p o.
Proof using All.
intros rd rd' p o HK Hp0 Hb H. destruct o as [l|]; [|exact H].
destruct H as (H1 & H2). split; [exact H1|].
exact (s5d_eqv_str rd rd' p l HK Hp0 (Hb l eq_refl) H2).
Qed.
Lemma s5d_eqv_label : forall cx ly S rd rd' f lp c m, s5d_eqv rd rd' ->
  S5_label B ly S rd cx f lp c m -> S5_label B ly S rd' cx f lp c m.
Proof using All.
intros cx ly S rd rd' f lp c m HK (Hlp & HO & HM).
assert (Hb : forall l, s5_lab (x_pl cx) f = Some l -> lp + Z.of_nat (length l) + 8 <= 2 ^ 64).
{ intros l El. rewrite El in HM. destruct HM as (Hlen & _ & (A1 & A2 & _) & _). lia. }
split; [exact Hlp|]. split; [exact (s5d_eqv_ostr rd rd' lp _ HK ltac:(lia) Hb HO)|].
revert HM. destruct (s5_lab (x_pl cx) f) as [l|]; [|trivial].
intros (Hlen & Hwh & Haddr & Hdm & Hdc).
split; [exact Hlen|]. split; [exact Hwh|]. split; [exact (s5d_eqv_addr rd rd' lp _ HK Haddr)|].
split; [exact Hdm | exact Hdc].
Qed.

(* ---- the symbolic seeds ---- *)
Definition s5d_E (regs : bvmap 5 word) (extra : list word) : env := Eimg (Ereg regs extra).
Lemma s5d_E_reg : forall regs extra n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (s5d_E regs extra) n = getr regs r.
Proof using All.
intros regs extra n r H. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
unfold s5d_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact H.
Qed.
(* the seed of a stretch with no region and no fact (run 1, 0x852c8) *)
Lemma s5d_seed0 : forall pc (W : world SEGS) regs mem,
  st_ok_pi SEGS VAL (s5d_E regs []) (mkSS pc sr_atoms [] None (mkFacts [] [] []))
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof using All.
intros pc W regs mem. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- unfold s5d_E. apply regs_ok_Eimg_Ereg.
- reflexivity.
- apply Forall_nil.
- exact I.
- split; [exact I | split; [exact I | exact I]].
Qed.
(* a run that has no write window keeps every byte *)
Lemma s5d_nowin_kept : forall E (W : world SEGS) (m m' : word -> option byte),
  frame_of E [] (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  forall a, 0 <= a < 2 ^ 64 -> rdW W m' a = rdW W m a.
Proof using All.
intros E W m m' HF a Ha.
apply (kept_of_frame (segs:=SEGS) E [] (w_H W) m m' (fun _ => False) HF); [|exact Ha|tauto].
intros b wlo whi a' Hin. cbn [windows map In] in Hin. destruct Hin.
Qed.
(* the seed at 0x852d4, where the run reads c from 168(s1) *)
Lemma s5d_seed2 : forall (W : world SEGS) (regs : bvmap 5 word) mem s1 c,
  getr regs 9 = w64 s1 -> 2 ^ 46 <= s1 -> s1 + 176 <= 2 ^ 47 -> s1 mod 32 = 0 ->
  4096 <= c -> c <= 2 ^ 47 -> c mod 16 = 0 ->
  rdword (rdW W mem) (s1 + 168) = Some c ->
  st_ok_pi SEGS VAL (s5d_E regs [Z_to_bv 64 c]) s5d_ss2
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + s5d_ra1)) mem (seg_rom SEGS))).
Proof using All.
intros W regs mem s1 c R9 Hs1a Hs1b Hs1c Hc1 Hc2 Hc16 Hw168.
set (E := s5d_E regs [Z_to_bv 64 c]).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 c]) n)
  by (intros n Hn; subst E; unfold s5d_E; apply Eimg_low; exact Hn).
assert (E9 : ew E 9 = Z_to_bv 64 s1)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact R9).
assert (E32 : ew E 32 = Z_to_bv 64 c) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (VB : base_val E (Some 9%nat) = s1)
  by (cbn [base_val]; rewrite E9; apply YP03.unsigned_lit_small; lia).
pose proof (val_mem_of_rdword SEGS (w_H W) mem (s1 + 168) c Hw168) as HV168.
unfold s5d_ss2. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- subst E. unfold s5d_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold s5d_rg2. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]; rewrite VB;
    (split; [lia|]); (split; [lia|]).
  split; [intros o Ho; lia|]. repeat apply Forall_cons; try apply Forall_nil.
  apply (chunk_ok_val SEGS E _ s1 168 8 (SOff 32 0) c);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia | exact HV168].
- apply pairwise_disjoint_of_extents. unfold s5d_rg2, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite VB.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; try exact I; lia.
- split; [|split; [exact I | exact I]].
  cbn [s5d_fa2 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E9, E32, !YP03.unsigned_lit_small by lia.
  change (2 ^ 5) with 32. change (2 ^ 4) with 16.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.

(* ================================ the two program calls ================================ *)
(* 0x852d0: m_file(m, text, label) through PaFx.cl_callSF, the contract at the FP state the walk reached, to its
   return at 0x852d4 at the FP state fx1 the call leaves (METHOD.md section 4.6) *)
Lemma s5d_mf_call : forall (fxa : YK11.FPState) cx ly S (W : world SEGS) regsT memT md k acc rem o O
  (m t lp : Z) (mc : SegModel.mconf) (s : list Z) (lab : option (list Z)),
  lt_base B MT cx -> frm0 fxa ->
  lt_core B MT cx ly S W regsT memT md k acc rem o O ->
  getr regsT 1 = w64 (BASE + s5d_ra1) ->
  getr regsT 10 = w64 m -> getr regsT 11 = w64 t -> getr regsT 12 = w64 lp ->
  0 <= m < 2 ^ 64 -> 0 <= t < 2 ^ 64 -> 0 <= lp < 2 ^ 64 ->
  In (m, seg_spec.SEG_M_SIZE) (ablocks B ly S) -> ~ In (m, seg_spec.SEG_M_SIZE) (x_bl0 B cx) ->
  m_file_c.m_file_pre SEGS B ly S (rdW W memT) m t lp mc s lab ->
  (forall (fx1 : YK11.FPState) ly2 S2 (W2 : world SEGS) regs2 mem2 md2,
     fxrel fxa fx1 ->
     ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
       (x_md cx) [(LT_FCLS, x_fpos cx)] ly2 S2 W2 mem2 md2 k ->
     ajournal SEGS B STK_m_file (x_s1 cx)
       (M_FILE_FP m (length (SegModel.mc_kept mc)) (SegModel.m_file mc s lab))
       ly S W memT md [] ly2 S2 W2 mem2 md2 EV_m_file ->
     aregs_preserved regsT regs2 ->
     sa_mconf (rdW W2 mem2) m (SegModel.m_file mc s lab) ->
     sa_noalloc B ly S ly2 S2 ->
     SRr SEGS W2 (mkCfg (@mkst fx1 regs2 (w64 (BASE + s5d_ra1)) mem2 (seg_rom SEGS)) md2)
       (lt_post (fx := fx1) B MT cx)) ->
  SRr SEGS W (mkCfg (@mkst fxa regsT (Z_to_bv 64 (BASE + AF_m_file)) memT (seg_rom SEGS)) md)
    (lt_post (fx := fxa) B MT cx).
Proof using All.
intros fxa cx ly S W regsT memT md k acc rem o O m t lp mc s lab HB Hfrm0 HC R1 R10 R11 R12
  Hm64 Ht64 Hlp64 HmIn Hmn0 HPRE HK.
pose proof (s5d_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
pose proof HC as (HF & HI & HBL & HBUD).
pose proof HF as (HJ & R2 & R3 & R4 & R8 & R9 & _).
pose proof (proj1 HJ) as HAR.
pose proof HB as (HPRE0 & HAP0 & _ & _ & _ & _ & _ & _ & _ & Hfr0 & _ & Hev & _).
pose proof HPRE0 as (_ & _ & _ & Hgp0 & Htp0 & _).
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & Hnev & _).
pose proof HBUD as (B1 & B2 & B3 & B4 & B5 & B6).
pose proof asan_consts as (C1 & _).
pose proof pa_B_ok as (HBa & HBb & _). pose proof pa_base_lo as HBLO.
assert (HSTK : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity.
assert (HSM : STK_m_file = 8592) by reflexivity.
destruct HI as (HRO & HIMG & HGI).
destruct HIMG as (Hm40 & Hm40i & Hfz & Hrcl & Hcat & Hcata & Hw & Hrl & Hssp & _).
assert (HROOM : sa_room S) by (unfold sa_room; rewrite Hfrs, Hfr0; cbn [app length]; lia).
assert (HEV : st_nev S + EV_m_file <= EV_MAX) by (unfold EV_m_file, EV_LTOI in *; lia).
assert (HLITS : forall x, In x m_file_c.M_FILE_LITS -> sa_lit SEGS B (rdW W memT) (seg_litA_fz x) x).
{ intros x Hx. destruct (Hfz x ltac:(unfold LTOI_FZ_LITS; apply in_or_app; right; apply in_or_app; right;
    apply in_or_app; right; exact Hx)) as [H1 _]. exact H1. }
assert (HWF : s5d_mwf (SegModel.m_file mc s lab)).
{ apply s5d_file_wf. destruct HPRE as (_ & _ & Hmc & _). exact (s5d_mwf_of _ _ _ Hmc). }
assert (Hsp' : spZ regsT = x_sp0 cx + (x_s1 cx - x_sp0 cx)).
{ unfold spZ. rewrite R2. unfold w64. rewrite YP03.unsigned_lit_small by lia. lia. }
assert (Hraw : YK0s.ret_ok (getr regsT 1))
  by (rewrite R1; unfold w64; apply ret_ok_codeptr_v; [unfold s5d_ra1; lia | reflexivity]).
assert (Hra4 : 4096 <= bv_unsigned (getr regsT 1))
  by (rewrite R1; unfold w64, s5d_ra1; rewrite YP03.unsigned_lit_small by lia; lia).
(* the frame chain at the call's sp *)
assert (HAP : astack_pres ly (w_H W) memT (x_sp0 cx - STK_LLVMFuzzerTestOneInput)).
{ apply (astack_pres_journal SEGS B pa_segs_low STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA)
    (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W memT md k HJ HAP0).
  intros a (r & Hr & Ha) Ha2. exfalso. unfold ltoi_PG in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  unfold longlA, A_LONGL, LONGL_N in Ha. lia. }
pose proof (astack_rd_of_pres SEGS ly (w_H W) memT (x_s1 cx)
  (astack_pres_mono ly (w_H W) memT (x_sp0 cx - STK_LLVMFuzzerTestOneInput) (x_s1 cx) ltac:(lia) HAP)) as HRD.
destruct (achain_any ly (rdW W memT) (x_s1 cx) (x_sp0 cx) HRD ltac:(right; right; right; lia)) as (ch & Hch).
assert (Hch' : achain ly (rdW W memT) (x_sp0 cx + (x_s1 cx - x_sp0 cx)) (s0Z regsT) ch).
{ replace (x_sp0 cx + (x_s1 cx - x_sp0 cx)) with (x_s1 cx) by lia.
  unfold s0Z. rewrite R8. unfold w64. rewrite YP03.unsigned_lit_small by lia. exact Hch. }
unfold lt_post.
eapply (srr_after_callF (fx := fxa) SEGS).
{ apply (cl_callSF (fx := fxa) B LAWS W regsT memT (Z_to_bv 64 (BASE + AF_m_file))
    STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx)
    [(LT_FCLS, x_fpos cx)] ly S md k STK_m_file
    (M_FILE_FP m (length (SegModel.mc_kept mc)) (SegModel.m_file mc s lab)) EV_m_file
    (x_s1 cx - x_sp0 cx) (getr regsT 1) ch
    (fun ly' S' (W' : world SEGS) (regs' : bvmap 5 word) mem' md' =>
       sa_mconf (aview SEGS (w_H W') mem') m (SegModel.m_file mc s lab) /\ sa_noalloc B ly S ly' S')
    HJ Hsp' ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(rewrite R3; exact Hgp0) ltac:(rewrite R4; exact Htp0) eq_refl Hraw Hra4 Hch').
  - intros HPRE1. eapply SRr_mono;
      [exact (HM_FILE fxa ly S W regsT memT md ch m t lp mc s lab HPRE1 Hfrm0 HROOM HRO HLITS Hw Hrl Hcat Hssp
                R10 Hm64 R11 Ht64 R12 Hlp64 HPRE HEV)
      | intros W3 c3 _ H3; exact H3].
  - intros a Ha. right. exists m, seg_spec.SEG_M_SIZE.
    split; [exact HmIn|]. split; [exact Hmn0|].
    pose proof (s5d_mfp_in m (length (SegModel.mc_kept mc)) (SegModel.m_file mc s lab) HWF a Ha) as Hin.
    change (req_size seg_spec.SEG_M_SIZE) with 9236. unfold seg_spec.SEG_M_SIZE in Hin. lia. }
intros fx1 ly2 S2 W2 regs2 mem2 md2 _ Hfxr (HJ2 & HJc & HPr & (Hmconf & HNA)).
replace (k + EV_m_file) with k in HJ2 by (unfold EV_m_file; lia).
replace (x_sp0 cx + (x_s1 cx - x_sp0 cx)) with (x_s1 cx) in HJc by ring.
rewrite R1. exact (HK fx1 ly2 S2 W2 regs2 mem2 md2 Hfxr HJ2 HJc HPr Hmconf HNA).
Qed.

(* 0x852e0: reac_segconf_parse_file(c, text, label), to its return at the kit's cut 0x852e4 *)
Lemma s5d_pf_call : forall (fxa : YK11.FPState) cx ly S (W : world SEGS) regsT memT md k acc rem o O
  (c t lp : Z) (rcs : SegModel.rconf) (s : list Z) (lab : option (list Z)),
  lt_base B MT cx ->
  lt_core B MT cx ly S W regsT memT md k acc rem o O ->
  getr regsT 1 = w64 (BASE + LO_S5CK) ->
  getr regsT 10 = w64 c -> getr regsT 11 = w64 t -> getr regsT 12 = w64 lp ->
  0 <= c < 2 ^ 64 -> 0 <= t < 2 ^ 64 -> 0 <= lp < 2 ^ 64 ->
  In (c, seg_spec.SEG_C_SIZE) (ablocks B ly S) -> ~ In (c, seg_spec.SEG_C_SIZE) (x_bl0 B cx) ->
  reac_segconf_parse_file_c.reac_segconf_parse_file_pre SEGS B seg_litA_rc catA gotwA guardA ly S
    (rdW W memT) c t lp rcs s lab ->
  (forall (fx1 : YK11.FPState) ly2 S2 (W2 : world SEGS) regs2 mem2 md2,
     fxrel fxa fx1 ->
     ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
       (x_md cx) [(LT_FCLS, x_fpos cx)] ly2 S2 W2 mem2 md2 k ->
     ajournal SEGS B STK_reac_segconf_parse_file (x_s1 cx) (seg_spec.RC_PARSE_W c)
       ly S W memT md [] ly2 S2 W2 mem2 md2 EV_reac_segconf_parse_file ->
     aregs_preserved regsT regs2 ->
     getr regs2 10 = w64 (snd (SegModel.r_parse_file rcs s lab)) ->
     sa_rconf (rdW W2 mem2) c (fst (SegModel.r_parse_file rcs s lab)) ->
     sa_noalloc B ly S ly2 S2 ->
     SRr SEGS W2 (mkCfg (@mkst fx1 regs2 (w64 (BASE + LO_S5CK)) mem2 (seg_rom SEGS)) md2)
       (lt_post (fx := fx1) B MT cx)) ->
  SRr SEGS W (mkCfg (@mkst fxa regsT (Z_to_bv 64 (BASE + AF_reac_segconf_parse_file)) memT (seg_rom SEGS)) md)
    (lt_post (fx := fxa) B MT cx).
Proof using All.
intros fxa cx ly S W regsT memT md k acc rem o O c t lp rcs s lab HB HC R1 R10 R11 R12
  Hc64 Ht64 Hlp64 HcIn Hcn0 HPRE HK.
pose proof (s5d_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
pose proof HC as (HF & HI & HBL & HBUD).
pose proof HF as (HJ & R2 & R3 & R4 & R8 & R9 & _).
pose proof (proj1 HJ) as HAR.
pose proof HB as (HPRE0 & HAP0 & _ & _ & _ & _ & _ & _ & _ & Hfr0 & _ & Hev & _).
pose proof HPRE0 as (_ & _ & _ & Hgp0 & Htp0 & _).
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & Hnev & _).
pose proof HBUD as (B1 & B2 & B3 & B4 & B5 & B6).
pose proof asan_consts as (C1 & _).
pose proof pa_B_ok as (HBa & HBb & _). pose proof pa_base_lo as HBLO.
assert (HSTK : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity.
assert (HSP : STK_reac_segconf_parse_file = 12832) by reflexivity.
destruct HI as (HRO & HIMG & HGI).
assert (HROOM : sa_room_n 2 S) by (unfold sa_room_n; rewrite Hfrs, Hfr0; cbn [app length]; lia).
assert (HEV : st_nev S + EV_reac_segconf_parse_file <= EV_MAX)
  by (unfold EV_reac_segconf_parse_file, EV_LTOI in *; lia).
assert (Hsp' : spZ regsT = x_sp0 cx + (x_s1 cx - x_sp0 cx)).
{ unfold spZ. rewrite R2. unfold w64. rewrite YP03.unsigned_lit_small by lia. lia. }
assert (Hraw : YK0s.ret_ok (getr regsT 1))
  by (rewrite R1; unfold w64; apply ret_ok_codeptr_v; [unfold LO_S5CK; lia | reflexivity]).
assert (Hra4 : 4096 <= bv_unsigned (getr regsT 1))
  by (rewrite R1; unfold w64, LO_S5CK; rewrite YP03.unsigned_lit_small by lia; lia).
assert (HAP : astack_pres ly (w_H W) memT (x_sp0 cx - STK_LLVMFuzzerTestOneInput)).
{ apply (astack_pres_journal SEGS B pa_segs_low STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA)
    (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W memT md k HJ HAP0).
  intros a (r & Hr & Ha) Ha2. exfalso. unfold ltoi_PG in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  unfold longlA, A_LONGL, LONGL_N in Ha. lia. }
pose proof (astack_rd_of_pres SEGS ly (w_H W) memT (x_s1 cx)
  (astack_pres_mono ly (w_H W) memT (x_sp0 cx - STK_LLVMFuzzerTestOneInput) (x_s1 cx) ltac:(lia) HAP)) as HRD.
destruct (achain_any ly (rdW W memT) (x_s1 cx) (x_sp0 cx) HRD ltac:(right; right; right; lia)) as (ch & Hch).
assert (Hch' : achain ly (rdW W memT) (x_sp0 cx + (x_s1 cx - x_sp0 cx)) (s0Z regsT) ch).
{ replace (x_sp0 cx + (x_s1 cx - x_sp0 cx)) with (x_s1 cx) by lia.
  unfold s0Z. rewrite R8. unfold w64. rewrite YP03.unsigned_lit_small by lia. exact Hch. }
unfold lt_post.
eapply (srr_after_callF (fx := fxa) SEGS).
{ apply (cl_callSF (fx := fxa) B LAWS W regsT memT (Z_to_bv 64 (BASE + AF_reac_segconf_parse_file))
    STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx)
    [(LT_FCLS, x_fpos cx)] ly S md k STK_reac_segconf_parse_file (seg_spec.RC_PARSE_W c)
    EV_reac_segconf_parse_file
    (x_s1 cx - x_sp0 cx) (getr regsT 1) ch
    (fun ly' S' (W' : world SEGS) (regs' : bvmap 5 word) mem' md' =>
       getr regs' 10 = w64 (snd (SegModel.r_parse_file rcs s lab)) /\
       sa_rconf (aview SEGS (w_H W') mem') c (fst (SegModel.r_parse_file rcs s lab)) /\
       sa_noalloc B ly S ly' S')
    HJ Hsp' ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(rewrite R3; exact Hgp0) ltac:(rewrite R4; exact Htp0) eq_refl Hraw Hra4 Hch').
  - intros HPRE1. eapply SRr_mono;
      [exact (HPARSE_FILE fxa ly S W regsT memT md ch c t lp rcs s lab HPRE1 HRO
                R10 Hc64 R11 Ht64 R12 Hlp64 HPRE HROOM HEV)
      | intros W3 c3 _ H3; exact H3].
  - intros a Ha. right. exists c, seg_spec.SEG_C_SIZE.
    split; [exact HcIn|]. split; [exact Hcn0|].
    pose proof (s5d_pfp_in c a Ha) as Hin.
    change (req_size seg_spec.SEG_C_SIZE) with 16616. unfold seg_spec.SEG_C_SIZE in Hin. lia. }
intros fx1 ly2 S2 W2 regs2 mem2 md2 _ Hfxr (HJ2 & HJc & HPr & (Hans & Hrconf & HNA)).
replace (k + EV_reac_segconf_parse_file) with k in HJ2 by (unfold EV_reac_segconf_parse_file; lia).
replace (x_sp0 cx + (x_s1 cx - x_sp0 cx)) with (x_s1 cx) in HJc by ring.
rewrite R1. exact (HK fx1 ly2 S2 W2 regs2 mem2 md2 Hfxr HJ2 HJc HPr Hans Hrconf HNA).
Qed.

(* ======================================== L4 ======================================== *)
Lemma s5_calls : forall f, S5A_CK B MT f -> S5_OTH_stmt B MT f.
Proof using All.
intros f HKA. unfold S5_OTH_stmt.
intros cx ly S W regs mem md k acc c m t lp HB Hfrm Hf HBODY HCM HSTR HLAB R10 R18 R19 R21 R22 R23 R24 R25
  R26 HSL.
destruct HBODY as (HC & HHc & HHm & HHt & HCNT).
destruct HCM as (Hrc & Hmc).
pose proof HC as (HFRM & HIMG & HBL & HBUD).
pose proof HFRM as (HJ & R2 & R3 & R4 & R8 & R9 & HSV & HH0 & HH8 & HH16 & HFL & H200 & HSH & H184).
pose proof (proj1 HJ) as HAR.
pose proof (s5d_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBok. pose proof pa_base_lo as HBLO.
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _).
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hfr0 & _).
assert (HF1 : frames S = [(LT_FCLS, x_fpos cx)]) by (rewrite Hfrs, Hfr0; reflexivity).
assert (HinF : In (LT_FCLS, x_fpos cx) (frames S)) by (rewrite HF1; left; reflexivity).
assert (EFr : frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx)
  by exact (s5d_frame_addr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ _ _).
pose proof HHm as (HmIn & Hm4 & Hm16 & Hmaddr).
pose proof HHc as (HcIn & Hc4 & Hc16 & Hcaddr).
pose proof HHt as (HtIn & Ht4 & Ht16 & Htaddr).
pose proof Hmaddr as (Hm0 & Hmhi & _). pose proof Hcaddr as (Hc0 & Hchi & _).
pose proof Htaddr as (Ht0 & Hthi & _).
assert (HRM : req_size seg_spec.SEG_M_SIZE = seg_spec.SEG_M_SIZE) by reflexivity.
assert (HRC : req_size seg_spec.SEG_C_SIZE = seg_spec.SEG_C_SIZE) by reflexivity.
assert (Etn : x_tn cx f = Z.of_nat (length (s5_txt (x_pl cx) f)) + 1) by reflexivity.
assert (HRT : req_size (x_tn cx f) = x_tn cx f) by (apply s5d_req; lia).
assert (HPOW : 2 ^ 63 < 2 ^ 64) by (vm_compute; reflexivity).
assert (HSM0 : 0 < seg_spec.SEG_M_SIZE) by (vm_compute; reflexivity).
assert (HSC0 : 0 < seg_spec.SEG_C_SIZE) by (vm_compute; reflexivity).
assert (HTN0 : 0 < x_tn cx f) by (rewrite Etn; lia).
assert (HP46 : 2 ^ 46 <= 140737479966720) by (vm_compute; discriminate).
assert (HP47 : 140737479966720 < 2 ^ 47) by (vm_compute; reflexivity).
destruct (al_blocks _ _ LAWS ly S W mem md c _ HAR HcIn) as (_ & _ & Hcce & _ & _ & _ & _).
destruct (al_blocks _ _ LAWS ly S W mem md m _ HAR HmIn) as (_ & _ & Hmce & _ & _ & _ & _).
rewrite HRC in Hcce. rewrite HRM in Hmce.
(* the three blocks are distinct and none is the entry's *)
assert (HND : List.NoDup (ablocks B ly S)) by exact (s5d_nodup ly S W mem md HAR).
pose proof (Permutation_NoDup HBL HND) as HND2. cbn [app] in HND2.
apply NoDup_cons_iff in HND2 as (Hnt & HND3).
apply NoDup_cons_iff in HND3 as (Hnm & HND4).
apply NoDup_cons_iff in HND4 as (Hnc & _).
assert (Hmn0 : ~ In (m, seg_spec.SEG_M_SIZE) (x_bl0 B cx)) by (intros Hx; apply Hnm; right; exact Hx).
assert (Hcn0 : ~ In (c, seg_spec.SEG_C_SIZE) (x_bl0 B cx)) by exact Hnc.
assert (Dtm : zdisjoint (t, req_size (x_tn cx f)) (m, req_size seg_spec.SEG_M_SIZE)).
{ apply (sep_blocks SEGS B LAWS ly S W mem md t _ m _ HAR HtIn HmIn).
  intros E. apply Hnt. left. exact (eq_sym E). }
assert (Dcm : zdisjoint (c, req_size seg_spec.SEG_C_SIZE) (m, req_size seg_spec.SEG_M_SIZE)).
{ apply (sep_blocks SEGS B LAWS ly S W mem md c _ m _ HAR HcIn HmIn).
  intros E. apply Hnm. left. exact E. }
assert (Dtc : zdisjoint (t, req_size (x_tn cx f)) (c, req_size seg_spec.SEG_C_SIZE)).
{ apply (sep_blocks SEGS B LAWS ly S W mem md t _ c _ HAR HtIn HcIn).
  intros E. apply Hnt. right. left. exact (eq_sym E). }
rewrite HRM, HRT in Dtm. rewrite HRM, HRC in Dcm. rewrite HRC, HRT in Dtc.
unfold zdisjoint in Dtm, Dcm, Dtc. cbn [fst snd] in Dtm, Dcm, Dtc.
(* the turn's text and the model's counters *)
destruct (s5d_txt_ok (x_pl cx) f) as (Hnul & Hlen).
pose proof (s5d_nfiles (x_pl cx)) as Hnf. unfold x_nf in Hf.
assert (Hfle : 0 <= Z.of_nat f <= 2) by lia.
pose proof HCNT as (N1 & N2 & N3 & N4 & N5 & N6).
change (2 ^ 20) with 1048576 in N2, N3, N5, N6.
(* the slots *)
assert (Hobnd : forall o v, In (o, v) (S5_slots cx c m f) -> 16 <= o <= 216).
{ intros o v Hin. unfold S5_slots, LT_L in Hin. apply in_app_or in Hin as [Hin | Hin]; cbn [In] in Hin;
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- _; lia|]); destruct Hin. }
assert (S168 : rdword (rdW W mem) (x_s1 cx + 168) = Some c)
  by (apply HSL; unfold S5_slots, LT_L; apply in_or_app; left; cbn [In]; tauto).
(* the tail of the mconf block, at any state of the same layout *)
assert (HmTail : forall (Wx : world SEGS) memx mdx, AR SEGS B ly S Wx memx mdx ->
  sa_tail (rdW Wx memx) (m + seg_spec.SEG_M_SIZE - 1)).
{ intros Wx memx mdx HARx x Hx Hnone.
  exact (YG0d_tail.AR_block_word_vis SEGS B ly S Wx memx mdx m seg_spec.SEG_M_SIZE
           (m + seg_spec.SEG_M_SIZE - 1) x HARx HmIn ltac:(unfold seg_spec.SEG_M_SIZE in *; lia)
           ltac:(lia) Hnone). }
(* ---------------- run 1: 0x852c8 .. 0x852d0, the jal of m_file ---------------- *)
pose proof (s5d_seed0 LO_S5OTH W regs mem) as HS.
assert (SHOK : sh_ok SEGS s5d_X [] (s5d_E regs []) (mrestrict (w_H W) mem)) by apply Forall_nil.
assert (HEI : img_env VAL A_LIM (s5d_E regs [])) by (unfold s5d_E; apply Eimg_env).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew (s5d_E regs []) n = getr regs rr)
  by (intros n rr Hn; exact (s5d_E_reg regs [] n rr Hn)).
remember (s5d_E regs []) as E eqn:HE. clear HE.
unfold cfg_at, w64.
paj_run_tok RUN HS HJ SHOK s5d_span.
{ apply awr_ok_nil. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md1 := d) in *; clearbody md1 end.
pmkst HS.
rewrite (SIGP SS_m_file ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_m_file) with AF_m_file by (vm_compute; reflexivity).
prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
prreg HS (12%bv : bv 5) P12.
assert (KR : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 24; 25; 26]%bv ->
  getr (ms_regs ms) r = getr regs r).
{ intros r Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr];
    [ let P := fresh "P" in lazymatch goal with |- getr _ ?rr = _ => prreg HS rr P end;
      rewrite P; apply EEo; reflexivity | ]).
  destruct Hr. }
pose proof (s5d_nowin_kept E W mem (ms_mem ms) HFr) as KM.
pose proof (s5d_core_run cx ly S W regs mem md k acc (5 + 2 * (x_nf cx - Z.of_nat f)) LFO_L
  [(t, x_tn cx f); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] (ms_regs ms) (ms_mem ms) md1 0 0
  HB HC HJ ltac:(intros a Ha _; exact (KM a Ha)) ltac:(lia) ltac:(lia)
  (KR 2%bv ltac:(cbn; tauto)) (KR 3%bv ltac:(cbn; tauto)) (KR 4%bv ltac:(cbn; tauto))
  (KR 8%bv ltac:(cbn; tauto)) (KR 9%bv ltac:(cbn; tauto))) as HC1.
pose proof (proj1 (proj1 HC1)) as HJ1. pose proof (proj1 HJ1) as HAR1.
(* the facts at the reader the run leaves *)
assert (Hrc1 : sa_rconf (rdW W (ms_mem ms)) c (seg_spec.seg_rc (x_st cx f))).
{ apply (s5d_rconf_kept (rdW W mem)); [|exact Hrc]. intros i Hi. apply KM.
  unfold seg_spec.SEG_C_SIZE in *. lia. }
assert (Hmc1 : sa_mconf (rdW W (ms_mem ms)) m (seg_spec.seg_mc (x_st cx f))).
{ apply (s5d_mconf_kept (rdW W mem)); [|exact Hmc]. intros i Hi. apply KM.
  unfold seg_spec.SEG_M_SIZE in *. lia. }
assert (HSTR1 : sa_str (rdW W (ms_mem ms)) t (s5_txt (x_pl cx) f))
  by (apply (s5d_eqv_str (rdW W mem)); [exact KM | lia | lia | exact HSTR]).
assert (HLAB1 : S5_label B ly S (rdW W (ms_mem ms)) cx f lp c m)
  by (apply (s5d_eqv_label cx ly S (rdW W mem)); [exact KM | exact HLAB]).
assert (HSL1 : lt_slots cx (rdW W (ms_mem ms)) (S5_slots cx c m f)).
{ intros o v Hin. pose proof (Hobnd o v Hin) as Ho.
  apply (s5d_word_kept (rdW W mem)); [|exact (HSL o v Hin)]. intros x Hx. apply KM. lia. }
(* the call of m_file *)
apply (s5d_mf_call fx cx ly S W (ms_regs ms) (ms_mem ms) md1 k acc (5 + 2 * (x_nf cx - Z.of_nat f)) LFO_L
  [(t, x_tn cx f); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)]
  m t lp (seg_spec.seg_mc (x_st cx f)) (s5_txt (x_pl cx) f) (s5_lab (x_pl cx) f) HB Hfrm HC1).
{ rewrite P1. reflexivity. }
{ rewrite P10, (EEo 10%nat 10%bv eq_refl). exact R10. }
{ rewrite P11, (EEo 23%nat 23%bv eq_refl). exact R23. }
{ rewrite P12, (EEo 19%nat 19%bv eq_refl). exact R19. }
{ lia. }
{ lia. }
{ pose proof HLAB as (Hlp & _ & _). lia. }
{ exact HmIn. }
{ exact Hmn0. }
{ (* m_file_pre *)
  split; [lia|]. split; [exact Hm16|]. split; [exact Hmc1|].
  split; [exists m, seg_spec.SEG_M_SIZE; split; [exact HmIn | split; lia]|].
  split; [apply (s5d_eqv_addr (rdW W mem)); [exact KM | exact Hmaddr]|].
  split; [exact (HmTail W (ms_mem ms) md1 HAR1)|].
  split; [change (2 ^ 31) with 2147483648; lia|].
  split; [change (2 ^ 17) with 131072; change (2 ^ 32) with 4294967296; lia|].
  split; [change (2 ^ 17) with 131072; change (2 ^ 32) with 4294967296; lia|].
  split; [lia|]. split; [exact HSTR1|]. split; [exact Hlen|].
  split; [exists t, (x_tn cx f); split; [exact HtIn | split; lia]|].
  split; [rewrite <- Etn; apply (s5d_eqv_addr (rdW W mem)); [exact KM | exact Htaddr]|].
  split.
  { destruct (al_blocks _ _ LAWS ly S W mem md t _ HAR HtIn) as (_ & _ & _ & Htapp & _).
    rewrite HRT in Htapp.
    exact (a3_amem_slack t (x_tn cx f) t (Z.of_nat (length (s5_txt (x_pl cx) f)) + 8) Htapp
             ltac:(lia) ltac:(lia) ltac:(lia)). }
  split.
  { unfold sa_disj. destruct Dtm as [Dtm | Dtm]; [left | right; unfold seg_spec.SEG_M_SIZE in *; lia].
    apply (s5d_span_le t (s5_txt (x_pl cx) f) m); [lia|].
    pose proof (Z.div_mod m 16 ltac:(lia)). lia. }
  pose proof HLAB1 as (Hlp1 & HO1 & HM1).
  split; [exact HO1|].
  revert HM1. destruct (s5_lab (x_pl cx) f) as [l|]; [|trivial].
  intros (Hlen1 & Hwh1 & Haddr1 & Hdm1 & Hdc1).
  split; [exact Hlen1|]. split; [exact Hwh1|]. split; [exact Haddr1|].
  unfold sa_disj in Hdm1 |- *. unfold seg_spec.MC_READING, seg_spec.SEG_M_SIZE in *. lia. }
(* ---------------- the state m_file left ---------------- *)
intros fx1 ly2 S2 W2 regs2 mem2 md2 Hfxr HJ2 HJc HPr Hmconf HNA.
pose proof HNA as (HPm & Ely & HSfs). subst ly2.
destruct HSfs as (fsf & ESfs).
pose proof HJc as (_ & _ & _ & _ & _ & Hfr2 & _). cbn [app] in Hfr2.
pose proof (proj1 HJc) as HAR2.
destruct (s5d_jkeep cx ly S W (ms_mem ms) md1 STK_m_file
  (M_FILE_FP m (length (SegModel.mc_kept (seg_spec.seg_mc (x_st cx f))))
     (SegModel.m_file (seg_spec.seg_mc (x_st cx f)) (s5_txt (x_pl cx) f) (s5_lab (x_pl cx) f)))
  EV_m_file ly S2 W2 mem2 md2 m seg_spec.SEG_M_SIZE HB HAR1 HinF HJc HmIn
  ltac:(unfold seg_spec.SEG_M_SIZE; lia) HRM
  ltac:(intros a Ha; exact (s5d_mfp_in m _ _ (s5d_file_wf _ _ _ (s5d_mwf_of _ _ _ Hmc1)) a Ha))
  HPm EFr) as (KS2 & KI2 & KF2 & KB2).
assert (MLE2 : mo_le MT (x_S cx) S2 acc).
{ rewrite ESfs. apply (mo_le_set_fs_r MT MTFL).
  pose proof HC1 as (_ & _ & _ & HBUD1). exact (proj1 (proj2 (proj2 (proj2 HBUD1)))). }
pose proof (s5d_carry cx ly S W (ms_regs ms) (ms_mem ms) md1 k acc (5 + 2 * (x_nf cx - Z.of_nat f)) LFO_L
  [(t, x_tn cx f); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] ly S2 W2 regs2 mem2 md2
  HB HC1 HJ2 HPr HPm MLE2 KS2 KI2 KF2) as HC2.
assert (KFL : forall cid pos a, In (cid, pos) (frames S) ->
  (frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid \/
   shadow_addr (frame_addr ly cid pos) <= a < shadow_addr (frame_addr ly cid pos) + fs_frame_bytes cid / 8) ->
  rdW W2 mem2 a = rdW W (ms_mem ms) a).
{ intros cid pos a Hin Hr. rewrite HF1 in Hin. cbn [In] in Hin. destruct Hin as [Eq | []].
  injection Eq as <- <-. rewrite EFr in Hr.
  assert (F512 : fs_frame_bytes LT_FCLS = 512) by (vm_compute; reflexivity).
  rewrite F512 in Hr. apply KF2. unfold x_sh. destruct Hr as [Hr | Hr]; [left | right]; lia. }
assert (Hlabdisj : forall a, m <= a < m + seg_spec.SEG_M_SIZE ->
  ~ (lp <= a < lp + seg_spec.cstr_span lp
       (match s5_lab (x_pl cx) f with Some l => l | None => [] end))).
{ intros a Ha. pose proof HLAB1 as (Hlp1 & HO1 & HM1). revert HO1 HM1.
  destruct (s5_lab (x_pl cx) f) as [l|]; intros HO1 HM1.
  - destruct HM1 as (_ & _ & _ & Hdm1 & _). unfold sa_disj in Hdm1. lia.
  - cbn in HO1. subst lp. unfold seg_spec.cstr_span. cbn [length].
    pose proof (Z.mod_pos_bound (- (0 + 0 + 1)) 8 ltac:(lia)). lia. }
assert (HLAB2 : S5_label B ly S2 (rdW W2 mem2) cx f lp c m).
{ apply (s5d_lab_kept cx ly S W (ms_mem ms) S2 W2 mem2 md2 f lp c m m seg_spec.SEG_M_SIZE HAR2 HmIn
    ltac:(unfold seg_spec.SEG_M_SIZE; lia) HRM HPm Hfr2 KI2 KFL KB2 Hlabdisj HLAB1). }
assert (HmIn2 : In (m, seg_spec.SEG_M_SIZE) (ablocks B ly S2))
  by exact (Permutation_in _ (Permutation_sym HPm) HmIn).
assert (HcIn2 : In (c, seg_spec.SEG_C_SIZE) (ablocks B ly S2))
  by exact (Permutation_in _ (Permutation_sym HPm) HcIn).
assert (HtIn2 : In (t, x_tn cx f) (ablocks B ly S2))
  by exact (Permutation_in _ (Permutation_sym HPm) HtIn).
assert (Hrc2 : sa_rconf (rdW W2 mem2) c (seg_spec.seg_rc (x_st cx f))).
{ apply (s5d_rconf_kept (rdW W (ms_mem ms))); [|exact Hrc1]. intros i Hi.
  replace (c + i) with (c + i) by reflexivity.
  apply (KB2 c seg_spec.SEG_C_SIZE i HcIn); [rewrite HRC; lia|].
  unfold seg_spec.SEG_C_SIZE, seg_spec.SEG_M_SIZE in *. lia. }
assert (HSTR2 : sa_str (rdW W2 mem2) t (s5_txt (x_pl cx) f)).
{ apply (s5d_str_blk ly S2 W2 mem2 md2 t _ (rdW W (ms_mem ms)) HAR2);
    [rewrite <- Etn; exact HtIn2 | exact (proj1 HSTR1) |].
  intros i Hi. apply (KB2 t (x_tn cx f) i HtIn); [rewrite HRT; lia|].
  unfold seg_spec.SEG_M_SIZE in *. lia. }
assert (HSL2 : lt_slots cx (rdW W2 mem2) (S5_slots cx c m f)).
{ intros o v Hin. pose proof (Hobnd o v Hin) as Ho.
  apply (s5d_word_kept (rdW W (ms_mem ms))); [|exact (HSL1 o v Hin)]. intros x Hx. apply KS2. lia. }
(* ---------------- run 2: 0x852d4 .. 0x852e0, the jal of reac_segconf_parse_file ---------------- *)
assert (R9b : getr regs2 9 = w64 (x_s1 cx)).
{ rewrite (s5d_pres_reg _ _ 9%bv 9 HPr ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (KR 9%bv ltac:(cbn; tauto)). exact R9. }
assert (S168b : rdword (rdW W2 mem2) (x_s1 cx + 168) = Some c)
  by (apply HSL2; unfold S5_slots, LT_L; apply in_or_app; left; cbn [In]; tauto).
pose proof (s5d_seed2 W2 regs2 mem2 (x_s1 cx) c R9b ltac:(lia) ltac:(lia) Hs1al Hc4 ltac:(lia) Hc16 S168b)
  as HS2.
pose proof (st_ok_pi_restrict_xfx fx fx1 SEGS VAL (s5d_E regs2 [Z_to_bv 64 c]) s5d_ss2 (w_H W2) regs2
  (Z_to_bv 64 (BASE + s5d_ra1)) mem2 (seg_rom SEGS) HS2) as HS2'.
clear HS2.
assert (SHOK2 : sh_ok SEGS s5d_X [] (s5d_E regs2 [Z_to_bv 64 c]) (mrestrict (w_H W2) mem2))
  by apply Forall_nil.
assert (HEI2 : img_env VAL A_LIM (s5d_E regs2 [Z_to_bv 64 c])) by (unfold s5d_E; apply Eimg_env).
assert (EEo2 : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr ->
  ew (s5d_E regs2 [Z_to_bv 64 c]) n = getr regs2 rr)
  by (intros n rr Hn; exact (s5d_E_reg regs2 _ n rr Hn)).
assert (E32b : ew (s5d_E regs2 [Z_to_bv 64 c]) 32 = Z_to_bv 64 c)
  by (unfold s5d_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
remember (s5d_E regs2 [Z_to_bv 64 c]) as E2 eqn:HE2. clear HE2.
rename ms into ms1.
pose proof (paj_run (fx := fx1) B LAWS) as RUN1.
paj_run_tok RUN1 HS2' HJ2 SHOK2 s5d_span.
{ lazymatch goal with |- awr_ok _ _ _ ?rs _ _ _ _ _ _ _ _ =>
    let rs' := eval vm_compute in rs in change rs with rs' end.
  repeat first [ apply awr_ok_nil | apply awr_ok_cons_ro; [cbn; lia|] ]. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md3 := d) in *; clearbody md3 end.
pmkst HS2'.
rewrite (SIGP SS_reac_segconf_parse_file
  ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_reac_segconf_parse_file) with AF_reac_segconf_parse_file by (vm_compute; reflexivity).
prreg HS2' (1%bv : bv 5) Q1. prreg HS2' (10%bv : bv 5) Q10. prreg HS2' (11%bv : bv 5) Q11.
prreg HS2' (12%bv : bv 5) Q12.
assert (KR2 : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 24; 25; 26]%bv ->
  getr (ms_regs ms) r = getr regs2 r).
{ intros r Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr];
    [ let P := fresh "P" in lazymatch goal with |- getr _ ?rr = _ => prreg HS2' rr P end;
      rewrite P; apply EEo2; reflexivity | ]).
  destruct Hr. }
lazymatch goal with Hfr : frame_of E2 _ (mrestrict _ _) (mrestrict _ _) |- _ =>
assert (KM2 : forall a, 0 <= a < 2 ^ 64 -> rdW W2 (ms_mem ms) a = rdW W2 mem2 a)
by (intros a Ha; apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun _ => False) Hfr);
   [ intros b wlo whi a' Hin Hrr; vm_compute in Hin;
     repeat (destruct Hin as [Hq0 | Hin]; [injection Hq0 as <- <- <-; cbn [base_val] in Hrr; lia|]);
     destruct Hin
   | exact Ha | tauto ]) end.
pose proof (s5d_core_run cx ly S2 W2 regs2 mem2 md2 k acc (5 + 2 * (x_nf cx - Z.of_nat f)) LFO_L
  [(t, x_tn cx f); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] (ms_regs ms) (ms_mem ms) md3 0 0
  HB HC2 HJ2 ltac:(intros a Ha _; exact (KM2 a Ha)) ltac:(lia) ltac:(lia)
  (KR2 2%bv ltac:(cbn; tauto)) (KR2 3%bv ltac:(cbn; tauto)) (KR2 4%bv ltac:(cbn; tauto))
  (KR2 8%bv ltac:(cbn; tauto)) (KR2 9%bv ltac:(cbn; tauto))) as HC3.
pose proof (proj1 (proj1 HC3)) as HJ3. pose proof (proj1 HJ3) as HAR3.
assert (Hrc3 : sa_rconf (rdW W2 (ms_mem ms)) c (seg_spec.seg_rc (x_st cx f))).
{ apply (s5d_rconf_kept (rdW W2 mem2)); [|exact Hrc2]. intros i Hi. apply KM2.
  unfold seg_spec.SEG_C_SIZE in *. lia. }
assert (Hmc3 : sa_mconf (rdW W2 (ms_mem ms)) m
  (SegModel.m_file (seg_spec.seg_mc (x_st cx f)) (s5_txt (x_pl cx) f) (s5_lab (x_pl cx) f))).
{ apply (s5d_mconf_kept (rdW W2 mem2)); [|exact Hmconf]. intros i Hi. apply KM2.
  unfold seg_spec.SEG_M_SIZE in *. lia. }
assert (HSTR3 : sa_str (rdW W2 (ms_mem ms)) t (s5_txt (x_pl cx) f))
  by (apply (s5d_eqv_str (rdW W2 mem2)); [exact KM2 | lia | lia | exact HSTR2]).
assert (HLAB3 : S5_label B ly S2 (rdW W2 (ms_mem ms)) cx f lp c m)
  by (apply (s5d_eqv_label cx ly S2 (rdW W2 mem2)); [exact KM2 | exact HLAB2]).
assert (HSL3 : lt_slots cx (rdW W2 (ms_mem ms)) (S5_slots cx c m f)).
{ intros o v Hin. pose proof (Hobnd o v Hin) as Ho.
  apply (s5d_word_kept (rdW W2 mem2)); [|exact (HSL2 o v Hin)]. intros x Hx. apply KM2. lia. }
(* the call of reac_segconf_parse_file *)
pose proof (proj1 (proj2 HC3)) as HIMG3.
pose proof HIMG3 as (HRO3 & HHI3 & _).
pose proof HHI3 as (_ & _ & _ & Hrcl3 & Hcat3 & _ & _ & _ & Hssp3 & _).
apply (s5d_pf_call fx1 cx ly S2 W2 (ms_regs ms) (ms_mem ms) md3 k acc
  (5 + 2 * (x_nf cx - Z.of_nat f)) LFO_L [(t, x_tn cx f); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)]
  c t lp (seg_spec.seg_rc (x_st cx f)) (s5_txt (x_pl cx) f) (s5_lab (x_pl cx) f) HB HC3).
{ rewrite Q1. reflexivity. }
{ rewrite Q10, E32b. reflexivity. }
{ rewrite Q11, (EEo2 23%nat 23%bv eq_refl).
  rewrite (s5d_pres_reg _ _ 23%bv 23 HPr ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (KR 23%bv ltac:(cbn; tauto)). exact R23. }
{ rewrite Q12, (EEo2 19%nat 19%bv eq_refl).
  rewrite (s5d_pres_reg _ _ 19%bv 19 HPr ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (KR 19%bv ltac:(cbn; tauto)). exact R19. }
{ lia. }
{ lia. }
{ pose proof HLAB as (Hlp & _ & _). lia. }
{ exact HcIn2. }
{ exact Hcn0. }
{ (* reac_segconf_parse_file_pre *)
  split.
  { split; [lia|]. split; [exact Hc16|]. split; [exact Hrc3|].
    split; [exists c, seg_spec.SEG_C_SIZE; split; [exact HcIn2 | split; lia]|].
    split; [exact (proj2 (proj2 (proj2 (s5d_hblk ly S2 W2 (ms_mem ms) md3 c _ HAR3 HcIn2))))|].
    split; [change (2 ^ 32) with 4294967296; lia|].
    split; [change (2 ^ 17) with 131072; change (2 ^ 32) with 4294967296; lia|].
    split; [change (2 ^ 17) with 131072; change (2 ^ 32) with 4294967296; lia|].
    split; [lia|]. split; [exact HSTR3|]. split; [exact (s5d_le_nat _ Hlen)|].
    split; [exists t, (x_tn cx f); split; [exact HtIn2 | split; lia]|].
    split; [rewrite <- Etn;
            exact (proj2 (proj2 (proj2 (s5d_hblk ly S2 W2 (ms_mem ms) md3 t _ HAR3 HtIn2))))|].
    split.
    { unfold sa_disj. destruct Dtc as [Dtc | Dtc]; [left | right; unfold seg_spec.SEG_C_SIZE in *; lia].
      apply (s5d_span_le t (s5_txt (x_pl cx) f) c); [lia|].
      pose proof (Z.div_mod c 16 ltac:(lia)). lia. }
    split; [exact (fxrel_frm0 fx fx1 Hfrm Hfxr)|].
    split; [exact Hssp3|]. split; [exact Hcat3|].
    intros x Hx. destruct (Hrcl3 x ltac:(unfold LTOI_RC_LITS; apply in_or_app; left; exact Hx)) as [Hl _].
    exact Hl. }
  pose proof HLAB3 as (Hlp3 & HO3 & HM3).
  split; [exact HO3|].
  revert HM3. destruct (s5_lab (x_pl cx) f) as [l|]; [|trivial].
  intros (Hlen3 & Hwh3 & Haddr3 & Hdm3 & Hdc3).
  split; [exact (s5d_le_nat _ Hlen3)|]. split; [exact Hwh3|]. split; [exact Haddr3|].
  unfold sa_disj in Hdc3 |- *. unfold seg_spec.RC_READING, seg_spec.SEG_C_SIZE in *. lia. }
(* ---------------- the state reac_segconf_parse_file left: the kit's cut S5_CK ---------------- *)
intros fx2 ly3 S3 W3 regs3 mem3 md4 Hfxr2 HJ4 HJc2 HPr2 Hans Hrconf HNA2.
pose proof HNA2 as (HPm2 & Ely2 & HSfs2). subst ly3.
destruct HSfs2 as (fsf2 & ESfs2).
pose proof (proj1 HJc2) as HAR4.
destruct (s5d_jkeep cx ly S2 W2 (ms_mem ms) md3 STK_reac_segconf_parse_file (seg_spec.RC_PARSE_W c)
  EV_reac_segconf_parse_file ly S3 W3 mem3 md4 c seg_spec.SEG_C_SIZE HB HAR3
  ltac:(rewrite Hfr2; exact HinF) HJc2 HcIn2 ltac:(unfold seg_spec.SEG_C_SIZE; lia) HRC
  ltac:(intros a Ha; exact (s5d_pfp_in c a Ha)) HPm2 EFr) as (KS4 & KI4 & KF4 & KB4).
assert (MLE4 : mo_le MT (x_S cx) S3 acc).
{ rewrite ESfs2. apply (mo_le_set_fs_r MT MTFL).
  pose proof HC3 as (_ & _ & _ & HBUD3). exact (proj1 (proj2 (proj2 (proj2 HBUD3)))). }
pose proof (s5d_carry cx ly S2 W2 (ms_regs ms) (ms_mem ms) md3 k acc (5 + 2 * (x_nf cx - Z.of_nat f)) LFO_L
  [(t, x_tn cx f); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] ly S3 W3 regs3 mem3 md4
  HB HC3 HJ4 HPr2 HPm2 MLE4 KS4 KI4 KF4) as HC4.
assert (HmIn3 : In (m, seg_spec.SEG_M_SIZE) (ablocks B ly S3))
  by exact (Permutation_in _ (Permutation_sym HPm2) HmIn2).
assert (HcIn3 : In (c, seg_spec.SEG_C_SIZE) (ablocks B ly S3))
  by exact (Permutation_in _ (Permutation_sym HPm2) HcIn2).
assert (HtIn3 : In (t, x_tn cx f) (ablocks B ly S3))
  by exact (Permutation_in _ (Permutation_sym HPm2) HtIn2).
assert (Hmc4 : sa_mconf (rdW W3 mem3) m
  (SegModel.m_file (seg_spec.seg_mc (x_st cx f)) (s5_txt (x_pl cx) f) (s5_lab (x_pl cx) f))).
{ apply (s5d_mconf_kept (rdW W2 (ms_mem ms))); [|exact Hmc3]. intros i Hi.
  apply (KB4 m seg_spec.SEG_M_SIZE i HmIn2); [rewrite HRM; lia|].
  unfold seg_spec.SEG_C_SIZE, seg_spec.SEG_M_SIZE in *. lia. }
assert (HSL4 : lt_slots cx (rdW W3 mem3) (S5_slots cx c m f)).
{ intros o v Hin. pose proof (Hobnd o v Hin) as Ho.
  apply (s5d_word_kept (rdW W2 (ms_mem ms))); [|exact (HSL3 o v Hin)]. intros x Hx. apply KS4. lia. }
refine (HKA fx2 cx ly S3 W3 regs3 mem3 md4 k acc c m t lp HB
  (fxrel_frm0 fx1 fx2 (fxrel_frm0 fx fx1 Hfrm Hfxr) Hfxr2) Hf _ _ _ _ _ _ _ _ _ _ _ _ _ _).
- split; [exact HC4|].
  split; [exact (s5d_hblk ly S3 W3 mem3 md4 c _ HAR4 HcIn3)|].
  split; [exact (s5d_hblk ly S3 W3 mem3 md4 m _ HAR4 HmIn3)|].
  split; [exact (s5d_hblk ly S3 W3 mem3 md4 t _ HAR4 HtIn3) | exact HCNT].
- exact Hrconf.
- exact Hmc4.
- exact (s5d_cnt_S f (seg_spec.seg_rc (x_st cx f)) (seg_spec.seg_mc (x_st cx f))
           (s5_txt (x_pl cx) f) (s5_lab (x_pl cx) f) HCNT Hnul Hlen).
- exact Hans.
- rewrite (s5d_pres_reg _ _ 18%bv 18 HPr2 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (KR2 18%bv ltac:(cbn; tauto)).
  rewrite (s5d_pres_reg _ _ 18%bv 18 HPr ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (KR 18%bv ltac:(cbn; tauto)). exact R18.
- rewrite (s5d_pres_reg _ _ 19%bv 19 HPr2 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (KR2 19%bv ltac:(cbn; tauto)).
  rewrite (s5d_pres_reg _ _ 19%bv 19 HPr ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (KR 19%bv ltac:(cbn; tauto)). exact R19.
- rewrite (s5d_pres_reg _ _ 21%bv 21 HPr2 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (KR2 21%bv ltac:(cbn; tauto)).
  rewrite (s5d_pres_reg _ _ 21%bv 21 HPr ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (KR 21%bv ltac:(cbn; tauto)). exact R21.
- rewrite (s5d_pres_reg _ _ 22%bv 22 HPr2 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (KR2 22%bv ltac:(cbn; tauto)).
  rewrite (s5d_pres_reg _ _ 22%bv 22 HPr ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (KR 22%bv ltac:(cbn; tauto)). exact R22.
- rewrite (s5d_pres_reg _ _ 23%bv 23 HPr2 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (KR2 23%bv ltac:(cbn; tauto)).
  rewrite (s5d_pres_reg _ _ 23%bv 23 HPr ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (KR 23%bv ltac:(cbn; tauto)). exact R23.
- rewrite (s5d_pres_reg _ _ 24%bv 24 HPr2 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (KR2 24%bv ltac:(cbn; tauto)).
  rewrite (s5d_pres_reg _ _ 24%bv 24 HPr ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (KR 24%bv ltac:(cbn; tauto)). exact R24.
- rewrite (s5d_pres_reg _ _ 25%bv 25 HPr2 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (KR2 25%bv ltac:(cbn; tauto)).
  rewrite (s5d_pres_reg _ _ 25%bv 25 HPr ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (KR 25%bv ltac:(cbn; tauto)). exact R25.
- rewrite (s5d_pres_reg _ _ 26%bv 26 HPr2 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (KR2 26%bv ltac:(cbn; tauto)).
  rewrite (s5d_pres_reg _ _ 26%bv 26 HPr ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (KR 26%bv ltac:(cbn; tauto)). exact R26.
- exact HSL4.
Qed.

End ed.
End fd.
End dd.

(* ============================================== piece L5 (e) ============================================== *)
(* reac-pw/fuzz_segconf, ASan+UBSan image B (fuzz_segconf.asan-ubsan, pin sha256 c3796c0b38f3): piece L5 of the walk
   of segment S05 of the test harness's entry function LLVMFuzzerTestOneInput (0x84dc0): s5_tail, from the inner cut
   0x852e4 (S5_CK, the kit LLVMFuzzerTestOneInput_s15k.v) to the cut K85530 f (LLVMFuzzerTestOneInput_defs.v).
   The code (dis/LLVMFuzzerTestOneInput.fuzz_segconf.asan-ubsan.s lines 331-345 and 474-477):
     0x852e4 ld a1,200(s1) (the shadow base); 0x852e8 bnez s5 (the trap; s5 = M & 3 = 0); 0x852ec .. 0x852f8 the
     instrumented check of m->n at m + 0x2000 (its shadow entry covers the 8 bytes, so the slow block 0x85570 is not
     entered) and a3 := 160(s1) = N1; 0x852fc .. 0x85318 176(s1) := returned && (answer = m->n); 0x8531c s6 :=
     192(s1) = m; 0x85320 j 0x85520; 0x85520 .. 0x85528 s4 := N1 - NP, a0 := t; 0x8552c free(t) (AFREE4).
   One token run 0x852e4 .. 0x8552c, the free through PaCall.afree04_sub, then K85530 f. *)
(* ======================================== generic helpers (s5e_) ======================================== *)
Lemma s5e_nth_firstn : forall (A : Type) (l : list A) n j d, (j < n)%nat -> nth j (firstn n l) d = nth j l d.
Proof.
intros A l. induction l as [|x l IH]; intros n j d Hj.
- destruct n as [|n]; [lia|]. destruct j; reflexivity.
- destruct n as [|n]; [lia|]. destruct j as [|j]; [reflexivity|]. cbn [firstn nth]. apply IH. lia.
Qed.
Lemma s5e_nth_skipn : forall (A : Type) (l : list A) off j d, nth j (skipn off l) d = nth (off + j) l d.
Proof.
intros A l off. revert l. induction off as [|off IH]; intros l j d; [reflexivity|].
destruct l as [|x l].
- cbn [skipn]. destruct j; reflexivity.
- cbn [skipn]. rewrite IH. reflexivity.
Qed.
(* the k-th byte of a u32 field holding v *)
Lemma s5e_u32_nth : forall v f k, seg_spec.u32_enc v f -> (k < 4)%nat ->
  bv_unsigned (nth k f ZB0) = (Z.shiftr (v mod 2 ^ (8 * Z.of_nat 4)) (8 * Z.of_nat k)) mod 256.
Proof.
intros v f k [Hv ->] Hk.
unfold OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Mem.le4.
rewrite (unsigned_lit_small v) by lia.
change (8 * Z.of_nat 4) with 32. rewrite (Z.mod_small v (2 ^ 32)) by lia.
destruct k as [|[|[|[|k]]]]; [| | | | lia]; cbn [Z_to_le_bytes nth]; rewrite Z_to_bv_unsigned;
  change (bv_wrap 8 ?x) with (x mod 2 ^ 8); rewrite ?Z.shiftr_shiftr by lia; reflexivity.
Qed.
(* a list without two overlapping members has no duplicate *)
Lemma s5e_pzd_nodup : forall l, (forall x, In x l -> 0 < snd x) -> pairwise zdisjoint l -> List.NoDup l.
Proof.
induction l as [|x l IH]; intros Hp Hd; [constructor|]. destruct Hd as [Hx Hl]. constructor.
- intros Hin. rewrite Forall_forall in Hx. specialize (Hx x Hin). pose proof (Hp x (or_introl eq_refl)).
  unfold zdisjoint in Hx. lia.
- apply IH; [intros y Hy; exact (Hp y (or_intror Hy)) | exact Hl].
Qed.
(* free removes its block from the list at any place: what is left, against the cut's list *)
Lemma s5e_perm_free : forall (bl bl2 O R : list (Z * Z)) x,
  Permutation bl ((x :: O) ++ R) ->
  (exists l1 l2, bl = l1 ++ x :: l2 /\ bl2 = l1 ++ l2) ->
  Permutation bl2 (O ++ R).
Proof.
intros bl bl2 O R x HP (l1 & l2 & E1 & E2). subst bl bl2.
apply (Permutation_cons_inv (a := x)).
eapply Permutation_trans; [apply Permutation_middle | exact HP].
Qed.
(* a word every byte of which two readers agree on *)
Lemma s5e_word_kept : forall (rd rd' : reader) a v,
  (forall x, a <= x < a + 8 -> rd' x = rd x) -> rdword rd a = Some v -> rdword rd' a = Some v.
Proof. intros rd rd' a v HK H. rewrite (rdword_ext rd rd' a); [exact H|]. intros k Hk. apply HK. lia. Qed.
(* a word all 8 bytes of which a reader shows *)
Lemma s5e_rdword_some : forall (rd : reader) a, (forall k, 0 <= k < 8 -> rd (a + k) <> None) ->
  exists v, rdword rd a = Some v.
Proof.
intros rd a H. unfold rdword.
pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
pose proof (H 1 ltac:(lia)) as H1. pose proof (H 2 ltac:(lia)) as H2. pose proof (H 3 ltac:(lia)) as H3.
pose proof (H 4 ltac:(lia)) as H4. pose proof (H 5 ltac:(lia)) as H5. pose proof (H 6 ltac:(lia)) as H6.
pose proof (H 7 ltac:(lia)) as H7.
destruct (rd a) as [b0|]; [|congruence]. destruct (rd (a + 1)) as [b1|]; [|congruence].
destruct (rd (a + 2)) as [b2|]; [|congruence]. destruct (rd (a + 3)) as [b3|]; [|congruence].
destruct (rd (a + 4)) as [b4|]; [|congruence]. destruct (rd (a + 5)) as [b5|]; [|congruence].
destruct (rd (a + 6)) as [b6|]; [|congruence]. destruct (rd (a + 7)) as [b7|]; [|congruence].
eexists; reflexivity.
Qed.
(* a callee-saved register a call keeps *)
Lemma s5e_pres_reg : forall regs regs' (r : bv 5) z,
  aregs_preserved regs regs' -> acallee_saved z -> Z_to_bv 5 z = r -> getr regs' r = getr regs r.
Proof. intros regs regs' r z HP Hz <-. exact (HP z Hz). Qed.
(* the reader's answer is its segment count *)
Lemma s5e_rp_snd : forall c t l,
  snd (SegModel.r_parse_file c t l) = Z.of_nat (length (SegModel.rc_seg (fst (SegModel.r_parse_file c t l)))).
Proof.
intros c t l. unfold SegModel.r_parse_file.
destruct (SegModel.r_lines _ _ _) as [[c2 x] y]. reflexivity.
Qed.
(* the state after a turn that is not the last *)
Lemma s5e_after : forall pl f, Z.of_nat f + 1 < seg_spec.seg_nfiles pl ->
  seg_spec.seg_after pl f =
  (fst (s5_rp pl f), s5_mc1 pl f,
   seg_spec.seg_ret (seg_spec.seg_run pl f) &&
   (snd (s5_rp pl f) =? Z.of_nat (length (SegModel.mc_seg (s5_mc1 pl f))))).
Proof.
intros pl f Hf. unfold seg_spec.seg_after.
replace (Z.of_nat (Datatypes.S f) =? seg_spec.seg_nfiles pl) with false by (symmetry; apply Z.eqb_neq; lia).
unfold s5_rp, s5_mc1, s5_txt, s5_lab, seg_spec.seg_mc, seg_spec.seg_ret, seg_spec.seg_rc.
destruct (seg_spec.seg_run pl f) as [[c0 mc0] r0]. cbn [seg_spec.seg_turn_step fst snd].
destruct (SegModel.r_parse_file c0 (seg_spec.seg_txt pl f) (seg_spec.seg_label pl f)) as [c1 n1]. reflexivity.
Qed.
(* the bytes of a struct the readers agree on *)
Lemma s5e_rconf_kept : forall (rd rd' : reader) c rc,
  (forall i, 0 <= i < seg_spec.SEG_C_SIZE -> rd' (c + i) = rd (c + i)) -> sa_rconf rd c rc -> sa_rconf rd' c rc.
Proof.
intros rd rd' c rc HK (bs & Hb & He). exists bs. split; [|exact He].
pose proof He as (Hl & _). intros i Hi. rewrite HK by lia. exact (Hb i Hi).
Qed.
Lemma s5e_mconf_kept : forall (rd rd' : reader) m mc,
  (forall i, 0 <= i < seg_spec.SEG_M_SIZE -> rd' (m + i) = rd (m + i)) -> sa_mconf rd m mc -> sa_mconf rd' m mc.
Proof.
intros rd rd' m mc HK (bs & Hb & He). exists bs. split; [|exact He].
pose proof He as (Hl & _). intros i Hi. rewrite HK by lia. exact (Hb i Hi).
Qed.
(* m->n as 4 bytes at m + 0x2000 *)
Lemma s5e_mconf_n : forall (rd : reader) m mc, sa_mconf rd m mc ->
  (length (SegModel.mc_seg mc) <= 32)%nat /\
  rd32 rd (m + seg_spec.MC_N) (Z.of_nat (length (SegModel.mc_seg mc))).
Proof.
intros rd m mc (bs & Hb & Hl & H32 & _ & Hn & _). split; [exact H32|].
intros k Hk.
pose proof (s5e_u32_nth _ _ k Hn Hk) as Hv.
assert (Hnth : nth k (seg_spec.fldz seg_spec.MC_N 4 bs) ZB0 = nth (8192 + k) bs ZB0).
{ unfold seg_spec.fldz, seg_spec.fld. rewrite s5e_nth_firstn by (cbn; lia). rewrite s5e_nth_skipn. reflexivity. }
rewrite Hnth in Hv.
assert (E8192 : Z.of_nat 8192 = 8192) by reflexivity.
assert (Hl' : (8192 + k < length bs)%nat).
{ apply Nat2Z.inj_lt. rewrite Nat2Z.inj_add, E8192, Hl. unfold seg_spec.SEG_M_SIZE. lia. }
pose proof (Hb (8192 + k)%nat Hl') as Hbk.
rewrite Hv in Hbk.
replace (m + Z.of_nat (8192 + k)) with (m + seg_spec.MC_N + Z.of_nat k) in Hbk
  by (rewrite Nat2Z.inj_add, E8192; unfold seg_spec.MC_N; lia).
exact Hbk.
Qed.
Lemma s5e_rconf_n : forall (rd : reader) c rc, sa_rconf rd c rc -> (length (SegModel.rc_seg rc) <= 32)%nat.
Proof. intros rd c rc (bs & _ & _ & H32 & _). exact H32. Qed.
(* the values the run leaves (the expressions are the token runner's, read off its end state) *)
(* s10 = (m + 0x2000) >> 3 *)
Lemma s5e_srl_val : forall E m, ew E 22 = Z_to_bv 64 m -> 0 <= m -> m + 8192 < 2 ^ 64 ->
  sv_denot E (SAlu ALU_SRL (SOff 22 8192) (SLit 3)) = w64 ((m + seg_spec.MC_N) / 8).
Proof.
intros E m E22 Hm0 Hm1.
apply bv_eq. unfold w64. rewrite unsigned_lit_small by (unfold seg_spec.MC_N; split; [apply Z.div_pos | apply (Z.le_lt_trans _ (m + 8192)); [apply Z.div_le_upper_bound |]]; lia).
change (bv_unsigned (sv_denot E (SAlu ALU_SRL (SOff 22 8192) (SLit 3)))) with (U E (SAlu ALU_SRL (SOff 22 8192) (SLit 3))).
rewrite U_SAlu, U_SLit, U_SOff, E22, unsigned_lit_small by lia.
rewrite (zcanon_id 3) by (unfold M64; lia). rewrite (zcanon_id (m + 8192)) by (unfold M64; lia).
cbn [zalu_raw]. change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
rewrite zcanon_id; [unfold seg_spec.MC_N; reflexivity|].
unfold M64. split; [apply Z.div_pos | apply (Z.le_lt_trans _ (m + 8192)); [apply Z.div_le_upper_bound |]]; lia.
Qed.
(* s4 = N1 - NP (the runner writes it -NP + N1) *)
Lemma s5e_sub_val : forall E a b, ew E 32 = Z_to_bv 64 a -> ew E 33 = Z_to_bv 64 b -> 0 <= a <= b -> b < 2 ^ 64 ->
  U E (SAlu ALU_ADD (SMd M_MUL (SOff 32 0) (SLit (-1))) (SOff 33 0)) = b - a.
Proof.
intros E a b E32 E33 Hab Hb.
rewrite U_SAlu, U_SMd, !U_SOff, U_SLit, E32, E33, !unsigned_lit_small by lia.
cbn [zalu_raw zmd_raw]. rewrite !Z.add_0_r.
unfold zcanon, M64. rewrite Zmult_mod_idemp_r, Zmult_mod_idemp_l, Zplus_mod_idemp_l, (Z.mod_small b) by lia.
replace (a * -1 + b) with (b - a) by ring. apply Z.mod_small. lia.
Qed.
(* 176(s1) := returned && (answer = m->n): xor, snez, addiw -1, and *)
Lemma s5e_latch : forall E (a n : Z) (ret : bool),
  ew E 10 = Z_to_bv 64 a -> ew E 35 = Z_to_bv 64 n -> ew E 34 = Z_to_bv 64 (seg_spec.b2z ret) ->
  0 <= a <= 32 -> 0 <= n <= 32 ->
  U E (SAlu ALU_AND (SAlu ALU_ADD (SAlu ALU_SLTU (SLit 0) (SAlu ALU_XOR (SOff 10 0) (SOff 35 0))) (SLit (-1)))
    (SOff 34 0)) = seg_spec.b2z (ret && (a =? n)).
Proof.
intros E a n ret E10 E35 E34 Ha Hn.
assert (Hr : 0 <= seg_spec.b2z ret <= 1) by (unfold seg_spec.b2z; destruct ret; lia).
rewrite !U_SAlu, !U_SLit.
rewrite (U_atom E 10 a E10) by lia. rewrite (U_atom E 35 n E35) by lia. rewrite (U_atom E 34 _ E34) by lia.
cbn [zalu_raw].
destruct (Z.eqb_spec a n) as [<- | Hne].
- rewrite Z.lxor_nilpotent, Bool.andb_true_r.
  destruct ret; reflexivity.
- rewrite Bool.andb_false_r.
  assert (Hx0 : 0 <= Z.lxor a n) by (apply Z.lxor_nonneg; split; intros; lia).
  assert (Hxn : Z.lxor a n <> 0) by (intros H; apply Hne; apply Z.lxor_eq; exact H).
  assert (Hx64 : Z.lxor a n < 2 ^ 6).
  { apply (proj2 (Z.log2_lt_pow2 (Z.lxor a n) 6 ltac:(lia))).
    pose proof (Z.log2_lxor a n ltac:(lia) ltac:(lia)) as HL.
    pose proof (Z.log2_le_mono a 32 ltac:(lia)) as La. pose proof (Z.log2_le_mono n 32 ltac:(lia)) as Ln.
    change (Z.log2 32) with 5 in La, Ln. lia. }
  rewrite (zcanon_id (Z.lxor a n)) by (unfold M64; lia).
  replace (zcanon 0) with 0 by reflexivity.
  replace (0 <? Z.lxor a n) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (zcanon (-1)) with (2 ^ 64 - 1) by reflexivity.
  replace (zcanon (1 + (2 ^ 64 - 1))) with 0 by reflexivity.
  rewrite Z.land_0_l. reflexivity.
Qed.

(* the symbolic seed at 0x852e4: every register its own atom but s5 (the literal 0, K85210's M & 3) and s10 (the
   expression (m + 0x2000) >> 3 over the atom of s6 = m, so that YCbn.match_x sees the instrumented check's address
   ((m + 0x2000) >> 3) + SHADOW_OFF); the frame slots 152 (NP, atom 32), 160 (N1, atom 33), 176 (returned, atom 34,
   the only write window), 192 (m), 200 (the shadow base), 216 (m + 0x2000) above s1, and m->n (atom 35) at
   m + 0x2000; the shadow entry of m + 0x2000 .. m + 0x2008 (check 8 vanishes) *)
Definition s5e_X : sv := SLit SHADOW_OFF.
Definition s5e_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition s5e_SH : list shent := [mkSHE 22 8192 8200].
Definition s5e_rg : smem := [
  YP09.mkRegion (Some 9%nat) 152 224 176 184
    [YP09.mkChunk 152 (CVal 8 (SOff 32 0)); YP09.mkChunk 160 (CVal 8 (SOff 33 0));
     YP09.mkChunk 176 (CVal 8 (SOff 34 0)); YP09.mkChunk 192 (CVal 8 (SOff 22 0));
     YP09.mkChunk 200 (CVal 8 (SLit SHADOW_OFF)); YP09.mkChunk 216 (CVal 8 (SOff 22 8192))];
  YP09.mkRegion (Some 22%nat) 8192 8196 8192 8192 [YP09.mkChunk 8192 (CVal 4 (SOff 35 0))] ].
Definition s5e_fa : facts :=
  mkFacts [ (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (22%nat, mkAF 4096 140737479966720 4); (10%nat, mkAF 0 32 0);
    (34%nat, mkAF 0 1 0); (35%nat, mkAF 0 32 0) ] [] [].
Definition s5e_regs : list sv :=
  sr_set (sr_set sr_atoms 21%bv (SLit 0)) 26%bv (SAlu ALU_SRL (SOff 22 8192) (SLit 3)).
Definition s5e_ss : sstate := mkSS LO_S5CK s5e_regs s5e_rg None s5e_fa.

Section de. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section fe.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section ee.
Variable B : asyms.
Variable MT : ameter_ops.
(* the image range the snprintf row's dest_off_globals uses, and the read-only ranges it reads; the S11 walk
   (the probe snprintf) takes the same three names and the same five HSNP_ hypotheses *)
Variable snp_lo snp_hi : Z.
Variable snp_cr : list (Z * Z).
(* AR's laws are a theorem of image B's kit, not a hypothesis *)
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis PRW : prog_rw SEGS B.
Hypothesis VOBJS : seg_val_objs.
Hypothesis SIGP : seg_sig_prog.
(* image B's per-image record (lib/B/Prog/SegRecBase.v, the image-B listing owner's commit c4abdaee306f, merged into
   this walk's integration commit da997fa1859d): the image facts lt_img needs at a reader after a call, each a field.
   It SUPERSEDES the three hypotheses IMG_RELRO / IMG_GOTW / IMG_GUARD an earlier version of this brief had.
   Never weaken lt_img instead. *)
Hypothesis IMGF : seg_img_facts SEGS B.
(* the allocator record's symbols at image B's values (lib/B/YF0m.v): with AR it gives the stack-protector
   cells at every state (SegRecCells.seg_rec_cells), since the runtime owns the .got word gotwA *)
Hypothesis HBS : YF0m.SegBSyms B.
(* longl's bytes are the program's own writable static, in the image and outside RELRO (the memset arm writes
   them), and no model-table pointer reaches within 65536 of longl (image A's S05 header takes the same
   three; they are what the longl arm and the literals' survival need) *)
Hypothesis HPGS : forall a, inFP (ltoi_PG longlA) a ->
  Exists (in_zr a) (as_prog_static B) /\ in_img SEGS a.
Hypothesis HPG_RO : forall a, inFP (ltoi_PG longlA) a -> ~ in_roP SEGS RLO_A RHI_A a.
Hypothesis HPG_PTR : forall a p,
  ((exists i, (i < 5)%nat /\ a = wordsA + 8 * Z.of_nat i) \/
   (exists i, (i < pin_spec.CAT_N)%nat /\ a = pin_spec.row_addr catA i)) ->
  rdword (fun x => option_map (fun b : byte => bv_unsigned b) (seg_rom SEGS (Z_to_bv 64 x))) a = Some p ->
  p + 65536 <= longlA.
(* the runtime entries S05 calls *)
Hypothesis AMEMCPY : forall fx0 : YK11.FPState, aintrin_realizes (fx := fx0) SEGS B OCpy (SIG SS___asan_memcpy).
Hypothesis AMEMSET : forall fx0 : YK11.FPState, aintrin_realizes (fx := fx0) SEGS B OSet (SIG SS___asan_memset).
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState,
  RtPFSeg.seg_asnprintf_realizes (fx := fx0) SEGS B snp_lo snp_hi snp_cr
    (SIG SS___interceptor_trampoline_snprintf) gotwA guardA.
Hypothesis AFREE4 : forall fx0 : YK11.FPState, afree04_rule (fx := fx0) SEGS B MT.
(* what image B's close shows of snp_lo / snp_hi / snp_cr; each is a computation there *)
Hypothesis HSNP_LIT : forall x, In x LLVMFuzzerTestOneInput_c.LTOI_LITS ->
  snp_lo <= seg_litA_fz x /\ seg_litA_fz x + Z.of_nat (length x) + 1 <= gotwA.
Hypothesis HSNP_CR : Forall (fun r => snp_lo <= fst r /\ 0 <= snd r /\ fst r + snd r <= snp_hi) snp_cr.
Hypothesis HSNP_LO : 0 <= snp_lo.
Hypothesis HSNP_CEIL : snp_hi <= alloc_ceiling.
Hypothesis HSNP_FAKE : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> snp_hi <= ly_F ly.
(* the two program callees, at every FP state *)
Hypothesis HM_FILE : forall fx0 : YK11.FPState,
  m_file_c.m_file_contract (fx := fx0) SEGS B (BASE + AF_m_file) STK_m_file RLO_A RHI_A seg_litA_fz
    wordsA rolesA catA gotwA guardA.
Hypothesis HPARSE_FILE : forall fx0 : YK11.FPState,
  reac_segconf_parse_file_c.reac_segconf_parse_file_contract (fx := fx0) SEGS B
    (BASE + AF_reac_segconf_parse_file) STK_reac_segconf_parse_file RLO_A RHI_A seg_litA_rc catA gotwA guardA.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* the three image facts lt_img needs at a reader after a call, each from a field of IMGF (image A's S00 walk
   takes the same three as its record s10_img); this text compiled on the VM, log build-20261030T183150Z.log.
   Rename `hdr_` to `s5e_` in your file. *)
Lemma s5e_relro : forall a, RLO_A <= a < RHI_A -> in_img SEGS a.
Proof. exact (cif_relro_img _ _ IMGF). Qed.

(* ------------------------ the walk's own facts at a cut (image B's S01 / S02 kit, s5e_ names) ------------------------ *)
(* the entry sp and the realigned base S1 (andi sp,sp,-32 at 0x84e00 after addi sp,sp,-352) *)
Lemma s5e_sp : forall cx, lt_base B MT cx ->
  x_sp0 cx mod 16 = 0 /\ alloc_ceiling + 32768 <= x_sp0 cx /\ x_sp0 cx <= 2 ^ 47 /\
  x_s1 cx mod 32 = 0 /\ x_sp0 cx - 368 <= x_s1 cx /\ x_s1 cx <= x_sp0 cx - 352.
Proof.
intros cx HB. destruct HB as (HPRE & _). destruct HPRE as (_ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal & _ & Hceil & Hslo & Hshi & H47 & _).
unfold x_s1, x_sp0, LT_FRAME, STK_LLVMFuzzerTestOneInput in *.
set (s := spZ (x_regs cx)) in *. clearbody s.
repeat split; lia.
Qed.
(* a live block of a state is a harness block of that state *)
Lemma s5e_hblk : forall ly S (W : world SEGS) mem md a n,
  AR SEGS B ly S W mem md -> In (a, n) (ablocks B ly S) -> lt_hblk B ly S (rdW W mem) a n.
Proof.
intros ly S W mem md a n HAR Hin.
destruct (al_blocks _ _ LAWS ly S W mem md a n HAR Hin) as (H16 & H4096 & Hceil & _ & _ & _ & Hn).
pose proof (req_size_pos n ltac:(lia)) as [_ Hreq].
pose proof asan_consts as (C1 & _).
split; [exact Hin|]. split; [exact H4096|]. split; [exact H16|].
split; [lia|]. split; [lia|].
split; [exact (amem_range_of_block SEGS B LAWS ly S W mem md a n a n HAR Hin ltac:(lia) ltac:(lia))|].
split; [exact (range_addressable_of_block SEGS B LAWS ly S W mem md a n a n HAR Hin ltac:(lia) ltac:(lia))|].
intros Hn0. exact (shadow_hull_vis_of_block SEGS B LAWS ly S W mem md a n a n HAR Hin ltac:(lia) ltac:(lia) Hn0).
Qed.
(* the frame address of a journal's target layout is the entry's *)
Lemma s5e_frame_addr : forall STK sp0 FP ly0 S0 W0 mem0 md0 own ly S (W : world SEGS) mem md k,
  ajournal SEGS B STK sp0 FP ly0 S0 W0 mem0 md0 own ly S W mem md k ->
  forall cid pos, frame_addr ly cid pos = frame_addr ly0 cid pos.
Proof.
intros STK sp0 FP ly0 S0 W0 mem0 md0 own ly S W mem md k HJ cid pos.
destruct HJ as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & EF & _). unfold frame_addr. rewrite EF. reflexivity.
Qed.
(* a ROM byte is shown by every reader *)
Lemma s5e_rom_view_some : forall (H : word -> bool) mem a, seg_rom SEGS (Z_to_bv 64 a) <> None -> aview SEGS H mem a <> None.
Proof.
intros H mem a Hr. unfold aview, mbyte. destruct (mrestrict H mem (Z_to_bv 64 a)) as [b|]; [cbn; discriminate|].
destruct (seg_rom SEGS (Z_to_bv 64 a)) as [b|] eqn:E; [cbn; discriminate | congruence].
Qed.
(* the stack-protector cells of seg_himg (the .got word gotwA holding guardA, and guardA's word shown) at a later
   reader, re-derived from AR at that state by SegRecCells.seg_rec_cells (owner's brief decision 12: the runtime
   owns the .got word gotwA, so image B's SegRo no longer lists it). ONE lemma on purpose; the agreement premise
   is kept so its callers do not change. *)
Lemma s5e_ssp_kept : forall ly' S' (W W' : world SEGS) mem mem' md',
  AR SEGS B ly' S' W' mem' md' ->
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     rdW W' mem' a = rdW W mem a) ->
  sa_ssp (rdW W mem) gotwA guardA -> sa_ssp (rdW W' mem') gotwA guardA.
Proof.
intros ly' S' W W' mem mem' md' HAR' _ _.
exact (proj1 (proj2 (SegRecCells.seg_rec_cells SEGS B LAWS HBS IMGF ly' S' W' mem' md' HAR'))).
Qed.
(* the image facts of a point carried to a later reader that agrees on every image byte the runtime does not own
   (image B's S01 / S02 walk's lk_img_kept; the stack-protector cells by s5e_ssp_kept) *)
Lemma s5e_lit_kept : forall (W W' : world SEGS) mem mem' a s,
  (forall x, a <= x < a + (Z.of_nat (length s) + 1) -> rdW W' mem' x = rdW W mem x) ->
  sa_lit SEGS B (rdW W mem) a s -> sa_lit SEGS B (rdW W' mem') a s.
Proof.
intros W W' mem mem' a s HK (Ha & ((Hzs & Hn0) & _) & Hpin & Hrt & Himg).
split; [exact Ha|]. split; [split; [split; [|exact Hn0] | exact (sa_tail_of_romtail SEGS (w_H W') mem' _ Hrt)]|].
- intros i Hi. rewrite HK; [exact (Hzs i Hi)|]. rewrite length_app in Hi. cbn [length] in Hi. lia.
- split; [exact Hpin|]. split; [exact Hrt | exact Himg].
Qed.
Lemma s5e_img_kept : forall cx ly' S' (W W' : world SEGS) mem mem' md',
  AR SEGS B ly' S' W' mem' md' ->
  lt_img B cx (rdW W mem) ->
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     rdW W' mem' a = rdW W mem a) ->
  lt_img B cx (rdW W' mem').
Proof.
intros cx ly' S' W W' mem mem' md' HAR' (HRO & HIMG & HGI) HK.
assert (KI : forall q n, sa_img SEGS B q n -> forall x, q <= x < q + n -> rdW W' mem' x = rdW W mem x).
{ intros q n Hq x Hx. destruct (Hq x Hx) as (H1 & H2 & H3). exact (HK x H1 H2 H3). }
assert (KL : forall a s, sa_lit SEGS B (rdW W mem) a s -> sa_lit SEGS B (rdW W' mem') a s).
{ intros a s Hl. apply (s5e_lit_kept W W' mem mem' a s); [|exact Hl].
  destruct Hl as (_ & _ & _ & _ & Himg). exact (KI _ _ Himg). }
destruct HIMG as (Hm40 & Hm40i & Hfz & Hrc & Hcat & Hcata & Hw & Hrl & Hssp & Hpin & Hrt & Hli & Hd1 & Hd2 & Hd3).
split; [|split].
- intros a Hro Ho He. rewrite (HK a); [exact (HRO a Hro Ho He) | | exact Ho | exact He].
  destruct Hro as [(s & Hs & _ & Hr) | Hrr]; [exists s; split; [exact Hs | exact Hr] | exact (s5e_relro a Hrr)].
- split; [intros k Hk; rewrite (KI _ 8 Hm40i) by lia; exact (Hm40 k Hk)|].
  split; [exact Hm40i|].
  split; [intros s Hs; destruct (Hfz s Hs) as [H1 H2]; exact (conj (KL _ _ H1) H2)|].
  split; [intros s Hs; destruct (Hrc s Hs) as [H1 H2]; exact (conj (KL _ _ H1) H2)|].
  split.
  { destruct Hcat as (Hcp & Hci & Hrows). split; [exact Hcp|]. split; [exact Hci|].
    intros i Hi. destruct (Hrows i Hi) as (tp & Htp & Hl). exists tp. split; [|exact (KL _ _ Hl)].
    apply (s5e_word_kept (rdW W mem)); [|exact Htp]. intros x Hx. apply (KI _ _ Hci).
    unfold pin_spec.row_addr, pin_spec.CAT_ROW, pin_spec.CAT_BYTES, pin_spec.CAT_N in *. lia. }
  split; [exact Hcata|].
  split.
  { destruct Hw as (Hwp & Hwi & Hws). split; [exact Hwp|]. split; [exact Hwi|].
    intros i Hi. destruct (Hws i Hi) as (wp & Hwp' & Hl). exists wp. split; [|exact (KL _ _ Hl)].
    apply (s5e_word_kept (rdW W mem)); [|exact Hwp']. intros x Hx. apply (KI _ _ Hwi). lia. }
  split.
  { destruct Hrl as (Hrp & Hri & Hrs). split; [exact Hrp|]. split; [exact Hri|].
    intros i Hi k Hk. rewrite (KI _ _ Hri) by lia. exact (Hrs i Hi k Hk). }
  split; [exact (s5e_ssp_kept ly' S' W W' mem mem' md' HAR' HK Hssp)|].
  split; [exact Hpin|]. split; [exact Hrt|]. split; [exact Hli|].
  split; [exact Hd1|]. split; [exact Hd2 | exact Hd3].
- intros i Hi. rewrite (KI _ _ Hli) by (unfold LONGL_W, LONGL_N; lia). exact (HGI i Hi).
Qed.
(* a chain for the call's chain_pre: the stack from S1 to the layout's top is mapped, s0 = SP0 >= S1 + 352 *)
Lemma s5e_chain : forall cx ly S (W : world SEGS) regs mem md k o,
  lt_base B MT cx -> lt_frame B cx ly S W regs mem md k o -> 4096 <= raZ regs ->
  exists ch, chain_pre ly (rdW W mem) regs ch.
Proof.
intros cx ly S W regs mem md k o HB HF Hra.
pose proof (s5e_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
destruct HF as (HJ & R2 & _ & _ & R8 & _).
pose proof HB as (_ & HPRES & _).
pose proof asan_consts as (C1 & _).
assert (HSTK : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity.
assert (Esp : spZ regs = x_s1 cx)
  by (unfold spZ; rewrite R2; unfold w64; rewrite YP03.unsigned_lit_small by lia; reflexivity).
assert (Es0 : s0Z regs = x_sp0 cx)
  by (unfold s0Z; rewrite R8; unfold w64; rewrite YP03.unsigned_lit_small by lia; reflexivity).
apply chain_pre_any; [exact Hra| |].
- rewrite Esp. apply (astack_rd_mono ly _ (x_sp0 cx - STK_LLVMFuzzerTestOneInput)); [lia|].
  apply astack_rd_of_pres.
  apply (astack_pres_journal SEGS B pa_segs_low STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA)
    (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem md k HJ HPRES).
  intros a (r & Hr & Ha) Ha2. exfalso. unfold ltoi_PG in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  unfold longlA, A_LONGL, LONGL_N in Ha. lia.
- rewrite Esp, Es0. lia.
Qed.
(* the facts of a point carried across a run of the walk that writes at most the s1 slots [S1 + lo, S1 + hi) below
   184(s1), keeps sp, gp, tp, s0, s1 and the allocator state *)
Lemma s5e_core_run : forall cx ly S (W : world SEGS) regs mem md k acc rem o O regs' mem' md' lo hi,
  lt_base B MT cx -> lt_core B MT cx ly S W regs mem md k acc rem o O ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem' md' k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 cx + lo <= a < x_s1 cx + hi) -> rdW W mem' a = rdW W mem a) ->
  0 <= lo <= hi -> hi <= 184 ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
  lt_core B MT cx ly S W regs' mem' md' k acc rem o O.
Proof.
intros cx ly S W regs mem md k acc rem o O regs' mem' md' lo hi HB HC HJ' HK Hlo Hhi P2 P3 P4 P8 P9.
pose proof (s5e_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hfr0 & _).
destruct HC as (HF & HI & HBL & HBUD).
destruct HF as (HJ & R2 & R3 & R4 & R8 & R9 & HSV & HH0 & HH8 & HH16 & HFL & H200 & HSH & H184).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity. assert (HAST : ASTACK = 16384) by reflexivity.
pose proof ltoi_stk_room as HSR. unfold LTOI_FRAME_MAX in HSR.
assert (HinF : In (LT_FCLS, x_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (EF : frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx) by exact (s5e_frame_addr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ _ _).
assert (F512 : fs_frame_bytes LT_FCLS = 512) by (vm_compute; reflexivity).
destruct (frames_bounds SEGS B LAWS ly S W mem md LT_FCLS (x_fpos cx) HAR HinF) as (Hf0 & Hfc & _).
rewrite EF in Hf0. rewrite EF, F512 in Hfc.
assert (KA : forall a, 0 <= a < x_s1 cx + lo \/ x_s1 cx + hi <= a < 2 ^ 64 -> rdW W mem' a = rdW W mem a).
{ intros a Ha. apply HK.
  - destruct Ha as [Ha | Ha]; split; lia.
  - intros [Hc1 Hc2]. destruct Ha as [Ha | Ha]; lia. }
split; [|split; [|split]].
- split; [exact HJ'|].
  rewrite P2, P3, P4, P8, P9.
  split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R8|]. split; [exact R9|].
  split.
  { intros i r Hi. assert (Hi13 : (i < length LT_SAVED)%nat) by (apply nth_error_Some; congruence).
    change (length LT_SAVED) with 13%nat in Hi13.
    apply (s5e_word_kept (rdW W mem)); [|exact (HSV i r Hi)]. intros x Hx. apply KA. right. lia. }
  split; [apply (s5e_word_kept (rdW W mem)); [|exact HH0]; intros x Hx; apply KA; left; lia|].
  split; [apply (s5e_word_kept (rdW W mem)); [|exact HH8]; intros x Hx; apply KA; left; lia|].
  split; [apply (s5e_word_kept (rdW W mem)); [|exact HH16]; intros x Hx; apply KA; left; lia|].
  split; [apply (s5e_word_kept (rdW W mem)); [|exact HFL]; intros x Hx; apply KA; left; unfold LT_FLAGW in *; lia|].
  split; [apply (s5e_word_kept (rdW W mem)); [|exact H200]; intros x Hx; apply KA; right; lia|].
  split.
  { intros i Hi. rewrite KA; [exact (HSH i Hi)|]. left. rewrite (lt_fsh_len o) in Hi.
    unfold x_sh, shadow_addr, SHADOW_OFF. lia. }
  apply (s5e_word_kept (rdW W mem)); [|exact H184]; intros x Hx; apply KA; right; lia.
- apply (s5e_img_kept cx ly S W W mem mem' md' (proj1 HJ') HI).
  intros a Ha _ _. apply KA. left. pose proof (pa_segs_low a Ha). lia.
- exact HBL.
- exact HBUD.
Qed.

(* ---------------------------------------------- the free of the text ---------------------------------------------- *)
(* the live blocks of a state are distinct *)
Lemma s5e_nodup : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> List.NoDup (ablocks B ly S).
Proof.
intros ly S W mem md HAR.
destruct (ablocks B ly S) as [|[p0 n0] bl] eqn:Eb; [constructor|].
assert (Hin0 : In (p0, n0) (ablocks B ly S)) by (rewrite Eb; left; reflexivity).
destruct (al_blocks _ _ LAWS ly S W mem md p0 n0 HAR Hin0) as (_ & _ & _ & _ & _ & Hpw & _).
rewrite <- Eb. apply (NoDup_map_inv (fun b : Z * Z => (fst b, req_size (snd b)))).
apply s5e_pzd_nodup; [|exact Hpw].
intros [a q] Hx. apply in_map_iff in Hx as ([pb nb] & Hq & Hpb). cbn in Hq. injection Hq as <- <-.
destruct (al_blocks _ _ LAWS ly S W mem md pb nb HAR Hpb) as (_ & _ & _ & _ & _ & _ & Hn).
cbn [snd]. pose proof (req_size_pos nb ltac:(lia)). lia.
Qed.
(* the head of the cut's block list is live and is not one of the entry's blocks nor of the rest *)
Lemma s5e_blk_head : forall cx ly S (W : world SEGS) mem md pa n O,
  AR SEGS B ly S W mem md -> lt_blocks B cx ly S ((pa, n) :: O) ->
  In (pa, n) (ablocks B ly S) /\ ~ In (pa, n) (x_bl0 B cx) /\ ~ In (pa, n) O.
Proof.
intros cx ly S W mem md pa n O HAR HP.
assert (HND : List.NoDup (ablocks B ly S)) by exact (s5e_nodup ly S W mem md HAR).
pose proof (Permutation_NoDup HP HND) as HND2. cbn [app] in HND2.
apply NoDup_cons_iff in HND2 as [Hni _].
split; [apply (Permutation_in _ (Permutation_sym HP)); left; reflexivity|].
split; intros Hb; apply Hni; apply in_or_app; [right | left]; exact Hb.
Qed.
(* the facts of a point after the free of the head block of the harness's list at sp = S1: the journal goes on
   with one event, the kept registers and every byte the facts read are the same, the block leaves the list,
   the budget pays one event (image B's S01 / S02 walk's lk_after_alloc, one block fewer) *)
Lemma s5e_after_free : forall cx ly S (W : world SEGS) regsT memT md k acc rem o pa n O
  ly2 S2 (W2 : world SEGS) regs2 mem2 md2 slo,
  lt_base B MT cx -> lt_core B MT cx ly S W regsT memT md k acc rem o ((pa, n) :: O) -> 1 <= rem ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly2 S2 W2 mem2 md2 (k + 1) ->
  aregs_preserved regsT regs2 -> frames S2 = frames S ->
  (exists l1 l2, ablocks B ly S = l1 ++ (pa, n) :: l2 /\ ablocks B ly2 S2 = l1 ++ l2) ->
  acall_kept SEGS B ly S W memT W2 mem2 slo (x_s1 cx) (fun a => pa <= a < pa + req_size n) ->
  mo_le MT S S2 (mo_free MT) ->
  lt_core B MT cx ly2 S2 W2 regs2 mem2 md2 (k + 1) (acc + mo_free MT) (rem - 1) o O /\
  (forall a, x_s1 cx <= a < 2 ^ 64 -> rdW W2 mem2 a = rdW W memT a) /\
  (forall b sz i, In (b, sz) O -> 0 <= i < req_size sz -> rdW W2 mem2 (b + i) = rdW W memT (b + i)).
Proof.
intros cx ly S W regsT memT md k acc rem o pa n O ly2 S2 W2 regs2 mem2 md2 slo HB HC Hrem HJ2 HP Hfr2 Hbl HKc MLE.
pose proof (s5e_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hfr0 & _ & HEV & _ & HMO).
destruct HC as (HF & HI & HBL & HBUD).
destruct HF as (HJ & R2 & R3 & R4 & R8 & R9 & HSV & HH0 & HH8 & HH16 & HFL & H200 & HSH & H184).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
pose proof HKc as (K1 & K2 & K3 & K4 & _ & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity. assert (HAST : ASTACK = 16384) by reflexivity.
pose proof ASAN_CEIL_range as (CR & _).
destruct (s5e_blk_head cx ly S W memT md pa n O HAR HBL) as (HinB & _ & HnO).
assert (HinF : In (LT_FCLS, x_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (EF : frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx) by exact (s5e_frame_addr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ _ _).
assert (F512 : fs_frame_bytes LT_FCLS = 512) by (vm_compute; reflexivity).
destruct (frames_bounds SEGS B LAWS ly S W memT md LT_FCLS (x_fpos cx) HAR HinF) as (Hf0 & Hfc & _).
rewrite EF in Hf0. rewrite EF, F512 in Hfc.
destruct (al_blocks _ _ LAWS ly S W memT md pa n HAR HinB) as (_ & Hp4096 & Hpceil & Hpapp & _ & _ & Hn).
pose proof (sep_block_frame SEGS B LAWS ly S W memT md pa n LT_FCLS (x_fpos cx) HAR HinB HinF) as Hsep.
rewrite EF, F512 in Hsep. unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
pose proof (req_size_pos n ltac:(lia)) as [Hq1 _].
(* the stack above S1 *)
assert (KS : forall a, x_s1 cx <= a < 2 ^ 64 -> rdW W2 mem2 a = rdW W memT a).
{ intros a Ha. pose proof ltoi_stk_room as HSR. unfold LTOI_FRAME_MAX in HSR.
  apply K1; [split; [lia | exact (proj2 Ha)] |]. intros [_ Hc]. lia. }
(* the frame's bytes *)
assert (KF : forall a, x_fr cx <= a < x_fr cx + 512 -> rdW W2 mem2 a = rdW W memT a).
{ intros a Ha. apply (K4 LT_FCLS (x_fpos cx) a HinF).
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF, F512. lia.
  - cbv beta. intros Hr. lia. }
(* the frame's shadow bytes *)
assert (KH : forall i, 0 <= i < 64 -> rdW W2 mem2 (x_sh cx + i) = rdW W memT (x_sh cx + i)).
{ intros i Hi. apply (K4 LT_FCLS (x_fpos cx) _ HinF).
  - right. unfold in_zr. cbn [fst snd]. rewrite EF, F512. unfold x_sh. lia.
  - cbv beta. intros Hr. unfold in_app, kLowShadowBeg, ASAN_CEIL in Hpapp. unfold x_sh, shadow_addr, SHADOW_OFF in Hr.
    lia. }
split; [|split; [exact KS|]].
2:{ intros b sz i Hb Hi.
    assert (HbB : In (b, sz) (ablocks B ly S))
      by (apply (Permutation_in _ (Permutation_sym HBL)); apply in_or_app; left; right; exact Hb).
    assert (Hne : (b, sz) <> (pa, n)) by (intros E; apply HnO; rewrite <- E; exact Hb).
    pose proof (sep_blocks SEGS B LAWS ly S W memT md b sz pa n HAR HbB HinB Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd.
    apply (K2 b sz i HbB Hi). cbv beta. lia. }
split; [|split; [|split]].
- (* the frame *)
  split; [exact HJ2|].
  rewrite (s5e_pres_reg _ _ 2%bv 2 HP ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (s5e_pres_reg _ _ 3%bv 3 HP ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (s5e_pres_reg _ _ 4%bv 4 HP ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (s5e_pres_reg _ _ 8%bv 8 HP ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (s5e_pres_reg _ _ 9%bv 9 HP ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R8|]. split; [exact R9|].
  split.
  { intros i r Hi. assert (Hi13 : (i < length LT_SAVED)%nat) by (apply nth_error_Some; congruence).
    change (length LT_SAVED) with 13%nat in Hi13.
    apply (s5e_word_kept (rdW W memT)); [|exact (HSV i r Hi)]. intros x Hx. apply KS. lia. }
  split; [apply (s5e_word_kept (rdW W memT)); [|exact HH0]; intros x Hx; apply KF; lia|].
  split; [apply (s5e_word_kept (rdW W memT)); [|exact HH8]; intros x Hx; apply KF; lia|].
  split; [apply (s5e_word_kept (rdW W memT)); [|exact HH16]; intros x Hx; apply KF; unfold LT_FLAGW; lia|].
  split; [apply (s5e_word_kept (rdW W memT)); [|exact HFL]; intros x Hx; apply KF; unfold LT_FLAGW in *; lia|].
  split; [apply (s5e_word_kept (rdW W memT)); [|exact H200]; intros x Hx; apply KS; lia|].
  split.
  { intros i Hi. rewrite (lt_fsh_len o) in Hi. rewrite KH by lia. exact (HSH i ltac:(rewrite lt_fsh_len; exact Hi)). }
  apply (s5e_word_kept (rdW W memT)); [|exact H184]; intros x Hx; apply KS; lia.
- (* the image facts *)
  exact (s5e_img_kept cx ly2 S2 W W2 memT mem2 md2 (proj1 HJ2) HI K3).
- (* the blocks *)
  unfold lt_blocks in *. exact (s5e_perm_free _ _ _ _ _ HBL Hbl).
- (* the budget *)
  destruct HBUD as (B1 & B2 & B3 & B4 & B5 & B6).
  pose proof (mo_free_nonneg MT MTL) as Hf0'. pose proof (mo_malloc_nonneg MT MTL 65536 ltac:(lia)) as Hm0.
  assert (HU : mo_free MT <= LT_U MT) by (unfold LT_U; lia).
  unfold lt_bud. split; [lia|]. split; [lia|]. split; [lia|].
  split; [exact (mo_le_trans MT MTL _ _ _ _ _ B4 MLE)|]. split; [lia|].
  set (U := LT_U MT) in *. clearbody U. nia.
Qed.
(* ---- one call of the free wrapper (the trampoline the listing's PCall names) on the head block of the harness's
   list, from a point where lt_core holds; the image A route of the S16 .. S20 walk's s24_free, in the S01 / S02 walk's
   lt_malloc_at form ---- *)
Lemma s5e_free_at : forall cx ly S (W : world SEGS) regsT memT md k acc rem o pa n O raw Q,
  lt_base B MT cx -> lt_core B MT cx ly S W regsT memT md k acc rem o ((pa, n) :: O) -> 1 <= rem ->
  getr regsT 10 = w64 pa -> getr regsT 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  (forall ly2 S2 (W2 : world SEGS) regs2 mem2 md2,
     lt_core B MT cx ly2 S2 W2 regs2 mem2 md2 (k + 1) (acc + mo_free MT) (rem - 1) o O ->
     aregs_preserved regsT regs2 ->
     (forall a, x_s1 cx <= a < 2 ^ 64 -> rdW W2 mem2 a = rdW W memT a) ->
     (forall b sz i, In (b, sz) O -> 0 <= i < req_size sz -> rdW W2 mem2 (b + i) = rdW W memT (b + i)) ->
     SRr SEGS W2 (mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (SIG SS___interceptor_trampoline_free)) memT (seg_rom SEGS)) md) Q.
Proof.
intros cx ly S W regsT memT md k acc rem o pa n O raw Q HB HC Hrem H10 H1 Hraw Hra4 HK.
pose proof (s5e_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
pose proof HC as (HF & _ & HBL & HBUD).
pose proof HF as (HJ & R2 & R3 & R4 & _).
pose proof (proj1 HJ) as HAR.
pose proof HB as (HPRE0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hev & _ & Hmo).
pose proof HPRE0 as (_ & _ & _ & Hgp0 & Htp0 & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _).
pose proof HBUD as (B1 & B2 & B3 & B4 & B5 & B6).
pose proof asan_consts as (C1 & _).
assert (HSTK : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity. assert (HAST : ASTACK = 16384) by reflexivity.
pose proof ltoi_stk_room as HSR. unfold LTOI_FRAME_MAX in HSR.
destruct (s5e_blk_head cx ly S W memT md pa n O HAR HBL) as (HinB & Hnb0 & _).
pose proof (mo_free_nonneg MT MTL) as Hf0. pose proof (mo_malloc_nonneg MT MTL 65536 ltac:(lia)) as Hm0.
assert (HU : mo_free MT <= LT_U MT) by (unfold LT_U; lia).
assert (HU0 : 0 <= LT_U MT) by (unfold LT_U; lia).
assert (MOK : mo_ok MT S (mo_free MT)).
{ apply (mok_station MT (x_S cx) S (XM_LTOI MT (x_pl cx)) acc (mo_free MT) MTL Hmo B4 Hf0). nia. }
assert (Hsp : spZ regsT = x_sp0 cx + (x_s1 cx - x_sp0 cx)).
{ unfold spZ. rewrite R2. unfold w64. rewrite YP03.unsigned_lit_small by lia. lia. }
destruct (s5e_chain cx ly S W regsT memT md k o HB HF ltac:(unfold raZ; rewrite H1; exact Hra4)) as (ch & Hch).
assert (Hcov : In (pa, n) (ablocks B (x_ly cx) (x_S cx)) -> forall i, 0 <= i < req_size n ->
  inFP (ltoi_PG longlA) (pa + i)) by (intros Hb; exfalso; exact (Hnb0 Hb)).
rewrite (pal_free B TL).
eapply SRr_bind.
{ exact (afree04_sub SEGS B LAWS pa_segs_low MT (AFREE4 fx) W regsT memT STK_LLVMFuzzerTestOneInput (x_sp0 cx)
    (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [(LT_FCLS, x_fpos cx)] ly S md k pa n
    (x_s1 cx - x_sp0 cx) raw ch HJ HinB H10 Hsp ltac:(lia) ltac:(lia)
    ltac:(unfold ASTACK in *; lia)
    ltac:(rewrite R3; exact Hgp0) ltac:(rewrite R4; exact Htp0) H1 Hraw ltac:(unfold EV_LTOI in *; lia) Hch Hcov MOK). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HPr & Hbl & Hfr & HKp & MLE & _).
replace (x_sp0 cx + (x_s1 cx - x_sp0 cx)) with (x_s1 cx) in HKp by ring.
destruct (s5e_after_free cx ly S W regsT memT md k acc rem o pa n O ly2 S2 W2 regs2 mem2 md2 _
  HB HC Hrem HJ2 HPr Hfr Hbl HKp MLE) as (HC2 & HK2 & HKB).
exact (HK ly2 S2 W2 regs2 mem2 md2 HC2 HPr HK2 HKB).
Qed.

(* a word of a chunk of the symbolic state, read through the reader (image A's S03 walk's s13_chunk_word, through
   PaDenot's region lemmas) *)
Lemma s5e_chunk_word : forall (W : world SEGS) E ss ms i rg p off e a v,
  st_ok SEGS E ss (restrict (w_H W) ms) -> nth_error (ss_mem ss) i = Some rg -> YP09.r_base rg = Some p ->
  In (YP09.mkChunk off (CVal 8 e)) (YP09.r_chunks rg) -> bv_unsigned (ew E p) = a ->
  U E e = v -> 0 <= v < 2 ^ 64 ->
  rdword (rdW W (ms_mem ms)) (a + off) = Some v.
Proof.
intros W E ss ms i rg p off e a v HS Hi Hb Hc Ha HU Hv.
assert (He : sv_denot E e = Z_to_bv 64 v) by (apply bv_eq; rewrite unsigned_lit_small by lia; exact HU).
pose proof (st_ok_region_nth E ss _ i rg HS Hi) as HR.
destruct rg as [b lo hi wlo whi cs]. cbn [YP09.r_base YP09.r_chunks] in Hb, Hc. subst b.
pose proof (field_of_region E _ p a cs lo hi wlo whi off 8 e v HR Ha Hc He
  ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)) as HV.
cbn [ms_mem restrict] in HV.
exact (rdword_of_val_mem SEGS (w_H W) (ms_mem ms) (a + off) v HV Hv).
Qed.

(* ------------------------------------------------ the seed at 0x852e4 ------------------------------------------------ *)
Lemma s5e_seed : forall (W : world SEGS) (regs : bvmap 5 word) mem s1 m ans np n1 rt nn,
  getr regs 9 = w64 s1 -> 2 ^ 46 <= s1 -> s1 + 224 <= 2 ^ 47 -> s1 mod 32 = 0 ->
  getr regs 22 = w64 m -> 4096 <= m -> m + 9236 <= 140737479966720 -> m mod 16 = 0 -> m + 9236 <= s1 ->
  getr regs 10 = w64 ans -> 0 <= ans <= 32 ->
  getr regs 21 = w64 0 -> getr regs 26 = w64 ((m + seg_spec.MC_N) / 8) ->
  0 <= np < 2 ^ 64 -> 0 <= n1 < 2 ^ 64 -> 0 <= rt <= 1 -> 0 <= nn <= 32 ->
  rdword (rdW W mem) (s1 + 152) = Some np -> rdword (rdW W mem) (s1 + 160) = Some n1 ->
  rdword (rdW W mem) (s1 + 176) = Some rt -> rdword (rdW W mem) (s1 + 192) = Some m ->
  rdword (rdW W mem) (s1 + 200) = Some SHADOW_OFF -> rdword (rdW W mem) (s1 + 216) = Some (m + seg_spec.MC_N) ->
  rd32 (rdW W mem) (m + seg_spec.MC_N) nn ->
  (forall a, s1 + 176 <= a < s1 + 184 -> apresent (w_H W) mem a) ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs [Z_to_bv 64 np; Z_to_bv 64 n1; Z_to_bv 64 rt; Z_to_bv 64 nn])) s5e_ss
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO_S5CK)) mem (seg_rom SEGS))).
Proof.
intros W regs mem s1 m ans np n1 rt nn R9 Hs1a Hs1b Hs1c R22 Hm1 Hm2 Hm16 Hms1 R10 Hans R21 R26 Hnp Hn1 Hrt Hnn
  W152 W160 W176 W192 W200 W216 W8192 Hpres.
set (E := Eimg (Ereg regs [Z_to_bv 64 np; Z_to_bv 64 n1; Z_to_bv 64 rt; Z_to_bv 64 nn])).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 np; Z_to_bv 64 n1; Z_to_bv 64 rt; Z_to_bv 64 nn]) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E9 : ew E 9 = Z_to_bv 64 s1)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact R9).
assert (E10 : ew E 10 = Z_to_bv 64 ans)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact R10).
assert (E22 : ew E 22 = Z_to_bv 64 m)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl); exact R22).
assert (E32 : ew E 32 = Z_to_bv 64 np) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 n1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 rt) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 nn) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (VB9 : base_val E (Some 9%nat) = s1) by (cbn [base_val]; rewrite E9; apply unsigned_lit_small; lia).
assert (VB22 : base_val E (Some 22%nat) = m) by (cbn [base_val]; rewrite E22; apply unsigned_lit_small; lia).
pose proof (val_mem_of_rdword SEGS (w_H W) mem (s1 + 152) np W152) as V152.
pose proof (val_mem_of_rdword SEGS (w_H W) mem (s1 + 160) n1 W160) as V160.
pose proof (val_mem_of_rdword SEGS (w_H W) mem (s1 + 176) rt W176) as V176.
pose proof (val_mem_of_rdword SEGS (w_H W) mem (s1 + 192) m W192) as V192.
pose proof (val_mem_of_rdword SEGS (w_H W) mem (s1 + 200) SHADOW_OFF W200) as V200.
pose proof (val_mem_of_rdword SEGS (w_H W) mem (s1 + 216) (m + seg_spec.MC_N) W216) as V216.
pose proof (val_mem_of_rd32 SEGS (w_H W) mem (m + seg_spec.MC_N) nn W8192) as V8192.
assert (HS0 : st_ok_pi SEGS VAL E (mkSS LO_S5CK sr_atoms s5e_rg None s5e_fa)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO_S5CK)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold s5e_rg. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]; rewrite ?VB9, ?VB22;
      (split; [lia|]); (split; [lia|]).
    + split; [intros o Ho; apply (apresent_writable SEGS); apply Hpres; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val SEGS E _ s1 152 8 (SOff 32 0) np);
          [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia | exact V152].
      * apply (chunk_ok_val SEGS E _ s1 160 8 (SOff 33 0) n1);
          [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia | exact V160].
      * apply (chunk_ok_val SEGS E _ s1 176 8 (SOff 34 0) rt);
          [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia | exact V176].
      * apply (chunk_ok_val SEGS E _ s1 192 8 (SOff 22 0) m);
          [cbn [sv_denot]; rewrite E22, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia | exact V192].
      * apply (chunk_ok_val SEGS E _ s1 200 8 (SLit SHADOW_OFF) SHADOW_OFF);
          [reflexivity | unfold SHADOW_OFF; cbn; lia | lia | exact V200].
      * apply (chunk_ok_val SEGS E _ s1 216 8 (SOff 22 8192) (m + seg_spec.MC_N));
          [cbn [sv_denot]; rewrite E22, unsigned_lit_small by lia; reflexivity
          | unfold seg_spec.MC_N; cbn; lia | lia | exact V216].
    + split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      apply (chunk_ok_val SEGS E _ m 8192 4 (SOff 35 0) nn);
        [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia | exact V8192].
  - apply pairwise_disjoint_of_extents. unfold s5e_rg, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite VB9, VB22.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [s5e_fa f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E9, E22, E10, E34, E35, !unsigned_lit_small by lia.
    change (2 ^ 5) with 32. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia]. }
pose proof (st_ok_pi_pin_reg' E _ _ 21%bv 0 HS0 ltac:(cbn [ms_regs restrict mkst]; exact R21) eq_refl) as HS1.
refine (st_ok_pi_set_reg E _ _ 26%bv (SAlu ALU_SRL (SOff 22 8192) (SLit 3)) HS1 ltac:(discriminate) _).
cbn [ms_regs restrict mkst]. rewrite R26.
apply bv_eq. unfold w64. rewrite unsigned_lit_small by (unfold seg_spec.MC_N; lia).
change (bv_unsigned (sv_denot E (SAlu ALU_SRL (SOff 22 8192) (SLit 3)))) with (U E (SAlu ALU_SRL (SOff 22 8192) (SLit 3))).
rewrite U_SAlu, U_SLit, U_SOff, E22, unsigned_lit_small by lia.
rewrite (zcanon_id 3) by (unfold M64; lia). rewrite (zcanon_id (m + 8192)) by (unfold M64; lia).
cbn [zalu_raw]. change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
rewrite zcanon_id by (unfold M64; lia). unfold seg_spec.MC_N. reflexivity.
Qed.

Lemma s5_tail : forall f, LTA_K85530 B MT f -> S5_CK_stmt B MT f.
Proof using All.
intros f HKA. unfold S5_CK_stmt.
intros cx ly S W regs mem md k acc c m t lp HB Hfrm Hf HBODY Hrc Hmc Hcnt R10 R18 R19 R21 R22 R23 R24 R25 R26 HSL.
pose proof (HKA fx) as HK. clear HKA.
destruct HBODY as (HC & HHc & HHm & HHt & _).
pose proof HC as (HFRM & HIMG & HBL & HBUD).
pose proof HFRM as (HJ & R2 & R3 & R4 & R8 & R9 & HSV & HH0 & HH8 & HH16 & HFL & H200 & HSH & H184).
pose proof (proj1 HJ) as HAR.
pose proof (s5e_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity. assert (HAST : ASTACK = 16384) by reflexivity.
pose proof ltoi_stk_room as HSR. unfold LTOI_FRAME_MAX in HSR.
pose proof pa_B_ok as HBok. pose proof pa_base_lo as HBLO.
pose proof HHm as (HmIn & Hm4 & Hm16 & _).
destruct (al_blocks _ _ LAWS ly S W mem md m _ HAR HmIn) as (_ & _ & Hmce & Hmapp & Hmpres & _).
change (req_size seg_spec.SEG_M_SIZE) with 9236 in Hmce, Hmapp, Hmpres.
(* the slots the run reads *)
assert (HSL' : forall o v, In (o, v) (S5_slots cx c m f) -> rdword (rdW W mem) (x_s1 cx + o) = Some v) by exact HSL.
assert (S152 : rdword (rdW W mem) (x_s1 cx + 152) = Some (x_np cx f))
  by (apply HSL'; unfold S5_slots; apply in_or_app; right; left; reflexivity).
assert (S160 : rdword (rdW W mem) (x_s1 cx + 160) = Some (x_n1 cx f))
  by (apply HSL'; unfold S5_slots; apply in_or_app; right; right; left; reflexivity).
assert (S176 : rdword (rdW W mem) (x_s1 cx + 176) = Some (seg_spec.b2z (seg_spec.seg_ret (x_st cx f))))
  by (apply HSL'; unfold S5_slots; apply in_or_app; right; right; right; left; reflexivity).
assert (S192 : rdword (rdW W mem) (x_s1 cx + 192) = Some m)
  by (apply HSL'; unfold S5_slots, LT_L; apply in_or_app; left; cbn [In]; tauto).
assert (S216 : rdword (rdW W mem) (x_s1 cx + 216) = Some (m + seg_spec.MC_N))
  by (apply HSL'; unfold S5_slots, LT_L; apply in_or_app; left; cbn [In]; tauto).
(* the model's numbers *)
pose proof (s5_np_le (x_pl cx) f) as Hnp1. pose proof (s5_np_nat (x_pl cx) f) as Hnp2.
pose proof (s5_tail_sfx (x_pl cx) f) as Hsfx. apply s5_sfx_len in Hsfx.
pose proof HB as (_ & _ & _ & _ & _ & _ & Hpn & Hnpl & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
assert (Hlpl : Z.of_nat (length (seg_spec.seg_in (x_pl cx))) < 2 ^ 26).
{ unfold seg_spec.seg_in, seg_spec.zs. rewrite length_map. rewrite <- Hnpl. destruct Hpn as [[Hn _] | [Hn _]]; lia. }
assert (Hnp : 0 <= x_np cx f <= x_n1 cx f) by (unfold x_np, x_n1; lia).
assert (Hn1 : x_n1 cx f < 2 ^ 26) by (unfold x_n1; lia).
assert (Hrt : 0 <= seg_spec.b2z (seg_spec.seg_ret (x_st cx f)) <= 1)
  by (unfold seg_spec.b2z; destruct (seg_spec.seg_ret (x_st cx f)); lia).
destruct (s5e_mconf_n _ _ _ Hmc) as (Hnn32 & W8192).
pose proof (s5e_rconf_n _ _ _ Hrc) as Hans32.
assert (Hans : 0 <= snd (s5_rp (x_pl cx) f) <= 32).
{ unfold s5_rp. rewrite s5e_rp_snd. fold (s5_rp (x_pl cx) f). lia. }
(* the seed *)
pose proof (s5e_seed W regs mem (x_s1 cx) m (snd (s5_rp (x_pl cx) f)) (x_np cx f) (x_n1 cx f)
  (seg_spec.b2z (seg_spec.seg_ret (x_st cx f))) (Z.of_nat (length (SegModel.mc_seg (s5_mc1 (x_pl cx) f))))
  R9 ltac:(lia) ltac:(lia) Hs1al R22 Hm4 ltac:(lia) Hm16 ltac:(lia) R10 Hans R21 R26 ltac:(lia) ltac:(lia) Hrt ltac:(lia)
  S152 S160 S176 S192 H200 S216 W8192 (fun a Ha => Hpres a ltac:(lia))) as HS.
set (E := Eimg (Ereg regs [Z_to_bv 64 (x_np cx f); Z_to_bv 64 (x_n1 cx f);
  Z_to_bv 64 (seg_spec.b2z (seg_spec.seg_ret (x_st cx f)));
  Z_to_bv 64 (Z.of_nat (length (SegModel.mc_seg (s5_mc1 (x_pl cx) f))))])) in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr)
  by (intros n rr Hn; unfold E; exact (ew_Eimg_Ereg_nat regs _ n rr Hn)).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 (x_np cx f); Z_to_bv 64 (x_n1 cx f);
  Z_to_bv 64 (seg_spec.b2z (seg_spec.seg_ret (x_st cx f)));
  Z_to_bv 64 (Z.of_nat (length (SegModel.mc_seg (s5_mc1 (x_pl cx) f))))]) n)
  by (intros n Hn; unfold E; apply Eimg_low; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 (x_np cx f)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (x_n1 cx f)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (seg_spec.b2z (seg_spec.seg_ret (x_st cx f))))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (Z.of_nat (length (SegModel.mc_seg (s5_mc1 (x_pl cx) f)))))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (Usp9 : bv_unsigned (ew E 9) = x_s1 cx).
{ rewrite (EEo 9%nat 9%bv eq_refl), R9. unfold w64. apply unsigned_lit_small. lia. }
assert (U22 : U E (SOff 22 0) = m).
{ apply U_atom; [rewrite (EEo 22%nat 22%bv eq_refl); exact R22 | lia]. }
assert (SHOK : sh_ok SEGS s5e_X s5e_SH E (mrestrict (w_H W) mem)).
{ unfold sh_ok, s5e_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) mem E s5e_X 22 (m + 8192) 8 m 8192 8200).
  - apply (range_addressable_of_block SEGS B LAWS ly S W mem md m seg_spec.SEG_M_SIZE); [exact HAR | exact HmIn | lia |].
    change (req_size seg_spec.SEG_M_SIZE) with 9236. lia.
  - unfold s5e_X. apply U_lit. unfold SHADOW_OFF. lia.
  - exact U22.
  - lia.
  - lia.
  - intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hmapp. unfold SHADOW_OFF. lia. }
clearbody E. clear EL.
unfold cfg_at, w64.
(* 0x852e4 .. 0x8552c: the shadow base, the trap (s5 = 0), check 8 (the shadow entry), a3 := N1, m->n, the latch
   into 176(s1), s6 := m, j 0x85520, a0 := NP, s4 := N1 - NP, a0 := t; then the jal of the free wrapper *)
paj_run_tok RUN HS HJ SHOK s5e_span.
{ lazymatch goal with |- awr_ok _ _ _ ?rs _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
  repeat first
    [ apply awr_ok_nil
    | apply awr_ok_cons_ro; [cbn; lia|]
    | apply awr_ok_cons_stack_off with (n := 9%nat) (d := x_s1 cx - x_sp0 cx);
        [reflexivity | rewrite Usp9; lia | cbn; lia | cbn; lia |] ]. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md1 := d) in *; clearbody md1 end.
pmkst HS.
(* the registers and the slot the run leaves *)
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (10%bv : bv 5) P10.
prreg HS (18%bv : bv 5) P18. prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22.
prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25.
assert (P20 : getr (ms_regs ms) 20 = sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff 32 0) (SLit (-1))) (SOff 33 0)))
  by exact (st_ok_restrict_reg SEGS (w_H W) E _ ms 20%bv HS).
assert (P26 : getr (ms_regs ms) 26 = sv_denot E (SAlu ALU_SRL (SOff 22 8192) (SLit 3)))
  by exact (st_ok_restrict_reg SEGS (w_H W) E _ ms 26%bv HS).
lazymatch goal with Hfr : frame_of E _ (mrestrict _ _) (mrestrict _ _) |- _ =>
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 cx + 176 <= a < x_s1 cx + 184) -> rdW W (ms_mem ms) a = rdW W mem a)
by (intros a Ha Hn; apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => x_s1 cx + 176 <= a < x_s1 cx + 184) Hfr); [
   intros b wlo whi a' Hin Hrr; vm_compute in Hin;
   repeat (destruct Hin as [Hq0 | Hin];
     [injection Hq0 as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp9 in Hrr; lia|]);
   destruct Hin
 | exact Ha | exact Hn ]) end.
assert (W176 : rdword (rdW W (ms_mem ms)) (x_s1 cx + 176) = Some (seg_spec.b2z (seg_spec.seg_ret (x_af cx f)))).
{ lazymatch type of HS with st_ok _ _ ?ss _ =>
    let l := eval vm_compute in (nth_error (ss_mem ss) 0) in
    lazymatch l with Some ?rg =>
      apply (s5e_chunk_word W E ss ms 0 rg 9%nat 176
        (SAlu ALU_AND (SAlu ALU_ADD (SAlu ALU_SLTU (SLit 0) (SAlu ALU_XOR (SOff 10 0) (SOff 35 0))) (SLit (-1)))
          (SOff 34 0)) _ _ HS);
      [ vm_compute; reflexivity | reflexivity | cbn [YP09.r_chunks]; left; reflexivity | exact Usp9 | | ]
    end
  end.
  - unfold x_af. rewrite (s5e_after (x_pl cx) f Hf). cbn [seg_spec.seg_ret snd].
    apply s5e_latch; [rewrite (EEo 10%nat 10%bv eq_refl); exact R10 | exact E35 | exact E34 | lia | lia].
  - unfold seg_spec.b2z. destruct (seg_spec.seg_ret (x_af cx f)); lia. }
(* the core at the call, across the run (it wrote 176(s1) only) *)
assert (KR : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> getr (ms_regs ms) r = ew E n -> getr (ms_regs ms) r = getr regs r)
  by (intros n r Hn Hr; rewrite Hr; exact (EEo n r Hn)).
pose proof (s5e_core_run cx ly S W regs mem md k acc (5 + 2 * (x_nf cx - Z.of_nat f)) LFO_L
  [(t, x_tn cx f); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] (ms_regs ms) (ms_mem ms) md1 176 184 HB HC HJ
  KEEP ltac:(lia) ltac:(lia)
  (KR 2%nat 2%bv eq_refl P2) (KR 3%nat 3%bv eq_refl P3) (KR 4%nat 4%bv eq_refl P4)
  (KR 8%nat 8%bv eq_refl P8) (KR 9%nat 9%bv eq_refl P9)) as HC1.
(* the free of the text block *)
pose proof HHc as (HcIn & _).
destruct (al_blocks _ _ LAWS ly S W mem md c _ HAR HcIn) as (_ & Hc4096 & Hcce & _).
change (req_size seg_spec.SEG_C_SIZE) with 16616 in Hcce.
apply (s5e_free_at cx ly S W (ms_regs ms) (ms_mem ms) md1 k acc (5 + 2 * (x_nf cx - Z.of_nat f)) LFO_L t (x_tn cx f)
  [(m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] (getr (ms_regs ms) 1) (lt_post B MT cx) HB HC1).
{ lia. }
{ rewrite P10, (EEo 23%nat 23%bv eq_refl). exact R23. }
{ reflexivity. }
{ rewrite P1. apply ret_ok_codeptr_v; [lia | reflexivity]. }
{ rewrite P1. rewrite unsigned_lit_small by lia. lia. }
intros ly2 S2 W2 regs2 mem2 md2 HC2 HPr HKS HKB.
pose proof HC2 as (HF2 & _ & HBL2 & _). pose proof (proj1 (proj1 HF2)) as HAR2.
assert (HPR : forall n (r : bv 5), acallee_saved (Z.of_nat n) -> Z.of_nat n = bv_unsigned r ->
  getr regs2 r = getr (ms_regs ms) r).
{ intros n r Hs Hn. apply (s5e_pres_reg _ _ r (Z.of_nat n) HPr Hs). apply bv_eq. rewrite Hn.
  rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. }
rewrite P1.
refine (HK cx ly2 S2 W2 regs2 mem2 md2 (k + 1) (acc + mo_free MT) c m HB Hfrm _ _ _ _ _ _ _ _ _ _ _ _ _ _).
- lia.
- replace (6 + 2 * (x_nf cx - Z.of_nat (Datatypes.S f))) with (5 + 2 * (x_nf cx - Z.of_nat f) - 1) by lia.
  exact HC2.
- apply (s5e_hblk ly2 S2 W2 mem2 md2 c _ HAR2).
  unfold lt_blocks in HBL2. apply (Permutation_in _ (Permutation_sym HBL2)). cbn [app]. right. left. reflexivity.
- apply (s5e_hblk ly2 S2 W2 mem2 md2 m _ HAR2).
  unfold lt_blocks in HBL2. apply (Permutation_in _ (Permutation_sym HBL2)). cbn [app]. left. reflexivity.
- rewrite (HPR 18%nat 18%bv ltac:(unfold acallee_saved; cbn; lia) eq_refl), P18, (EEo 18%nat 18%bv eq_refl). exact R18.
- rewrite (HPR 20%nat 20%bv ltac:(unfold acallee_saved; cbn; lia) eq_refl), P20.
  assert (Hcurn : x_curn cx (Datatypes.S f) = x_n1 cx f - x_np cx f)
    by (unfold x_curn, x_n1, x_np; rewrite s5_cur_n_S; reflexivity).
  rewrite Hcurn. apply bv_eq. unfold w64. rewrite (unsigned_lit_small (x_n1 cx f - x_np cx f)) by lia.
  change (bv_unsigned (sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff 32 0) (SLit (-1))) (SOff 33 0))))
    with (U E (SAlu ALU_ADD (SMd M_MUL (SOff 32 0) (SLit (-1))) (SOff 33 0))).
  apply s5e_sub_val; [exact E32 | exact E33 | lia | lia].
- rewrite (HPR 21%nat 21%bv ltac:(unfold acallee_saved; cbn; lia) eq_refl), P21. reflexivity.
- rewrite (HPR 22%nat 22%bv ltac:(unfold acallee_saved; cbn; lia) eq_refl), P22, (EEo 22%nat 22%bv eq_refl). exact R22.
- rewrite (HPR 24%nat 24%bv ltac:(unfold acallee_saved; cbn; lia) eq_refl), P24, (EEo 24%nat 24%bv eq_refl).
  unfold x_cur. rewrite s5_cur_at_S. exact R24.
- rewrite (HPR 25%nat 25%bv ltac:(unfold acallee_saved; cbn; lia) eq_refl), P25, (EEo 25%nat 25%bv eq_refl).
  replace (Z.of_nat (Datatypes.S f)) with (Z.of_nat f + 1) by lia. exact R25.
- rewrite (HPR 26%nat 26%bv ltac:(unfold acallee_saved; cbn; lia) eq_refl), P26.
  apply s5e_srl_val; [rewrite (EEo 22%nat 22%bv eq_refl); exact R22 | lia | lia].
- (* the slots *)
  intros o v Hin. apply in_app_or in Hin as [Hin | Hin].
  + assert (Ho : 16 <= o <= 216 /\ (o + 8 <= 176 \/ 184 <= o)).
    { unfold LT_L in Hin. cbn [In] in Hin.
      repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- _; lia|]). destruct Hin. }
    assert (Hv : rdword (rdW W mem) (x_s1 cx + o) = Some v)
      by (apply HSL'; unfold S5_slots; apply in_or_app; left; exact Hin).
    apply (s5e_word_kept (rdW W mem)); [|exact Hv]. intros x Hx.
    rewrite (HKS x) by lia. apply KEEP; lia.
  + cbn [In] in Hin. destruct Hin as [Hq | []]. injection Hq as <- <-.
    apply (s5e_word_kept (rdW W (ms_mem ms))); [|exact W176]. intros x Hx. apply HKS. lia.
- (* c and m hold the state after the turn *)
  unfold lt_cm, x_af. rewrite (s5e_after (x_pl cx) f Hf). cbn [seg_spec.seg_rc seg_spec.seg_mc fst snd].
  split.
  + apply (s5e_rconf_kept (rdW W mem)); [|exact Hrc]. intros i Hi.
    rewrite (HKB c seg_spec.SEG_C_SIZE i ltac:(right; left; reflexivity) ltac:(change (req_size seg_spec.SEG_C_SIZE) with 16616; unfold seg_spec.SEG_C_SIZE in Hi; lia)).
    apply KEEP; unfold seg_spec.SEG_C_SIZE in Hi; lia.
  + apply (s5e_mconf_kept (rdW W mem)); [|exact Hmc]. intros i Hi.
    rewrite (HKB m seg_spec.SEG_M_SIZE i ltac:(left; reflexivity) ltac:(change (req_size seg_spec.SEG_M_SIZE) with 9236; unfold seg_spec.SEG_M_SIZE in Hi; lia)).
    apply KEEP; unfold seg_spec.SEG_M_SIZE in Hi; lia.
- unfold x_af. rewrite (s5e_after (x_pl cx) f Hf). cbn [seg_spec.seg_rc seg_spec.seg_mc fst snd]. exact Hcnt.
Qed.


End ee.
End fe.
End de.

(* ============================================ the composition ============================================
   lt_seg_S05 from the five closed pieces. Each piece's section is closed, so its lemma takes the FP state as an
   argument and is applied here at every FP state where a call returns at one of its own (L3, L4, L5); L1 and L2
   are applied at the FP state of K85210. Every piece lemma takes the same argument list, in the order of the
   shared Section header (the pieces' `Proof using All`). *)
Section dS. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section fS.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
Section eS.
Variable B : asyms.
Variable MT : ameter_ops.
Variable snp_lo snp_hi : Z.
Variable snp_cr : list (Z * Z).
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis PRW : prog_rw SEGS B.
Hypothesis VOBJS : seg_val_objs.
Hypothesis SIGP : seg_sig_prog.
Hypothesis IMGF : seg_img_facts SEGS B.
(* the allocator record's symbols at image B's values (lib/B/YF0m.v): with AR it gives the stack-protector
   cells at every state (SegRecCells.seg_rec_cells), since the runtime owns the .got word gotwA *)
Hypothesis HBS : YF0m.SegBSyms B.
Hypothesis HPGS : forall a, inFP (ltoi_PG longlA) a ->
  Exists (in_zr a) (as_prog_static B) /\ in_img SEGS a.
Hypothesis HPG_RO : forall a, inFP (ltoi_PG longlA) a -> ~ in_roP SEGS RLO_A RHI_A a.
Hypothesis HPG_PTR : forall a p,
  ((exists i, (i < 5)%nat /\ a = wordsA + 8 * Z.of_nat i) \/
   (exists i, (i < pin_spec.CAT_N)%nat /\ a = pin_spec.row_addr catA i)) ->
  rdword (fun x => option_map (fun b : byte => bv_unsigned b) (seg_rom SEGS (Z_to_bv 64 x))) a = Some p ->
  p + 65536 <= longlA.
Hypothesis AMEMCPY : forall fx0 : YK11.FPState, aintrin_realizes (fx := fx0) SEGS B OCpy (SIG SS___asan_memcpy).
Hypothesis AMEMSET : forall fx0 : YK11.FPState, aintrin_realizes (fx := fx0) SEGS B OSet (SIG SS___asan_memset).
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState,
  RtPFSeg.seg_asnprintf_realizes (fx := fx0) SEGS B snp_lo snp_hi snp_cr
    (SIG SS___interceptor_trampoline_snprintf) gotwA guardA.
Hypothesis AFREE4 : forall fx0 : YK11.FPState, afree04_rule (fx := fx0) SEGS B MT.
Hypothesis HSNP_LIT : forall x, In x LLVMFuzzerTestOneInput_c.LTOI_LITS ->
  snp_lo <= seg_litA_fz x /\ seg_litA_fz x + Z.of_nat (length x) + 1 <= gotwA.
Hypothesis HSNP_CR : Forall (fun r => snp_lo <= fst r /\ 0 <= snd r /\ fst r + snd r <= snp_hi) snp_cr.
Hypothesis HSNP_LO : 0 <= snp_lo.
Hypothesis HSNP_CEIL : snp_hi <= alloc_ceiling.
Hypothesis HSNP_FAKE : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> snp_hi <= ly_F ly.
Hypothesis HM_FILE : forall fx0 : YK11.FPState,
  m_file_c.m_file_contract (fx := fx0) SEGS B (BASE + AF_m_file) STK_m_file RLO_A RHI_A seg_litA_fz
    wordsA rolesA catA gotwA guardA.
Hypothesis HPARSE_FILE : forall fx0 : YK11.FPState,
  reac_segconf_parse_file_c.reac_segconf_parse_file_contract (fx := fx0) SEGS B
    (BASE + AF_reac_segconf_parse_file) STK_reac_segconf_parse_file RLO_A RHI_A seg_litA_rc catA gotwA guardA.

(* segment S05: K85210 f -> K85338 f (the last turn) or K85530 f *)
Theorem lt_seg_S05 : lt_seg_S05_stmt B MT.
Proof.
unfold lt_seg_S05_stmt. intros f H338 H530.
assert (HCK : S5A_CK B MT f).
{ intros fx1. exact (@s5_tail fx1 rc SK PI B MT snp_lo snp_hi snp_cr MTL MTFL TL TLF ML PRW VOBJS SIGP IMGF HBS
    HPGS HPG_RO HPG_PTR AMEMCPY AMEMSET ASNPRINTF AFREE4 HSNP_LIT HSNP_CR HSNP_LO HSNP_CEIL HSNP_FAKE
    HM_FILE HPARSE_FILE f H530). }
assert (HOTH : S5A_OTH B MT f).
{ intros fx1. exact (@s5_calls fx1 rc SK PI B MT snp_lo snp_hi snp_cr MTL MTFL TL TLF ML PRW VOBJS SIGP IMGF HBS
    HPGS HPG_RO HPG_PTR AMEMCPY AMEMSET ASNPRINTF AFREE4 HSNP_LIT HSNP_CR HSNP_LO HSNP_CEIL HSNP_FAKE
    HM_FILE HPARSE_FILE f HCK). }
assert (HLST : S5A_LST B MT f).
{ intros fx1. exact (@s5_last fx1 rc SK PI B MT snp_lo snp_hi snp_cr MTL MTFL TL TLF ML PRW VOBJS SIGP IMGF HBS
    HPGS HPG_RO HPG_PTR AMEMCPY AMEMSET ASNPRINTF AFREE4 HSNP_LIT HSNP_CR HSNP_LO HSNP_CEIL HSNP_FAKE
    HM_FILE HPARSE_FILE f H338). }
exact (@s5_head fx rc SK PI B MT snp_lo snp_hi snp_cr MTL MTFL TL TLF ML PRW VOBJS SIGP IMGF HBS
  HPGS HPG_RO HPG_PTR AMEMCPY AMEMSET ASNPRINTF AFREE4 HSNP_LIT HSNP_CR HSNP_LO HSNP_CEIL HSNP_FAKE
  HM_FILE HPARSE_FILE f
  (@s5_label fx rc SK PI B MT snp_lo snp_hi snp_cr MTL MTFL TL TLF ML PRW VOBJS SIGP IMGF HBS
    HPGS HPG_RO HPG_PTR AMEMCPY AMEMSET ASNPRINTF AFREE4 HSNP_LIT HSNP_CR HSNP_LO HSNP_CEIL HSNP_FAKE
    HM_FILE HPARSE_FILE f HOTH HLST)).
Qed.

End eS.
End fS.
End dS.
