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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_round_trip.v, with its module paths and module names changed; 4505 of its 4800 lines of code are new or changed and 4758 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan image A (fuzz_segconf.asan, pin sha256 48c5355bdacb): the walk of segment S05 of
   the test harness's entry function LLVMFuzzerTestOneInput (image A entry 0x84d34), the code at
   0x850f8 .. 0x85204 and 0x85404 .. 0x85410: the NULL test of the text block (refuted), checked_memcpy of the
   turn's bytes, text[n] = 0 behind instrumented check 7, label[40] made usable (five frame-shadow stores), the
   label's three arms (snprintf(label, 40, "reac-pw.conf.d/%u-x.conf", lb) / checked_memset(longl, 'L', 120) /
   none), and then either the last turn's m_file(m, text, NULL) to K85208 f, or m_file and
   reac_segconf_parse_file with the label, check 8 on m->n, the latch of `returned`, the cursor update and
   free(text) to K85414 f.

   proves function LLVMFuzzerTestOneInput, segment S05 (reuse search: the rule-24 record of the walk's shared brief, checker
   (fresh, read-only) CONFIRM; none: written new).

   THE THEOREM: lt_seg_S05 : lt_seg_S05_stmt B MT, the statement of LLVMFuzzerTestOneInput_defs.v
   (forall f, LTA_K85208 B MT f -> LTA_K85414 B MT f -> LT_K850f8_stmt B MT f), composed at the end of this file
   from five pieces at the four inner cuts of LLVMFuzzerTestOneInput_s15k.v:
     a  s5_head  : S5_LB_stmt f -> LT_K850f8_stmt f        0x850f8 -> 0x85148
     b  s5_label : S5A_OTH f -> S5A_LST f -> S5_LB_stmt f  0x85148 -> 0x851a4 | 0x851f0
     c  s5_last  : LTA_K85208 f -> S5_LST_stmt f           0x851f0 -> 0x85208
     e  s5_tail  : LTA_K85414 f -> S5_CK_stmt f            0x851c0 -> 0x85414
     d  s5_calls : S5A_CK f -> S5_OTH_stmt f               0x851a4 -> 0x851c0
   Each piece lives in its own closed Section with the identical header and `Proof using All`, so that it can
   be instantiated at the FP state a callee returns (snprintf, m_file and reac_segconf_parse_file each return
   at one of their own, apost_baseF) and every closed piece takes the same argument list. The five pieces of segment
   S05's proof were written separately and are assembled here unchanged.

   THE SECTION HYPOTHESES (the header of each piece; order fixed):
   - B, MT; snp_lo, snp_hi, snp_cr: the image range and read-only ranges of interceptor row 4 (snprintf,
     RtPFSeg.seg_asnprintf_realizes, FINAL at commit 755e9278f8ff, RtPFSeg.v sha256
     5fcabfce1726), with the five HSNP_ facts image A's close computes (_s20 takes the same names);
   - MTL, MTFL (the meter's laws), TL, TLF (the listing's GOT / cell facts), IMGS (_s10's s10_img bundle,
     LLVMFuzzerTestOneInput_s10k.v), BSYM (AF0m.SegBSyms B: AR's stack-protector cells, s10_lt_img_kept's other
     premise), ML (model_laws), PRW (prog_rw), VOBJS, SIGP (the listing's object and program addresses);
   - HPGS, HPG_RO, HPG_PTR: longl is a program static in the image, not read-only, and apart from the 16
     literals the image's words point at (fuzz_command takes these from its B record; segconf's record
     modules SegRecBase / SegRecImg do not build yet: they Require the listing's stage-2 AF0m / AB1v);
   - AMEMCPY, AMEMSET (aintrin_realizes OCpy / OSet), AFREE4 (afree04_rule), ASNPRINTF, HM_FILE, HPARSE_FILE
     (the two callees' FINAL contracts at commit 6f783602b5e3), each at every
     FP state: aintrin_realizes and afree04_rule are indexed by it.
   AR_laws is the kit's theorem YG0q.AR_laws_ok, not a hypothesis. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YC5d YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtPFPf RtPFShared RtPFSx RtPFCmd RtPFSeg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaCall PaDenot PaSB
PaArt PaFx PaLibG SegGlob SegObj.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaLibF.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_c reac_segconf_parse_file_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import LLVMFuzzerTestOneInput_c SegInstA
  LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_s10k LLVMFuzzerTestOneInput_s15k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0d_tail.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require AF0m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================== piece a ======================================== *)

(* ======================= the symbolic states of this piece (before the section block) ======================= *)
(* the shadow base is read from the frame slot 176(s1), so the token runner's Bx is the LITERAL SHADOW_OFF and
   the slot is a read-only region holding it (a decision of the segment's brief) *)
Definition s5a_Bx : sv := SLit SHADOW_OFF.
Definition s5a_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* A, at 0x850f8: every register its own atom, no region; the fact on a0 (= t) refutes `beqz a0` *)
Definition s5a_ssA : sstate :=
  mkSS LO_K850f8 sr_atoms [] None (mkFacts [(10%nat, mkAF 4096 (2 ^ 47 - 1) 0)] [] []).
(* B, at 0x85114, seated afresh: atom 32 = t + n (the value `add a0,s7,s4` computes), its one byte a write
   window, and the slot 176(s1) read-only with the shadow base *)
Definition s5a_rtxt : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 1 [].
Definition s5a_rslot : YP09.region :=
  YP09.mkRegion (Some 9%nat) 176 184 0 0 [YP09.mkChunk 176 (CVal 8 (SLit SHADOW_OFF))].
Definition s5a_ssB : sstate :=
  mkSS 0x3e0 sr_atoms [s5a_rtxt; s5a_rslot] None
    (mkFacts [(32%nat, mkAF 4096 (2 ^ 47 - 1) 0)] []
             [(SAlu ALU_ADD (SOff 23 0) (SOff 20 0), SOff 32 0)]).
Definition s5a_SH : list shent := [mkSHE 32 0 1].
(* C, at 0x85130, for the PLAIN runner: the frame's shadow with the write window of the label's five bytes *)
Definition s5a_rsh : YP09.region := YP09.mkRegion (Some 21%nat) 0 64 12 17 [].
Definition s5a_ssC : sstate := mkSS 0x3fc sr_atoms [s5a_rsh] None (mkFacts [] [] []).

(* ================================ the frame's shadow bytes: LFO0 against LFO_L ================================ *)
Lemma s5a_fsh_lab : forall i, (12 <= i < 17)%nat -> nth i (lt_fsh LFO_L) 0 = 0.
Proof. intros i Hi. do 17 (destruct i as [|i]; [first [reflexivity | lia] |]). lia. Qed.
Lemma s5a_fsh_same : forall i, (i < 36)%nat -> ~ (12 <= i < 17)%nat ->
  nth i (lt_fsh LFO_L) 0 = nth i (lt_fsh LFO0) 0.
Proof. intros i Hi Hn. do 36 (destruct i as [|i]; [first [reflexivity | lia] |]). lia. Qed.

(* ===================================== lists, registers and readers (pure) ===================================== *)
Lemma s5a_nth_firstn : forall {A} (l : list A) L i d, (i < L)%nat -> nth i (firstn L l) d = nth i l d.
Proof.
intros A l. induction l as [|b l IH]; intros [|L] [|i] d Hi; cbn [firstn nth]; try reflexivity; try lia.
apply IH. lia.
Qed.
Lemma s5a_rdword_xfer : forall (rd rd' : reader) a v,
  (forall j, 0 <= j < 8 -> rd' (a + j) = rd (a + j)) -> rdword rd a = Some v -> rdword rd' a = Some v.
Proof. intros rd rd' a v K H. rewrite (rdword_ext rd rd'); [exact H | exact K]. Qed.
Lemma s5a_cm_xfer : forall (rd rd' : reader) c m st,
  (forall i, 0 <= i < seg_spec.SEG_C_SIZE -> rd' (c + i) = rd (c + i)) ->
  (forall i, 0 <= i < seg_spec.SEG_M_SIZE -> rd' (m + i) = rd (m + i)) ->
  lt_cm rd c m st -> lt_cm rd' c m st.
Proof.
intros rd rd' c m st Kc Km ((bc & Hbc & Hec) & (bm & Hbm & Hem)). split.
- exists bc. split; [|exact Hec]. pose proof (proj1 Hec) as Hl. intros i Hi. rewrite Kc by lia. exact (Hbc i Hi).
- exists bm. split; [|exact Hem]. pose proof (proj1 Hem) as Hl. intros i Hi. rewrite Km by lia. exact (Hbm i Hi).
Qed.
Lemma s5a_sll56 : forall z, alu64 ALU_SLL (Z_to_bv 64 z) (Z_to_bv 64 56) = Z_to_bv 64 (Z.shiftl z 56).
Proof.
intros z. apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw].
rewrite !Z_to_bv_unsigned. change (bv_wrap 64 56) with 56. change (Z.land 56 63) with 56.
rewrite !Z.shiftl_mul_pow2 by lia. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
rewrite Zmult_mod_idemp_l. reflexivity.
Qed.
(* `vm_compute` turns `18 <= z <= 27` into a comparison lia cannot read, so the register number is
   computed first and the membership proved on the literal *)
Lemma s5a_cs2 : forall (r : bv 5) (z : Z), bv_unsigned r = z -> acallee_saved z -> acallee_saved (bv_unsigned r).
Proof. intros r z H Hz. rewrite H. exact Hz. Qed.
Ltac s5a_cs :=
  lazymatch goal with
  | |- acallee_saved (bv_unsigned ?r) =>
      let z := eval vm_compute in (bv_unsigned r) in
      apply (s5a_cs2 r z ltac:(vm_compute; reflexivity)); unfold acallee_saved; lia
  end.
Lemma s5a_pres1 : forall (regs2 regs3 : bvmap 5 word) (r : bv 5),
  aregs_preserved regs2 regs3 -> acallee_saved (bv_unsigned r) -> getr regs3 r = getr regs2 r.
Proof.
intros regs2 regs3 r HP Hz. pose proof (HP (bv_unsigned r) Hz) as H.
rewrite Z_to_bv_bv_unsigned in H. exact H.
Qed.
(* a list whose extents are pairwise disjoint and positive repeats no entry *)
Lemma s5a_nodup_pw : forall (l : list (Z * Z)),
  pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) l) ->
  Forall (fun b : Z * Z => 0 <= snd b) l -> List.NoDup l.
Proof.
induction l as [|y l IH]; intros Hpw Hf; [constructor|].
cbn [map pairwise] in Hpw. destruct Hpw as [Hd Hpw].
inversion Hf as [|y0 l0 Hy Hl]; subst.
constructor; [|exact (IH Hpw Hl)].
intros Hin. rewrite Forall_forall in Hd.
pose proof (Hd _ (in_map (fun b : Z * Z => (fst b, req_size (snd b))) l y Hin)) as Hz.
unfold zdisjoint in Hz. cbn [fst snd] in Hz. pose proof (req_size_pos0 (snd y) Hy) as [Hp _]. lia.
Qed.
(* text after the copy and the NUL (fuzz_command's wc_text_bytes_loc, over list Z) *)
Lemma s5a_txt_bytes : forall (rd0 rd3 : reader) (tp src : Z) (D : list Z) (L : nat),
  (forall i, (i < L)%nat -> rd0 (src + Z.of_nat i) = Some (nth i D 0)) -> (L <= length D)%nat ->
  (forall i, 0 <= i < Z.of_nat L -> rd3 (tp + i) = rd0 (src + i)) ->
  rd3 (tp + Z.of_nat L) = Some 0 ->
  sa_zs rd3 tp (firstn L D ++ [0]).
Proof.
intros rd0 rd3 tp src D L HD HL HC HZ i Hi.
rewrite length_app, length_firstn in Hi. cbn [length] in Hi.
destruct (Nat.lt_ge_cases i L) as [Hlt | Hge].
- rewrite app_nth1 by (rewrite length_firstn; lia). rewrite s5a_nth_firstn by exact Hlt.
  rewrite (HC (Z.of_nat i)) by lia. exact (HD i ltac:(lia)).
- assert (Hi' : i = L) by lia. subst i.
  rewrite app_nth2 by (rewrite length_firstn; lia). rewrite length_firstn.
  replace (L - Nat.min L (length D))%nat with 0%nat by lia. cbn [nth]. exact HZ.
Qed.

(* ================================ the pieces of the walk that need the section ================================ *)
Section s5a_d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section s5a_f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Lemma s5a_slots_xfer : forall cx (rd rd' : reader) L, lt_slots cx rd L ->
  (forall o v, In (o, v) L -> forall j, 0 <= j < 8 -> rd' (x_s1 cx + o + j) = rd (x_s1 cx + o + j)) ->
  lt_slots cx rd' L.
Proof.
intros cx rd rd' L H HK o v Hin. rewrite (rdword_ext rd rd'); [exact (H o v Hin)|].
intros j Hj. exact (HK o v Hin j Hj).
Qed.
Lemma s5a_off_bound : forall cx c m (z : Z) o v, In (o, v) (LT_L cx c m ++ [(152, z)]) -> 0 <= o <= 184.
Proof.
intros cx c m z o v Hin. apply in_app_or in Hin as [Hin | Hin].
- unfold LT_L in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [Hq|Hin]; [injection Hq as <- _; lia|]). destruct Hin.
- destruct Hin as [Hq|[]]. injection Hq as <- _. lia.
Qed.

Section s5a_e.
Variable B : asyms.
Variable MT : ameter_ops.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(* ---- where the entry's stack lies ---- *)
Lemma s5a_sp : forall cx, lt_base B MT cx ->
  x_sp0 cx mod 16 = 0 /\ alloc_ceiling + STK_LLVMFuzzerTestOneInput <= x_sp0 cx <= 2 ^ 47 /\
  x_sp0 cx - 352 <= x_s1 cx <= x_sp0 cx - 320 /\ x_s1 cx mod 32 = 0 /\ (x_s1 cx - x_sp0 cx) mod 16 = 0 /\
  getr (x_regs cx) 3 = w64 (as_gp B) /\ getr (x_regs cx) 4 = w64 (as_tp B).
Proof.
intros cx HB. pose proof HB as (HPRE & _). pose proof HPRE as (_ & _ & _ & Hgp & Htp & Hstk & _).
pose proof Hstk as (Hal & _ & Hceil & Hslo & Hshi & H47 & _).
unfold x_s1, x_sp0, LT_FRAME, STK_LLVMFuzzerTestOneInput in *. set (sp := spZ (x_regs cx)) in *.
pose proof (Z.mod_pos_bound (sp - 320) 32 ltac:(lia)) as Hm.
pose proof (Z.div_mod (sp - 320) 32 ltac:(lia)) as Hd.
pose proof (Z.div_mod sp 16 ltac:(lia)) as Hd16.
split; [exact Hal|]. split; [lia|]. split; [lia|]. split.
- replace (sp - 320 - (sp - 320) mod 32) with (((sp - 320) / 32) * 32) by lia. apply Z_mod_mult.
- split; [|split; [exact Hgp | exact Htp]].
  replace (sp - 320 - (sp - 320) mod 32 - sp) with ((2 * ((sp - 320) / 32) - sp / 16) * 16) by lia.
  apply Z_mod_mult.
Qed.

(* ---- where the class-3 frame and its shadow lie ---- *)
Lemma s5a_fr : forall cx ly S (W : world SEGS) mem md k, lt_base B MT cx ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem md k ->
  In (LT_FCLS, x_fpos cx) (frames S) /\ frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx /\
  4096 <= x_fr cx /\ x_fr cx + 512 <= alloc_ceiling /\
  (x_fr cx + 512 <= 2147446784 \/ 17594333495296 <= x_fr cx) /\
  2147451392 <= x_sh cx /\ x_sh cx + 64 <= 17594333495296 /\
  (forall i, 0 <= i < 64 -> apresent (w_H W) mem (x_sh cx + i)).
Proof.
intros cx ly S W mem md k HB HJ.
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hfr0 & _).
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _).
pose proof Hly as (_ & _ & _ & _ & _ & HlyF & _).
assert (Hfs : frames S = [(LT_FCLS, x_fpos cx)]) by (rewrite Hfrs, Hfr0, app_nil_r; reflexivity).
assert (Hin : In (LT_FCLS, x_fpos cx) (frames S)) by (rewrite Hfs; left; reflexivity).
assert (HFA : frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx)
  by (unfold x_fr, frame_addr; rewrite HlyF; reflexivity).
destruct (frames_bounds SEGS B LAWS ly S W mem md LT_FCLS (x_fpos cx) HAR Hin) as (H4 & Hc & _).
destruct (al_frames _ _ LAWS ly S W mem md LT_FCLS (x_fpos cx) HAR Hin) as (_ & Happ & _ & HSp).
rewrite HFA in H4, Hc, HSp, Happ. change (fs_frame_bytes LT_FCLS) with 512 in Hc, HSp, Happ.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
change (512 / 8) with 64 in HSp.
pose proof ASAN_CEIL_range as [CR1 CR2]. unfold ASAN_CEIL in CR1, CR2.
assert (Esh : x_sh cx = 2147450880 + x_fr cx / 8) by reflexivity.
assert (Hlo : 512 <= x_fr cx / 8) by (apply Z.div_le_lower_bound; lia).
assert (Hhi : x_fr cx / 8 <= 17592186044416 - 64) by (apply Z.div_le_upper_bound; lia).
split; [exact Hin|]. split; [exact HFA|]. split; [lia|]. split; [lia|].
split; [lia|]. split; [lia|]. split; [lia|].
intros i Hi. unfold x_sh. exact (proj1 (HSp i Hi)).
Qed.

(* ---- a live block: where it lies and that it is addressable ---- *)
Lemma s5a_blk_app : forall ly S (W : world SEGS) mem md p n,
  AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) ->
  4096 <= p /\ p + req_size n <= alloc_ceiling /\ n <= req_size n /\ 0 <= n /\ 1 <= req_size n /\
  (p + req_size n <= 2147446784 \/ 17594333495296 <= p).
Proof.
intros ly S W mem md p n HAR Hin.
destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & H4 & Hc & Happ & _ & _ & Hm).
pose proof (req_size_pos n ltac:(lia)) as [Hr1 Hr2].
destruct Happ as (_ & Happ2). unfold kLowShadowBeg, kHighMemBeg in Happ2.
split; [exact H4|]. split; [exact Hc|]. split; [exact Hr2|]. split; [lia|]. split; [exact Hr1|].
destruct Happ2 as [Hl | [Hh _]]; [left; exact Hl | right; exact Hh].
Qed.
Lemma s5a_hblk_of : forall ly S (W : world SEGS) mem md a n,
  AR SEGS B ly S W mem md -> In (a, n) (ablocks B ly S) -> 0 < n -> lt_hblk B ly S (rdW W mem) a n.
Proof.
intros ly S W mem md a n HAR Hin Hn.
destruct (al_blocks _ _ LAWS ly S W mem md a n HAR Hin) as (H16 & H4096 & Hceil & _ & _ & _ & HM).
pose proof (req_size_pos n ltac:(lia)) as [_ Hreq]. pose proof asan_consts as (C1 & _).
split; [exact Hin|]. split; [exact H4096|]. split; [exact H16|].
split; [lia|]. split; [lia|].
split; [exact (amem_range_of_block SEGS B LAWS ly S W mem md a n a n HAR Hin ltac:(lia) ltac:(lia))|].
split; [exact (range_addressable_of_block SEGS B LAWS ly S W mem md a n a n HAR Hin ltac:(lia) ltac:(lia))|].
intros _. exact (shadow_hull_vis_of_block SEGS B LAWS ly S W mem md a n a n HAR Hin ltac:(lia) ltac:(lia) Hn).
Qed.
Lemma s5a_sep : forall ly S (W : world SEGS) mem md p n q r,
  AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) -> In (q, r) (ablocks B ly S) -> (p, n) <> (q, r) ->
  p + req_size n <= q \/ q + req_size r <= p.
Proof.
intros ly S W mem md p n q r HAR H1 H2 Hne.
pose proof (sep_blocks SEGS B LAWS ly S W mem md p n q r HAR H1 H2 Hne) as H.
unfold zdisjoint in H. cbn [fst snd] in H. exact H.
Qed.
Lemma s5a_blk_frame : forall ly S (W : world SEGS) mem md p n cid pos,
  AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) -> In (cid, pos) (frames S) ->
  p + req_size n <= frame_addr ly cid pos \/ frame_addr ly cid pos + fs_frame_bytes cid <= p.
Proof.
intros ly S W mem md p n cid pos HAR Hb Hf.
destruct (al_sep _ _ LAWS ly S W mem md HAR) as [HP _].
pose proof (pairwise_In zdisjoint _ (p, req_size n) (frame_addr ly cid pos, fs_frame_bytes cid) _ _ eq_refl HP
  (in_map (fun b : Z * Z => (fst b, req_size (snd b))) _ _ Hb)
  (in_map (fun g : Z * Z => (frame_addr ly (fst g) (snd g), fs_frame_bytes (fst g))) _ _ Hf)) as HD.
unfold zdisjoint in HD. cbn [fst snd] in HD. exact HD.
Qed.
Lemma s5a_blk_not_img : forall ly S (W : world SEGS) mem md p n a,
  AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) -> p <= a < p + req_size n -> ~ in_img SEGS a.
Proof.
intros ly S W mem md p n a HAR Hin Ha.
exact (proj2 (al_client_img _ _ LAWS ly S W mem md a HAR
  (or_introl (ex_intro _ p (ex_intro _ n (conj Hin Ha)))))).
Qed.
Lemma s5a_blocks_nodup : forall ly S (W : world SEGS) mem md,
  AR SEGS B ly S W mem md -> List.NoDup (ablocks B ly S).
Proof.
intros ly S W mem md HAR.
assert (HF : Forall (fun b : Z * Z => 0 <= snd b) (ablocks B ly S)).
{ apply Forall_forall. intros [p n] Hin.
  destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & _ & _ & _ & _ & _ & Hr). cbn [snd]. lia. }
destruct (ablocks B ly S) as [|y l] eqn:E; [constructor|].
assert (Hin0 : In y (ablocks B ly S)) by (rewrite E; left; reflexivity).
destruct y as [p0 n0].
destruct (al_blocks _ _ LAWS ly S W mem md p0 n0 HAR Hin0) as (_ & _ & _ & _ & _ & Hpw & _).
rewrite E in Hpw. rewrite ?E in HF. exact (s5a_nodup_pw _ Hpw HF).
Qed.

(* ---- a byte of a garr8 array through the reader ---- *)
Lemma s5a_garr8_view : forall (H : word -> bool) mem p l i,
  garr8 SEGS (mrestrict H mem) p l -> (i < length l)%nat ->
  aview SEGS H mem (p + Z.of_nat i) = Some (nth i l 0).
Proof.
intros H mem p l i Hg Hi. destruct (Hg i Hi) as [Hv Hr].
exact (aview_of_val_mem1 SEGS H mem _ _ Hv Hr).
Qed.

(* ---- an 8-byte chunk whose value is a literal ---- *)
Lemma s5a_chunk_lit : forall (W : world SEGS) mem E base off v,
  rdword (rdW W mem) (base + off) = Some v -> 0 <= v < 2 ^ 64 ->
  YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) base (YP09.mkChunk off (CVal 8 (SLit v))).
Proof.
intros W mem E base off v Hw Hr.
apply (chunk_ok_val SEGS E _ base off 8 (SLit v) v);
  [ cbn [sv_denot]; apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity
  | cbn; lia | cbn; lia |].
exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Hw).
Qed.

End s5a_e.
End s5a_f.
End s5a_d.

(* ================================= the piece ================================= *)
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
Variable snp_lo snp_hi : Z.
Variable snp_cr : list (Z * Z).
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis IMGS : s10_img.
Hypothesis BSYM : AF0m.SegBSyms B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis PRW : prog_rw SEGS B.
Hypothesis VOBJS : seg_val_objs.
Hypothesis SIGP : seg_sig_prog.
Hypothesis HPGS : forall a, inFP (ltoi_PG longlA) a ->
  Exists (in_zr a) (as_prog_static B) /\ in_img SEGS a.
Hypothesis HPG_RO : forall a, inFP (ltoi_PG longlA) a -> ~ in_roP SEGS RLO_A RHI_A a.
Hypothesis HPG_PTR : forall a p,
  ((exists i, (i < 5)%nat /\ a = wordsA + 8 * Z.of_nat i) \/
   (exists i, (i < pin_spec.CAT_N)%nat /\ a = pin_spec.row_addr catA i)) ->
  rdword (fun x => option_map (fun b : byte => bv_unsigned b) (seg_rom SEGS (Z_to_bv 64 x))) a = Some p ->
  p + 65536 <= longlA.
Hypothesis AMEMCPY : forall fx0 : YK11.FPState,
  @aintrin_realizes fx0 rc SEGS B OCpy (SIG SS___asan_memcpy).
Hypothesis AMEMSET : forall fx0 : YK11.FPState,
  @aintrin_realizes fx0 rc SEGS B OSet (SIG SS___asan_memset).
Hypothesis AFREE4 : forall fx0 : YK11.FPState, @afree04_rule fx0 rc SK SEGS B MT.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState,
  @RtPFSeg.seg_asnprintf_realizes fx0 rc SEGS B snp_lo snp_hi snp_cr
    (SIG SS___interceptor_trampoline_snprintf) gotwA guardA.
Hypothesis HSNP_LIT : forall x, In x LLVMFuzzerTestOneInput_c.LTOI_LITS ->
  snp_lo <= seg_litA_fz x /\ seg_litA_fz x + Z.of_nat (length x) + 1 <= gotwA.
Hypothesis HSNP_CR : Forall (fun r => snp_lo <= fst r /\ 0 <= snd r /\ fst r + snd r <= snp_hi) snp_cr.
Hypothesis HSNP_LO : 0 <= snp_lo.
Hypothesis HSNP_CEIL : snp_hi <= alloc_ceiling.
Hypothesis HSNP_FAKE : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> snp_hi <= ly_F ly.
Hypothesis HM_FILE : forall fx0 : YK11.FPState,
  @m_file_c.m_file_contract fx0 rc SK SEGS B (BASE + AF_m_file) STK_m_file RLO_A RHI_A seg_litA_fz
    wordsA rolesA catA gotwA guardA.
Hypothesis HPARSE_FILE : forall fx0 : YK11.FPState,
  @reac_segconf_parse_file_c.reac_segconf_parse_file_contract fx0 rc SK SEGS B
    (BASE + AF_reac_segconf_parse_file) STK_reac_segconf_parse_file RLO_A RHI_A seg_litA_rc catA gotwA guardA.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let BR := paj_branch (PI := PI).

Lemma s5_head : forall f, S5_LB_stmt B MT f -> LT_K850f8_stmt B MT f.
Proof using All.
intros f HLB cx ly S W regs mem md k acc c m t HBASE HFRM Hf HCORE Hc Hm Ht
  R10 R18 R19 R20 R21 R22 R24 R25 R26 R27 SLOTS HCM HCNT.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HCORE as ((HJ & Rsp & Rgp & Rtp & Rs0 & Rs1 & SAVED & HD0 & HD8 & HD16 & HFLW & S176 & FSH)
  & HIMG & HBL & HBUD).
pose proof (proj1 HJ) as HAR.
pose proof HJ as (JAR & Jly & Jsec & Jwle & Jio & Jfrs & Jnev & Jk & JK1 & JK2 & JK3 & JK4 & JK5
  & Jpres & Jstk & Jext & Jqt).
pose proof (s5a_sp B MT cx HBASE) as (Hal16 & Hsp0 & Hs1b & Hs1al & Ho16 & Hgp0 & Htp0).
pose proof (s5a_fr B MT cx ly S W mem md k HBASE HJ) as (Hfin & HFA & HF4 & HFc & HFapp & Hshlo & Hshhi & HSHpres).
assert (WS : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity.
rewrite WS in Hsp0.
pose proof ASAN_CEIL_range as [CR1 CR2]. unfold ASAN_CEIL in CR1, CR2.
pose proof HBASE as (HPRE & HSTP & HRO & HIM & H10 & H11 & Hpn & Hlen & HG8 & Hfr0 & HGI & HEVM & HLIVE & HMO).
pose proof HPRE as (HAR0 & Hra0 & Hra40 & Hgpx & Htpx & Hstkd & Hpres0 & Hch0 & HQT0).
(* the three blocks *)
pose proof Ht as (HtIn & Ht4 & Ht16 & HtAddr).
pose proof Hc as (HcIn & Hc4 & _).
pose proof Hm as (HmIn & Hm4 & _).
set (nn := seg_spec.seg_txt_n (x_pl cx) f) in *.
assert (Hnn0 : 0 <= nn) by (unfold nn, seg_spec.seg_txt_n; lia).
assert (Htn : x_tn cx f = nn + 1) by reflexivity.
assert (Hreqt : req_size (x_tn cx f) = nn + 1).
{ unfold req_size. rewrite Htn. replace (nn + 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
destruct (s5a_blk_app B ly S W mem md t (x_tn cx f) HAR HtIn) as (_ & Htc & _ & _ & _ & Htapp).
destruct (s5a_blk_app B ly S W mem md c seg_spec.SEG_C_SIZE HAR HcIn) as (_ & Hcc & _ & _ & _ & Hcapp).
destruct (s5a_blk_app B ly S W mem md m seg_spec.SEG_M_SIZE HAR HmIn) as (_ & Hmc & _ & _ & _ & Hmapp).
assert (HreqC : req_size seg_spec.SEG_C_SIZE = seg_spec.SEG_C_SIZE) by reflexivity.
assert (HreqM : req_size seg_spec.SEG_M_SIZE = seg_spec.SEG_M_SIZE) by reflexivity.
rewrite Hreqt in Htc, Htapp. rewrite HreqC in Hcc, Hcapp. rewrite HreqM in Hmc, Hmapp.
pose proof (s5a_blk_frame B ly S W mem md t (x_tn cx f) LT_FCLS (x_fpos cx) HAR HtIn Hfin) as Dtf.
rewrite Hreqt, HFA in Dtf. change (fs_frame_bytes LT_FCLS) with 512 in Dtf.
(* t is a block made since the entry, and the three are different entries *)
pose proof (s5a_blocks_nodup B ly S W mem md HAR) as HND.
pose proof (Permutation_NoDup HBL HND) as HND2. cbn [app] in HND2.
apply NoDup_cons_iff in HND2 as [HtNotIn HND3].
assert (HtNot : ~ In (t, x_tn cx f) (x_bl0 B cx)) by (intros Hq; apply HtNotIn; right; right; exact Hq).
assert (Htm : (t, x_tn cx f) <> (m, seg_spec.SEG_M_SIZE))
  by (intros Hq; apply HtNotIn; left; exact (eq_sym Hq)).
assert (Htc' : (t, x_tn cx f) <> (c, seg_spec.SEG_C_SIZE))
  by (intros Hq; apply HtNotIn; right; left; exact (eq_sym Hq)).
pose proof (s5a_sep B ly S W mem md t (x_tn cx f) m seg_spec.SEG_M_SIZE HAR HtIn HmIn Htm) as Dtm.
pose proof (s5a_sep B ly S W mem md t (x_tn cx f) c seg_spec.SEG_C_SIZE HAR HtIn HcIn Htc') as Dtc.
rewrite Hreqt in Dtm, Dtc. rewrite HreqM in Dtm. rewrite HreqC in Dtc.
assert (ECS : seg_spec.SEG_C_SIZE = 16616) by reflexivity.
assert (EMS : seg_spec.SEG_M_SIZE = 9236) by reflexivity.
assert (HES : ESTACK = 4096) by reflexivity.
(* the eight range disjunctions become implications and are then cleared: `lia` case-splits every
   disjunction of the context, and eight of them is 256 linear problems per call (walk-common pitfall 2) *)
assert (DT_SH : forall a, t <= a < t + (nn + 1) -> ~ (x_sh cx <= a < x_sh cx + 64))
  by (intros a Ha; clear - Ha Htapp Hshlo Hshhi; lia).
assert (DT_BAND : forall a, t <= a < t + (nn + 1) ->
    ~ (2147450880 <= a < 2147450880 + 17592186044416))
  by (intros a Ha; clear - Ha Htapp; lia).
assert (DC_SH : forall a, c <= a < c + seg_spec.SEG_C_SIZE -> ~ (x_sh cx <= a < x_sh cx + 64))
  by (intros a Ha; clear - Ha Hcapp Hshlo Hshhi; lia).
assert (DM_SH : forall a, m <= a < m + seg_spec.SEG_M_SIZE -> ~ (x_sh cx <= a < x_sh cx + 64))
  by (intros a Ha; clear - Ha Hmapp Hshlo Hshhi; lia).
assert (DF_SH : forall a, x_fr cx <= a < x_fr cx + 512 -> ~ (x_sh cx <= a < x_sh cx + 64))
  by (intros a Ha; clear - Ha HFapp Hshlo Hshhi; lia).
assert (DC_T : forall a, c <= a < c + seg_spec.SEG_C_SIZE -> ~ (t <= a < t + (nn + 1)))
  by (intros a Ha; clear - Ha Dtc; lia).
assert (DM_T : forall a, m <= a < m + seg_spec.SEG_M_SIZE -> ~ (t <= a < t + (nn + 1)))
  by (intros a Ha; clear - Ha Dtm; lia).
assert (DF_T : forall a, x_fr cx <= a < x_fr cx + 512 -> ~ (t <= a < t + (nn + 1)))
  by (intros a Ha; clear - Ha Dtf; lia).
clear Htapp Hcapp Hmapp HFapp Dtm Dtc Dtf.
(* ---- the turn's text against the turn's tail and the payload ---- *)
destruct (s5_txt_firstn (x_pl cx) f Hf) as (Hfirst & Hle1 & Hle2).
pose proof (s5_tail_sfx (x_pl cx) f) as Hsfx.
pose proof (s5_sfx_len _ _ Hsfx) as Hsfxlen.
assert (Hinlen : length (seg_spec.seg_in (x_pl cx)) = length (x_pl cx))
  by (unfold seg_spec.seg_in, seg_spec.zs; apply length_map).
assert (Hnn_nat : Z.to_nat nn = length (seg_spec.seg_txt (x_pl cx) f))
  by (unfold nn, seg_spec.seg_txt_n; rewrite Nat2Z.id; reflexivity).
assert (Hnn_tail : (Z.to_nat nn <= length (seg_spec.seg_turn_tail (x_pl cx) f))%nat) by lia.
assert (Htail_pl : (length (seg_spec.seg_turn_tail (x_pl cx) f) <= length (x_pl cx))%nat) by lia.
assert (Hnn_pl : nn <= x_n cx) by (rewrite Hlen; lia).
assert (Hpay : 0 < nn -> In (x_p cx, x_n cx) (ablocks B (x_ly cx) (x_S cx))).
{ intros Hpos. destruct Hpn as [[Hz _] | [_ Hq]]; [exfalso; clear - Hz Hpos Hnn_pl; lia | exact Hq]. }
clear Hpn.
(* the bytes of the turn's tail, read at the state's memory *)
assert (HPAY : forall i, (i < Z.to_nat nn)%nat ->
   rdW W mem (seg_spec.seg_turn_at (x_pl cx) (x_p cx) f + Z.of_nat i)
   = Some (nth i (seg_spec.seg_turn_tail (x_pl cx) f) 0)).
{ intros i Hi.
  assert (Hnpos : 0 < nn) by lia.
  assert (Hp0 : In (x_p cx, x_n cx) (ablocks B (x_ly cx) (x_S cx))) by (apply Hpay; lia).
  assert (HpIn : In (x_p cx, x_n cx) (ablocks B ly S))
    by exact (Permutation_in _ (Permutation_sym HBL) (in_or_app _ _ _ (or_intror Hp0))).
  pose proof (req_size_pos (x_n cx) ltac:(lia)) as [_ Hrp].
  assert (Hrp' : req_size (x_n cx) = x_n cx).
  { unfold req_size. replace (x_n cx =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
  set (j := (length (x_pl cx) - length (seg_spec.seg_turn_tail (x_pl cx) f) + i)%nat).
  assert (Hj : (j < length (x_pl cx))%nat) by (unfold j; lia).
  assert (Heq : seg_spec.seg_turn_at (x_pl cx) (x_p cx) f + Z.of_nat i = x_p cx + Z.of_nat j)
    by (unfold seg_spec.seg_turn_at, j; lia).
  rewrite Heq.
  assert (Hnfp : ~ inFP (ltoi_PG longlA) (x_p cx + Z.of_nat j)).
  { intros HFP.
    exact (s5a_blk_not_img B (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) (x_p cx) (x_n cx)
      (x_p cx + Z.of_nat j) HAR0 Hp0 ltac:(rewrite Hrp'; lia) (proj2 (HPGS _ HFP))). }
  rewrite (JK2 (x_p cx) (x_n cx) (Z.of_nat j) Hp0 HpIn ltac:(rewrite Hrp'; lia) Hnfp).
  rewrite (s5a_garr8_view (w_H (x_W cx)) (x_mem cx) (x_p cx) _ j HG8 ltac:(rewrite length_map; lia)).
  f_equal. rewrite (s5_sfx_nth _ _ Hsfx i ltac:(lia)). unfold j. rewrite <- Hinlen. reflexivity. }
(* every `lia` below runs with `Unset Lia Cache`, so it re-solves from scratch; the hypotheses it no longer
   needs go now, above all the `sa_addr`s, whose `amem_range` is a disjunction lia case-splits *)
try clear Ht.
try clear Hc.
try clear Hm.
try clear HtAddr.
try clear Ht16.
try clear HSTP.
try clear HRO.
try clear HIM.
try clear HG8.
try clear HGI.
try clear HEVM.
try clear HLIVE.
try clear HMO.
try clear HPRE.
try clear Hra0.
try clear Hra40.
try clear Hgpx.
try clear Htpx.
try clear Hpres0.
try clear Hch0.
try clear HQT0.
try clear Hstkd.
try clear H10.
try clear H11.
try clear Hfr0.
try clear JAR.
try clear Jly.
try clear Jsec.
try clear Jwle.
try clear Jio.
try clear Jfrs.
try clear Jnev.
try clear Jk.
try clear JK1.
try clear JK2.
try clear JK3.
try clear JK4.
try clear JK5.
try clear Jpres.
try clear Jstk.
try clear Jext.
try clear Jqt.
try clear HND.
try clear HND3.
try clear HtNotIn.
try clear Hsfx.
try clear Hsfxlen.
try clear Hinlen.
try clear Hal16.
try clear Hs1al.
try clear HAR0.

(* =============== the tail: from 0x85114 to the cut S5_LB at 0x85148 =============== *)
assert (TAIL : forall (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model),
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx)
    (x_mem cx) (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem2 md2 k ->
  getr regs2 2 = getr regs 2 -> getr regs2 3 = getr regs 3 -> getr regs2 4 = getr regs 4 ->
  getr regs2 8 = getr regs 8 -> getr regs2 9 = getr regs 9 ->
  getr regs2 18 = getr regs 18 -> getr regs2 19 = getr regs 19 -> getr regs2 20 = getr regs 20 ->
  getr regs2 21 = getr regs 21 -> getr regs2 22 = getr regs 22 -> getr regs2 23 = w64 t ->
  getr regs2 24 = getr regs 24 -> getr regs2 25 = getr regs 25 -> getr regs2 26 = getr regs 26 ->
  getr regs2 27 = getr regs 27 ->
  (forall i, 0 <= i < nn ->
     rdW W mem2 (t + i) = rdW W mem (seg_spec.seg_turn_at (x_pl cx) (x_p cx) f + i)) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (t <= a < t + (nn + 1)) -> ~ (x_s1 cx - 4096 <= a < x_s1 cx) ->
     rdW W mem2 a = rdW W mem a) ->
  SRr SEGS W (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + 0x3e0)) mem2 (seg_rom SEGS)) md2) (lt_post B MT cx)).
{ intros regs2 mem2 md2 HJ2 Q2 Q3 Q4 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 Q24 Q25 Q26 Q27 HCPY HKEEP.
  pose proof (proj1 HJ2) as HAR2.
  destruct (al_blocks _ _ LAWS ly S W mem2 md2 t (x_tn cx f) HAR2 HtIn) as (_ & _ & _ & _ & Htpres & _ & _).
  rewrite Hreqt in Htpres.
  assert (S176' : rdword (rdW W mem2) (x_s1 cx + 176) = Some SHADOW_OFF).
  { apply (s5a_rdword_xfer (rdW W mem) (rdW W mem2)); [|exact S176].
    intros j Hj. apply HKEEP; lia. }
  (* ---- the seed at 0x85114 ---- *)
  assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs2 [Z_to_bv 64 (t + nn)]))) by apply Eimg_env.
  assert (EE : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r ->
      ew (Eimg (Ereg regs2 [Z_to_bv 64 (t + nn)])) n0 = getr regs2 r)
    by (intros n0 r Hr; apply ew_Eimg_Ereg_nat; exact Hr).
  assert (EX : forall j, (j < 1)%nat ->
      ew (Eimg (Ereg regs2 [Z_to_bv 64 (t + nn)])) (32 + j) = nth j [Z_to_bv 64 (t + nn)] (Z_to_bv 64 0))
    by (intros j Hj; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  pose proof (EX 0%nat ltac:(lia)) as E32. cbn [Nat.add nth] in E32.
  assert (U32 : bv_unsigned (ew (Eimg (Ereg regs2 [Z_to_bv 64 (t + nn)])) 32) = t + nn)
    by (rewrite E32; apply unsigned_lit_small; lia).
  assert (U9 : bv_unsigned (ew (Eimg (Ereg regs2 [Z_to_bv 64 (t + nn)])) 9) = x_s1 cx)
    by (rewrite (EE 9%nat 9%bv eq_refl), Q9, Rs1; apply unsigned_lit_small; lia).
  assert (U20 : bv_unsigned (ew (Eimg (Ereg regs2 [Z_to_bv 64 (t + nn)])) 20) = nn)
    by (rewrite (EE 20%nat 20%bv eq_refl), Q20, R20; apply unsigned_lit_small; lia).
  assert (U23 : bv_unsigned (ew (Eimg (Ereg regs2 [Z_to_bv 64 (t + nn)])) 23) = t)
    by (rewrite (EE 23%nat 23%bv eq_refl), Q23; apply unsigned_lit_small; lia).
  assert (HS : st_ok_pi SEGS VAL (Eimg (Ereg regs2 [Z_to_bv 64 (t + nn)])) s5a_ssB
      (restrict (w_H W) (mkst regs2 (Z_to_bv 64 (BASE + 0x3e0)) mem2 (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold s5a_ssB. apply pa_entry_st_ok_full.
    - apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - unfold s5a_rtxt, s5a_rslot.
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      + rewrite U32. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. apply (apresent_writable SEGS). exact (proj1 (Htpres (t + nn + o) ltac:(lia))).
      + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        exact (s5a_chunk_lit W mem2 _ (x_s1 cx) 176 SHADOW_OFF S176' ltac:(unfold SHADOW_OFF; lia)).
    - apply pairwise_disjoint_of_extents. unfold extent_of_region, s5a_rtxt, s5a_rslot.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
      rewrite U9, U32. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      repeat split; lia.
    - split; [|split; [exact I|]].
      + cbn [ss_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite U32. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
        repeat match goal with |- _ /\ _ => split end; first [exact I | lia | reflexivity].
      + cbn [ss_facts f_alias alias_ok]. split; [|exact I].
        apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U23, U20, U32, !Z.add_0_r.
        rewrite (zcanon_small t) by lia. rewrite (zcanon_small nn) by lia. reflexivity. }
  assert (SHOK : sh_ok SEGS s5a_Bx s5a_SH (Eimg (Ereg regs2 [Z_to_bv 64 (t + nn)]))
      (mrestrict (w_H W) mem2)).
  { unfold sh_ok, s5a_SH. constructor; [|constructor].
    apply (shent_ok_of_range SEGS (w_H W) mem2 _ s5a_Bx 32 (t + nn) 1 (t + nn) 0 1).
    - exact (range_addressable_of_block SEGS B LAWS ly S W mem2 md2 t (x_tn cx f) (t + nn) 1 HAR2 HtIn
        ltac:(lia) ltac:(rewrite Hreqt; lia)).
    - unfold s5a_Bx. apply U_lit. unfold SHADOW_OFF. lia.
    - apply U_atom; [exact E32 | lia].
    - lia.
    - lia.
    - intros x Hx. change (Z.min 0 1) with 0 in Hx. change (Z.max 0 1) with 1 in Hx.
      unfold SHADOW_OFF. exact (DT_BAND x ltac:(lia)). }
  remember (Eimg (Ereg regs2 [Z_to_bv 64 (t + nn)])) as EB eqn:HEB. clear HEB.
  (* ---- 0x85114 .. 0x8512c: a0 = t + n, check 7 (a token), text[n] = 0 ---- *)
  paj_run_to_tok RUNTO HS HJ2 SHOK s5a_span 0x3fc.
  { lazymatch goal with |- awr_ok ?sg ?bb ?E0 ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok sg bb E0 rs' stk spx fp b0 bc fr lyx own) end.
    eapply awr_ok_cons_gen; [reflexivity | exact U32 | | apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]].
    intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
    right; right; left. exists t, (x_tn cx f).
    split; [exact HtIn | split; [exact HtNot | rewrite Hreqt; lia]]. }
  lazymatch goal with |- SRr _ _ (mkCfg _ ?dd) _ => set (md3 := dd) in *; clearbody md3 end.
  rename ms into msB.
  (* what the token run changed: the one byte text[n] *)
  assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (t + nn <= a < t + nn + 1) ->
      rdW W (ms_mem msB) a = rdW W mem2 a).
  { intros a Ha Hna.
    apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a0 => t + nn <= a0 < t + nn + 1) HFr);
      [|exact Ha | exact Hna].
    intros b wlo whi a' Hin Hrr. vm_compute in Hin.
    repeat (destruct Hin as [Hq | Hin];
      [ injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U32, ?U9 in Hrr; cbv beta; lia |]).
    destruct Hin. }
  (* the NUL byte that `sb zero,0(a0)` wrote *)
  assert (HZ : rdW W (ms_mem msB) (t + nn) = Some 0).
  { pose proof (st_ok_mem_ok SEGS _ _ _ HS) as HM. cbn [abs_ss setpc ss_mem restrict ms_mem] in HM.
    pose proof (mem_ok_region SEGS _ _ _ _ HM (in_eq _ _)) as HR3.
    pose proof (region_ok_chunk SEGS _ _ _ _ HR3 (in_eq _ _)) as HCk.
    cbn [YP09.r_base YP09.r_chunks base_val] in HCk.
    lazymatch type of HCk with YP09.chunk_ok _ _ _ ?bb _ =>
      assert (HU : bb = t + nn) by (cbn [ew ewset Nat.eqb]; exact U32) end.
    rewrite HU in HCk.
    pose proof (val_of_chunk_ok SEGS _ _ _ 0 1 (SLit 0) 0 HCk eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as HV.
    rewrite Z.add_0_r in HV. exact (aview_of_val_mem1 SEGS (w_H W) (ms_mem msB) _ _ HV ltac:(lia)). }
  clear HF HFr HG.
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18.
  prreg HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20. prreg HS (21%bv : bv 5) P21.
  prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) P24.
  prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27.
  rewrite (EE 2%nat 2%bv eq_refl) in P2. rewrite (EE 3%nat 3%bv eq_refl) in P3.
  rewrite (EE 4%nat 4%bv eq_refl) in P4. rewrite (EE 8%nat 8%bv eq_refl) in P8.
  rewrite (EE 9%nat 9%bv eq_refl) in P9. rewrite (EE 18%nat 18%bv eq_refl) in P18.
  rewrite (EE 19%nat 19%bv eq_refl) in P19. rewrite (EE 20%nat 20%bv eq_refl) in P20.
  rewrite (EE 21%nat 21%bv eq_refl) in P21. rewrite (EE 22%nat 22%bv eq_refl) in P22.
  rewrite (EE 23%nat 23%bv eq_refl) in P23. rewrite (EE 24%nat 24%bv eq_refl) in P24.
  rewrite (EE 25%nat 25%bv eq_refl) in P25. rewrite (EE 26%nat 26%bv eq_refl) in P26.
  rewrite (EE 27%nat 27%bv eq_refl) in P27.
  clear HS SHOK.
  (* ---- the re-seat for the PLAIN runner at 0x85130 ---- *)
  pose proof (s5a_fr B MT cx ly S W (ms_mem msB) md3 k HBASE HJ2)
    as (_ & _ & _ & _ & _ & _ & _ & HSHpresB).
  assert (HEI2 : img_env VAL A_LIM (Eimg (Ereg (ms_regs msB) []))) by apply Eimg_env.
  assert (EE2 : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r ->
      ew (Eimg (Ereg (ms_regs msB) [])) n0 = getr (ms_regs msB) r)
    by (intros n0 r Hr; apply ew_Eimg_Ereg_nat; exact Hr).
  assert (U21b : bv_unsigned (ew (Eimg (Ereg (ms_regs msB) [])) 21) = x_sh cx)
    by (rewrite (EE2 21%nat 21%bv eq_refl), P21, Q21, R21; apply unsigned_lit_small; lia).
  assert (U26b : bv_unsigned (ew (Eimg (Ereg (ms_regs msB) [])) 26) = zcanon (seg_spec.seg_lb (x_pl cx) f))
    by (rewrite (EE2 26%nat 26%bv eq_refl), P26, Q26, R26; apply unsigned_lit).
  assert (HS2 : st_ok_pi SEGS VAL (Eimg (Ereg (ms_regs msB) [])) s5a_ssC
      (restrict (w_H W) (mkst (ms_regs msB) (Z_to_bv 64 (BASE + 0x3fc)) (ms_mem msB) (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold s5a_ssC. apply pa_entry_st_ok_full.
    - apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - unfold s5a_rsh. apply Forall_cons; [|apply Forall_nil]; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U21b. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). exact (HSHpresB o ltac:(lia)).
    - cbn [pairwise_disjoint all_disjoint]. tauto.
    - unfold facts_ok. cbn [ss_facts f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. tauto. }
  remember (Eimg (Ereg (ms_regs msB) [])) as EC eqn:HEC. clear HEC.
  (* ---- 0x85130 .. 0x85144: the five shadow stores and `slli a0,s10,0x38` ---- *)
  paj_run_to_sh RUNTOP HS2 HJ2 0x414.
  { lazymatch goal with |- awr_ok ?sg ?bb ?E0 ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok sg bb E0 rs' stk spx fp b0 bc fr lyx own) end.
    eapply awr_ok_cons_gen; [reflexivity | exact U21b | | apply awr_ok_nil].
    intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
    right; right; right; left. exists LT_FCLS, (x_fpos cx). split; [left; reflexivity|].
    right. rewrite HFA. unfold in_zr. cbn [fst snd].
    change (fs_frame_bytes LT_FCLS / 8) with 64. change (shadow_addr (x_fr cx)) with (x_sh cx). lia. }
  rename ms into msC.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?dd) _ => set (md4 := dd) in *; clearbody md4 end.
  pose proof (proj1 HJ2) as HARC.
  (* the five shadow bytes the plain run wrote, and what it kept *)
  lazymatch type of HS2 with st_ok_pi _ _ _ ?ssB _ =>
    let r0 := eval vm_compute in (nth 0 (ss_mem ssB) (YP09.mkRegion None 0 0 0 0 [])) in
    pose proof (st_ok_pi_region_nth _ _ _ 0%nat r0 HS2 ltac:(vm_compute; reflexivity)) as RSH end.
  destruct RSH as (_ & _ & _ & CSH). cbn [YP09.r_base YP09.r_chunks base_val] in CSH.
  rewrite U21b in CSH.
  pose proof (s10_zs_ok _ (w_H W) (ms_mem msC) (x_sh cx) _ [0; 0; 0; 0; 0] 12 CSH
    ltac:(vm_compute; reflexivity)) as HZS5.
  assert (HZS5' : forall j, (j < 5)%nat -> rdW W (ms_mem msC) (x_sh cx + 12 + Z.of_nat j) = Some 0).
  { intros j Hj. rewrite (HZS5 j ltac:(cbn [length]; lia)).
    destruct j as [|[|[|[|[|j]]]]]; cbn [nth]; first [reflexivity | cbn in Hj; lia]. }
  assert (KC : forall a, 0 <= a < 2 ^ 64 -> ~ (x_sh cx + 12 <= a < x_sh cx + 17) ->
      rdW W (ms_mem msC) a = rdW W (ms_mem msB) a).
  { intros a Ha Hna.
    apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a0 => x_sh cx + 12 <= a0 < x_sh cx + 17) HFr);
      [|exact Ha | exact Hna].
    intros b wlo whi a' Hin Hrr. vm_compute in Hin.
    repeat (destruct Hin as [Hq | Hin];
      [ injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U21b in Hrr; cbv beta; lia |]).
    destruct Hin. }
  assert (KALL : forall a, 0 <= a < 2 ^ 64 -> ~ (t <= a < t + (nn + 1)) ->
      ~ (x_s1 cx - 4096 <= a < x_s1 cx) -> ~ (x_sh cx + 12 <= a < x_sh cx + 17) ->
      rdW W (ms_mem msC) a = rdW W mem a).
  { intros a Ha H1 H2 H3. rewrite (KC a Ha H3), (KB a Ha ltac:(lia)). exact (HKEEP a Ha H1 H2). }
  assert (KFR : forall a, x_fr cx <= a < x_fr cx + 512 -> rdW W (ms_mem msC) a = rdW W mem a).
  { intros a Ha. apply KALL; [lia | exact (DF_T a Ha) | lia | intros Hq; exact (DF_SH a Ha ltac:(lia))]. }
  assert (KST : forall a, x_s1 cx <= a < x_sp0 cx -> rdW W (ms_mem msC) a = rdW W mem a)
    by (intros a Ha; apply KALL; lia).
  assert (KCB : forall i, 0 <= i < seg_spec.SEG_C_SIZE -> rdW W (ms_mem msC) (c + i) = rdW W mem (c + i)).
  { intros i Hi. apply KALL;
      [lia | exact (DC_T (c + i) ltac:(lia)) | lia | intros Hq; exact (DC_SH (c + i) ltac:(lia) ltac:(lia))]. }
  assert (KMB : forall i, 0 <= i < seg_spec.SEG_M_SIZE -> rdW W (ms_mem msC) (m + i) = rdW W mem (m + i)).
  { intros i Hi. apply KALL;
      [lia | exact (DM_T (m + i) ltac:(lia)) | lia | intros Hq; exact (DM_SH (m + i) ltac:(lia) ltac:(lia))]. }
  assert (KSH : forall j, (j < 36)%nat -> ~ (12 <= j < 17)%nat ->
      rdW W (ms_mem msC) (x_sh cx + Z.of_nat j) = rdW W mem (x_sh cx + Z.of_nat j)).
  { intros j Hj Hnj.
    assert (HjZ : 0 <= Z.of_nat j < 36) by (clear - Hj; lia).
    assert (HnjZ : ~ (12 <= Z.of_nat j < 17)) by (clear - Hnj; lia).
    apply KALL; [lia | | lia | lia].
    intros Hq. exact (DT_SH (x_sh cx + Z.of_nat j) Hq ltac:(lia)). }
  assert (KTXT : forall i, 0 <= i <= nn -> rdW W (ms_mem msC) (t + i) = rdW W (ms_mem msB) (t + i)).
  { intros i Hi. apply KC; [lia | intros Hq; apply (DT_SH (t + i) ltac:(lia)); lia]. }
  assert (KIMG : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) ->
      ~ (as_errno B <= a < as_errno B + 4) -> rdW W (ms_mem msC) a = rdW W mem a).
  { intros a Ha _ _. pose proof (pa_img_range a Ha) as HIR. unfold kImgEnd in HIR.
    apply KALL; [lia | | lia | lia].
    intros Hq. exact (s5a_blk_not_img B ly S W (ms_mem msC) md4 t (x_tn cx f) a HARC HtIn
      ltac:(rewrite Hreqt; lia) Ha). }
  (* the registers at 0x85148 *)
  pmkst HS2.
  prreg HS2 (2%bv : bv 5) G2. prreg HS2 (3%bv : bv 5) G3. prreg HS2 (4%bv : bv 5) G4.
  prreg HS2 (8%bv : bv 5) G8. prreg HS2 (9%bv : bv 5) G9. prreg HS2 (10%bv : bv 5) G10.
  prreg HS2 (18%bv : bv 5) G18. prreg HS2 (19%bv : bv 5) G19. prreg HS2 (20%bv : bv 5) G20.
  prreg HS2 (21%bv : bv 5) G21. prreg HS2 (22%bv : bv 5) G22. prreg HS2 (23%bv : bv 5) G23.
  prreg HS2 (24%bv : bv 5) G24. prreg HS2 (25%bv : bv 5) G25. prreg HS2 (26%bv : bv 5) G26.
  prreg HS2 (27%bv : bv 5) G27.
  rewrite (EE2 2%nat 2%bv eq_refl), P2, Q2, Rsp in G2.
  rewrite (EE2 3%nat 3%bv eq_refl), P3, Q3, Rgp in G3.
  rewrite (EE2 4%nat 4%bv eq_refl), P4, Q4, Rtp in G4.
  rewrite (EE2 8%nat 8%bv eq_refl), P8, Q8, Rs0 in G8.
  rewrite (EE2 9%nat 9%bv eq_refl), P9, Q9, Rs1 in G9.
  rewrite (EE2 18%nat 18%bv eq_refl), P18, Q18, R18 in G18.
  rewrite (EE2 19%nat 19%bv eq_refl), P19, Q19, R19 in G19.
  rewrite (EE2 20%nat 20%bv eq_refl), P20, Q20, R20 in G20.
  rewrite (EE2 21%nat 21%bv eq_refl), P21, Q21, R21 in G21.
  rewrite (EE2 22%nat 22%bv eq_refl), P22, Q22, R22 in G22.
  rewrite (EE2 23%nat 23%bv eq_refl), P23, Q23 in G23.
  rewrite (EE2 24%nat 24%bv eq_refl), P24, Q24, R24 in G24.
  rewrite (EE2 25%nat 25%bv eq_refl), P25, Q25, R25 in G25.
  rewrite (EE2 26%nat 26%bv eq_refl), P26, Q26, R26 in G26.
  rewrite (EE2 27%nat 27%bv eq_refl), P27, Q27, R27 in G27.
  assert (G10' : getr (ms_regs msC) 10 = w64 (Z.shiftl (seg_spec.seg_lb (x_pl cx) f) 56)).
  { rewrite G10, (EE2 26%nat 26%bv eq_refl), P26, Q26, R26. unfold w64. apply s5a_sll56. }
  (* ---- the frame part at the cut, with the label's shadow now usable ---- *)
  assert (FRM' : lt_frame B cx ly S W (ms_regs msC) (ms_mem msC) md4 k LFO_L).
  { split; [exact HJ2|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|].
    split; [exact G8|]. split; [exact G9|].
    split.
    { intros i r Hi. apply (s5a_rdword_xfer (rdW W mem) (rdW W (ms_mem msC))); [|exact (SAVED i r Hi)].
      assert (Hi13 : (i < length LT_SAVED)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
      cbn [length LT_SAVED] in Hi13. intros j Hj. apply KST; lia. }
    split; [apply (s5a_rdword_xfer (rdW W mem) (rdW W (ms_mem msC)));
            [intros j Hj; apply KFR; lia | exact HD0]|].
    split; [apply (s5a_rdword_xfer (rdW W mem) (rdW W (ms_mem msC)));
            [intros j Hj; apply KFR; lia | exact HD8]|].
    split; [apply (s5a_rdword_xfer (rdW W mem) (rdW W (ms_mem msC)));
            [intros j Hj; apply KFR; lia | exact HD16]|].
    split; [apply (s5a_rdword_xfer (rdW W mem) (rdW W (ms_mem msC)));
            [intros j Hj; apply KFR; unfold LT_FLAGW; lia | exact HFLW]|].
    split; [apply (s5a_rdword_xfer (rdW W mem) (rdW W (ms_mem msC)));
            [intros j Hj; apply KST; lia | exact S176]|].
    intros i Hi. rewrite lt_fsh_len in Hi.
    destruct (Nat.lt_ge_cases i 12) as [Hlt|Hge].
    - rewrite (KSH i Hi ltac:(clear - Hlt; lia)).
      rewrite (s5a_fsh_same i Hi ltac:(clear - Hlt; lia)).
      exact (FSH i ltac:(rewrite lt_fsh_len; exact Hi)).
    - destruct (Nat.lt_ge_cases i 17) as [Hlt2|Hge2].
      + rewrite (s5a_fsh_lab i ltac:(clear - Hge Hlt2; lia)).
        replace (x_sh cx + Z.of_nat i) with (x_sh cx + 12 + Z.of_nat (i - 12)%nat)
          by (clear - Hge Hlt2; lia).
        exact (HZS5' (i - 12)%nat ltac:(clear - Hge Hlt2; lia)).
      + rewrite (KSH i Hi ltac:(clear - Hge2; lia)).
        rewrite (s5a_fsh_same i Hi ltac:(clear - Hge2; lia)).
        exact (FSH i ltac:(rewrite lt_fsh_len; exact Hi)). }
  assert (IMG' : lt_img B cx (rdW W (ms_mem msC)))
    by exact (s10_lt_img_kept B IMGS BSYM cx W (ms_mem msC) (rdW W mem) HARC KIMG HIMG).
  assert (CM' : lt_cm (rdW W (ms_mem msC)) c m (x_st cx f))
    by exact (s5a_cm_xfer (rdW W mem) (rdW W (ms_mem msC)) c m (x_st cx f) KCB KMB HCM).
  (* ---- the text block holds the turn's text as a C string ---- *)
  assert (STR' : sa_str (rdW W (ms_mem msC)) t (s5_txt (x_pl cx) f)).
  { split.
    - split.
      + assert (HQ : sa_zs (rdW W (ms_mem msC)) t
            (firstn (length (seg_spec.seg_txt (x_pl cx) f)) (seg_spec.seg_turn_tail (x_pl cx) f) ++ [0])).
        { apply (s5a_txt_bytes (rdW W mem) (rdW W (ms_mem msC)) t
            (seg_spec.seg_turn_at (x_pl cx) (x_p cx) f) (seg_spec.seg_turn_tail (x_pl cx) f)
            (length (seg_spec.seg_txt (x_pl cx) f))).
          - intros i Hi. apply HPAY. lia.
          - lia.
          - intros i Hi. rewrite (KTXT i ltac:(lia)), (KB (t + i) ltac:(lia) ltac:(lia)).
            apply HCPY. lia.
          - replace (t + Z.of_nat (length (seg_spec.seg_txt (x_pl cx) f))) with (t + nn) by lia.
            rewrite (KTXT nn ltac:(lia)). exact HZ. }
        rewrite <- Hfirst in HQ. exact HQ.
      + unfold s5_txt. rewrite (s5_txt_eq (x_pl cx) f Hf). apply s5_cut_nul_nulfree.
    - change (sa_tail (rdW W (ms_mem msC)) (t + nn)). intros x Hx.
      exact (YG0d_tail.AR_block_word_vis SEGS B ly S W (ms_mem msC) md4 t (x_tn cx f) (t + nn) x
        HARC HtIn ltac:(rewrite Hreqt; lia) ltac:(lia)). }
  assert (SLOTS' : lt_slots cx (rdW W (ms_mem msC))
      (LT_L cx c m ++ [(152, Z.of_nat (length (seg_spec.seg_turn_tail (x_pl cx) f)))])).
  { apply (s5a_slots_xfer cx (rdW W mem) (rdW W (ms_mem msC))); [exact SLOTS|].
    intros o v Hin j Hj. pose proof (s5a_off_bound cx c m _ o v Hin) as Ho. apply KST; lia. }
  assert (BODY : S5_body B MT cx ly S W (ms_regs msC) (ms_mem msC) md4 k acc LFO_L c m t f).
  { split; [split; [exact FRM' | split; [exact IMG' | split; [exact HBL | exact HBUD]]]|].
    split; [exact (s5a_hblk_of B ly S W (ms_mem msC) md4 c seg_spec.SEG_C_SIZE HARC HcIn ltac:(lia))|].
    split; [exact (s5a_hblk_of B ly S W (ms_mem msC) md4 m seg_spec.SEG_M_SIZE HARC HmIn ltac:(lia))|].
    split; [exact (s5a_hblk_of B ly S W (ms_mem msC) md4 t (x_tn cx f) HARC HtIn ltac:(lia)) | exact HCNT]. }
  change (SRr SEGS W (cfg_at SEGS (BASE + LO_S5LB) (ms_regs msC) (ms_mem msC) md4) (lt_post B MT cx)).
  exact (HLB cx ly S W (ms_regs msC) (ms_mem msC) md4 k acc c m t HBASE HFRM Hf BODY CM' STR'
    G10' G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 SLOTS'). }

(* =============== 0x850f8 .. the branch at 0x85100 =============== *)
assert (HEIA : img_env VAL A_LIM (Eimg (Ereg regs []))) by apply Eimg_env.
assert (EEA : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r ->
    ew (Eimg (Ereg regs [])) n0 = getr regs r)
  by (intros n0 r Hr; apply ew_Eimg_Ereg_nat; exact Hr).
assert (U10 : bv_unsigned (ew (Eimg (Ereg regs [])) 10) = t)
  by (rewrite (EEA 10%nat 10%bv eq_refl), R10; apply unsigned_lit_small; lia).
assert (U20a : ew (Eimg (Ereg regs [])) 20 = Z_to_bv 64 nn)
  by (rewrite (EEA 20%nat 20%bv eq_refl); exact R20).
assert (HSA : st_ok_pi SEGS VAL (Eimg (Ereg regs [])) s5a_ssA
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO_K850f8)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold s5a_ssA. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - exact I.
  - split; [|split; [exact I | exact I]].
    cbn [ss_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U10. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia | reflexivity]. }
assert (SHOKA : sh_ok SEGS s5a_Bx [] (Eimg (Ereg regs [])) (mrestrict (w_H W) mem))
  by (unfold sh_ok; apply Forall_nil).
unfold cfg_at. change (w64 (BASE + LO_K850f8)) with (Z_to_bv 64 (BASE + LO_K850f8)).
remember (Eimg (Ereg regs [])) as EA eqn:HEA. clear HEA.
assert (UA20 : U EA (SOff 20 0) = nn) by (apply U_atom; [exact U20a | lia]).
paj_run_tok RUN HSA HJ SHOKA s5a_span.
{ apply awr_ok_nil. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?dd) _ => set (md1 := dd) in *; clearbody md1 end.
rename ms into ms0.
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms0) a = rdW W mem a).
{ intros a Ha. apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun _ => False) HFr); [|exact Ha | intros []].
  intros b wlo whi a' Hin Hrr. vm_compute in Hin. destruct Hin. }
clear HF HFr HG.
psrr_branch_tok RUN BR HSA SHOKA s5a_span.
- (* s4 = 0: the copy is skipped; the turn's text is empty *)
  assert (Hnz : nn = 0).
  { rewrite branch_eq_U, UA20, U_SLit in Hc. change (zcanon 0) with 0 in Hc.
    apply Z.eqb_eq in Hc. exact Hc. }
  paj_run_to_tok RUNTO HSA HJ SHOKA s5a_span 0x3e0.
  { apply awr_ok_nil. }
  lazymatch goal with |- SRr _ _ (mkCfg _ ?dd) _ => set (md2 := dd) in *; clearbody md2 end.
  assert (K2 : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms) a = rdW W mem a).
  { intros a Ha.
    assert (HK : rdW W (ms_mem ms) a = rdW W (ms_mem ms0) a).
    { apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun _ => False) HFr); [|exact Ha | intros []].
      intros b wlo whi a' Hin Hrr. vm_compute in Hin. destruct Hin. }
    rewrite HK. exact (K1 a Ha). }
  pmkst HSA.
  prreg HSA (2%bv : bv 5) T2. prreg HSA (3%bv : bv 5) T3. prreg HSA (4%bv : bv 5) T4.
  prreg HSA (8%bv : bv 5) T8. prreg HSA (9%bv : bv 5) T9. prreg HSA (18%bv : bv 5) T18.
  prreg HSA (19%bv : bv 5) T19. prreg HSA (20%bv : bv 5) T20. prreg HSA (21%bv : bv 5) T21.
  prreg HSA (22%bv : bv 5) T22. prreg HSA (23%bv : bv 5) T23. prreg HSA (24%bv : bv 5) T24.
  prreg HSA (25%bv : bv 5) T25. prreg HSA (26%bv : bv 5) T26. prreg HSA (27%bv : bv 5) T27.
  rewrite (EEA 2%nat 2%bv eq_refl) in T2. rewrite (EEA 3%nat 3%bv eq_refl) in T3.
  rewrite (EEA 4%nat 4%bv eq_refl) in T4. rewrite (EEA 8%nat 8%bv eq_refl) in T8.
  rewrite (EEA 9%nat 9%bv eq_refl) in T9. rewrite (EEA 18%nat 18%bv eq_refl) in T18.
  rewrite (EEA 19%nat 19%bv eq_refl) in T19. rewrite (EEA 20%nat 20%bv eq_refl) in T20.
  rewrite (EEA 21%nat 21%bv eq_refl) in T21. rewrite (EEA 22%nat 22%bv eq_refl) in T22.
  rewrite (EEA 10%nat 10%bv eq_refl), R10 in T23. rewrite (EEA 24%nat 24%bv eq_refl) in T24.
  rewrite (EEA 25%nat 25%bv eq_refl) in T25. rewrite (EEA 26%nat 26%bv eq_refl) in T26.
  rewrite (EEA 27%nat 27%bv eq_refl) in T27.
  exact (TAIL (ms_regs ms) (ms_mem ms) md2 HJ T2 T3 T4 T8 T9 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27
    ltac:(intros i Hi; exfalso; lia) ltac:(intros a Ha _ _; exact (K2 a Ha))).
- (* s4 <> 0: the checked memcpy of the turn's bytes into the text block *)
  assert (Hnz : nn <> 0).
  { rewrite branch_eq_U, UA20, U_SLit in Hc. change (zcanon 0) with 0 in Hc.
    apply Z.eqb_neq in Hc. exact Hc. }
  (* the payload block, and where the turn's bytes lie inside it *)
  assert (Hp0 : In (x_p cx, x_n cx) (ablocks B (x_ly cx) (x_S cx))) by (apply Hpay; lia).
  assert (HpIn : In (x_p cx, x_n cx) (ablocks B ly S))
    by exact (Permutation_in _ (Permutation_sym HBL) (in_or_app _ _ _ (or_intror Hp0))).
  assert (Hrp' : req_size (x_n cx) = x_n cx).
  { unfold req_size. replace (x_n cx =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
  destruct (s5a_blk_app B ly S W mem md (x_p cx) (x_n cx) HAR HpIn) as (Hp4 & Hpc & _ & _ & _ & _).
  rewrite Hrp' in Hpc.
  assert (Htp : (t, x_tn cx f) <> (x_p cx, x_n cx)) by (intros Hq; apply HtNot; rewrite Hq; exact Hp0).
  pose proof (s5a_sep B ly S W mem md t (x_tn cx f) (x_p cx) (x_n cx) HAR HtIn HpIn Htp) as Dtp.
  rewrite Hreqt, Hrp' in Dtp.
  assert (Hsrc_lo : x_p cx <= seg_spec.seg_turn_at (x_pl cx) (x_p cx) f)
    by (unfold seg_spec.seg_turn_at; lia).
  assert (Hsrc_hi : seg_spec.seg_turn_at (x_pl cx) (x_p cx) f + nn <= x_p cx + x_n cx)
    by (unfold seg_spec.seg_turn_at; lia).
  destruct (al_blocks _ _ LAWS ly S W mem md t (x_tn cx f) HAR HtIn) as (_ & _ & _ & _ & _ & _ & Htmax).
  (* 0x85104 .. 0x85110: a0 := t, a1 := the cursor, a2 := n, the jal *)
  paj_run_tok RUN HSA HJ SHOKA s5a_span.
  { apply awr_ok_nil. }
  lazymatch goal with |- SRr _ _ (mkCfg _ ?dd) _ => set (mdv1 := dd) in *; clearbody mdv1 end.
  assert (K2 : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms) a = rdW W mem a).
  { intros a Ha.
    assert (HK : rdW W (ms_mem ms) a = rdW W (ms_mem ms0) a).
    { apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun _ => False) HFr); [|exact Ha | intros []].
      intros b wlo whi a' Hin Hrr. vm_compute in Hin. destruct Hin. }
    rewrite HK. exact (K1 a Ha). }
  pose proof (proj1 HJ) as HAR1.
  destruct (al_blocks _ _ LAWS ly S W (ms_mem ms) mdv1 (x_p cx) (x_n cx) HAR1 HpIn)
    as (_ & _ & _ & _ & Hppres & _ & _).
  rewrite Hrp' in Hppres.
  pmkst HSA.
  prreg HSA (1%bv : bv 5) T1. prreg HSA (10%bv : bv 5) T10. prreg HSA (11%bv : bv 5) T11.
  prreg HSA (12%bv : bv 5) T12.
  prreg HSA (2%bv : bv 5) T2. prreg HSA (3%bv : bv 5) T3. prreg HSA (4%bv : bv 5) T4.
  prreg HSA (8%bv : bv 5) T8. prreg HSA (9%bv : bv 5) T9. prreg HSA (18%bv : bv 5) T18.
  prreg HSA (19%bv : bv 5) T19. prreg HSA (20%bv : bv 5) T20. prreg HSA (21%bv : bv 5) T21.
  prreg HSA (22%bv : bv 5) T22. prreg HSA (23%bv : bv 5) T23. prreg HSA (24%bv : bv 5) T24.
  prreg HSA (25%bv : bv 5) T25. prreg HSA (26%bv : bv 5) T26. prreg HSA (27%bv : bv 5) T27.
  rewrite (EEA 2%nat 2%bv eq_refl) in T2. rewrite (EEA 3%nat 3%bv eq_refl) in T3.
  rewrite (EEA 4%nat 4%bv eq_refl) in T4. rewrite (EEA 8%nat 8%bv eq_refl) in T8.
  rewrite (EEA 9%nat 9%bv eq_refl) in T9. rewrite (EEA 18%nat 18%bv eq_refl) in T18.
  rewrite (EEA 19%nat 19%bv eq_refl) in T19. rewrite (EEA 20%nat 20%bv eq_refl) in T20.
  rewrite (EEA 21%nat 21%bv eq_refl) in T21. rewrite (EEA 22%nat 22%bv eq_refl) in T22.
  rewrite (EEA 10%nat 10%bv eq_refl), R10 in T23. rewrite (EEA 24%nat 24%bv eq_refl) in T24.
  rewrite (EEA 25%nat 25%bv eq_refl) in T25. rewrite (EEA 26%nat 26%bv eq_refl) in T26.
  rewrite (EEA 27%nat 27%bv eq_refl) in T27.
  rewrite (EEA 10%nat 10%bv eq_refl), R10 in T10.
  rewrite (EEA 24%nat 24%bv eq_refl), R24 in T11.
  rewrite (EEA 20%nat 20%bv eq_refl), R20 in T12.
  assert (P3' : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite T3, Rgp; exact Hgp0).
  assert (P4' : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite T4, Rtp; exact Htp0).
  assert (HspT : spZ (ms_regs ms) = x_sp0 cx + (x_s1 cx - x_sp0 cx)).
  { unfold spZ. rewrite T2, Rsp. rewrite unsigned_lit_small by lia. lia. }
  assert (HraT : YK0s.ret_ok (Z_to_bv 64 (BASE + 0x3e0))) by (apply ret_ok_codeptr_v; [lia | reflexivity]).
  eapply SRr_bind.
  { apply (aj_intrin_atS SEGS B LAWS pa_segs_low OCpy (SIG SS___asan_memcpy) (AMEMCPY fx) W
      (ms_regs ms) (ms_mem ms) STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA)
      (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [(LT_FCLS, x_fpos cx)] ly S mdv1 k
      t (seg_spec.seg_turn_at (x_pl cx) (x_p cx) f) nn (x_s1 cx - x_sp0 cx) (Z_to_bv 64 (BASE + 0x3e0))
      HJ T10 T11 T12 ltac:(unfold MALLOC_MAX in Htmax; lia) ltac:(lia) ltac:(lia)
      HspT Ho16 ltac:(lia) ltac:(lia) P3' P4' T1 HraT).
    - intros a Ha. split.
      + right; right; left. exists t, (x_tn cx f).
        split; [exact HtIn | split; [exact HtNot | rewrite Hreqt; lia]].
      + lia.
    - intros a Ha HFP _. exfalso.
      exact (s5a_blk_not_img B ly S W (ms_mem ms) mdv1 t (x_tn cx f) a HAR1 HtIn
        ltac:(rewrite Hreqt; lia) (proj2 (HPGS a HFP))).
    - exact (amem_range_of_block SEGS B LAWS ly S W (ms_mem ms) mdv1 t (x_tn cx f) t nn HAR1 HtIn
        ltac:(lia) ltac:(rewrite Hreqt; lia)).
    - exact (range_addressable_of_block SEGS B LAWS ly S W (ms_mem ms) mdv1 t (x_tn cx f) t nn HAR1 HtIn
        ltac:(lia) ltac:(rewrite Hreqt; lia)).
    - intros Hpos. exact (shadow_hull_vis_of_block SEGS B LAWS ly S W (ms_mem ms) mdv1 t (x_tn cx f) t nn
        HAR1 HtIn ltac:(lia) ltac:(rewrite Hreqt; lia) Hpos).
    - split; [lia|]. split; [lia|]. split.
      { intros a Ha. split.
        - apply (aview_some_of_apresent SEGS). exact (proj1 (Hppres a ltac:(lia))).
        - rewrite HspT. lia. }
      split; [lia|].
      split; [exact (amem_range_of_block SEGS B LAWS ly S W (ms_mem ms) mdv1 (x_p cx) (x_n cx)
        (seg_spec.seg_turn_at (x_pl cx) (x_p cx) f) nn HAR1 HpIn ltac:(lia) ltac:(rewrite Hrp'; lia))|].
      split; [exact (range_addressable_of_block SEGS B LAWS ly S W (ms_mem ms) mdv1 (x_p cx) (x_n cx)
        (seg_spec.seg_turn_at (x_pl cx) (x_p cx) f) nn HAR1 HpIn ltac:(lia) ltac:(rewrite Hrp'; lia))|].
      intros Hpos. exact (shadow_hull_vis_of_block SEGS B LAWS ly S W (ms_mem ms) mdv1 (x_p cx) (x_n cx)
        (seg_spec.seg_turn_at (x_pl cx) (x_p cx) f) nn HAR1 HpIn ltac:(lia) ltac:(rewrite Hrp'; lia) Hpos). }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & H10b & HCPY & HKC & HPRS & HSAME).
  assert (QQ : forall (r : bv 5), acallee_saved (bv_unsigned r) -> getr regs2 r = getr (ms_regs ms) r)
    by (intros r Hr; exact (s5a_pres1 (ms_regs ms) regs2 r HP2 Hr)).
  apply (TAIL regs2 mem2 md2 HJ2).
  + rewrite (QQ 2%bv ltac:(s5a_cs)). exact T2.
  + rewrite (QQ 3%bv ltac:(s5a_cs)). exact T3.
  + rewrite (QQ 4%bv ltac:(s5a_cs)). exact T4.
  + rewrite (QQ 8%bv ltac:(s5a_cs)). exact T8.
  + rewrite (QQ 9%bv ltac:(s5a_cs)). exact T9.
  + rewrite (QQ 18%bv ltac:(s5a_cs)). exact T18.
  + rewrite (QQ 19%bv ltac:(s5a_cs)). exact T19.
  + rewrite (QQ 20%bv ltac:(s5a_cs)). exact T20.
  + rewrite (QQ 21%bv ltac:(s5a_cs)). exact T21.
  + rewrite (QQ 22%bv ltac:(s5a_cs)). exact T22.
  + rewrite (QQ 23%bv ltac:(s5a_cs)). exact T23.
  + rewrite (QQ 24%bv ltac:(s5a_cs)). exact T24.
  + rewrite (QQ 25%bv ltac:(s5a_cs)). exact T25.
  + rewrite (QQ 26%bv ltac:(s5a_cs)). exact T26.
  + rewrite (QQ 27%bv ltac:(s5a_cs)). exact T27.
  + intros i Hi. rewrite (HCPY i ltac:(lia)).
    exact (K2 (seg_spec.seg_turn_at (x_pl cx) (x_p cx) f + i) ltac:(lia)).
  + intros a Ha H1 H2. rewrite (HKC a Ha ltac:(lia) ltac:(lia)). exact (K2 a Ha).
Qed.

End ea.
End fa.
End da.
Print Assumptions s5_head.

(* ======================================== piece b ======================================== *)

(* ============================== pure facts of the turn's label byte ============================== *)
Lemma s5b_nfiles_range : forall pl, 1 <= seg_spec.seg_nfiles pl <= 4.
Proof.
intros pl. unfold seg_spec.seg_nfiles, seg_spec.seg_files, seg_spec.seg_pay, SegModel.decode.
destruct (SegModel.fuzz_u8 (seg_spec.seg_in pl)) as [b0 i1].
destruct (SegModel.fuzz_u8 i1) as [fl i2]. destruct (SegModel.fuzz_u8 i2) as [b2 i3].
cbn [SegModel.p_files]. rewrite s5_dec_files_length.
pose proof (Z.mod_pos_bound b2 4 ltac:(lia)) as H. rewrite Z2Nat.id by lia. lia.
Qed.

Lemma s5b_sfx_forall : forall (P : Z -> Prop) a b, s5_sfx a b -> Forall P b -> Forall P a.
Proof.
intros P a b (j & _ & ->) H. rewrite Forall_forall in *. intros x Hx. apply H.
rewrite <- (firstn_skipn j b). apply in_or_app. right. exact Hx.
Qed.

Lemma s5b_in_range : forall pl, Forall (fun z => 0 <= z < 256) (seg_spec.seg_in pl).
Proof.
intros pl. unfold seg_spec.seg_in, seg_spec.zs. apply Forall_forall. intros x Hx.
apply in_map_iff in Hx as (b & <- & _). pose proof (bv_unsigned_in_range 8 b) as H.
change (bv_modulus 8) with 256 in H. exact H.
Qed.

Lemma s5b_cur_sfx : forall pl f, s5_sfx (seg_spec.seg_cur pl f) (seg_spec.seg_in pl).
Proof.
intros pl f. unfold seg_spec.seg_cur.
apply (s5_sfx_trans _ (seg_spec.seg_hdr pl)); [apply s5_skip_sfx|].
unfold seg_spec.seg_hdr.
apply (s5_sfx_trans _ (snd (SegModel.fuzz_u8 (snd (SegModel.fuzz_u8 (seg_spec.seg_in pl)))))); [apply s5_u8_sfx|].
apply (s5_sfx_trans _ (snd (SegModel.fuzz_u8 (seg_spec.seg_in pl)))); [apply s5_u8_sfx | apply s5_u8_sfx].
Qed.

(* the label byte lb is a payload byte *)
Lemma s5b_lb_range : forall pl f, Z.of_nat f < seg_spec.seg_nfiles pl -> 0 <= seg_spec.seg_lb pl f < 256.
Proof.
intros pl f Hf. rewrite (s5_lb_eq pl f Hf).
pose proof (s5b_sfx_forall _ _ _ (s5b_cur_sfx pl f) (s5b_in_range pl)) as H.
destruct (seg_spec.seg_cur pl f) as [|b l]; cbn; [lia|]. inversion H. assumption.
Qed.

(* bltz a0 with a0 = lb << 56 (0x85140): taken exactly when lb has bit 7, for every byte value *)
Lemma s5b_bltz_tab : forallb (fun z => Bool.eqb (bv_lts (Z_to_bv 64 (Z.shiftl z 56)) (Z_to_bv 64 0))
  (negb (Z.land z 128 =? 0))) (map Z.of_nat (seq 0 256)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma s5b_in_seq : forall lo n z, Z.of_nat lo <= z < Z.of_nat lo + Z.of_nat n -> In z (map Z.of_nat (seq lo n)).
Proof.
intros lo n z Hz. apply in_map_iff. exists (Z.to_nat z). split; [lia|]. apply in_seq. lia.
Qed.
Lemma s5b_bltz : forall lb, 0 <= lb < 256 ->
  bv_lts (Z_to_bv 64 (Z.shiftl lb 56)) (Z_to_bv 64 0) = negb (Z.land lb 128 =? 0).
Proof.
intros lb Hlb. pose proof s5b_bltz_tab as H. rewrite forallb_forall in H.
specialize (H lb (s5b_in_seq 0 256 lb ltac:(lia))). apply Bool.eqb_prop in H. exact H.
Qed.

(* ============================== the printf-text glue ============================== *)
(* the parsed format of LIT_LABEL "reac-pw.conf.d/%u-x.conf" *)
Definition s5b_qs : list RtPFSeg.seg_piece :=
  match RtPFSeg.seg_parse LLVMFuzzerTestOneInput_c.LIT_LABEL with Some q => q | None => [] end.
Lemma s5b_parse : RtPFSeg.seg_parse LLVMFuzzerTestOneInput_c.LIT_LABEL = Some s5b_qs.
Proof. vm_compute. reflexivity. Qed.
Definition s5b_glue_b (v : Z) : bool :=
  match RtPFSeg.seg_text s5b_qs [RtPFPf.AInt v] with
  | Some T => (if list_eq_dec Z.eq_dec T (SegModel.fmt SegModel.F_label [SegModel.AI v]) then true else false) &&
      forallb (fun c => (0 <? c) && (c <? 256)) T && (Z.of_nat (length T) <=? 38)
  | None => false
  end.
Lemma s5b_glue_tab : forallb s5b_glue_b (map Z.of_nat (seq 1 127)) = true.
Proof. vm_compute. reflexivity. Qed.
(* RtPFSeg's text of the format at the argument AInt lb is SegModel's fmt F_label [AI lb], for 1 <= lb < 128:
   %u is Pu, whose text is pf_udec (lb mod 2 ^ 32), and SegModel's %u is dec lb *)
Lemma s5b_glue : forall lb, 1 <= lb < 128 ->
  RtPFSeg.seg_text s5b_qs [RtPFPf.AInt lb] = Some (SegModel.fmt SegModel.F_label [SegModel.AI lb]) /\
  Forall (fun c => 0 < c < 256) (SegModel.fmt SegModel.F_label [SegModel.AI lb]) /\
  Z.of_nat (length (SegModel.fmt SegModel.F_label [SegModel.AI lb])) <= 38.
Proof.
intros lb Hlb. pose proof s5b_glue_tab as H. rewrite forallb_forall in H.
specialize (H lb (s5b_in_seq 1 127 lb ltac:(lia))). unfold s5b_glue_b in H.
destruct (RtPFSeg.seg_text s5b_qs [RtPFPf.AInt lb]) as [T|]; [|discriminate].
destruct (list_eq_dec Z.eq_dec T (SegModel.fmt SegModel.F_label [SegModel.AI lb])) as [<-|]; [|discriminate].
apply andb_prop in H as [H1 H2]. apply andb_prop in H1 as [_ H1]. apply Z.leb_le in H2.
split; [reflexivity|]. split; [|exact H2].
rewrite forallb_forall in H1. apply Forall_forall. intros c Hc. specialize (H1 c Hc).
apply andb_prop in H1 as [Ha Hb]. apply Z.ltb_lt in Ha, Hb. lia.
Qed.
Lemma s5b_pk : Forall RtPFSeg.seg_pk s5b_qs.
Proof. vm_compute. repeat constructor. Qed.
Lemma s5b_prec : forall lb, RtPFSeg.seg_prec_pos s5b_qs [RtPFPf.AInt lb].
Proof. intros lb. vm_compute. exact I. Qed.
Lemma s5b_lit_label : seg_litA_fz LLVMFuzzerTestOneInput_c.LIT_LABEL = 135136.
Proof. vm_compute. reflexivity. Qed.
Lemma s5b_flabel : SegModel.F_label = LLVMFuzzerTestOneInput_c.LIT_LABEL.
Proof. reflexivity. Qed.
Lemma s5b_label_len : forall lb, 1 <= lb < 128 ->
  SegModel.snprintf_s 40 SegModel.F_label [SegModel.AI lb] = SegModel.fmt SegModel.F_label [SegModel.AI lb].
Proof.
intros lb Hlb. destruct (s5b_glue lb Hlb) as (_ & _ & HL). unfold SegModel.snprintf_s.
apply firstn_all2. lia.
Qed.

(* ============================== the snprintf step through the walk's journal ==============================
   plugin-hostd/fuzz_command's lib/A/Prog/PaRt.v:271-424 cwc_aj_snprintf_atSF (origin/ossv/recipes 501c0d516c69),
   ported to segconf's row 4 RtPFSeg.seg_asnprintf_realizes (lib/A/Rt/RtPFSeg.v): the window is
   RtPFSeg.SEG_SNP_K = 2 * ESTACK in place of the donor's 3 * ESTACK, and the format family is
   RtPFSeg.FR_seg lo gotw, taken as a premise in place of the donor's RtPFCmd.FR_cmd built from fr_lit_ok. The
   destination [d, d + n) is one the walk may write (awr_byte) outside the caller's window; the journal is rebuilt
   with YCbq.v's ajournal_after_write over the destination and the window; the ecall_pre_stk is PaArt.v's
   ecall_pre_stk_at. *)
Section s5b_c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section s5b_g.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Lemma s5b_aj_snprintf_atSF : forall lo hi cr pc gotw guard,
  RtPFSeg.seg_asnprintf_realizes segs B lo hi cr pc gotw guard ->
  forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d n f T (o : Z) raw cval,
  ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  getr regsT 10 = w64 d -> getr regsT 11 = w64 n -> getr regsT 12 = w64 f ->
  1 <= n < 2 ^ 31 -> 0 < d -> d + n <= 2 ^ 63 ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> RtPFSeg.SEG_SNP_K - o <= STK ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
  (forall a, d <= a < d + n -> awr_byte segs B STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) (frames S) lyc own a /\
    ~ (sp0 + o - RtPFSeg.SEG_SNP_K <= a < sp0 + o)) ->
  (forall a, d <= a < d + n -> inFP FP a -> (Exists (in_zr a) (as_prog_static B) /\ in_img segs a) \/
    sp0 <= a < ly_top lyc -> writable_at segs (mrestrict (w_H W) memT) a) ->
  amem_range d (n + 8) ->
  range_addressable (aview segs (w_H W) memT) SHADOW_OFF d n ->
  shadow_hull_vis (aview segs (w_H W) memT) d n ->
  RtDefs.rt_rom_view segs B W memT ->
  Forall (fun r => 0 <= fst r /\ fst r + snd r <= 2 ^ 63) cr ->
  Forall (fun r => Forall (zdisjoint r)
    (RtPFShared.snp_out RtPFSeg.SEG_SNP_K (spZ regsT) d (RtPFShared.sn_len (n - 1) T))) cr ->
  rdword (aview segs (w_H W) memT) gotw = Some guard -> rdword (aview segs (w_H W) memT) guard = Some cval ->
  0 <= gotw -> gotw + 8 <= 2 ^ 63 -> 0 <= guard -> guard + 8 <= 2 ^ 63 ->
  Forall (zdisjoint (gotw, 8)) (RtPFShared.snp_out RtPFSeg.SEG_SNP_K (spZ regsT) d (RtPFShared.sn_len (n - 1) T)) ->
  Forall (zdisjoint (guard, 8)) (RtPFShared.snp_out RtPFSeg.SEG_SNP_K (spZ regsT) d (RtPFShared.sn_len (n - 1) T)) ->
  spZ regsT <= 2 ^ 47 ->
  RtPFSeg.FR_seg lo gotw (aview segs (w_H W) memT)
    (RtPFShared.snp_out RtPFSeg.SEG_SNP_K (spZ regsT) d (RtPFShared.sn_len (n - 1) T)) f
    (map (argZ regsT) [3; 4; 5; 6; 7]) T ->
  Z.of_nat (length T) < 2 ^ 31 - 1 ->
  zdisjoint (d, RtPFShared.sn_len (n - 1) T) (lo, hi - lo) ->
  frm0 fx ->
  SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
  (fun W2 c2 => W2 = W /\ exists (fx1 : YK11.FPState) regs2 mem2 md2, fxrel fx fx1 /\
    c2 = mkCfg (@mkst fx1 regs2 raw mem2 (seg_rom segs)) md2 /\
    ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
    aregs_preserved regsT regs2 /\
    getr regs2 10 = w64 (Z.of_nat (length T)) /\
    (forall i, 0 <= i < RtPFShared.sn_len (n - 1) T ->
      aview segs (w_H W) mem2 (d + i) = Some (nth (Z.to_nat i) (RtPFShared.sn_bytes (n - 1) T) 0)) /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (sp0 + o - RtPFSeg.SEG_SNP_K <= a < sp0 + o) ->
      aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
    (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) /\
    same_but_materialized mdc md2).
Proof using LAWS segs_low.
intros lo hi cr pc gotw guard AP W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d n f T o raw cval
  HJ Ha0 Ha1 Ha2 Hn Hd Hdn Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hdest HPC Hamr Hrad Hhull Hrom Hcr1 Hcr2
  Hgc Hgv Hgc0 Hgc1 Hgv0 Hgv1 Hgcd Hgvd Hsp47 HFF HT Hdog Hfrm.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
assert (HK : RtPFSeg.SEG_SNP_K = 2 * ESTACK) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
rewrite HK in Hbud, Hdest.
assert (HPRE : ecall_pre_stk segs B (2 * ESTACK) lyc Sc W regsT memT mdc).
{ apply (ecall_pre_stk_at segs B (2 * ESTACK) STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o HJ Hsp' Hal Hneg);
  [lia | exact Hbud | rewrite Hra; exact Hraw | exact Hgp | exact Htp]. }
destruct HPRE as (HEP & Hslo & Hscr).
set (len := RtPFShared.sn_len (n - 1) T) in *.
assert (Hlen : 1 <= len <= n).
{ unfold len, RtPFShared.sn_len, RtPFShared.sn_bytes. rewrite length_app, length_firstn. cbn [length]. lia. }
assert (HDW : d + len <= sp0 + o - 2 * ESTACK \/ sp0 + o <= d).
{ destruct (Z_le_gt_dec (sp0 + o) d) as [Hge|Hlt]; [right; exact Hge|left].
  destruct (Z_le_gt_dec (d + len) (sp0 + o - 2 * ESTACK)) as [Hle|Hgt]; [exact Hle|exfalso].
  destruct (Z_le_gt_dec (sp0 + o - 2 * ESTACK) d) as [Hd1|Hd1].
  - exact (proj2 (Hdest d ltac:(lia)) ltac:(lia)).
  - exact (proj2 (Hdest (sp0 + o - 2 * ESTACK) ltac:(lia)) ltac:(lia)). }
assert (HDEST : dest_ok segs B lyc Sc W regsT memT d len).
{ intros a Ha. destruct (Hdest a ltac:(lia)) as [Hw Hns].
  destruct (awr_byte_present segs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw (HPC a ltac:(lia))) as [Hp Hno].
  split; [exact Hp|]. split; [exact Hno|]. rewrite Hsp'. lia. }
assert (HAMRl : amem_range d (len + 8)) by (unfold amem_range in *; lia).
assert (HRADl : range_addressable (aview segs (w_H W) memT) SHADOW_OFF d len) by (intros x Hx; apply Hrad; lia).
assert (HHULLl : shadow_hull_vis (aview segs (w_H W) memT) d len).
{ intros s Hs. apply Hhull. split; [lia|].
  assert (E1 : (d + len - 1) / 8 <= (d + n - 1) / 8) by (apply Z.div_le_mono; lia).
  unfold shadow_addr in *.
  assert (E2 : (SHADOW_OFF + (d + len - 1) / 8) / 8 <= (SHADOW_OFF + (d + n - 1) / 8) / 8) by (apply Z.div_le_mono; lia).
  lia. }
eapply SRr_mono.
{ apply (AP lyc Sc W regsT memT mdc d n f [] (map (argZ regsT) [3; 4; 5; 6; 7]) T cval HEP).
  - exact Hslo.
  - intros a Ha. apply Hscr. exact Ha.
  - exact Ha0. - exact Ha1. - exact Ha2. - exact Hrom. - exact Hcr1. - exact Hcr2.
  - exact Hgc. - exact Hgv. - exact Hgc0. - exact Hgc1. - exact Hgv0. - exact Hgv1. - exact Hgcd. - exact Hgvd.
  - split; [rewrite app_nil_r; reflexivity | intros i Hi; cbn [length] in Hi; lia].
  - cbn [length]. lia.
  - cbn [length]. unfold RtPFShared.snp_out. rewrite HK, Hsp'.
    apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia|].
    apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia | apply Forall_nil].
  - exact HFF.
  - exact Hn. - exact HT. - exact Hd. - lia.
  - unfold RtPFShared.snp_out. rewrite HK, Hsp'. cbn [pairwise]. split; [|split; [apply Forall_nil | exact I]].
    apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia | apply Forall_nil].
  - exact HDEST. - exact HAMRl. - exact HRADl. - exact HHULLl. - exact Hdog. - exact Hfrm. }
cbv beta. intros W2 c2 _ (-> & fx1 & regs2 & mem2 & md2 & -> & Hf1 & Hf2 & HAR2 & HP & Hsame & H10 & Hby & Hfr & Hgr).
assert (Hkeep : forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (sp0 + o - RtPFSeg.SEG_SNP_K <= a < sp0 + o) ->
  aview segs (w_H W) mem2 a = aview segs (w_H W) memT a).
{ intros a H0 H1 H2. apply (Hfr a H0); [lia | rewrite HK, Hsp'; rewrite HK in H2; lia]. }
split; [reflexivity|]. exists fx1, regs2, mem2, md2.
split; [exact (fxrel_of_frm0 fx fx1 Hf1 Hf2)|].
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write segs B LAWS segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
    (fun a => (d <= a < d + n) \/ (sp0 + o - RtPFSeg.SEG_SNP_K <= a < sp0 + o)) Sc own HJ).
  - intros a Ha Hna. apply (Hkeep a Ha); intros H'; apply Hna; [left | right]; exact H'.
  - exact Hgr.
  - exact Hsame.
  - intros a [Ha | Ha]; left; [exact (proj1 (Hdest a Ha)) | left; rewrite HK in Ha; lia].
  - exact HAR2.
  - reflexivity. - reflexivity. - lia. - exact Hfrs. - exact HQT. }
split; [exact HP|]. split; [exact H10|]. split; [exact Hby|]. split; [exact Hkeep|]. split; [exact Hgr | exact Hsame].
Qed.
End s5b_g.
End s5b_c.

(* ============================== small facts the walk's lemmas share ============================== *)
Lemma s5b_word_kept : forall (rd rd' : reader) a v,
  (forall x, a <= x < a + 8 -> rd' x = rd x) -> rdword rd a = Some v -> rdword rd' a = Some v.
Proof. intros rd rd' a v HK H. rewrite (rdword_ext rd rd' a); [exact H|]. intros k Hk. apply HK. lia. Qed.
(* the token and role-word literals the image's words point at are short *)
Lemma s5b_tok_len : forall i, (i < pin_spec.CAT_N)%nat ->
  Z.of_nat (length (seg_spec.zs (pin_spec.tok_bytes i))) + 1 <= 65536.
Proof.
intros i Hi.
assert (H : forallb (fun j => Nat.leb (length (seg_spec.zs (pin_spec.tok_bytes j))) 100) (seq 0 pin_spec.CAT_N) = true)
  by (vm_compute; reflexivity).
rewrite forallb_forall in H. specialize (H i ltac:(apply in_seq; lia)). apply Nat.leb_le in H. lia.
Qed.
Lemma s5b_word_len : forall i, (i < 5)%nat ->
  Z.of_nat (length (nth i m_file_c.MF_ROLE_WORDS [])) + 1 <= 65536.
Proof.
intros i Hi.
assert (H : forallb (fun j => Nat.leb (length (nth j m_file_c.MF_ROLE_WORDS [])) 100) (seq 0 5) = true)
  by (vm_compute; reflexivity).
rewrite forallb_forall in H. specialize (H i ltac:(apply in_seq; lia)). apply Nat.leb_le in H. lia.
Qed.
Lemma s5b_apart_longl : forall a n, sa_apart_all a n (ltoi_PG longlA) -> a + n <= longlA \/ longlA + 120 <= a.
Proof.
intros a n H. inversion H as [|iv l H1 _]. cbn [fst snd] in H1. unfold LONGL_N in H1. lia.
Qed.
(* a run whose regions have no write window keeps every byte *)
Lemma s5b_nowin : forall segs E rs (H : word -> bool) (m m' : word -> option byte),
  Forall (fun r => YP09.r_whi r <= YP09.r_wlo r) rs ->
  frame_of E rs (mrestrict H m) (mrestrict H m') -> forall a, aview segs H m' a = aview segs H m a.
Proof.
intros segs E rs H m m' Hw Hfr a. apply aview_eq_of. apply Hfr. intros (r & Hin & Hr).
rewrite Forall_forall in Hw. specialize (Hw r Hin). lia.
Qed.
(* addiw rd, rs, 1 and srli rd, rs, 3 over atoms *)
Lemma s5b_addw1 : forall E (n : nat) f, ew E n = w64 f -> 0 <= f < 2 ^ 31 - 1 ->
  sv_denot E (SAluw ALU_ADD (SOff n 0) (SLit 1)) = w64 (f + 1).
Proof.
intros E n f Hn Hf. rewrite denot_lit_U. unfold w64. f_equal.
rewrite U_of_S, S_SAluw. cbn [zalu_raw]. rewrite U_SOff, U_SLit, Hn. unfold w64.
rewrite unsigned_lit_small by lia. rewrite Z.add_0_r.
rewrite (zcanon_id f) by (unfold M64; lia). change (zcanon 1) with 1.
rewrite (Z.mod_small f) by lia. change (1 mod 2 ^ 32) with 1.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N].
rewrite (Z.mod_small (f + 1 + _)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma s5b_srl3 : forall E (n : nat) v, ew E n = w64 v -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SAlu ALU_SRL (SOff n 0) (SLit 3)) = w64 (v / 8).
Proof.
intros E n v Hn Hv. rewrite denot_lit_U. unfold w64. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SOff, U_SLit, Hn. unfold w64.
rewrite unsigned_lit_small by lia. rewrite Z.add_0_r.
rewrite (zcanon_id v) by (unfold M64; lia). change (Z.land (zcanon 3) 63) with 3.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
apply zcanon_id. unfold M64. pose proof (Z.div_le_upper_bound v 8 v ltac:(lia) ltac:(lia)).
pose proof (Z.div_pos v 8 ltac:(lia) ltac:(lia)). lia.
Qed.

(* ============================== the walk's points between 0x85148 and the two cuts ============================== *)
Section s5b_d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section s5b_f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section s5b_e.
Variable B : asyms.
Variable MT : ameter_ops.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis IMGS : s10_img.
Hypothesis BSYM : AF0m.SegBSyms B.
Hypothesis HPG_RO : forall a, inFP (ltoi_PG longlA) a -> ~ in_roP SEGS RLO_A RHI_A a.
Hypothesis HPG_PTR : forall a p,
  ((exists i, (i < 5)%nat /\ a = wordsA + 8 * Z.of_nat i) \/
   (exists i, (i < pin_spec.CAT_N)%nat /\ a = pin_spec.row_addr catA i)) ->
  rdword (fun x => option_map (fun b : byte => bv_unsigned b) (seg_rom SEGS (Z_to_bv 64 x))) a = Some p ->
  p + 65536 <= longlA.

(* what every point of the piece holds besides its registers and its label: S5_LB_stmt's premises *)
Definition s5b_pt (cx : lcx) ly S (W : world SEGS) (regs : bvmap 5 word) mem md (k acc c m t : Z) (f : nat) : Prop :=
  S5_body B MT cx ly S W regs mem md k acc LFO_L c m t f /\
  lt_cm (rdW W mem) c m (x_st cx f) /\
  sa_str (rdW W mem) t (s5_txt (x_pl cx) f) /\
  lt_slots cx (rdW W mem) (LT_L cx c m ++ [(152, Z.of_nat (length (seg_spec.seg_turn_tail (x_pl cx) f)))]).
(* the bytes the piece writes: longl[0 .. 120) (memset), label[40] (snprintf), a runtime entry's window below S1 *)
Definition s5b_X (cx : lcx) (a : Z) : Prop :=
  (longlA <= a < longlA + 120) \/ (x_fr cx + 96 <= a < x_fr cx + 136) \/ (x_s1 cx - 8192 <= a < x_s1 cx).

(* the entry sp, the realigned S1, the class-3 frame, from the context and the journal from the entry *)
Lemma s5b_geo : forall cx ly S (W : world SEGS) mem md k,
  lt_base B MT cx ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem md k ->
  x_sp0 cx mod 16 = 0 /\ alloc_ceiling + 32768 <= x_sp0 cx <= 2 ^ 47 /\
  x_sp0 cx - 336 <= x_s1 cx <= x_sp0 cx - 320 /\ x_s1 cx mod 16 = 0 /\
  In (LT_FCLS, x_fpos cx) (frames S) /\ frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx /\
  4096 <= x_fr cx /\ x_fr cx + 512 <= alloc_ceiling /\ x_fr cx mod 64 = 0 /\
  (x_fr cx + 512 <= 65536 \/ 6295552 <= x_fr cx) /\
  (x_fr cx + 512 <= kLowShadowBeg \/ kHighMemBeg <= x_fr cx) /\
  140735332483072 <= alloc_ceiling <= 140737479966720 /\ alloc_ceiling mod 4096 = 0.
Proof.
intros cx ly S W mem md k HB HJ.
pose proof HB as (HPRE & _). pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof (proj1 HJ) as HAR. pose proof HJ as (_ & Hly & _ & _ & _ & Hfrs & _).
assert (Hin : In (LT_FCLS, x_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (EF : frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx).
{ unfold x_fr, frame_addr. pose proof Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
destruct (frames_bounds SEGS B LAWS ly S W mem md LT_FCLS (x_fpos cx) HAR Hin) as (Hf0 & Hfc & Happ).
pose proof (frame_al64 SEGS B ly S W mem md LT_FCLS (x_fpos cx) HAR Hin) as (Hal64 & _).
pose proof (PaLibH.frm_off_imgP B ly S W mem md LT_FCLS (x_fpos cx) HAR Hin) as Hoff.
rewrite EF in Hf0, Hfc, Happ, Hal64, Hoff. change (fs_frame_bytes LT_FCLS) with 512 in Hfc, Happ, Hoff.
pose proof (@alloc_ceiling_val rc) as (C1 & C2).
change STK_LLVMFuzzerTestOneInput with 32768 in *.
unfold in_app, off_img in *.
assert (Es1 : x_s1 cx = (x_sp0 cx - 320) - (x_sp0 cx - 320) mod 32) by reflexivity.
change (spZ (x_regs cx)) with (x_sp0 cx) in *.
clear Hly Hfrs HJ HPRE Hstk HB.
split; [exact Hal|]. split; [lia|]. split; [rewrite Es1; lia|]. split; [rewrite Es1; lia|].
split; [exact Hin|]. split; [exact EF|]. split; [lia|]. split; [lia|]. split; [exact Hal64|].
split; [exact Hoff|]. split; [unfold ASAN_CEIL in Happ; lia|]. split; [exact C1 | exact C2].
Qed.

(* the bytes of a live block, and the 8-byte word after its last byte, miss what the piece writes *)
Lemma s5b_notX_blk : forall cx ly S (W : world SEGS) mem md p n a,
  AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) -> In (LT_FCLS, x_fpos cx) (frames S) ->
  frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx -> alloc_ceiling + 8192 <= x_s1 cx ->
  p <= a < p + req_size n -> ~ s5b_X cx a.
Proof.
intros cx ly S W mem md p n a HAR Hin HinF EF Hs1 Ha.
destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & _ & Hceil & _).
pose proof (blk_off_imgP B ly S W mem md p n HAR Hin) as Hoff.
pose proof (sep_block_frame SEGS B LAWS ly S W mem md p n LT_FCLS (x_fpos cx) HAR Hin HinF) as Hsep.
rewrite EF in Hsep. change (fs_frame_bytes LT_FCLS) with 512 in Hsep.
unfold zdisjoint, off_img in *. cbn [fst snd] in Hsep. unfold s5b_X, longlA, A_LONGL.
destruct Hoff as [Ho|Ho]; destruct Hsep as [Hs|Hs]; lia.
Qed.
Lemma s5b_notX_tail : forall cx ly S (W : world SEGS) mem md p n e x,
  AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) -> In (LT_FCLS, x_fpos cx) (frames S) ->
  frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx -> alloc_ceiling + 16384 <= x_s1 cx -> x_fr cx mod 64 = 0 ->
  p <= e < p + req_size n -> e < x < e - e mod 8 + 8 -> ~ s5b_X cx x.
Proof.
intros cx ly S W mem md p n e x HAR Hin HinF EF Hs1 Hf64 He Hx.
destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & _ & Hceil & _).
pose proof (blk_off_imgP B ly S W mem md p n HAR Hin) as Hoff.
pose proof (sep_block_frame SEGS B LAWS ly S W mem md p n LT_FCLS (x_fpos cx) HAR Hin HinF) as Hsep.
rewrite EF in Hsep. change (fs_frame_bytes LT_FCLS) with 512 in Hsep.
unfold zdisjoint, off_img in *. cbn [fst snd] in Hsep. unfold s5b_X, longlA, A_LONGL.
pose proof (Z.mod_pos_bound e 8 ltac:(lia)). pose proof (Z.div_mod e 8 ltac:(lia)).
pose proof (Z.div_mod (x_fr cx) 64 ltac:(lia)).
destruct Hoff as [Ho|Ho]; destruct Hsep as [Hs|Hs]; lia.
Qed.

(* a live block of a state is a harness block of that state (_s12's lk_hblk) *)
Lemma s5b_hblk : forall ly S (W : world SEGS) mem md a n,
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

(* lt_img at a later reader that keeps every image byte but longl[0 .. 120): longl is not read-only (HPG_RO),
   every literal seg_himg names directly is apart from longl (its sa_apart_all), and the literals the role words
   and the catalogue's rows point at lie below it (HPG_PTR, through arodata_okP's RELRO view of the words) *)
Lemma s5b_img_kept : forall cx (W : world SEGS) mem mem',
  (forall a, in_img SEGS a -> ~ (longlA <= a < longlA + 120) -> rdW W mem' a = rdW W mem a) ->
  lt_img B cx (rdW W mem) -> lt_img B cx (rdW W mem').
Proof.
intros cx W mem mem' K (HRO & HIM & HGI).
destruct HIM as (Hm40 & Hm40i & HLF & HLR & (Hcp & Hci & Hcr) & HCa & (Hwp & Hwi & Hwr) & (Hrp & Hri & Hrr) &
  (Hg1 & Hg2) & HLP & HLT & HLI & HD1 & HD2 & HD3).
assert (KI : forall q n, sa_img SEGS B q n -> (q + n <= longlA \/ longlA + 120 <= q) ->
  forall a, q <= a < q + n -> rdW W mem' a = rdW W mem a).
{ intros q n Hq Hap a Ha. apply K; [exact (proj1 (Hq a Ha)) | lia]. }
assert (KL : forall a s, sa_lit SEGS B (rdW W mem) a s ->
  (a + (Z.of_nat (length s) + 1) <= longlA \/ longlA + 120 <= a) -> sa_lit SEGS B (rdW W mem') a s).
{ intros a s (Ha & ((Hz & Hn0) & _) & Hp & Hr & Hi) Hap. split; [exact Ha|]. split; [split; [split|]|].
  - intros i Hix. rewrite (KI _ _ Hi Hap); [exact (Hz i Hix)|]. rewrite length_app in Hix. cbn [length] in Hix. lia.
  - exact Hn0.
  - exact (sa_tail_of_romtail SEGS (w_H W) mem' _ Hr).
  - split; [exact Hp|]. split; [exact Hr | exact Hi]. }
assert (KR : forall q n a, sa_img SEGS B q n -> q <= a -> a + 8 <= q + n -> RLO_A <= a -> a + 8 <= RHI_A ->
  rdword (rdW W mem) a =
  rdword (fun x => option_map (fun b : byte => bv_unsigned b) (seg_rom SEGS (Z_to_bv 64 x))) a).
{ intros q n a Hq H1 H2 H3 H4. symmetry. apply rdword_ext. intros kk Hkk.
  destruct (Hq (a + kk) ltac:(lia)) as (_ & Ho & He).
  symmetry. apply (HRO (a + kk)); [right; lia | exact Ho | exact He]. }
assert (KP : forall a p s, ((exists i, (i < 5)%nat /\ a = wordsA + 8 * Z.of_nat i) \/
   (exists i, (i < pin_spec.CAT_N)%nat /\ a = pin_spec.row_addr catA i)) ->
   rdword (fun x => option_map (fun b : byte => bv_unsigned b) (seg_rom SEGS (Z_to_bv 64 x))) a = Some p ->
   Z.of_nat (length s) + 1 <= 65536 ->
   sa_lit SEGS B (rdW W mem) p s -> sa_lit SEGS B (rdW W mem') p s).
{ intros a p s Ha Hp Hs Hl. pose proof (HPG_PTR a p Ha Hp) as Hlo. apply KL; [exact Hl | left; lia]. }
split; [|split].
- (* arodata_okP *)
  intros a Hro Ho He. rewrite (K a); [exact (HRO a Hro Ho He) | |].
  + destruct Hro as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | exact (s10i_relro IMGS a Hr)].
  + intros Hl. apply (HPG_RO a); [|exact Hro]. exists (longlA, longlA + LONGL_N).
    split; [left; reflexivity|]. cbn [fst snd]. unfold LONGL_N. lia.
- (* seg_himg *)
  assert (Hm40a : mod40A + 8 <= longlA \/ longlA + 120 <= mod40A) by (unfold sa_disj, LONGL_N in HD3; lia).
  split; [intros kk Hkk; rewrite (KI _ 8 Hm40i Hm40a) by lia; exact (Hm40 kk Hkk)|].
  split; [exact Hm40i|].
  split; [intros s Hs; destruct (HLF s Hs) as [Hl Ha]; split; [exact (KL _ _ Hl (s5b_apart_longl _ _ Ha)) | exact Ha]|].
  split; [intros s Hs; destruct (HLR s Hs) as [Hl Ha]; split; [exact (KL _ _ Hl (s5b_apart_longl _ _ Ha)) | exact Ha]|].
  split.
  { split; [exact Hcp|]. split; [exact Hci|]. intros i Hi. destruct (Hcr i Hi) as (tp & Htp & Hl). exists tp.
    pose proof catA_ro as (Cr1 & Cr2).
    assert (Hrow : catA <= pin_spec.row_addr catA i /\ pin_spec.row_addr catA i + 8 <= catA + pin_spec.CAT_BYTES)
      by (unfold pin_spec.row_addr, pin_spec.CAT_ROW, pin_spec.CAT_BYTES; unfold pin_spec.CAT_N in Hi; lia).
    pose proof (s5b_apart_longl _ _ HCa) as Hcatap.
    split.
    - rewrite <- Htp. apply rdword_ext. intros kk Hkk. apply (KI _ _ Hci Hcatap). lia.
    - apply (KP (pin_spec.row_addr catA i) tp); [right; exists i; split; [exact Hi | reflexivity] | | apply s5b_tok_len; exact Hi | exact Hl].
      rewrite <- (KR catA pin_spec.CAT_BYTES (pin_spec.row_addr catA i) Hci); [exact Htp | lia | lia | lia | lia]. }
  split; [exact HCa|].
  split.
  { split; [exact Hwp|]. split; [exact Hwi|]. intros i Hi. destruct (Hwr i Hi) as (wp & Hwp' & Hl). exists wp.
    assert (Hwa : wordsA + 40 <= longlA \/ longlA + 120 <= wordsA) by (unfold wordsA, longlA, A_LONGL; lia).
    split.
    - rewrite <- Hwp'. apply rdword_ext. intros kk Hkk. apply (KI _ _ Hwi Hwa). lia.
    - apply (KP (wordsA + 8 * Z.of_nat i) wp); [left; exists i; split; [exact Hi | reflexivity] | | apply s5b_word_len; exact Hi | exact Hl].
      rewrite <- (KR wordsA 40 (wordsA + 8 * Z.of_nat i) Hwi); [exact Hwp' | lia | lia | | ];
      unfold RLO_A, RHI_A, SEG_RLO, SEG_RHI, wordsA; lia. }
  split.
  { split; [exact Hrp|]. split; [exact Hri|]. intros i Hi kk Hkk.
    rewrite (KI _ _ Hri ltac:(unfold rolesA, longlA, A_LONGL; lia)) by lia. exact (Hrr i Hi kk Hkk). }
  split.
  { split.
    - rewrite <- Hg1. apply rdword_ext. intros kk Hkk.
      pose proof (s10i_relro IMGS (gotwA + kk) ltac:(unfold gotwA, RLO_A, RHI_A, SEG_RLO, SEG_RHI; lia)) as Hi.
      apply K; [exact Hi | unfold gotwA, longlA, A_LONGL; lia].
    - apply s10_rdword_some. intros kk Hkk. apply s10_rom_view_some. apply (s10i_guard IMGS). lia. }
  split; [exact HLP|]. split; [exact HLT|]. split; [exact HLI|]. split; [exact HD1|]. split; [exact HD2 | exact HD3].
- (* ltoi_GI: longl[120] *)
  intros i Hi. rewrite K; [exact (HGI i Hi) | exact (proj1 (HLI (longlA + LONGL_W + i) ltac:(unfold LONGL_W, LONGL_N; lia))) |].
  unfold LONGL_W. lia.
Qed.

(* the point's facts carried to a later memory that keeps every byte the piece does not write, with the journal
   from the entry at the later memory and the five registers lt_frame names *)
Lemma s5b_kept : forall cx ly S (W : world SEGS) regs mem md k acc c m t f regs' mem' md',
  lt_base B MT cx ->
  s5b_pt cx ly S W regs mem md k acc c m t f ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem' md' k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ s5b_X cx a -> rdW W mem' a = rdW W mem a) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
  s5b_pt cx ly S W regs' mem' md' k acc c m t f.
Proof.
intros cx ly S W regs mem md k acc c m t f regs' mem' md' HB HP HJ' KEEP P2 P3 P4 P8 P9.
destruct HP as ((((HJ & R2 & R3 & R4 & R8 & R9 & HSV & HH0 & HH8 & HH16 & HFL & H176 & HSH) & HIMG & HBL & HBUD) &
  HHc & HHm & HHt & HCNT) & (HCc & HCm) & HSTR & HSL).
destruct (s5b_geo cx ly S W mem md k HB HJ) as (G1 & G2 & G3 & G4 & HinF & EF & G5 & G6 & G7 & G8 & G9 & C1 & C2).
pose proof (proj1 HJ) as HAR. pose proof (proj1 HJ') as HAR'.
assert (Hs1 : alloc_ceiling + 8192 <= x_s1 cx) by lia.
assert (Hs2 : alloc_ceiling + 16384 <= x_s1 cx) by lia.
assert (KS : forall a, x_s1 cx <= a < 2 ^ 64 -> rdW W mem' a = rdW W mem a).
{ intros a Ha. apply KEEP; [lia|]. unfold s5b_X, longlA, A_LONGL. lia. }
assert (KF : forall a, x_fr cx <= a < x_fr cx + 96 \/ x_fr cx + 136 <= a < x_fr cx + 512 -> rdW W mem' a = rdW W mem a).
{ intros a Ha. apply KEEP; [lia|]. unfold s5b_X, longlA, A_LONGL. destruct G8 as [G8|G8]; lia. }
assert (Hq1 : SHADOW_OFF + 512 <= x_sh cx).
{ unfold x_sh, shadow_addr. pose proof (Z.div_le_mono 4096 (x_fr cx) 8 ltac:(lia) ltac:(lia)) as Hd.
  change (4096 / 8) with 512 in Hd. lia. }
assert (Hq2 : x_sh cx + 64 <= 17594332446784).
{ unfold x_sh, shadow_addr, SHADOW_OFF. pose proof (Z.div_le_mono (x_fr cx) 140737479966720 8 ltac:(lia) ltac:(lia)) as Hd.
  change (140737479966720 / 8) with 17592184995840 in Hd. lia. }
assert (KH : forall i, 0 <= i < 64 -> rdW W mem' (x_sh cx + i) = rdW W mem (x_sh cx + i)).
{ intros i Hi. apply KEEP; [unfold SHADOW_OFF in Hq1; lia|]. unfold s5b_X, longlA, A_LONGL.
  unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. destruct G9 as [G9|G9]; lia. }
assert (KB : forall p n a, In (p, n) (ablocks B ly S) -> p <= a < p + req_size n -> rdW W mem' a = rdW W mem a).
{ intros p n a Hin Ha. destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & H4096 & Hceil & _).
  apply KEEP; [lia|]. exact (s5b_notX_blk cx ly S W mem md p n a HAR Hin HinF EF Hs1 Ha). }
split; [split; [split; [|split; [|split; [exact HBL | exact HBUD]]] | split; [|split; [|split; [|exact HCNT]]]] | split; [|split]].
- (* lt_frame *)
  split; [exact HJ'|]. rewrite P2, P3, P4, P8, P9.
  split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R8|]. split; [exact R9|].
  split.
  { intros i r Hi. assert (Hi13 : (i < length LT_SAVED)%nat) by (apply nth_error_Some; congruence).
    change (length LT_SAVED) with 13%nat in Hi13.
    apply (s5b_word_kept (rdW W mem)); [|exact (HSV i r Hi)]. intros x Hx. apply KS. lia. }
  split; [apply (s5b_word_kept (rdW W mem)); [|exact HH0]; intros x Hx; apply KF; lia|].
  split; [apply (s5b_word_kept (rdW W mem)); [|exact HH8]; intros x Hx; apply KF; lia|].
  split; [apply (s5b_word_kept (rdW W mem)); [|exact HH16]; intros x Hx; apply KF; lia|].
  split; [apply (s5b_word_kept (rdW W mem)); [|exact HFL]; intros x Hx; apply KF; unfold LT_FLAGW in *; lia|].
  split; [apply (s5b_word_kept (rdW W mem)); [|exact H176]; intros x Hx; apply KS; lia|].
  intros i Hi. rewrite (lt_fsh_len LFO_L) in Hi. rewrite KH by lia. apply HSH. rewrite lt_fsh_len. exact Hi.
- (* lt_img *)
  apply (s5b_img_kept cx W mem mem'); [|exact HIMG]. intros a Ha Hl. pose proof (pa_img_range a Ha) as Hr.
  apply KEEP; [unfold kImgEnd in Hr; lia|]. unfold s5b_X. unfold kImgEnd in Hr. destruct G8 as [G8|G8]; lia.
- exact (s5b_hblk ly S W mem' md' c _ HAR' (proj1 HHc)).
- exact (s5b_hblk ly S W mem' md' m _ HAR' (proj1 HHm)).
- exact (s5b_hblk ly S W mem' md' t _ HAR' (proj1 HHt)).
- (* lt_cm *)
  split.
  + destruct HCc as (bs & Hbs & Henc). exists bs. split; [|exact Henc]. intros i Hi.
    rewrite (KB c seg_spec.SEG_C_SIZE); [exact (Hbs i Hi) | exact (proj1 HHc) |].
    pose proof (proj1 Henc) as HL. change (req_size seg_spec.SEG_C_SIZE) with seg_spec.SEG_C_SIZE. lia.
  + destruct HCm as (bs & Hbs & Henc). exists bs. split; [|exact Henc]. intros i Hi.
    rewrite (KB m seg_spec.SEG_M_SIZE); [exact (Hbs i Hi) | exact (proj1 HHm) |].
    pose proof (proj1 Henc) as HL. change (req_size seg_spec.SEG_M_SIZE) with seg_spec.SEG_M_SIZE. lia.
- (* the text's C string *)
  destruct HSTR as ((Hzs & Hn0) & Htail).
  assert (Htn : x_tn cx f = Z.of_nat (length (s5_txt (x_pl cx) f)) + 1) by reflexivity.
  assert (Hreq : req_size (x_tn cx f) = x_tn cx f) by (unfold req_size; destruct (Z.eqb_spec (x_tn cx f) 0); lia).
  split; [split; [|exact Hn0]|].
  + intros i Hi. rewrite (KB t (x_tn cx f)); [exact (Hzs i Hi) | exact (proj1 HHt) |].
    rewrite length_app in Hi. cbn [length] in Hi. rewrite Hreq, Htn. lia.
  + intros x Hx. pose proof (proj1 HHt) as Hin. destruct (al_blocks _ _ LAWS ly S W mem md t _ HAR Hin) as (_ & H4096 & Hceil & _).
    rewrite Hreq in Hceil. rewrite KEEP; [exact (Htail x Hx) | lia |].
    apply (s5b_notX_tail cx ly S W mem md t (x_tn cx f) (t + Z.of_nat (length (s5_txt (x_pl cx) f))) x HAR Hin HinF EF Hs2 G7);
    [rewrite Hreq, Htn; lia | exact Hx].
- (* the s1 slots *)
  intros o v Hin. assert (Ho : 8 <= o <= 184).
  { apply in_app_or in Hin. destruct Hin as [Hin | Hin]; unfold LT_L in Hin; cbn [In] in Hin;
    repeat (destruct Hin as [Hin | Hin]; [injection Hin as H1 _; subst o; lia|]); destruct Hin. }
  apply (s5b_word_kept (rdW W mem)); [|exact (HSL o v Hin)]. intros x Hx. apply KS. lia.
Qed.

(* the label's facts carried to a reader that agrees everywhere *)
Lemma s5b_label_ext : forall ly S (rd rd' : reader) cx f lp c m,
  (forall a, rd' a = rd a) -> S5_label B ly S rd cx f lp c m -> S5_label B ly S rd' cx f lp c m.
Proof.
intros ly S rd rd' cx f lp c m E (H0 & Hs & Hm). split; [exact H0|].
destruct (s5_lab (x_pl cx) f) as [l|]; [|split; [exact Hs | exact Hm]].
destruct Hs as (Hnz & ((Hz & Hn0) & Ht)).
split; [split; [exact Hnz|]; split; [split; [intros i Hi; rewrite E; exact (Hz i Hi) | exact Hn0] | intros x Hx; rewrite E; exact (Ht x Hx)]|].
destruct Hm as (H1 & H2 & (A1 & A2 & A3 & A4 & A5) & H4 & H5).
split; [exact H1|]. split; [exact H2|]. split; [|split; [exact H4 | exact H5]].
split; [exact A1|]. split; [exact A2|]. split; [exact A3|].
split; [intros x Hx; destruct (A4 x Hx) as (s & Hs & Hok); exists s; rewrite E; split; [exact Hs | exact Hok]|].
intros Hn s Hs. rewrite E. exact (A5 Hn s Hs).
Qed.


Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* the s1 slots the join reads: 168(s1) = m (atom 32) and 184(s1) = m + 0x2000 (atom 33) *)
Definition s5b_jreg : YP09.region :=
  YP09.mkRegion (Some 9%nat) 168 192 0 0
    [YP09.mkChunk 168 (CVal 8 (SOff 32 0)); YP09.mkChunk 184 (CVal 8 (SOff 33 0))].
Definition s5b_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* the state at the bgeu 0x851a0 after the join's run: s2 = f + 1, a0 = m, s10 = (m + 0x2000) >> 3 *)
Definition s5b_ssj : sstate :=
  mkSS 0x46c
    [SLit 0; SOff 1 0; SOff 2 0; SOff 3 0; SOff 4 0; SOff 5 0; SOff 6 0; SOff 7 0; SOff 8 0; SOff 9 0;
     SOff 32 0; SOff 11 0; SOff 12 0; SOff 13 0; SOff 14 0; SOff 15 0; SOff 16 0; SOff 17 0;
     SAluw ALU_ADD (SOff 18 0) (SLit 1); SOff 19 0; SOff 20 0; SOff 21 0; SOff 22 0; SOff 23 0; SOff 24 0;
     SOff 25 0; SAlu ALU_SRL (SOff 33 0) (SLit 3); SOff 27 0; SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0]
    [s5b_jreg] None (mkFacts [] [] []).

Lemma s5b_denot_atom : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

(* the register a symbolic state holds, read back without unfolding the value *)
Ltac s5b_rreg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  end.
(* the write permission of a run whose regions are all read-only: no byte is in a write window *)
Ltac s5b_awr_ro :=
  lazymatch goal with |- awr_ok ?sg ?Bv ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?f0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg Bv Ex rs' stk spx fp b0 bc f0 lyx own) end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.

(* ---- the join, 0x85190 .. 0x851a0, reached from the snprintf arm's j at 0x8516c (offset 0x438), the memset
   arm's j at 0x85188 (0x454) or the fall-through at 0x85190 (0x45c): s2 = f + 1, s10 = (m + 0x2000) >> 3,
   a0 = m, then bgeu s2, s9 to the last turn's cut 0x851f0 or on to 0x851a4 ---- *)
Lemma s5b_join : forall f, S5A_OTH B MT f -> S5A_LST B MT f ->
  forall p0 cx ly S (W : world SEGS) regs mem md k acc c m t lp,
  (p0 = 0x438 \/ p0 = 0x454 \/ p0 = 0x45c) ->
  lt_base B MT cx -> sa_frm0 -> Z.of_nat f < x_nf cx ->
  s5b_pt cx ly S W regs mem md k acc c m t f ->
  S5_label B ly S (rdW W mem) cx f lp c m ->
  getr regs 18 = w64 (Z.of_nat f) -> getr regs 19 = w64 (-8) -> getr regs 20 = w64 lp ->
  getr regs 21 = w64 (x_sh cx) -> getr regs 22 = w64 (seg_spec.b2z (seg_spec.seg_ret (x_st cx f))) ->
  getr regs 23 = w64 t -> getr regs 24 = w64 (seg_spec.seg_turn_at (x_pl cx) (x_p cx) f) ->
  getr regs 25 = w64 (x_nf cx) -> getr regs 27 = w64 (seg_spec.seg_turn_np (x_pl cx) f) ->
  SRr SEGS W (cfg_at SEGS (BASE + p0) regs mem md) (lt_post B MT cx).
Proof.
intros f HOTH HLST p0 cx ly S W regs mem md k acc c m t lp Hp0 HB Hfrm Hf HP HL
  R18 R19 R20 R21 R22 R23 R24 R25 R27.
pose proof HP as ((((HJ & R2 & R3 & R4 & R8 & R9 & _) & _) & _ & HHm & _) & _ & _ & HSL).
destruct (s5b_geo cx ly S W mem md k HB HJ) as (G1 & G2 & G3 & G4 & HinF & EF & G5 & G6 & G7 & G8 & G9 & C1 & C2).
pose proof (s5b_nfiles_range (x_pl cx)) as Hnf. unfold x_nf in *.
pose proof (proj1 HJ) as HAR.
destruct (al_blocks _ _ LAWS ly S W mem md m _ HAR (proj1 HHm)) as (_ & Hm4096 & Hmceil & _).
change (req_size seg_spec.SEG_M_SIZE) with 9236 in Hmceil.
assert (H168 : rdword (rdW W mem) (x_s1 cx + 168) = Some m).
{ apply HSL. apply in_or_app. left. unfold LT_L. cbn [In]. repeat (first [left; reflexivity | right]). }
assert (H184 : rdword (rdW W mem) (x_s1 cx + 184) = Some (m + seg_spec.MC_N)).
{ apply HSL. apply in_or_app. left. unfold LT_L. cbn [In]. repeat (first [left; reflexivity | right]). }
set (E := Eimg (Ereg regs [w64 m; w64 (m + seg_spec.MC_N)])).
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r).
{ intros n r Hn. unfold E. pose proof (bv_unsigned_in_range 5 r) as Hr5.
  change (bv_modulus 5) with 32 in Hr5. rewrite Eimg_low by (unfold A_TEXT; lia).
  apply ew_Ereg_nat. exact Hn. }
assert (E32 : ew E 32 = w64 m).
{ unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). }
assert (E33 : ew E 33 = w64 (m + seg_spec.MC_N)).
{ unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 1). }
assert (E9u : bv_unsigned (ew E 9) = x_s1 cx).
{ rewrite (EE 9%nat 9%bv eq_refl), R9. unfold w64. apply unsigned_lit_small. lia. }
assert (HS : st_ok_pi SEGS VAL E (mkSS p0 sr_atoms [s5b_jreg] None (mkFacts [] [] []))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + p0)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold s5b_jreg, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E9u.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor; [|constructor]].
    + apply (chunk_ok_val SEGS E _ (x_s1 cx) 168 8 (SOff 32 0) m);
      [rewrite s5b_denot_atom, E32; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia
      | apply val_mem_of_rdword; exact H168].
    + apply (chunk_ok_val SEGS E _ (x_s1 cx) 184 8 (SOff 33 0) (m + seg_spec.MC_N));
      [rewrite s5b_denot_atom, E33; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold seg_spec.MC_N; lia | cbn; lia
      | apply val_mem_of_rdword; exact H184].
  - cbn. tauto.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    repeat match goal with |- _ /\ _ => split end; exact I. }
assert (SHOK : sh_ok SEGS (SLit SHADOW_OFF) [] E (mrestrict (w_H W) mem)) by apply Forall_nil.
assert (Hf31 : 0 <= Z.of_nat f < 2 ^ 31 - 1) by lia.
assert (E18 : ew E 18 = w64 (Z.of_nat f)) by (rewrite (EE 18%nat 18%bv eq_refl); exact R18).
assert (E25 : ew E 25 = w64 (seg_spec.seg_nfiles (x_pl cx))) by (rewrite (EE 25%nat 25%bv eq_refl); exact R25).
assert (EK : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> sv_denot E (SOff n 0) = getr regs r)
  by (intros n r Hn; rewrite s5b_denot_atom; exact (EE n r Hn)).
unfold cfg_at. change (w64 (BASE + p0)) with (Z_to_bv 64 (BASE + p0)).
clearbody E.
(* the state at the bgeu 0x851a0, whichever way the join was entered: the shared rest of the piece *)
assert (CONT : forall ms1 md1, st_ok_pi SEGS VAL E s5b_ssj (restrict (w_H W) ms1) ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W (ms_mem ms1) md1 k ->
  (forall a, rdW W (ms_mem ms1) a = rdW W mem a) ->
  SRr SEGS W (mkCfg ms1 md1) (lt_post B MT cx)).
{ intros ms1 md1 HS1 HJ1 K1. clear HS SHOK HJ. rename HS1 into HS. rename HJ1 into HJ.
  assert (SHOK : sh_ok SEGS (SLit SHADOW_OFF) [] E (mrestrict (w_H W) (ms_mem ms1))) by apply Forall_nil.
  (* 0x851a0 bgeu s2, s9: f + 1 >= nfiles is the last turn *)
  psrr_branch_tok RUN BR HS SHOK s5b_span;
  rewrite branch_geu_U in Hc; unfold U in Hc; rewrite (s5b_addw1 E 18 (Z.of_nat f) E18 Hf31), s5b_denot_atom, E25 in Hc;
  unfold w64 in Hc; rewrite !unsigned_lit_small in Hc by lia.
  - (* taken: 0x851f0, the last turn *)
    assert (Hlast : Z.of_nat f + 1 = x_nf cx) by (apply Bool.negb_true_iff, Z.ltb_ge in Hc; unfold x_nf; lia).
    clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK s5b_span 0x4bc; [s5b_awr_ro|].
    assert (K2 : forall a, rdW W (ms_mem ms) a = rdW W (ms_mem ms1) a)
      by (apply (s5b_nowin SEGS E [s5b_jreg] (w_H W) (ms_mem ms1) (ms_mem ms)); [repeat constructor; cbn; lia | exact HFr]).
    clear HF HFr HG.
    lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md2 := d) in *; clearbody md2 end.
    pmkst HS.
    s5b_rreg HS (2%bv : bv 5) P2. s5b_rreg HS (3%bv : bv 5) P3. s5b_rreg HS (4%bv : bv 5) P4.
    s5b_rreg HS (8%bv : bv 5) P8. s5b_rreg HS (9%bv : bv 5) P9. s5b_rreg HS (10%bv : bv 5) P10.
    s5b_rreg HS (18%bv : bv 5) P18. s5b_rreg HS (21%bv : bv 5) P21. s5b_rreg HS (22%bv : bv 5) P22.
    s5b_rreg HS (23%bv : bv 5) P23. s5b_rreg HS (24%bv : bv 5) P24. s5b_rreg HS (26%bv : bv 5) P26.
    s5b_rreg HS (27%bv : bv 5) P27.
    rewrite (EK 2%nat 2%bv eq_refl) in P2. rewrite (EK 3%nat 3%bv eq_refl) in P3. rewrite (EK 4%nat 4%bv eq_refl) in P4.
    rewrite (EK 8%nat 8%bv eq_refl) in P8. rewrite (EK 9%nat 9%bv eq_refl) in P9.
    rewrite s5b_denot_atom, E32 in P10. rewrite (s5b_addw1 E 18 (Z.of_nat f) E18 Hf31) in P18.
    rewrite (EK 21%nat 21%bv eq_refl), R21 in P21. rewrite (EK 22%nat 22%bv eq_refl), R22 in P22.
    rewrite (EK 23%nat 23%bv eq_refl), R23 in P23. rewrite (EK 24%nat 24%bv eq_refl), R24 in P24.
    rewrite (EK 27%nat 27%bv eq_refl), R27 in P27.
    rewrite (s5b_srl3 E 33 (m + seg_spec.MC_N) E33 ltac:(unfold seg_spec.MC_N; lia)) in P26.
    destruct (s5b_kept cx ly S W regs mem md k acc c m t f (ms_regs ms) (ms_mem ms) md2 HB HP HJ
      (fun a _ _ => eq_trans (K2 a) (K1 a)) P2 P3 P4 P8 P9) as (HBODY2 & HCM2 & HSTR2 & HSL2).
    pose proof (HLST fx) as HL'. unfold S5_LST_stmt in HL'.
    change (SRr SEGS W (cfg_at SEGS (BASE + LO_S5LST) (ms_regs ms) (ms_mem ms) md2) (lt_post B MT cx)).
    exact (HL' cx ly S W (ms_regs ms) (ms_mem ms) md2 k acc c m t HB Hfrm Hlast HBODY2 HCM2 HSTR2
      P10 P18 P21 P22 P23 P24 P26 P27 HSL2).
  - (* not taken: 0x851a4, a turn that is not the last *)
    assert (Hoth : Z.of_nat f + 1 < x_nf cx) by (apply Bool.negb_false_iff, Z.ltb_lt in Hc; unfold x_nf; lia).
    clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK s5b_span 0x470; [s5b_awr_ro|].
    assert (K2 : forall a, rdW W (ms_mem ms) a = rdW W (ms_mem ms1) a)
      by (apply (s5b_nowin SEGS E [s5b_jreg] (w_H W) (ms_mem ms1) (ms_mem ms)); [repeat constructor; cbn; lia | exact HFr]).
    clear HF HFr HG.
    lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md2 := d) in *; clearbody md2 end.
    pmkst HS.
    s5b_rreg HS (2%bv : bv 5) P2. s5b_rreg HS (3%bv : bv 5) P3. s5b_rreg HS (4%bv : bv 5) P4.
    s5b_rreg HS (8%bv : bv 5) P8. s5b_rreg HS (9%bv : bv 5) P9. s5b_rreg HS (10%bv : bv 5) P10.
    s5b_rreg HS (18%bv : bv 5) P18. s5b_rreg HS (19%bv : bv 5) P19. s5b_rreg HS (20%bv : bv 5) P20.
    s5b_rreg HS (21%bv : bv 5) P21. s5b_rreg HS (22%bv : bv 5) P22.
    s5b_rreg HS (23%bv : bv 5) P23. s5b_rreg HS (24%bv : bv 5) P24. s5b_rreg HS (25%bv : bv 5) P25.
    s5b_rreg HS (26%bv : bv 5) P26. s5b_rreg HS (27%bv : bv 5) P27.
    rewrite (EK 2%nat 2%bv eq_refl) in P2. rewrite (EK 3%nat 3%bv eq_refl) in P3. rewrite (EK 4%nat 4%bv eq_refl) in P4.
    rewrite (EK 8%nat 8%bv eq_refl) in P8. rewrite (EK 9%nat 9%bv eq_refl) in P9.
    rewrite s5b_denot_atom, E32 in P10. rewrite (s5b_addw1 E 18 (Z.of_nat f) E18 Hf31) in P18.
    rewrite (EK 19%nat 19%bv eq_refl), R19 in P19. rewrite (EK 20%nat 20%bv eq_refl), R20 in P20.
    rewrite (EK 21%nat 21%bv eq_refl), R21 in P21. rewrite (EK 22%nat 22%bv eq_refl), R22 in P22.
    rewrite (EK 23%nat 23%bv eq_refl), R23 in P23. rewrite (EK 24%nat 24%bv eq_refl), R24 in P24.
    rewrite (EK 25%nat 25%bv eq_refl), R25 in P25. rewrite (EK 27%nat 27%bv eq_refl), R27 in P27.
    rewrite (s5b_srl3 E 33 (m + seg_spec.MC_N) E33 ltac:(unfold seg_spec.MC_N; lia)) in P26.
    destruct (s5b_kept cx ly S W regs mem md k acc c m t f (ms_regs ms) (ms_mem ms) md2 HB HP HJ
      (fun a _ _ => eq_trans (K2 a) (K1 a)) P2 P3 P4 P8 P9) as (HBODY2 & HCM2 & HSTR2 & HSL2).
    pose proof (s5b_label_ext ly S (rdW W mem) (rdW W (ms_mem ms)) cx f lp c m
      (fun a => eq_trans (K2 a) (K1 a)) HL) as HL2.
    pose proof (HOTH fx) as HO'. unfold S5_OTH_stmt in HO'.
    change (SRr SEGS W (cfg_at SEGS (BASE + LO_S5OTH) (ms_regs ms) (ms_mem ms) md2) (lt_post B MT cx)).
    exact (HO' cx ly S W (ms_regs ms) (ms_mem ms) md2 k acc c m t lp HB Hfrm Hoth HBODY2 HCM2 HSTR2 HL2
      P10 P18 P19 P20 P21 P22 P23 P24 P25 P26 P27 HSL2). }
(* 0x8516c / 0x85188 j 0x85190 (as the case is), then 0x85190 .. 0x8519c, to the bgeu at 0x851a0 *)
destruct Hp0 as [-> | [-> | ->]];
  (paj_run_tok RUN HS HJ SHOK s5b_span; [s5b_awr_ro|]);
  (apply CONT; [exact HS | exact HJ |
     apply (s5b_nowin SEGS E [s5b_jreg] (w_H W) mem (ms_mem ms)); [repeat constructor; cbn; lia | exact HFr]]).
Qed.

End s5b_e.
End s5b_f.
End s5b_d.

(* ============================== more pure facts the arms use ============================== *)
(* a byte value whose bit 7 is clear is below 128 *)
Lemma s5b_bit7_tab : forallb (fun z => implb (Z.land z 128 =? 0) (z <? 128)) (map Z.of_nat (seq 0 256)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma s5b_bit7 : forall lb, 0 <= lb < 256 -> Z.land lb 128 = 0 -> lb < 128.
Proof.
intros lb Hlb H0. pose proof s5b_bit7_tab as H. rewrite forallb_forall in H.
specialize (H lb (s5b_in_seq 0 256 lb ltac:(lia))). rewrite (proj2 (Z.eqb_eq _ _) H0) in H. cbn [implb] in H.
apply Z.ltb_lt in H. exact H.
Qed.
(* what snprintf(d, 40, ...) leaves of a text of at most 38 bytes *)
Lemma s5b_snlen : forall T : list Z, (length T <= 38)%nat ->
  RtPFShared.sn_len (40 - 1) T = Z.of_nat (length T) + 1 /\ RtPFShared.sn_bytes (40 - 1) T = T ++ [0].
Proof.
intros T HT. unfold RtPFShared.sn_len, RtPFShared.sn_bytes. rewrite firstn_all2 by (cbn; lia).
split; [rewrite length_app; cbn [length]; lia | reflexivity].
Qed.
(* the five shadow bytes of label[40] when the frame's shadow is LFO_L's *)
Lemma s5b_lab_shadow : forall (rd : reader) sh, sa_zs rd sh (lt_fsh LFO_L) ->
  forall j, 12 <= j < 17 -> rd (sh + j) = Some 0.
Proof.
intros rd sh H j Hj. assert (Hj' : j = 12 \/ j = 13 \/ j = 14 \/ j = 15 \/ j = 16) by lia.
destruct Hj' as [-> | [-> | [-> | [-> | ->]]]];
[exact (H 12%nat ltac:(vm_compute; lia)) | exact (H 13%nat ltac:(vm_compute; lia)) |
 exact (H 14%nat ltac:(vm_compute; lia)) | exact (H 15%nat ltac:(vm_compute; lia)) |
 exact (H 16%nat ltac:(vm_compute; lia))].
Qed.
Lemma s5b_lab_addressable : forall (rd : reader) fr d n, 0 <= fr -> fr mod 8 = 0 ->
  sa_zs rd (shadow_addr fr) (lt_fsh LFO_L) -> fr + 96 <= d -> d + n <= fr + 136 ->
  range_addressable rd SHADOW_OFF d n.
Proof.
intros rd fr d n H0 H8 HZ H1 H2 x Hx. exists 0. split; [|left; reflexivity].
unfold shadow_of_addr. unfold shadow_addr in HZ.
pose proof (Z.div_mod fr 8 ltac:(lia)). pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
replace (SHADOW_OFF + x / 8) with (SHADOW_OFF + fr / 8 + (x / 8 - fr / 8)) by lia.
apply (s5b_lab_shadow rd _ HZ). lia.
Qed.
Lemma s5b_hull_mono : forall (rd : reader) d n n', shadow_hull_vis rd d n -> 0 < n' <= n -> shadow_hull_vis rd d n'.
Proof.
intros rd d n n' H Hn s Hs. apply H. split; [lia|].
assert (E1 : (d + n' - 1) / 8 <= (d + n - 1) / 8) by (apply Z.div_le_mono; lia).
unfold shadow_addr in *.
assert (E2 : (SHADOW_OFF + (d + n' - 1) / 8) / 8 <= (SHADOW_OFF + (d + n - 1) / 8) / 8) by (apply Z.div_le_mono; lia).
lia.
Qed.
Lemma s5b_pres_reg : forall regs regs' (r : bv 5) z,
  aregs_preserved regs regs' -> acallee_saved z -> Z_to_bv 5 z = r -> getr regs' r = getr regs r.
Proof. intros regs regs' r z HP Hz <-. exact (HP z Hz). Qed.

(* ============================== the three arms and the piece ============================== *)
Section s5b_md. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section s5b_mf.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section s5b_me.
Variable B : asyms.
Variable MT : ameter_ops.
Variable snp_lo snp_hi : Z.
Variable snp_cr : list (Z * Z).
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis IMGS : s10_img.
Hypothesis BSYM : AF0m.SegBSyms B.
Hypothesis PRW : prog_rw SEGS B.
Hypothesis VOBJS : seg_val_objs.
Hypothesis HPGS : forall a, inFP (ltoi_PG longlA) a ->
  Exists (in_zr a) (as_prog_static B) /\ in_img SEGS a.
Hypothesis HPG_RO : forall a, inFP (ltoi_PG longlA) a -> ~ in_roP SEGS RLO_A RHI_A a.
Hypothesis HPG_PTR : forall a p,
  ((exists i, (i < 5)%nat /\ a = wordsA + 8 * Z.of_nat i) \/
   (exists i, (i < pin_spec.CAT_N)%nat /\ a = pin_spec.row_addr catA i)) ->
  rdword (fun x => option_map (fun b : byte => bv_unsigned b) (seg_rom SEGS (Z_to_bv 64 x))) a = Some p ->
  p + 65536 <= longlA.
Hypothesis AMEMSET : forall fx0 : YK11.FPState,
  @aintrin_realizes fx0 rc SEGS B OSet (SIG SS___asan_memset).
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState,
  @RtPFSeg.seg_asnprintf_realizes fx0 rc SEGS B snp_lo snp_hi snp_cr
    (SIG SS___interceptor_trampoline_snprintf) gotwA guardA.
Hypothesis HSNP_LIT : forall x, In x LLVMFuzzerTestOneInput_c.LTOI_LITS ->
  snp_lo <= seg_litA_fz x /\ seg_litA_fz x + Z.of_nat (length x) + 1 <= gotwA.
Hypothesis HSNP_CR : Forall (fun r => snp_lo <= fst r /\ 0 <= snd r /\ fst r + snd r <= snp_hi) snp_cr.
Hypothesis HSNP_LO : 0 <= snp_lo.
Hypothesis HSNP_CEIL : snp_hi <= alloc_ceiling.
Hypothesis HSNP_FAKE : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> snp_hi <= ly_F ly.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* 80(s1) = FR + 96, the label's address the snprintf arm loads (atom 32) *)
Definition s5b_lreg : YP09.region :=
  YP09.mkRegion (Some 9%nat) 80 88 0 0 [YP09.mkChunk 80 (CVal 8 (SOff 32 0))].
Definition s5b_ss0 : sstate := mkSS 0x414 sr_atoms [s5b_lreg] None (mkFacts [] [] []).

Ltac s5b_rreg2 HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  end.
Ltac s5b_awr_ro2 :=
  lazymatch goal with |- awr_ok ?sg ?Bv ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?f0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg Bv Ex rs' stk spx fp b0 bc f0 lyx own) end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.

(* a live frame lies at or above the fake stack's base (fuzz_command's RtPFDog.v:35-44 pa_frame_above_img) *)
Lemma s5b_fake_le : forall ly S (W : world SEGS) mem md cid pos,
  AR SEGS B ly S W mem md -> In (cid, pos) (frames S) -> ly_F ly <= frame_addr ly cid pos.
Proof.
intros ly S W mem md cid pos HA Hin. destruct HA as (M & _ & _).
pose proof (frame_facts B ly S _ cid pos M Hin) as (Fc & _ & _ & _ & _ & P1 & _).
pose proof (Z.mul_nonneg_nonneg cid (2 ^ 20) ltac:(lia) ltac:(lia)) as CN.
unfold frame_addr, kFakeFramesOff in *. lia.
Qed.

Lemma s5b_main : forall f, S5A_OTH B MT f -> S5A_LST B MT f -> S5_LB_stmt B MT f.
Proof.
unfold S5_LB_stmt.
intros f HOTH HLST cx ly S W regs mem md k acc c m t HB Hfrm Hf HBODY HCM HSTR
  R10 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27 HSL.
assert (HP : s5b_pt B MT cx ly S W regs mem md k acc c m t f) by exact (conj HBODY (conj HCM (conj HSTR HSL))).
pose proof HBODY as (((HJ & R2 & R3 & R4 & R8 & R9 & _) & HIMG & _) & HHc & HHm & HHt & _).
destruct (s5b_geo B MT cx ly S W mem md k HB HJ) as (G1 & G2 & G3 & G4 & HinF & EF & G5 & G6 & G7 & G8 & G9 & C1 & C2).
pose proof (s5b_nfiles_range (x_pl cx)) as Hnf.
pose proof (s5b_lb_range (x_pl cx) f Hf) as Hlb.
pose proof HB as (HPRE0 & _). pose proof HPRE0 as (_ & _ & _ & Hgp0 & Htp0 & _).
pose proof HIMG as (_ & (_ & _ & HLF & _ & _ & _ & _ & _ & _ & HLP & HLT & HLI & _) & _).
set (lb := seg_spec.seg_lb (x_pl cx) f) in *.
assert (H80 : rdword (rdW W mem) (x_s1 cx + 80) = Some (x_fr cx + FO_LABEL)).
{ apply HSL. apply in_or_app. left. unfold LT_L. cbn [In]. repeat (first [left; reflexivity | right]). }
set (E := Eimg (Ereg regs [w64 (x_fr cx + FO_LABEL)])).
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r).
{ intros n r Hn. unfold E. pose proof (bv_unsigned_in_range 5 r) as Hr5.
  change (bv_modulus 5) with 32 in Hr5. rewrite Eimg_low by (unfold A_TEXT; lia).
  apply ew_Ereg_nat. exact Hn. }
assert (EK : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> sv_denot E (SOff n 0) = getr regs r)
  by (intros n r Hn; rewrite s5b_denot_atom; exact (EE n r Hn)).
assert (E32 : sv_denot E (SOff 32 0) = w64 (x_fr cx + FO_LABEL)).
{ rewrite s5b_denot_atom. unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). }
assert (E9u : bv_unsigned (ew E 9) = x_s1 cx).
{ rewrite (EE 9%nat 9%bv eq_refl), R9. unfold w64. apply unsigned_lit_small. lia. }
assert (EOBJ : forall i v, (i < length SegAddr.seg_objs)%nat -> nth i SegAddr.seg_objs 0 = v ->
  sv_denot E (SOff (A_OBJ i) 0) = w64 v).
{ intros i v Hi Hv. cbn [sv_denot]. rewrite (HEI (A_OBJ i)); [|unfold A_OBJ, A_TEXT, A_LIM; vm_compute in Hi; lia].
  rewrite (VOBJS i Hi), Hv, Z.add_0_r. reflexivity. }
assert (ECP : forall kk, sv_denot E (SOff A_TEXT kk) = Z_to_bv 64 (BASE + kk)) by (intros kk; exact (codeptr_val E kk HEI)).
assert (HS : st_ok_pi SEGS VAL E s5b_ss0
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO_S5LB)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold s5b_ss0. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold s5b_lreg, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E9u.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (x_s1 cx) 80 8 (SOff 32 0) (x_fr cx + FO_LABEL));
    [exact E32 | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold FO_LABEL; lia | cbn; lia
    | apply val_mem_of_rdword; exact H80].
  - cbn. tauto.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    repeat match goal with |- _ /\ _ => split end; exact I. }
assert (SHOK : sh_ok SEGS (SLit SHADOW_OFF) [] E (mrestrict (w_H W) mem)) by apply Forall_nil.
assert (E10 : sv_denot E (SOff 10 0) = w64 (Z.shiftl lb 56)) by (rewrite (EK 10%nat 10%bv eq_refl); exact R10).
assert (E26 : sv_denot E (SOff 26 0) = w64 lb) by (rewrite (EK 26%nat 26%bv eq_refl); exact R26).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HSTK : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity.
assert (Ho16 : (x_s1 cx - x_sp0 cx) mod 16 = 0).
{ rewrite Zminus_mod, G1, G4. reflexivity. }
assert (G7' : x_fr cx mod 8 = 0).
{ pose proof (Z.div_mod (x_fr cx) 64 ltac:(lia)) as Hd. rewrite G7 in Hd.
  pose proof (Z.mod_pos_bound (x_fr cx) 8 ltac:(lia)). pose proof (Z.div_mod (x_fr cx) 8 ltac:(lia)). lia. }
unfold cfg_at. change (w64 (BASE + LO_S5LB)) with (Z_to_bv 64 (BASE + LO_S5LB)).
clearbody E.
(* 0x85148 bltz a0: a0 = lb << 56 is negative exactly when lb has bit 7 *)
psrr_branch_tok RUN BR HS SHOK s5b_span.
- (* taken: lb has bit 7; 0x85170 .. 0x85184: s4 = a0 = longl, a1 = 'L', a2 = 120, memset(longl, 'L', 120) *)
  assert (Hb7 : Z.land lb 128 <> 0).
  { rewrite E10 in Hc. cbn [sv_denot branch_taken] in Hc. unfold w64 in Hc. rewrite s5b_bltz in Hc by lia.
    apply Bool.negb_true_iff, Z.eqb_neq in Hc. exact Hc. }
  assert (Hlab : s5_lab (x_pl cx) f = Some SegModel.longl).
  { destruct (s5_label_cases (x_pl cx) f) as [(_ & Hl) | [(H0 & _) | (H0 & _)]];
    [exact Hl | exfalso; exact (Hb7 H0) | exfalso; exact (Hb7 H0)]. }
  clear Hc.
  paj_run_tok RUN HS HJ SHOK s5b_span; [s5b_awr_ro2|].
  assert (K1 : forall a, rdW W (ms_mem ms) a = rdW W mem a)
    by (apply (s5b_nowin SEGS E [s5b_lreg] (w_H W) mem (ms_mem ms)); [repeat constructor; cbn; lia | exact HFr]).
  clear HF HFr HG.
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md1 := d) in *; clearbody md1 end.
  pmkst HS.
  s5b_rreg2 HS (1%bv : bv 5) P1. s5b_rreg2 HS (2%bv : bv 5) P2. s5b_rreg2 HS (3%bv : bv 5) P3.
  s5b_rreg2 HS (4%bv : bv 5) P4. s5b_rreg2 HS (8%bv : bv 5) P8. s5b_rreg2 HS (9%bv : bv 5) P9.
  s5b_rreg2 HS (10%bv : bv 5) P10. s5b_rreg2 HS (11%bv : bv 5) P11. s5b_rreg2 HS (12%bv : bv 5) P12.
  s5b_rreg2 HS (18%bv : bv 5) P18. s5b_rreg2 HS (19%bv : bv 5) P19. s5b_rreg2 HS (20%bv : bv 5) P20.
  s5b_rreg2 HS (21%bv : bv 5) P21. s5b_rreg2 HS (22%bv : bv 5) P22. s5b_rreg2 HS (23%bv : bv 5) P23.
  s5b_rreg2 HS (24%bv : bv 5) P24. s5b_rreg2 HS (25%bv : bv 5) P25. s5b_rreg2 HS (27%bv : bv 5) P27.
  pose proof (EOBJ 6%nat longlA ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity)) as EL.
  change (A_OBJ 6) with 247%nat in EL.
  rewrite ECP in P1. rewrite EL in P10, P20.
  rewrite (EK 2%nat 2%bv eq_refl) in P2. rewrite (EK 3%nat 3%bv eq_refl) in P3. rewrite (EK 4%nat 4%bv eq_refl) in P4.
  rewrite (EK 8%nat 8%bv eq_refl) in P8. rewrite (EK 9%nat 9%bv eq_refl) in P9.
  rewrite (EK 18%nat 18%bv eq_refl), R18 in P18. rewrite (EK 19%nat 19%bv eq_refl), R19 in P19.
  rewrite (EK 21%nat 21%bv eq_refl), R21 in P21. rewrite (EK 22%nat 22%bv eq_refl), R22 in P22.
  rewrite (EK 23%nat 23%bv eq_refl), R23 in P23. rewrite (EK 24%nat 24%bv eq_refl), R24 in P24.
  rewrite (EK 25%nat 25%bv eq_refl), R25 in P25. rewrite (EK 27%nat 27%bv eq_refl), R27 in P27.
  assert (HspT : spZ (ms_regs ms) = x_sp0 cx + (x_s1 cx - x_sp0 cx)).
  { unfold spZ. rewrite P2, R2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
  assert (Hgp : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite P3, R3; exact Hgp0).
  assert (Htp : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite P4, R4; exact Htp0).
  pose proof (proj1 HJ) as HAR1.
  destruct (HLP ly S W (ms_mem ms) md1 HAR1) as (Ha0 & Ha1 & Ha2 & Ha3 & Ha4).
  assert (HinPG : forall a, longlA <= a < longlA + 120 -> inFP (ltoi_PG longlA) a).
  { intros a Ha. exists (longlA, longlA + LONGL_N). split; [left; reflexivity|]. cbn [fst snd]. unfold LONGL_N. lia. }
  eapply SRr_bind.
  { apply (aj_intrin_atS SEGS B LAWS pa_segs_low OSet (SIG SS___asan_memset) (AMEMSET fx) W (ms_regs ms) (ms_mem ms)
      STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx)
      [(LT_FCLS, x_fpos cx)] ly S md1 k longlA 76 120 (x_s1 cx - x_sp0 cx) (Z_to_bv 64 (BASE + 0x454)) HJ P10 P11 P12).
    - lia.
    - unfold longlA, A_LONGL. lia.
    - unfold longlA, A_LONGL. lia.
    - exact HspT.
    - exact Ho16.
    - lia.
    - rewrite Hes, HSTK. lia.
    - exact Hgp.
    - exact Htp.
    - exact P1.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - intros a Ha. split.
      + right; right; right; right. left. split; [exact (HinPG a Ha) | exact (HPGS a (HinPG a Ha))].
      + rewrite Hes. unfold longlA, A_LONGL in *. lia.
    - intros a Ha HFP _. apply PRW. exact (proj1 (HPGS a HFP)).
    - unfold amem_range, longlA, A_LONGL, kLowMemEnd. lia.
    - intros x Hx. apply Ha3. unfold LONGL_N. lia.
    - intros _. apply (s5b_hull_mono _ longlA LONGL_N 120); [apply Ha4; unfold LONGL_N; lia | unfold LONGL_N; lia].
    - exact I. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HPR2 & _ & HSET & HKEEP & _ & _).
  assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ s5b_X cx a -> rdW W mem2 a = rdW W mem a).
  { intros a Ha Hx. rewrite <- (K1 a). apply HKEEP; [exact Ha | intros Hl; apply Hx; left; exact Hl |].
    intros Hw. apply Hx. right; right. rewrite Hes in Hw. lia. }
  assert (QS : forall (r : bv 5) z, 0 <= z <= 31 -> acallee_saved z -> bv_unsigned r = z ->
    getr regs2 r = getr (ms_regs ms) r).
  { intros r z Hz0 Hz Hr. apply (s5b_pres_reg _ _ r z HPR2 Hz). apply bv_eq. rewrite Z_to_bv_unsigned, Hr.
    unfold bv_wrap. change (bv_modulus 5) with 32. apply Z.mod_small. lia. }
  assert (Q2 : getr regs2 2 = getr regs 2) by (rewrite (QS 2%bv 2); [exact P2 | lia | unfold acallee_saved; lia | reflexivity]).
  assert (Q3 : getr regs2 3 = getr regs 3) by (rewrite (QS 3%bv 3); [exact P3 | lia | unfold acallee_saved; lia | reflexivity]).
  assert (Q4 : getr regs2 4 = getr regs 4) by (rewrite (QS 4%bv 4); [exact P4 | lia | unfold acallee_saved; lia | reflexivity]).
  assert (Q8 : getr regs2 8 = getr regs 8) by (rewrite (QS 8%bv 8); [exact P8 | lia | unfold acallee_saved; lia | reflexivity]).
  assert (Q9 : getr regs2 9 = getr regs 9) by (rewrite (QS 9%bv 9); [exact P9 | lia | unfold acallee_saved; lia | reflexivity]).
  assert (Q18 : getr regs2 18 = w64 (Z.of_nat f)) by (rewrite (QS 18%bv 18); [exact P18 | lia | unfold acallee_saved; lia | reflexivity]).
  assert (Q19 : getr regs2 19 = w64 (-8)) by (rewrite (QS 19%bv 19); [exact P19 | lia | unfold acallee_saved; lia | reflexivity]).
  assert (Q20 : getr regs2 20 = w64 longlA) by (rewrite (QS 20%bv 20); [exact P20 | lia | unfold acallee_saved; lia | reflexivity]).
  assert (Q21 : getr regs2 21 = w64 (x_sh cx)) by (rewrite (QS 21%bv 21); [exact P21 | lia | unfold acallee_saved; lia | reflexivity]).
  assert (Q22 : getr regs2 22 = w64 (seg_spec.b2z (seg_spec.seg_ret (x_st cx f))))
    by (rewrite (QS 22%bv 22); [exact P22 | lia | unfold acallee_saved; lia | reflexivity]).
  assert (Q23 : getr regs2 23 = w64 t) by (rewrite (QS 23%bv 23); [exact P23 | lia | unfold acallee_saved; lia | reflexivity]).
  assert (Q24 : getr regs2 24 = w64 (seg_spec.seg_turn_at (x_pl cx) (x_p cx) f))
    by (rewrite (QS 24%bv 24); [exact P24 | lia | unfold acallee_saved; lia | reflexivity]).
  assert (Q25 : getr regs2 25 = w64 (x_nf cx)) by (rewrite (QS 25%bv 25); [exact P25 | lia | unfold acallee_saved; lia | reflexivity]).
  assert (Q27 : getr regs2 27 = w64 (seg_spec.seg_turn_np (x_pl cx) f))
    by (rewrite (QS 27%bv 27); [exact P27 | lia | unfold acallee_saved; lia | reflexivity]).
  pose proof (s5b_kept B MT IMGS HPG_RO HPG_PTR cx ly S W regs mem md k acc c m t f regs2 mem2 md2 HB HP HJ2 KEEP2
    Q2 Q3 Q4 Q8 Q9) as HP2.
  pose proof HP2 as ((((_ & _) & (_ & _ & HGI2) & _) & _) & _).
  pose proof s5_longl_len as HLL.
  assert (HL2 : S5_label B ly S (rdW W mem2) cx f longlA c m).
  { unfold S5_label. rewrite Hlab. rewrite HLL. cbn [Z.of_nat Pos.of_succ_nat].
    split; [unfold longlA, A_LONGL; lia|]. split.
    - split; [unfold longlA, A_LONGL; lia|]. split; [split|].
      + intros i Hi. rewrite length_app, HLL in Hi. cbn [length] in Hi.
        destruct (Nat.lt_ge_cases i 120) as [Hi1 | Hi1].
        * rewrite (HSET (Z.of_nat i) ltac:(lia)). rewrite app_nth1 by (rewrite HLL; exact Hi1).
          f_equal. symmetry. apply (repeat_spec 120 76). unfold SegModel.longl. apply nth_In.
          rewrite repeat_length. exact Hi1.
        * assert (Hi2 : i = 120%nat) by lia. subst i. rewrite app_nth2 by (rewrite HLL; lia). rewrite HLL.
          replace (120 - 120)%nat with 0%nat by lia. cbn [nth].
          pose proof (HGI2 0 ltac:(lia)) as H0. unfold LONGL_W in H0. rewrite Z.add_0_r in H0. exact H0.
      + intros Hin. unfold SegModel.longl in Hin. apply repeat_spec in Hin. lia.
      + rewrite HLL. apply (sa_tail_of_romtail SEGS (w_H W) mem2). exact HLT.
    - split; [lia|]. split.
      + right; right. split; [exact HLI|]. split; [exact HLP|].
        apply sa_pinned_tail_of_romtail. exact HLT.
      + split; [exact (HLP ly S W mem2 md2 (proj1 HJ2))|].
        assert (Hspan : seg_spec.cstr_span longlA SegModel.longl = 128) by (vm_compute; reflexivity).
        rewrite Hspan. pose proof (proj1 HJ2) as HAR2.
        pose proof (blk_off_imgP B ly S W mem2 md2 m _ HAR2 (proj1 HHm)) as Hmo.
        pose proof (blk_off_imgP B ly S W mem2 md2 c _ HAR2 (proj1 HHc)) as Hco.
        change (req_size seg_spec.SEG_M_SIZE) with 9236 in Hmo. change (req_size seg_spec.SEG_C_SIZE) with 16616 in Hco.
        unfold off_img in Hmo, Hco. unfold sa_disj, seg_spec.SEG_M_SIZE, seg_spec.SEG_C_SIZE, longlA, A_LONGL.
        split; [destruct Hmo; lia | destruct Hco; lia]. }
  change (SRr SEGS W (cfg_at SEGS (BASE + 0x454) regs2 mem2 md2) (lt_post B MT cx)).
  exact (s5b_join B MT IMGS HPG_RO HPG_PTR f HOTH HLST 0x454 cx ly S W regs2 mem2 md2 k acc c m t longlA
    (or_intror (or_introl eq_refl)) HB Hfrm Hf HP2 HL2 Q18 Q19 Q20 Q21 Q22 Q23 Q24 Q25 Q27).
- (* not taken: lb has no bit 7; 0x8514c beqz s10 *)
  assert (Hb7 : Z.land lb 128 = 0).
  { rewrite E10 in Hc. cbn [sv_denot branch_taken] in Hc. unfold w64 in Hc. rewrite s5b_bltz in Hc by lia.
    apply Bool.negb_false_iff, Z.eqb_eq in Hc. exact Hc. }
  clear Hc.
  paj_run_tok RUN HS HJ SHOK s5b_span; [s5b_awr_ro2|].
  assert (K1 : forall a, rdW W (ms_mem ms) a = rdW W mem a)
    by (apply (s5b_nowin SEGS E [s5b_lreg] (w_H W) mem (ms_mem ms)); [repeat constructor; cbn; lia | exact HFr]).
  clear HF HFr HG. rename ms into ms1.
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md1 := d) in *; clearbody md1 end.
  psrr_branch_tok RUN BR HS SHOK s5b_span.
  + (* beqz taken: lb = 0, no label; 0x8518c li s4,0, to the join at 0x85190 *)
    assert (Hlb0 : lb = 0).
    { rewrite branch_eq_U in Hc. unfold U in Hc. rewrite E26 in Hc. cbn [sv_denot] in Hc. unfold w64 in Hc.
      rewrite !unsigned_lit_small in Hc by lia. apply Z.eqb_eq in Hc. exact Hc. }
    assert (Hlab : s5_lab (x_pl cx) f = None).
    { destruct (s5_label_cases (x_pl cx) f) as [(H0 & _) | [(_ & _ & Hl) | (_ & H0 & _)]];
      [exfalso; exact (H0 Hb7) | exact Hl | exfalso; exact (H0 Hlb0)]. }
    clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK s5b_span 0x45c; [s5b_awr_ro2|].
    assert (K2 : forall a, rdW W (ms_mem ms) a = rdW W (ms_mem ms1) a)
      by (apply (s5b_nowin SEGS E [s5b_lreg] (w_H W) (ms_mem ms1) (ms_mem ms)); [repeat constructor; cbn; lia | exact HFr]).
    clear HF HFr HG.
    lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md2 := d) in *; clearbody md2 end.
    pmkst HS.
    s5b_rreg2 HS (2%bv : bv 5) P2. s5b_rreg2 HS (3%bv : bv 5) P3.
    s5b_rreg2 HS (4%bv : bv 5) P4. s5b_rreg2 HS (8%bv : bv 5) P8. s5b_rreg2 HS (9%bv : bv 5) P9.
    s5b_rreg2 HS (18%bv : bv 5) P18. s5b_rreg2 HS (19%bv : bv 5) P19. s5b_rreg2 HS (20%bv : bv 5) P20.
    s5b_rreg2 HS (21%bv : bv 5) P21. s5b_rreg2 HS (22%bv : bv 5) P22. s5b_rreg2 HS (23%bv : bv 5) P23.
    s5b_rreg2 HS (24%bv : bv 5) P24. s5b_rreg2 HS (25%bv : bv 5) P25. s5b_rreg2 HS (27%bv : bv 5) P27.
    rewrite (EK 2%nat 2%bv eq_refl) in P2. rewrite (EK 3%nat 3%bv eq_refl) in P3. rewrite (EK 4%nat 4%bv eq_refl) in P4.
    rewrite (EK 8%nat 8%bv eq_refl) in P8. rewrite (EK 9%nat 9%bv eq_refl) in P9.
    rewrite (EK 18%nat 18%bv eq_refl), R18 in P18. rewrite (EK 19%nat 19%bv eq_refl), R19 in P19.
    rewrite (EK 21%nat 21%bv eq_refl), R21 in P21. rewrite (EK 22%nat 22%bv eq_refl), R22 in P22.
    rewrite (EK 23%nat 23%bv eq_refl), R23 in P23. rewrite (EK 24%nat 24%bv eq_refl), R24 in P24.
    rewrite (EK 25%nat 25%bv eq_refl), R25 in P25. rewrite (EK 27%nat 27%bv eq_refl), R27 in P27.
    pose proof (s5b_kept B MT IMGS HPG_RO HPG_PTR cx ly S W regs mem md k acc c m t f (ms_regs ms) (ms_mem ms) md2
      HB HP HJ (fun a _ _ => eq_trans (K2 a) (K1 a)) P2 P3 P4 P8 P9) as HP2.
    assert (HL2 : S5_label B ly S (rdW W (ms_mem ms)) cx f 0 c m).
    { unfold S5_label. rewrite Hlab. split; [lia|]. split; [cbn [sa_ostr]; reflexivity | exact I]. }
    change (SRr SEGS W (cfg_at SEGS (BASE + 0x45c) (ms_regs ms) (ms_mem ms) md2) (lt_post B MT cx)).
    exact (s5b_join B MT IMGS HPG_RO HPG_PTR f HOTH HLST 0x45c cx ly S W (ms_regs ms) (ms_mem ms) md2 k acc c m t 0
      (or_intror (or_intror eq_refl)) HB Hfrm Hf HP2 HL2 P18 P19 P20 P21 P22 P23 P24 P25 P27).
  + (* beqz not taken: 1 <= lb < 128; 0x85150 .. 0x85168: snprintf(label = FR + 96, 40, LIT_LABEL, lb) *)
    assert (Hlbn : lb <> 0).
    { rewrite branch_eq_U in Hc. unfold U in Hc. rewrite E26 in Hc. cbn [sv_denot] in Hc. unfold w64 in Hc.
      rewrite !unsigned_lit_small in Hc by lia. apply Z.eqb_neq in Hc. exact Hc. }
    clear Hc.
    assert (Hlb128 : 1 <= lb < 128) by (pose proof (s5b_bit7 lb Hlb Hb7); lia).
    destruct (s5b_glue lb Hlb128) as (HTXT & HTB & HTL).
    assert (Hlab : s5_lab (x_pl cx) f = Some (SegModel.fmt SegModel.F_label [SegModel.AI lb])).
    { rewrite <- (s5b_label_len lb Hlb128).
      destruct (s5_label_cases (x_pl cx) f) as [(H0 & _) | [(_ & H0 & _) | (_ & _ & Hl)]];
      [exfalso; exact (H0 Hb7) | exfalso; exact (Hlbn H0) | exact Hl]. }
    set (T := SegModel.fmt SegModel.F_label [SegModel.AI lb]) in *.
    destruct (s5b_snlen T ltac:(lia)) as (HSL1 & HSB1).
    paj_run_tok RUN HS HJ SHOK s5b_span; [s5b_awr_ro2|].
    assert (K2 : forall a, rdW W (ms_mem ms) a = rdW W (ms_mem ms1) a)
      by (apply (s5b_nowin SEGS E [s5b_lreg] (w_H W) (ms_mem ms1) (ms_mem ms)); [repeat constructor; cbn; lia | exact HFr]).
    clear HF HFr HG.
    lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md2 := d) in *; clearbody md2 end.
    pmkst HS.
    s5b_rreg2 HS (1%bv : bv 5) P1. s5b_rreg2 HS (2%bv : bv 5) P2. s5b_rreg2 HS (3%bv : bv 5) P3.
    s5b_rreg2 HS (4%bv : bv 5) P4. s5b_rreg2 HS (8%bv : bv 5) P8. s5b_rreg2 HS (9%bv : bv 5) P9.
    s5b_rreg2 HS (10%bv : bv 5) P10. s5b_rreg2 HS (11%bv : bv 5) P11. s5b_rreg2 HS (12%bv : bv 5) P12.
    s5b_rreg2 HS (13%bv : bv 5) P13.
    s5b_rreg2 HS (18%bv : bv 5) P18. s5b_rreg2 HS (19%bv : bv 5) P19. s5b_rreg2 HS (20%bv : bv 5) P20.
    s5b_rreg2 HS (21%bv : bv 5) P21. s5b_rreg2 HS (22%bv : bv 5) P22. s5b_rreg2 HS (23%bv : bv 5) P23.
    s5b_rreg2 HS (24%bv : bv 5) P24. s5b_rreg2 HS (25%bv : bv 5) P25. s5b_rreg2 HS (27%bv : bv 5) P27.
    pose proof (EOBJ 5%nat 135136 ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity)) as EF5.
    change (A_OBJ 5) with 246%nat in EF5.
    rewrite ECP in P1. rewrite E32 in P10, P20. rewrite EF5 in P12. rewrite E26 in P13.
    rewrite (EK 2%nat 2%bv eq_refl) in P2. rewrite (EK 3%nat 3%bv eq_refl) in P3. rewrite (EK 4%nat 4%bv eq_refl) in P4.
    rewrite (EK 8%nat 8%bv eq_refl) in P8. rewrite (EK 9%nat 9%bv eq_refl) in P9.
    rewrite (EK 18%nat 18%bv eq_refl), R18 in P18. rewrite (EK 19%nat 19%bv eq_refl), R19 in P19.
    rewrite (EK 21%nat 21%bv eq_refl), R21 in P21. rewrite (EK 22%nat 22%bv eq_refl), R22 in P22.
    rewrite (EK 23%nat 23%bv eq_refl), R23 in P23. rewrite (EK 24%nat 24%bv eq_refl), R24 in P24.
    rewrite (EK 25%nat 25%bv eq_refl), R25 in P25. rewrite (EK 27%nat 27%bv eq_refl), R27 in P27.
    assert (KT : forall a, rdW W (ms_mem ms) a = rdW W mem a) by (intros a; exact (eq_trans (K2 a) (K1 a))).
    pose proof (s5b_kept B MT IMGS HPG_RO HPG_PTR cx ly S W regs mem md k acc c m t f (ms_regs ms) (ms_mem ms) md2
      HB HP HJ (fun a _ _ => KT a) P2 P3 P4 P8 P9) as HPT.
    pose proof HPT as ((((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSHT) & HIMGT & _) & _) & _).
    pose proof HIMGT as (HROT & (_ & _ & HLFT & _ & _ & _ & _ & _ & (Hg1T & Hg2T) & _) & _).
    destruct Hg2T as (cval & Hcval).
    pose proof (proj1 HJ) as HAR1.
    assert (HspT : spZ (ms_regs ms) = x_sp0 cx + (x_s1 cx - x_sp0 cx)).
    { unfold spZ. rewrite P2, R2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
    assert (Hgp : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite P3, R3; exact Hgp0).
    assert (Htp : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite P4, R4; exact Htp0).
    pose proof (HSNP_FAKE ly S W (ms_mem ms) md2 HAR1) as Hfake.
    pose proof (s5b_fake_le ly S W (ms_mem ms) md2 LT_FCLS (x_fpos cx) HAR1 HinF) as HFd. rewrite EF in HFd.
    assert (HL24 : Z.of_nat (length LLVMFuzzerTestOneInput_c.LIT_LABEL) = 24) by (vm_compute; reflexivity).
    destruct (HLFT LLVMFuzzerTestOneInput_c.LIT_LABEL ltac:(apply in_or_app; left; left; reflexivity)) as (HLl & _).
    pose proof (HSNP_LIT LLVMFuzzerTestOneInput_c.LIT_LABEL ltac:(left; reflexivity)) as HLIT.
    rewrite s5b_lit_label in HLl, HLIT. rewrite HL24 in HLIT.
    destruct HLl as (_ & ((HLz & _) & _) & HLpin & _ & _).
    destruct (HLpin ly S W (ms_mem ms) md2 HAR1) as (_ & _ & HLam & HLra & HLhv).
    rewrite HL24 in HLam, HLra, HLhv.
    assert (A3 : argZ (ms_regs ms) 3 = lb).
    { change (argZ (ms_regs ms) 3) with (bv_unsigned (getr (ms_regs ms) (13%bv : bv 5))). rewrite P13. unfold w64.
      apply unsigned_lit_small. lia. }
    set (d := x_fr cx + FO_LABEL) in *.
    unfold lt_post.
    eapply (srr_after_callF (fx := fx) SEGS W _ (Z_to_bv 64 (BASE + 0x438))
      (fun ly2 S2 W2 regs2 mem2 md3 => ly2 = ly /\ S2 = S /\ W2 = W /\
        ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx)
          (x_mem cx) (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem2 md3 k /\
        aregs_preserved (ms_regs ms) regs2 /\
        (forall i, 0 <= i < Z.of_nat (length T) + 1 -> rdW W mem2 (d + i) = Some (nth (Z.to_nat i) (T ++ [0]) 0)) /\
        (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + 40) -> ~ (x_s1 cx - 8192 <= a < x_s1 cx) ->
          rdW W mem2 a = rdW W (ms_mem ms) a))).
    { eapply SRr_mono.
      { apply (s5b_aj_snprintf_atSF SEGS B LAWS pa_segs_low snp_lo snp_hi snp_cr
          (SIG SS___interceptor_trampoline_snprintf) gotwA guardA (ASNPRINTF fx)
          W (ms_regs ms) (ms_mem ms) STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx)
          (x_W cx) (x_mem cx) (x_md cx) [(LT_FCLS, x_fpos cx)] ly S md2 k d 40 135136 T (x_s1 cx - x_sp0 cx)
          (Z_to_bv 64 (BASE + 0x438)) cval HJ P10 P11 P12).
        - lia.
        - unfold d, FO_LABEL. lia.
        - unfold d, FO_LABEL. lia.
        - exact HspT.
        - exact Ho16.
        - lia.
        - unfold RtPFSeg.SEG_SNP_K. rewrite Hes, HSTK. lia.
        - exact Hgp.
        - exact Htp.
        - exact P1.
        - apply ret_ok_codeptr_v; [lia | reflexivity].
        - intros a Ha. split.
          + right; right; right; left. exists LT_FCLS, (x_fpos cx). split; [left; reflexivity|]. left.
            unfold in_zr. cbn [fst snd]. rewrite EF. change (fs_frame_bytes LT_FCLS) with 512. unfold d, FO_LABEL in Ha. lia.
          + unfold RtPFSeg.SEG_SNP_K. rewrite Hes. unfold d, FO_LABEL in Ha. lia.
        - intros a Ha (r & Hr & Hlo) _. exfalso. destruct Hr as [<- | []]. cbn [fst snd] in Hlo.
          unfold longlA, A_LONGL, LONGL_N, d, FO_LABEL in *. destruct G8; lia.
        - unfold amem_range, d, FO_LABEL, kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd in *. destruct G9; lia.
        - apply (s5b_lab_addressable _ (x_fr cx) d 40); [lia | exact G7'
            | exact HSHT | unfold d, FO_LABEL; lia | unfold d, FO_LABEL; lia].
        - apply (shadow_hull_vis_of_frame SEGS B LAWS ly S W (ms_mem ms) md2 LT_FCLS (x_fpos cx) d 40 HAR1 HinF);
          [rewrite EF; unfold d, FO_LABEL; lia | rewrite EF; change (fs_frame_bytes LT_FCLS) with 512; unfold d, FO_LABEL; lia | lia].
        - intros a Hrom Ho He. apply HROT; [left; exact Hrom | exact Ho | exact He].
        - eapply Forall_impl; [|exact HSNP_CR]. intros r (H1 & H2 & H3). split; lia.
        - eapply Forall_impl; [|exact HSNP_CR]. intros r (H1 & H2 & H3). unfold RtPFShared.snp_out.
          rewrite HspT, HSL1. unfold RtPFSeg.SEG_SNP_K. rewrite Hes.
          repeat (apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; unfold d, FO_LABEL; lia|]); apply Forall_nil.
        - exact Hg1T.
        - exact Hcval.
        - unfold gotwA. lia. - unfold gotwA. lia. - unfold guardA. lia. - unfold guardA. lia.
        - unfold RtPFShared.snp_out. rewrite HspT, HSL1. unfold RtPFSeg.SEG_SNP_K. rewrite Hes.
          repeat (apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; unfold d, FO_LABEL, gotwA in *; destruct G8; lia|]);
          apply Forall_nil.
        - unfold RtPFShared.snp_out. rewrite HspT, HSL1. unfold RtPFSeg.SEG_SNP_K. rewrite Hes.
          repeat (apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; unfold d, FO_LABEL, guardA in *; destruct G8; lia|]);
          apply Forall_nil.
        - lia.
        - exists LLVMFuzzerTestOneInput_c.LIT_LABEL, s5b_qs, [RtPFPf.AInt lb].
          split.
          { split; [lia|]. split.
            - intros i Hi. pose proof (HLz (Z.to_nat i)) as Hzi. rewrite Z2Nat.id in Hzi by lia. apply Hzi.
              rewrite length_app. cbn [length]. lia.
            - split.
              + unfold RtPFShared.snp_out. rewrite HspT, HSL1, HL24. unfold RtPFSeg.SEG_SNP_K. rewrite Hes.
                repeat (apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; unfold d, FO_LABEL in *; destruct G8; lia|]);
                apply Forall_nil.
              + rewrite HL24. split; [exact HLam|]. split; [exact HLra | apply HLhv; lia]. }
          split; [exact s5b_parse|]. split; [exact s5b_pk|].
          split; [cbn [map RtPFShared.pf_args_asan RtPFShared.pf_arg_asan]; rewrite A3; split; [split; [lia | reflexivity] | exact I]|].
          split; [exact HTXT|]. split; [exact (s5b_prec lb)|].
          split; [lia|]. split; [rewrite HL24; lia|].
          split; [cbn; exact I|]. split; [intros H0; rewrite H0 in HL24; discriminate HL24 | cbn; exact I].
        - lia.
        - apply (RtPFSx.dest_off_globals_of_fake (ly_F ly) d _ snp_lo snp_hi Hfake). unfold d, FO_LABEL. lia.
        - exact Hfrm. }
      cbv beta. intros W2 c2 _ (-> & fx1 & regs2 & mem2 & md3 & Hfx & -> & HJ2 & HPR2 & _ & Hby & Hkeep & _ & _).
      exists fx1, ly, S, regs2, mem2, md3. split; [exact Hfx|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HPR2|].
      split.
      - rewrite HSL1, HSB1 in Hby. exact Hby.
      - intros a Ha H1 H2. apply Hkeep; [exact Ha | exact H1 |].
        unfold RtPFSeg.SEG_SNP_K. rewrite Hes. intros Hw. apply H2. lia. }
    intros fx1 ly2 S2 W2 regs2 mem2 md3 _ Hfx (-> & -> & -> & HJ2 & HPR2 & Hby & Hkeep).
    assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ s5b_X cx a -> rdW W mem2 a = rdW W mem a).
    { intros a Ha Hx. rewrite <- (KT a). apply Hkeep; [exact Ha | | ]; intros Hw; apply Hx; unfold s5b_X;
      [right; left; unfold d, FO_LABEL in Hw; lia | right; right; exact Hw]. }
    assert (QS : forall (r : bv 5) z, 0 <= z <= 31 -> acallee_saved z -> bv_unsigned r = z ->
      getr regs2 r = getr (ms_regs ms) r).
    { intros r z Hz0 Hz Hr. apply (s5b_pres_reg _ _ r z HPR2 Hz). apply bv_eq. rewrite Z_to_bv_unsigned, Hr.
      unfold bv_wrap. change (bv_modulus 5) with 32. apply Z.mod_small. lia. }
    assert (Q2 : getr regs2 2 = getr regs 2) by (rewrite (QS 2%bv 2); [exact P2 | lia | unfold acallee_saved; lia | reflexivity]).
    assert (Q3 : getr regs2 3 = getr regs 3) by (rewrite (QS 3%bv 3); [exact P3 | lia | unfold acallee_saved; lia | reflexivity]).
    assert (Q4 : getr regs2 4 = getr regs 4) by (rewrite (QS 4%bv 4); [exact P4 | lia | unfold acallee_saved; lia | reflexivity]).
    assert (Q8 : getr regs2 8 = getr regs 8) by (rewrite (QS 8%bv 8); [exact P8 | lia | unfold acallee_saved; lia | reflexivity]).
    assert (Q9 : getr regs2 9 = getr regs 9) by (rewrite (QS 9%bv 9); [exact P9 | lia | unfold acallee_saved; lia | reflexivity]).
    assert (Q18 : getr regs2 18 = w64 (Z.of_nat f)) by (rewrite (QS 18%bv 18); [exact P18 | lia | unfold acallee_saved; lia | reflexivity]).
    assert (Q19 : getr regs2 19 = w64 (-8)) by (rewrite (QS 19%bv 19); [exact P19 | lia | unfold acallee_saved; lia | reflexivity]).
    assert (Q20 : getr regs2 20 = w64 d) by (rewrite (QS 20%bv 20); [exact P20 | lia | unfold acallee_saved; lia | reflexivity]).
    assert (Q21 : getr regs2 21 = w64 (x_sh cx)) by (rewrite (QS 21%bv 21); [exact P21 | lia | unfold acallee_saved; lia | reflexivity]).
    assert (Q22 : getr regs2 22 = w64 (seg_spec.b2z (seg_spec.seg_ret (x_st cx f))))
      by (rewrite (QS 22%bv 22); [exact P22 | lia | unfold acallee_saved; lia | reflexivity]).
    assert (Q23 : getr regs2 23 = w64 t) by (rewrite (QS 23%bv 23); [exact P23 | lia | unfold acallee_saved; lia | reflexivity]).
    assert (Q24 : getr regs2 24 = w64 (seg_spec.seg_turn_at (x_pl cx) (x_p cx) f))
      by (rewrite (QS 24%bv 24); [exact P24 | lia | unfold acallee_saved; lia | reflexivity]).
    assert (Q25 : getr regs2 25 = w64 (x_nf cx)) by (rewrite (QS 25%bv 25); [exact P25 | lia | unfold acallee_saved; lia | reflexivity]).
    assert (Q27 : getr regs2 27 = w64 (seg_spec.seg_turn_np (x_pl cx) f))
      by (rewrite (QS 27%bv 27); [exact P27 | lia | unfold acallee_saved; lia | reflexivity]).
    pose proof (s5b_kept B MT IMGS HPG_RO HPG_PTR cx ly S W regs mem md k acc c m t f regs2 mem2 md3 HB HP HJ2 KEEP2
      Q2 Q3 Q4 Q8 Q9) as HP2.
    pose proof HP2 as ((((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSH2) & _) & _) & _).
    pose proof (proj1 HJ2) as HAR2.
    destruct (al_frames _ _ LAWS ly S W mem2 md3 LT_FCLS (x_fpos cx) HAR2 HinF) as (_ & _ & HFP2 & _).
    rewrite EF in HFP2. change (fs_frame_bytes LT_FCLS) with 512 in HFP2.
    assert (HL2 : S5_label B ly S (rdW W mem2) cx f d c m).
    { unfold S5_label. rewrite Hlab. split; [unfold d, FO_LABEL; lia|]. split.
      - split; [unfold d, FO_LABEL; lia|]. split; [split|].
        + intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
          rewrite (Hby (Z.of_nat i) ltac:(lia)). rewrite Nat2Z.id. reflexivity.
        + intros H0. rewrite Forall_forall in HTB. specialize (HTB 0 H0). lia.
        + intros x Hx. apply (aview_some_of_apresent SEGS).
          assert (Hxr : x_fr cx <= x < x_fr cx + 512).
          { pose proof (Z.mod_pos_bound (d + Z.of_nat (length T)) 8 ltac:(lia)). unfold d, FO_LABEL in *. lia. }
          exact (proj1 (HFP2 x Hxr)).
      - split; [lia|]. split.
        + right; left. exists LT_FCLS, (x_fpos cx). split; [exact HinF|]. split; [unfold LT_FCLS; lia|].
          rewrite EF. change (fs_frame_bytes LT_FCLS) with 512. unfold d, FO_LABEL. lia.
        + split.
          * split; [unfold d, FO_LABEL; lia|]. split; [unfold d, FO_LABEL; lia|]. split.
            { unfold amem_range, d, FO_LABEL, kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd in *. destruct G9; lia. }
            split.
            { apply (s5b_lab_addressable _ (x_fr cx) d); [lia | exact G7'
                | exact HSH2 | unfold d, FO_LABEL; lia | unfold d, FO_LABEL; lia]. }
            intros _. apply (shadow_hull_vis_of_frame SEGS B LAWS ly S W mem2 md3 LT_FCLS (x_fpos cx) d _ HAR2 HinF);
            [rewrite EF; unfold d, FO_LABEL; lia | rewrite EF; change (fs_frame_bytes LT_FCLS) with 512; unfold d, FO_LABEL; lia | lia].
          * pose proof (sep_block_frame SEGS B LAWS ly S W mem2 md3 m _ LT_FCLS (x_fpos cx) HAR2 (proj1 HHm) HinF) as Hsm.
            pose proof (sep_block_frame SEGS B LAWS ly S W mem2 md3 c _ LT_FCLS (x_fpos cx) HAR2 (proj1 HHc) HinF) as Hsc.
            rewrite EF in Hsm, Hsc. change (fs_frame_bytes LT_FCLS) with 512 in Hsm, Hsc.
            change (req_size seg_spec.SEG_M_SIZE) with 9236 in Hsm. change (req_size seg_spec.SEG_C_SIZE) with 16616 in Hsc.
            unfold zdisjoint in Hsm, Hsc. cbn [fst snd] in Hsm, Hsc.
            unfold sa_disj, seg_spec.cstr_span, seg_spec.SEG_M_SIZE, seg_spec.SEG_C_SIZE.
            pose proof (Z.mod_pos_bound (- (d + Z.of_nat (length T) + 1)) 8 ltac:(lia)).
            unfold d, FO_LABEL in *. split; [destruct Hsm; lia | destruct Hsc; lia]. }
    change (SRr SEGS W (@cfg_at fx1 SEGS (BASE + 0x438) regs2 mem2 md3) (@lt_post fx1 rc SK PI B MT cx)).
    exact (@s5b_join fx1 rc SK PI B MT IMGS HPG_RO HPG_PTR f HOTH HLST 0x438 cx ly S W regs2 mem2 md3 k acc c m t d
      (or_introl eq_refl) HB (fxrel_frm0 fx fx1 Hfrm Hfx) Hf HP2 HL2 Q18 Q19 Q20 Q21 Q22 Q23 Q24 Q25 Q27).
Qed.

End s5b_me.
End s5b_mf.
End s5b_md.
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
Variable snp_lo snp_hi : Z.
Variable snp_cr : list (Z * Z).
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis IMGS : s10_img.
Hypothesis BSYM : AF0m.SegBSyms B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis PRW : prog_rw SEGS B.
Hypothesis VOBJS : seg_val_objs.
Hypothesis SIGP : seg_sig_prog.
Hypothesis HPGS : forall a, inFP (ltoi_PG longlA) a ->
  Exists (in_zr a) (as_prog_static B) /\ in_img SEGS a.
Hypothesis HPG_RO : forall a, inFP (ltoi_PG longlA) a -> ~ in_roP SEGS RLO_A RHI_A a.
Hypothesis HPG_PTR : forall a p,
  ((exists i, (i < 5)%nat /\ a = wordsA + 8 * Z.of_nat i) \/
   (exists i, (i < pin_spec.CAT_N)%nat /\ a = pin_spec.row_addr catA i)) ->
  rdword (fun x => option_map (fun b : byte => bv_unsigned b) (seg_rom SEGS (Z_to_bv 64 x))) a = Some p ->
  p + 65536 <= longlA.
Hypothesis AMEMCPY : forall fx0 : YK11.FPState,
  @aintrin_realizes fx0 rc SEGS B OCpy (SIG SS___asan_memcpy).
Hypothesis AMEMSET : forall fx0 : YK11.FPState,
  @aintrin_realizes fx0 rc SEGS B OSet (SIG SS___asan_memset).
Hypothesis AFREE4 : forall fx0 : YK11.FPState, @afree04_rule fx0 rc SK SEGS B MT.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState,
  @RtPFSeg.seg_asnprintf_realizes fx0 rc SEGS B snp_lo snp_hi snp_cr
    (SIG SS___interceptor_trampoline_snprintf) gotwA guardA.
Hypothesis HSNP_LIT : forall x, In x LLVMFuzzerTestOneInput_c.LTOI_LITS ->
  snp_lo <= seg_litA_fz x /\ seg_litA_fz x + Z.of_nat (length x) + 1 <= gotwA.
Hypothesis HSNP_CR : Forall (fun r => snp_lo <= fst r /\ 0 <= snd r /\ fst r + snd r <= snp_hi) snp_cr.
Hypothesis HSNP_LO : 0 <= snp_lo.
Hypothesis HSNP_CEIL : snp_hi <= alloc_ceiling.
Hypothesis HSNP_FAKE : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> snp_hi <= ly_F ly.
Hypothesis HM_FILE : forall fx0 : YK11.FPState,
  @m_file_c.m_file_contract fx0 rc SK SEGS B (BASE + AF_m_file) STK_m_file RLO_A RHI_A seg_litA_fz
    wordsA rolesA catA gotwA guardA.
Hypothesis HPARSE_FILE : forall fx0 : YK11.FPState,
  @reac_segconf_parse_file_c.reac_segconf_parse_file_contract fx0 rc SK SEGS B
    (BASE + AF_reac_segconf_parse_file) STK_reac_segconf_parse_file RLO_A RHI_A seg_litA_rc catA gotwA guardA.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* 0x85148 .. 0x851a4 / 0x851f0: the three label arms and the join *)
Lemma s5_label : forall f, S5A_OTH B MT f -> S5A_LST B MT f -> S5_LB_stmt B MT f.
Proof using All.
intros f HO HL. eapply (s5b_main B MT snp_lo snp_hi snp_cr); eassumption.
Qed.

End eb.
End fb.
End db.

(* ======================================== piece c ======================================== *)

(* ================================ L3's model facts (SegModel and seg_spec only) ================================ *)
(* nfiles = 1 + in[2] % 4 (LLVMFuzzerTestOneInput_s02.v's lt_nfiles_range, which this file does not import) *)
Lemma s5c_nfiles : forall pl, 1 <= seg_spec.seg_nfiles pl <= 4.
Proof.
intros pl. unfold seg_spec.seg_nfiles, seg_spec.seg_files, seg_spec.seg_pay, SegModel.decode.
destruct (SegModel.fuzz_u8 (seg_spec.seg_in pl)) as [b0 i1].
destruct (SegModel.fuzz_u8 i1) as [fl i2]. destruct (SegModel.fuzz_u8 i2) as [b2 i3].
cbn [SegModel.p_files]. rewrite s5_dec_files_length.
pose proof (Z.mod_pos_bound b2 4 ltac:(lia)) as H. rewrite Z2Nat.id by lia. lia.
Qed.
(* the turn's text is at most 65,535 bytes: it is a prefix of the n' = min(len, left) bytes taken, len a u16
   (stated in Z: lia cannot read a nat literal of this size, which Rocq abstracts as Nat.of_num_uint) *)
Lemma s5c_txt_len : forall pl f, Z.of_nat f < seg_spec.seg_nfiles pl ->
  Z.of_nat (length (seg_spec.seg_txt pl f)) <= 65535.
Proof.
intros pl f Hf. destruct (s5_txt_firstn pl f Hf) as (_ & H1 & _).
assert (EL : forall x, Z.land x 65535 = x mod 2 ^ 16)
  by (intros x; change 65535 with (Z.ones 16); apply Z.land_ones; lia).
assert (Hl : 0 <= seg_spec.seg_turn_len pl f <= 65535).
{ unfold seg_spec.seg_turn_len, SegModel.fuzz_u16.
  destruct (SegModel.fuzz_u8 (snd (SegModel.fuzz_u8 (seg_spec.seg_cur pl f)))) as [lo i1].
  destruct (SegModel.fuzz_u8 i1) as [hi i2]. cbn [fst]. rewrite EL.
  pose proof (Z.mod_pos_bound (Z.lor lo (Z.shiftl hi 8)) (2 ^ 16) ltac:(lia)) as HM. lia. }
assert (H2 : Z.of_nat (Z.to_nat (seg_spec.seg_turn_np pl f)) <= seg_spec.seg_turn_len pl f).
{ unfold seg_spec.seg_turn_np. rewrite s5_take_fst, length_firstn, Nat2Z.id, !Nat2Z.inj_min.
  rewrite Z2Nat.id by lia. lia. }
apply Nat2Z.inj_le in H1. lia.
Qed.
(* the turn's text has no NUL: it is a fuzz_str, cut at the first NUL *)
Lemma s5c_txt_nulfree : forall pl f, Z.of_nat f < seg_spec.seg_nfiles pl ->
  SegModel.nulfree (seg_spec.seg_txt pl f).
Proof. intros pl f Hf. rewrite (s5_txt_eq pl f Hf). apply s5_cut_nul_nulfree. Qed.
(* the input cursor of a turn: a suffix of the input bytes *)
Lemma s5c_tail_len : forall pl f, (length (seg_spec.seg_turn_tail pl f) <= length pl)%nat.
Proof.
intros pl f. pose proof (s5_sfx_len _ _ (s5_tail_sfx pl f)) as H.
unfold seg_spec.seg_in, seg_spec.zs in H. rewrite length_map in H. exact H.
Qed.

(* m_file keeps the two counts the mconf encoding bounds (mconf_encp: n <= 32, n_kept <= 8): m_header adds a
   segment only below 32 (SegModel.v H:183-186) and m_refuse keeps a refusal only below 8 (H:101-111) *)
Definition s5c_inv (mc : SegModel.mconf) : Prop :=
  (length (SegModel.mc_seg mc) <= 32)%nat /\ (length (SegModel.mc_kept mc) <= 8)%nat.
Lemma s5c_upd_nth_len : forall {A} i (g : A -> A) l, length (SegModel.upd_nth i g l) = length l.
Proof. intros A i g l. revert i. induction l as [|x l IH]; intros [|i]; cbn; try reflexivity; rewrite IH; reflexivity. Qed.
Lemma s5c_inv_refuse : forall c line knock, s5c_inv c -> s5c_inv (SegModel.m_refuse c line knock).
Proof.
intros c line knock [H1 H2]. unfold SegModel.m_refuse. cbv zeta. unfold s5c_inv.
cbn [SegModel.mc_seg SegModel.mc_kept]. split; [exact H1|].
destruct (Z.of_nat (length (SegModel.mc_kept c)) <? 8) eqn:E; [|exact H2].
apply Z.ltb_lt in E. rewrite length_app. cbn [length]. lia.
Qed.
Lemma s5c_inv_upd : forall c i g, s5c_inv c -> s5c_inv (SegModel.m_upd c i g).
Proof.
intros c i g [H1 H2]. unfold SegModel.m_upd, SegModel.m_set_segs, s5c_inv.
cbn [SegModel.mc_seg SegModel.mc_kept]. rewrite s5c_upd_nth_len. split; assumption.
Qed.
Lemma s5c_inv_mk : forall c o r g rd, s5c_inv c ->
  s5c_inv (SegModel.MConf (SegModel.mc_seg c) o r (SegModel.mc_kept c) g rd).
Proof. intros c o r g rd H. exact H. Qed.
Lemma s5c_inv_add : forall c x, s5c_inv c -> (32 <=? length (SegModel.mc_seg c))%nat = false ->
  s5c_inv (SegModel.m_set_segs c (SegModel.mc_seg c ++ [x])).
Proof.
intros c x [H1 H2] H3. apply Nat.leb_gt in H3. unfold SegModel.m_set_segs, s5c_inv.
cbn [SegModel.mc_seg SegModel.mc_kept]. rewrite length_app. cbn [length]. split; lia.
Qed.
Lemma s5c_header_inv : forall c l line, s5c_inv c -> s5c_inv (fst (SegModel.m_header c l line)).
Proof.
intros c l line H. unfold SegModel.m_header. cbv zeta.
destruct (SegModel.memchr l SegModel.RBR) as [ci|]; [|apply s5c_inv_refuse, H].
repeat match goal with
       | |- context [if ?b then _ else _] => let E := fresh "E" in destruct b eqn:E
       | |- context [SegModel.m_find ?a ?b] => destruct (SegModel.m_find a b)
       end; cbn [fst];
  first [ apply s5c_inv_refuse; first [exact H | apply s5c_inv_mk; exact H]
        | apply s5c_inv_upd; first [exact H | apply s5c_inv_refuse; exact H]
        | apply s5c_inv_add; [exact H | assumption] ].
Qed.
Lemma s5c_key_inv : forall c g l line, s5c_inv c -> s5c_inv (SegModel.m_key c g l line).
Proof.
intros c g l line H. unfold SegModel.m_key. cbv zeta.
destruct (SegModel.memchr l SegModel.EQ); [|apply s5c_inv_refuse, H]. destruct g; [|apply s5c_inv_refuse, H].
repeat match goal with
       | |- context [if ?b then _ else _] => destruct b
       | |- context [SegModel.h_role_word ?a] => destruct (SegModel.h_role_word a)
       | |- context [SegModel.cat_row ?a] => destruct (SegModel.cat_row a)
       end; first [apply s5c_inv_upd, H | apply s5c_inv_refuse, H].
Qed.
Lemma s5c_line_inv : forall st n l, s5c_inv (fst st) -> s5c_inv (fst (SegModel.m_line st n l)).
Proof.
intros [c cur] n l H. cbn [fst] in H. unfold SegModel.m_line. cbv beta iota zeta.
destruct (512 <=? length l)%nat; [cbn [fst]; apply s5c_inv_refuse, H|].
destruct (SegModel.h_strip (SegModel.h_cut_comment l)) as [|b s]; [exact H|].
destruct (b =? SegModel.LBR); [apply s5c_header_inv, H | cbn [fst]; apply s5c_key_inv, H].
Qed.
Lemma s5c_lines_inv : forall ls st n, s5c_inv (fst st) -> s5c_inv (fst (SegModel.m_lines st n ls)).
Proof.
induction ls as [|l r IH]; intros st n H; cbn [SegModel.m_lines]; [exact H|]. apply IH, s5c_line_inv, H.
Qed.
Lemma s5c_file_inv : forall mc s lab, s5c_inv mc -> s5c_inv (SegModel.m_file mc s lab).
Proof.
intros mc s lab H. unfold SegModel.m_file. cbv zeta. apply s5c_lines_inv. cbn [fst]. apply s5c_inv_mk. exact H.
Qed.
(* the bytes of the mconf block m_file may write (m_file_c.M_FILE_FP) lie in the block *)
Lemma s5c_fp_in : forall m k0 mc' a, s5c_inv mc' -> inFP (m_file_c.M_FILE_FP m k0 mc') a ->
  m <= a < m + seg_spec.SEG_M_SIZE.
Proof.
intros m k0 mc' a [H1 H2] (r & Hr & Hlo & Hhi). unfold m_file_c.M_FILE_FP in Hr. cbn [In] in Hr.
unfold seg_spec.mseg_addr, seg_spec.kept_addr, seg_spec.MC_N, seg_spec.MC_REFUSED, seg_spec.MC_KEPT,
  seg_spec.MC_KEPT_LEN, seg_spec.MC_KNOCK, seg_spec.MC_NKEPT, seg_spec.MC_READING, seg_spec.MSEG_SIZE,
  seg_spec.SEG_M_SIZE in *.
repeat (destruct Hr as [<- | Hr]; [cbn [fst snd] in Hlo, Hhi; lia|]). destruct Hr.
Qed.
(* the counters after the last turn's m_file: gen + 1, refused and overflow up by at most the text's length *)
Lemma s5c_cnt : forall f rc0 mc s lab, lt_cnt f rc0 mc -> SegModel.nulfree s -> Z.of_nat (length s) <= 65535 ->
  lt_cnt (Datatypes.S f) rc0 (SegModel.m_file mc s lab).
Proof.
intros f rc0 mc s lab (C1 & C2 & C3 & C4 & C5 & C6) Hn Hl.
pose proof (m_file_c.m_file_gen mc s lab) as G. pose proof (m_file_c.m_file_refused mc s lab Hn) as R.
pose proof (m_file_c.m_file_overflow mc s lab Hn) as O.
unfold lt_cnt. rewrite Nat2Z.inj_succ. change (2 ^ 20) with 1048576 in *.
repeat split; lia.
Qed.

(* ============================== L3's walk facts (the frame, the blocks, the readers) ============================== *)
(* the seed of 0x851f0 .. 0x85204: the three slot stores write 120(s1) .. 143(s1), s1 being its own atom 9; the
   fact on atom 9 keeps the window in the stack, above the shadow band, for the token runner's static check (as
   LLVMFuzzerTestOneInput_s10k.v's atom N_SP1); no instrumented check in the stretch *)
Definition s5c_slots : YP09.region := YP09.mkRegion (Some 9%nat) 120 144 120 144 [].
Definition s5c_ss : sstate :=
  mkSS LO_S5LST sr_atoms [s5c_slots] None (mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5)] [] []).
Definition s5c_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).

Lemma s5c_perm3 : forall {A} (x y z : A) l,
  Permutation (x :: y :: z :: l) (y :: z :: x :: l) /\ Permutation (x :: y :: z :: l) (x :: z :: y :: l).
Proof.
intros A x y z l. split.
- eapply Permutation_trans; [apply perm_swap|]. apply perm_skip. apply perm_swap.
- apply perm_skip. apply perm_swap.
Qed.
Lemma s5c_pres_reg : forall regs regs' (r : bv 5) z,
  aregs_preserved regs regs' -> acallee_saved z -> Z_to_bv 5 z = r -> getr regs' r = getr regs r.
Proof. intros regs regs' r z HP Hz <-. exact (HP z Hz). Qed.
Lemma s5c_word_kept : forall (rd rd' : reader) a v,
  (forall x, a <= x < a + 8 -> rd' x = rd x) -> rdword rd a = Some v -> rdword rd' a = Some v.
Proof. intros rd rd' a v HK H. rewrite (rdword_ext rd rd' a); [exact H|]. intros k Hk. apply HK. lia. Qed.
Lemma s5c_bytes_agree : forall (rd rd' : reader) a bs,
  (forall x, a <= x < a + Z.of_nat (length bs) -> rd' x = rd x) -> sa_bytes rd a bs -> sa_bytes rd' a bs.
Proof. intros rd rd' a bs HK H i Hi. rewrite HK by lia. exact (H i Hi). Qed.
Lemma s5c_mconf_agree : forall (rd rd' : reader) a mc,
  (forall x, a <= x < a + seg_spec.SEG_M_SIZE -> rd' x = rd x) -> sa_mconf rd a mc -> sa_mconf rd' a mc.
Proof.
intros rd rd' a mc HK H. unfold sa_mconf, sa_mconfp in *. destruct H as (bs & Hb & He).
exists bs. split; [|exact He]. apply (s5c_bytes_agree rd); [|exact Hb].
destruct He as (Hl & _). intros x Hx. apply HK. lia.
Qed.
Lemma s5c_rconf_agree : forall (rd rd' : reader) a rc0,
  (forall x, a <= x < a + seg_spec.SEG_C_SIZE -> rd' x = rd x) -> sa_rconf rd a rc0 -> sa_rconf rd' a rc0.
Proof.
intros rd rd' a rc0 HK H. unfold sa_rconf in *. destruct H as (bs & Hb & He).
exists bs. split; [|exact He]. apply (s5c_bytes_agree rd); [|exact Hb].
destruct He as (Hl & _). intros x Hx. apply HK. lia.
Qed.
Lemma s5c_strz_agree : forall (rd rd' : reader) p s,
  (forall x, p <= x <= p + Z.of_nat (length s) -> rd' x = rd x) -> sa_strz rd p s -> sa_strz rd' p s.
Proof.
intros rd rd' p s HK (Hz & Hn). split; [|exact Hn]. intros i Hi.
pose proof Hi as Hi'. rewrite length_app in Hi'. cbn [length] in Hi'.
rewrite HK by lia. exact (Hz i Hi).
Qed.

Section s5c_d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section s5c_f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section s5c_e.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis IMGS : s10_img.
Hypothesis BSYM : AF0m.SegBSyms B.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(* the turn's three blocks at the head of the live blocks: pairwise apart, and the middle one not an entry block *)
Lemma s5c_sep3 : forall ly S (W : world SEGS) mem md x y z l,
  AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) (x :: y :: z :: l) ->
  zdisjoint (block_rng x) (block_rng y) /\ zdisjoint (block_rng y) (block_rng z) /\
  zdisjoint (block_rng x) (block_rng z).
Proof using B.
intros ly S W mem md x y z l HAR HP. destruct (s5c_perm3 x y z l) as [P1 P2].
split; [exact (sep_blocks_perm SEGS B LAWS ly S W mem md x y (z :: l) HAR HP)|].
split; [exact (sep_blocks_perm SEGS B LAWS ly S W mem md y z (x :: l) HAR (Permutation_trans HP P1))|].
exact (sep_blocks_perm SEGS B LAWS ly S W mem md x z (y :: l) HAR (Permutation_trans HP P2)).
Qed.
Lemma s5c_notin : forall ly S (W : world SEGS) mem md x y z l,
  AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) (x :: y :: z :: l) -> ~ In y l.
Proof using B.
intros ly S W mem md x y z l HAR HP Hin.
assert (Hy : In y (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym HP)); right; left; reflexivity).
apply in_split in Hin as (l1 & l2 & ->).
assert (HP2 : Permutation (ablocks B ly S) (y :: y :: x :: z :: l1 ++ l2)).
{ eapply Permutation_trans; [exact HP|]. eapply Permutation_trans; [apply perm_swap|]. apply perm_skip.
  exact (Permutation_sym (Permutation_middle (x :: z :: l1) l2 y)). }
pose proof (sep_blocks_perm SEGS B LAWS ly S W mem md y y _ HAR HP2) as D.
destruct y as [p n]. destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hy) as (_ & _ & _ & _ & _ & _ & Hn).
pose proof (req_size_pos n ltac:(lia)) as [R _]. unfold zdisjoint, block_rng in D. cbn [fst snd] in D. lia.
Qed.

(* the entry sp and the realigned base S1 (LLVMFuzzerTestOneInput_s12k.v's lk_sp, with the frame's bound 336) *)
Lemma s5c_sp : forall cx, lt_base B MT cx ->
  x_sp0 cx mod 16 = 0 /\ alloc_ceiling + 32768 <= x_sp0 cx /\ x_sp0 cx <= 2 ^ 47 /\
  x_s1 cx mod 32 = 0 /\ x_sp0 cx - 336 <= x_s1 cx /\ x_s1 cx <= x_sp0 cx - 320.
Proof using B MT.
intros cx HB. destruct HB as (HPRE & _). destruct HPRE as (_ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal & _ & Hceil & Hslo & Hshi & H47 & _).
assert (WS : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity. rewrite WS in Hslo.
unfold x_s1, x_sp0, LT_FRAME in *. set (s := spZ (x_regs cx)) in *. clearbody s.
repeat split; lia.
Qed.
(* the frame address of a journal's target layout is the entry's (s12k's lk_frame_addr) *)
Lemma s5c_frame_addr : forall STK sp0 FP ly0 S0 W0 mem0 md0 own ly S (W : world SEGS) mem md k,
  ajournal SEGS B STK sp0 FP ly0 S0 W0 mem0 md0 own ly S W mem md k ->
  forall cid pos, frame_addr ly cid pos = frame_addr ly0 cid pos.
Proof using B.
intros STK sp0 FP ly0 S0 W0 mem0 md0 own ly S W mem md k HJ cid pos.
destruct HJ as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & EF & _). unfold frame_addr. rewrite EF. reflexivity.
Qed.
(* a live block of a state is a harness block of that state (s12k's lk_hblk) *)
Lemma s5c_hblk : forall ly S (W : world SEGS) mem md a n,
  AR SEGS B ly S W mem md -> In (a, n) (ablocks B ly S) -> lt_hblk B ly S (rdW W mem) a n.
Proof using B.
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
(* the rest of the aligned word that holds a live block's byte is mapped (the chunk's tail, YG0d_tail.v) *)
Lemma s5c_tail_of_AR : forall ly S (W : world SEGS) mem md p n e,
  AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) -> p <= e < p + req_size n -> sa_tail (rdW W mem) e.
Proof using B.
intros ly S W mem md p n e HAR Hin He x Hx.
exact (YG0d_tail.AR_block_word_vis SEGS B ly S W mem md p n e x HAR Hin He ltac:(lia)).
Qed.

(* lt_core across the three slot stores: the run wrote only 120(s1) .. 143(s1) and kept sp, gp, tp, s0, s1
   (s12k's lk_core_run, with the image facts by _s10's s10_lt_img_kept) *)
Lemma s5c_core_run : forall cx ly S (W : world SEGS) regs mem md k acc rem o O regs' mem' md',
  lt_base B MT cx -> lt_core B MT cx ly S W regs mem md k acc rem o O ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem' md' k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 cx + 120 <= a < x_s1 cx + 144) -> rdW W mem' a = rdW W mem a) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
  lt_core B MT cx ly S W regs' mem' md' k acc rem o O.
Proof using B MT IMGS BSYM.
intros cx ly S W regs mem md k acc rem o O regs' mem' md' HB HC HJ' HK P2 P3 P4 P8 P9.
pose proof (s5c_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
destruct HC as (HF & HI & HBL & HBUD).
destruct HF as (HJ & R2 & R3 & R4 & R8 & R9 & HSV & HH0 & HH8 & HH16 & HFL & H176 & HSH).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HinF : In (LT_FCLS, x_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (EF : frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx) by exact (s5c_frame_addr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ _ _).
assert (F512 : fs_frame_bytes LT_FCLS = 512) by (vm_compute; reflexivity).
destruct (frames_bounds SEGS B LAWS ly S W mem md LT_FCLS (x_fpos cx) HAR HinF) as (Hf0 & Hfc & _).
rewrite EF in Hf0. rewrite EF, F512 in Hfc.
assert (KA : forall a, 0 <= a < x_s1 cx + 120 \/ x_s1 cx + 144 <= a < 2 ^ 64 -> rdW W mem' a = rdW W mem a).
{ intros a Ha. apply HK; lia. }
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
  split; [apply (s5c_word_kept (rdW W mem)); [|exact H176]; intros x Hx; apply KA; right; lia|].
  intros i Hi. rewrite KA; [exact (HSH i Hi)|]. left. rewrite (lt_fsh_len o) in Hi.
  unfold x_sh, shadow_addr, SHADOW_OFF. lia.
- apply (s10_lt_img_kept B IMGS BSYM cx W mem' (rdW W mem) (proj1 HJ')); [|exact HI].
  intros a Ha _ _. apply KA. left. pose proof (pa_segs_low a Ha). lia.
- exact HBL.
- exact HBUD.
Qed.

(* lt_core across a call that keeps the blocks and every byte above S1, the frame's bytes and shadow and the
   image facts, preserves the callee-saved registers and spends no allocator event (m_file: sa_noalloc,
   EV_m_file = 0); the meter carried by MTFL's mo_le_set_fs_r *)
Lemma s5c_core_call : forall cx ly S (W : world SEGS) regs mem md k acc rem o O ly2 S2 (W2 : world SEGS) regs2
  mem2 md2,
  lt_base B MT cx -> lt_core B MT cx ly S W regs mem md k acc rem o O ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly2 S2 W2 mem2 md2 k ->
  aregs_preserved regs regs2 -> sa_noalloc B ly S ly2 S2 ->
  (forall a, x_s1 cx <= a < 2 ^ 64 -> rdW W2 mem2 a = rdW W mem a) ->
  (forall a, x_fr cx <= a < x_fr cx + 512 \/ x_sh cx <= a < x_sh cx + 64 -> rdW W2 mem2 a = rdW W mem a) ->
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     rdW W2 mem2 a = rdW W mem a) ->
  lt_core B MT cx ly2 S2 W2 regs2 mem2 md2 k acc rem o O.
Proof using B MT MTFL IMGS BSYM.
intros cx ly S W regs mem md k acc rem o O ly2 S2 W2 regs2 mem2 md2 HB HC HJ2 HP HNA KS KF KI.
pose proof (s5c_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
destruct HC as (HF & HI & HBL & HBUD).
destruct HF as (HJ & R2 & R3 & R4 & R8 & R9 & HSV & HH0 & HH8 & HH16 & HFL & H176 & HSH).
destruct HNA as (HPm & _ & (fs & ES2)).
split; [|split; [|split]].
- split; [exact HJ2|].
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
  split; [apply (s5c_word_kept (rdW W mem)); [|exact HH0]; intros x Hx; apply KF; left; lia|].
  split; [apply (s5c_word_kept (rdW W mem)); [|exact HH8]; intros x Hx; apply KF; left; lia|].
  split; [apply (s5c_word_kept (rdW W mem)); [|exact HH16]; intros x Hx; apply KF; left; lia|].
  split; [apply (s5c_word_kept (rdW W mem)); [|exact HFL]; intros x Hx; apply KF; left; unfold LT_FLAGW in *; lia|].
  split; [apply (s5c_word_kept (rdW W mem)); [|exact H176]; intros x Hx; apply KS; lia|].
  intros i Hi. rewrite KF; [exact (HSH i Hi)|]. right. rewrite (lt_fsh_len o) in Hi. lia.
- exact (s10_lt_img_kept B IMGS BSYM cx W2 mem2 (rdW W mem) (proj1 HJ2) KI HI).
- unfold lt_blocks in *. eapply Permutation_trans; [exact HPm | exact HBL].
- destruct HBUD as (B1 & B2 & B3 & B4 & B5 & B6). unfold lt_bud.
  split; [exact B1|]. split; [exact B2|]. split; [exact B3|].
  split; [rewrite ES2; exact (mo_le_set_fs_r MT MTFL _ _ _ _ B4)|]. split; [exact B5 | exact B6].
Qed.
End s5c_e.
End s5c_f.
End s5c_d.

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
Variable snp_lo snp_hi : Z.
Variable snp_cr : list (Z * Z).
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis IMGS : s10_img.
Hypothesis BSYM : AF0m.SegBSyms B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis PRW : prog_rw SEGS B.
Hypothesis VOBJS : seg_val_objs.
Hypothesis SIGP : seg_sig_prog.
Hypothesis HPGS : forall a, inFP (ltoi_PG longlA) a ->
  Exists (in_zr a) (as_prog_static B) /\ in_img SEGS a.
Hypothesis HPG_RO : forall a, inFP (ltoi_PG longlA) a -> ~ in_roP SEGS RLO_A RHI_A a.
Hypothesis HPG_PTR : forall a p,
  ((exists i, (i < 5)%nat /\ a = wordsA + 8 * Z.of_nat i) \/
   (exists i, (i < pin_spec.CAT_N)%nat /\ a = pin_spec.row_addr catA i)) ->
  rdword (fun x => option_map (fun b : byte => bv_unsigned b) (seg_rom SEGS (Z_to_bv 64 x))) a = Some p ->
  p + 65536 <= longlA.
Hypothesis AMEMCPY : forall fx0 : YK11.FPState,
  @aintrin_realizes fx0 rc SEGS B OCpy (SIG SS___asan_memcpy).
Hypothesis AMEMSET : forall fx0 : YK11.FPState,
  @aintrin_realizes fx0 rc SEGS B OSet (SIG SS___asan_memset).
Hypothesis AFREE4 : forall fx0 : YK11.FPState, @afree04_rule fx0 rc SK SEGS B MT.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState,
  @RtPFSeg.seg_asnprintf_realizes fx0 rc SEGS B snp_lo snp_hi snp_cr
    (SIG SS___interceptor_trampoline_snprintf) gotwA guardA.
Hypothesis HSNP_LIT : forall x, In x LLVMFuzzerTestOneInput_c.LTOI_LITS ->
  snp_lo <= seg_litA_fz x /\ seg_litA_fz x + Z.of_nat (length x) + 1 <= gotwA.
Hypothesis HSNP_CR : Forall (fun r => snp_lo <= fst r /\ 0 <= snd r /\ fst r + snd r <= snp_hi) snp_cr.
Hypothesis HSNP_LO : 0 <= snp_lo.
Hypothesis HSNP_CEIL : snp_hi <= alloc_ceiling.
Hypothesis HSNP_FAKE : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> snp_hi <= ly_F ly.
Hypothesis HM_FILE : forall fx0 : YK11.FPState,
  @m_file_c.m_file_contract fx0 rc SK SEGS B (BASE + AF_m_file) STK_m_file RLO_A RHI_A seg_litA_fz
    wordsA rolesA catA gotwA guardA.
Hypothesis HPARSE_FILE : forall fx0 : YK11.FPState,
  @reac_segconf_parse_file_c.reac_segconf_parse_file_contract fx0 rc SK SEGS B
    (BASE + AF_reac_segconf_parse_file) STK_reac_segconf_parse_file RLO_A RHI_A seg_litA_rc catA gotwA guardA.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* ---- L3, 0x851f0 .. 0x85208: the last turn's three slot stores (120(s1) := returned, 128(s1) := f + 1,
   136(s1) := the turn's cursor), a1 := t, a2 := 0, and m_file(m, t, NULL) through PaFx.v's cl_callSF; m_file
   returns at an FP state of its own (apost_baseF), and K85208 is applied there (srr_after_callF) ---- *)
Lemma s5_last : forall f, LTA_K85208 B MT f -> S5_LST_stmt B MT f.
Proof using All.
intros f HKA. unfold S5_LST_stmt.
intros cx ly S W regs mem md k acc c m t HB HFRM HLST HBODY HCM HSTR R10 R18 R21 R22 R23 R24 R26 R27 HSL.
destruct HBODY as (HCo & HHc & HHm & HHt & HCNT).
destruct HCM as (HRC & HMC).
pose proof HCo as (HFm & HI & HBL & HBUD).
pose proof HFm as (HJ & R2 & R3 & R4 & R8 & R9 & _).
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & Hnev & _ & _ & _ & _ & _ & _ & HJpres & _).
pose proof HB as (HPRE0 & HPRES0 & _ & _ & _ & _ & Hpn & Hlen & _ & Hfr0 & _ & Hev0 & _).
pose proof HPRE0 as (HAR0 & _ & _ & Hgp0 & Htp0 & _).
pose proof (s5c_sp B MT cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
assert (WS : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity.
assert (STKV : STK_m_file = 8560) by (vm_compute; reflexivity).
pose proof (s5c_nfiles (x_pl cx)) as Hnf.
assert (Hf : Z.of_nat f < seg_spec.seg_nfiles (x_pl cx)) by (unfold x_nf in HLST; lia).
assert (Hf4 : Z.of_nat f + 1 <= 4) by (unfold x_nf in HLST; lia).
pose proof (s5c_txt_len (x_pl cx) f Hf) as Hsl.
pose proof (s5c_txt_nulfree (x_pl cx) f Hf) as Hsn.
change (s5_txt (x_pl cx) f) with (seg_spec.seg_txt (x_pl cx) f) in HSTR.
set (s := seg_spec.seg_txt (x_pl cx) f) in *.
assert (Etn : x_tn cx f = Z.of_nat (length s) + 1) by reflexivity.
(* the turn's three blocks: t, m, c *)
destruct HHc as (HinC & Hc4 & Hc16 & HaC).
destruct HHm as (HinM & Hm4 & Hm16 & HaM).
destruct HHt as (HinT & Ht4 & Ht16 & HaT).
destruct (al_blocks _ _ LAWS ly S W mem md m _ HAR HinM) as (_ & _ & HmC & HmApp & _ & _ & _).
destruct (al_blocks _ _ LAWS ly S W mem md t _ HAR HinT) as (_ & _ & HtC & HtApp & _ & _ & _).
destruct (al_blocks _ _ LAWS ly S W mem md c _ HAR HinC) as (_ & _ & HcC & HcApp & _ & _ & _).
assert (RqM : req_size seg_spec.SEG_M_SIZE = 9236) by reflexivity.
assert (RqC : req_size seg_spec.SEG_C_SIZE = 16616) by reflexivity.
assert (RqT : req_size (x_tn cx f) = x_tn cx f) by (unfold req_size; destruct (Z.eqb_spec (x_tn cx f) 0); lia).
rewrite RqM in HmC, HmApp. rewrite RqC in HcC, HcApp. rewrite RqT in HtC, HtApp.
assert (HBLp : Permutation (ablocks B ly S)
  ((t, x_tn cx f) :: (m, seg_spec.SEG_M_SIZE) :: (c, seg_spec.SEG_C_SIZE) :: x_bl0 B cx)) by exact HBL.
destruct (s5c_sep3 B ly S W mem md _ _ _ _ HAR HBLp) as (Dtm & Dmc & Dtc).
unfold zdisjoint, block_rng in Dtm, Dmc, Dtc. cbn [fst snd] in Dtm, Dmc, Dtc.
rewrite RqT, RqM in Dtm. rewrite RqM, RqC in Dmc. rewrite RqT, RqC in Dtc.
pose proof (s5c_notin B ly S W mem md _ _ _ _ HAR HBLp) as HnotM.
(* the turn's cursor, stored at 136(s1), is an unsigned word *)
assert (HTA : 0 <= seg_spec.seg_turn_at (x_pl cx) (x_p cx) f < 2 ^ 64).
{ unfold seg_spec.seg_turn_at. pose proof (s5c_tail_len (x_pl cx) f) as HTL.
  destruct Hpn as [(Hn0 & Hp0) | (Hn & Hpin)].
  - rewrite Hp0. unfold emptyA. lia.
  - destruct (al_blocks _ _ LAWS (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) (x_p cx) (x_n cx) HAR0 Hpin)
      as (_ & Hp4 & Hpc & _).
    pose proof (req_size_pos (x_n cx) ltac:(lia)) as [_ Hr]. lia. }
(* ---- the seed at 0x851f0: every register its own atom, the window 120(s1) .. 143(s1) ---- *)
remember (Eimg (Ereg regs [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EEo : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U9 : bv_unsigned (ew E 9) = x_s1 cx).
{ rewrite (EEo 9%nat 9%bv eq_refl), R9. unfold w64. apply unsigned_lit_small. lia. }
assert (HS : st_ok_pi SEGS VAL E s5c_ss
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO_S5LST)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold s5c_ss. apply pa_entry_st_ok_full.
  - rewrite HE. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, s5c_slots.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply HJpres. lia.
  - cbn [pairwise_disjoint all_disjoint]. split; exact I.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. split; [|exact I].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9. change (2 ^ 5) with 32. lia. }
assert (SHOK : sh_ok SEGS (SLit SHADOW_OFF) [] E (mrestrict (w_H W) mem)) by (unfold sh_ok; apply Forall_nil).
unfold cfg_at, w64.
(* 0x851f0 .. 0x85204: sd s6,120(s1); sd s2,128(s1); sd s8,136(s1); mv a1,s7; li a2,0; jal m_file *)
paj_run_tok RUN HS HJ SHOK s5c_span.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply awr_ok_cons_stack_off with (n := 9%nat) (d := x_s1 cx - x_sp0 cx);
  [reflexivity | rewrite U9; ring | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia | apply awr_ok_nil]. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md1 := d) in *; clearbody md1 end.
pose proof (proj1 HJ) as HAR1.
(* the registers the stretch kept, and the three it set *)
assert (KR : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 22; 23; 24; 26; 27]%bv -> getr (ms_regs ms) r = getr regs r).
{ intros r Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr];
    [ let P := fresh "P" in lazymatch goal with |- getr _ ?rr = _ => prreg HS rr P end;
      rewrite P; apply EEo; reflexivity | ]).
  destruct Hr. }
prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
prreg HS (12%bv : bv 5) P12.
(* the bytes the stretch did not write *)
assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 cx + 120 <= a < x_s1 cx + 144) ->
  rdW W (ms_mem ms) a = rdW W mem a).
{ intros a Ha Hn.
  apply (kept_of_frame (segs := SEGS) E (ss_mem s5c_ss) (w_H W) mem (ms_mem ms)
    (fun y => x_s1 cx + 120 <= y < x_s1 cx + 144) HFr); [|exact Ha | exact Hn].
  intros b wlo whi x Hin Hx.
  lazymatch type of Hin with In _ (windows ?rs) =>
    let w := eval vm_compute in (windows rs) in change (In (b, wlo, whi) w) in Hin end.
  cbn [In] in Hin. destruct Hin as [Hq | []]. injection Hq as <- <- <-. cbn [base_val] in Hx. rewrite U9 in Hx.
  exact Hx. }
assert (KMlow : forall a, 0 <= a < alloc_ceiling + 8 -> rdW W (ms_mem ms) a = rdW W mem a)
  by (intros a Ha; apply KM; lia).
(* the facts of the cut at the memory after the stores *)
pose proof (s5c_core_run B MT IMGS BSYM cx ly S W regs mem md k acc _ LFO_L _ (ms_regs ms) (ms_mem ms) md1 HB HCo HJ KM
  (KR 2%bv ltac:(cbn; tauto)) (KR 3%bv ltac:(cbn; tauto)) (KR 4%bv ltac:(cbn; tauto))
  (KR 8%bv ltac:(cbn; tauto)) (KR 9%bv ltac:(cbn; tauto))) as HCo1.
pose proof (s5c_hblk B ly S W (ms_mem ms) md1 c _ HAR1 HinC) as HHc1.
pose proof (s5c_hblk B ly S W (ms_mem ms) md1 m _ HAR1 HinM) as HHm1.
pose proof (s5c_hblk B ly S W (ms_mem ms) md1 t _ HAR1 HinT) as HHt1.
assert (HMC1 : sa_mconf (rdW W (ms_mem ms)) m (seg_spec.seg_mc (x_st cx f))).
{ apply (s5c_mconf_agree (rdW W mem)); [|exact HMC]. intros x Hx. apply KMlow. unfold seg_spec.SEG_M_SIZE in Hx. lia. }
assert (HRC1 : sa_rconf (rdW W (ms_mem ms)) c (seg_spec.seg_rc (x_st cx f))).
{ apply (s5c_rconf_agree (rdW W mem)); [|exact HRC]. intros x Hx. apply KMlow. unfold seg_spec.SEG_C_SIZE in Hx. lia. }
assert (HSTR1 : sa_str (rdW W (ms_mem ms)) t s).
{ destruct HSTR as (Hz & _). split.
  - apply (s5c_strz_agree (rdW W mem)); [|exact Hz]. intros x Hx. apply KMlow. lia.
  - apply (s5c_tail_of_AR B ly S W (ms_mem ms) md1 t (x_tn cx f) _ HAR1 HinT). rewrite RqT. lia. }
assert (HTM1 : sa_tail (rdW W (ms_mem ms)) (m + seg_spec.SEG_M_SIZE - 1)).
{ apply (s5c_tail_of_AR B ly S W (ms_mem ms) md1 m seg_spec.SEG_M_SIZE _ HAR1 HinM). rewrite RqM.
  unfold seg_spec.SEG_M_SIZE. lia. }
pose proof HCo1 as (_ & HI1 & _ & _).
pose proof HI1 as (HRO1 & HIM1 & _).
pose proof HIM1 as (_ & _ & Hfz1 & _ & Hcat1 & _ & Hwd1 & Hrl1 & Hssp1 & _).
(* the three words the stores wrote *)
lazymatch type of HS with st_ok _ _ ?ssB _ =>
  let r0 := eval vm_compute in (nth 0 (ss_mem ssB) (YP09.mkRegion None 0 0 0 0 [])) in
  pose proof (st_ok_region_nth E ssB _ 0%nat r0 HS ltac:(vm_compute; reflexivity)) as RS1 end.
destruct RS1 as (_ & _ & _ & CS1).
cbn [YP09.r_base YP09.r_chunks base_val ms_mem restrict] in CS1. rewrite U9 in CS1.
assert (W120 : rdword (rdW W (ms_mem ms)) (x_s1 cx + 120) = Some (seg_spec.b2z (seg_spec.seg_ret (x_st cx f)))).
{ assert (Hb : 0 <= seg_spec.b2z (seg_spec.seg_ret (x_st cx f)) < 2 ^ 64)
    by (unfold seg_spec.b2z; destruct (seg_spec.seg_ret _); lia).
  apply (s10_rd_chunk8 E (w_H W) (ms_mem ms) (x_s1 cx) 120 _ (SOff 22 0) _ _ CS1);
  [ repeat first [left; reflexivity | right] | reflexivity | | exact Hb ].
  cbn [sv_denot]. rewrite (EEo 22%nat 22%bv eq_refl), R22. unfold w64.
  rewrite unsigned_lit_small by exact Hb. rewrite Z.add_0_r. reflexivity. }
assert (W128 : rdword (rdW W (ms_mem ms)) (x_s1 cx + 128) = Some (Z.of_nat f + 1)).
{ assert (Hb : 0 <= Z.of_nat f + 1 < 2 ^ 64) by lia.
  apply (s10_rd_chunk8 E (w_H W) (ms_mem ms) (x_s1 cx) 128 _ (SOff 18 0) _ _ CS1);
  [ repeat first [left; reflexivity | right] | reflexivity | | exact Hb ].
  cbn [sv_denot]. rewrite (EEo 18%nat 18%bv eq_refl), R18. unfold w64.
  rewrite unsigned_lit_small by exact Hb. rewrite Z.add_0_r. reflexivity. }
assert (W136 : rdword (rdW W (ms_mem ms)) (x_s1 cx + 136) = Some (seg_spec.seg_turn_at (x_pl cx) (x_p cx) f)).
{ apply (s10_rd_chunk8 E (w_H W) (ms_mem ms) (x_s1 cx) 136 _ (SOff 24 0) _ _ CS1);
  [ repeat first [left; reflexivity | right] | reflexivity | | exact HTA ].
  cbn [sv_denot]. rewrite (EEo 24%nat 24%bv eq_refl), R24. unfold w64.
  rewrite unsigned_lit_small by exact HTA. rewrite Z.add_0_r. reflexivity. }
assert (HSL1 : lt_slots cx (rdW W (ms_mem ms)) (LT_L cx c m ++
    [(120, seg_spec.b2z (seg_spec.seg_ret (x_st cx f))); (128, Z.of_nat f + 1);
     (136, seg_spec.seg_turn_at (x_pl cx) (x_p cx) f);
     (152, Z.of_nat (length (seg_spec.seg_turn_tail (x_pl cx) f)))])).
{ assert (HO : forall o v, In (o, v) (LT_L cx c m ++ [(152, Z.of_nat (length (seg_spec.seg_turn_tail (x_pl cx) f)))]) ->
    (o + 8 <= 120 \/ 144 <= o) /\ 0 <= o <= 184).
  { intros o v Hin. apply in_app_or in Hin as [Hin | Hin]; unfold LT_L in Hin; cbn [In] in Hin;
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- _; lia|]); destruct Hin. }
  assert (HK1 : forall o v, In (o, v) (LT_L cx c m ++ [(152, Z.of_nat (length (seg_spec.seg_turn_tail (x_pl cx) f)))]) ->
    rdword (rdW W (ms_mem ms)) (x_s1 cx + o) = Some v).
  { intros o v Hin. destruct (HO o v Hin) as [Ho1 Ho2].
    apply (s5c_word_kept (rdW W mem)); [|exact (HSL o v Hin)]. intros x Hx. apply KM; lia. }
  intros o v Hin. apply in_app_or in Hin as [Hin | Hin].
  - apply HK1. apply in_or_app. left. exact Hin.
  - cbn [In] in Hin. destruct Hin as [Hq | [Hq | [Hq | [Hq | []]]]]; injection Hq as <- <-.
    + exact W120.
    + exact W128.
    + exact W136.
    + apply HK1. apply in_or_app. right. left. reflexivity. }
(* ---- the call of m_file at 0x85204: pc = SIG SS_m_file = BASE + AF_m_file, ra = BASE + 0x4d4 ---- *)
pmkst HS.
rewrite (SIGP SS_m_file ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_m_file) with AF_m_file by (vm_compute; reflexivity).
set (regs1 := ms_regs ms) in *. set (mem1 := ms_mem ms) in *.
assert (P10' : getr regs1 10 = w64 m) by (rewrite P10, (EEo 10%nat 10%bv eq_refl); exact R10).
assert (P11' : getr regs1 11 = w64 t) by (rewrite P11, (EEo 23%nat 23%bv eq_refl); exact R23).
assert (P12' : getr regs1 12 = w64 0) by (rewrite P12; reflexivity).
assert (Hsp1 : spZ regs1 = x_sp0 cx + (x_s1 cx - x_sp0 cx)).
{ unfold spZ. rewrite (KR 2%bv ltac:(cbn; tauto)), R2. unfold w64. rewrite unsigned_lit_small by lia. ring. }
assert (Hgp1 : getr regs1 3 = w64 (as_gp B)) by (rewrite (KR 3%bv ltac:(cbn; tauto)), R3; exact Hgp0).
assert (Htp1 : getr regs1 4 = w64 (as_tp B)) by (rewrite (KR 4%bv ltac:(cbn; tauto)), R4; exact Htp0).
assert (Hraw : YK0s.ret_ok (getr regs1 1)) by (rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (Hra4 : 4096 <= bv_unsigned (getr regs1 1)) by (rewrite P1, unsigned_lit_small by lia; lia).
(* the frame chain at the call: s0 = SP0 is above the call's sp + 16 *)
assert (HRD : astack_rd ly (rdW W mem1) (x_s1 cx)).
{ apply (astack_rd_mono ly _ (x_sp0 cx - STK_LLVMFuzzerTestOneInput)); [lia|].
  apply astack_rd_of_pres.
  apply (astack_pres_journal SEGS B pa_segs_low STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA)
    (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem1 md1 k HJ HPRES0).
  intros a (r & Hr & Ha) Ha2. exfalso. unfold ltoi_PG in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  unfold longlA, A_LONGL, LONGL_N in Ha. lia. }
assert (HCHx : exists ch, achain ly (rdW W mem1) (x_sp0 cx + (x_s1 cx - x_sp0 cx)) (s0Z regs1) ch).
{ apply achain_any.
  - replace (x_sp0 cx + (x_s1 cx - x_sp0 cx)) with (x_s1 cx) by ring. exact HRD.
  - right; right; right. unfold s0Z. rewrite (KR 8%bv ltac:(cbn; tauto)), R8. unfold w64.
    rewrite unsigned_lit_small by lia. lia. }
destruct HCHx as (ch & Hch).
(* m_file's premises *)
assert (HROOM : sa_room S) by (unfold sa_room; rewrite Hfrs, Hfr0; cbn; lia).
assert (HEV : st_nev S + m_file_c.EV_m_file <= EV_MAX).
{ unfold m_file_c.EV_m_file. pose proof HBUD as (Bk & Br & Bkr & _). lia. }
pose proof HCNT as (_ & _ & _ & K4 & K5 & K6).
pose proof HMC as (bsm & _ & _ & Hseg32 & _ & _ & _ & _ & Hkept8 & _).
assert (HINV : s5c_inv (seg_spec.seg_mc (x_st cx f))) by (split; assumption).
pose proof (s5c_file_inv _ s None HINV) as HINV'.
assert (HMFP : m_file_c.m_file_pre SEGS B ly S (rdW W mem1) m t 0 (seg_spec.seg_mc (x_st cx f)) s None).
{ unfold m_file_c.m_file_pre. change (2 ^ 20) with 1048576 in K4, K5, K6.
  split; [lia|]. split; [exact Hm16|]. split; [exact HMC1|].
  split; [exists m, seg_spec.SEG_M_SIZE; split; [exact HinM | lia]|].
  split; [exact (proj2 (proj2 (proj2 HHm1)))|]. split; [exact HTM1|].
  split; [change (2 ^ 31) with 2147483648; lia|].
  split; [change (2 ^ 32) with 4294967296; change (2 ^ 17) with 131072; lia|].
  split; [change (2 ^ 32) with 4294967296; change (2 ^ 17) with 131072; lia|].
  split; [lia|]. split; [exact HSTR1|]. split; [lia|].
  split; [exists t, (x_tn cx f); split; [exact HinT | lia]|].
  split; [exact (proj2 (proj2 (proj2 HHt1)))|].
  split.
  { unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HtApp. lia. }
  split.
  { unfold sa_disj, seg_spec.cstr_span. unfold seg_spec.SEG_M_SIZE in *. lia. }
  split; [reflexivity | exact I]. }
pose proof (fun HPRE1 : afn_pre SEGS B STK_m_file ly S W regs1 mem1 md1 ch =>
  HM_FILE fx ly S W regs1 mem1 md1 ch m t 0 (seg_spec.seg_mc (x_st cx f)) s None HPRE1 HFRM HROOM HRO1
    (fun x Hx => proj1 (Hfz1 x ltac:(unfold LTOI_FZ_LITS; rewrite !in_app_iff; right; right; right; exact Hx)))
    Hwd1 Hrl1 Hcat1 Hssp1 P10' ltac:(lia) P11' ltac:(lia) P12' ltac:(lia) HMFP HEV) as HCALL.
lazymatch type of HCALL with _ -> SRr _ _ _ (apost_baseF _ _ _ ?FPq _ _ _ _ _ _ _ ?Kq) =>
  set (FP1 := FPq) in HCALL; set (K := Kq) in HCALL end.
assert (HFP : forall a, inFP FP1 a -> m <= a < m + 9236).
{ intros a Ha. pose proof (s5c_fp_in m (length (SegModel.mc_kept (seg_spec.seg_mc (x_st cx f))))
    (SegModel.m_file (seg_spec.seg_mc (x_st cx f)) s None) a HINV' Ha) as H.
  unfold seg_spec.SEG_M_SIZE in H. exact H. }
unfold lt_post.
eapply (srr_after_callF (fx := fx) SEGS).
{ apply (cl_callSF B LAWS W regs1 mem1 (Z_to_bv 64 (BASE + AF_m_file)) STK_LLVMFuzzerTestOneInput (x_sp0 cx)
    (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [(LT_FCLS, x_fpos cx)] ly S md1 k STK_m_file
    FP1 m_file_c.EV_m_file (x_s1 cx - x_sp0 cx) (getr regs1 1) ch K HJ Hsp1 ltac:(lia) ltac:(lia)
    ltac:(lia) ltac:(lia) Hgp1 Htp1 eq_refl Hraw Hra4 Hch).
  - intros HPRE1. eapply SRr_mono; [exact (HCALL HPRE1) | intros W3 c3 _ H3; exact H3].
  - intros a Ha. right. exists m, seg_spec.SEG_M_SIZE. split; [exact HinM|]. split; [exact HnotM|].
    pose proof (HFP a Ha) as Hma. rewrite RqM. lia. }
(* ---- back at 0x85208 at the FP state m_file returned ---- *)
cbv beta. intros fx1 ly2 S2 W2 regs2 mem2 md2 _ Hfx (HJ2 & HJc & HP & HK).
unfold K in HK. destruct HK as (HMC2 & HNA).
replace (k + m_file_c.EV_m_file) with k in HJ2 by (unfold m_file_c.EV_m_file; ring).
pose proof (proj1 HJ2) as HAR2.
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & JF1 & JF2 & JF3 & JF4 & _).
pose proof HNA as (HPm & _ & _).
assert (HIn2 : forall pn, In pn (ablocks B ly S) -> In pn (ablocks B ly2 S2))
  by (intros pn H; apply (Permutation_in _ (Permutation_sym HPm)); exact H).
(* what m_file kept: the stack above S1, the frame and its shadow, the image, the blocks c and t *)
assert (KEEP : forall a, x_s1 cx <= a < 2 ^ 64 -> rdW W2 mem2 a = rdW W mem1 a).
{ intros a Ha. apply JF1; [lia | lia |]. intros Hfp. pose proof (HFP a Hfp). lia. }
assert (HinF : In (LT_FCLS, x_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (EF : frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx)
  by exact (s5c_frame_addr B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ _ _).
assert (F512 : fs_frame_bytes LT_FCLS = 512) by (vm_compute; reflexivity).
destruct (frames_bounds SEGS B LAWS ly S W mem1 md1 LT_FCLS (x_fpos cx) HAR1 HinF) as (Hf0 & Hfc & _).
rewrite EF in Hf0. rewrite EF, F512 in Hfc.
pose proof (sep_block_frame SEGS B LAWS ly S W mem1 md1 m _ LT_FCLS (x_fpos cx) HAR1 HinM HinF) as Hsep.
rewrite EF, F512, RqM in Hsep. unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
assert (KFR : forall a, x_fr cx <= a < x_fr cx + 512 \/ x_sh cx <= a < x_sh cx + 64 ->
  rdW W2 mem2 a = rdW W mem1 a).
{ intros a Ha. apply (JF4 LT_FCLS (x_fpos cx) a HinF).
  - unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF, F512. change (512 / 8) with 64.
    unfold x_sh in Ha. destruct Ha as [Ha | Ha]; [left | right]; lia.
  - intros Hfp. pose proof (HFP a Hfp) as Hma.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HmApp. unfold x_sh, shadow_addr, SHADOW_OFF in Ha. lia. }
assert (HNS : ~ YI16.sink_open_fp FP1).
{ intros (r & Hr & Hlo & Hhi). assert (Hin0 : inFP FP1 0) by (exists r; split; [exact Hr | lia]).
  pose proof (HFP 0 Hin0). lia. }
assert (KIMG2 : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) ->
  ~ (as_errno B <= a < as_errno B + 4) -> rdW W2 mem2 a = rdW W mem1 a).
{ intros a Hi Ho He. apply (JF3 a Hi Ho He). apply fp_spares_closed; [exact HNS|].
  intros Hfp. pose proof (HFP a Hfp) as Hma.
  exact (blk_img SEGS B LAWS ly S W mem1 md1 m _ a HAR1 HinM ltac:(rewrite RqM; lia) Hi). }
assert (KBc : forall x, c <= x < c + seg_spec.SEG_C_SIZE -> rdW W2 mem2 x = rdW W mem1 x).
{ intros x Hx. unfold seg_spec.SEG_C_SIZE in Hx. replace x with (c + (x - c)) by ring.
  apply (JF2 c _ (x - c) HinC (HIn2 _ HinC)); [rewrite RqC; lia|].
  intros Hfp. pose proof (HFP _ Hfp). lia. }
assert (KBt : forall x, t <= x < t + x_tn cx f -> rdW W2 mem2 x = rdW W mem1 x).
{ intros x Hx. replace x with (t + (x - t)) by ring.
  apply (JF2 t _ (x - t) HinT (HIn2 _ HinT)); [rewrite RqT; lia|].
  intros Hfp. pose proof (HFP _ Hfp). lia. }
(* the cut K85208 at the state m_file returned *)
pose proof (s5c_core_call B MT MTFL IMGS BSYM cx ly S W regs1 mem1 md1 k acc _ LFO_L _ ly2 S2 W2 regs2 mem2 md2
  HB HCo1 HJ2 HP HNA KEEP KFR KIMG2) as HCo2.
pose proof (s5c_hblk B ly2 S2 W2 mem2 md2 c _ HAR2 (HIn2 _ HinC)) as HHc2.
pose proof (s5c_hblk B ly2 S2 W2 mem2 md2 m _ HAR2 (HIn2 _ HinM)) as HHm2.
pose proof (s5c_hblk B ly2 S2 W2 mem2 md2 t _ HAR2 (HIn2 _ HinT)) as HHt2.
assert (HRC2 : sa_rconf (rdW W2 mem2) c (seg_spec.seg_rc (x_st cx f)))
  by (apply (s5c_rconf_agree (rdW W mem1)); [exact KBc | exact HRC1]).
assert (HSTR2 : sa_str (rdW W2 mem2) t s).
{ destruct HSTR1 as (Hz1 & _). split.
  - apply (s5c_strz_agree (rdW W mem1)); [|exact Hz1]. intros x Hx. apply KBt. lia.
  - apply (s5c_tail_of_AR B ly2 S2 W2 mem2 md2 t (x_tn cx f) _ HAR2 (HIn2 _ HinT)). rewrite RqT. lia. }
assert (HSL2 : lt_slots cx (rdW W2 mem2) (LT_L cx c m ++
    [(120, seg_spec.b2z (seg_spec.seg_ret (x_st cx f))); (128, Z.of_nat f + 1);
     (136, seg_spec.seg_turn_at (x_pl cx) (x_p cx) f);
     (152, Z.of_nat (length (seg_spec.seg_turn_tail (x_pl cx) f)))])).
{ intros o v Hin. assert (Ho : 0 <= o <= 184).
  { apply in_app_or in Hin as [Hin | Hin]; [unfold LT_L in Hin|]; cbn [In] in Hin;
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- _; lia|]); destruct Hin. }
  apply (s5c_word_kept (rdW W mem1)); [|exact (HSL1 o v Hin)]. intros x Hx. apply KEEP. lia. }
assert (R23' : getr regs2 23 = w64 t).
{ rewrite (s5c_pres_reg _ _ 23%bv 23 HP ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (KR 23%bv ltac:(cbn; tauto)). exact R23. }
assert (R26' : getr regs2 26 = w64 ((m + seg_spec.MC_N) / 8)).
{ rewrite (s5c_pres_reg _ _ 26%bv 26 HP ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (KR 26%bv ltac:(cbn; tauto)). exact R26. }
assert (R27' : getr regs2 27 = w64 (seg_spec.seg_turn_np (x_pl cx) f)).
{ rewrite (s5c_pres_reg _ _ 27%bv 27 HP ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (KR 27%bv ltac:(cbn; tauto)). exact R27. }
pose proof (s5c_cnt f _ _ s None HCNT Hsn Hsl) as HCNT2.
rewrite P1.
exact (HKA fx1 cx ly2 S2 W2 regs2 mem2 md2 k acc c m t HB (fxrel_frm0 fx fx1 HFRM Hfx) HLST HCo2 HHc2 HHm2 HHt2
  R23' R26' R27' HSL2 HRC2 HMC2 HSTR2 HCNT2).
Qed.

End ec.
End fc.
End dc.

(* ======================================== piece e ======================================== *)

(* ================================ the tail's symbolic state at 0x851c0 ================================
   Every register is its own atom but s10, which is seeded as (atom 32) >> 3: atom 32 is the word at 184(s1),
   m + 0x2000 = &m->n, so check 8's address s10 + 176(s1) is `(x >> 3) + Bx` with Bx = SHADOW_OFF and the token
   runner's match_x sees it. The read-only region at s1 (atom 9) holds the three slots the
   tail reads: 152 (atom 34, the count after the turn's header), 176 (SHADOW_OFF), 184 (atom 32). The region at
   atom 32 holds m->n (atom 33, 0 .. 32). The shadow entry covers the 8 bytes at &m->n: the slow block at 0x8544c
   starts with a load, so the runner takes check 8 in its 8-byte form. *)
Definition s5e_regions : smem := [
  YP09.mkRegion (Some 9%nat) 152 192 0 0
    [YP09.mkChunk 152 (CVal 8 (SOff 34 0)); YP09.mkChunk 176 (CVal 8 (SLit SHADOW_OFF));
     YP09.mkChunk 184 (CVal 8 (SOff 32 0))];
  YP09.mkRegion (Some 32%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 33 0))] ].
Definition s5e_facts : facts := mkFacts [(32%nat, mkAF 4096 0x7fffff800000 3); (33%nat, mkAF 0 32 0)] [] [].
Definition s5e_ss : sstate :=
  mkSS LO_S5CK (sr_set sr_atoms 26%bv (SAlu ALU_SRL (SOff 32 0) (SLit 3))) s5e_regions None s5e_facts.
Definition s5e_Bx : sv := SLit SHADOW_OFF.
Definition s5e_SH : list shent := [mkSHE 32 0 8].
Definition s5e_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).

(* a register of a call state, read without normalising its symbolic value *)
Ltac s5e_reg HS r P :=
  lazymatch type of HS with
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_restrict_reg segs H E ss ms r HS) as P;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in P
  end.

(* ================================ the words the tail computes ================================ *)
Lemma s5e_denot_mod : forall E e v, U E e mod 2 ^ 64 = v mod 2 ^ 64 -> sv_denot E e = w64 v.
Proof. intros E e v H. rewrite denot_lit_U. unfold w64. apply Z_to_bv64_eq_mod. exact H. Qed.
Lemma s5e_U_atom_mod : forall E n v, ew E n = Z_to_bv 64 v -> U E (SOff n 0) = v mod 2 ^ 64.
Proof.
intros E n v H. rewrite U_SOff, H, Z.add_0_r, Z_to_bv_unsigned. unfold zcanon, M64, bv_wrap.
change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. lia.
Qed.
Lemma s5e_atom : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.
(* 0x851d8 .. 0x851e4: xor; snez; addiw -1; and s6 -- s6 when the two words are equal, 0 otherwise *)
Lemma s5e_latch : forall E r nn (ret : bool),
  ew E 10 = Z_to_bv 64 r -> ew E 33 = Z_to_bv 64 nn -> ew E 22 = Z_to_bv 64 (seg_spec.b2z ret) ->
  0 <= r < 2 ^ 64 -> 0 <= nn < 2 ^ 64 ->
  sv_denot E (SAlu ALU_AND (SAlu ALU_ADD (SAlu ALU_SLTU (SLit 0) (SAlu ALU_XOR (SOff 10 0) (SOff 33 0)))
    (SLit (-1))) (SOff 22 0)) = w64 (seg_spec.b2z (ret && (r =? nn))).
Proof.
intros E r nn ret H10 H33 H22 Hr Hn. apply s5e_denot_mod.
rewrite !U_SAlu, !U_SLit, (s5e_U_atom_mod E 10 r H10), (s5e_U_atom_mod E 33 nn H33), (s5e_U_atom_mod E 22 _ H22).
rewrite (Z.mod_small r), (Z.mod_small nn) by lia.
assert (Hb : 0 <= seg_spec.b2z ret < 2 ^ 64) by (destruct ret; cbn; lia).
rewrite (Z.mod_small (seg_spec.b2z ret)) by lia.
cbn [zalu_raw]. unfold zcanon, M64.
destruct (Z.eqb_spec r nn) as [<- | Hne].
- rewrite Z.lxor_nilpotent, andb_true_r. destruct ret; reflexivity.
- rewrite andb_false_r.
  assert (Hx0 : 0 < Z.lxor r nn).
  { assert (H0 : 0 <= Z.lxor r nn) by (apply Z.lxor_nonneg; lia).
    assert (H1 : Z.lxor r nn <> 0) by (rewrite Z.lxor_eq_0_iff; exact Hne). lia. }
  assert (Hx1 : Z.lxor r nn < 2 ^ 64).
  { apply (proj2 (Z.log2_lt_pow2 _ 64 Hx0)).
    pose proof (Z.log2_lxor r nn ltac:(lia) ltac:(lia)) as Hl.
    assert (Hr2 : Z.log2 r < 64).
    { destruct (Z.eq_dec r 0) as [->|Hr0]; [cbn; lia|]. apply (proj1 (Z.log2_lt_pow2 r 64 ltac:(lia))). lia. }
    assert (Hn2 : Z.log2 nn < 64).
    { destruct (Z.eq_dec nn 0) as [->|Hn0]; [cbn; lia|]. apply (proj1 (Z.log2_lt_pow2 nn 64 ltac:(lia))). lia. }
    lia. }
  rewrite (Z.mod_0_l (2 ^ 64)) by lia. rewrite (Z.mod_small (Z.lxor r nn)) by lia.
  replace (0 <? Z.lxor r nn) with true by (symmetry; apply Z.ltb_lt; exact Hx0).
  destruct ret; reflexivity.
Qed.
(* 0x85408 `sub s4,a0,s11`: the count left *)
Lemma s5e_sub : forall E L np,
  ew E 27 = Z_to_bv 64 np -> ew E 34 = Z_to_bv 64 L ->
  sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff 27 0) (SLit (-1))) (SOff 34 0)) = w64 (L - np).
Proof.
intros E L np H27 H34. apply s5e_denot_mod.
rewrite U_SAlu, U_SMd, U_SLit, (s5e_U_atom_mod E 27 np H27), (s5e_U_atom_mod E 34 L H34).
cbn [zalu_raw zmd_raw]. unfold zcanon, M64.
rewrite Z.mod_mod by lia. rewrite Z.mul_mod_idemp_l, Z.mul_mod_idemp_r by lia.
rewrite Z.add_mod_idemp_l, Z.add_mod_idemp_r by lia.
f_equal. ring.
Qed.
(* 0x85404 `add s8,s8,s11`: the cursor moves past the turn's bytes *)
Lemma s5e_add : forall E a b,
  ew E 24 = Z_to_bv 64 a -> ew E 27 = Z_to_bv 64 b ->
  sv_denot E (SAlu ALU_ADD (SOff 24 0) (SOff 27 0)) = w64 (a + b).
Proof.
intros E a b H24 H27. apply s5e_denot_mod.
rewrite U_SAlu, (s5e_U_atom_mod E 24 a H24), (s5e_U_atom_mod E 27 b H27). cbn [zalu_raw]. unfold zcanon, M64.
rewrite Z.mod_mod by lia. rewrite Z.add_mod_idemp_l, Z.add_mod_idemp_r by lia. reflexivity.
Qed.
(* s10 = (m + 0x2000) >> 3 (0x85198) *)
Lemma s5e_srl : forall E mn, ew E 32 = Z_to_bv 64 mn -> 0 <= mn < 2 ^ 64 ->
  sv_denot E (SAlu ALU_SRL (SOff 32 0) (SLit 3)) = w64 (mn / 8).
Proof.
intros E mn H32 Hmn. apply s5e_denot_mod.
rewrite U_SAlu, U_SLit, (s5e_U_atom_mod E 32 mn H32). cbn [zalu_raw]. unfold zcanon, M64.
rewrite (Z.mod_small mn) by lia. change (Z.land (3 mod 2 ^ 64) 63) with 3.
rewrite Z.shiftr_div_pow2 by lia. rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* ================================ readers, words, registers ================================ *)
Lemma s5e_word_kept : forall (rd rd' : reader) a v,
  (forall x, a <= x < a + 8 -> rd' x = rd x) -> rdword rd a = Some v -> rdword rd' a = Some v.
Proof. intros rd rd' a v HK H. rewrite (rdword_ext rd rd' a); [exact H|]. intros k Hk. apply HK. lia. Qed.
Lemma s5e_pres : forall regs regs' (r : bv 5) z,
  aregs_preserved regs regs' -> acallee_saved z -> Z_to_bv 5 z = r -> getr regs' r = getr regs r.
Proof. intros regs regs' r z HP Hz <-. exact (HP z Hz). Qed.
Lemma s5e_bytes_kept : forall (rd rd' : reader) a bs,
  (forall i, 0 <= i < Z.of_nat (length bs) -> rd' (a + i) = rd (a + i)) -> sa_bytes rd a bs -> sa_bytes rd' a bs.
Proof. intros rd rd' a bs HK H i Hi. rewrite (HK (Z.of_nat i)) by lia. exact (H i Hi). Qed.
Lemma s5e_rconf_kept : forall (rd rd' : reader) c rc0,
  (forall i, 0 <= i < seg_spec.SEG_C_SIZE -> rd' (c + i) = rd (c + i)) -> sa_rconf rd c rc0 -> sa_rconf rd' c rc0.
Proof.
intros rd rd' c rc0 HK (bs & Hb & He). exists bs. split; [|exact He].
apply (s5e_bytes_kept rd); [|exact Hb]. pose proof He as (Hl & _). rewrite Hl. exact HK.
Qed.
Lemma s5e_mconf_kept : forall (rd rd' : reader) m mc0,
  (forall i, 0 <= i < seg_spec.SEG_M_SIZE -> rd' (m + i) = rd (m + i)) -> sa_mconf rd m mc0 -> sa_mconf rd' m mc0.
Proof.
intros rd rd' m mc0 HK (bs & Hb & He). exists bs. split; [|exact He].
apply (s5e_bytes_kept rd); [|exact Hb]. pose proof He as (Hl & _). rewrite Hl. exact HK.
Qed.
(* the 4 bytes of a u32 field of an encoding, as the reader shows them *)
Lemma s5e_nth_le : forall n z k, (k < n)%nat ->
  nth k (Z_to_le_bytes n z) ZB0 = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k)).
Proof.
induction n as [|n IH]; intros z k Hk; [lia|].
destruct k as [|k]; cbn [Z_to_le_bytes nth].
- change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
- rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. lia.
Qed.
Lemma s5e_rd32 : forall (rd : reader) a bs off v,
  sa_bytes rd a bs -> seg_spec.u32_enc v (seg_spec.fldz off 4 bs) ->
  0 <= off -> off + 4 <= Z.of_nat (length bs) -> rd32 rd (a + off) v.
Proof.
intros rd a bs off v Hb (Hv & Hf) Ho Hl k Hk.
assert (Hi : (Z.to_nat off + k < length bs)%nat) by lia.
replace (a + off + Z.of_nat k) with (a + Z.of_nat (Z.to_nat off + k)) by lia.
rewrite (Hb _ Hi). f_equal.
assert (Hn : nth (Z.to_nat off + k) bs ZB0 = nth k (seg_spec.fldz off 4 bs) ZB0).
{ unfold seg_spec.fldz, seg_spec.fld. change (Z.to_nat 4) with 4%nat.
  rewrite <- (firstn_skipn (Z.to_nat off) bs) at 1.
  rewrite app_nth2 by (rewrite length_firstn; lia). rewrite length_firstn.
  replace (Z.to_nat off + k - Nat.min (Z.to_nat off) (length bs))%nat with k by lia.
  rewrite <- (firstn_skipn 4 (skipn (Z.to_nat off) bs)) at 1.
  rewrite app_nth1 by (rewrite length_firstn, length_skipn; lia). reflexivity. }
rewrite Hn, Hf. unfold OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Mem.le4.
rewrite unsigned_lit_small by lia. rewrite (s5e_nth_le 4 v k Hk).
rewrite Z_to_bv_unsigned. unfold le_byte, bv_wrap. change (8 * Z.of_nat 4) with 32.
rewrite (Z.mod_small v (2 ^ 32)) by lia. reflexivity.
Qed.

(* ================================ the model side of turn f ================================ *)
(* turn f is not the last: seg_after takes seg_turn_step's non-last branch, whose state is s5_rp's reader,
   s5_mc1's model and the latch *)
Lemma s5e_af : forall pl f, Z.of_nat f + 1 < seg_spec.seg_nfiles pl ->
  seg_spec.seg_after pl f =
  (fst (s5_rp pl f), s5_mc1 pl f,
   seg_spec.seg_ret (seg_spec.seg_run pl f) &&
   (snd (s5_rp pl f) =? Z.of_nat (length (SegModel.mc_seg (s5_mc1 pl f))))).
Proof.
intros pl f Hf. unfold seg_spec.seg_after.
replace (Z.of_nat (Datatypes.S f) =? seg_spec.seg_nfiles pl) with false by (symmetry; apply Z.eqb_neq; lia).
unfold seg_spec.seg_turn_step, s5_rp, s5_mc1, s5_txt, s5_lab, seg_spec.seg_rc, seg_spec.seg_mc, seg_spec.seg_ret.
destruct (seg_spec.seg_run pl f) as [[c0 mc0] ret0]. cbn [fst snd].
destruct (SegModel.r_parse_file c0 (seg_spec.seg_txt pl f) (seg_spec.seg_label pl f)) as [c1 n1].
reflexivity.
Qed.
(* the reader's answer is the count of entries it holds (so 0 .. 32 by rconf_enc) *)
Lemma s5e_rp_n : forall pl f, snd (s5_rp pl f) = Z.of_nat (length (SegModel.rc_seg (fst (s5_rp pl f)))).
Proof.
intros pl f. unfold s5_rp, SegModel.r_parse_file. cbv zeta.
match goal with |- context [SegModel.r_lines ?a ?b ?c] => destruct (SegModel.r_lines a b c) as [[c2 x] y] end.
reflexivity.
Qed.

(* ================================ the next turn's cursor; the seed of the tail ================================ *)
Section s5e_rd. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* K85414's cursor and count after turn f: the turn's tail past the bytes it took (s5_cur_S) *)
Lemma s5e_cur_next : forall cx f, Z.of_nat f < x_nf cx ->
  x_cur cx (Datatypes.S f) = seg_spec.seg_turn_at (x_pl cx) (x_p cx) f + seg_spec.seg_turn_np (x_pl cx) f /\
  x_curn cx (Datatypes.S f) =
    Z.of_nat (length (seg_spec.seg_turn_tail (x_pl cx) f)) - seg_spec.seg_turn_np (x_pl cx) f.
Proof.
intros cx f Hf.
destruct (s5_txt_firstn (x_pl cx) f Hf) as (_ & _ & Hle).
assert (Hnp0 : 0 <= seg_spec.seg_turn_np (x_pl cx) f) by (unfold seg_spec.seg_turn_np; lia).
assert (Hc : Z.of_nat (length (seg_spec.seg_cur (x_pl cx) (Datatypes.S f))) =
  Z.of_nat (length (seg_spec.seg_turn_tail (x_pl cx) f)) - seg_spec.seg_turn_np (x_pl cx) f).
{ rewrite s5_cur_S, length_skipn. lia. }
unfold x_cur, x_curn, seg_spec.seg_cur_at, seg_spec.seg_cur_n, seg_spec.seg_turn_at. rewrite Hc.
split; ring.
Qed.

(* the valuation: the registers, then atom 32 = m + 0x2000, 33 = m->n, 34 = 152(s1) *)
Definition s5e_E (regs : bvmap 5 word) (mn nn L : Z) : env :=
  Eimg (Ereg regs [Z_to_bv 64 mn; Z_to_bv 64 nn; Z_to_bv 64 L]).
Lemma s5e_E_reg : forall regs mn nn L n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (s5e_E regs mn nn L) n = getr regs r.
Proof. intros regs mn nn L n r Hn. unfold s5e_E. apply ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma s5e_E_x : forall regs mn nn L,
  ew (s5e_E regs mn nn L) 32 = Z_to_bv 64 mn /\ ew (s5e_E regs mn nn L) 33 = Z_to_bv 64 nn /\
  ew (s5e_E regs mn nn L) 34 = Z_to_bv 64 L.
Proof.
intros regs mn nn L. unfold s5e_E. rewrite !Eimg_low by (unfold A_TEXT; lia).
split; [exact (ew_Ereg_extra regs _ 0) | split; [exact (ew_Ereg_extra regs _ 1) | exact (ew_Ereg_extra regs _ 2)]].
Qed.

Lemma s5e_seed : forall (W : world SEGS) regs mem (s1 mn nn L : Z),
  getr regs 9 = w64 s1 -> getr regs 26 = w64 (mn / 8) ->
  0 <= s1 -> s1 + 192 <= 2 ^ 64 ->
  4096 <= mn <= 0x7fffff800000 -> mn mod 8 = 0 -> mn + 4 <= s1 + 152 ->
  0 <= nn <= 32 -> 0 <= L < 2 ^ 64 ->
  rdword (rdW W mem) (s1 + 152) = Some L -> rdword (rdW W mem) (s1 + 176) = Some SHADOW_OFF ->
  rdword (rdW W mem) (s1 + 184) = Some mn -> rd32 (rdW W mem) mn nn ->
  st_ok_pi SEGS VAL (s5e_E regs mn nn L) s5e_ss
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO_S5CK)) mem (seg_rom SEGS))).
Proof.
intros W regs mem s1 mn nn L R9 R26 Hs10 Hs11 Hmn Hmn8 Hdis Hnn HL S152 S176 S184 H32.
pose proof (s5e_E_x regs mn nn L) as (E32 & E33 & E34).
assert (E9 : ew (s5e_E regs mn nn L) 9 = getr regs 9) by (apply s5e_E_reg; reflexivity).
set (E := s5e_E regs mn nn L) in *.
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
assert (V9 : base_val E (Some 9%nat) = s1) by (apply VB; [rewrite E9; exact R9 | lia]).
assert (V32 : base_val E (Some 32%nat) = mn) by (apply VB; [exact E32 | lia]).
rewrite restrict_mkst_fx. unfold s5e_ss. apply pa_entry_st_ok_full.
- intros r. destruct (decide (r = 26%bv)) as [->|Hne].
  + rewrite sr_get_set_same by reflexivity. rewrite R26. symmetry. apply s5e_srl; [exact E32 | lia].
  + rewrite sr_get_set_other by exact Hne. exact (regs_ok_Eimg_Ereg regs _ r).
- vm_compute. reflexivity.
- unfold s5e_regions. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + rewrite V9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    * apply (chunk_ok_val SEGS E _ s1 152 8 (SOff 34 0) L); [rewrite s5e_atom; exact E34 | cbn; lia | cbn; lia |].
      exact (val_mem_of_rdword SEGS (w_H W) mem _ _ S152).
    * apply (chunk_ok_val SEGS E _ s1 176 8 (SLit SHADOW_OFF) SHADOW_OFF);
        [reflexivity | unfold SHADOW_OFF; cbn; lia | cbn; lia |].
      exact (val_mem_of_rdword SEGS (w_H W) mem _ _ S176).
    * apply (chunk_ok_val SEGS E _ s1 184 8 (SOff 32 0) mn); [rewrite s5e_atom; exact E32 | cbn; lia | cbn; lia |].
      exact (val_mem_of_rdword SEGS (w_H W) mem _ _ S184).
  + rewrite V32. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ mn 0 4 (SOff 33 0) nn); [rewrite s5e_atom; exact E33 | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H W) mem _ _ H32).
- unfold s5e_regions. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite V9, V32.
  repeat split; lia.
- split; [|split; exact I].
  cbn [s5e_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E32, E33, !unsigned_lit_small by lia.
  change (2 ^ 3) with 8. rewrite Z.pow_0_r, Z.mod_1_r. repeat split; lia.
Qed.
End s5e_rd.

(* ================================ the harness's state across the tail ================================ *)
Section s5e_kit. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis MTL : ameter_laws MT.
Hypothesis IMGS : s10_img.
Hypothesis BSYM : AF0m.SegBSyms B.

(* the entry sp and the realigned base S1 (andi sp,sp,-32 at 0x84d74 after addi sp,sp,-320) *)
Lemma s5e_sp : forall cx, lt_base B MT cx ->
  x_sp0 cx mod 16 = 0 /\ alloc_ceiling + STK_LLVMFuzzerTestOneInput <= x_sp0 cx /\ x_sp0 cx <= 2 ^ 47 /\
  x_s1 cx mod 32 = 0 /\ x_sp0 cx - 336 <= x_s1 cx /\ x_s1 cx <= x_sp0 cx - 320.
Proof using All.
intros cx HB. destruct HB as (HPRE & _). destruct HPRE as (_ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal & _ & Hceil & Hslo & Hshi & H47 & _).
unfold x_s1, x_sp0, LT_FRAME in *.
set (s := spZ (x_regs cx)) in *. clearbody s.
repeat split; lia.
Qed.
(* the frame address of a journal's target layout is the entry's *)
Lemma s5e_frame_addr : forall STK sp0 FP ly0 S0 W0 mem0 md0 own ly S (W : world SEGS) mem md k,
  ajournal SEGS B STK sp0 FP ly0 S0 W0 mem0 md0 own ly S W mem md k ->
  forall cid pos, frame_addr ly cid pos = frame_addr ly0 cid pos.
Proof using All.
intros STK sp0 FP ly0 S0 W0 mem0 md0 own ly S W mem md k HJ cid pos.
destruct HJ as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & EF & _). unfold frame_addr. rewrite EF. reflexivity.
Qed.
(* a live block of a state is a harness block of that state *)
Lemma s5e_hblk : forall ly S (W : world SEGS) mem md a n,
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
(* the first block of a list the live blocks are a permutation of is apart from every other one of it *)
Lemma s5e_sep2 : forall ly S (W : world SEGS) mem md x y l,
  AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) (x :: l) -> In y l ->
  zdisjoint (block_rng x) (block_rng y).
Proof using All.
intros ly S W mem md x y l HAR HP Hy.
destruct (in_split y l Hy) as (l1 & l2 & ->).
apply (sep_blocks_perm SEGS B LAWS ly S W mem md x y (l1 ++ l2) HAR).
eapply Permutation_trans; [exact HP|]. apply perm_skip. apply Permutation_sym. apply Permutation_middle.
Qed.
(* a chain for the call's chain_pre: the stack from S1 to the layout's top is mapped, s0 = SP0 >= S1 + 320 *)
Lemma s5e_chain : forall cx ly S (W : world SEGS) regs mem md k,
  lt_base B MT cx ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem md k ->
  getr regs 2 = w64 (x_s1 cx) -> getr regs 8 = w64 (x_sp0 cx) -> 4096 <= raZ regs ->
  exists ch, chain_pre ly (rdW W mem) regs ch.
Proof using All.
intros cx ly S W regs mem md k HB HJ R2 R8 Hra.
pose proof (s5e_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
assert (WS : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity.
pose proof HB as (_ & HPRES & _).
pose proof asan_consts as (C1 & _).
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
(* the facts of a point carried across a run that wrote nothing and kept sp, gp, tp, s0, s1 *)
Lemma s5e_core_kept : forall cx ly S (W : world SEGS) regs mem md k acc rem o O regs' mem' md',
  lt_base B MT cx -> lt_core B MT cx ly S W regs mem md k acc rem o O ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem' md' k ->
  (forall a, 0 <= a < 2 ^ 64 -> rdW W mem' a = rdW W mem a) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
  lt_core B MT cx ly S W regs' mem' md' k acc rem o O.
Proof using All.
intros cx ly S W regs mem md k acc rem o O regs' mem' md' HB HC HJ' HK P2 P3 P4 P8 P9.
pose proof (s5e_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
assert (WS : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity.
destruct HC as (HF & HI & HBL & HBUD).
destruct HF as (HJ & R2 & R3 & R4 & R8 & R9 & HSV & HH0 & HH8 & HH16 & HFL & H176 & HSH).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HinF : In (LT_FCLS, x_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (EF : frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx)
  by exact (s5e_frame_addr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ _ _).
assert (F512 : fs_frame_bytes LT_FCLS = 512) by (vm_compute; reflexivity).
destruct (frames_bounds SEGS B LAWS ly S W mem md LT_FCLS (x_fpos cx) HAR HinF) as (Hf0 & Hfc & _).
rewrite EF in Hf0. rewrite EF, F512 in Hfc.
split; [|split; [|split]].
- split; [exact HJ'|].
  rewrite P2, P3, P4, P8, P9.
  split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R8|]. split; [exact R9|].
  split.
  { intros i r Hi. assert (Hi13 : (i < length LT_SAVED)%nat) by (apply nth_error_Some; congruence).
    change (length LT_SAVED) with 13%nat in Hi13.
    apply (s5e_word_kept (rdW W mem)); [|exact (HSV i r Hi)]. intros x Hx. apply HK. lia. }
  split; [apply (s5e_word_kept (rdW W mem)); [|exact HH0]; intros x Hx; apply HK; lia|].
  split; [apply (s5e_word_kept (rdW W mem)); [|exact HH8]; intros x Hx; apply HK; lia|].
  split; [apply (s5e_word_kept (rdW W mem)); [|exact HH16]; intros x Hx; apply HK; lia|].
  split; [apply (s5e_word_kept (rdW W mem)); [|exact HFL]; intros x Hx; apply HK; unfold LT_FLAGW in *; lia|].
  split; [apply (s5e_word_kept (rdW W mem)); [|exact H176]; intros x Hx; apply HK; lia|].
  intros i Hi. rewrite HK; [exact (HSH i Hi)|]. rewrite (lt_fsh_len o) in Hi.
  unfold x_sh, shadow_addr, SHADOW_OFF. lia.
- apply (s10_lt_img_kept B IMGS BSYM cx W mem' (rdW W mem) (proj1 HJ')); [|exact HI].
  intros a Ha _ _. apply HK. pose proof (pa_segs_low a Ha). lia.
- exact HBL.
- exact HBUD.
Qed.
(* the facts of a point after one free of the harness at sp = S1: the journal from the entry goes on with one
   event, the freed block leaves the harness's blocks, every byte the facts read is kept (it lies on the stack
   above S1, in the frame and its shadow, in the image, or in another block), the budget pays one event *)
Lemma s5e_after_free : forall cx ly S (W : world SEGS) regsT memT md k acc rem o O
  ly2 S2 (W2 : world SEGS) regs2 mem2 md2 t tn l1 l2,
  lt_base B MT cx -> lt_core B MT cx ly S W regsT memT md k acc rem o ((t, tn) :: O) ->
  1 <= rem -> 0 <= tn ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly2 S2 W2 mem2 md2 (k + 1) ->
  aregs_preserved regsT regs2 -> frames S2 = frames S ->
  ablocks B ly S = l1 ++ (t, tn) :: l2 -> ablocks B ly2 S2 = l1 ++ l2 ->
  acall_kept SEGS B ly S W memT W2 mem2 (x_s1 cx - ASTACK) (x_s1 cx) (fun a => t <= a < t + req_size tn) ->
  mo_le MT S S2 (mo_free MT) ->
  lt_core B MT cx ly2 S2 W2 regs2 mem2 md2 (k + 1) (acc + mo_free MT) (rem - 1) o O /\
  (forall a, x_s1 cx <= a < 2 ^ 64 -> rdW W2 mem2 a = rdW W memT a) /\
  (forall b n, In (b, n) O -> In (b, n) (ablocks B ly2 S2) /\
     (forall i, 0 <= i < req_size n -> rdW W2 mem2 (b + i) = rdW W memT (b + i))).
Proof using All.
intros cx ly S W regsT memT md k acc rem o O ly2 S2 W2 regs2 mem2 md2 t tn l1 l2 HB HC Hrem Htn HJ2 HP Hfr2 Ebl
  Ebl2 HKc MLE.
pose proof (s5e_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
assert (WS : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity.
destruct HC as (HF & HI & HBL & HBUD).
destruct HF as (HJ & R2 & R3 & R4 & R8 & R9 & HSV & HH0 & HH8 & HH16 & HFL & H176 & HSH).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
pose proof HKc as (K1 & K2 & K3 & K4 & _ & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold lt_blocks in HBL. cbn [app] in HBL.
assert (HinT : In (t, tn) (ablocks B ly S)) by (rewrite Ebl; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS ly S W memT md t tn HAR HinT) as (_ & Ht4096 & Htceil & Htapp & _ & _ & _).
pose proof (req_size_pos tn Htn) as [Hrq1 Hrq2].
(* the freed block is apart from every other harness block and every entry block *)
assert (HsepO : forall b n, In (b, n) (O ++ x_bl0 B cx) -> t + req_size tn <= b \/ b + req_size n <= t).
{ intros b n Hb. pose proof (s5e_sep2 ly S W memT md (t, tn) (b, n) (O ++ x_bl0 B cx) HAR HBL Hb) as Hd.
  unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. exact Hd. }
assert (HinO : forall b n, In (b, n) O -> In (b, n) (ablocks B ly S)).
{ intros b n Hb. apply (Permutation_in _ (Permutation_sym HBL)). right. apply in_or_app. left. exact Hb. }
assert (HinO2 : forall b n, In (b, n) O -> In (b, n) (ablocks B ly2 S2)).
{ intros b n Hb. pose proof (HinO b n Hb) as Hb'. rewrite Ebl in Hb'. rewrite Ebl2.
  apply in_app_or in Hb' as [Hb' | [Hb' | Hb']]; [apply in_or_app; left; exact Hb' | | apply in_or_app; right; exact Hb'].
  exfalso. injection Hb' as E1 E2. subst b n.
  pose proof (HsepO t tn ltac:(apply in_or_app; left; exact Hb)) as Hd. lia. }
assert (KO : forall b n, In (b, n) O -> forall i, 0 <= i < req_size n -> rdW W2 mem2 (b + i) = rdW W memT (b + i)).
{ intros b n Hb i Hi. apply (K2 b n i (HinO b n Hb) Hi). cbv beta. intros Hc.
  pose proof (HsepO b n ltac:(apply in_or_app; left; exact Hb)) as Hd. lia. }
(* the frame *)
assert (HinF : In (LT_FCLS, x_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (EF : frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx)
  by exact (s5e_frame_addr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ _ _).
assert (F512 : fs_frame_bytes LT_FCLS = 512) by (vm_compute; reflexivity).
destruct (frames_bounds SEGS B LAWS ly S W memT md LT_FCLS (x_fpos cx) HAR HinF) as (Hf0 & Hfc & _).
rewrite EF in Hf0. rewrite EF, F512 in Hfc.
pose proof (sep_block_frame SEGS B LAWS ly S W memT md t tn LT_FCLS (x_fpos cx) HAR HinT HinF) as Hsep.
rewrite EF, F512 in Hsep. unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
(* the stack above S1 *)
assert (KS : forall a, x_s1 cx <= a < 2 ^ 64 -> rdW W2 mem2 a = rdW W memT a).
{ intros a Ha. apply K1; [lia|]. intros [_ Hc]. lia. }
(* the frame's bytes *)
assert (KF : forall a, x_fr cx <= a < x_fr cx + 512 -> rdW W2 mem2 a = rdW W memT a).
{ intros a Ha. apply (K4 LT_FCLS (x_fpos cx) a HinF).
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF, F512. lia.
  - cbv beta. intros Hr. lia. }
(* the frame's shadow bytes *)
assert (KH : forall i, 0 <= i < 64 -> rdW W2 mem2 (x_sh cx + i) = rdW W memT (x_sh cx + i)).
{ intros i Hi. apply (K4 LT_FCLS (x_fpos cx) _ HinF).
  - right. unfold in_zr. cbn [fst snd]. rewrite EF, F512. unfold x_sh. lia.
  - cbv beta. intros Hr. unfold in_app, kLowShadowBeg, ASAN_CEIL in Htapp. unfold x_sh, shadow_addr, SHADOW_OFF in Hr.
    lia. }
split; [|split; [exact KS | intros b n Hb; split; [exact (HinO2 b n Hb) | exact (KO b n Hb)]]].
split; [|split; [|split]].
- (* the frame *)
  split; [exact HJ2|].
  rewrite (s5e_pres _ _ 2%bv 2 HP ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (s5e_pres _ _ 3%bv 3 HP ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (s5e_pres _ _ 4%bv 4 HP ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (s5e_pres _ _ 8%bv 8 HP ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (s5e_pres _ _ 9%bv 9 HP ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R8|]. split; [exact R9|].
  split.
  { intros i r Hi. assert (Hi13 : (i < length LT_SAVED)%nat) by (apply nth_error_Some; congruence).
    change (length LT_SAVED) with 13%nat in Hi13.
    apply (s5e_word_kept (rdW W memT)); [|exact (HSV i r Hi)]. intros x Hx. apply KS. lia. }
  split; [apply (s5e_word_kept (rdW W memT)); [|exact HH0]; intros x Hx; apply KF; lia|].
  split; [apply (s5e_word_kept (rdW W memT)); [|exact HH8]; intros x Hx; apply KF; lia|].
  split; [apply (s5e_word_kept (rdW W memT)); [|exact HH16]; intros x Hx; apply KF; unfold LT_FLAGW; lia|].
  split; [apply (s5e_word_kept (rdW W memT)); [|exact HFL]; intros x Hx; apply KF; unfold LT_FLAGW in *; lia|].
  split; [apply (s5e_word_kept (rdW W memT)); [|exact H176]; intros x Hx; apply KS; lia|].
  intros i Hi. rewrite (lt_fsh_len o) in Hi. rewrite KH by lia. exact (HSH i ltac:(rewrite lt_fsh_len; exact Hi)).
- (* the image facts *)
  exact (s10_lt_img_kept B IMGS BSYM cx W2 mem2 (rdW W memT) (proj1 HJ2) K3 HI).
- (* the blocks: the freed one leaves *)
  unfold lt_blocks. rewrite Ebl2. apply Permutation_cons_inv with (t, tn).
  eapply Permutation_trans; [apply Permutation_middle|]. rewrite <- Ebl. exact HBL.
- (* the budget: one event *)
  destruct HBUD as (B1 & B2 & B3 & B4 & B5 & B6).
  pose proof (mo_malloc_nonneg MT MTL 65536 ltac:(lia)) as M0.
  pose proof (mo_free_nonneg MT MTL) as M3.
  assert (HU : mo_free MT <= LT_U MT) by (unfold LT_U; lia).
  unfold lt_bud. split; [lia|]. split; [lia|]. split; [lia|].
  split; [exact (mo_le_trans MT MTL _ _ _ _ _ B4 MLE)|]. split; [lia|].
  set (U := LT_U MT) in *. clearbody U. nia.
Qed.
End s5e_kit.

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
Variable snp_lo snp_hi : Z.
Variable snp_cr : list (Z * Z).
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis IMGS : s10_img.
Hypothesis BSYM : AF0m.SegBSyms B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis PRW : prog_rw SEGS B.
Hypothesis VOBJS : seg_val_objs.
Hypothesis SIGP : seg_sig_prog.
Hypothesis HPGS : forall a, inFP (ltoi_PG longlA) a ->
  Exists (in_zr a) (as_prog_static B) /\ in_img SEGS a.
Hypothesis HPG_RO : forall a, inFP (ltoi_PG longlA) a -> ~ in_roP SEGS RLO_A RHI_A a.
Hypothesis HPG_PTR : forall a p,
  ((exists i, (i < 5)%nat /\ a = wordsA + 8 * Z.of_nat i) \/
   (exists i, (i < pin_spec.CAT_N)%nat /\ a = pin_spec.row_addr catA i)) ->
  rdword (fun x => option_map (fun b : byte => bv_unsigned b) (seg_rom SEGS (Z_to_bv 64 x))) a = Some p ->
  p + 65536 <= longlA.
Hypothesis AMEMCPY : forall fx0 : YK11.FPState,
  @aintrin_realizes fx0 rc SEGS B OCpy (SIG SS___asan_memcpy).
Hypothesis AMEMSET : forall fx0 : YK11.FPState,
  @aintrin_realizes fx0 rc SEGS B OSet (SIG SS___asan_memset).
Hypothesis AFREE4 : forall fx0 : YK11.FPState, @afree04_rule fx0 rc SK SEGS B MT.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState,
  @RtPFSeg.seg_asnprintf_realizes fx0 rc SEGS B snp_lo snp_hi snp_cr
    (SIG SS___interceptor_trampoline_snprintf) gotwA guardA.
Hypothesis HSNP_LIT : forall x, In x LLVMFuzzerTestOneInput_c.LTOI_LITS ->
  snp_lo <= seg_litA_fz x /\ seg_litA_fz x + Z.of_nat (length x) + 1 <= gotwA.
Hypothesis HSNP_CR : Forall (fun r => snp_lo <= fst r /\ 0 <= snd r /\ fst r + snd r <= snp_hi) snp_cr.
Hypothesis HSNP_LO : 0 <= snp_lo.
Hypothesis HSNP_CEIL : snp_hi <= alloc_ceiling.
Hypothesis HSNP_FAKE : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> snp_hi <= ly_F ly.
Hypothesis HM_FILE : forall fx0 : YK11.FPState,
  @m_file_c.m_file_contract fx0 rc SK SEGS B (BASE + AF_m_file) STK_m_file RLO_A RHI_A seg_litA_fz
    wordsA rolesA catA gotwA guardA.
Hypothesis HPARSE_FILE : forall fx0 : YK11.FPState,
  @reac_segconf_parse_file_c.reac_segconf_parse_file_contract fx0 rc SK SEGS B
    (BASE + AF_reac_segconf_parse_file) STK_reac_segconf_parse_file RLO_A RHI_A seg_litA_rc catA gotwA guardA.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* L5: 0x851c0 (S5_CK f) .. 0x85414 (K85414 f). One token run 0x851c0 .. 0x85410: a1 := 176(s1), check 8 on
   s10 + a1 (the shadow entry covers &m->n), a1 := 184(s1), lw m->n, the latch of s6, a0 := 152(s1), j 0x85404,
   s8 += s11, s4 := a0 - s11, a0 := s7 and the jal of the free wrapper; then free(text) by afree04_sub, and
   K85414 f at the return. *)
Lemma s5_tail : forall f, LTA_K85414 B MT f -> S5_CK_stmt B MT f.
Proof using All.
intros f HKA cx ly S W regs mem md k acc c m t lp HB Hfrm Hf1 HBODY HRC HMC HCNT
  R10 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27 HSL.
pose proof (HKA fx) as HK. clear HKA.
destruct HBODY as (HC & HHc & HHm & HHt & _).
pose proof (s5e_sp B MT MTL IMGS BSYM cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HC as (HF & _ & HBL & HBUD).
pose proof HF as (HJ & F2 & F3 & F4 & F8 & F9 & _ & _ & _ & _ & _ & H176 & _).
pose proof (proj1 HJ) as HAR.
pose proof HB as (HPRE0 & _ & _ & _ & _ & _ & Hpn & Hlen & _ & _ & _ & Hev0 & _ & Hmo0).
pose proof HPRE0 as (_ & _ & _ & Hgp0 & Htp0 & _).
(* the three blocks *)
set (tn := x_tn cx f) in *.
assert (Htn : 1 <= tn) by (unfold tn, x_tn, seg_spec.seg_txt_n; lia).
pose proof HHt as (HinT & _).
pose proof HHm as (HinM & Hm4096 & Hm16 & _).
pose proof HHc as (HinC & Hc4096 & _).
destruct (al_blocks _ _ LAWS ly S W mem md m seg_spec.SEG_M_SIZE HAR HinM) as (_ & _ & Hmceil & Hmapp & _ & _ & _).
destruct (al_blocks _ _ LAWS ly S W mem md c seg_spec.SEG_C_SIZE HAR HinC) as (_ & _ & Hcceil & _ & _ & _ & _).
change (req_size seg_spec.SEG_M_SIZE) with 9236 in Hmceil, Hmapp.
change (req_size seg_spec.SEG_C_SIZE) with 16616 in Hcceil.
(* the values the tail reads: the reader's answer r, m->n, 152(s1), the bytes the turn took, &m->n *)
set (r := snd (s5_rp (x_pl cx) f)) in *.
set (nn := Z.of_nat (length (SegModel.mc_seg (s5_mc1 (x_pl cx) f)))).
set (L := Z.of_nat (length (seg_spec.seg_turn_tail (x_pl cx) f))) in *.
set (np := seg_spec.seg_turn_np (x_pl cx) f) in *.
set (mn := m + seg_spec.MC_N) in *.
assert (Hr : 0 <= r <= 32).
{ pose proof HRC as (bsc & _ & _ & Hc32 & _). unfold r. rewrite s5e_rp_n. lia. }
assert (Hnn : 0 <= nn <= 32 /\ rd32 (rdW W mem) mn nn).
{ pose proof HMC as (bsm & Hbsm & Hlenm & Hm32 & _ & Hu & _).
  split; [unfold nn; lia|].
  apply (s5e_rd32 (rdW W mem) m bsm seg_spec.MC_N nn Hbsm Hu);
    [unfold seg_spec.MC_N; lia | rewrite Hlenm; unfold seg_spec.MC_N, seg_spec.SEG_M_SIZE; lia]. }
destruct Hnn as [Hnn H32].
assert (HL : 0 <= L < 2 ^ 64).
{ pose proof (s5_sfx_len _ _ (s5_tail_sfx (x_pl cx) f)) as Hs.
  unfold seg_spec.seg_in, seg_spec.zs in Hs. rewrite length_map in Hs.
  unfold L. destruct Hpn as [[Hn0 _] | [Hn _]]; lia. }
assert (S152 : rdword (rdW W mem) (x_s1 cx + 152) = Some L)
  by (apply HSL; apply in_or_app; right; left; reflexivity).
assert (S184 : rdword (rdW W mem) (x_s1 cx + 184) = Some mn)
  by (apply HSL; apply in_or_app; left; unfold LT_L; repeat (first [left; reflexivity | right])).
(* the seed, its valuation and its shadow entry *)
pose proof (s5e_E_x regs mn nn L) as (E32 & E33 & E34).
pose proof (s5e_seed W regs mem (x_s1 cx) mn nn L F9 R26 ltac:(lia) ltac:(lia)
  ltac:(unfold mn, seg_spec.MC_N; lia) ltac:(unfold mn, seg_spec.MC_N; lia) ltac:(unfold mn, seg_spec.MC_N; lia)
  Hnn HL S152 H176 S184 H32) as HS.
set (E := s5e_E regs mn nn L) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E, s5e_E; apply Eimg_env).
assert (EE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr)
  by (intros n rr Hn; unfold E; apply s5e_E_reg; exact Hn).
clearbody E.
assert (SHOK : sh_ok SEGS s5e_Bx s5e_SH E (mrestrict (w_H W) mem)).
{ unfold sh_ok, s5e_SH. apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range SEGS (w_H W) mem E s5e_Bx 32 mn 8 mn 0 8).
  - apply (range_addressable_of_block SEGS B LAWS ly S W mem md m seg_spec.SEG_M_SIZE mn 8 HAR HinM);
      change (req_size seg_spec.SEG_M_SIZE) with 9236; unfold mn, seg_spec.MC_N; lia.
  - unfold s5e_Bx. rewrite U_lit; [reflexivity | unfold SHADOW_OFF; lia].
  - rewrite (U_atom E 32 mn E32) by (unfold mn, seg_spec.MC_N; lia). reflexivity.
  - lia.
  - lia.
  - intros x Hx. cbn [Z.min Z.max] in Hx. unfold in_app, kLowShadowBeg in Hmapp. unfold SHADOW_OFF.
    unfold mn, seg_spec.MC_N in Hx. lia. }
(* 0x851c0 .. 0x85410 *)
unfold cfg_at, w64.
paj_run_tok RUN HS HJ SHOK s5e_span.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end.
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md1 := d) in *; clearbody md1 end.
(* the run has no write window: every byte is kept *)
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms) a = rdW W mem a).
{ intros a Ha.
  lazymatch goal with HFr' : frame_of _ ?rs (mrestrict _ mem) (mrestrict _ (ms_mem ms)) |- _ =>
    apply (kept_of_frame (segs := SEGS) E rs (w_H W) mem (ms_mem ms) (fun _ => False) HFr'); [| exact Ha | tauto];
    intros b wlo whi x Hin Hx;
    let w := eval vm_compute in (windows rs) in change (In (b, wlo, whi) w) in Hin end.
  cbn [In] in Hin. exfalso. repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; lia |]). destruct Hin. }
pmkst HS.
rewrite (pal_free B TL).
(* the registers at the jal of the free wrapper *)
s5e_reg HS (1%bv : bv 5) P1. s5e_reg HS (2%bv : bv 5) P2. s5e_reg HS (3%bv : bv 5) P3.
s5e_reg HS (4%bv : bv 5) P4. s5e_reg HS (8%bv : bv 5) P8. s5e_reg HS (9%bv : bv 5) P9.
s5e_reg HS (10%bv : bv 5) P10. s5e_reg HS (18%bv : bv 5) P18. s5e_reg HS (19%bv : bv 5) P19.
s5e_reg HS (20%bv : bv 5) P20. s5e_reg HS (21%bv : bv 5) P21. s5e_reg HS (22%bv : bv 5) P22.
s5e_reg HS (24%bv : bv 5) P24. s5e_reg HS (25%bv : bv 5) P25. s5e_reg HS (26%bv : bv 5) P26.
assert (GA : forall (rr : bv 5) n, getr (ms_regs ms) rr = sv_denot E (SOff n 0) -> Z.of_nat n = bv_unsigned rr ->
  getr (ms_regs ms) rr = getr regs rr) by (intros rr n Hq Hn; rewrite Hq, s5e_atom; apply EE; exact Hn).
pose proof (GA _ 2%nat P2 eq_refl) as G2. pose proof (GA _ 3%nat P3 eq_refl) as G3.
pose proof (GA _ 4%nat P4 eq_refl) as G4. pose proof (GA _ 8%nat P8 eq_refl) as G8.
pose proof (GA _ 9%nat P9 eq_refl) as G9. pose proof (GA _ 18%nat P18 eq_refl) as G18.
pose proof (GA _ 19%nat P19 eq_refl) as G19. pose proof (GA _ 21%nat P21 eq_refl) as G21.
pose proof (GA _ 25%nat P25 eq_refl) as G25.
assert (G1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + LO_K85414)) by (rewrite P1; exact (codeptr_val E 1760 HEI)).
assert (G10 : getr (ms_regs ms) 10 = w64 t) by (rewrite P10, s5e_atom, (EE 23%nat 23%bv eq_refl); exact R23).
assert (G20 : getr (ms_regs ms) 20 = w64 (L - np)).
{ rewrite P20. apply s5e_sub; [rewrite (EE 27%nat 27%bv eq_refl); exact R27 | exact E34]. }
assert (G22 : getr (ms_regs ms) 22 = w64 (seg_spec.b2z (seg_spec.seg_ret (x_st cx f) && (r =? nn)))).
{ rewrite P22. apply s5e_latch;
    [rewrite (EE 10%nat 10%bv eq_refl); exact R10 | exact E33 | rewrite (EE 22%nat 22%bv eq_refl); exact R22 | lia | lia]. }
assert (G24 : getr (ms_regs ms) 24 = w64 (seg_spec.seg_turn_at (x_pl cx) (x_p cx) f + np)).
{ rewrite P24. apply s5e_add; [rewrite (EE 24%nat 24%bv eq_refl); exact R24 | rewrite (EE 27%nat 27%bv eq_refl); exact R27]. }
assert (G26 : getr (ms_regs ms) 26 = w64 (mn / 8))
  by (rewrite P26; apply s5e_srl; [exact E32 | unfold mn, seg_spec.MC_N; lia]).
clear P1 P2 P3 P4 P8 P9 P10 P18 P19 P20 P21 P22 P24 P25 P26 GA.
(* free(text) at 0x85410: the premises of afree04_sub *)
assert (Hsp : spZ (ms_regs ms) = x_sp0 cx + (x_s1 cx - x_sp0 cx)).
{ unfold spZ. rewrite G2, F2. unfold w64. rewrite YP03.unsigned_lit_small by lia. lia. }
assert (Hgp : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite G3, F3; exact Hgp0).
assert (Htp : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite G4, F4; exact Htp0).
assert (Hraw : YK0s.ret_ok (getr (ms_regs ms) 1))
  by (rewrite G1; apply ret_ok_codeptr_v; [unfold LO_K85414; lia | reflexivity]).
assert (Hra4 : 4096 <= raZ (ms_regs ms)).
{ unfold raZ. rewrite G1. rewrite YP03.unsigned_lit_small by (unfold LO_K85414; lia). unfold LO_K85414. lia. }
destruct (s5e_chain B MT MTL IMGS BSYM cx ly S W (ms_regs ms) (ms_mem ms) md1 k HB HJ
  ltac:(rewrite G2; exact F2) ltac:(rewrite G8; exact F8) Hra4) as (ch & Hch).
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _).
pose proof HBUD as (B1 & B2 & B3 & B4 & B5 & B6).
pose proof (mo_malloc_nonneg MT MTL 65536 ltac:(lia)) as M0.
pose proof (mo_free_nonneg MT MTL) as M3.
assert (HU : mo_free MT <= LT_U MT) by (unfold LT_U; lia).
assert (Hnev' : st_nev S < EV_MAX) by lia.
assert (MOK : mo_ok MT S (mo_free MT)).
{ apply (mok_station MT (x_S cx) S (XM_LTOI MT (x_pl cx)) acc (mo_free MT) MTL Hmo0 B4 M3).
  clear - B6 HU Hf1 M3. set (U := LT_U MT) in *. clearbody U. nia. }
assert (Hcov : In (t, tn) (ablocks B (x_ly cx) (x_S cx)) ->
  forall i, 0 <= i < req_size tn -> inFP (ltoi_PG longlA) (t + i)).
{ intros Hb0. exfalso. unfold lt_blocks in HBL.
  pose proof (s5e_sep2 B MT MTL IMGS BSYM ly S W mem md (t, tn) (t, tn) _ HAR HBL
    ltac:(cbn [app]; right; right; exact Hb0)) as Hd.
  unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. pose proof (req_size_pos tn ltac:(lia)) as [Hq _]. lia. }
eapply SRr_bind.
{ exact (afree04_sub SEGS B LAWS pa_segs_low MT (AFREE4 fx) W (ms_regs ms) (ms_mem ms) STK_LLVMFuzzerTestOneInput
    (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [(LT_FCLS, x_fpos cx)] ly S md1 k
    t tn (x_s1 cx - x_sp0 cx) (getr (ms_regs ms) 1) ch HJ HinT G10 Hsp ltac:(lia) ltac:(lia)
    ltac:(change ASTACK with 16384; lia) Hgp Htp eq_refl Hraw Hnev' Hch Hcov MOK). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (l1 & l2 & Ebl & Ebl2) & Hfr2 & HK2 & MLE & _).
replace (x_sp0 cx + (x_s1 cx - x_sp0 cx)) with (x_s1 cx) in HK2 by ring.
(* the facts across the run and across the free *)
assert (HCr : lt_core B MT cx ly S W (ms_regs ms) (ms_mem ms) md1 k acc (5 + 2 * (x_nf cx - Z.of_nat f)) LFO_L
  [(t, tn); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)])
  by exact (s5e_core_kept B MT MTL IMGS BSYM cx ly S W regs mem md k acc _ LFO_L _ (ms_regs ms) (ms_mem ms) md1
    HB HC HJ KEEP G2 G3 G4 G8 G9).
destruct (s5e_after_free B MT MTL IMGS BSYM cx ly S W (ms_regs ms) (ms_mem ms) md1 k acc _ LFO_L _ ly2 S2 W2 regs2
  mem2 md2 t tn l1 l2 HB HCr ltac:(lia) ltac:(lia) HJ2 HP2 Hfr2 Ebl Ebl2 HK2 MLE) as (HC2 & KS2 & KO2).
pose proof (proj1 HJ2) as HAR2.
assert (QP : forall (rr : bv 5) z, acallee_saved z -> Z_to_bv 5 z = rr -> getr regs2 rr = getr (ms_regs ms) rr)
  by (intros rr z Hz Hq; exact (s5e_pres _ _ rr z HP2 Hz Hq)).
(* K85414 f at the return address *)
rewrite G1.
change (SRr SEGS W2 (cfg_at SEGS (BASE + LO_K85414) regs2 mem2 md2) (lt_post B MT cx)).
apply (HK cx ly2 S2 W2 regs2 mem2 md2 (k + 1) (acc + mo_free MT) c m HB Hfrm ltac:(lia)).
- replace (6 + 2 * (x_nf cx - Z.of_nat (Datatypes.S f))) with (5 + 2 * (x_nf cx - Z.of_nat f) - 1) by lia.
  exact HC2.
- exact (s5e_hblk B MT MTL IMGS BSYM ly2 S2 W2 mem2 md2 c _ HAR2
    (proj1 (KO2 c _ ltac:(right; left; reflexivity)))).
- exact (s5e_hblk B MT MTL IMGS BSYM ly2 S2 W2 mem2 md2 m _ HAR2 (proj1 (KO2 m _ ltac:(left; reflexivity)))).
- rewrite (QP 18%bv 18) by (first [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
  rewrite G18, Nat2Z.inj_succ. exact R18.
- rewrite (QP 19%bv 19) by (first [unfold acallee_saved; lia | apply bv_eq; reflexivity]). rewrite G19. exact R19.
- rewrite (QP 20%bv 20) by (first [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
  rewrite G20, (proj2 (s5e_cur_next cx f ltac:(lia))). reflexivity.
- rewrite (QP 21%bv 21) by (first [unfold acallee_saved; lia | apply bv_eq; reflexivity]). rewrite G21. exact R21.
- rewrite (QP 22%bv 22) by (first [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
  rewrite G22. unfold x_af. rewrite (s5e_af (x_pl cx) f Hf1). reflexivity.
- rewrite (QP 24%bv 24) by (first [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
  rewrite G24, (proj1 (s5e_cur_next cx f ltac:(lia))). reflexivity.
- rewrite (QP 25%bv 25) by (first [unfold acallee_saved; lia | apply bv_eq; reflexivity]). rewrite G25. exact R25.
- rewrite (QP 26%bv 26) by (first [unfold acallee_saved; lia | apply bv_eq; reflexivity]). exact G26.
- (* the slots: on the stack above S1 *)
  intros o v Hin.
  assert (Ho : 8 <= o <= 184).
  { unfold LT_L in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- _; lia |]). destruct Hin. }
  apply (s5e_word_kept (rdW W mem)); [| exact (HSL o v ltac:(apply in_or_app; left; exact Hin))].
  intros x Hx. rewrite (KS2 x) by lia. apply KEEP. lia.
- (* c and m hold seg_after f: their bytes are kept *)
  unfold lt_cm, x_af. rewrite (s5e_af (x_pl cx) f Hf1). unfold seg_spec.seg_rc, seg_spec.seg_mc. cbn [fst snd].
  destruct (KO2 c seg_spec.SEG_C_SIZE ltac:(right; left; reflexivity)) as (_ & Kc).
  destruct (KO2 m seg_spec.SEG_M_SIZE ltac:(left; reflexivity)) as (_ & Km).
  split.
  + apply (s5e_rconf_kept (rdW W mem)); [|exact HRC]. intros i Hi. unfold seg_spec.SEG_C_SIZE in Hi.
    rewrite (Kc i) by (change (req_size seg_spec.SEG_C_SIZE) with 16616; lia).
    apply KEEP. lia.
  + apply (s5e_mconf_kept (rdW W mem)); [|exact HMC]. intros i Hi. unfold seg_spec.SEG_M_SIZE in Hi.
    rewrite (Km i) by (change (req_size seg_spec.SEG_M_SIZE) with 9236; lia).
    apply KEEP. lia.
- (* the counters after turn f *)
  unfold x_af. rewrite (s5e_af (x_pl cx) f Hf1). unfold seg_spec.seg_rc, seg_spec.seg_mc. cbn [fst snd].
  exact HCNT.
Qed.

End ee.
End fe.
End de.

(* ======================================== piece d ======================================== *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0d_tail.

(* the helpers keep zify's euclidean division off, as _s10's kit does (LLVMFuzzerTestOneInput_s10k.v): every
   lia below that meets a / or a mod is handed its Z.div_mod / Z.mod_pos_bound facts *)
Section s5dm.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* ================================ model facts (SegModel / seg_spec only) ================================ *)
(* the two bounds of a model state that keep m_file's footprint inside the block: at most 32 segments and at most
   8 kept refusals (mconf_encp's own bounds) *)
Definition s5d_mb (mc : SegModel.mconf) : Prop :=
  Z.of_nat (length (SegModel.mc_seg mc)) <= 32 /\ Z.of_nat (length (SegModel.mc_kept mc)) <= 8.
Lemma s5d_mref_mb : forall c l k, s5d_mb c -> s5d_mb (SegModel.m_refuse c l k).
Proof.
intros c l k [H1 H2]. unfold SegModel.m_refuse. cbv zeta.
destruct (Z.of_nat (length (SegModel.mc_kept c)) <? 8) eqn:E; split; cbn [SegModel.mc_seg SegModel.mc_kept];
  try exact H1; try exact H2.
rewrite length_app. cbn [length]. apply Z.ltb_lt in E. rewrite Nat2Z.inj_add. cbn [Z.of_nat]. lia.
Qed.
Lemma s5d_mupd_mb : forall c i g, s5d_mb c -> s5d_mb (SegModel.m_upd c i g).
Proof.
intros c i g [H1 H2]. unfold SegModel.m_upd, SegModel.m_set_segs.
split; cbn [SegModel.mc_seg SegModel.mc_kept]; [rewrite SegModel.upd_nth_len|]; assumption.
Qed.
Lemma s5d_mhdr_mb : forall c l n, s5d_mb c -> s5d_mb (fst (SegModel.m_header c l n)).
Proof.
intros c l n Hc. unfold SegModel.m_header. cbv zeta.
destruct (SegModel.memchr l SegModel.RBR) as [ci|]; cbv beta iota; [|apply s5d_mref_mb; exact Hc].
repeat match goal with
| |- context [if ?b then _ else _] => let E := fresh "E" in destruct b eqn:E
| |- context [SegModel.m_find ?a ?b] => destruct (SegModel.m_find a b)
end; cbv beta iota; cbn [fst];
first
[ apply s5d_mref_mb; exact Hc
| apply s5d_mupd_mb; apply s5d_mref_mb; exact Hc
| apply s5d_mupd_mb; exact Hc
| apply s5d_mref_mb; destruct Hc as [H1 H2]; split; cbn [SegModel.mc_seg SegModel.mc_kept]; assumption
| match goal with H : (32 <=? length (SegModel.mc_seg c))%nat = false |- _ =>
    apply Nat.leb_gt in H; apply Nat2Z.inj_lt in H; change (Z.of_nat 32) with 32 in H;
    destruct Hc as [H1 H2]; unfold SegModel.m_set_segs;
    split; cbn [SegModel.mc_seg SegModel.mc_kept];
    [rewrite length_app, Nat2Z.inj_add; cbn [length Z.of_nat]; lia | exact H2] end ].
Qed.
Lemma s5d_mkey_mb : forall c g l n, s5d_mb c -> s5d_mb (SegModel.m_key c g l n).
Proof.
intros c g l n Hc. unfold SegModel.m_key. cbv zeta.
destruct (SegModel.memchr l SegModel.EQ) as [ei|]; [|apply s5d_mref_mb; exact Hc].
destruct g as [gi|]; [|apply s5d_mref_mb; exact Hc].
repeat match goal with
| |- context [if ?b then _ else _] => destruct b
| |- context [SegModel.h_role_word ?a] => destruct (SegModel.h_role_word a)
| |- context [SegModel.cat_row ?a] => destruct (SegModel.cat_row a)
end; first [apply s5d_mupd_mb; exact Hc | apply s5d_mref_mb; exact Hc].
Qed.
Lemma s5d_mline_mb : forall st n l, s5d_mb (fst st) -> s5d_mb (fst (SegModel.m_line st n l)).
Proof.
intros [c cur] n l Hc. cbn [fst] in Hc. unfold SegModel.m_line. cbv beta iota zeta.
destruct (512 <=? length l)%nat; [cbn [fst]; apply s5d_mref_mb; exact Hc|].
destruct (SegModel.h_strip (SegModel.h_cut_comment l)) as [|b s]; [exact Hc|].
destruct (b =? SegModel.LBR); [apply s5d_mhdr_mb; exact Hc | cbn [fst]; apply s5d_mkey_mb; exact Hc].
Qed.
Lemma s5d_mlines_mb : forall ls st n, s5d_mb (fst st) -> s5d_mb (fst (SegModel.m_lines st n ls)).
Proof.
induction ls as [|l r IH]; intros st n H; cbn [SegModel.m_lines]; [exact H|].
apply IH. apply s5d_mline_mb. exact H.
Qed.
Lemma s5d_mfile_mb : forall c s lab, s5d_mb c -> s5d_mb (SegModel.m_file c s lab).
Proof.
intros c s lab [H1 H2]. unfold SegModel.m_file. cbv zeta. apply s5d_mlines_mb. cbn [fst].
split; cbn [SegModel.mc_seg SegModel.mc_kept]; assumption.
Qed.
(* m_file's footprint lies in the block of the mconf *)
Lemma s5d_mfp_in : forall m k0 mc' a, s5d_mb mc' -> inFP (M_FILE_FP m k0 mc') a ->
  m <= a < m + seg_spec.SEG_M_SIZE.
Proof.
intros m k0 mc' a [H1 H2] (r & Hr & Hlo & Hhi). unfold M_FILE_FP in Hr.
unfold seg_spec.mseg_addr, seg_spec.kept_addr, seg_spec.MC_N, seg_spec.MC_REFUSED, seg_spec.MC_KEPT,
  seg_spec.MC_KEPT_LEN, seg_spec.MC_KNOCK, seg_spec.MC_NKEPT, seg_spec.MC_READING, seg_spec.MSEG_SIZE,
  seg_spec.SEG_M_SIZE in *.
cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [cbn [fst snd] in Hlo, Hhi; lia|]). destruct Hr.
Qed.
(* parse_file's footprint lies in the block of the rconf *)
Lemma s5d_pfw_in : forall c a, inFP (seg_spec.RC_PARSE_W c) a -> c <= a < c + seg_spec.SEG_C_SIZE.
Proof.
intros c a (r & Hr & Hlo & Hhi). unfold seg_spec.RC_PARSE_W in Hr.
unfold seg_spec.RC_N, seg_spec.RC_REFUSAL, seg_spec.RC_OVERFLOW, seg_spec.RC_READING, seg_spec.RC_GEN,
  seg_spec.SEG_C_SIZE in *.
cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [cbn [fst snd] in Hlo, Hhi; lia|]). destruct Hr.
Qed.
(* the encodings give the bounds *)
Lemma s5d_mb_of_enc : forall pend mc bs, seg_spec.mconf_encp pend mc bs -> s5d_mb mc.
Proof.
intros pend mc bs (_ & H1 & _ & _ & _ & _ & H2 & _). apply Nat2Z.inj_le in H1. apply Nat2Z.inj_le in H2.
split; [exact H1 | exact H2].
Qed.

(* the input's bytes and the files decode reads from them *)
Definition s5d_byte (x : Z) : Prop := 0 <= x < 256.
Definition s5d_fok (fl : SegModel.file) : Prop :=
  0 <= SegModel.f_lb fl < 256 /\ ~ In 0 (SegModel.f_text fl) /\ Z.of_nat (length (SegModel.f_text fl)) <= 65535.
Lemma s5d_in_bytes : forall pl, Forall s5d_byte (seg_spec.seg_in pl).
Proof.
intros pl. unfold seg_spec.seg_in, seg_spec.zs. apply Forall_forall. intros x Hx.
apply in_map_iff in Hx as (b & <- & _). pose proof (bv_unsigned_in_range 8 b) as Hb.
change (bv_modulus 8) with 256 in Hb. unfold s5d_byte. lia.
Qed.
Lemma s5d_sfx_bytes : forall a b, s5_sfx a b -> Forall s5d_byte b -> Forall s5d_byte a.
Proof. intros a b (j & _ & ->) H. apply SegModel.Forall_skipn'. exact H. Qed.
Lemma s5d_u8_byte : forall l, Forall s5d_byte l -> s5d_byte (fst (SegModel.fuzz_u8 l)).
Proof. intros [|x l] H; cbn [SegModel.fuzz_u8 fst]; [unfold s5d_byte; lia | inversion H; assumption]. Qed.
Lemma s5d_u16_le : forall l, 0 <= fst (SegModel.fuzz_u16 l) <= 65535.
Proof.
intros l. unfold SegModel.fuzz_u16.
destruct (SegModel.fuzz_u8 l) as [lo i1]. destruct (SegModel.fuzz_u8 i1) as [hi i2]. cbn [fst].
assert (E : forall y, Z.land y 65535 = y mod 65536)
  by (intros y; change 65535 with (Z.ones 16); rewrite Z.land_ones by lia; reflexivity).
rewrite E. generalize (Z.lor lo (Z.shiftl hi 8)). intros x. pose proof (Z.mod_pos_bound x 65536 ltac:(lia)) as [H1 H2].
split; [exact H1|]. apply Z.lt_succ_r. exact H2.
Qed.
Lemma s5d_dec_ok : forall k l, Forall s5d_byte l -> Forall s5d_fok (SegModel.dec_files k l).
Proof.
induction k as [|k IH]; intros l Hl; cbn [SegModel.dec_files]; [constructor|].
pose proof (s5d_u8_byte l Hl) as Hlb.
pose proof (s5_u8_sfx l) as S1. pose proof (s5_u16_sfx (snd (SegModel.fuzz_u8 l))) as S2.
pose proof (s5d_u16_le (snd (SegModel.fuzz_u8 l))) as Hlen.
destruct (SegModel.fuzz_u8 l) as [lb i1] eqn:E1. cbn [fst snd] in Hlb, S1, S2, Hlen.
pose proof (s5_take_sfx (snd (SegModel.fuzz_u16 i1)) (fst (SegModel.fuzz_u16 i1))) as S3.
pose proof (s5_take_fst (snd (SegModel.fuzz_u16 i1)) (fst (SegModel.fuzz_u16 i1))) as T3.
destruct (SegModel.fuzz_u16 i1) as [len i2] eqn:E2. cbn [fst snd] in S2, S3, T3, Hlen.
destruct (SegModel.fuzz_take i2 len) as [p i3] eqn:E3. cbn [fst snd] in S3, T3.
constructor.
- split; [exact Hlb|]. cbn [SegModel.f_text]. unfold SegModel.fuzz_str. split.
  + exact (SegModel.cut_nul_nulfree p).
  + pose proof (SegModel.cut_nul_len p) as Hc. rewrite T3 in Hc |- *. rewrite length_firstn in Hc.
    assert (Hl2 : (length (SegModel.cut_nul (firstn (Nat.min (Z.to_nat len) (length i2)) i2)) <= Z.to_nat len)%nat).
    { eapply Nat.le_trans; [exact Hc|]. eapply Nat.le_trans; [apply Nat.le_min_l|]. apply Nat.le_min_l. }
    apply Nat2Z.inj_le in Hl2. rewrite Z2Nat.id in Hl2 by lia. lia.
- apply IH. apply (s5d_sfx_bytes i3 i2 S3). apply (s5d_sfx_bytes i2 i1 S2). exact (s5d_sfx_bytes i1 l S1 Hl).
Qed.
Lemma s5d_files_ok : forall pl, Forall s5d_fok (seg_spec.seg_files pl).
Proof.
intros pl. pose proof (s5d_in_bytes pl) as H0.
unfold seg_spec.seg_files, seg_spec.seg_pay, SegModel.decode.
pose proof (s5_u8_sfx (seg_spec.seg_in pl)) as S1.
destruct (SegModel.fuzz_u8 (seg_spec.seg_in pl)) as [b0 i1]. cbn [snd] in S1.
pose proof (s5_u8_sfx i1) as S2. destruct (SegModel.fuzz_u8 i1) as [fl i2]. cbn [snd] in S2.
pose proof (s5_u8_sfx i2) as S3. destruct (SegModel.fuzz_u8 i2) as [b2 i3]. cbn [snd] in S3.
cbn [SegModel.p_files]. apply s5d_dec_ok.
apply (s5d_sfx_bytes i3 i2 S3). apply (s5d_sfx_bytes i2 i1 S2). exact (s5d_sfx_bytes i1 _ S1 H0).
Qed.
Lemma s5d_file_ok : forall pl j, s5d_fok (seg_spec.seg_file pl j).
Proof.
intros pl j. unfold seg_spec.seg_file.
destruct (Nat.lt_ge_cases j (length (seg_spec.seg_files pl))) as [Hj|Hj].
- exact (proj1 (Forall_forall _ _) (s5d_files_ok pl) _ (nth_In _ _ Hj)).
- rewrite nth_overflow by exact Hj. unfold s5d_fok. cbn [SegModel.f_lb SegModel.f_text length Z.of_nat].
  split; [lia|]. split; [intros []|lia].
Qed.
(* the reader's and the model's states after k turns are related (SegModel.file_rel at every turn) *)
Lemma s5d_run_rel : forall pl k,
  SegModel.conf_rel (seg_spec.seg_rc (seg_spec.seg_run pl k)) (seg_spec.seg_mc (seg_spec.seg_run pl k)).
Proof.
intros pl. induction k as [|k IH]; [exact SegModel.conf_rel0|].
cbn [seg_spec.seg_run]. unfold seg_spec.seg_turn_step. revert IH.
destruct (seg_spec.seg_run pl k) as [[c mc] ret]. unfold seg_spec.seg_rc, seg_spec.seg_mc. cbn [fst snd].
intros IH. cbv beta iota zeta.
pose proof (s5d_file_ok pl k) as (Hlb & Hnf & Hlen).
destruct (SegModel.file_rel c mc (seg_spec.seg_txt pl k) (seg_spec.seg_label pl k) (seg_spec.seg_label pl k) IH Hnf
  Hlen eq_refl (SegModel.rd_label_ok _ Hlb)) as (HR & _ & _).
destruct (SegModel.r_parse_file c (seg_spec.seg_txt pl k) (seg_spec.seg_label pl k)) as [c1 n].
cbn [fst snd] in HR |- *. exact HR.
Qed.
(* the counters after the turn: m_file adds one gen and at most a line per refusal / overflow, the reader keeps
   the same counts (conf_rel) *)
Lemma s5d_cnt_next : forall pl f,
  lt_cnt f (seg_spec.seg_rc (seg_spec.seg_run pl f)) (seg_spec.seg_mc (seg_spec.seg_run pl f)) ->
  lt_cnt (Datatypes.S f) (fst (s5_rp pl f)) (s5_mc1 pl f).
Proof.
intros pl f (G1 & R1 & O1 & G2 & R2 & O2).
pose proof (s5d_file_ok pl f) as (Hlb & Hnf & Hlen).
destruct (SegModel.file_rel _ _ (seg_spec.seg_txt pl f) (seg_spec.seg_label pl f) (seg_spec.seg_label pl f)
  (s5d_run_rel pl f) Hnf Hlen eq_refl (SegModel.rd_label_ok _ Hlb))
  as ((_ & _ & _ & Hov & Href & _ & _ & Hgen) & _ & _).
unfold lt_cnt, s5_rp, s5_mc1, s5_txt, s5_lab, seg_spec.seg_label. unfold seg_spec.seg_label in Hov, Href, Hgen.
rewrite Hov, Href, Hgen.
pose proof (m_file_gen (seg_spec.seg_mc (seg_spec.seg_run pl f)) (seg_spec.seg_txt pl f)
  (SegModel.label_of (seg_spec.seg_lb pl f))) as E1.
pose proof (m_file_refused (seg_spec.seg_mc (seg_spec.seg_run pl f)) (seg_spec.seg_txt pl f)
  (SegModel.label_of (seg_spec.seg_lb pl f)) Hnf) as E2.
pose proof (m_file_overflow (seg_spec.seg_mc (seg_spec.seg_run pl f)) (seg_spec.seg_txt pl f)
  (SegModel.label_of (seg_spec.seg_lb pl f)) Hnf) as E3.
unfold seg_spec.seg_txt in *. change (2 ^ 20) with 1048576 in *.
rewrite Nat2Z.inj_succ. lia.
Qed.
Lemma s5d_nf_le4 : forall pl, seg_spec.seg_nfiles pl <= 4.
Proof.
intros pl. unfold seg_spec.seg_nfiles, seg_spec.seg_files, seg_spec.seg_pay, SegModel.decode.
destruct (SegModel.fuzz_u8 (seg_spec.seg_in pl)) as [b0 i1].
destruct (SegModel.fuzz_u8 i1) as [fl i2]. destruct (SegModel.fuzz_u8 i2) as [b2 i3].
cbn [SegModel.p_files]. rewrite s5_dec_files_length.
pose proof (Z.mod_pos_bound b2 4 ltac:(lia)) as H. rewrite Z2Nat.id by lia. lia.
Qed.

(* ================================ readers ================================ *)
Lemma s5d_zs_kept : forall (rd rd' : reader) a l,
  (forall i, 0 <= i < Z.of_nat (length l) -> rd' (a + i) = rd (a + i)) -> sa_zs rd a l -> sa_zs rd' a l.
Proof. intros rd rd' a l HK H i Hi. rewrite HK by lia. exact (H i Hi). Qed.
Lemma s5d_bytes_kept : forall (rd rd' : reader) a bs,
  (forall i, 0 <= i < Z.of_nat (length bs) -> rd' (a + i) = rd (a + i)) -> sa_bytes rd a bs -> sa_bytes rd' a bs.
Proof. intros rd rd' a bs HK H i Hi. rewrite HK by lia. exact (H i Hi). Qed.
Lemma s5d_mconf_kept : forall (rd rd' : reader) a mc,
  (forall i, 0 <= i < seg_spec.SEG_M_SIZE -> rd' (a + i) = rd (a + i)) -> sa_mconf rd a mc -> sa_mconf rd' a mc.
Proof.
intros rd rd' a mc HK (bs & Hb & He). exists bs. split; [|exact He].
apply (s5d_bytes_kept rd); [|exact Hb]. intros i Hi. apply HK. destruct He as (Hl & _). lia.
Qed.
Lemma s5d_rconf_kept : forall (rd rd' : reader) a rc,
  (forall i, 0 <= i < seg_spec.SEG_C_SIZE -> rd' (a + i) = rd (a + i)) -> sa_rconf rd a rc -> sa_rconf rd' a rc.
Proof.
intros rd rd' a rc HK (bs & Hb & He). exists bs. split; [|exact He].
apply (s5d_bytes_kept rd); [|exact Hb]. intros i Hi. apply HK. destruct He as (Hl & _). lia.
Qed.
(* a C string, its NUL and its slack to the next 8-byte boundary *)
Lemma s5d_str_kept : forall (rd rd' : reader) p s,
  (forall x, p <= x < p + Z.of_nat (length s) - (p + Z.of_nat (length s)) mod 8 + 8 -> rd' x = rd x) ->
  sa_str rd p s -> sa_str rd' p s.
Proof.
intros rd rd' p s HK ((Hzs & Hnul) & Htl).
pose proof (Z.mod_pos_bound (p + Z.of_nat (length s)) 8 ltac:(lia)) as Hm.
split; [split; [|exact Hnul]|].
- apply (s5d_zs_kept rd); [|exact Hzs]. intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. apply HK. lia.
- intros x Hx. rewrite HK by lia. exact (Htl x Hx).
Qed.
Lemma s5d_addr_rd : forall (rd rd' : reader) q n, (forall a, rd' a = rd a) -> sa_addr rd q n -> sa_addr rd' q n.
Proof.
intros rd rd' q n HK (H0 & H1 & H2 & H3 & H4).
split; [exact H0|]. split; [exact H1|]. split; [exact H2|]. split.
- intros x Hx. rewrite HK. exact (H3 x Hx).
- intros Hn s Hs. rewrite HK. exact (H4 Hn s Hs).
Qed.
Lemma s5d_pres : forall regs regs' (r : bv 5) z,
  aregs_preserved regs regs' -> acallee_saved z -> Z_to_bv 5 z = r -> getr regs' r = getr regs r.
Proof. intros regs regs' r z HP Hz <-. exact (HP z Hz). Qed.
Lemma s5d_dup : forall {A} (x : A) l l', Permutation l (x :: l') -> In x l' -> exists r, Permutation l (x :: x :: r).
Proof.
intros A x l l' HP Hin. apply in_split in Hin as (l1 & l2 & ->). exists (l1 ++ l2).
eapply Permutation_trans; [exact HP|]. apply perm_skip. apply Permutation_sym, Permutation_middle.
Qed.
End s5dm.

Section s5dd. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Context {SK : YI16.sink_head}.
Section s5df.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Lemma s5d_slots_kept : forall cx (rd rd' : reader) L,
  (forall o v, In (o, v) L -> 0 <= o <= 184) ->
  (forall a, x_s1 cx <= a < x_s1 cx + 192 -> rd' a = rd a) -> lt_slots cx rd L -> lt_slots cx rd' L.
Proof.
intros cx rd rd' L HL HK HS o v Hin. pose proof (HL o v Hin) as Ho.
rewrite (rdword_ext rd rd'); [exact (HS o v Hin)|]. intros j Hj. apply HK. lia.
Qed.
Lemma s5d_L_bnd : forall cx c m z o v, In (o, v) (LT_L cx c m ++ [(152, z)]) -> 0 <= o <= 184.
Proof.
intros cx c m z o v H. unfold LT_L in H. cbn [app In] in H.
repeat (destruct H as [H|H]; [injection H as <- _; lia|]). destruct H.
Qed.
(* a run whose windows are empty keeps every byte *)
Lemma s5d_frame_all : forall E rs (H : word -> bool) m m', (forall a, ~ in_wrange E rs a) ->
  frame_of E rs (mrestrict H m) (mrestrict H m') -> forall a, aview SEGS H m' a = aview SEGS H m a.
Proof. intros E rs H m m' Hn HF a. unfold aview, mbyte. rewrite (HF (Z_to_bv 64 a) (Hn _)). reflexivity. Qed.
(* the seed of the first stretch: no region, no fact *)
Lemma s5d_seed0 : forall pc (W : world SEGS) regs mem,
  st_ok_pi SEGS VAL (Eimg (Ereg regs [])) (mkSS pc sr_atoms [] None (mkFacts [] [] []))
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
intros pc W regs mem. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- reflexivity.
- apply Forall_nil.
- exact I.
- split; [exact I | split; [exact I | exact I]].
Qed.
(* the seed of the second stretch: the s1 slot 160 holds c (atom 32), read by `ld a0,160(s1)` *)
Definition s5d_r160 : YP09.region := YP09.mkRegion (Some 9%nat) 160 168 0 0 [YP09.mkChunk 160 (CVal 8 (SOff 32 0))].
Lemma s5d_seed1 : forall pc (W : world SEGS) regs mem v,
  bv_unsigned (getr regs 9) + 168 <= 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
  rdword (rdW W mem) (bv_unsigned (getr regs 9) + 160) = Some v ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs [Z_to_bv 64 v])) (mkSS pc sr_atoms [s5d_r160] None (mkFacts [] [] []))
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
intros pc W regs mem v Hhi Hv Hrd. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- reflexivity.
- apply Forall_cons; [|apply Forall_nil].
  assert (E9 : ew (Eimg (Ereg regs [Z_to_bv 64 v])) 9 = getr regs 9) by (apply ew_Eimg_Ereg_nat; reflexivity).
  pose proof (bv_unsigned_in_range 64 (getr regs 9)) as Hr9. change (bv_modulus 64) with (2 ^ 64) in Hr9.
  unfold region_ok, s5d_r160. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS _ _ _ 160 8%N (SOff 32 0) v).
  + cbn [sv_denot]. rewrite Eimg_low by (unfold A_TEXT; lia).
    change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. cbn [nth].
    rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
  + change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact Hv.
  + lia.
  + exact (val_mem_of_rdword SEGS (w_H W) mem _ v Hrd).
- split; exact I.
- split; [exact I | split; [exact I | exact I]].
Qed.

Section s5de.
Variable B : asyms.
Variable MT : ameter_ops.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis IMGS : s10_img.
Hypothesis BSYM : AF0m.SegBSyms B.

(* the entry sp and the realigned base S1 *)
Lemma s5d_sp : forall cx, lt_base B MT cx ->
  x_sp0 cx mod 16 = 0 /\ alloc_ceiling + 32768 <= x_sp0 cx /\ x_sp0 cx <= 2 ^ 47 /\
  x_s1 cx mod 32 = 0 /\ x_sp0 cx - 336 <= x_s1 cx /\ x_s1 cx <= x_sp0 cx - 320.
Proof.
intros cx HB. destruct HB as (HPRE & _). destruct HPRE as (_ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal & _ & Hceil & Hslo & Hshi & H47 & _).
destruct (s10_sp1_facts (x_sp0 cx) Hal) as (H32 & Hs).
change (x_s1 cx) with (s10_sp1 (x_sp0 cx)). unfold x_sp0 in *. unfold STK_LLVMFuzzerTestOneInput in Hslo.
split; [exact Hal|]. split; [lia|]. split; [lia|]. split; [exact H32|].
destruct Hs as [-> | ->]; split; lia.
Qed.
(* the frame address of a journal's target layout is the entry's *)
Lemma s5d_frame_addr : forall STK sp0 FP ly0 S0 W0 mem0 md0 own ly S (W : world SEGS) mem md k,
  ajournal SEGS B STK sp0 FP ly0 S0 W0 mem0 md0 own ly S W mem md k ->
  forall cid pos, frame_addr ly cid pos = frame_addr ly0 cid pos.
Proof.
intros STK sp0 FP ly0 S0 W0 mem0 md0 own ly S W mem md k HJ cid pos.
destruct HJ as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & EF & _). unfold frame_addr. rewrite EF. reflexivity.
Qed.
(* a live block of a state is a harness block of that state *)
Lemma s5d_hblk : forall ly S (W : world SEGS) mem md a n,
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
(* the chain for a call from the harness's frame: the stack from S1 up is mapped, s0 = SP0 >= S1 + 320 *)
Lemma s5d_chain : forall cx ly S (W : world SEGS) regs mem md k o,
  lt_base B MT cx -> lt_frame B cx ly S W regs mem md k o ->
  exists ch, achain ly (rdW W mem) (x_s1 cx) (s0Z regs) ch.
Proof.
intros cx ly S W regs mem md k o HB HF.
pose proof (s5d_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
destruct HF as (HJ & R2 & _ & _ & R8 & _).
pose proof HB as (_ & HPRES & _).
pose proof asan_consts as (C1 & _).
assert (Es0 : s0Z regs = x_sp0 cx)
  by (unfold s0Z; rewrite R8; unfold w64; rewrite YP03.unsigned_lit_small by lia; reflexivity).
rewrite Es0. apply achain_any; [|right; right; right; lia].
apply (astack_rd_mono ly _ (x_sp0 cx - STK_LLVMFuzzerTestOneInput)); [unfold STK_LLVMFuzzerTestOneInput; lia|].
apply astack_rd_of_pres.
apply (astack_pres_journal SEGS B pa_segs_low STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA)
  (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem md k HJ HPRES).
intros a (r & Hr & Ha) Ha2. exfalso. unfold ltoi_PG in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
unfold longlA, A_LONGL, LONGL_N in Ha. lia.
Qed.
(* lt_core across a stretch that wrote no byte and kept sp, gp, tp, s0, s1 *)
Lemma s5d_core_rd : forall cx ly S (W : world SEGS) regs mem md k acc rem o O regs' mem' md',
  lt_core B MT cx ly S W regs mem md k acc rem o O ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem' md' k ->
  (forall a, rdW W mem' a = rdW W mem a) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
  lt_core B MT cx ly S W regs' mem' md' k acc rem o O.
Proof.
intros cx ly S W regs mem md k acc rem o O regs' mem' md' HC HJ' KM P2 P3 P4 P8 P9.
destruct HC as (HF & HI & HBL & HBUD).
destruct HF as (HJ & R2 & R3 & R4 & R8 & R9 & HSV & HH0 & HH8 & HH16 & HFL & H176 & HSH).
assert (KW : forall a v, rdword (rdW W mem) a = Some v -> rdword (rdW W mem') a = Some v).
{ intros a v H. rewrite (rdword_ext (rdW W mem) (rdW W mem')); [exact H|]. intros j _. apply KM. }
split; [|split; [|split]].
- split; [exact HJ'|]. rewrite P2, P3, P4, P8, P9.
  split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R8|]. split; [exact R9|].
  split; [intros i r Hi; apply KW; exact (HSV i r Hi)|].
  split; [apply KW; exact HH0|]. split; [apply KW; exact HH8|]. split; [apply KW; exact HH16|].
  split; [apply KW; exact HFL|]. split; [apply KW; exact H176|].
  intros i Hi. rewrite KM. exact (HSH i Hi).
- apply (s10_lt_img_kept B IMGS BSYM cx W mem' (rdW W mem) (proj1 HJ')); [intros a _ _ _; apply KM | exact HI].
- exact HBL.
- exact HBUD.
Qed.
(* lt_core across a call of a program function that allocates nothing and writes, outside its own window and
   frames, only FP1 inside live blocks; and what of the caller's memory the call keeps *)
Lemma s5d_carry : forall cx ly S (W : world SEGS) regs mem md k acc rem o O ly2 S2 (W2 : world SEGS) regs2 mem2 md2
  STK1 FP1,
  lt_base B MT cx -> lt_core B MT cx ly S W regs mem md k acc rem o O ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly2 S2 W2 mem2 md2 k ->
  ajournal SEGS B STK1 (x_s1 cx) FP1 ly S W mem md [] ly2 S2 W2 mem2 md2 0 ->
  (forall a, inFP FP1 a -> exists b n, In (b, n) (ablocks B ly S) /\ b <= a < b + req_size n) ->
  aregs_preserved regs regs2 -> sa_noalloc B ly S ly2 S2 ->
  lt_core B MT cx ly2 S2 W2 regs2 mem2 md2 k acc rem o O /\
  (forall a, x_s1 cx <= a < 2 ^ 64 -> rdW W2 mem2 a = rdW W mem a) /\
  (forall b n i, In (b, n) (ablocks B ly S) -> 0 <= i < req_size n -> ~ inFP FP1 (b + i) ->
     rdW W2 mem2 (b + i) = rdW W mem (b + i)) /\
  (forall cid pos a, In (cid, pos) (frames S) ->
     (frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid \/
      shadow_addr (frame_addr ly cid pos) <= a < shadow_addr (frame_addr ly cid pos) + fs_frame_bytes cid / 8) ->
     rdW W2 mem2 a = rdW W mem a) /\
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     rdW W2 mem2 a = rdW W mem a).
Proof.
intros cx ly S W regs mem md k acc rem o O ly2 S2 W2 regs2 mem2 md2 STK1 FP1 HB HC HJ2 HJc HFP HP HNA.
pose proof (s5d_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
destruct HC as (HF & HI & HBL & HBUD).
destruct HF as (HJ & R2 & R3 & R4 & R8 & R9 & HSV & HH0 & HH8 & HH16 & HFL & H176 & HSH).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & F2 & F3 & F4 & _).
destruct HNA as (HPm & Hly2 & (fS & HS2)).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (NFh : forall a, inFP FP1 a -> 4096 <= a /\ a < alloc_ceiling).
{ intros a Ha. destruct (HFP a Ha) as (b & n & Hbn & Hr).
  destruct (al_blocks _ _ LAWS ly S W mem md b n HAR Hbn) as (_ & H4 & Hc & _). lia. }
assert (KS : forall a, x_s1 cx <= a < 2 ^ 64 -> rdW W2 mem2 a = rdW W mem a).
{ intros a Ha. apply F1; [lia | lia | intros Hf; pose proof (NFh a Hf); lia]. }
assert (KF : forall cid pos a, In (cid, pos) (frames S) ->
     (frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid \/
      shadow_addr (frame_addr ly cid pos) <= a < shadow_addr (frame_addr ly cid pos) + fs_frame_bytes cid / 8) ->
     rdW W2 mem2 a = rdW W mem a).
{ intros cid pos a Hin Ha. apply (F4 cid pos a Hin).
  - destruct Ha as [Ha | Ha]; [left | right]; unfold in_zr, frame_rng; cbn [fst snd]; lia.
  - intros Hf. destruct (HFP a Hf) as (b & n & Hbn & Hr).
    destruct (al_blocks _ _ LAWS ly S W mem md b n HAR Hbn) as (_ & _ & _ & Happ & _).
    destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hin) as (Hf0 & Hfc & Hfapp).
    pose proof (fs_frame_bytes_nonneg cid) as Hnn.
    destruct Ha as [Ha | Ha].
    + pose proof (sep_block_frame SEGS B LAWS ly S W mem md b n cid pos HAR Hbn Hin) as Hsep.
      unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. lia.
    + unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ, Hfapp. unfold shadow_addr, SHADOW_OFF in Ha.
      pose proof (Z.div_mod (frame_addr ly cid pos) 8 ltac:(lia)) as D1.
      pose proof (Z.mod_pos_bound (frame_addr ly cid pos) 8 ltac:(lia)) as M1.
      pose proof (Z.div_mod (fs_frame_bytes cid) 8 ltac:(lia)) as D2.
      pose proof (Z.mod_pos_bound (fs_frame_bytes cid) 8 ltac:(lia)) as M2.
      lia. }
assert (KB : forall b n i, In (b, n) (ablocks B ly S) -> 0 <= i < req_size n -> ~ inFP FP1 (b + i) ->
     rdW W2 mem2 (b + i) = rdW W mem (b + i)).
{ intros b n i Hbn Hi Hf. apply (F2 b n i Hbn); [apply (Permutation_in _ (Permutation_sym HPm)); exact Hbn | exact Hi | exact Hf]. }
assert (KI : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     rdW W2 mem2 a = rdW W mem a).
{ intros a Ha Ho He. apply (F3 a Ha Ho He). apply fp_spares_closed.
  - intros Hs. destruct (NFh 0 Hs) as [H0 _]. lia.
  - intros Hf. destruct (HFP a Hf) as (b & n & Hbn & Hr). exact (blk_img SEGS B LAWS ly S W mem md b n a HAR Hbn Hr Ha). }
assert (HinF : In (LT_FCLS, x_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (EF : frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx) by exact (s5d_frame_addr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ _ _).
assert (F512 : fs_frame_bytes LT_FCLS = 512) by (vm_compute; reflexivity).
assert (KFR : forall a, x_fr cx <= a < x_fr cx + 512 -> rdW W2 mem2 a = rdW W mem a).
{ intros a Ha. apply (KF LT_FCLS (x_fpos cx) a HinF). left. rewrite EF, F512. exact Ha. }
assert (KSH : forall i, 0 <= i < 64 -> rdW W2 mem2 (x_sh cx + i) = rdW W mem (x_sh cx + i)).
{ intros i Hi. apply (KF LT_FCLS (x_fpos cx) _ HinF). right. rewrite EF, F512. unfold x_sh.
  change (512 / 8) with 64. lia. }
assert (KW : forall a v, (forall x, a <= x < a + 8 -> rdW W2 mem2 x = rdW W mem x) ->
  rdword (rdW W mem) a = Some v -> rdword (rdW W2 mem2) a = Some v).
{ intros a v HK H. rewrite (rdword_ext (rdW W mem) (rdW W2 mem2)); [exact H|]. intros j Hj. apply HK. lia. }
split; [|split; [exact KS | split; [exact KB | split; [exact KF | exact KI]]]].
split; [|split; [|split]].
- (* the frame *)
  split; [exact HJ2|].
  rewrite (s5d_pres _ _ 2%bv 2 HP ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (s5d_pres _ _ 3%bv 3 HP ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (s5d_pres _ _ 4%bv 4 HP ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (s5d_pres _ _ 8%bv 8 HP ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (s5d_pres _ _ 9%bv 9 HP ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R8|]. split; [exact R9|].
  split.
  { intros i r Hi. assert (Hi13 : (i < length LT_SAVED)%nat) by (apply nth_error_Some; congruence).
    change (length LT_SAVED) with 13%nat in Hi13.
    apply KW; [|exact (HSV i r Hi)]. intros x Hx. apply KS. unfold x_sp0 in *. lia. }
  split; [apply KW; [|exact HH0]; intros x Hx; apply KFR; lia|].
  split; [apply KW; [|exact HH8]; intros x Hx; apply KFR; lia|].
  split; [apply KW; [|exact HH16]; intros x Hx; apply KFR; lia|].
  split; [apply KW; [|exact HFL]; intros x Hx; apply KFR; unfold LT_FLAGW in *; lia|].
  split; [apply KW; [|exact H176]; intros x Hx; apply KS; lia|].
  intros i Hi. pose proof Hi as Hi0. rewrite (lt_fsh_len o) in Hi0. apply Nat2Z.inj_lt in Hi0.
  change (Z.of_nat 36) with 36 in Hi0. rewrite KSH by lia. exact (HSH i Hi).
- (* the image facts *)
  exact (s10_lt_img_kept B IMGS BSYM cx W2 mem2 (rdW W mem) (proj1 HJ2) KI HI).
- (* the blocks *)
  unfold lt_blocks in *. eapply Permutation_trans; [exact HPm | exact HBL].
- (* the budget: nothing spent, the meter carried over the FP-state change *)
  destruct HBUD as (B1 & B2 & B3 & B4 & B5 & B6).
  unfold lt_bud. split; [exact B1|]. split; [exact B2|]. split; [exact B3|].
  split; [rewrite HS2; exact (mo_le_set_fs_r MT MTFL _ _ fS acc B4)|]. split; [exact B5 | exact B6].
Qed.

(* a C string inside a live block of the state after a call, its bytes kept: the string at the new reader *)
Lemma s5d_str_blk : forall (rd : reader) ly S (W2 : world SEGS) mem2 md2 b nb p s,
  AR SEGS B ly S W2 mem2 md2 -> In (b, nb) (ablocks B ly S) -> b <= p ->
  p + Z.of_nat (length s) + 1 <= b + nb ->
  (forall x, p <= x <= p + Z.of_nat (length s) -> rdW W2 mem2 x = rd x) ->
  sa_str rd p s -> sa_str (rdW W2 mem2) p s.
Proof.
intros rd ly S W2 mem2 md2 b nb p s HAR Hin Hb1 Hb2 HK ((Hzs & Hnul) & _).
destruct (al_blocks _ _ LAWS ly S W2 mem2 md2 b nb HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn).
pose proof (req_size_pos nb ltac:(lia)) as [_ Hreq].
split; [split; [|exact Hnul]|].
- intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. rewrite HK by lia. exact (Hzs i ltac:(rewrite length_app; cbn [length]; lia)).
- intros x Hx. apply (YG0d_tail.AR_block_word_vis SEGS B ly S W2 mem2 md2 b nb (p + Z.of_nat (length s)) x HAR Hin); lia.
Qed.

(* the label across m_file: it lies in a live block other than m, in a live frame, or in the image *)
Lemma s5d_label_post : forall cx f lp c m ly S (W : world SEGS) mem ly2 S2 (W2 : world SEGS) mem2 md2,
  S5_label B ly S (rdW W mem) cx f lp c m ->
  AR SEGS B ly2 S2 W2 mem2 md2 -> ly2 = ly -> frames S2 = frames S ->
  (forall b n, In (b, n) (ablocks B ly S) -> In (b, n) (ablocks B ly2 S2)) ->
  (forall b n i, In (b, n) (ablocks B ly S) -> 0 <= i < req_size n -> ~ (m <= b + i < m + seg_spec.SEG_M_SIZE) ->
     rdW W2 mem2 (b + i) = rdW W mem (b + i)) ->
  (forall cid pos a, In (cid, pos) (frames S) ->
     (frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid \/
      shadow_addr (frame_addr ly cid pos) <= a < shadow_addr (frame_addr ly cid pos) + fs_frame_bytes cid / 8) ->
     rdW W2 mem2 a = rdW W mem a) ->
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     rdW W2 mem2 a = rdW W mem a) ->
  S5_label B ly2 S2 (rdW W2 mem2) cx f lp c m.
Proof.
intros cx f lp c m ly S W mem ly2 S2 W2 mem2 md2 (Hlp & Hos & Hmt) HAR2 -> Hfr2 HBin KB KF KI.
unfold S5_label. split; [exact Hlp|]. revert Hos Hmt.
destruct (s5_lab (x_pl cx) f) as [l|]; intros Hos Hmt; [|split; [exact Hos | exact I]].
destruct Hos as (Hnz & (Hzs & Hnul) & Htl).
destruct Hmt as (Hlen & Hloc & Had & Hdm & Hdc).
pose proof (Z.mod_pos_bound (- (lp + Z.of_nat (length l) + 1)) 8 ltac:(lia)) as Hsp8.
assert (Hsp : Z.of_nat (length l) + 1 <= seg_spec.cstr_span lp l) by (unfold seg_spec.cstr_span; lia).
destruct Had as (Ha0 & Ha1 & Ha2 & Ha3 & Ha4).
destruct Hloc as [(b & nb & Hbn & Hb1 & Hb2) | [(cid & pos & Hin & Hcid & Hf1 & Hf2) | (Himg & Hpin & Hpt)]].
- (* a heap block *)
  pose proof (HBin _ _ Hbn) as Hbn2.
  destruct (al_blocks _ _ LAWS ly S2 W2 mem2 md2 b nb HAR2 Hbn2) as (_ & _ & _ & _ & _ & _ & Hn).
  pose proof (req_size_pos nb ltac:(lia)) as [_ Hreq].
  assert (KL : forall x, lp <= x <= lp + Z.of_nat (length l) -> rdW W2 mem2 x = rdW W mem x).
  { intros x Hx. replace x with (b + (x - b)) by lia. apply (KB b nb); [exact Hbn | lia |].
    unfold sa_disj in Hdm. lia. }
  split; [split; [exact Hnz|]|].
  { apply (s5d_str_blk (rdW W mem) ly S2 W2 mem2 md2 b nb lp l HAR2 Hbn2); [lia | lia | exact KL |].
    split; [split; [exact Hzs | exact Hnul] | exact Htl]. }
  split; [exact Hlen|].
  split; [left; exists b, nb; split; [exact Hbn2 | lia]|].
  split; [|split; [exact Hdm | exact Hdc]].
  split; [exact Ha0|]. split; [exact Ha1|]. split; [exact Ha2|].
  split; [exact (range_addressable_of_block SEGS B LAWS ly S2 W2 mem2 md2 b nb lp (Z.of_nat (length l) + 1) HAR2 Hbn2 ltac:(lia) ltac:(lia))|].
  intros Hpos. exact (shadow_hull_vis_of_block SEGS B LAWS ly S2 W2 mem2 md2 b nb lp (Z.of_nat (length l) + 1) HAR2 Hbn2 ltac:(lia) ltac:(lia) Hpos).
- (* a live side-stack frame *)
  assert (Hin2 : In (cid, pos) (frames S2)) by (rewrite Hfr2; exact Hin).
  destruct (al_frames _ _ LAWS ly S2 W2 mem2 md2 cid pos HAR2 Hin2) as (Hal32 & _ & _ & _).
  assert (Hfb8 : fs_frame_bytes cid mod 8 = 0).
  { unfold fs_frame_bytes. rewrite Z.shiftl_mul_pow2 by lia.
    replace (64 * 2 ^ cid) with ((8 * 2 ^ cid) * 8) by ring. apply Z.mod_mul. lia. }
  pose proof (fs_frame_bytes_nonneg cid) as Hnn.
  set (F := frame_addr ly cid pos) in *. set (FB := fs_frame_bytes cid) in *.
  assert (HF8 : F mod 8 = 0).
  { pose proof (Z.div_mod F 32 ltac:(lia)) as D. rewrite Hal32, Z.add_0_r in D. rewrite D.
    replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by ring. apply Z.mod_mul. lia. }
  assert (Htop : lp + Z.of_nat (length l) - (lp + Z.of_nat (length l)) mod 8 + 8 <= F + FB).
  { pose proof (Z.div_mod (lp + Z.of_nat (length l)) 8 ltac:(lia)) as D1.
    pose proof (Z.div_mod F 8 ltac:(lia)) as D2. pose proof (Z.div_mod FB 8 ltac:(lia)) as D3.
    pose proof (Z.mod_pos_bound (lp + Z.of_nat (length l)) 8 ltac:(lia)) as M1. lia. }
  assert (KL : forall x, lp <= x < lp + Z.of_nat (length l) - (lp + Z.of_nat (length l)) mod 8 + 8 ->
    rdW W2 mem2 x = rdW W mem x).
  { intros x Hx. apply (KF cid pos x Hin). left. fold F FB. lia. }
  split; [split; [exact Hnz|]|].
  { apply (s5d_str_kept (rdW W mem)); [exact KL|]. split; [split; [exact Hzs | exact Hnul] | exact Htl]. }
  split; [exact Hlen|].
  split; [right; left; exists cid, pos; split; [exact Hin2|]; split; [exact Hcid|]; fold F FB; lia|].
  split; [|split; [exact Hdm | exact Hdc]].
  split; [exact Ha0|]. split; [exact Ha1|]. split; [exact Ha2|].
  split.
  { intros x Hx. destruct (Ha3 x Hx) as (sb & Hsb & Hok). exists sb. split; [|exact Hok].
    rewrite (KF cid pos); [exact Hsb | exact Hin|]. right. fold F FB.
    unfold shadow_of_addr, shadow_addr.
    pose proof (Z.div_mod x 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as M1.
    pose proof (Z.div_mod F 8 ltac:(lia)) as D2. pose proof (Z.div_mod FB 8 ltac:(lia)) as D3.
    pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as M2. pose proof (Z.mod_pos_bound FB 8 ltac:(lia)) as M3.
    lia. }
  intros Hpos. exact (shadow_hull_vis_of_frame SEGS B LAWS ly S2 W2 mem2 md2 cid pos lp (Z.of_nat (length l) + 1) HAR2 Hin2 ltac:(fold F; lia)
    ltac:(fold F FB; lia) Hpos).
- (* the image *)
  assert (KL : forall x, lp <= x <= lp + Z.of_nat (length l) -> rdW W2 mem2 x = rdW W mem x).
  { intros x Hx. destruct (Himg x ltac:(lia)) as (H1 & H2 & H3). exact (KI x H1 H2 H3). }
  split; [split; [exact Hnz|]|].
  { split; [split; [|exact Hnul] | exact (Hpt _ _ _ _ _ HAR2)].
    intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. rewrite KL by lia.
    exact (Hzs i ltac:(rewrite length_app; cbn [length]; lia)). }
  split; [exact Hlen|].
  split; [right; right; split; [exact Himg|]; split; [exact Hpin | exact Hpt]|].
  split; [exact (Hpin _ _ _ _ _ HAR2) | split; [exact Hdm | exact Hdc]].
Qed.

(* S5_label read through a reader equal to the first everywhere *)
Lemma s5d_label_rd : forall cx f lp c m ly S (rd rd' : reader), (forall a, rd' a = rd a) ->
  S5_label B ly S rd cx f lp c m -> S5_label B ly S rd' cx f lp c m.
Proof.
intros cx f lp c m ly S rd rd' HK (Hlp & Hos & Hmt).
split; [exact Hlp|]. revert Hos Hmt.
destruct (s5_lab (x_pl cx) f) as [l|]; intros Hos Hmt; [|split; [exact Hos | exact I]].
destruct Hos as (Hnz & Hst). destruct Hmt as (Hlen & Hloc & Had & Hdm & Hdc).
split; [split; [exact Hnz | apply (s5d_str_kept rd); [intros x _; apply HK | exact Hst]]|].
split; [exact Hlen|]. split; [exact Hloc|]. split; [exact (s5d_addr_rd rd rd' _ _ HK Had)|].
split; [exact Hdm | exact Hdc].
Qed.

(* a block the harness made since the entry is not one of the entry's blocks *)
Lemma s5d_new_blk : forall cx ly S (W : world SEGS) mem md x O, AR SEGS B ly S W mem md -> lt_blocks B cx ly S O ->
  In x O -> ~ In x (x_bl0 B cx).
Proof.
intros cx ly S W mem md x O HAR HBL HxO Hin. apply in_split in HxO as (o1 & o2 & ->). unfold lt_blocks in HBL.
assert (HP : Permutation (ablocks B ly S) (x :: (o1 ++ o2 ++ x_bl0 B cx))).
{ eapply Permutation_trans; [exact HBL|]. rewrite <- app_assoc. cbn [app]. apply Permutation_sym, Permutation_middle. }
destruct (s5d_dup x _ _ HP ltac:(apply in_or_app; right; apply in_or_app; right; exact Hin)) as (r & Hr).
pose proof (sep_blocks_perm SEGS B LAWS ly S W mem md x x r HAR Hr) as Hsep.
assert (Hx : In x (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym Hr)); left; reflexivity).
destruct x as [b n]. destruct (al_blocks _ _ LAWS ly S W mem md b n HAR Hx) as (_ & _ & _ & _ & _ & _ & Hn).
unfold zdisjoint, block_rng in Hsep. cbn [fst snd] in Hsep. pose proof (req_size_pos n ltac:(lia)) as [Hr1 _]. lia.
Qed.
Lemma s5d_req : forall n, 0 < n -> req_size n = n.
Proof. intros n Hn. unfold req_size. destruct (n =? 0) eqn:E; [apply Z.eqb_eq in E; lia | reflexivity]. Qed.
(* the three blocks of the turn, pairwise apart *)
Lemma s5d_seps : forall cx f ly S (W : world SEGS) mem md c m t, AR SEGS B ly S W mem md ->
  lt_blocks B cx ly S [(t, x_tn cx f); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] ->
  (t + x_tn cx f <= m \/ m + seg_spec.SEG_M_SIZE <= t) /\
  (t + x_tn cx f <= c \/ c + seg_spec.SEG_C_SIZE <= t) /\
  (m + seg_spec.SEG_M_SIZE <= c \/ c + seg_spec.SEG_C_SIZE <= m).
Proof.
intros cx f ly S W mem md c m t HAR HBL. unfold lt_blocks in HBL. cbn [app] in HBL.
assert (Htn : 0 < x_tn cx f) by (unfold x_tn, seg_spec.seg_txt_n; lia).
assert (HMs : 0 < seg_spec.SEG_M_SIZE) by (unfold seg_spec.SEG_M_SIZE; lia).
assert (HCs : 0 < seg_spec.SEG_C_SIZE) by (unfold seg_spec.SEG_C_SIZE; lia).
pose proof (sep_blocks_perm SEGS B LAWS ly S W mem md _ _ _ HAR HBL) as S1.
assert (P2 : Permutation (ablocks B ly S)
  ((t, x_tn cx f) :: (c, seg_spec.SEG_C_SIZE) :: (m, seg_spec.SEG_M_SIZE) :: x_bl0 B cx)).
{ eapply Permutation_trans; [exact HBL|]. apply perm_skip, perm_swap. }
assert (P3 : Permutation (ablocks B ly S)
  ((m, seg_spec.SEG_M_SIZE) :: (c, seg_spec.SEG_C_SIZE) :: (t, x_tn cx f) :: x_bl0 B cx)).
{ eapply Permutation_trans; [exact HBL|]. eapply Permutation_trans; [apply perm_swap|]. apply perm_skip, perm_swap. }
pose proof (sep_blocks_perm SEGS B LAWS ly S W mem md _ _ _ HAR P2) as S2.
pose proof (sep_blocks_perm SEGS B LAWS ly S W mem md _ _ _ HAR P3) as S3.
unfold zdisjoint, block_rng in S1, S2, S3. cbn [fst snd] in S1, S2, S3.
rewrite !s5d_req in S1, S2, S3 by assumption.
split; [exact S1|]. split; [exact S2 | exact S3].
Qed.
(* a text block's string read span stays inside the block's 16-aligned room, apart from another block *)
Lemma s5d_span_disj : forall t s x n, t mod 16 = 0 -> x mod 16 = 0 ->
  (t + (Z.of_nat (length s) + 1) <= x \/ x + n <= t) -> sa_disj t (seg_spec.cstr_span t s) x n.
Proof.
intros t s x n Ht Hx Hd. unfold sa_disj, seg_spec.cstr_span.
pose proof (Z.div_mod (- (t + Z.of_nat (length s) + 1)) 8 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (- (t + Z.of_nat (length s) + 1)) 8 ltac:(lia)) as M1.
pose proof (Z.div_mod x 16 ltac:(lia)) as D2.
pose proof (Z.mod_pos_bound (- (t + Z.of_nat (length s) + 1)) 8 ltac:(lia)) as M2.
lia.
Qed.
(* amem_range of a span inside a live block's in_app room plus the next 7 bytes *)
Lemma s5d_amem : forall p n k, in_app p n -> 0 <= k <= n + 7 -> amem_range p k.
Proof.
intros p n k Happ Hk. pose proof asan_consts as (C1 & _).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd. lia.
Qed.

(* m_file's pre at the call 0x851ac, from the cut's facts *)
Lemma s5d_mf_pre : forall cx f ly S (W : world SEGS) mem md c m t lp,
  AR SEGS B ly S W mem md ->
  lt_blocks B cx ly S [(t, x_tn cx f); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] ->
  lt_cnt f (seg_spec.seg_rc (x_st cx f)) (seg_spec.seg_mc (x_st cx f)) -> (f < 4)%nat ->
  sa_mconf (rdW W mem) m (seg_spec.seg_mc (x_st cx f)) ->
  sa_str (rdW W mem) t (s5_txt (x_pl cx) f) ->
  S5_label B ly S (rdW W mem) cx f lp c m ->
  m_file_pre SEGS B ly S (rdW W mem) m t lp (seg_spec.seg_mc (x_st cx f)) (s5_txt (x_pl cx) f)
    (s5_lab (x_pl cx) f).
Proof.
intros cx f ly S W mem md c m t lp HAR HBL Hcnt Hf4 HMC HSTR HLAB.
pose proof (s5d_seps cx f ly S W mem md c m t HAR HBL) as (Stm & Stc & Smc).
pose proof HBL as HBL0. unfold lt_blocks in HBL0. cbn [app] in HBL0.
assert (HinT : In (t, x_tn cx f) (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym HBL0)); left; reflexivity).
assert (HinM : In (m, seg_spec.SEG_M_SIZE) (ablocks B ly S))
  by (apply (Permutation_in _ (Permutation_sym HBL0)); right; left; reflexivity).
pose proof (s5d_hblk ly S W mem md _ _ HAR HinT) as (_ & Ht4 & Ht16 & HtA).
pose proof (s5d_hblk ly S W mem md _ _ HAR HinM) as (_ & Hm4 & Hm16 & HmA).
destruct (al_blocks _ _ LAWS ly S W mem md t _ HAR HinT) as (_ & _ & _ & HtApp & _).
pose proof (s5d_file_ok (x_pl cx) f) as (_ & Hnul & Hlen).
assert (Etn : x_tn cx f = Z.of_nat (length (s5_txt (x_pl cx) f)) + 1) by reflexivity.
rewrite s5d_req in HtApp by (rewrite Etn; lia).
destruct Hcnt as (_ & _ & _ & G2 & R2 & O2).
destruct HLAB as (Hlp & Hos & Hmt).
unfold m_file_pre.
split; [lia|]. split; [exact Hm16|]. split; [exact HMC|].
split; [exists m, seg_spec.SEG_M_SIZE; split; [exact HinM | lia]|].
split; [exact HmA|].
split.
{ intros x Hx. apply (YG0d_tail.AR_block_word_vis SEGS B ly S W mem md m seg_spec.SEG_M_SIZE
    (m + seg_spec.SEG_M_SIZE - 1) x HAR HinM); [rewrite s5d_req by (unfold seg_spec.SEG_M_SIZE; lia) | ];
    unfold seg_spec.SEG_M_SIZE in *; lia. }
split; [lia|]. split; [lia|]. split; [lia|].
split; [lia|]. split; [exact HSTR|]. split; [unfold s5_txt, seg_spec.seg_txt; lia|].
split; [exists t, (x_tn cx f); split; [exact HinT | rewrite Etn; lia]|].
split; [rewrite <- Etn; exact HtA|].
split; [apply (s5d_amem t (Z.of_nat (length (s5_txt (x_pl cx) f)) + 1)); [exact HtApp | lia]|].
split; [apply s5d_span_disj; [exact Ht16 | exact Hm16 | rewrite <- Etn; exact Stm]|].
split; [exact Hos|].
revert Hmt. destruct (s5_lab (x_pl cx) f) as [l|]; intros Hmt; [|exact I].
destruct Hmt as (Hl & Hloc & Had & Hdm & Hdc).
split; [exact Hl|]. split; [exact Hloc|]. split; [exact Had|].
unfold sa_disj in *. unfold seg_spec.MC_READING, seg_spec.SEG_M_SIZE in *. lia.
Qed.

(* reac_segconf_parse_file's pre at the call 0x851bc *)
Lemma s5d_pf_pre : forall cx f ly S (W : world SEGS) mem md c m t lp,
  AR SEGS B ly S W mem md ->
  lt_blocks B cx ly S [(t, x_tn cx f); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] ->
  lt_cnt f (seg_spec.seg_rc (x_st cx f)) (seg_spec.seg_mc (x_st cx f)) -> (f < 4)%nat ->
  lt_img B cx (rdW W mem) -> sa_frm0 ->
  sa_rconf (rdW W mem) c (seg_spec.seg_rc (x_st cx f)) ->
  sa_str (rdW W mem) t (s5_txt (x_pl cx) f) ->
  S5_label B ly S (rdW W mem) cx f lp c m ->
  reac_segconf_parse_file_pre SEGS B seg_litA_rc catA gotwA guardA ly S (rdW W mem) c t lp
    (seg_spec.seg_rc (x_st cx f)) (s5_txt (x_pl cx) f) (s5_lab (x_pl cx) f).
Proof.
intros cx f ly S W mem md c m t lp HAR HBL Hcnt Hf4 HI HFRM HRC HSTR HLAB.
pose proof (s5d_seps cx f ly S W mem md c m t HAR HBL) as (Stm & Stc & Smc).
pose proof HBL as HBL0. unfold lt_blocks in HBL0. cbn [app] in HBL0.
assert (HinT : In (t, x_tn cx f) (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym HBL0)); left; reflexivity).
assert (HinC : In (c, seg_spec.SEG_C_SIZE) (ablocks B ly S))
  by (apply (Permutation_in _ (Permutation_sym HBL0)); right; right; left; reflexivity).
pose proof (s5d_hblk ly S W mem md _ _ HAR HinT) as (_ & Ht4 & Ht16 & HtA).
pose proof (s5d_hblk ly S W mem md _ _ HAR HinC) as (_ & Hc4 & Hc16 & HcA).
pose proof (s5d_file_ok (x_pl cx) f) as (_ & Hnul & Hlen).
assert (Etn : x_tn cx f = Z.of_nat (length (s5_txt (x_pl cx) f)) + 1) by reflexivity.
destruct Hcnt as (G1 & R1 & O1 & _).
destruct HLAB as (Hlp & Hos & Hmt).
destruct HI as (HRO & HIMG & _).
destruct HIMG as (_ & _ & _ & Hrc & Hcat & _ & _ & _ & Hssp & _).
split.
{ split; [lia|]. split; [exact Hc16|]. split; [exact HRC|].
  split; [exists c, seg_spec.SEG_C_SIZE; split; [exact HinC | lia]|].
  split; [exact HcA|].
  split; [lia|]. split; [lia|]. split; [lia|].
  split; [lia|]. split; [exact HSTR|]. split; [apply Nat2Z.inj_le; exact Hlen|].
  split; [exists t, (x_tn cx f); split; [exact HinT | rewrite Etn; lia]|].
  split; [rewrite <- Etn; exact HtA|].
  split; [apply s5d_span_disj; [exact Ht16 | exact Hc16 | rewrite <- Etn; exact Stc]|].
  split; [exact HFRM|]. split; [exact Hssp|]. split; [exact Hcat|].
  intros x Hx. apply (Hrc x). unfold LTOI_RC_LITS. apply in_or_app. left. exact Hx. }
split; [exact Hos|].
revert Hmt. destruct (s5_lab (x_pl cx) f) as [l|]; intros Hmt; [|exact I].
destruct Hmt as (Hl & Hloc & Had & Hdm & Hdc).
split; [apply Nat2Z.inj_le; exact Hl|]. split; [exact Hloc|]. split; [exact Had|].
unfold sa_disj in *. unfold seg_spec.RC_READING, seg_spec.SEG_C_SIZE in *. lia.
Qed.

(* one call of a program function that allocates nothing, from a point where lt_core holds, through
   PaFx.cl_callSF; the continuation is given the state the callee returned, at its FP state *)
Lemma s5d_call_at : forall cx ly S (W : world SEGS) regsT memT md k acc rem o O pc STK1 FP1 raw
  (Kc : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  lt_base B MT cx -> lt_core B MT cx ly S W regsT memT md k acc rem o O ->
  0 <= STK1 -> STK1 + 336 <= STK_LLVMFuzzerTestOneInput ->
  getr regsT 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  (forall a, inFP FP1 a -> exists b n, In (b, n) (ablocks B ly S) /\ ~ In (b, n) (x_bl0 B cx) /\
     b <= a < b + req_size n) ->
  (forall ly2 S2 (W2 : world SEGS) regs2 mem2 md2, Kc ly2 S2 W2 regs2 mem2 md2 -> sa_noalloc B ly S ly2 S2) ->
  (forall ch, afn_pre SEGS B STK1 ly S W regsT memT md ch ->
     SRr SEGS W (mkCfg (mkst regsT pc memT (seg_rom SEGS)) md)
       (apost_baseF SEGS B STK1 FP1 regsT ly S W memT md 0 Kc)) ->
  (forall (fx1 : YK11.FPState) S2 (W2 : world SEGS) regs2 mem2 md2, fxrel fx fx1 ->
     lt_core B MT cx ly S2 W2 regs2 mem2 md2 k acc rem o O ->
     AR SEGS B ly S2 W2 mem2 md2 -> frames S2 = frames S ->
     Permutation (ablocks B ly S2) (ablocks B ly S) ->
     aregs_preserved regsT regs2 -> Kc ly S2 W2 regs2 mem2 md2 ->
     (forall a, x_s1 cx <= a < 2 ^ 64 -> rdW W2 mem2 a = rdW W memT a) ->
     (forall b n i, In (b, n) (ablocks B ly S) -> 0 <= i < req_size n -> ~ inFP FP1 (b + i) ->
        rdW W2 mem2 (b + i) = rdW W memT (b + i)) ->
     (forall cid pos a, In (cid, pos) (frames S) ->
        (frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid \/
         shadow_addr (frame_addr ly cid pos) <= a < shadow_addr (frame_addr ly cid pos) + fs_frame_bytes cid / 8) ->
        rdW W2 mem2 a = rdW W memT a) ->
     (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
        rdW W2 mem2 a = rdW W memT a) ->
     SRr SEGS W2 (mkCfg (@mkst fx1 regs2 raw mem2 (seg_rom SEGS)) md2)
       (apost_baseF (fx := fx1) SEGS B STK_LLVMFuzzerTestOneInput (ltoi_PG longlA) (x_regs cx) (x_ly cx) (x_S cx)
         (x_W cx) (x_mem cx) (x_md cx) (EV_LTOI (x_pl cx)) (lt_Q B MT cx))) ->
  SRr SEGS W (mkCfg (mkst regsT pc memT (seg_rom SEGS)) md) (lt_post B MT cx).
Proof.
intros cx ly S W regsT memT md k acc rem o O pc STK1 FP1 raw Kc HB HC HS0 HS1 H1 Hraw Hra4 HFP HNA HCALLEE HK.
pose proof (s5d_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
pose proof HC as (HF & _). pose proof HF as (HJ & R2 & R3 & R4 & _).
pose proof HB as (HPRE0 & _). pose proof HPRE0 as (_ & _ & _ & Hgp0 & Htp0 & _).
pose proof asan_consts as (C1 & _).
unfold STK_LLVMFuzzerTestOneInput in HS1.
destruct (s5d_chain cx ly S W regsT memT md k o HB HF) as (ch & Hch).
assert (Hsp : spZ regsT = x_sp0 cx + (x_s1 cx - x_sp0 cx))
  by (unfold spZ; rewrite R2; unfold w64; rewrite YP03.unsigned_lit_small by lia; ring).
assert (Ho16 : (x_s1 cx - x_sp0 cx) mod 16 = 0).
{ destruct (s10_sp1_facts (x_sp0 cx) Hal0) as (_ & [Hq | Hq]); change (x_s1 cx) with (s10_sp1 (x_sp0 cx)); rewrite Hq;
  [replace (x_sp0 cx - 320 - x_sp0 cx) with (-320) by ring | replace (x_sp0 cx - 336 - x_sp0 cx) with (-336) by ring];
  reflexivity. }
assert (Hch' : achain ly (rdW W memT) (x_sp0 cx + (x_s1 cx - x_sp0 cx)) (s0Z regsT) ch)
  by (replace (x_sp0 cx + (x_s1 cx - x_sp0 cx)) with (x_s1 cx) by ring; exact Hch).
unfold lt_post.
eapply (srr_after_callF (fx := fx) SEGS).
{ apply (cl_callSF B LAWS W regsT memT pc STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA)
    (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [(LT_FCLS, x_fpos cx)] ly S md k STK1 FP1 0
    (x_s1 cx - x_sp0 cx) (getr regsT 1) ch Kc HJ Hsp Ho16 ltac:(lia) HS0 ltac:(unfold STK_LLVMFuzzerTestOneInput; lia)
    ltac:(rewrite R3; exact Hgp0) ltac:(rewrite R4; exact Htp0) eq_refl ltac:(rewrite H1; exact Hraw)
    ltac:(rewrite H1; exact Hra4) Hch').
  - intros HPRE1. eapply SRr_mono; [exact (HCALLEE ch HPRE1) | intros W3 c3 _ H3; exact H3].
  - intros a Ha. right. destruct (HFP a Ha) as (b & n & Hb1 & Hb2 & Hb3). exists b, n. auto. }
cbv beta. intros fx1 ly2 S2 W2 regs2 mem2 md2 _ Hfx (HJ2 & HJc & HP & HKc).
rewrite Z.add_0_r in HJ2.
replace (x_sp0 cx + (x_s1 cx - x_sp0 cx)) with (x_s1 cx) in HJc by ring.
pose proof (HNA _ _ _ _ _ _ HKc) as HNA2.
pose proof HNA2 as (HPm & Hly2 & _). subst ly2.
pose proof HJc as (HAR2 & _ & _ & _ & _ & Hfrs2 & _).
destruct (s5d_carry cx ly S W regsT memT md k acc rem o O ly S2 W2 regs2 mem2 md2 STK1 FP1 HB HC HJ2 HJc
  ltac:(intros a Ha; destruct (HFP a Ha) as (b & n & Hb1 & _ & Hb3); exists b, n; auto) HP HNA2)
  as (HC2 & KS & KB & KF & KI).
rewrite H1.
exact (HK fx1 S2 W2 regs2 mem2 md2 Hfx HC2 HAR2 ltac:(rewrite Hfrs2; reflexivity) HPm HP HKc KS KB KF KI).
Qed.

Hypothesis SIGP : seg_sig_prog.
Hypothesis HPARSE_FILE : forall fx0 : YK11.FPState,
  @reac_segconf_parse_file_c.reac_segconf_parse_file_contract fx0 rc SK SEGS B
    (BASE + AF_reac_segconf_parse_file) STK_reac_segconf_parse_file RLO_A RHI_A seg_litA_rc catA gotwA guardA.

(* ---- 0x851b0 .. 0x851bc and the call of reac_segconf_parse_file, to the cut S5_CK (0x851c0), at the FP state m_file
   returned: `ld a0,160(s1)` (c from the slot), `mv a1,s7`, `mv a2,s4`, `jal reac_segconf_parse_file` ---- *)
Lemma s5d_mid : forall f, S5A_CK B MT f ->
  forall cx ly S (W : world SEGS) regs mem md k acc (c m t lp : Z),
  lt_base B MT cx -> sa_frm0 -> Z.of_nat f + 1 < x_nf cx ->
  S5_body B MT cx ly S W regs mem md k acc LFO_L c m t f ->
  sa_rconf (rdW W mem) c (seg_spec.seg_rc (x_st cx f)) ->
  sa_mconf (rdW W mem) m (s5_mc1 (x_pl cx) f) ->
  sa_str (rdW W mem) t (s5_txt (x_pl cx) f) ->
  S5_label B ly S (rdW W mem) cx f lp c m ->
  getr regs 18 = w64 (Z.of_nat f + 1) -> getr regs 19 = w64 (-8) ->
  getr regs 20 = w64 lp -> getr regs 21 = w64 (x_sh cx) ->
  getr regs 22 = w64 (seg_spec.b2z (seg_spec.seg_ret (x_st cx f))) ->
  getr regs 23 = w64 t ->
  getr regs 24 = w64 (seg_spec.seg_turn_at (x_pl cx) (x_p cx) f) -> getr regs 25 = w64 (x_nf cx) ->
  getr regs 26 = w64 ((m + seg_spec.MC_N) / 8) ->
  getr regs 27 = w64 (seg_spec.seg_turn_np (x_pl cx) f) ->
  lt_slots cx (rdW W mem) (LT_L cx c m ++ [(152, Z.of_nat (length (seg_spec.seg_turn_tail (x_pl cx) f)))]) ->
  SRr SEGS W (cfg_at SEGS (BASE + 0x47c) regs mem md) (lt_post B MT cx).
Proof.
intros f HKA cx ly S W regs mem md k acc c m t lp HB HFRM Hf HBODY HRC HMC HSTR HLAB
  R18 R19 R20 R21 R22 R23 R24 R25 R26 R27 HSL.
pose proof (paj_run B LAWS) as RUN.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (s5d_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
pose proof (s5d_nf_le4 (x_pl cx)) as Hnf4. unfold x_nf in Hf.
assert (Hf4 : (f < 4)%nat) by lia.
pose proof HBODY as (HC & HHc & HHm & HHt & Hcnt).
pose proof HC as (HF & HI & HBL & HBUD).
pose proof HF as (HJ & FR2 & FR3 & FR4 & FR8 & FR9 & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & Hnev & _).
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hfr0 & _ & Hev0 & _).
pose proof asan_consts as (C1 & _).
assert (HS160 : rdword (rdW W mem) (x_s1 cx + 160) = Some c).
{ apply HSL. apply in_or_app. left. unfold LT_L. cbn [In]. repeat (first [left; reflexivity | right]). }
destruct HHc as (HinC & Hc4 & Hc16 & HcA). destruct HHt as (HinT & Ht4 & Ht16 & HtA).
assert (Hc64 : 0 <= c < 2 ^ 64) by (destruct HcA as (Ha0 & Ha1 & _); unfold seg_spec.SEG_C_SIZE in Ha1; lia).
assert (Ht64 : 0 <= t < 2 ^ 64) by (destruct HtA as (Ha0 & Ha1 & _); unfold x_tn, seg_spec.seg_txt_n in Ha1; lia).
assert (Hlp64 : 0 <= lp < 2 ^ 64) by (destruct HLAB as (Hq & _); exact Hq).
assert (Us1 : bv_unsigned (getr regs 9) = x_s1 cx)
  by (rewrite FR9; unfold w64; apply YP03.unsigned_lit_small; lia).
pose proof (s5d_seed1 0x47c W regs mem c ltac:(rewrite Us1; lia) Hc64 ltac:(rewrite Us1; exact HS160)) as HS.
assert (SHOK : sh_ok SEGS (SLit SHADOW_OFF) [] (Eimg (Ereg regs [Z_to_bv 64 c])) (mrestrict (w_H W) mem))
  by apply Forall_nil.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs [Z_to_bv 64 c]))) by apply Eimg_env.
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew (Eimg (Ereg regs [Z_to_bv 64 c])) n = getr regs rr)
  by (intros n rr Hn; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew (Eimg (Ereg regs [Z_to_bv 64 c])) 32 = Z_to_bv 64 c).
{ rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs [Z_to_bv 64 c] 0). }
assert (Hnw : forall E0 a, ~ in_wrange E0 [s5d_r160] a).
{ intros E0 a (r & Hr & Ha). destruct Hr as [<- | []]. cbn [YP09.r_wlo YP09.r_whi s5d_r160] in Ha. lia. }
remember (Eimg (Ereg regs [Z_to_bv 64 c])) as E eqn:HE. clear HE.
unfold cfg_at, w64.
paj_run_tok RUN HS HJ SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
{ apply awr_ok_cons_ro; [unfold s5d_r160; cbn [YP09.r_whi YP09.r_wlo]; lia | apply awr_ok_nil]. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md1 := d) in *; clearbody md1 end.
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12.
assert (KR : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
  getr (ms_regs ms) r = getr regs r).
{ intros r Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr];
    [ let P := fresh "P" in lazymatch goal with |- getr _ ?rr = _ => prreg HS rr P end;
      rewrite P; apply EEo; reflexivity | ]).
  destruct Hr. }
pose proof (s5d_frame_all E _ (w_H W) mem (ms_mem ms) (Hnw E) HFr) as KM.
pose proof (s5d_core_rd cx ly S W regs mem md k acc _ LFO_L _ (ms_regs ms) (ms_mem ms) md1 HC HJ KM
  (KR 2%bv ltac:(cbn; tauto)) (KR 3%bv ltac:(cbn; tauto)) (KR 4%bv ltac:(cbn; tauto))
  (KR 8%bv ltac:(cbn; tauto)) (KR 9%bv ltac:(cbn; tauto))) as HC1.
pose proof HC1 as ((HJ1 & _) & HI1 & _).
pose proof (proj1 HJ1) as HAR1.
assert (Q10 : getr (ms_regs ms) 10 = w64 c) by (rewrite P10; exact E32).
assert (Q11 : getr (ms_regs ms) 11 = w64 t) by (rewrite P11, (EEo 23%nat 23%bv eq_refl); exact R23).
assert (Q12 : getr (ms_regs ms) 12 = w64 lp) by (rewrite P12, (EEo 20%nat 20%bv eq_refl); exact R20).
assert (HPF : In SS_reac_segconf_parse_file seg_prog_syms)
  by (cbn [seg_prog_syms In]; repeat (first [left; reflexivity | right])).
rewrite (SIGP SS_reac_segconf_parse_file HPF).
replace (seg_af SS_reac_segconf_parse_file) with AF_reac_segconf_parse_file by (vm_compute; reflexivity).
assert (HinM : In (m, seg_spec.SEG_M_SIZE) (ablocks B ly S)) by exact (proj1 HHm).
pose proof (s5d_seps cx f ly S W mem md c m t HAR HBL) as (Stm & Stc & Smc).
assert (HROOM : sa_room_n 2 S) by (unfold sa_room_n; rewrite Hfrs, Hfr0; cbn [app length Z.of_nat]; lia).
assert (HEVc : st_nev S + EV_reac_segconf_parse_file <= EV_MAX).
{ destruct HBUD as (B1 & B2 & B3 & _). unfold EV_reac_segconf_parse_file. unfold EV_LTOI in Hev0, B3.
  clear - Hnev Hev0 B1 B2 B3. lia. }
set (rc0 := seg_spec.seg_rc (x_st cx f)) in *.
set (s := s5_txt (x_pl cx) f) in *. set (lab := s5_lab (x_pl cx) f) in *.
eapply (s5d_call_at cx ly S W (ms_regs ms) (ms_mem ms) md1 k acc _ LFO_L _
  (Z_to_bv 64 (BASE + AF_reac_segconf_parse_file)) STK_reac_segconf_parse_file (seg_spec.RC_PARSE_W c) _
  (fun ly' S' W' regs' mem' md' =>
     getr regs' 10 = w64 (snd (SegModel.r_parse_file rc0 s lab)) /\
     sa_rconf (aview SEGS (w_H W') mem') c (fst (SegModel.r_parse_file rc0 s lab)) /\
     sa_noalloc B ly S ly' S') HB HC1).
- apply Z.leb_le. vm_compute. reflexivity.
- apply Z.leb_le. vm_compute. reflexivity.
- exact P1.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- rewrite YP03.unsigned_lit_small by lia. lia.
- intros a Ha. apply s5d_pfw_in in Ha. exists c, seg_spec.SEG_C_SIZE. split; [exact HinC|].
  split; [apply (s5d_new_blk cx ly S W mem md _ _ HAR HBL); right; right; left; reflexivity|].
  rewrite s5d_req by (unfold seg_spec.SEG_C_SIZE; lia). exact Ha.
- intros ly2 S2 W2 regs2 mem2 md2 (_ & _ & H). exact H.
- intros ch HPRE1.
  exact (HPARSE_FILE fx ly S W (ms_regs ms) (ms_mem ms) md1 ch c t lp rc0 s lab HPRE1 (proj1 HI1) Q10 Hc64 Q11 Ht64
    Q12 Hlp64
    (s5d_pf_pre cx f ly S W (ms_mem ms) md1 c m t lp HAR1 HBL Hcnt Hf4 HI1 HFRM
      (s5d_rconf_kept (rdW W mem) _ c rc0 (fun i _ => KM (c + i)) HRC)
      (s5d_str_kept (rdW W mem) _ t s (fun x _ => KM x) HSTR)
      (s5d_label_rd cx f lp c m ly S (rdW W mem) _ KM HLAB))
    HROOM HEVc).
- intros fx2 S3 W3 regs3 mem3 md3 Hfx HC3 HAR3 Hfr3 HPm3 HP3 (H10' & HRC3 & _) KS3 KB3 KF3 KI3.
  assert (HRS : forall r z, acallee_saved z -> Z_to_bv 5 z = r -> In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
    getr regs3 r = getr regs r).
  { intros r z Hz Hr Hin. rewrite (s5d_pres _ _ r z HP3 Hz Hr). exact (KR r Hin). }
  assert (HbIn : forall b n, In (b, n) (ablocks B ly S) -> In (b, n) (ablocks B ly S3))
    by (intros b n H; apply (Permutation_in _ (Permutation_sym HPm3)); exact H).
  change (Z_to_bv 64 (BASE + 1164)) with (w64 (BASE + LO_S5CK)).
  apply (HKA fx2 cx ly S3 W3 regs3 mem3 md3 k acc c m t lp HB (fxrel_frm0 fx fx2 HFRM Hfx) Hf).
  + (* S5_body at the return *)
    split; [exact HC3|].
    split; [exact (s5d_hblk ly S3 W3 mem3 md3 _ _ HAR3 (HbIn _ _ HinC))|].
    split; [exact (s5d_hblk ly S3 W3 mem3 md3 _ _ HAR3 (HbIn _ _ HinM))|].
    split; [exact (s5d_hblk ly S3 W3 mem3 md3 _ _ HAR3 (HbIn _ _ HinT))|].
    exact Hcnt.
  + exact HRC3.
  + apply (s5d_mconf_kept (rdW W mem)); [|exact HMC]. intros i Hi.
    rewrite (KB3 m seg_spec.SEG_M_SIZE i HinM ltac:(rewrite s5d_req by (unfold seg_spec.SEG_M_SIZE; lia); lia)).
    * apply KM.
    * intros Hq. apply s5d_pfw_in in Hq. unfold seg_spec.SEG_M_SIZE, seg_spec.SEG_C_SIZE in *. lia.
  + exact (s5d_cnt_next (x_pl cx) f Hcnt).
  + exact H10'.
  + rewrite (HRS 18%bv 18) by first [unfold acallee_saved; lia | apply bv_eq; reflexivity | cbn; tauto]. exact R18.
  + rewrite (HRS 19%bv 19) by first [unfold acallee_saved; lia | apply bv_eq; reflexivity | cbn; tauto]. exact R19.
  + rewrite (HRS 20%bv 20) by first [unfold acallee_saved; lia | apply bv_eq; reflexivity | cbn; tauto]. exact R20.
  + rewrite (HRS 21%bv 21) by first [unfold acallee_saved; lia | apply bv_eq; reflexivity | cbn; tauto]. exact R21.
  + rewrite (HRS 22%bv 22) by first [unfold acallee_saved; lia | apply bv_eq; reflexivity | cbn; tauto]. exact R22.
  + rewrite (HRS 23%bv 23) by first [unfold acallee_saved; lia | apply bv_eq; reflexivity | cbn; tauto]. exact R23.
  + rewrite (HRS 24%bv 24) by first [unfold acallee_saved; lia | apply bv_eq; reflexivity | cbn; tauto]. exact R24.
  + rewrite (HRS 25%bv 25) by first [unfold acallee_saved; lia | apply bv_eq; reflexivity | cbn; tauto]. exact R25.
  + rewrite (HRS 26%bv 26) by first [unfold acallee_saved; lia | apply bv_eq; reflexivity | cbn; tauto]. exact R26.
  + rewrite (HRS 27%bv 27) by first [unfold acallee_saved; lia | apply bv_eq; reflexivity | cbn; tauto]. exact R27.
  + apply (s5d_slots_kept cx (rdW W mem)); [apply s5d_L_bnd | | exact HSL].
    intros a Ha. rewrite KS3 by lia. apply KM.
Qed.

End s5de.
End s5df.
End s5dd.

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
Variable snp_lo snp_hi : Z.
Variable snp_cr : list (Z * Z).
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis IMGS : s10_img.
Hypothesis BSYM : AF0m.SegBSyms B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis PRW : prog_rw SEGS B.
Hypothesis VOBJS : seg_val_objs.
Hypothesis SIGP : seg_sig_prog.
Hypothesis HPGS : forall a, inFP (ltoi_PG longlA) a ->
  Exists (in_zr a) (as_prog_static B) /\ in_img SEGS a.
Hypothesis HPG_RO : forall a, inFP (ltoi_PG longlA) a -> ~ in_roP SEGS RLO_A RHI_A a.
Hypothesis HPG_PTR : forall a p,
  ((exists i, (i < 5)%nat /\ a = wordsA + 8 * Z.of_nat i) \/
   (exists i, (i < pin_spec.CAT_N)%nat /\ a = pin_spec.row_addr catA i)) ->
  rdword (fun x => option_map (fun b : byte => bv_unsigned b) (seg_rom SEGS (Z_to_bv 64 x))) a = Some p ->
  p + 65536 <= longlA.
Hypothesis AMEMCPY : forall fx0 : YK11.FPState,
  @aintrin_realizes fx0 rc SEGS B OCpy (SIG SS___asan_memcpy).
Hypothesis AMEMSET : forall fx0 : YK11.FPState,
  @aintrin_realizes fx0 rc SEGS B OSet (SIG SS___asan_memset).
Hypothesis AFREE4 : forall fx0 : YK11.FPState, @afree04_rule fx0 rc SK SEGS B MT.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState,
  @RtPFSeg.seg_asnprintf_realizes fx0 rc SEGS B snp_lo snp_hi snp_cr
    (SIG SS___interceptor_trampoline_snprintf) gotwA guardA.
Hypothesis HSNP_LIT : forall x, In x LLVMFuzzerTestOneInput_c.LTOI_LITS ->
  snp_lo <= seg_litA_fz x /\ seg_litA_fz x + Z.of_nat (length x) + 1 <= gotwA.
Hypothesis HSNP_CR : Forall (fun r => snp_lo <= fst r /\ 0 <= snd r /\ fst r + snd r <= snp_hi) snp_cr.
Hypothesis HSNP_LO : 0 <= snp_lo.
Hypothesis HSNP_CEIL : snp_hi <= alloc_ceiling.
Hypothesis HSNP_FAKE : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> snp_hi <= ly_F ly.
Hypothesis HM_FILE : forall fx0 : YK11.FPState,
  @m_file_c.m_file_contract fx0 rc SK SEGS B (BASE + AF_m_file) STK_m_file RLO_A RHI_A seg_litA_fz
    wordsA rolesA catA gotwA guardA.
Hypothesis HPARSE_FILE : forall fx0 : YK11.FPState,
  @reac_segconf_parse_file_c.reac_segconf_parse_file_contract fx0 rc SK SEGS B
    (BASE + AF_reac_segconf_parse_file) STK_reac_segconf_parse_file RLO_A RHI_A seg_litA_rc catA gotwA guardA.

(* ---- 0x851a4 .. 0x851ac and the call of m_file, then s5d_mid at the FP state m_file returned ---- *)
Lemma s5_calls : forall f, S5A_CK B MT f -> S5_OTH_stmt B MT f.
Proof using All.
intros f HKA. unfold S5_OTH_stmt.
intros cx ly S W regs mem md k acc c m t lp HB HFRM Hf HBODY HCM HSTR HLAB
  R10 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27 HSL.
pose proof (paj_run B LAWS) as RUN.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (s5d_sp B MT cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
pose proof (s5d_nf_le4 (x_pl cx)) as Hnf4. unfold x_nf in Hf.
assert (Hf4 : (f < 4)%nat) by lia.
pose proof HBODY as (HC & HHc & HHm & HHt & Hcnt).
pose proof HC as (HF & HI & HBL & HBUD).
pose proof HF as (HJ & FR2 & FR3 & FR4 & FR8 & FR9 & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & Hnev & _).
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hfr0 & _ & Hev0 & _).
pose proof HCM as (HRC & HMC).
pose proof asan_consts as (C1 & _).
destruct HHc as (HinC & Hc4 & Hc16 & HcA). destruct HHt as (HinT & Ht4 & Ht16 & HtA).
destruct HHm as (HinM & Hm4 & Hm16 & HmA).
assert (Hm64 : 0 <= m < 2 ^ 64) by (destruct HmA as (Ha0 & Ha1 & _); unfold seg_spec.SEG_M_SIZE in Ha1; lia).
assert (Ht64 : 0 <= t < 2 ^ 64) by (destruct HtA as (Ha0 & Ha1 & _); unfold x_tn, seg_spec.seg_txt_n in Ha1; lia).
assert (Hlp64 : 0 <= lp < 2 ^ 64) by (destruct HLAB as (Hq & _); exact Hq).
pose proof (s5d_seed0 LO_S5OTH W regs mem) as HS.
assert (SHOK : sh_ok SEGS (SLit SHADOW_OFF) [] (Eimg (Ereg regs [])) (mrestrict (w_H W) mem)) by apply Forall_nil.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs []))) by apply Eimg_env.
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew (Eimg (Ereg regs [])) n = getr regs rr)
  by (intros n rr Hn; apply ew_Eimg_Ereg_nat; exact Hn).
assert (Hnw : forall E0 a, ~ in_wrange E0 [] a) by (intros E0 a (r & Hr & _); destruct Hr).
remember (Eimg (Ereg regs [])) as E eqn:HE. clear HE.
unfold cfg_at, w64.
paj_run_tok RUN HS HJ SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
{ apply awr_ok_nil. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md1 := d) in *; clearbody md1 end.
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12.
assert (KR : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
  getr (ms_regs ms) r = getr regs r).
{ intros r Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr];
    [ let P := fresh "P" in lazymatch goal with |- getr _ ?rr = _ => prreg HS rr P end;
      rewrite P; apply EEo; reflexivity | ]).
  destruct Hr. }
pose proof (s5d_frame_all E _ (w_H W) mem (ms_mem ms) (Hnw E) HFr) as KM.
pose proof (s5d_core_rd B MT IMGS BSYM cx ly S W regs mem md k acc _ LFO_L _ (ms_regs ms) (ms_mem ms) md1 HC HJ KM
  (KR 2%bv ltac:(cbn; tauto)) (KR 3%bv ltac:(cbn; tauto)) (KR 4%bv ltac:(cbn; tauto))
  (KR 8%bv ltac:(cbn; tauto)) (KR 9%bv ltac:(cbn; tauto))) as HC1.
pose proof HC1 as ((HJ1 & _) & HI1 & _).
pose proof (proj1 HJ1) as HAR1.
pose proof HI1 as (HRO1 & HIMG1 & _).
pose proof HIMG1 as (_ & _ & Hfz1 & _ & Hcat1 & _ & Hwd1 & Hrl1 & Hssp1 & _).
assert (Q10 : getr (ms_regs ms) 10 = w64 m) by (rewrite P10, (EEo 10%nat 10%bv eq_refl); exact R10).
assert (Q11 : getr (ms_regs ms) 11 = w64 t) by (rewrite P11, (EEo 23%nat 23%bv eq_refl); exact R23).
assert (Q12 : getr (ms_regs ms) 12 = w64 lp) by (rewrite P12, (EEo 20%nat 20%bv eq_refl); exact R20).
assert (HPM : In SS_m_file seg_prog_syms) by (cbn [seg_prog_syms In]; left; reflexivity).
rewrite (SIGP SS_m_file HPM).
replace (seg_af SS_m_file) with AF_m_file by (vm_compute; reflexivity).
pose proof (s5d_seps B cx f ly S W mem md c m t HAR HBL) as (Stm & Stc & Smc).
assert (HROOM : sa_room S) by (unfold sa_room; rewrite Hfrs, Hfr0; cbn [app length Z.of_nat]; lia).
assert (HEVc : st_nev S + EV_m_file <= EV_MAX).
{ destruct HBUD as (B1 & B2 & B3 & _). unfold EV_m_file. unfold EV_LTOI in Hev0, B3.
  clear - Hnev Hev0 B1 B2 B3. lia. }
set (mc0 := seg_spec.seg_mc (x_st cx f)) in *.
set (s := s5_txt (x_pl cx) f) in *. set (lab := s5_lab (x_pl cx) f) in *.
assert (HMB : s5d_mb (SegModel.m_file mc0 s lab)).
{ apply s5d_mfile_mb. destruct HMC as (bs & _ & He). exact (s5d_mb_of_enc _ _ _ He). }
eapply (s5d_call_at B MT MTFL IMGS BSYM cx ly S W (ms_regs ms) (ms_mem ms) md1 k acc _ LFO_L _
  (Z_to_bv 64 (BASE + AF_m_file)) STK_m_file (M_FILE_FP m (length (SegModel.mc_kept mc0)) (SegModel.m_file mc0 s lab)) _
  (fun ly' S' W' regs' mem' md' =>
     sa_mconf (aview SEGS (w_H W') mem') m (SegModel.m_file mc0 s lab) /\ sa_noalloc B ly S ly' S') HB HC1).
- apply Z.leb_le. vm_compute. reflexivity.
- apply Z.leb_le. vm_compute. reflexivity.
- exact P1.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- rewrite YP03.unsigned_lit_small by lia. lia.
- intros a Ha. apply (s5d_mfp_in _ _ _ _ HMB) in Ha. exists m, seg_spec.SEG_M_SIZE. split; [exact HinM|].
  split; [apply (s5d_new_blk B cx ly S W mem md _ _ HAR HBL); right; left; reflexivity|].
  rewrite s5d_req by (unfold seg_spec.SEG_M_SIZE; lia). exact Ha.
- intros ly2 S2 W2 regs2 mem2 md2 (_ & H). exact H.
- intros ch HPRE1.
  exact (HM_FILE fx ly S W (ms_regs ms) (ms_mem ms) md1 ch m t lp mc0 s lab HPRE1 HFRM
    HROOM HRO1
    (fun x Hx => proj1 (Hfz1 x ltac:(unfold LTOI_FZ_LITS; rewrite !in_app_iff; right; right; right; exact Hx)))
    Hwd1 Hrl1 Hcat1 Hssp1 Q10 Hm64 Q11 Ht64 Q12 Hlp64
    (s5d_mf_pre B cx f ly S W (ms_mem ms) md1 c m t lp HAR1 HBL Hcnt Hf4
      (s5d_mconf_kept (rdW W mem) _ m mc0 (fun i _ => KM (m + i)) HMC)
      (s5d_str_kept (rdW W mem) _ t s (fun x _ => KM x) HSTR)
      (s5d_label_rd B cx f lp c m ly S (rdW W mem) _ KM HLAB))
    HEVc).
- intros fx1 S2 W2 regs2 mem2 md2 Hfx HC2 HAR2 Hfr2 HPm2 HP2 (HMC2 & _) KS2 KB2 KF2 KI2.
  assert (HRS : forall r z, acallee_saved z -> Z_to_bv 5 z = r ->
    In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs2 r = getr regs r).
  { intros r z Hz Hr Hin. rewrite (s5d_pres _ _ r z HP2 Hz Hr). exact (KR r Hin). }
  assert (HbIn : forall b n, In (b, n) (ablocks B ly S) -> In (b, n) (ablocks B ly S2))
    by (intros b n H; apply (Permutation_in _ (Permutation_sym HPm2)); exact H).
  assert (Hreq : forall n, 0 < n -> req_size n = n) by exact s5d_req.
  assert (Htn : x_tn cx f = Z.of_nat (length s) + 1) by reflexivity.
  (* the bytes of a block other than m: kept, and the entry's *)
  assert (KBo : forall b n i, In (b, n) (ablocks B ly S) -> 0 <= i < req_size n ->
     ~ (m <= b + i < m + seg_spec.SEG_M_SIZE) -> rdW W2 mem2 (b + i) = rdW W (ms_mem ms) (b + i)).
  { intros b n i Hbn Hi Hn. apply (KB2 b n i Hbn Hi). intros Hq. exact (Hn (s5d_mfp_in _ _ _ _ HMB Hq)). }
  pose proof Stm as Stm'. rewrite Htn in Stm'.
  assert (KC : forall i, 0 <= i < seg_spec.SEG_C_SIZE -> rdW W2 mem2 (c + i) = rdW W mem (c + i)).
  { intros i Hi. rewrite (KBo c seg_spec.SEG_C_SIZE i HinC); [apply KM | |].
    - rewrite Hreq by (unfold seg_spec.SEG_C_SIZE; lia). lia.
    - unfold seg_spec.SEG_M_SIZE, seg_spec.SEG_C_SIZE in *. lia. }
  assert (KLt : forall x, t <= x <= t + Z.of_nat (length s) -> rdW W2 mem2 x = rdW W mem x).
  { intros x Hx. replace x with (t + (x - t)) by ring.
    rewrite (KBo t (x_tn cx f) (x - t) HinT); [apply KM | |].
    - rewrite Hreq by (rewrite Htn; lia). rewrite Htn. lia.
    - unfold seg_spec.SEG_M_SIZE in *. lia. }
  assert (KSl : forall a, x_s1 cx <= a < x_s1 cx + 192 -> rdW W2 mem2 a = rdW W mem a).
  { intros a Ha. rewrite KS2 by lia. apply KM. }
  assert (HBODY2 : S5_body B MT cx ly S2 W2 regs2 mem2 md2 k acc LFO_L c m t f).
  { split; [exact HC2|].
    split; [exact (s5d_hblk B ly S2 W2 mem2 md2 _ _ HAR2 (HbIn _ _ HinC))|].
    split; [exact (s5d_hblk B ly S2 W2 mem2 md2 _ _ HAR2 (HbIn _ _ HinM))|].
    split; [exact (s5d_hblk B ly S2 W2 mem2 md2 _ _ HAR2 (HbIn _ _ HinT))|].
    exact Hcnt. }
  change (Z_to_bv 64 (BASE + 1148)) with (w64 (BASE + 0x47c)).
  apply (s5d_mid (fx := fx1) B MT MTFL IMGS BSYM SIGP HPARSE_FILE f HKA cx ly S2 W2 regs2 mem2 md2 k acc c m t lp HB
    (fxrel_frm0 fx fx1 HFRM Hfx) Hf HBODY2).
  + exact (s5d_rconf_kept (rdW W mem) _ c _ KC HRC).
  + exact HMC2.
  + exact (s5d_str_blk B (rdW W mem) ly S2 W2 mem2 md2 t (x_tn cx f) t s HAR2 (HbIn _ _ HinT) ltac:(lia)
      ltac:(rewrite Htn; lia) KLt HSTR).
  + exact (s5d_label_post B cx f lp c m ly S W (ms_mem ms) ly S2 W2 mem2 md2
      (s5d_label_rd B cx f lp c m ly S (rdW W mem) _ KM HLAB) HAR2 eq_refl Hfr2 HbIn KBo KF2 KI2).
  + rewrite (HRS 18%bv 18) by first [unfold acallee_saved; lia | apply bv_eq; reflexivity | cbn; tauto]. exact R18.
  + rewrite (HRS 19%bv 19) by first [unfold acallee_saved; lia | apply bv_eq; reflexivity | cbn; tauto]. exact R19.
  + rewrite (HRS 20%bv 20) by first [unfold acallee_saved; lia | apply bv_eq; reflexivity | cbn; tauto]. exact R20.
  + rewrite (HRS 21%bv 21) by first [unfold acallee_saved; lia | apply bv_eq; reflexivity | cbn; tauto]. exact R21.
  + rewrite (HRS 22%bv 22) by first [unfold acallee_saved; lia | apply bv_eq; reflexivity | cbn; tauto]. exact R22.
  + rewrite (HRS 23%bv 23) by first [unfold acallee_saved; lia | apply bv_eq; reflexivity | cbn; tauto]. exact R23.
  + rewrite (HRS 24%bv 24) by first [unfold acallee_saved; lia | apply bv_eq; reflexivity | cbn; tauto]. exact R24.
  + rewrite (HRS 25%bv 25) by first [unfold acallee_saved; lia | apply bv_eq; reflexivity | cbn; tauto]. exact R25.
  + rewrite (HRS 26%bv 26) by first [unfold acallee_saved; lia | apply bv_eq; reflexivity | cbn; tauto]. exact R26.
  + rewrite (HRS 27%bv 27) by first [unfold acallee_saved; lia | apply bv_eq; reflexivity | cbn; tauto]. exact R27.
  + exact (s5d_slots_kept cx (rdW W mem) _ _ (s5d_L_bnd cx c m _) KSl HSL).
Qed.

End ed.
End fd.
End dd.

(* ================================== the segment: the five pieces composed ================================== *)
Section dz. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section fz.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
Section ez.
Variable B : asyms.
Variable MT : ameter_ops.
Variable snp_lo snp_hi : Z.
Variable snp_cr : list (Z * Z).
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis IMGS : s10_img.
Hypothesis BSYM : AF0m.SegBSyms B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis PRW : prog_rw SEGS B.
Hypothesis VOBJS : seg_val_objs.
Hypothesis SIGP : seg_sig_prog.
Hypothesis HPGS : forall a, inFP (ltoi_PG longlA) a ->
  Exists (in_zr a) (as_prog_static B) /\ in_img SEGS a.
Hypothesis HPG_RO : forall a, inFP (ltoi_PG longlA) a -> ~ in_roP SEGS RLO_A RHI_A a.
Hypothesis HPG_PTR : forall a p,
  ((exists i, (i < 5)%nat /\ a = wordsA + 8 * Z.of_nat i) \/
   (exists i, (i < pin_spec.CAT_N)%nat /\ a = pin_spec.row_addr catA i)) ->
  rdword (fun x => option_map (fun b : byte => bv_unsigned b) (seg_rom SEGS (Z_to_bv 64 x))) a = Some p ->
  p + 65536 <= longlA.
Hypothesis AMEMCPY : forall fx0 : YK11.FPState,
  @aintrin_realizes fx0 rc SEGS B OCpy (SIG SS___asan_memcpy).
Hypothesis AMEMSET : forall fx0 : YK11.FPState,
  @aintrin_realizes fx0 rc SEGS B OSet (SIG SS___asan_memset).
Hypothesis AFREE4 : forall fx0 : YK11.FPState, @afree04_rule fx0 rc SK SEGS B MT.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState,
  @RtPFSeg.seg_asnprintf_realizes fx0 rc SEGS B snp_lo snp_hi snp_cr
    (SIG SS___interceptor_trampoline_snprintf) gotwA guardA.
Hypothesis HSNP_LIT : forall x, In x LLVMFuzzerTestOneInput_c.LTOI_LITS ->
  snp_lo <= seg_litA_fz x /\ seg_litA_fz x + Z.of_nat (length x) + 1 <= gotwA.
Hypothesis HSNP_CR : Forall (fun r => snp_lo <= fst r /\ 0 <= snd r /\ fst r + snd r <= snp_hi) snp_cr.
Hypothesis HSNP_LO : 0 <= snp_lo.
Hypothesis HSNP_CEIL : snp_hi <= alloc_ceiling.
Hypothesis HSNP_FAKE : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> snp_hi <= ly_F ly.
Hypothesis HM_FILE : forall fx0 : YK11.FPState,
  @m_file_c.m_file_contract fx0 rc SK SEGS B (BASE + AF_m_file) STK_m_file RLO_A RHI_A seg_litA_fz
    wordsA rolesA catA gotwA guardA.
Hypothesis HPARSE_FILE : forall fx0 : YK11.FPState,
  @reac_segconf_parse_file_c.reac_segconf_parse_file_contract fx0 rc SK SEGS B
    (BASE + AF_reac_segconf_parse_file) STK_reac_segconf_parse_file RLO_A RHI_A seg_litA_rc catA gotwA guardA.

(* lt_seg_S05_stmt: the three pieces that a callee returns into are instantiated at every FP state (their
   sections are closed), the two that run at the segment's own FP state at the ambient one *)
Theorem lt_seg_S05 : lt_seg_S05_stmt B MT.
Proof.
unfold lt_seg_S05_stmt. intros f H208 H414.
assert (HCK : S5A_CK B MT f).
{ intros fx1. exact (@s5_tail fx1 rc SK PI B MT snp_lo snp_hi snp_cr MTL MTFL TL TLF IMGS BSYM ML PRW VOBJS SIGP
    HPGS HPG_RO HPG_PTR AMEMCPY AMEMSET AFREE4 ASNPRINTF HSNP_LIT HSNP_CR HSNP_LO HSNP_CEIL HSNP_FAKE
    HM_FILE HPARSE_FILE f H414). }
assert (HOTH : S5A_OTH B MT f).
{ intros fx1. exact (@s5_calls fx1 rc SK PI B MT snp_lo snp_hi snp_cr MTL MTFL TL TLF IMGS BSYM ML PRW VOBJS SIGP
    HPGS HPG_RO HPG_PTR AMEMCPY AMEMSET AFREE4 ASNPRINTF HSNP_LIT HSNP_CR HSNP_LO HSNP_CEIL HSNP_FAKE
    HM_FILE HPARSE_FILE f HCK). }
assert (HLST : S5A_LST B MT f).
{ intros fx1. exact (@s5_last fx1 rc SK PI B MT snp_lo snp_hi snp_cr MTL MTFL TL TLF IMGS BSYM ML PRW VOBJS SIGP
    HPGS HPG_RO HPG_PTR AMEMCPY AMEMSET AFREE4 ASNPRINTF HSNP_LIT HSNP_CR HSNP_LO HSNP_CEIL HSNP_FAKE
    HM_FILE HPARSE_FILE f H208). }
exact (@s5_head fx rc SK PI B MT snp_lo snp_hi snp_cr MTL MTFL TL TLF IMGS BSYM ML PRW VOBJS SIGP
  HPGS HPG_RO HPG_PTR AMEMCPY AMEMSET AFREE4 ASNPRINTF HSNP_LIT HSNP_CR HSNP_LO HSNP_CEIL HSNP_FAKE
  HM_FILE HPARSE_FILE f
  (@s5_label fx rc SK PI B MT snp_lo snp_hi snp_cr MTL MTFL TL TLF IMGS BSYM ML PRW VOBJS SIGP
     HPGS HPG_RO HPG_PTR AMEMCPY AMEMSET AFREE4 ASNPRINTF HSNP_LIT HSNP_CR HSNP_LO HSNP_CEIL HSNP_FAKE
     HM_FILE HPARSE_FILE f HOTH HLST)).
Qed.

End ez.
End fz.
End dz.
