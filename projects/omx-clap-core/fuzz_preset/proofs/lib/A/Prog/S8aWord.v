(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S8aNumE.v, with its module paths and module names changed; 815 of its 890 lines of code are new or changed and 1840 lines of the source are left out. *)
(* fuzz_preset, slice S8a EX-VALUE, image A' (#102 asan, 1be0f53d / unstripped twin bff8519b): PIECE 4 of the walk of
   ex_value (A 0x832a4), ev_word: 0x83494-0x834a0 ('f'), 0x83554-0x83564 ('n'), 0x83748-0x83764 ('t'), 17
   instructions, from P_KIND (S8aIface.v ev_at_kind) at EV_WORD_F / EV_WORD_N / EV_WORD_T, through `jal ex_word` with
   the literal "false" / "null" / "true", to P_EXIT (ev_to_exit). Also THE STATEMENTS of pieces 3 and 4
   (ev_string_spec, ev_word_spec; approved by the unit owner 05:04Z as sent) and the program-call kit both pieces use:
   ev_call_st (aj_call_xWF's symbolic-state premise at the journal's sp), ev_rod (fpre's read-only view at a call),
   ev_chain (the frame chain at a call), ev_mid_rt (ev_mid after a caller-window program call).
   Base (#102, 2026-10-29): the S8a of record commit 6d4ad7fbfc10 (ec3ecbdf6a65 + int102
   d7322b084da6, kit f97c8b2f046b, PRH_Base.v fdb45545469b). MOVED from the old-image proof of
   commit b8ea5a686a5 by a Theorem Labs lane's alreloc c4338d099cfb8025 plus hand fixes (relocation
   audit docs/S8A102-RELOC-AUDIT.md). RE-FIT to #102: the ledger's two new cells (ea_most / ea_own) and fpre's last
   conjunct frm_zero (FRM0-ENTRY), supplied at the ex_word call from ev_fx, as the S8a interface writer does at ex_string in
   S8aP7a. The caller-window call rule is the engine's YCbqGcallW.aj_call_xWF_d; ZSB_x is the engine's
   alx_zshadow_byte (AR_laws_x field 13); the frame chain at a call comes from ev_pre's prhex_ch_apart conjunct.
   RE-PROVED (2026-10-29): the ev_word of commit 9d7dd411769 is WITHDRAWN (the unit owner): it took
   WORDX = tex_word_specX, FALSE as stated then (v = 2 ^ 64 with a3 = 0 takes the NULL arm, and the post asked a store
   at q + 32 the binary never makes). The kit's tex_word_specX now asks `0 <= v /\ v + 4 <= 2 ^ 47` (PRH_FnEx.v);
   ev_word_call discharges it from the tree root's three homes (a heap block of Lam, a live fake frame, the real stack
   above the entry sp) by S8aDisp.ev_home_bound, which bounds each home by 2 ^ 47 from LAWS alone.
   MEMNORM (S8aIface.v: ev_pre's and ev_mid's last conjunct): every runner segment keeps `YAkMemnorm.memnorm SEGS mem`
   by YC1fPx's _inv runners at P := that predicate (laws YSRrMemnorm.srr_inv_laws_memnorm_k); the call keeps it by the
   text's m-form post (fpostWm's keep `memnorm mem -> memnorm mem'`); ev_mid_rt takes it at the new memory.
   HFHULL / HSTK64 (stand-ins at 9d7dd411769) are no longer hypotheses: ev_frame_hull / ev_stk64 derive them from
   AR_laws_x field 18 (alx_layout_ok, stk_aligned_x), as S8aEntry.v and pieces 7 + 8 do.
   EX-LIT-SHADOW (the literal's shadow at ex_word's call sites, the named gap PRH_FnEx.v:36-38) is CLOSED here: the
   stand-in LIT is DELETED and ev_lit_cstr proves it by a Theorem Labs lane's YGcallRoStr.ro_cstr_x with vm_compute witnesses
   at A' (ev_lit_img_A) and the image binding TS. The literal addresses are Listing_prog.v's (blob 7ed1529926bd)
   slots 1966 / 2014 / 2139 (PAddHi a1 a0 j (A_OBJ 2) 0x10f80 / 0x10fa0 / 0x10f60; PAImg_prog.v A_prog_obj 2 =
   0x10000).
   ADDRESS CHECK on the #102 image A', 2026-10-29 ~19:3xZ (this file's writer S8a102): twin
   the #102 pin A' unstripped twin fuzz_preset.asan (sha256 bff8519bbe3ea0e4),
   sha256 bff8519bbe3ea0e4d8edf35fa48015b5846960886633a77a5e9f86cb565bd590, read by a 90-line Python ELF64 reader
   (PT_LOAD bytes + .symtab; no disassembler): bytes at 0x20f60 = 'true\0' (.symtab .str, 32 B), 0x20f80 = 'false\0'
   (.str.1, 32 B), 0x20fa0 = 'null\0' (.str.2, 32 B); auipc/addi pairs 0x83494/0x83498 -> 0x20f80, 0x83554/0x83558
   -> 0x20fa0, 0x83748/0x8374c -> 0x20f60 (addi slots (pc - 0x815e0) / 4 = 1966 / 2014 / 2139); jal words 0x834d0 =
   0x365000ef -> 0x84034 = .symtab ex_string (1272 B), 0x8375c = 0x5d1000ef -> 0x8452c = .symtab ex_word (348 B);
   ex_value = 0x832a4 (3472 B). No address is taken from a *_c.v.
   Every conclusion is srealizes through SRr. No released plain or UBSan file is Required, no lemma of one cited.
   NUMERALS (rule 7): EV_* offsets and 0x4bc (LENGTH: pc - 0x832a4 on the bff8519b listing: 0x83760, after ex_word);
   0x10f60, 0x10f80, 0x10fa0 (DERIVED: the listing's object offsets of .str / .str.1 / .str.2 from A_OBJ 2); 256,
   272, 152, 248, 240, 8, 16, 32, 36, 40, 56, 4096 (LENGTH: frame, save-area slots, word, struct ex, tree node,
   page); 2 ^ 44, 2 ^ 47, 2 ^ 64 (DERIVED: shadow / stack / word bounds); 0, 1, 2 (WORD: PJ_NULL / PJ_FALSE /
   PJ_TRUE, ex_word's type argument); 102, 110, 116 (WORD: the bytes 'f', 'n', 't'); 2147450880, 268431360 (WORD:
   SHADOW_OFF and SHADOW_OFF / 8, ev_granule_64); 64, 576, 16384, 1048576 (DERIVED: the shadow granule of a 64-byte
   frame unit and fs_frame_off's terms, ev_frame_hull). No ADDRESS literal. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn
YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallHull.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YGcallMx YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require PjStruct ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog PAImg_prog PRH_Base PRH_Img PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S8aIface S8aModel S8aDisp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Reader AF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require S1ImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YSRrMemnorm YGcallRoStr.
(* the word-read lemma rdword_of_val_mem (cgif donor), cited by name: YCem builds on this base (log
   the internal file build-20261029T170422Z.log); the flagged copy ev_rdword_of_vm of 9d7dd411769 is deleted. Nothing
   else of YCem / YCeh is cited (no image-B fact). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* ======== THE STATEMENTS OF PIECES 3 AND 4 (S8aIface.v's Section c context; the shape of ev_number_spec) ======== *)
Section stmt. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg}
  {RL : PrhRoomLive}.
Context {L : ptable asym} {PA : PAImg L}.
Local Notation segs := pa_segs.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.

(* piece 3, ev_string (0x834cc-0x83550, 0x83cb0-0x83cb4, report arms 0x83e90-0x83ea0, 0x83ebc-0x83ec8,
   0x8400c-0x84014): from P_KIND with the quote at EV_STR, through ex_string, v->type and strcmp, to P_EXIT. *)
Definition ev_string_spec : Prop :=
  forall a fxc W regs mem md ly S Hp k i1 c,
  ev_pre (fx := fx) B ARx a -> ev_fx (fx := fx) fxc -> ev_at_kind B ARx SK a W regs mem md ly S Hp k i1 c -> c = 34 ->
  SRr segs W (ev_cfg fxc regs EV_STR mem md) (ev_to_exit (fx := fx) B ARx SK a).

(* piece 4, ev_word (0x83494-0x834a0, 0x83554-0x83564, 0x83748-0x83764): from P_KIND with 'f' / 'n' / 't' at
   EV_WORD_F / EV_WORD_N / EV_WORD_T, through ex_word with "false" / "null" / "true", to P_EXIT. *)
Definition ev_word_spec : Prop :=
  forall a fxc W regs mem md ly S Hp k i1 c off,
  ev_pre (fx := fx) B ARx a -> ev_fx (fx := fx) fxc -> ev_at_kind B ARx SK a W regs mem md ly S Hp k i1 c ->
  (c = 102 /\ off = EV_WORD_F) \/ (c = 110 /\ off = EV_WORD_N) \/ (c = 116 /\ off = EV_WORD_T) ->
  SRr segs W (ev_cfg fxc regs off mem md) (ev_to_exit (fx := fx) B ARx SK a).
End stmt.

(* ---- the return site of `jal ex_word` (LENGTH, offset from ex_value's entry) ---- *)
Definition EV_WRET : Z := 0x4bc.   (* 0x83760: `mv s11, a0` *)

(* ---- the word cases: the byte, the cut, ex_word's type argument, the literal's offset from A_OBJ 2, the word,
   the tree read ---- *)
Definition ev_wcase (c off ty lo : Z) (wl : list Z) (u : PjTree.jv) : Prop :=
  (c = 116 /\ off = EV_WORD_T /\ ty = 2 /\ lo = 0x10f60 /\ wl = PjGrammar.w_true /\ u = PjTree.JTrue) \/
  (c = 102 /\ off = EV_WORD_F /\ ty = 1 /\ lo = 0x10f80 /\ wl = PjGrammar.w_false /\ u = PjTree.JFalse) \/
  (c = 110 /\ off = EV_WORD_N /\ ty = 0 /\ lo = 0x10fa0 /\ wl = PjGrammar.w_null /\ u = PjTree.JNull).

(* ---- H1: a symbolic state for aj_call_xWF's premise at the journal's sp (generic; the engine's own state has
   atom 2 = the body's sp, while ev_mid's journal sits at sp0 + d) ---- *)
Lemma ev_call_st : forall (fxc : YK11.FPState) (segs : list Segment) (H : word -> bool) regs pc mem sp0 o,
  0 <= sp0 < 2 ^ 64 -> getr regs 2 = Z_to_bv 64 (sp0 + o) ->
  exists E ss, st_ok (fx := fxc) segs E ss (restrict H (@YK11.mkst fxc regs (Z_to_bv 64 pc) mem (YK11.seg_rom segs))) /\
    ss_resv ss = None /\ ss_pc ss = pc /\ getr regs 2 = sv_denot E (SOff 2 o) /\ ew E 2 = Z_to_bv 64 sp0.
Proof.
intros fxc segs H regs pc mem sp0 o Hsp0 Hr2.
set (f := fun i : nat => SLit (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat i))))).
set (lits := map f (seq 0 32)).
exists (mkEnv (fun n => if Nat.eqb n 2 then Z_to_bv 64 sp0 else Z_to_bv 64 0) (fun _ => [])).
exists (mkSS pc (sr_set lits 2%bv (SOff 2 o)) [] None (mkFacts [] [] [])).
assert (Hden : sv_denot (mkEnv (fun n => if Nat.eqb n 2 then Z_to_bv 64 sp0 else Z_to_bv 64 0) (fun _ => [])) (SOff 2 o) =
  getr regs 2).
{ apply bv_eq. rewrite denot_SOff. cbn [ew Nat.eqb]. rewrite unsigned_lit_small by lia. rewrite Hr2.
  rewrite Z_to_bv_unsigned. reflexivity. }
split; [|split; [reflexivity|split; [reflexivity|split; [symmetry; exact Hden | reflexivity]]]].
unfold st_ok. cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem restrict YK11.mkst
  ss_pc ss_regs ss_mem ss_resv ss_facts resv_denot].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [reflexivity|].
split.
- intros r. destruct (decide (r = 2%bv)) as [->|Hne].
  + rewrite sr_get_set_same by reflexivity. symmetry. exact Hden.
  + rewrite sr_get_set_other by exact Hne. unfold sr_get.
    destruct (bv_eqb r 0) eqn:E0.
    * apply reg_eqb_eq in E0. subst r. unfold getr. reflexivity.
    * unfold lits. pose proof (bv_unsigned_in_range _ r) as Hrr. unfold bv_modulus in Hrr. cbn in Hrr.
      assert (Hi : (ridx r < 32)%nat) by (unfold ridx; lia).
      rewrite (nth_indep (map f (seq 0 32)) (SLit 0) (f 0%nat)) by (rewrite length_map, length_seq; exact Hi).
      rewrite map_nth, seq_nth by exact Hi. unfold f. cbn [sv_denot Nat.add].
      unfold ridx. rewrite Z2Nat.id by lia. rewrite !Z_to_bv_bv_unsigned. reflexivity.
- split; [split; [reflexivity | split; [constructor | exact I]]|].
  split; [exact I | split; exact I].
Qed.

(* ---- the tree root's header (PRH_Reader.pj_nodeR): its type at p (a u32), p 8-aligned, the str field at p + 16, and
   for a string node the C string str points to (one block of the footprint) ---- *)
Lemma ev_hdrR : forall segs m lblk p t D, PRH_Reader.pj_nodeR segs m lblk p t D ->
  exists str, PRH_Reader.rd_u32 segs m p (PjTree.tag t) /\ p mod 8 = 0 /\ PRH_Reader.rd_u64 segs m (p + 16) str /\
  (forall s, t = PjTree.JStr s -> exists k, PRH_Reader.pj_cstrR segs m lblk str k s /\ D = [(str, k)]).
Proof.
intros segs m lblk p t D H.
destruct t; cbn [PRH_Reader.pj_nodeR] in H;
  destruct H as (_ & _ & num & str & kids & keys & n & cap & (Hrw & Hty & _ & Hstr & _) & Hm);
  exists str; (split; [exact Hty|]); (split; [exact (proj1 Hrw)|]); (split; [exact Hstr|]);
  intros s0 Es; try discriminate Es.
injection Es as Es. subst s0. destruct Hm as (_ & _ & _ & _ & k & Hk & ED). exists k. split; [exact Hk | exact ED].
Qed.

Section w.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
#[local] Notation PIA := prh_img_A.
#[local] Notation PA := (@PI_prog_A rc).
#[local] Notation PL := PL_prog_A.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation VAL := (@pa_val _ A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
#[local] Notation PST := (prh_pst (PI := PIA)).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Context {hl : Z}.  (* AR_laws_x's head length (YCbqG.v), implicit: inferred from LAWS *)
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
(* the real stack's shadow bytes read 0 (S8aDisp's ZSB_x text = the engine's alx_zshadow_byte, AR_laws_x field 13) *)
Lemma ZSB_x : forall ly S Hp W mem md a, ARx ly S Hp W mem md -> ly_stk_lo ly <= a < ly_stk_hi ly ->
  aview SEGS (w_H W) mem (SHADOW_OFF + a / 8) = Some 0.
Proof. exact (alx_zshadow_byte SEGS B ARx LAWS). Qed.
(* STAND-IN, Lam-block home and the text / scratch blocks: exactly AR_shadow_law_cf's text (YG0dcf.v:290) over ARx (=
   S8aNumber.v's HSHD, lane E's CUTFIX_shadow_hd): the shadow of a live block past its hidden head and the hull of the
   whole block. DISCHARGE at the preset instance: AR_shadow_law_ok_cf (YG0sshcf.v:160, core 074d9f39628f). The
   engine's alx_shadow (field 11) / alx_hshadow (field 14) do not give it for a generic hl. *)
Hypothesis HSHD : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) ->
  block_shadow (aview SEGS (w_H W) mem) SHADOW_OFF (p + hd_skip Hp p) (req_size n - hd_skip Hp p) /\
  shadow_hull_vis (aview SEGS (w_H W) mem) p (req_size n).
(* ---- the two hull facts the walk took as HFHULL / HSTK64 at 9d7dd411769, DERIVED here from AR_laws_x field 18
   (alx_layout_ok, YCbqG.v) through named projections: COPIED (statements and proofs) from S8aEntry.v eve_granule_64 /
   eve_stk64 / eve_fs_cid / eve_frame_hull (S8aEntry's LAWS fixes the head length at cf_head and this file's is generic;
   the proofs never read it, so they are copied, not cited). Pieces 7 + 8 dropped the same two hypotheses the same way
   (S8aItemsTop.v :93, commit f2bdcc4ec76). The real stack's top is 64-aligned
   (stk_aligned_x); a live fake frame of 56 bytes or more is 64-aligned (layout_ok's lo_F_al), so its shadow hull is
   its own fs_frame_bytes cid / 8 shadow bytes, present by field 3 (alx_frames). ---- *)
Lemma ev_granule_64 : forall x, shadow_addr x / 8 * 8 = SHADOW_OFF + x / 64 * 8.
Proof.
intro x. unfold shadow_addr, SHADOW_OFF.
replace (2147450880 + x / 8) with (268431360 * 8 + x / 8) by lia.
rewrite Z.div_add_l by lia. rewrite Z.div_div by lia. change (8 * 8) with 64. lia.
Qed.
Lemma ev_stk64 : forall ly S Hp (W : world SEGS) mem md, ARx ly S Hp W mem md -> ly_stk_hi ly mod 64 = 0.
Proof. intros ly S Hp W mem md HAR. exact (proj2 (stk_aligned_x SEGS B ARx LAWS ly S Hp W mem md HAR)). Qed.
Lemma ev_fs_cid : forall c, 56 <= fs_frame_bytes c -> 0 <= c.
Proof.
intros c H. unfold fs_frame_bytes in *. destruct (Z.le_gt_cases 0 c) as [Hc|Hc]; [exact Hc|].
exfalso. assert (En : c = - (- c)) by lia. remember (- c) as n eqn:Hn. rewrite En in H.
rewrite Z.shiftl_div_pow2 in H by lia. rewrite ?Z.opp_involutive in H.
assert (H2 : 2 <= 2 ^ n).
{ replace 2 with (2 ^ 1) at 1 by reflexivity. apply Z.pow_le_mono_r; lia. }
assert (H3 : 64 / 2 ^ n <= 64 / 2) by (apply Z.div_le_compat_l; lia).
change (64 / 2) with 32 in H3. pose proof (Z.le_trans _ _ _ H H3) as H5. apply H5. reflexivity.
Qed.
Lemma ev_frame_hull : forall ly S Hp (W : world SEGS) mem md cid pos,
  ARx ly S Hp W mem md -> In (cid, pos) (frames S) -> 56 <= fs_frame_bytes cid ->
  shadow_hull_vis (aview SEGS (w_H W) mem) (frame_addr ly cid pos) (fs_frame_bytes cid).
Proof.
intros ly S Hp W mem md cid pos HAR Hin H56.
destruct (alx_frames SEGS B ARx LAWS ly S Hp W mem md cid pos HAR Hin) as (_ & _ & _ & HSP).
pose proof (lo_F_al _ (alx_layout_ok SEGS B ARx LAWS ly S Hp W mem md HAR)) as HF. unfold page_aligned in HF.
pose proof (ev_fs_cid cid H56) as Hc.
pose proof (Z.pow_pos_nonneg 2 cid ltac:(lia) Hc) as Ht0.
assert (Hfs : fs_frame_bytes cid = 64 * 2 ^ cid) by (unfold fs_frame_bytes; rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
assert (Hfa : frame_addr ly cid pos = 64 * (ly_F ly / 4096 * 64 + 576 + cid * 16384 + pos * 2 ^ cid)).
{ unfold frame_addr, fs_frame_off, kFakeFramesOff, kStackSizeLog. change (Z.shiftl 1 20) with 1048576. rewrite Hfs.
  pose proof (Z.div_mod (ly_F ly) 4096 ltac:(lia)) as D. rewrite HF, Z.add_0_r in D.
  set (fq := ly_F ly / 4096) in D |- *. rewrite D. ring. }
set (u := ly_F ly / 4096 * 64 + 576 + cid * 16384 + pos * 2 ^ cid) in Hfa.
set (t := 2 ^ cid) in *.
assert (Hsh : shadow_addr (frame_addr ly cid pos) = SHADOW_OFF + u * 8).
{ unfold shadow_addr. rewrite Hfa. replace (64 * u) with ((u * 8) * 8) by ring. rewrite Z.div_mul by lia. reflexivity. }
assert (Hf8 : fs_frame_bytes cid / 8 = t * 8).
{ rewrite Hfs. replace (64 * t) with ((t * 8) * 8) by ring. rewrite Z.div_mul by lia. reflexivity. }
intros s Hs. rewrite !ev_granule_64 in Hs. rewrite Hfa, Hfs in Hs.
replace (64 * u) with (u * 64) in Hs by ring. rewrite Z.div_mul in Hs by lia.
replace (u * 64 + 64 * t - 1) with ((u + t - 1) * 64 + 63) in Hs by ring.
rewrite Z.div_add_l in Hs by lia. change (63 / 64) with 0 in Hs.
destruct (HSP (s - shadow_addr (frame_addr ly cid pos)) ltac:(rewrite Hf8, Hsh; lia)) as [Hps _].
replace (shadow_addr (frame_addr ly cid pos) + (s - shadow_addr (frame_addr ly cid pos))) with s in Hps by lia.
exact (aview_some_of_apresent SEGS _ _ _ Hps).
Qed.
#[local] Notation PRE := (ev_pre (fx := fx) (PI := PIA) (L := A_prog_listing) (PA := PA) B ARx).
#[local] Notation MID := (ev_mid (PI := PIA) (L := A_prog_listing) (PA := PA) B ARx SK).
#[local] Notation REGS := (ev_regs (L := A_prog_listing) (PA := PA)).
#[local] Notation AT_KIND := (ev_at_kind (PI := PIA) (L := A_prog_listing) (PA := PA) B ARx SK).
#[local] Notation AT_EXIT := (ev_at_exit (PI := PIA) (L := A_prog_listing) (PA := PA) B ARx SK).
#[local] Notation TO_EXIT := (ev_to_exit (fx := fx) (PI := PIA) (L := A_prog_listing) (PA := PA) B ARx SK).
#[local] Notation CFG := (ev_cfg (L := A_prog_listing) (PA := PA)).
#[local] Notation FXOK := (ev_fx (fx := fx)).
#[local] Notation AJ := (ajournal_x (SK := SK) SEGS B PST ARx).
#[local] Notation STKa a := (ea_STK (PI := PIA) (L := A_prog_listing) (PA := PA) a).
#[local] Notation sp0a a := (ea_sp0 (L := A_prog_listing) (PA := PA) a).
#[local] Notation S1a a := (ea_S1 (L := A_prog_listing) (PA := PA) a).
#[local] Notation SAa a := (ea_SA (L := A_prog_listing) (PA := PA) a).
#[local] Notation fra a := (ea_fr (L := A_prog_listing) (PA := PA) a).
#[local] Notation FPa a := (ea_FP (L := A_prog_listing) (PA := PA) a).
#[local] Notation lena a := (ea_len (L := A_prog_listing) (PA := PA) a).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* STAND-IN: the ex_word walk (the kit's text tex_word_specX, PRH_FnEx.v; owner the unit owner's S8b lane), at every float
   state (ex_word touches none; the unit owner ruled the forall fx1 form, Main 05:4xZ). Since kit old-pin bd0d3c3a486b
   the text asks `0 <= v /\ v + 4 <= 2 ^ 47` (the fix of its v = 2 ^ 64 counterexample); ev_word_call discharges it. *)
Hypothesis WORDX : forall fx1, tex_word_specX (fx := fx1) (PI := PIA) (L := A_prog_listing) (PA := PA) B ARx SK.
(* OWNER the final image instance (AD2l.v TfibB_syms, Qed): image A's symbol record (AF0m.v TfibSyms), the image
   premise S8aEntry.v takes as TS. Here it gives B's owned statics, errno, zero-shadow ranges and const cells, which
   the literals' discharge reads (ev_lit_img). *)
Hypothesis TS : AF0m.TfibSyms B.
(* THE LITERALS "true" / "false" / "null" that ex_value passes to ex_word (A' 0x20f60 / 0x20f80 / 0x20fa0 =
   VAL (A_OBJ 2) + 0x10f60 / 0x10f80 / 0x10fa0, checked on the twin, see the header) are valid C strings at every
   ARx state that has fpre's read-only view. This was the stand-in LIT (EX-LIT-SHADOW, PRH_FnEx.v:36-38), which is
   now DELETED. The proof is a Theorem Labs lane's engine lemma YGcallRoStr.ro_cstr_x (commit
   9747e78ff620, blob 570a4a7a3251). Its premises: AR_laws_x (LAWS), ARx, arodata_okP (ev_rod), and the image
   premise ro_str_img. ro_str_img is DECIDED at image A' by ro_str_check over the instance's tables (ev_lit_img_A,
   vm_compute) and applied at B by ro_str_check_ok through TS (ev_lit_img). The tables' const cells are
   AF0m.Tfib_const_shadow, the layout-free tail of Tfib_const. *)
Lemma ev_lit_img_A :
  YGcallRoStr.ro_str_check SEGS AF0m.Tfib_const_shadow AF0m.Tfib_zero_shadow AF0m.Tfib_owned_static AF0m.TFIB_ERRNO
    (VAL (A_OBJ 2) + 0x10f60) PjGrammar.w_true = true /\
  YGcallRoStr.ro_str_check SEGS AF0m.Tfib_const_shadow AF0m.Tfib_zero_shadow AF0m.Tfib_owned_static AF0m.TFIB_ERRNO
    (VAL (A_OBJ 2) + 0x10f80) PjGrammar.w_false = true /\
  YGcallRoStr.ro_str_check SEGS AF0m.Tfib_const_shadow AF0m.Tfib_zero_shadow AF0m.Tfib_owned_static AF0m.TFIB_ERRNO
    (VAL (A_OBJ 2) + 0x10fa0) PjGrammar.w_null = true.
Proof. split; [|split]; vm_compute; reflexivity. Qed.
Lemma ev_lit_img : forall p l,
  YGcallRoStr.ro_str_check SEGS AF0m.Tfib_const_shadow AF0m.Tfib_zero_shadow AF0m.Tfib_owned_static AF0m.TFIB_ERRNO
    p l = true ->
  YGcallRoStr.ro_str_img SEGS B p l.
Proof.
intros p l H.
apply (YGcallRoStr.ro_str_check_ok SEGS _ _ _ _ B p l H (AF0m.ts_owned _ TS) (AF0m.ts_errno _ TS) (AF0m.ts_zsh _ TS)).
intros ly c Hc. rewrite (AF0m.ts_const _ TS). unfold AF0m.Tfib_const.
apply in_or_app. right. apply in_or_app. right. exact Hc.
Qed.
Lemma ev_lit_cstr : forall ly S Hp W mem md p l, ARx ly S Hp W mem md ->
  arodata_okP SEGS (pa_relro_lo (PAImg := PA)) (pa_relro_hi (PAImg := PA)) B (aview SEGS (w_H W) mem) ->
  YGcallRoStr.ro_str_check SEGS AF0m.Tfib_const_shadow AF0m.Tfib_zero_shadow AF0m.Tfib_owned_static AF0m.TFIB_ERRNO
    p l = true ->
  cstr_ok (PA := PA) W mem p l.
Proof.
intros ly S Hp W mem md p l HAR HRO HC.
(* ro_cstr_x states cstr_ok's conjuncts with the pre-SRC-CEIL ceiling `p + len + 8 <= alloc_ceiling`; the kit's
   cstr_ok (PRH_Base.v) now asks `p + len + 1`, which it implies. Every other conjunct is cstr_ok's verbatim: the first
   is `cstr W mem p l` itself (garr8 over l ++ [0] and no NUL in l, with rdW W mem = mrestrict (w_H W) mem). *)
destruct (YGcallRoStr.ro_cstr_x SEGS B ARx LAWS _ _ p l ly S Hp W mem md HAR HRO (ev_lit_img p l HC))
  as (Hcs & H4096 & Hceil8 & Hrest).
unfold cstr_ok. split; [exact Hcs|]. split; [exact H4096|]. split; [lia | exact Hrest].
Qed.

(* ---- small facts ---- *)
Lemma ev_raw_of_aview : forall (H H' : word -> bool) (m m' : word -> option byte) z,
  0 <= z < 2 ^ 64 -> ~ in_img SEGS z -> aview SEGS H' m' z = aview SEGS H m z ->
  mrestrict H' m' (Z_to_bv 64 z) = mrestrict H m (Z_to_bv 64 z).
Proof.
intros H H' m m' z Hz Hn E. apply mbyte_of_aview in E. unfold mbyte in E.
rewrite (seg_rom_none SEGS z Hz Hn) in E.
destruct (mrestrict H' m' (Z_to_bv 64 z)), (mrestrict H m (Z_to_bv 64 z)); congruence.
Qed.

(* the FP of the activation: the scratch (in an allocator block, below the ceiling) and three cells of [q, q + 40) *)
Lemma ev_inFP : forall a z, inFP (FPa a) z ->
  (ea_scr a <= z < ea_scr a + lena a + 1) \/ (ea_q a <= z < ea_q a + 40).
Proof.
intros a z (r & Hin & Hr). unfold ea_FP in Hin. cbn [In] in Hin.
destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hr; [left | right | right | right]; lia.
Qed.

(* ---- ev_rod: fpre's read-only view at any mid state (the entry's, kept by the journal's image clause; no static
   byte of prh_img_A is read-only: S1ImgA.pst_not_ro_A) ---- *)
Lemma ev_rod : forall a ly S Hp W mem md k p dep dl, PRE a -> MID a ly S Hp W mem md k p dep dl ->
  arodata_okP SEGS (pa_relro_lo (PAImg := PA)) (pa_relro_hi (PAImg := PA)) B (aview SEGS (w_H W) mem).
Proof.
intros a ly S Hp W mem md k p dep dl HP HM z Hro Ho He.
pose proof (ev_arith B ARx a HP) as (Hal16 & Hceil & Hslo & Hdtop & Htop & H47 & Hd0 & Hd16 & Hspq & Hq40 & Hqm & EK & HS1m &
  HS1 & ESA & Hx4096 & Hxc & Hi0 & Hlen & Hdep & Hdl).
pose proof HP as HP0. unfold ev_pre in HP0. cbv zeta in HP0.
destruct HP0 as ((HAF0 & HROD & _) & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hwd0 & Hinbs0 & _).
destruct HM as (HJ & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & Him & _).
rewrite (Him z).
- exact (HROD z Hro Ho He).
- destruct Hro as [(s & Hs & _ & Hr) | Hrr]; [exists s; split; [exact Hs | exact Hr]|].
  exact (pa_relro_img z Hrr).
- exact Ho.
- exact He.
- intros Hpst. exact (S1ImgA.pst_not_ro_A z Hpst Hro).
- intros (r & Hin & H0). unfold ea_FP in Hin. cbn [In] in Hin.
  destruct Hinbs0 as (b & m & Hbm & Hb & Hbe & _).
  destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ (proj1 HAF0) Hbm) as (_ & H4096 & _).
  destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in H0; lia.
Qed.

(* ---- ev_chain: the frame chain at a call from the body (sp = the body's sp, s0 = the entry sp): ex_value's own
   record (the save area's ra and s0) on top of the entry chain, which the struct ex cells do not disturb (ev_pre's
   prhex_ch_apart) ---- *)
Lemma ev_chain : forall a ly S Hp W mem md k p dep dl spc, PRE a -> MID a ly S Hp W mem md k p dep dl ->
  spc + 16 <= sp0a a ->
  exists ch1, achain ly (aview SEGS (w_H W) mem) spc (sp0a a) ch1.
Proof.
intros a ly S Hp W mem md k p dep dl spc HP HM Hspc.
pose proof (ev_arith B ARx a HP) as (Hal16 & Hceil & Hslo & Hdtop & Htop & H47 & Hd0 & Hd16 & Hspq & Hq40 & Hqm & EK & HS1m &
  HS1 & ESA & Hx4096 & Hxc & Hi0 & Hlen & Hdep & Hdl).
pose proof (asan_consts (rc := rc)) as (C1 & _).
pose proof HP as HP0. unfold ev_pre in HP0. cbv zeta in HP0.
destruct HP0 as ((HAF0 & HROD & _) & _ & _ & _ & _ & _ & _ & HCH & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hwd0 & _).
pose proof Hwd0 as (_ & Hwdc & _).
destruct HAF0 as (HAR0 & Hra0 & Hra40 & _ & _ & _ & _ & Hch0 & _).
destruct HM as (HJ & Hwin & _ & _ & _ & _ & _ & _ & _ & Hsav & _).
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & Hhi & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
unfold ev_saved in Hsav. rewrite Forall_forall in Hsav.
pose proof (Hsav (248, 1) ltac:(cbv; tauto)) as Hw1. pose proof (Hsav (240, 8) ltac:(cbv; tauto)) as Hw8.
cbn [fst snd] in Hw1, Hw8.
replace (SAa a + 248) with (sp0a a - 8) in Hw1 by (unfold ea_SA in *; lia).
replace (SAa a + 240) with (sp0a a - 16) in Hw8 by (unfold ea_SA in *; lia).
assert (H8 : sp0a a mod 8 = 0).
{ pose proof (Z.div_mod (sp0a a) 16 ltac:(lia)). pose proof (Z.div_mod (sp0a a) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (sp0a a) 8 ltac:(lia)). lia. }
destruct (Z_le_gt_dec (ly_top ly - 16) (sp0a a)) as [Hbad|Hgood].
- exists []. left. split; [right; left; exact Hbad | reflexivity].
- exists ((sp0a a, raZ (ea_regs a), s0Z (ea_regs a)) :: ea_ch a). right.
  split; [lia|]. split; [lia|]. split; [exact H8|].
  (* the view through which prhex_ch_apart reads the entry chain: the current bytes inside the struct, the entry's
     outside *)
  set (rd' := fun z => if (ea_q a <=? z) && (z <? ea_q a + 40) then aview SEGS (w_H W) mem z
                       else aview SEGS (w_H (ea_W a)) (ea_mem a) z).
  assert (Hrd' : forall z, ~ (ea_q a <= z < ea_q a + 40) -> rd' z = aview SEGS (w_H (ea_W a)) (ea_mem a) z).
  { intros z Hz. unfold rd'. destruct (ea_q a <=? z) eqn:E1, (z <? ea_q a + 40) eqn:E2; try reflexivity.
    apply Z.leb_le in E1. apply Z.ltb_lt in E2. exfalso. exact (Hz (conj E1 E2)). }
  pose proof (HCH rd' Hrd') as Hach. change (spZ (ea_regs a)) with (sp0a a) in Hach.
  (* above the entry sp the current view and rd' agree *)
  assert (Hag : forall z, sp0a a <= z < 2 ^ 64 -> aview SEGS (w_H W) mem z = rd' z).
  { intros z Hz. unfold rd'.
    destruct (ea_q a <=? z) eqn:E1, (z <? ea_q a + 40) eqn:E2; try reflexivity; cbn [andb];
    try apply Z.leb_gt in E1; try apply Z.ltb_ge in E2; try apply Z.leb_le in E1; try apply Z.ltb_lt in E2;
    (destruct (Z_lt_le_dec z (sp0a a + ea_d a)) as [Hlt|Hge];
      [ apply Hwin; [lia|]; intros HF; apply ev_inFP in HF; destruct HF as [HF|HF]; unfold ea_len in *; lia
      | apply Hhi; lia ]). }
  split.
  + cbn [fpchain]. split; [reflexivity|]. split; [exact H8|].
    pose proof (bv_unsigned_in_range _ (getr (ea_regs a) 1)) as Hr1.
    pose proof (bv_unsigned_in_range _ (getr (ea_regs a) 8)) as Hr8.
    unfold bv_modulus in Hr1, Hr8. change (2 ^ Z.of_N 64) with (2 ^ 64) in Hr1, Hr8.
    split; [exact (YCem.rdword_of_val_mem SEGS (w_H W) mem _ _ Hw1 Hr1)|].
    split; [exact (YCem.rdword_of_val_mem SEGS (w_H W) mem _ _ Hw8 Hr8)|].
    split; [exact Hra40|].
    destruct (bad_next (sp0a a) (ly_top ly) (s0Z (ea_regs a))) eqn:Eb.
    * destruct Hach as [[_ Hnil] | (Hge & Hlt & Hm8 & _ & _)]; [exact Hnil|].
      exfalso. unfold bad_next in Eb. rewrite Etop in Eb.
      apply orb_true_iff in Eb as [Eb1 | Eb2].
      { apply orb_true_iff in Eb1 as [Eb11 | Eb12]; [apply Z.leb_le in Eb11 | apply Z.leb_le in Eb12]; lia. }
      { apply negb_true_iff, Z.eqb_neq in Eb2. exact (Eb2 Hm8). }
    * unfold bad_next in Eb. rewrite Etop in Eb.
      apply orb_false_iff in Eb as [Eb1 Eb2]. apply orb_false_iff in Eb1 as [Eb11 Eb12].
      apply Z.leb_gt in Eb11. apply Z.leb_gt in Eb12. apply negb_false_iff, Z.eqb_eq in Eb2.
      destruct Hach as [[Hb _] | (Hge & Hlt & Hm8 & Hfp & _)].
      { exfalso. destruct Hb as [Hb | [Hb | Hb]]; lia. }
      rewrite Etop. apply (fpchain_ext (rdword rd')); [| lia | exact Hfp].
      intros z Hz1 Hz2. apply rdword_ext. intros kk Hk. apply Hag. lia.
  + constructor; [cbn [fst snd]; lia|].
    destruct Hach as [[_ ->] | (_ & _ & _ & _ & HF)]; [constructor|].
    eapply Forall_impl; [|exact HF]. intros r Hr. cbv beta in Hr |- *. lia.
Qed.

(* ---- block arithmetic: the hidden-head skip, req_size ---- *)
Lemma ev_req_ge : forall m, m <= req_size m.
Proof. intros m. unfold req_size. destruct (Z.eqb_spec m 0); lia. Qed.
Lemma ev_hd_rng : forall Hp b, 0 <= hd_skip Hp b <= cf_head.
Proof. intros Hp b. pose proof (@cf_head_nonneg cp). unfold hd_skip. destruct (existsb (Z.eqb b) Hp); lia. Qed.
Lemma ev_hd_le : forall Hp b x, b <= x -> (In b Hp -> b + cf_head <= x) -> b + hd_skip Hp b <= x.
Proof.
intros Hp b x H1 H2. unfold hd_skip. destruct (existsb (Z.eqb b) Hp) eqn:E; [|lia].
apply existsb_exists in E as (h & Hin & Eh). apply Z.eqb_eq in Eh. subst h. exact (H2 Hin).
Qed.

(* a sub-range of a visible hull is visible: COPIED (statement and proof) from lane E's S8aNumE.v eve_hull_sub
   (commit da73e1570f8), which no longer builds on this base *)
Lemma ev_hull_sub : forall (rd : reader) p mm d n, shadow_hull_vis rd p mm -> p <= d -> d + n <= p + mm -> 0 < n ->
  shadow_hull_vis rd d n.
Proof.
  intros rd p mm d n Hh Hpd Hdn Hn s Hs. apply Hh.
  pose proof (shadow_mono p d Hpd) as M1. pose proof (shadow_mono (d + n - 1) (p + mm - 1) ltac:(lia)) as M2.
  assert (R8 : forall u v, u <= v -> u / 8 * 8 <= v / 8 * 8)
    by (intros u v Huv; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
  pose proof (R8 _ _ M1). pose proof (R8 _ _ M2). lia.
Qed.

(* ---- the shadow of a byte range of a live block, at any state ARx holds (HSHD) ---- *)
Lemma ev_blk_shadow : forall ly S Hp W mem md b m x n, ARx ly S Hp W mem md -> In (b, m) (ablocks B ly S) ->
  b + hd_skip Hp b <= x -> x + n <= b + m -> 0 <= n ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF x n /\
  (0 < n -> shadow_hull_vis (aview SEGS (w_H W) mem) x n).
Proof.
intros ly S Hp W mem md b m x n HAR Hin H1 H2 Hn. destruct (HSHD ly S Hp W mem md b m HAR Hin) as [Hbs Hhv].
pose proof (ev_req_ge m). pose proof (ev_hd_rng Hp b).
split.
- apply (block_shadow_range _ _ (b + hd_skip Hp b) (req_size m - hd_skip Hp b)); [exact Hbs | lia | lia].
- intros Hn0. eapply ev_hull_sub; [exact Hhv | lia | lia | lia].
Qed.

(* a fake frame of a 56-byte node has a whole number of granules *)
Lemma ev_fb8 : forall cid, 56 <= fs_frame_bytes cid -> fs_frame_bytes cid mod 8 = 0.
Proof.
intros cid H. unfold fs_frame_bytes in *. destruct (Z_lt_le_dec cid 0) as [Hn|Hp].
- rewrite Z.shiftl_div_pow2 in H by lia.
  assert (2 <= 2 ^ (- cid)) by (change 2 with (2 ^ 1) at 1; apply Z.pow_le_mono_r; lia).
  assert (64 / 2 ^ (- cid) <= 64 / 2) by (apply Z.div_le_compat_l; lia). change (64 / 2) with 32 in *. lia.
- rewrite Z.shiftl_mul_pow2 by lia. replace (64 * 2 ^ cid) with ((8 * 2 ^ cid) * 8) by lia. apply Z.mod_mul. lia.
Qed.

(* ---- H2, ev_mid_rt: ev_mid after a caller-window PROGRAM call made from the body (sp = S1): the composed journal
   from the activation's entry (aj_call_xWF's first journal), the callee's journal from the call (its frames clause
   keeps the frame's flag word), the callee's window clause on [S1, sp0 + d) outside its FP (FP1, inside the
   activation's FP and apart from [q + 8, q + 32)), Hp / ablocks / ledger as the callee text states them, the two
   cursor cells the callee may write, and the memory normal after the call (the callee's m-form keep). The text, the
   scratch and a Lam tree node take their shadow from HSHD; a fake frame home keeps its shadow by the journal; the
   real stack by ZSB_x. ---- *)
Lemma ev_mid_rt : forall a ly S Hp W mem md k p dep dl ly2 S2 Hp2 W2 mem2 md2 k2 STK1 FP1 k1 p' dl',
  PRE a -> MID a ly S Hp W mem md k p dep dl ->
  AJ (STKa a + ea_d a) (sp0a a + ea_d a) (FPa a) (ea_ly a) (ea_S a) (ea_Hp a) (ea_W a) (ea_mem a) (ea_md a)
    [(1, ea_pos a)] ly2 S2 Hp2 W2 mem2 md2 k2 ->
  AJ STK1 (sp0a a + ea_d a) FP1 ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  (forall z, S1a a <= z < sp0a a + ea_d a -> ~ inFP FP1 z ->
     aview SEGS (w_H W2) mem2 z = aview SEGS (w_H W) mem z) ->
  (forall z, inFP FP1 z -> inFP (FPa a) z) -> (forall z, ea_q a + 8 <= z < ea_q a + 32 -> ~ inFP FP1 z) ->
  Hp2 = Hp -> ablocks B ly2 S2 = ablocks B ly S ->
  prh_ledger (PI := PIA) B ly2 S2 Hp2 W2 mem2 (ea_Lam a) (ea_peak a) (ea_cnt a) (ea_fail a) (ea_ran a) (ea_most a)
    (ea_own a) ->
  val_mem SEGS (rdW W2 mem2) (ea_q a) 8 p' -> val_mem SEGS (rdW W2 mem2) (ea_q a + 32) 4 dl' ->
  0 < lena a -> (room_live_cf S -> room_live_cf S2) -> PresetHullBudget.hull_used S S2 [] ->
  (forall rp_sm rp_x rp_os rp_i rp_H0 rp_hist,
     PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S ->
     PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S2) ->
  YAkMemnorm.memnorm SEGS mem2 ->
  MID a ly2 S2 Hp2 W2 mem2 md2 k2 p' dep dl'.
Proof.
intros a ly S Hp W mem md k p dep dl ly2 S2 Hp2 W2 mem2 md2 k2 STK1 FP1 k1 p' dl'
  HP HM HJ2 HJ1 HX HFP1 HFPq EHp2 Eab2 Hled2 Hq' Hdl' Hlen0 HRLc HHUc HRPc HMN2.
pose proof (ev_arith B ARx a HP) as (Hal16 & Hceil & Hslo & Hdtop & Htop & H47 & Hd0 & Hd16 & Hspq & Hq40 & Hqm & EK & HS1m &
  HS1 & ESA & Hx4096 & Hxc & Hi0 & Hlen & Hdep & Hdl).
pose proof (asan_consts (rc := rc)) as (C1 & C2 & C3 & C4 & C5).
pose proof (@cf_head_nonneg cp) as Hch.
pose proof HP as HP0. unfold ev_pre in HP0. cbv zeta in HP0.
destruct HP0 as ((HAF0 & HROD & _) & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsrc0 & Hinb0 & _ & _ & _ & _ & _ & Hwd0 & Hinbs0 &
  Hd1 & Hd2 & Htree0 & Hled0 & _).
specialize (Hinb0 Hlen0).
pose proof HAF0 as (HAR0 & _).
destruct HM as (HJ & Hwin & EHp & Eab & Hled & Hcur & Hsrc & Hwd & Htree & Hsav & Hflag & HRL & HRP & _).
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _).
pose proof Hly as (_ & _ & _ & _ & _ & EF & _ & _ & Etop & Eslo & Eshi & _).
pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfrk1 & _).
pose proof HJ2 as (HAR2 & Hly2 & _ & _ & _ & Hfrs2 & _ & _ & Hhi2 & Hbk2 & _ & Hfrk2 & _).
pose proof Hly2 as (_ & _ & _ & _ & _ & EF2 & _ & _ & Etop2 & Eslo2 & Eshi2 & _).
assert (Eab2' : ablocks B ly2 S2 = ablocks B (ea_ly a) (ea_S a)) by (rewrite Eab2; exact Eab).
assert (EHp2' : Hp2 = ea_Hp a) by (rewrite EHp2; exact EHp).
pose proof Hwd0 as (_ & Hwdc & _).
(* bytes the activation's FP names: the scratch (below the ceiling) and [q, q + 40) *)
assert (HnFP : forall z, (z < ea_scr a \/ ea_scr a + lena a + 1 <= z) -> ~ (ea_q a <= z < ea_q a + 40) -> ~ inFP (FPa a) z).
{ intros z Hz1 Hz2 HF. apply ev_inFP in HF. lia. }
(* WINDOW after the call, relative to the entry *)
assert (WIN2 : forall z, sp0a a <= z < sp0a a + ea_d a -> ~ inFP (FPa a) z ->
          aview SEGS (w_H W2) mem2 z = aview SEGS (w_H (ea_W a)) (ea_mem a) z).
{ intros z Hz Hn. rewrite (HX z ltac:(lia) ltac:(intros HF; exact (Hn (HFP1 z HF)))). exact (Hwin z Hz Hn). }
(* above the entry sp, outside the activation's FP *)
assert (KA : forall z, sp0a a <= z < 2 ^ 64 -> ~ inFP (FPa a) z ->
          aview SEGS (w_H W2) mem2 z = aview SEGS (w_H (ea_W a)) (ea_mem a) z).
{ intros z Hz Hn. destruct (Z_lt_le_dec z (sp0a a + ea_d a)) as [Hlt|Hge]; [exact (WIN2 z ltac:(lia) Hn)|].
  apply Hhi2; lia. }
(* a byte of a live entry block, outside the activation's FP *)
assert (KB : forall b m z, In (b, m) (ablocks B (ea_ly a) (ea_S a)) -> b <= z < b + req_size m -> ~ inFP (FPa a) z ->
          aview SEGS (w_H W2) mem2 z = aview SEGS (w_H (ea_W a)) (ea_mem a) z).
{ intros b m z Hin Hz Hn. replace z with (b + (z - b)) by lia.
  apply (Hbk2 b m (z - b) Hin); [rewrite Eab2'; exact Hin | lia | replace (b + (z - b)) with z by lia; exact Hn]. }
(* the byte-level transport of a value through aview equality *)
assert (VM : forall z n v, (forall kk, (kk < n)%nat -> aview SEGS (w_H W2) mem2 (z + Z.of_nat kk) = aview SEGS (w_H W) mem (z + Z.of_nat kk)) ->
          val_mem SEGS (rdW W mem) z n v -> val_mem SEGS (rdW W2 mem2) z n v).
{ intros z n v He Hv. eapply ev_vm_kept; [|exact Hv]. intros kk Hk. apply mbyte_of_aview. exact (He kk Hk). }
assert (VM0 : forall z n v, (forall kk, (kk < n)%nat -> aview SEGS (w_H W2) mem2 (z + Z.of_nat kk) = aview SEGS (w_H (ea_W a)) (ea_mem a) (z + Z.of_nat kk)) ->
          val_mem SEGS (rdW (ea_W a) (ea_mem a)) z n v -> val_mem SEGS (rdW W2 mem2) z n v).
{ intros z n v He Hv. eapply ev_vm_kept; [|exact Hv]. intros kk Hk. apply mbyte_of_aview. exact (He kk Hk). }
(* the struct ex cells outside FP1 *)
assert (HXq : forall z, ea_q a + 8 <= z < ea_q a + 32 -> aview SEGS (w_H W2) mem2 z = aview SEGS (w_H W) mem z)
  by (intros z Hz; apply HX; [lia | exact (HFPq z Hz)]).
split; [exact HJ2|].
split; [exact WIN2|].
split; [exact EHp2'|].
split; [exact Eab2'|].
split; [exact Hled2|].
split.
{ destruct Hcur as (Q1 & Q2 & Q3 & Q4 & Q5).
  split; [exact Hq'|].
  split; [apply (VM _ 8%nat _); [intros kk Hk; apply HXq; lia | exact Q2]|].
  split; [apply (VM _ 4%nat _); [intros kk Hk; apply HXq; lia | exact Q3]|].
  split; [apply (VM _ 8%nat _); [intros kk Hk; apply HXq; lia | exact Q4]|].
  exact Hdl'. }
(* the text, from the entry (its block is kept, its shadow is HSHD's) *)
destruct Hinb0 as (bt & mt & Hbt & Hbt1 & Hbt2 & Hbt3).
pose proof (ev_req_ge mt) as Hrt.
pose proof (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR0 Hbt) as (_ & Hbt4096 & Hbtc & _).
split.
{ destruct Hsrc0 as (Hg & H4 & Hc & Ham & Hra & Hhv). unfold ea_len in *.
  assert (HSH : range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF (ea_x0 a) (Z.of_nat (length (ea_x a))) /\
           (0 < Z.of_nat (length (ea_x a)) -> shadow_hull_vis (aview SEGS (w_H W2) mem2) (ea_x0 a) (Z.of_nat (length (ea_x a))))).
  { apply (ev_blk_shadow ly2 S2 Hp2 W2 mem2 md2 bt mt); [exact HAR2 | rewrite Eab2'; exact Hbt | | lia | lia].
    rewrite EHp2'. apply ev_hd_le; [lia | exact Hbt3]. }
  split; [|split; [exact H4 | split; [exact Hc | split; [exact Ham | exact HSH]]]].
  eapply ev_garr8_kept; [|exact Hg]. intros j Hj. apply mbyte_of_aview.
  apply (KB bt mt); [exact Hbt | lia | apply HnFP; lia]. }
(* the scratch: its block is live, so writable, not owned, and its shadow is HSHD's *)
destruct Hinbs0 as (bs & ms & Hbs & Hbs1 & Hbs2 & Hbs3).
pose proof (ev_req_ge ms) as Hrs.
split.
{ destruct Hwd as (W0' & W1' & W2' & W3' & W4' & W5'). unfold ea_len in *.
  assert (Hbs' : In (bs, ms) (ablocks B ly2 S2)) by (rewrite Eab2'; exact Hbs).
  pose proof (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR2 Hbs') as (_ & _ & _ & _ & Hpr & _).
  assert (HSH : range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF (ea_scr a) (Z.of_nat (length (ea_x a)) + 1) /\
           (0 < Z.of_nat (length (ea_x a)) + 1 ->
              shadow_hull_vis (aview SEGS (w_H W2) mem2) (ea_scr a) (Z.of_nat (length (ea_x a)) + 1))).
  { apply (ev_blk_shadow ly2 S2 Hp2 W2 mem2 md2 bs ms); [exact HAR2 | exact Hbs' | | lia | lia].
    rewrite EHp2'. apply ev_hd_le; [lia | exact Hbs3]. }
  split; [exact W0'|]. split; [exact W1'|]. split; [exact W2'|]. split; [|exact HSH].
  intros z Hz. destruct (W3' z Hz) as (_ & _ & Hns). destruct (Hpr z ltac:(lia)) as (Hzp & Hzo).
  split; [apply (apresent_writable SEGS); exact Hzp|]. split; [exact Hzo | exact Hns]. }
(* the tree, from the entry *)
split.
{ destruct Htree0 as [Hv0 | (Ht0 & HDpos & Hfoot)]; [left; exact Hv0|]. right.
  destruct Ht0 as (Hpj & Hhome & Hra0 & Hhv0).
  (* a byte of a Lam block: kept, not an image byte *)
  assert (LK : forall xb kb z, In (xb, kb) (ea_Lam a) -> xb <= z < xb + kb -> ~ inFP (FPa a) z ->
            aview SEGS (w_H W2) mem2 z = aview SEGS (w_H (ea_W a)) (ea_mem a) z /\ ~ in_img SEGS z /\ 0 <= z < 2 ^ 64).
  { intros xb kb z Hin Hz Hn. destruct Hled0 as (_ & _ & HF & _). rewrite Forall_forall in HF.
    destruct (HF _ Hin) as (Hk0 & Hab & _ & _ & _). cbn [fst snd] in Hk0, Hab.
    pose proof (ev_req_ge (kb + cf_head)).
    pose proof (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR0 Hab) as (_ & H4096 & Hbc & _).
    split; [apply (KB (xb - cf_head) (kb + cf_head)); [exact Hab | lia | exact Hn]|].
    split; [|lia].
    apply (alx_client_img SEGS B ARx LAWS _ _ _ _ _ _ z HAR0). left. exists (xb - cf_head), (kb + cf_head). split; [exact Hab | lia]. }
  (* every footprint byte is kept and lies outside the image *)
  assert (KF : forall z, PRH_Reader.pj_footR (ea_v a) (ea_D a) z ->
            aview SEGS (w_H W2) mem2 z = aview SEGS (w_H (ea_W a)) (ea_mem a) z /\ ~ in_img SEGS z /\ 0 <= z < 2 ^ 64).
  { intros z Hz. destruct (Hfoot z Hz) as (Hns & Hnq & Hnstk & _).
    assert (Hn : ~ inFP (FPa a) z) by (intros HF; apply ev_inFP in HF; tauto).
    destruct Hz as [Hroot | ((xb, kb) & HinD & Hh)].
    - destruct Hhome as [(b & m & HinL & Hb & Hm) | [(cid & pos & HinF & Hb & Hm) | (Hb & Hm)]].
      + exact (LK b m z HinL ltac:(lia) Hn).
      + destruct (frames_bounds_x SEGS B ARx LAWS _ _ _ _ _ _ cid pos HAR0 HinF) as (Hf0 & Hfc & _).
        split; [apply (Hfrk2 cid pos z HinF); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | exact Hn]|].
        split; [|lia].
        apply (alx_client_img SEGS B ARx LAWS _ _ _ _ _ _ z HAR0). right. left. exists cid, pos. split; [exact HinF | lia].
      + change (spZ (ea_regs a)) with (sp0a a) in Hb. split; [apply KA; [lia | exact Hn]|].
        split; [|lia]. intros Himg. pose proof (@pa_segs_low _ A_prog_listing PA z Himg). unfold kLowMemEnd in *. lia.
    - pose proof (ev_node_blocks SEGS _ _ _ _ _ Hpj xb kb HinD) as HL. unfold prh_lin in HL.
      unfold PRH_Reader.pj_holdsR in Hh. cbn [fst snd] in Hh. exact (LK xb kb z HL Hh Hn). }
  split; [|split; [|split]].
  - apply (PRH_Reader.pj_nodeR_frame SEGS (ea_t a) _ _ _ _ _ Hpj).
    intros x Hx. destruct (KF _ Hx) as (Hk & Hni & Hr).
    split; [apply mbyte_of_aview; exact Hk|].
    pose proof (ev_raw_of_aview _ _ _ _ _ Hr Hni Hk) as E.
    intros Hwa. unfold writable_at, LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview in *. rewrite E. exact Hwa.
  - destruct Hhome as [Hh | [(cid & pos & HinF & Hb & Hm) | (Hb & Hm)]]; [left; exact Hh| |].
    + right; left. exists cid, pos. split; [rewrite Hfrs2; apply in_or_app; right; exact HinF|].
      unfold frame_addr in *. rewrite EF2. split; assumption.
    + right; right. rewrite Eshi2. split; assumption.
  - destruct Hhome as [(b & m & HinL & Hb & Hm) | [(cid & pos & HinF & Hb & Hm) | (Hb & Hm)]].
    + destruct Hled0 as (_ & _ & HF & _). rewrite Forall_forall in HF.
      destruct (HF _ HinL) as (Hk0 & Hab & Hhp & _ & _). cbn [fst snd] in Hk0, Hab, Hhp.
      apply (ev_blk_shadow ly2 S2 Hp2 W2 mem2 md2 (b - cf_head) (m + cf_head)); [exact HAR2 | rewrite Eab2'; exact Hab | | lia | lia].
      rewrite EHp2'. apply ev_hd_le; [lia|]. intros _. lia.
    + destruct (alx_frames SEGS B ARx LAWS _ _ _ _ _ _ cid pos HAR0 HinF) as (Hfa32 & Happ & _).
      destruct (frames_bounds_x SEGS B ARx LAWS _ _ _ _ _ _ cid pos HAR0 HinF) as (Hf0 & Hfc & _).
      assert (Hfb8 : fs_frame_bytes cid mod 8 = 0) by (apply ev_fb8; lia).
      assert (Hfa8 : frame_addr (ea_ly a) cid pos mod 8 = 0).
      { pose proof (Z.div_mod (frame_addr (ea_ly a) cid pos) 32 ltac:(lia)). rewrite Hfa32 in *.
        rewrite Z.add_0_r in *. rewrite Z.mul_comm in *. rewrite (proj2 (Z.mod_divide _ 8 ltac:(lia))); [reflexivity|].
        exists ((frame_addr (ea_ly a) cid pos / 32) * 4). lia. }
      eapply range_addressable_agree; [|exact Hra0].
      intros x Hx. unfold shadow_of_addr.
      pose proof (Z.div_mod (frame_addr (ea_ly a) cid pos) 8 ltac:(lia)) as Dfa.
      pose proof (Z.div_mod (fs_frame_bytes cid) 8 ltac:(lia)) as Dfb.
      assert (Hx8 : (frame_addr (ea_ly a) cid pos) / 8 <= x / 8 < (frame_addr (ea_ly a) cid pos) / 8 + fs_frame_bytes cid / 8).
      { split; [apply Z.div_le_mono; lia|]. apply Z.div_lt_upper_bound; lia. }
      apply (Hfrk2 cid pos (SHADOW_OFF + x / 8) HinF).
      * right. unfold in_zr, shadow_addr. cbn [fst snd]. lia.
      * intros HF. apply ev_inFP in HF. destruct HF as [HF|HF]; [|unfold SHADOW_OFF in *; lia].
        (* the scratch is an application byte (in_app of its block); a shadow byte of an application byte is not *)
        unfold ea_len in *.
        pose proof (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR0 Hbs) as (_ & _ & _ & Happs & _).
        pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
        unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in Happs, Happ, HF. lia.
    + intros x Hx. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr.
      apply (ZSB_x ly2 S2 Hp2 W2 mem2 md2 x HAR2). rewrite Eslo2, Eshi2. change (spZ (ea_regs a)) with (sp0a a) in Hb. lia.
  - (* the root's granule hull: a Lam block by HSHD, a fake frame by ev_frame_hull, the real stack by the engine's
       YGcallHull.stack_hull_vis_x_rng with ev_stk64 *)
    pose proof (@ASAN_CEIL_range rc) as [Cm0 Cm]. unfold ASAN_CEIL in Cm0, Cm.
    destruct Hhome as [(b & m & HinL & Hb & Hm) | [(cid & pos & HinF & Hb & Hm) | (Hb & Hm)]].
    + destruct Hled0 as (_ & _ & HF & _). rewrite Forall_forall in HF.
      destruct (HF _ HinL) as (Hk0 & Hab & Hhp & _ & _). cbn [fst snd] in Hk0, Hab, Hhp.
      refine (proj2 (ev_blk_shadow ly2 S2 Hp2 W2 mem2 md2 (b - cf_head) (m + cf_head) (ea_v a) 56 HAR2 _ _ _ _) _);
        [rewrite Eab2'; exact Hab | | lia | lia | lia].
      rewrite EHp2'. apply ev_hd_le; [lia|]. intros _. lia.
    + assert (HinF2 : In (cid, pos) (frames S2)) by (rewrite Hfrs2; apply in_or_app; right; exact HinF).
      pose proof (ev_frame_hull ly2 S2 Hp2 W2 mem2 md2 cid pos HAR2 HinF2 ltac:(lia)) as Hfh.
      assert (Efa : frame_addr ly2 cid pos = frame_addr (ea_ly a) cid pos) by (unfold frame_addr; rewrite EF2; reflexivity).
      rewrite Efa in Hfh.
      apply (ev_hull_sub _ _ _ _ _ Hfh); lia.
    + change (spZ (ea_regs a)) with (sp0a a) in Hb.
      pose proof (ev_stk64 ly2 S2 Hp2 W2 mem2 md2 HAR2) as H64. rewrite Eshi2 in H64.
      pose proof (Z.div_mod (ea_v a) 64 ltac:(lia)). pose proof (Z.mod_pos_bound (ea_v a) 64 ltac:(lia)).
      pose proof (Z.div_mod (ea_v a + 56 - 1) 64 ltac:(lia)). pose proof (Z.mod_pos_bound (ea_v a + 56 - 1) 64 ltac:(lia)).
      pose proof (Z.div_mod (ly_stk_hi (ea_ly a)) 64 ltac:(lia)).
      apply (YGcallHull.stack_hull_vis_x_rng SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HAR2); [rewrite Eslo2; lia | rewrite Eshi2; lia]. }
(* the save area: inside the callee's window, outside FP1 *)
split.
{ unfold ev_saved in *. rewrite Forall_forall in *. intros orr Hin. pose proof (ev_saved_offs orr Hin) as Ho.
  apply (VM _ 8%nat _); [|exact (Hsav orr Hin)]. intros kk Hk. apply HX; [unfold ea_SA, ea_S1 in *; lia|].
  intros HF. apply HFP1, ev_inFP in HF. unfold ea_len, ea_SA in *. lia. }
(* the frame's flag word: the callee's journal keeps the frame (1, pos) the call was made from *)
split.
{ rewrite <- Hflag. apply rdword_ext. intros kk Hk.
  assert (Hin : In (1, ea_pos a) (frames S)) by (rewrite Hfrs; left; reflexivity).
  destruct (frames_bounds_x SEGS B ARx LAWS _ _ _ _ _ _ 1 (ea_pos a) HAR Hin) as (Hf0 & Hfc & _).
  assert (Efr : frame_addr ly 1 (ea_pos a) = fra a) by (unfold ea_fr, frame_addr; rewrite EF; reflexivity).
  rewrite Efr in Hf0, Hfc. change (fs_frame_bytes 1) with 128 in *.
  apply (Hfrk1 1 (ea_pos a) _ Hin).
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite Efr. change (fs_frame_bytes 1) with 128. lia.
  - intros HF. apply HFP1, ev_inFP in HF. destruct HF as [HF|HF]; [|lia].
    (* the scratch block and the frame are apart (alx_sep at the call's state) *)
    assert (Hbs1' : In (bs, ms) (ablocks B ly S)) by (rewrite Eab; exact Hbs).
    pose proof (sep_block_frame_x SEGS B ARx LAWS _ _ _ _ _ _ bs ms 1 (ea_pos a) HAR Hbs1' Hin) as Hsep.
    unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. rewrite Efr in Hsep. change (fs_frame_bytes 1) with 128 in Hsep.
    unfold ea_len in *. lia. }
(* the room and its paired hull use, and the run position: the activation's, then the callee's; the memory normal: the
   callee's keep *)
split; [split; [intros H0; exact (HRLc (proj1 HRL H0)) | exact (PresetHullBudget.hull_used_app _ _ _ nil nil (proj2 HRL) HHUc)]|].
split; [intros rp_sm rp_x rp_os rp_i rp_H0 rp_hist H0; exact (HRPc _ _ _ _ _ _ (HRP _ _ _ _ _ _ H0)) | exact HMN2].
Qed.
(* ======== PIECE 4 ======== *)

(* a word's tree is fixed by its tag *)
Lemma ev_wcase_tag : forall c off ty lo wl u t, ev_wcase c off ty lo wl u ->
  PjTree.tag u = ty /\ (PjTree.tag t = ty -> t = u).
Proof.
intros c off ty lo wl u t Hw.
destruct Hw as [(_ & _ & -> & _ & _ & ->)|[(_ & _ & -> & _ & _ & ->)|(_ & _ & -> & _ & _ & ->)]];
  (split; [reflexivity|]); destruct t; cbn [PjTree.tag]; intro H; first [reflexivity | discriminate H].
Qed.

(* H4 (word): ex_word's outcome at the activation's cursor is the text's outcome (ev_out) *)
Lemma ev_word_out : forall a i1 c off ty lo wl u r p' dl' t,
  ev_wcase c off ty lo wl u -> (i1 < length (ea_x a))%nat -> nth i1 (ea_x a) 0 = c ->
  PjGrammar.skip (skipn (Z.to_nat (ea_i0 a)) (ea_x a)) = skipn i1 (ea_x a) ->
  (ea_dl a = 0 \/ ea_dl a = 1) -> 0 <= ea_dep a <= 32 ->
  (ea_v a <> 0 -> t = PjTree.tag (ea_t a)) ->
  ((Z.of_nat (length wl) <= Z.of_nat (length (ea_x a)) - Z.of_nat i1 /\
      firstn (length wl) (skipn (Z.to_nat (Z.of_nat i1)) (ea_x a)) = wl) /\
     r = 0 /\ p' = Z.of_nat i1 + Z.of_nat (length wl) /\
     ((ea_v a <> 0 /\ t <> ty /\ dl' = 1) \/ ((ea_v a = 0 \/ t = ty) /\ dl' = ea_dl a))) \/
  (~ (Z.of_nat (length wl) <= Z.of_nat (length (ea_x a)) - Z.of_nat i1 /\
      firstn (length wl) (skipn (Z.to_nat (Z.of_nat i1)) (ea_x a)) = wl) /\
     r = -1 /\ p' = Z.of_nat i1 /\ dl' = ea_dl a) ->
  ev_out (L := A_prog_listing) (PA := PA) a r p' (ea_dep a) dl'.
Proof.
intros a i1 c off ty lo wl u r p' dl' t Hw Hi Hc Hsk Hdl Hdep Ht Hcase.
rewrite Nat2Z.id in Hcase.
assert (HV : prhex_V (ea_dep a) (skipn (Z.to_nat (ea_i0 a)) (ea_x a)) =
  if PjGrammar.prefixb wl (skipn i1 (ea_x a)) then Some (u, skipn (length wl) (skipn i1 (ea_x a))) else None).
{ rewrite (ev_skipn_cons _ i1 Hi) in Hsk |- *. rewrite Hc in Hsk |- *.
  apply (ev_V_word _ _ _ _ _ _ Hsk).
  destruct Hw as [(-> & _ & _ & _ & -> & ->)|[(-> & _ & _ & _ & -> & ->)|(-> & _ & _ & _ & -> & ->)]];
    [left | right; left | right; right]; auto. }
destruct (ev_wcase_tag c off ty lo wl u (ea_t a) Hw) as (Etu & Etag).
unfold ev_out. rewrite HV.
destruct Hcase as [((Hh1 & Hh2) & -> & -> & Hd) | (Hnh & -> & -> & ->)].
- assert (Hpre : PjGrammar.prefixb wl (skipn i1 (ea_x a)) = true) by (apply ev_prefixb_firstn; exact Hh2).
  rewrite Hpre.
  split; [destruct Hd as [(_ & _ & ->)|(_ & ->)]; [right; reflexivity | exact Hdl]|].
  split; [reflexivity|]. split; [unfold ea_len; rewrite !length_skipn; lia|]. split; [reflexivity|].
  destruct Hd as [(Hv & Htt & ->)|(Hvt & ->)].
  + split; [intros _; right; split; [exact Hv|]|intros _; reflexivity].
    intros E. apply Htt. rewrite (Ht Hv), E. exact Etu.
  + split; [intros H; left; exact H|]. intros [H|(Hv & Hne)]; [exact H|]. exfalso.
    destruct Hvt as [Hv0|Hty]; [exact (Hv Hv0)|]. apply Hne. apply Etag. rewrite <- (Ht Hv). exact Hty.
- assert (Hpre : PjGrammar.prefixb wl (skipn i1 (ea_x a)) = false).
  { destruct (PjGrammar.prefixb wl (skipn i1 (ea_x a))) eqn:E; [|reflexivity]. exfalso. apply Hnh.
    apply ev_prefixb_firstn in E. split; [|exact E].
    pose proof (f_equal (@length Z) E) as EL. rewrite length_firstn, length_skipn in EL. lia. }
  rewrite Hpre. split; [exact Hdl|]. split; [reflexivity|]. split; [unfold ea_len; lia|]. lia.
Qed.

(* S8aDisp's ev_cfg_to (a Section-local Ltac there, so restated): the mkst configuration at BASE + n as ev_cfg at off *)
Ltac ev_cfg_to off :=
  lazymatch goal with |- SRr _ _ {| cfg_ms := YK11.mkst ?r (Z_to_bv 64 (pa_val A_TEXT + ?n)) ?m _; cfg_model := ?d |} _ =>
    rewrite (ev_cfg_eq _ r off m d n ltac:(rewrite ev_pc_eq; vm_compute; reflexivity)) end.

(* the return site 0x83760: `mv s11, a0; j 0x83d48` - P_EXIT with r in s11 *)
Definition ss_wret : sstate := mkSS (EV0 + EV_WRET) sr_atoms [] None (mkFacts [] [] []).
Lemma ev_word_ret : forall a fx' W regs mem md ly S Hp k r p' dl',
  PRE a -> FXOK fx' -> MID a ly S Hp W mem md k (ea_x0 a + p') (ea_dep a) dl' -> REGS a regs ->
  getr regs 22 = w64 (fra a) -> getr regs 10 = w64 r -> ev_out (L := A_prog_listing) (PA := PA) a r p' (ea_dep a) dl' ->
  SRr SEGS W (CFG fx' regs EV_WRET mem md) (TO_EXIT a).
Proof.
intros a fx' W regs mem md ly S Hp k r p' dl' HP HFX HM HR H22 H10 Hout.
pose proof HM as (HJ & _ & _ & _ & _ & (Q1 & _ & _ & _ & Q5) & _).
pose proof HM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMN).
remember (Eimg (Ereg regs [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs []) E) by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (HS : st_ok_pi SEGS VAL E ss_wret (restrict (w_H W) (@YK11.mkst fx' regs (Z_to_bv 64 (BASE + (EV0 + EV_WRET))) mem (YK11.seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_wret. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - reflexivity.
  - constructor.
  - exact I.
  - split; [exact I | split; exact I]. }
assert (E10 : ew E 10 = w64 r)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
clear HE.
assert (SHOK : sh_ok SEGS D_Bx [] E (mrestrict (w_H W) mem)) by apply Forall_nil.
unfold ev_cfg, ev_pc. rewrite ev_pc_eq.
pose (RUNTOI := @paj_run_to_x_inv fx' rc SK A_prog_listing PL PA B PST ARx hl LAWS (YAkMemnorm.memnorm SEGS)
  (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)).
paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HMN D_Bspan (EV0 + EV_EXIT).
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp ?fp ?b0 ?bc ?ly' ?own => let rs' := eval vm_compute in rs in
    change (awr_ok Ex rs' stk sp fp b0 bc ly' own) end.
  apply awr_ok_nil. }
pose proof (ev_frame_ro E _ _ _ HFr ltac:(vm_compute; reflexivity)) as HM1. clear HF HFr HG.
pose proof (regs_kept_of_st_ok_pi E _ _ regs _ [2; 3; 4; 8; 9; 18; 19; 22; 24; 25; 26]%bv HS HAE
  ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
prreg HS (27%bv : bv 5) N27.
pmkst HS. ev_cfg_to EV_EXIT.
apply SRr_ret.
lazymatch goal with |- TO_EXIT a W (CFG fx' ?r EV_EXIT ?m ?d) => exists fx', r, m, d, ly, S, Hp end.
eexists. exists r, p', (ea_dep a), dl'. split; [reflexivity|]. split; [exact HFX|].
split.
{ apply (ev_mid_frame B ARx SK LAWS a ly S Hp W mem md k _ _ _ _ _ _ _ _ HP HM HJ).
  - intros x _. exact (HM1 x).
  - exact (ev_vm_eq SEGS _ _ _ _ _ HM1 Q1).
  - exact (ev_vm_eq SEGS _ _ _ _ _ HM1 Q5).
  - exact HMN. }
split; [apply (ev_regs_kept a regs _ HR); intros r0 Hr0; apply HK; cbv in Hr0 |- *; tauto|].
split; [rewrite (HK 22%bv) by (cbv; tauto); exact H22|].
split; [rewrite N27; exact E10|].
exact Hout.
Qed.

(* the callee-saved registers ex_value's cut points carry survive a program call *)
Lemma ev_regs_call : forall a regs regs2, REGS a regs -> aregs_preserved regs regs2 ->
  REGS a regs2 /\ getr regs2 22 = getr regs 22.
Proof.
intros a regs regs2 HR HPr.
assert (HK : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 22; 24; 25; 26]%bv -> getr regs2 r = getr regs r).
{ intros r Hr. pose proof (HPr (bv_unsigned r)) as Hk. rewrite Z_to_bv_bv_unsigned in Hk. apply Hk.
  assert (Hb : forall z, ((z =? 2) || (z =? 3) || (z =? 4) || (z =? 8) || (z =? 9) || ((18 <=? z) && (z <=? 27)))%bool = true ->
            acallee_saved z).
  { intros z Hz. unfold acallee_saved. repeat rewrite orb_true_iff in Hz. rewrite andb_true_iff in Hz.
    rewrite !Z.eqb_eq, !Z.leb_le in Hz. lia. }
  apply Hb. cbv [In] in Hr.
  repeat (destruct Hr as [<-|Hr]; [vm_compute; reflexivity|]); try destruct Hr. }
split; [apply (ev_regs_kept a regs regs2 HR); intros r Hr; apply HK; cbv in Hr |- *; tauto|].
apply HK. cbv; tauto.
Qed.

(* ---- the call `jal ex_word` (0x8375c): from ex_word's entry, with a0 = in, a1 = the literal, a2 = the type,
   a3 = v, ra = 0x83760, through the text (WORDX) by aj_call_xWF, to P_EXIT ---- *)
Lemma ev_word_call : forall a fxc W regs mem md ly S Hp k i1 c off ty lo wl u,
  PRE a -> FXOK fxc -> ev_wcase c off ty lo wl u ->
  MID a ly S Hp W mem md k (ea_x0 a + Z.of_nat i1) (ea_dep a) (ea_dl a) -> REGS a regs ->
  getr regs 22 = w64 (fra a) ->
  getr regs 10 = w64 (ea_q a) -> getr regs 11 = w64 (VAL (A_OBJ 2) + lo) -> getr regs 12 = w64 ty ->
  getr regs 13 = w64 (ea_v a) -> getr regs 1 = Z_to_bv 64 (BASE + (EV0 + EV_WRET)) ->
  (i1 < length (ea_x a))%nat -> nth i1 (ea_x a) 0 = c ->
  PjGrammar.skip (skipn (Z.to_nat (ea_i0 a)) (ea_x a)) = skipn i1 (ea_x a) ->
  SRr SEGS W (mkCfg (@YK11.mkst fxc regs (Z_to_bv 64 (SIGMA AS_ex_word)) mem (YK11.seg_rom SEGS)) md) (TO_EXIT a).
Proof.
intros a fxc W regs mem md ly S Hp k i1 c off ty lo wl u HP HFX Hw HM HR H22 H10 H11 H12 H13 H1 Hi Hc Hsk.
pose proof (ev_arith B ARx a HP) as (Hal16 & Hceil & Hslo & Hdtop & Htop & H47 & Hd0 & Hd16 & Hspq & Hq40 & Hqm & EK & HS1m &
  HS1 & ESA & Hx4096 & Hxc & Hi0 & Hlen & Hdep & Hdl).
pose proof (asan_consts (rc := rc)) as (C1 & C2 & C3 & C4 & C5).
pose proof (@cf_head_nonneg cp) as Hch.
pose proof HP as HP0. unfold ev_pre in HP0. cbv zeta in HP0.
destruct HP0 as ((HAF0 & HROD & HSH0 & _) & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hinb0 & _ & _ & _ & _ & _ & _ & _ & _ &
  _ &
  Hled0 & _).
pose proof HAF0 as (HAR0 & _ & _ & Hgp0 & Htp0 & _).
pose proof HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R24 & R25 & R26).
pose proof HM as (HJ & Hwin & EHp & Eab & Hled & Hcur & Hsrc & Hwd & Htree & Hsav & Hflag & HRL & HRP & HMN).
assert (Hlen0 : 0 < lena a) by (unfold ea_len; lia).
assert (Hinb : prhex_inblk B ly S Hp (ea_x0 a) (lena a))
  by (unfold prhex_inblk; rewrite EHp, Eab; exact (Hinb0 Hlen0)).
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof Hcur as (Q1 & Q2 & _ & _ & Q5).
assert (HSTKw : (0 <=? STK_ex_word (PI := PIA)) && (STK_ex_word (PI := PIA) <=? 16384) = true) by (vm_compute; reflexivity).
apply andb_prop in HSTKw as [HSw1 HSw2]. apply Z.leb_le in HSw1. apply Z.leb_le in HSw2.
assert (ES1 : spZ regs = S1a a) by (unfold spZ; rewrite R2; apply unsigned_lit_small; lia).
set (spJ := sp0a a + ea_d a) in *.
assert (Ho16 : (S1a a - spJ) mod 16 = 0 /\ (spJ - S1a a) mod 16 = 0).
{ unfold spJ. pose proof (Z.div_mod (S1a a) 32 ltac:(lia)). pose proof (Z.div_mod (sp0a a) 16 ltac:(lia)).
  pose proof (Z.div_mod (ea_d a) 16 ltac:(lia)).
  split.
  - replace (S1a a - (sp0a a + ea_d a)) with ((2 * (S1a a / 32) - sp0a a / 16 - ea_d a / 16) * 16) by lia.
    apply Z.mod_mul. lia.
  - replace (sp0a a + ea_d a - S1a a) with ((sp0a a / 16 + ea_d a / 16 - 2 * (S1a a / 32)) * 16) by lia.
    apply Z.mod_mul. lia. }
destruct (ev_call_st fxc SEGS (w_H W) regs (SIGMA AS_ex_word) mem spJ (S1a a - spJ)) as (E0 & ss0 & HS0 & Hrv0 & Hpc0 & Hsp0 & HE2).
{ unfold spJ. lia. }
{ rewrite R2. unfold w64. f_equal. lia. }
destruct (ev_chain a ly S Hp W mem md k _ _ _ (S1a a) HP HM ltac:(lia)) as (ch1 & Hch1).
set (FP1 := [(ea_q a, ea_q a + 8); (ea_q a + 32, ea_q a + 36)]).
set (t := PjTree.tag (ea_t a)).
(* ex_word's premises at the call *)
pose proof (ev_rod a ly S Hp W mem md k _ _ _ HP HM) as Hrod.
assert (Hlit : cstr_ok (PA := PA) W mem (VAL (A_OBJ 2) + lo) wl /\ 0 <= ty <= 2).
{ destruct ev_lit_img_A as (Lt & Lf & Ln).
  destruct Hw as [(_ & _ & -> & -> & -> & _)|[(_ & _ & -> & -> & -> & _)|(_ & _ & -> & -> & -> & _)]];
    (split; [eapply ev_lit_cstr; [exact HAR | exact Hrod | eassumption] | lia]). }
assert (Hwin' : fwin ly W regs mem (spJ - S1a a)).
{ split; [lia|]. split; [exact (proj2 Ho16)|]. split; [rewrite ES1, Etop; unfold spJ; lia|].
  intros z Hz. rewrite ES1 in Hz. apply Hpres. unfold spJ in *. lia. }
assert (Hvt : ea_v a <> 0 -> val_mem SEGS (rdW W mem) (ea_v a) 4 t /\ 0 <= t < 2 ^ 32 /\ ea_v a mod 8 = 0 /\
          range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (ea_v a) 4 /\
          (ea_v a + 4 <= spZ regs - STK_ex_word (PI := PIA) \/ spZ regs <= ea_v a)).
{ intros Hv0. destruct Htree as [Hz|(Hpj & Hhome & Hra & _)]; [contradiction|].
  destruct (ev_hdrR _ _ _ _ _ _ Hpj) as (str & (Ht32 & Htv) & Hv8 & _).
  split; [exact Htv|]. split; [exact Ht32|]. split; [exact Hv8|].
  split; [apply (range_addressable_sub _ _ (ea_v a) 56); [exact Hra | lia | lia]|].
  rewrite ES1.
  destruct Hhome as [(b & m & HinL & Hb & Hm) | [(cid & pos & HinF & Hb & Hm) | (Hb & Hm)]].
  - left. destruct Hled as (_ & _ & HF & _). rewrite Forall_forall in HF.
    destruct (HF _ HinL) as (Hk0 & Hab & _). cbn [fst snd] in Hk0, Hab.
    destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR Hab) as (_ & _ & Hbc & _).
    pose proof (ev_req_ge (m + cf_head)). lia.
  - left. destruct (frames_bounds_x SEGS B ARx LAWS _ _ _ _ _ _ cid pos HAR HinF) as (_ & Hfc & _). lia.
  - right. change (spZ (ea_regs a)) with (sp0a a) in Hb. lia. }
(* tex_word_specX's machine-address premise on v (the kit's fix of WORDX's counterexample): v = 0, or v is the tree
   root, whose home (a Lam heap block, a live fake frame, the real stack above the entry sp) lies below 2 ^ 47 at
   every state LAWS governs (S8aDisp.ev_home_bound: alx_blocks, alx_sep's frame bounds, ly_stk_hi <= 2 ^ 47) *)
assert (Hvb : 0 <= ea_v a /\ ea_v a + 4 <= 2 ^ 47).
{ destruct Htree as [Hv0|(_ & Hhome & _)]; [rewrite Hv0; lia|].
  pose proof (ev_home_bound B ARx LAWS ly S Hp W mem md mem (ea_Lam a) (ea_regs a) (ea_v a) 56 _ _ _ _ _ _ HAR Hled
    ltac:(rewrite Eshi; exact H47) ltac:(lia) Hhome) as (Hvlo & Hvhi). lia. }
(* PRH_Base.fpre's two conjuncts past the read-only view (walkkit old-pin be60d536d2af): ex_word's entry sp is the body's
   S1, 64 or more below the stack's top (S1 <= sp0 - 256 and fpre's sp0 + 64 <= ly_stk_hi at the activation); its ra
   is the jal's return pc, a listing literal below the ceiling's least value *)
assert (HSPc : spZ regs + 64 <= ly_stk_hi ly).
{ rewrite ES1, Eshi. change (spZ (ea_regs a)) with (sp0a a) in HSH0. lia. }
assert (HRAc : raZ regs < YM05.alloc_ceiling).
{ unfold raZ. rewrite H1. apply (Z.lt_le_trans _ 0x7fff7f800000); [apply Z.ltb_lt; vm_compute; reflexivity | lia]. }
eapply SRr_bind.
{ eapply (aj_call_xWF_d (fx := fxc) (SK := SK) SEGS B PST ARx LAWS (@pa_segs_low _ A_prog_listing PA) W E0 ss0
    (@YK11.mkst fxc regs (Z_to_bv 64 (SIGMA AS_ex_word)) mem (YK11.seg_rom SEGS))
    (STKa a + ea_d a) spJ (FPa a) (ea_ly a) (ea_S a) (ea_Hp a) (ea_W a) (ea_mem a) (ea_md a) [(1, ea_pos a)]
    ly S Hp md k (STK_ex_word (PI := PIA)) FP1 (S1a a - spJ) (spJ - S1a a) (Z_to_bv 64 spJ)
    (Z_to_bv 64 (BASE + (EV0 + EV_WRET))) ch1 _ HS0 Hrv0 HJ).
  - exact Hsp0.
  - exact HE2.
  - apply unsigned_lit_small. unfold spJ. lia.
  - exact (proj1 Ho16).
  - lia.
  - lia.
  - unfold spJ. rewrite EK. lia.
  - lia.
  - lia.
  - cbn [ms_regs YK11.mkst]. rewrite R3. exact Hgp0.
  - cbn [ms_regs YK11.mkst]. rewrite R4. exact Htp0.
  - exact H1.
  - apply (ret_ok_codeptr_v (PI := PA)); [split; apply Z.leb_le || apply Z.ltb_lt; vm_compute; reflexivity | vm_compute; reflexivity].
  - rewrite unsigned_lit_small; [apply Z.leb_le; vm_compute; reflexivity|].
    split; [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity.
  - cbn [ms_regs ms_mem YK11.mkst]. replace (spJ + (S1a a - spJ)) with (S1a a) by lia.
    unfold s0Z. rewrite R8, unsigned_lit_small by lia. exact Hch1.
  - intros HAFN. rewrite Hpc0. eapply SRr_mono.
    + exact (WORDX fxc ly S Hp W regs mem md ch1 (ea_q a) (VAL (A_OBJ 2) + lo) ty (ea_v a) t (ea_x0 a) (Z.of_nat i1)
        (spJ - S1a a) wl (ea_x a) (ea_Lam a) (ea_peak a) (ea_cnt a) (ea_fail a) (ea_ran a) (ea_most a) (ea_own a)
        (conj HAFN (conj Hrod (conj HSPc (conj HRAc (proj1 HFX))))) H10 H11 H12 H13 (proj1 Hlit) (proj2 Hlit) Hvb Q1 Q2 Hqm
        ltac:(rewrite ES1; lia)
        ltac:(rewrite ES1; unfold spJ; lia) Hwin' Hsrc Hinb ltac:(unfold ea_len in Hlen; exact Hlen)
        ltac:(unfold ea_len in *; lia) Hvt Hled).
    + cbv beta. intros W' c' _ (ly' & S' & Hp' & regs' & mem' & md' & k' & -> & HJc & HXc & HPr & HQ).
      exists fxc, ly', S', Hp', regs', mem', md', k'. split; [reflexivity|]. split; [exact (proj1 HFX)|].
      split; [intros r0 _; reflexivity|]. split; [exact HJc|]. split; [exact HPr|]. exact (conj HXc HQ).
  - intros z (r0 & Hin & Hr0). left. exists r0. split; [|exact Hr0]. unfold FP1 in Hin. unfold ea_FP.
    cbn [In] in Hin |- *. destruct Hin as [<-|[<-|[]]]; tauto. }
cbv beta. intros W2 c2 _ (fx2 & ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HFZ & HFK & HJo & HJc & HPr &
  (HXc & (HRLc & EHp2 & ES2 & Eab2 & Hled2 & Hcase) & HMNk)).
pose proof (HMNk HMN) as HMN2.
ev_cfg_to EV_WRET.
assert (HFX2 : FXOK fx2).
{ split; [exact HFZ|]. intros rr Hrr. rewrite (HFK rr Hrr). exact (proj2 HFX rr Hrr). }
destruct (ev_regs_call a regs regs2 HR HPr) as (HR2 & E22).
replace (spJ + (S1a a - spJ) + (spJ - S1a a)) with spJ in HJc by lia.
assert (HX' : forall z, S1a a <= z < sp0a a + ea_d a -> ~ inFP FP1 z ->
          aview SEGS (w_H W2) mem2 z = aview SEGS (w_H W) mem z)
  by (intros z Hz Hn; apply HXc; [rewrite ES1; unfold spJ in *; lia | exact Hn]).
assert (HFP1 : forall z, inFP FP1 z -> inFP (FPa a) z).
{ intros z (r0 & Hin & Hr0). exists r0. split; [|exact Hr0]. unfold FP1 in Hin. unfold ea_FP.
  cbn [In] in Hin |- *. destruct Hin as [<-|[<-|[]]]; tauto. }
assert (HFPq : forall z, ea_q a + 8 <= z < ea_q a + 32 -> ~ inFP FP1 z).
{ intros z Hz (r0 & Hin & Hr0). unfold FP1 in Hin. cbn [In] in Hin. destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr0; lia. }
(* the two cursor cells after the call, in the three outcomes *)
assert (VMS : forall z (n : nat) v, prhex_same (PA := PA) W mem W2 mem2 z (Z.of_nat n) ->
          val_mem SEGS (rdW W mem) z n v -> val_mem SEGS (rdW W2 mem2) z n v).
{ intros z n v Hs Hv. eapply ev_vm_kept; [|exact Hv]. intros kk Hk. apply mbyte_of_aview. apply Hs. lia. }
destruct Hcase as [(Hhit & Ha0 & Hq2 & [(Hv & Hty & Hdl2) | (Hvt' & Hsame)]) | (Hnh & Ha0 & Hsq & Hsd)].
- apply (ev_word_ret a fx2 W2 regs2 mem2 md2 ly2 S2 Hp2 (k + k1) 0 (Z.of_nat i1 + Z.of_nat (length wl)) 1 HP HFX2).
  + apply (ev_mid_rt a ly S Hp W mem md k _ _ _ ly2 S2 Hp2 W2 mem2 md2 (k + k1) _ FP1 k1 _ _ HP HM HJo HJc HX' HFP1 HFPq
      EHp2 Eab2 Hled2); [rewrite Z.add_assoc; exact Hq2 | exact Hdl2 | exact Hlen0 | exact HRLc |
      rewrite ES2; apply PresetHullBudget.hull_used_refl |
      intros rp_sm rp_x rp_os rp_i rp_H0 rp_hist H0; rewrite ES2; exact H0 | exact HMN2].
  + exact HR2.
  + rewrite E22. exact H22.
  + exact Ha0.
  + apply (ev_word_out a i1 c off ty lo wl u 0 _ 1 t Hw Hi Hc Hsk Hdl Hdep (fun _ => eq_refl)).
    left. split; [exact Hhit|]. split; [reflexivity|]. split; [reflexivity|]. left. split; [exact Hv|]. split; [exact Hty | reflexivity].
- apply (ev_word_ret a fx2 W2 regs2 mem2 md2 ly2 S2 Hp2 (k + k1) 0 (Z.of_nat i1 + Z.of_nat (length wl)) (ea_dl a) HP HFX2).
  + apply (ev_mid_rt a ly S Hp W mem md k _ _ _ ly2 S2 Hp2 W2 mem2 md2 (k + k1) _ FP1 k1 _ _ HP HM HJo HJc HX' HFP1 HFPq
      EHp2 Eab2 Hled2); [rewrite Z.add_assoc; exact Hq2 | exact (VMS _ 4%nat _ Hsame Q5) | exact Hlen0 | exact HRLc |
      rewrite ES2; apply PresetHullBudget.hull_used_refl |
      intros rp_sm rp_x rp_os rp_i rp_H0 rp_hist H0; rewrite ES2; exact H0 | exact HMN2].
  + exact HR2.
  + rewrite E22. exact H22.
  + exact Ha0.
  + apply (ev_word_out a i1 c off ty lo wl u 0 _ (ea_dl a) t Hw Hi Hc Hsk Hdl Hdep (fun _ => eq_refl)).
    left. split; [exact Hhit|]. split; [reflexivity|]. split; [reflexivity|]. right. split; [exact Hvt' | reflexivity].
- apply (ev_word_ret a fx2 W2 regs2 mem2 md2 ly2 S2 Hp2 (k + k1) (-1) (Z.of_nat i1) (ea_dl a) HP HFX2).
  + apply (ev_mid_rt a ly S Hp W mem md k _ _ _ ly2 S2 Hp2 W2 mem2 md2 (k + k1) _ FP1 k1 _ _ HP HM HJo HJc HX' HFP1 HFPq
      EHp2 Eab2 Hled2); [exact (VMS _ 8%nat _ Hsq Q1) | exact (VMS _ 4%nat _ Hsd Q5) | exact Hlen0 | exact HRLc |
      rewrite ES2; apply PresetHullBudget.hull_used_refl |
      intros rp_sm rp_x rp_os rp_i rp_H0 rp_hist H0; rewrite ES2; exact H0 | exact HMN2].
  + exact HR2.
  + rewrite E22. exact H22.
  + exact Ha0.
  + apply (ev_word_out a i1 c off ty lo wl u (-1) _ (ea_dl a) t Hw Hi Hc Hsk Hdl Hdep (fun _ => eq_refl)).
    right. split; [exact Hnh|]. split; [reflexivity|]. split; reflexivity.
Qed.

(* ---- PIECE 4: from P_KIND at EV_WORD_F / EV_WORD_N / EV_WORD_T, the straight run to `jal ex_word`, then the call ---- *)
Definition ss_word (off : Z) : sstate := mkSS (EV0 + off) sr_atoms [] None (mkFacts [] [] []).
Lemma ev_word : ev_word_spec (fx := fx) (PI := PIA) (L := A_prog_listing) (PA := PA) B ARx SK.
Proof.
intros a fxc W regs mem md ly S Hp k i1 c off HP HFX HK Hc.
assert (Hw : exists ty lo wl u, ev_wcase c off ty lo wl u).
{ unfold ev_wcase. destruct Hc as [(-> & ->)|[(-> & ->)|(-> & ->)]].
  - exists 1, 0x10f80, PjGrammar.w_false, PjTree.JFalse. right; left. repeat split.
  - exists 0, 0x10fa0, PjGrammar.w_null, PjTree.JNull. right; right. repeat split.
  - exists 2, 0x10f60, PjGrammar.w_true, PjTree.JTrue. left. repeat split. }
destruct Hw as (ty & lo & wl & u & Hw).
destruct HK as (HM & HR & H20 & H21 & H22 & H23 & H27 & H11 & H12 & Hi & Hnth & Hws & Hsk).
pose proof HM as (HJ & _ & _ & _ & _ & (Q1 & _ & _ & _ & Q5) & _).
pose proof HM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMN).
pose proof HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R24 & R25 & R26).
remember (Eimg (Ereg regs [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs []) E) by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E19 : ew E 19 = w64 (ea_q a))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact R19).
assert (E23 : ew E 23 = w64 (ea_v a))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 23 23%bv eq_refl); exact H23).
assert (HS : st_ok_pi SEGS VAL E (ss_word off) (restrict (w_H W) (@YK11.mkst fxc regs (Z_to_bv 64 (BASE + (EV0 + off))) mem (YK11.seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_word. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - reflexivity.
  - constructor.
  - exact I.
  - split; [exact I | split; exact I]. }
clear HE.
assert (SHOK : sh_ok SEGS D_Bx [] E (mrestrict (w_H W) mem)) by apply Forall_nil.
unfold ev_cfg, ev_pc. rewrite ev_pc_eq.
pose (RUNI := @paj_run_x_inv fxc rc SK A_prog_listing PL PA B PST ARx hl LAWS (YAkMemnorm.memnorm SEGS)
  (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)).
pose proof Hw as Hw0.
destruct Hw0 as [(-> & -> & -> & -> & -> & ->)|[(-> & -> & -> & -> & -> & ->)|(-> & -> & -> & -> & -> & ->)]];
  unfold ss_word in HS;
  (paj_run_tok_x_inv RUNI HS HJ SHOK HMN D_Bspan;
   [ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp ?fp ?b0 ?bc ?ly' ?own => let rs' := eval vm_compute in rs in
       change (awr_ok Ex rs' stk sp fp b0 bc ly' own) end; apply awr_ok_nil
   | ]);
  (pose proof (ev_frame_ro E _ _ _ HFr ltac:(vm_compute; reflexivity)) as HM1; clear HF HFr HG;
   pose proof (regs_kept_of_st_ok SEGS _ _ _ regs [] [2; 3; 4; 8; 9; 18; 19; 22; 24; 25; 26]%bv HS
     ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HK; cbn [ms_regs restrict] in HK;
   prreg HS (10%bv : bv 5) N10; prreg HS (11%bv : bv 5) N11; prreg HS (12%bv : bv 5) N12;
   prreg HS (13%bv : bv 5) N13; prreg HS (1%bv : bv 5) N1;
   pmkst HS;
   eapply (ev_word_call a fxc W _ _ _ ly S Hp _ i1 _ _ _ _ _ _ HP HFX Hw);
   [ apply (ev_mid_frame B ARx SK LAWS a ly S Hp W mem md k _ _ _ _ _ _ _ _ HP HM HJ);
       [ intros x _; exact (HM1 x) | exact (ev_vm_eq SEGS _ _ _ _ _ HM1 Q1) | exact (ev_vm_eq SEGS _ _ _ _ _ HM1 Q5)
       | exact HMN ]
   | apply (ev_regs_kept a regs _ HR); intros r0 Hr0; apply HK; cbv in Hr0 |- *; tauto
   | rewrite (HK 22%bv) by (cbv; tauto); exact H22
   | rewrite N10; exact E19
   | rewrite N11; rewrite (HEI 243%nat) by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity
   | rewrite N12; reflexivity
   | rewrite N13; exact E23
   | rewrite N1; f_equal; f_equal; vm_compute; reflexivity
   | exact Hi | exact Hnth | exact Hsk ]).
Qed.
End w.
