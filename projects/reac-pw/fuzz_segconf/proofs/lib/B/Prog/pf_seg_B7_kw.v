(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_box_catalogue on fuzz_segconf.asan-ubsan (image B, pin sha256
   c3796c0b38f3, twin 80e82127e8ca; entry 0x8a8a0, 84 bytes, 21 instructions, a 16-byte frame, no side-stack
   frame): reac_box_catalogue_contract of lib/B/Prog/reac_box_catalogue_c.v (image B's copy of the image-A owner's FINAL
   text at 6f783602b5e3) at image B's numbers, in plugin-hostd/fuzz_command's lib/A/Prog form (afn_pre at the
   entry, SRr of apost_base at the return, over `Context {PI : PAImg seg_listing}` of image B's listing,
   lib/B/Prog/SegPa.v).
   ADAPTATION (relocation + one trap) of lib/A/Prog/reac_box_catalogueA.v (the image-A m_file-family lane, commit
   434ade288123, both arms): the same entry seeds, token runs and return steps over image B's listing modules and
   B's kit copies. The UBSan alignment check is read from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_catalogue.v
   at origin/ossv/recipes 3abc3740de97 (the same image-B code but 4 pc-relative words; caller-journal form, not
   copied), whose token run decides it the same way.
   Image B's code differs from image A's by two instructions: `andi a1,a0,7` (0x8a8ac) and `bnez a1,0x8a8ec`
   (0x8a8b0) to `unimp` (0x8a8ec), the UBSan alignment check of the 8-byte store through c.
   UBSan trap branch (one): 0x8a8b0 `bnez a1` -> unimp 0x8a8ec. Not taken: the c <> 0 run's entry seed carries the
   fact (10%nat, mkAF 4096 (2 ^ 47 - 8) 3) on a0 (rbc_facts: c is 2^3-aligned, from the contract premise
   c mod 8 = 0, seeded by rbc_entry), so the token executor (paj_run_tok, its branch step under facts_ok) computes
   a1 = c & 7 = 0 and decides the branch not taken; the trap instruction is never executed. The c = 0 run leaves at
   the beqz 0x8a8a8 (a0 pinned to 0) before the check.
   c <> 0: the instrumented check of the 8-byte cell (a load of the shadow byte at (c >> 3) + the shadow base, lbu
   0x8a8c8, and a compare, bnez 0x8a8cc) reads 0, because the contract's sa_addr gives the cell addressable; so the
   error path (the call of errpath_store8 at 0x8a8f0) is not reached; the sd at 0x8a8d4 writes 11 as 8 bytes. In
   both arms a0 = fuzz_catalogue (auipc/addi 0x8a8d8-0x8a8dc, 0xa20a0). The shadow base is the word the GOT cell
   as_got_shadow B holds (image B 0xa3210, the ld at 0x8a8b8, listing object 0; its target
   __asan_shadow_memory_dynamic_address 0xac7b8, listing object 12): the walk takes both from PALib (pal_got_shadow,
   pal_cell), a listing fact, not a contract premise.
   Positional names checked against image B's own listing (lib/B/Prog/SegAddr.v seg_objs, SegList.v) by address and
   anchor symbol (twin nm): A_OBJ 0 = 0xa3210 (the .got word the ld at 0x8a8b8 reads), A_OBJ 12 = 0xac7b8
   (__asan_shadow_memory_dynamic_address), A_OBJ 77 = RBC_CAT_OBJ = 0xa20a0 (fuzz_catalogue; SegList.v
   `PAddHi (10%bv : reg) (10%bv : reg) 123 (A_OBJ 77) 0x0` at 0x8a8dc), AF_reac_box_catalogue = 0x5ae0 =
   0x8a8a0 - seg_text 0x84dc0, atom 32 = the first extra env word (the shadow base SB, rbc_extra): 5 checked, 0
   pointing elsewhere.
   Image B's numbers of the statement: the entry BASE + AF_reac_box_catalogue; STK_reac_box_catalogue = 16 (the
   contract's STK comment: its frame, 0x8a8a0 addi sp,sp,-16 released at 0x8a8e4; the unimp at 0x8a8ec and the jal
   at 0x8a8f0 are the dead trap and error arms; no callee); cat = catA = 0xa20a0. Both are lib/B/Prog/SegInstB.v's
   definitions (SegInstA's names at image B): SegInstB.STK_reac_box_catalogue and SegInstB.catA, tied to this walk
   by the lemmas STK_reac_box_catalogue_B (the value 16) and catA_B (listing object 77 of B's seg_objs). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 474 of its 524 lines of code are new or changed and 403 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/pf_seg_B9_s11.v, with its module names changed; 1155 of its 1280 lines of code are new or changed and 399 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3): the KWOK piece of segment B7 of
   reac_segconf_parse_file's walk, `b7kw_ok : B7_S_KWOK B` (lib/B/Prog/pf_seg_B7_m.v): HA_UNK, HA_NONAME,
   HA_REFTL, HA_SEG -> H_KWOK at every FP state. A B7 sub-lane of the image-B G3 walk owner, 2026-10-30.
   proves no function (kind: segment lemma of reac_segconf_parse_file's walk, piece KWOK of segment B7).
   The code (reac_segconf_parse_file.fuzz_segconf.asan-ubsan.s), 26 instructions:
     KWOK 0x88764 .. 0x88788  li a0,-8; bltu a0,s3 (trap T19, not taken: decided by the executor from the seed's
                              range of s3 = the body, [4096, 2 ^ 47 - 512]); body + 7; the check B#20 (load1 of
                              body[7], token executor, Bx = s4 = x20, the obligation from pf_seg_B7_d.v
                              b7_addr_buf); lbu body[7]; beq s11 (TAB) / bne s8 (SP): neither -> UNK 0x88508
                              with r_header = F_unknown (b7_hdr_unknown, right disjunct);
     0x8878c                  jal trim(body + 7) (PaNoChain.cl_callS_wide, premises pf_seg_B7_s.v
                              b7_trim_site_8878c, the frame chain pf_seg_B7_ch.v b7_chain; trim's footprint is
                              its NUL inside buf, owned through the class-5 frame (awr_byte's in_frames arm));
     0x88790 .. 0x887b4       s7 = the name; the check B#21 (load1 of *name); lbu *name; s3 = 32; beqz -> NONAME
                              0x88c88 (b7_hdr_noname); jal strlen (PaArt.aj_art_at with ASTRLEN, premises
                              pf_seg_B7_r.v b7_strlen_pre_887b4);
     0x887b8 .. 0x887c8       bltu |name|,16 -> SEG 0x88ca0 (b7_hdr_get = pf_seg_step), else a2 = .str.9
                              (listing object 49, 0x21560 = seg_litA_rc F_toolong), a4 = 15 -> REFTL 0x887cc
                              (b7_hdr_toolong; the counter room after the line from pf_cnt and pf_next_skipn_lt).
   The check stubs 0x89028 .. 0x89030 and 0x89064 .. 0x8906c are the slow arms the token executor reads; their
   error calls 0x892a4 / 0x892b4 are never reached. One trap (T19), two checks (B#20, B#21), two calls (trim,
   strlen) of the segment's eight.
   The cut facts after each step: pf_seg_B7_k.v's b7k_base_move / b7k_keeps_low (runs and strlen write nothing
   below s1 outside the callee's window); after trim, b7kw_base_move_e, the same rebuild with the frame
   agreement weakened at trim's one byte. Section hypotheses: VRO, SSPX (b7k_base_move), SIGP (trim's call target),
   OBJ (the .str.9 object atom), TL (the errno cell aj_art_at keeps apart), TRIM, ASTRLEN.
   ADAPTED from the image-A G3 walk owner's image-A A7 segment lane lib/A/Prog/pf_a7_w3_k.v (the pure spine, a7_ / w3_ ->
   b7kw_) and pf_a7_w3_c.v (the trim step), and from the proved image-B pieces lib/B/Prog/pf_seg_B10b_j.v and
   pf_seg_B5_r2.v (seed, run, branch, cut rebuild), trim_l.v / trim_s.v (the token executor's check and byte
   region, the interceptor call), pf_seg_B9_s1.v and lib/B/Prog/reac_segconf_parse.v (the program call). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI08 YI09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0d_tail.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0p YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtString.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun PaArt PaFx PaNoChain PaSB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c trim_c reac_segconf_parse_file_c
SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_pieces pf_seg_B7_f pf_seg_B7_d
pf_seg_B7_r pf_seg_B7_s pf_seg_B7_k pf_seg_B7_m pf_seg_B7_ch.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require reac_segconf_parse.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(** ** The pcs of the piece, as listing offsets (BASE + AF_reac_segconf_parse_file = 0x87e38) *)
Definition B7KW_TRIM : Z := AF_reac_segconf_parse_file + 0x954.   (* 0x8878c, jal trim *)
Definition B7KW_NAME : Z := AF_reac_segconf_parse_file + 0x958.   (* 0x88790, trim's return *)
Definition B7KW_BNE : Z := AF_reac_segconf_parse_file + 0x950.    (* 0x88788, the second blank test *)
Definition B7KW_LEN : Z := AF_reac_segconf_parse_file + 0x980.    (* 0x887b8, strlen's return + 4 *)
Lemma b7kw_pcs :
  seg_text + B7_KWOK = 0x88764 /\ seg_text + B7KW_TRIM = 0x8878c /\ seg_text + B7KW_NAME = 0x88790 /\
  seg_text + B7KW_LEN = 0x887b8 /\ seg_text + PF_SEG = 0x88ca0 /\ seg_text + PF_REFTL = 0x887cc /\
  seg_text + B7_UNK = 0x88508 /\ seg_text + B7_NONAME = 0x88c88.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** ** 1. The pure spine (the image-A G3 walk owner's image-A A7 segment lane lib/A/Prog/pf_a7_w3_k.v, a7_ / w3_ -> b7kw_) *)
Lemma b7kw_nth_skipn : forall (l : list Z) k j, nth j (skipn k l) 0 = nth (k + j) l 0.
Proof.
  induction l as [|x l IH]; intros [|k] j; cbn; try reflexivity.
  - destruct j; reflexivity.
  - apply IH.
Qed.

Lemma b7kw_nul7 : forall body, ~ In 0 body -> ~ In 0 (skipn 7 body).
Proof. intros body H. exact (nulfree_skipn 7 body H). Qed.

Lemma b7kw_name_facts : forall body, ~ In 0 body ->
  (seg_spec.trim_lead (skipn 7 body) + length (b7_name body) <= length (skipn 7 body))%nat /\
  b7_name body = firstn (length (b7_name body)) (skipn (seg_spec.trim_lead (skipn 7 body)) (skipn 7 body)) /\
  ~ In 0 (b7_name body).
Proof. intros body H. unfold b7_name. exact (L_trim_holds (skipn 7 body) (b7kw_nul7 body H)). Qed.

Lemma b7kw_name_nth : forall body i, ~ In 0 body -> (i < length (b7_name body))%nat ->
  nth i (b7_name body) 0 = nth (7 + (seg_spec.trim_lead (skipn 7 body) + i)) body 0.
Proof.
  intros body i H Hi. destruct (b7kw_name_facts body H) as (_ & HE & _).
  rewrite HE at 1. rewrite nth_firstn.
  destruct (Nat.ltb_spec i (length (b7_name body))) as [_|]; [|lia].
  rewrite !b7kw_nth_skipn. reflexivity.
Qed.

(** the name's address: the body's, plus the keyword, plus the blanks trim skips *)
Definition b7kw_np (bp : Z) (body : list Z) : Z := bp + 7 + Z.of_nat (seg_spec.trim_lead (skipn 7 body)).

Lemma b7kw_zs_nth : forall (rd : reader) p (s : list Z) i, sa_zs rd p (s ++ [0]) -> (i <= length s)%nat ->
  rd (p + Z.of_nat i) = Some (nth i s 0).
Proof.
  intros rd p s i H Hi. rewrite (H i) by (rewrite length_app; cbn [length]; lia).
  destruct (Nat.lt_ge_cases i (length s)) as [Hl|Hg].
  - rewrite app_nth1 by exact Hl. reflexivity.
  - assert (i = length s) as -> by lia. rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth].
    rewrite nth_overflow by lia. reflexivity.
Qed.

Lemma b7kw_zb_nth_lt : forall (l : list Z) i, (i < length l)%nat ->
  nth i (seg_spec.zb l ++ [seg_spec.ZERO]) ZB0 = Z_to_bv 8 (nth i l 0).
Proof.
  intros l i Hi. unfold seg_spec.zb. rewrite app_nth1 by (rewrite length_map; exact Hi).
  change ZB0 with (Z_to_bv 8 0). apply map_nth.
Qed.
Lemma b7kw_zb_nth_end : forall (l : list Z) i, length l = i ->
  nth i (seg_spec.zb l ++ [seg_spec.ZERO]) ZB0 = seg_spec.ZERO.
Proof.
  intros l i Hi. unfold seg_spec.zb. rewrite app_nth2 by (rewrite length_map; lia).
  rewrite length_map, Hi, Nat.sub_diag. reflexivity.
Qed.

(** body[7], the byte 0x88780 loads (the body's NUL when the body is the bare keyword) *)
Lemma b7kw_byte7 : forall (rd : reader) bp body, sa_str rd bp body -> (7 <= length body)%nat ->
  rd (bp + 7) = Some (nth 7 body 0).
Proof.
  intros rd bp body ((HZ & _) & _) H7. pose proof (b7kw_zs_nth rd bp body 7 HZ H7) as E.
  change (Z.of_nat 7) with 7 in E. exact E.
Qed.

(** the C string trim gets at 0x8878c: the body from byte 7 on, with the body's own NUL and slack *)
Lemma b7kw_skip7_str : forall (rd : reader) bp body, sa_str rd bp body -> (7 <= length body)%nat ->
  sa_str rd (bp + 7) (skipn 7 body).
Proof.
  intros rd bp body ((HZ & HN) & HT) H7. split; [split|].
  - intros i Hi. rewrite length_app, length_skipn in Hi; cbn [length] in Hi.
    replace (bp + 7 + Z.of_nat i) with (bp + Z.of_nat (7 + i)) by lia.
    rewrite (b7kw_zs_nth rd bp body (7 + i) HZ) by lia. f_equal.
    destruct (Nat.lt_ge_cases i (length (skipn 7 body))) as [Hl|Hg].
    + rewrite app_nth1 by exact Hl. rewrite b7kw_nth_skipn. reflexivity.
    + rewrite length_skipn in Hg. rewrite app_nth2 by (rewrite length_skipn; lia).
      rewrite length_skipn. assert (Hi' : i = (length body - 7)%nat) by lia. subst i.
      rewrite Nat.sub_diag. cbn [nth]. rewrite nth_overflow by lia. reflexivity.
  - exact (b7kw_nul7 body HN).
  - rewrite length_skipn. replace (bp + 7 + Z.of_nat (length body - 7)) with (bp + Z.of_nat (length body)) by lia.
    exact HT.
Qed.

(** the name after trim(body + 7): its bytes and NUL are trim's post; the bytes after the NUL up to the next
    8-byte boundary are the body's own bytes or its slack, which trim did not write (KEEP) *)
Lemma b7kw_name_str : forall segs H mem H' mem' bp body,
  sa_str (aview segs H mem) bp body -> (7 <= length body)%nat ->
  sa_bytes (aview segs H' mem') (bp + 7)
    (seg_spec.zb (firstn (seg_spec.trim_lead (skipn 7 body) + length (r_trim (skipn 7 body))) (skipn 7 body)) ++
     [seg_spec.ZERO]) ->
  (forall a, b7kw_np bp body + Z.of_nat (length (b7_name body)) < a ->
     a < bp + Z.of_nat (length body) - (bp + Z.of_nat (length body)) mod 8 + 8 ->
     aview segs H' mem' a = aview segs H mem a) ->
  sa_str (aview segs H' mem') (b7kw_np bp body) (b7_name body).
Proof.
  intros segs H mem H' mem' bp body HS H7 HB HK.
  change (r_trim (skipn 7 body)) with (b7_name body) in HB.
  pose proof HS as ((HZ & HN) & HT).
  destruct (b7kw_name_facts body HN) as (HL & _ & HNN).
  rewrite length_skipn in HL.
  unfold b7kw_np in *.
  set (lead := seg_spec.trim_lead (skipn 7 body)) in *.
  set (nm := b7_name body) in *.
  assert (HR : forall j, (j <= length body)%nat -> 0 <= nth j body 0 < 256).
  { intros j Hj. exact (sa_aview_rng _ _ _ _ _ (b7kw_zs_nth _ bp body j HZ Hj)). }
  assert (HBL : length (seg_spec.zb (firstn (lead + length nm) (skipn 7 body)) ++ [seg_spec.ZERO]) =
                S (lead + length nm)).
  { unfold seg_spec.zb. rewrite length_app, length_map, length_firstn, length_skipn. cbn [length]. lia. }
  split; [split|].
  - intros i Hi. rewrite length_app in Hi; cbn [length] in Hi.
    replace (bp + 7 + Z.of_nat lead + Z.of_nat i) with (bp + 7 + Z.of_nat (lead + i)) by lia.
    rewrite (HB (lead + i)%nat) by (rewrite HBL; lia). f_equal.
    destruct (Nat.lt_ge_cases i (length nm)) as [Hl | Hg].
    + rewrite (b7kw_zb_nth_lt _ (lead + i)) by (rewrite length_firstn, length_skipn; lia).
      rewrite nth_firstn.
      destruct (Nat.ltb_spec (lead + i) (lead + length nm)) as [_|]; [|lia].
      rewrite b7kw_nth_skipn. rewrite (app_nth1 nm [0] 0 Hl).
      subst nm. rewrite (b7kw_name_nth body i HN Hl). fold lead.
      rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. apply HR. lia.
    + assert (Hi' : i = length nm) by lia. subst i.
      rewrite (b7kw_zb_nth_end _ (lead + length nm)) by (rewrite length_firstn, length_skipn; lia).
      rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
  - exact HNN.
  - intros x Hx.
    set (e := bp + 7 + Z.of_nat lead + Z.of_nat (length nm)) in *.
    set (EE := bp + Z.of_nat (length body)) in *.
    assert (HeE : e <= EE) by (subst e EE; lia).
    pose proof (Z.div_mod e 8 ltac:(lia)) as De. pose proof (Z.mod_pos_bound e 8 ltac:(lia)) as Me.
    pose proof (Z.div_mod EE 8 ltac:(lia)) as DE. pose proof (Z.mod_pos_bound EE 8 ltac:(lia)) as ME.
    pose proof (Z.div_le_mono e EE 8 ltac:(lia) HeE) as Dm.
    rewrite HK by lia.
    destruct (Z_le_gt_dec x EE) as [Hle | Hgt].
    + replace x with (bp + Z.of_nat (Z.to_nat (x - bp))) by lia.
      rewrite (b7kw_zs_nth _ bp body (Z.to_nat (x - bp)) HZ) by lia. discriminate.
    + unfold sa_tail in HT. apply HT. lia.
Qed.

(** name[0], the byte 0x887a4 loads: hd0 name (the name's NUL when it is empty) *)
Lemma b7kw_name_hd : forall (rd : reader) np nm, sa_str rd np nm -> rd np = Some (hd0 nm).
Proof.
  intros rd np nm ((HZ & _) & _). pose proof (b7kw_zs_nth rd np nm 0 HZ ltac:(lia)) as E.
  change (Z.of_nat 0) with 0 in E. rewrite Z.add_0_r in E. rewrite E. destruct nm; reflexivity.
Qed.

(** the name stays in buf *)
Lemma b7kw_name_inb : forall b bp body, pf_inb b bp body -> ~ In 0 body -> (7 <= length body)%nat ->
  pf_inb b (b7kw_np bp body) (b7_name body).
Proof.
  intros b bp body [H1 H2] HN H7. destruct (b7kw_name_facts body HN) as (HL & _).
  rewrite length_skipn in HL. unfold pf_inb, b7kw_np. lia.
Qed.

Lemma b7kw_name_len : forall nm, hd0 nm <> 0 -> (length nm < 16)%nat -> (1 <= length nm <= 15)%nat.
Proof. intros [|x nm] H1 H2; cbn in *; [lia | lia]. Qed.

(** ** 2. The step of each exit (the r_header equations of pf_seg_B7_f.v) *)
Section post.
Variables (rcf : rconf) (nm : list Z) (ln : Z) (l : list Z) (ci : nat).
Hypothesis HCL : strchr l RBR = Some ci.
Hypothesis HNUL : nth (S ci) l 0 = 0.

Lemma b7kw_post_unk : nth 7 (b7_body l ci) 0 <> 32 -> nth 7 (b7_body l ci) 0 <> 9 ->
  r_header rcf nm ln l = (refuse rcf ln F_unknown [AS (b7_body l ci)], None, nm).
Proof.
  intros H1 H2. apply (b7_hdr_unknown rcf nm ln l ci HCL HNUL). right. exact (b7_sp_tab_false _ H1 H2).
Qed.

Hypothesis HKW : strncasecmp (b7_body l ci) S_segment 7 = 0.

Lemma b7kw_post_noname : nth 7 (b7_body l ci) 0 = 32 \/ nth 7 (b7_body l ci) 0 = 9 ->
  hd0 (b7_name (b7_body l ci)) = 0 ->
  r_header rcf nm ln l = (refuse rcf ln F_noname [], None, nm).
Proof. intros H1 H2. exact (b7_hdr_noname rcf nm ln l ci HCL HNUL HKW (b7_sp_tab_true _ H1) H2). Qed.

Lemma b7kw_post_toolong : nth 7 (b7_body l ci) 0 = 32 \/ nth 7 (b7_body l ci) 0 = 9 ->
  hd0 (b7_name (b7_body l ci)) <> 0 -> (16 <= length (b7_name (b7_body l ci)))%nat ->
  r_header rcf nm ln l = (refuse rcf ln F_toolong [AS (b7_name (b7_body l ci)); AI 15], None, nm).
Proof.
  intros H1 H2 H3. apply (b7_hdr_toolong rcf nm ln l ci HCL HNUL HKW (b7_sp_tab_true _ H1) H2).
  rewrite b7_strlen_name. exact H3.
Qed.

Lemma b7kw_post_seg : nth 7 (b7_body l ci) 0 = 32 \/ nth 7 (b7_body l ci) 0 = 9 ->
  hd0 (b7_name (b7_body l ci)) <> 0 -> (length (b7_name (b7_body l ci)) < 16)%nat ->
  r_header rcf nm ln l = pf_seg_step rcf nm ln (b7_name (b7_body l ci)).
Proof.
  intros H1 H2 H3. rewrite <- b7_get_is_seg_step.
  apply (b7_hdr_get rcf nm ln l ci HCL HNUL HKW (b7_sp_tab_true _ H1) H2).
  rewrite b7_strlen_name. exact H3.
Qed.
End post.

(** ** 3. Small tools of the walk (lib/B/Prog/pf_seg_B10b_j.v, pf_seg_B5_r2.v) *)
Lemma b7kw_rg : forall rX L r z, pf_rg rX L -> In (r, z) L -> getr rX (Z_to_bv 5 r) = w64 z.
Proof. intros rX L r z H Hin. exact (proj1 (Forall_forall _ _) H (r, z) Hin). Qed.
Lemma b7kw_rg_app : forall rX L1 L2, pf_rg rX (L1 ++ L2) <-> pf_rg rX L1 /\ pf_rg rX L2.
Proof. intros rX L1 L2. unfold pf_rg. apply Forall_app. Qed.
Ltac b7kw_in := cbn [In app]; repeat first [left; reflexivity | right].
Ltac b7kw_clear_md := repeat match goal with |- context [with_vm_backing (m_vm_lazy ?m) ?x ?m] =>
  let mdv := fresh "mdv" in set (mdv := with_vm_backing (m_vm_lazy m) x m) in *; clearbody mdv end.
Ltac b7kw_rreg HS :=
 lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
 lazymatch type of HS with
 | st_ok_pi _ _ ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_pi_restrict_reg Hh E ss ms r HS);
  let val := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with val
 end end.
Lemma b7kw_w64_off : forall x c, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 x) + c) = Z_to_bv 64 (x + c).
Proof.
intros x c. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
rewrite Zplus_mod_idemp_l. reflexivity.
Qed.
Ltac b7kw_den :=
  cbn [sv_denot];
  repeat match goal with H : ew ?E ?nn = Z_to_bv 64 _ |- context [ew ?E ?nn] => rewrite H end;
  rewrite ?b7kw_w64_off, ?alu64_add_lit, ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
  unfold w64; first [reflexivity | f_equal; lia].
Lemma b7kw_den_atom0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

(** the seed of a stretch that reads no byte of buf: every register its own atom, no region, no fact *)
Definition b7kw_ss0 (pc : Z) : sstate := mkSS pc sr_atoms [] None (mkFacts [] [] []).

(** the seed of a stretch that reads ONE byte of buf through a pointer register (trim_l.v's tl_regions):
    the byte is a read-only region of its own on the pointer's atom r at offset d, holding the fresh atom 32;
    the facts give the pointer's range (for the inline check's obligation), the shadow base s4 = x20 = SB
    exactly (the executor's Bx) and that the byte is a byte. *)
Definition b7kw_byte_r (r : nat) (d : Z) : YP09.region :=
  YP09.mkRegion (Some r) d (d + 1) d d [YP09.mkChunk d (CVal 1 (SOff 32 0))].
Definition b7kw_facts (r : nat) : facts :=
  mkFacts [ (r, mkAF 4096 (2 ^ 47 - 512) 0); (20%nat, mkAF SB SB 0); (32%nat, mkAF 0 255 0) ] [] [].
Definition b7kw_ss1 (pc : Z) (r : nat) (d : Z) : sstate :=
  mkSS pc sr_atoms [b7kw_byte_r r d] None (b7kw_facts r).
Lemma b7kw_byte_wf : forall r d, regions_wf [b7kw_byte_r r d] = true.
Proof.
  intros r d. assert (E1 : (d <=? d + 1) = true) by (apply Z.leb_le; lia).
  unfold regions_wf, region_wf, b7kw_byte_r, chunk_inside.
  cbn [YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks forallb YP09.c_off YP09.c_len YP09.c_val
    YP09.cv_len Z.of_N andb].
  rewrite E1, !Z.leb_refl. reflexivity.
Qed.
(** image B keeps SHADOW_OFF in s4 = x20: the shadow base of every inline check of B7 *)
Definition b7kw_Bx : sv := SOff 20 0.

Lemma b7kw_ag32 : forall (E1 E2 E3 : env), env_agree 32 E1 E2 -> env_agree 33 E2 E3 -> env_agree 32 E1 E3.
Proof.
intros E1 E2 E3 [H1 D1] [H2 D2]. split; [|congruence].
intros n Hn. rewrite (H2 n ltac:(lia)). exact (H1 n Hn).
Qed.
Lemma b7kw_ag : forall (E E' : env) n w, env_agree 33 E E' -> (n <? 33)%nat = true -> ew E n = w -> ew E' n = w.
Proof. intros E E' n w [H _] Hn Hw. apply Nat.ltb_lt in Hn. rewrite (H n Hn). exact Hw. Qed.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
Hypothesis VRO : seg_val_relro (PI := PI).
Hypothesis SIGP : seg_sig_prog (PI := PI).
Hypothesis OBJ : seg_val_objs (PI := PI).
Hypothesis SSPX : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) gotwA guardA.
Hypothesis TL : PALib B.
Hypothesis TRIM : forall fx0 : YK11.FPState, trim_contract (fx := fx0) SEGS B (BASE + AF_trim) STK_trim RLO_A RHI_A.
Hypothesis ASTRLEN : forall fx0 : YK11.FPState,
  @RtString.astrlen_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strlen).
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

Ltac b7kw_awr := lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
(** after a token run that wrote nothing: the environment agrees with E0 below 33, the memory is the seed's,
    every byte present at the seed is present (trim_s.v's ta_after) *)
Ltac b7kw_after E0 HAE KM KP :=
  let mdv := fresh "mdv" in
  set (mdv := with_vm_backing _ _ _) in *; clearbody mdv;
  lazymatch goal with
  | HS : st_ok_pi _ _ ?En _ (restrict _ ?msn), HFr : frame_of ?Eo _ (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msn)),
    HG : mem_grows (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msn)) |- _ =>
    lazymatch type of HAE with env_agree ?kk _ _ =>
    let HAEn := fresh "HAEn" in let KMn := fresh "KMn" in let KPn := fresh "KPn" in
    assert (HAEn : env_agree kk E0 En) by (env_agree_chain HAE);
    assert (KMn : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H _) (ms_mem msn) a = aview SEGS (w_H _) _ a)
      by (let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
          rewrite (kept_of_frame (segs := SEGS) Eo _ _ m0 (ms_mem msn) (fun _ => False) HFr);
          [ exact (KM a Ha)
          | let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a' := fresh "a'" in
            let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in
            intros b wlo whi a' Hin Hrr; vm_compute in Hin;
            repeat (let Hq := fresh "Hq" in destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia |]);
            destruct Hin
          | exact Ha | tauto ]);
    assert (KPn : forall a, apresent (w_H _) _ a -> apresent (w_H _) (ms_mem msn) a)
      by (let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; exact (apresent_grows _ _ _ a HG (KP a Ha)));
    clear HFr HG HAE KM KP; rename HAEn into HAE; rename KMn into KM; rename KPn into KP;
    repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end
    end
  end.


(** the listing object of .str.9 (0x21560 = seg_litA_rc F_toolong), index 49 of SegAddr.seg_objs *)
Lemma b7kw_lit_toolong : forall E, img_env VAL A_LIM E -> ew E 290%nat = w64 (seg_litA_rc F_toolong).
Proof.
intros E HE. rewrite (img_env_atomP E 290%nat HE) by (unfold A_TEXT, A_LIM; lia).
change 290%nat with (A_OBJ 49). rewrite (OBJ 49%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)).
vm_compute. reflexivity.
Qed.

Section x. Context {fx : YK11.FPState}.
Let RUNP := SRr_run_pi_AJ (fx := fx) B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ (fx := fx) B LAWS.
Let RUNC := SRr_run_pi_AJ_call (fx := fx) B LAWS.
Let RUN := paj_run (fx := fx) B LAWS.
Let RUNTO := paj_run_to (fx := fx) B LAWS.
Let BR := paj_branch (PI := PI).

(** the part of a cut that pf_seg_B7_d.v's b7_st names, out of pf_base *)
Lemma b7kw_st_of_base : forall v pos lyc Sc Wc rX memc mdc,
  pf_base (fx := fx) B v pos lyc Sc Wc rX memc mdc PF_SC_LINE -> b7_st B v pos lyc Sc Wc memc mdc.
Proof.
intros v pos lyc Sc Wc rX memc mdc (HCX & (HJ & Hly & _ & Hperm & _) & HOBJ & _ & HFSH).
constructor; [exact HCX | exact HJ | exact Hly | exact Hperm | exact HOBJ | exact HFSH].
Qed.

(** the seed of a no-byte stretch *)
Lemma b7kw_seed0 : forall (Wc : world SEGS) (rX : bvmap 5 word) memc pc,
  st_ok_pi SEGS VAL (Eimg (Ereg rX [])) (b7kw_ss0 pc)
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))).
Proof.
intros Wc rX memc pc. rewrite restrict_mkst_fx. unfold b7kw_ss0. apply pa_entry_st_ok_full;
  [apply regs_ok_Eimg_Ereg | vm_compute; reflexivity | constructor | cbn; tauto
  | split; [exact I | split; exact I]].
Qed.

(** the seed of a stretch that reads one byte of buf through the pointer register r at offset d *)
Lemma b7kw_seed1 : forall v pos lyc Sc (Wc : world SEGS) rX memc mdc pc (r : nat) (rb : bv 5) q d z,
  pf_base (fx := fx) B v pos lyc Sc Wc rX memc mdc PF_SC_LINE ->
  Z.of_nat r = bv_unsigned rb -> getr rX rb = w64 q ->
  4096 <= q -> q + 512 <= 2 ^ 47 -> 0 <= d < 512 ->
  rdW Wc memc (q + d) = Some z ->
  st_ok_pi SEGS VAL (Eimg (Ereg rX [Z_to_bv 64 z])) (b7kw_ss1 pc r d)
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))).
Proof.
intros v pos lyc Sc Wc rX memc mdc pc r rb q d z HB Hrb Hq Hq0 Hq47 Hd Hz.
pose proof HB as (_ & HFI & _).
pose proof HFI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HRG0).
assert (R20 : getr rX (Z_to_bv 5 20) = w64 SHADOW_OFF) by (apply (b7kw_rg rX _ 20 _ HRG0); b7kw_in).
pose proof (sa_aview_rng _ _ _ _ _ Hz) as Hz255.
destruct (aview_byte SEGS (w_H Wc) memc (q + d) z Hz) as (b & Hb & Hzb & _).
set (E := Eimg (Ereg rX [Z_to_bv 64 z])).
assert (EE : forall k (rr : bv 5), Z.of_nat k = bv_unsigned rr -> ew E k = getr rX rr)
  by (intros k rr Hk; subst E; apply ew_Eimg_Ereg_nat; exact Hk).
assert (Er : bv_unsigned (ew E r) = q)
  by (rewrite (EE r rb Hrb), Hq; unfold w64; apply unsigned_lit_small; lia).
assert (E20 : bv_unsigned (ew E 20) = SHADOW_OFF)
  by (rewrite (EE 20%nat (Z_to_bv 5 20) eq_refl), R20; unfold w64; apply unsigned_lit_small;
      unfold SHADOW_OFF; lia).
assert (E32 : bv_unsigned (ew E 32) = z).
{ subst E. rewrite Eimg_low by (unfold A_TEXT; lia).
  change 32%nat with (32 + 0)%nat. rewrite (ew_Ereg_extra rX [Z_to_bv 64 z] 0). cbn [nth].
  apply unsigned_lit_small. lia. }
rewrite restrict_mkst_fx. unfold b7kw_ss1. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- apply b7kw_byte_wf.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok, b7kw_byte_r.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite Er. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  unfold YP09.chunk_ok, YP09.c_len, YP09.cv_len. cbn [YP09.c_off YP09.c_val Z.of_N].
  intros i Hi. assert (i = 0) as -> by lia. exists b. split.
  + cbn [YP09.cbyte]. f_equal. unfold YP09.byte_of_word. cbn [sv_denot].
    rewrite !Z.add_0_r, Z_to_bv_bv_unsigned, E32.
    change (8 * 0) with 0. rewrite Z.shiftr_0_r, Hzb. apply Z_to_bv_bv_unsigned.
  + cbn [Z.of_nat]. rewrite !Z.add_0_r. exact Hb.
- cbn. tauto.
- split; [|split; exact I].
  cbn [b7kw_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Er, E20, E32. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB, SHADOW_OFF. repeat split; lia.
Qed.

(** pf_base at the same frame state after a run or a call that kept every byte *)
Lemma b7kw_base_same : forall v pos lyc Sc Wc rX memc mdc sc rX' memc' mdc',
  pf_base (fx := fx) B v pos lyc Sc Wc rX memc mdc sc ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc' mdc' 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> a < alloc_ceiling \/ pf_s1 v <= a -> rdW Wc memc' a = rdW Wc memc a) ->
  (forall r, In r [2; 3; 4; 8; 9; 20] -> getr rX' (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)) ->
  pf_base (fx := fx) B v pos lyc Sc Wc rX' memc' mdc' sc.
Proof.
intros v pos lyc Sc Wc rX memc mdc sc rX' memc' mdc' HB HJ' KM KR.
exact (b7k_base_move B VRO SSPX fx v pos lyc Sc Wc rX memc mdc sc lyc Sc Wc rX' memc' mdc' HB (fxrel_refl fx) HJ'
  eq_refl ltac:(exists (st_fs Sc); destruct Sc; reflexivity) (Permutation_refl _)
  (b7k_keeps_low B v pos lyc Sc Wc rX memc mdc sc Wc memc' HB KM) KR).
Qed.

(** pf_base after a call that wrote ONE byte e of buf besides its own window below s1 (trim's NUL): the kit's
    b7k_base_move with its fourth agreement weakened at e. The proof is pf_seg_B7_k.v's b7k_base_move, which uses
    that agreement twice only: at the frame's flag word (F + 2040 .. F + 2047) and at the frame's 144 shadow
    cells, both apart from buf. *)
Definition b7kw_keeps_e (v : pfv) (pos : Z) (Wc : world SEGS) memc (W2 : world SEGS) mem2 (e : Z) : Prop :=
  (forall a, pf_s1 v <= a < 2 ^ 64 -> rdW W2 mem2 a = rdW Wc memc a) /\
  (forall i, 0 <= i <= Z.of_nat (length (p_s v)) -> rdW W2 mem2 (p_t v + i) = rdW Wc memc (p_t v + i)) /\
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     rdW W2 mem2 a = rdW Wc memc a) /\
  (forall a, (pf_F v pos <= a < pf_F v pos + fs_frame_bytes 5 \/
              pf_SH v pos <= a < pf_SH v pos + fs_frame_bytes 5 / 8) -> a <> e ->
     rdW W2 mem2 a = rdW Wc memc a).

Lemma b7kw_base_move_e : forall (fx1 : YK11.FPState) v pos lyc Sc Wc rX memc mdc ly2 S2 (W2 : world SEGS) regs2
  mem2 md2 e,
  pf_base (fx := fx) B v pos lyc Sc Wc rX memc mdc PF_SC_LINE ->
  fxrel fx fx1 ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] ly2 S2 W2 mem2 md2 0 ->
  ly2 = lyc -> (exists f, S2 = set_fs f Sc) -> Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
  b7_buf v pos <= e < b7_buf v pos + 512 ->
  b7kw_keeps_e v pos Wc memc W2 mem2 e ->
  (forall r, In r [2; 3; 4; 8; 9; 20] -> getr regs2 (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)) ->
  pf_base (fx := fx1) B v pos ly2 S2 W2 regs2 mem2 md2 PF_SC_LINE.
Proof.
intros fx1 v pos lyc Sc Wc rX memc mdc ly2 S2 W2 regs2 mem2 md2 e HB Hfx HJ2 Hly2 HS2e HP2 He (K1 & K2 & K3 & K4) KR.
pose proof HB as (CX & FI & OBJx & SL & FSH).
destruct HS2e as (f2 & HS2).
destruct (b7k_cx B v CX) as (Hc0 & Hc16 & HLS & HDJ & Hceil & Hslo & H47 & Hsp16).
destruct (b7k_frame B v pos lyc Sc Wc rX memc mdc FI) as (Hfin & HF4 & HFc & HF32 & HFapp & HFE).
pose proof (b7k_s1 (pf_sp0 v) Hsp16) as (S1a & S1b & S1c & S1d). rewrite <- b7k_s1_eq in S1a, S1b, S1c, S1d.
destruct FI as (HJ & Hly & (f & HSf) & HPerm & HSV & HFLW & HFRM & HTF & HC8 & HRG).
destruct OBJx as (STR & AT & HT & ACx & HC & CAT & LITS & ROD & SSP).
pose proof (proj1 HJ2) as HAR2. pose proof (proj1 HJ) as HAR.
pose proof alloc_ceiling_lt as Hac.
pose proof asan_consts as (AC1 & AC2 & AC3 & AC4 & AC5).
assert (E5 : fs_frame_bytes 5 = 2048) by reflexivity.
unfold b7_buf, PF_O_BUF in He.
(* the one written byte is neither the flag word nor a shadow cell of the frame *)
assert (HSHe : forall i, 0 <= i < 144 -> pf_SH v pos + i <> e).
{ intros i Hi HEq.
  pose proof (Z.div_lt_upper_bound (pf_F v pos) 8 (2 ^ 44 - 256) ltac:(lia) ltac:(lia)).
  pose proof (Z.div_pos (pf_F v pos) 8 ltac:(lia) ltac:(lia)).
  apply (b7k_band_not_app (pf_F v pos) 2048 (pf_SH v pos + i));
    [rewrite E5 in HFapp; exact HFapp | unfold pf_SH, shadow_addr, SHADOW_OFF; lia | lia]. }
split; [exact CX|].
split.
{ split; [exact HJ2|]. split; [rewrite Hly2; exact Hly|].
  split; [exists f2; rewrite HS2, HSf; reflexivity|].
  split; [exact (Permutation_trans HP2 HPerm)|].
  split.
  { intros j r Hj. rewrite <- (HSV j r Hj). apply rdword_ext. intros k Hk.
    pose proof (proj1 (nth_error_Some PF_SAVED j) ltac:(rewrite Hj; discriminate)) as Hj13.
    unfold PF_SAVED in Hj13. cbn [length] in Hj13.
    apply K1. lia. }
  split.
  { rewrite <- HFLW. apply rdword_ext. intros k Hk. apply K4; [left; lia | lia]. }
  split; [exact (fxrel_frm0 fx fx1 HFRM Hfx)|].
  split; [exact HTF|].
  split.
  { apply (b7k_sl_move (rdW Wc memc) (rdW W2 mem2) (pf_s1 v) [(0xc8, p_c v)] HC8);
      [apply Forall_cons; [cbn [fst]; lia | apply Forall_nil] | lia | lia |].
    intros a Ha. apply K1. exact Ha. }
  unfold pf_rg in *. rewrite Forall_forall in HRG |- *. intros rv Hin.
  rewrite (KR (fst rv)); [exact (HRG rv Hin)|].
  cbn [In] in Hin. repeat (destruct Hin as [<- | Hin]; [cbn [fst In]; tauto|]). destruct Hin. }
split.
{ destruct (b7k_heap_bounds B lyc Sc Wc memc mdc (p_t v) (Z.of_nat (length (p_s v)) + 1) HAR HT ltac:(lia))
    as (bt & mt & Hint & Hbt1 & Hbt2 & _ & _ & _).
  assert (HT2 : sa_heap B ly2 S2 (p_t v) (Z.of_nat (length (p_s v)) + 1))
    by exact (b7k_heap_perm B _ _ _ _ _ _ HP2 HT).
  assert (HC2 : sa_heap B ly2 S2 (p_c v) seg_spec.SEG_C_SIZE) by exact (b7k_heap_perm B _ _ _ _ _ _ HP2 HC).
  split.
  { destruct STR as ((Hz & Hn) & _). split; [split; [|exact Hn]|].
    - intros i Hi. pose proof Hi as Hl. rewrite length_app in Hl. cbn [length] in Hl.
      rewrite K2 by lia. exact (Hz i Hi).
    - intros x Hx. apply (AR_block_word_vis SEGS B ly2 S2 W2 mem2 md2 bt mt
        (p_t v + Z.of_nat (length (p_s v))) x HAR2).
      + exact (Permutation_in _ (Permutation_sym HP2) Hint).
      + lia.
      + lia. }
  split; [exact (b7k_heap_addr B ly2 S2 W2 mem2 md2 _ _ HAR2 HT2 ltac:(lia))|].
  split; [exact HT2|].
  split; [exact (b7k_heap_addr B ly2 S2 W2 mem2 md2 _ _ HAR2 HC2 ltac:(unfold seg_spec.SEG_C_SIZE; lia))|].
  split; [exact HC2|].
  split; [exact (b7k_cat_move B _ W2 mem2 CAT K3)|].
  split; [intros x Hx; exact (b7k_lit_move B _ W2 mem2 _ _ (LITS x Hx) K3)|].
  split; [intros a Hro Ho Hee; rewrite (K3 a (b7k_in_roP_img VRO a Hro) Ho Hee); exact (ROD a Hro Ho Hee)|].
  exact (SSPX ly2 S2 W2 mem2 md2 HAR2). }
split.
{ apply (b7k_sl_move (rdW Wc memc) _ (pf_s1 v) _ SL (b7k_PF_SL_offs v pos)); [lia | lia |].
  intros a Ha. apply K1. exact Ha. }
intros i Hi. rewrite K4; [exact (FSH i Hi) | right; rewrite E5; change (2048 / 8) with 256; lia |].
exact (HSHe i Hi).
Qed.

(** where the block c lies, and that it does not meet the class-5 frame *)
Lemma b7kw_c_rng : forall v pos lyc Sc Wc memc mdc, b7_st B v pos lyc Sc Wc memc mdc ->
  4096 <= p_c v /\ p_c v + seg_spec.SEG_C_SIZE <= alloc_ceiling /\
  (p_c v + seg_spec.SEG_C_SIZE <= pf_F v pos \/ pf_F v pos + 2048 <= p_c v).
Proof.
intros v pos lyc Sc Wc memc mdc H.
pose proof (b7_AR B v pos lyc Sc Wc memc mdc H) as HAR.
pose proof (b7_fin B v pos lyc Sc Wc memc mdc H) as Hfin.
pose proof H as [_ _ HLY _ HOBJ _].
destruct HOBJ as (_ & _ & _ & _ & (b & m & Hin & Hb & Hm) & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hin) as (_ & H4096 & Hceil & _ & _ & _ & Hmm).
pose proof (req_size_pos m ltac:(unfold seg_spec.SEG_C_SIZE in Hm; lia)) as [_ Hrq].
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ b m 5 pos HAR Hin Hfin) as Hsep.
unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. rewrite b7_fb5 in Hsep.
replace (frame_addr lyc 5 pos) with (pf_F v pos) in Hsep by (unfold pf_F; rewrite HLY; reflexivity).
unfold seg_spec.SEG_C_SIZE in *.
split; [lia|]. split; [lia|]. lia.
Qed.

(** pf_st0 at a later state: c's bytes and cur_name are below the ceiling, off buf *)
Lemma b7kw_st0_keep : forall v pos lyc Sc Wc memc mdc (rd' : reader) cf nm k e,
  b7_st B v pos lyc Sc Wc memc mdc ->
  b7_buf v pos <= e < b7_buf v pos + 512 ->
  (forall a, 0 <= a < alloc_ceiling -> a <> e -> rd' a = rdW Wc memc a) ->
  pf_st0 v pos (rdW Wc memc) cf nm k -> pf_st0 v pos rd' cf nm k.
Proof.
intros v pos lyc Sc Wc memc mdc rd' cf nm k e H He KM (HRC & HNM & HCNT).
destruct (b7kw_c_rng v pos lyc Sc Wc memc mdc H) as (Hc1 & Hc2 & Hc3).
destruct (b7_frame_rng B v pos lyc Sc Wc memc mdc H) as (F1 & F2 & _ & _).
unfold b7_buf, PF_O_BUF in He.
split; [|split; [|exact HCNT]].
- destruct HRC as (bs & Hb & Henc). exists bs. split; [|exact Henc].
  intros i Hi. destruct Henc as [Hl _].
  rewrite KM; [exact (Hb i Hi) | unfold seg_spec.SEG_C_SIZE in *; lia | unfold seg_spec.SEG_C_SIZE in *; lia].
- destruct HNM as (f & Hf & Hfe). exists f. split; [|exact Hfe].
  intros i Hi. pose proof Hi as Hi2. destruct Hfe as [Hl _]. rewrite Hl in Hi2. unfold PF_O_CN.
  rewrite KM; [exact (Hf i Hi) | lia | lia].
Qed.

(** ** 4. The last stretch: 0x887b8 .. 0x887c8, the length test (SEG or REFTL) *)
Lemma b7kw_len : forall (n : nat) (v : pfv) pos lyc Sc (Wc : world SEGS) rX memc mdc cf nm o ln d ci np,
  HA_REFTL B n -> HA_SEG B n ->
  b7_core (fx := fx) B n v pos lyc Sc Wc rX memc mdc cf nm o ln d ->
  strchr (pf_tline (p_s v) o) RBR = Some ci ->
  nth (S ci) (pf_tline (p_s v) o) 0 = 0 ->
  strncasecmp (b7_body (pf_tline (p_s v) o) ci) S_segment 7 = 0 ->
  (nth 7 (b7_body (pf_tline (p_s v) o) ci) 0 = 32 \/ nth 7 (b7_body (pf_tline (p_s v) o) ci) 0 = 9) ->
  hd0 (b7_name (b7_body (pf_tline (p_s v) o) ci)) <> 0 ->
  sa_str (rdW Wc memc) np (b7_name (b7_body (pf_tline (p_s v) o) ci)) ->
  pf_inb (b7_buf v pos) np (b7_name (b7_body (pf_tline (p_s v) o) ci)) ->
  pf_rg rX (PF_RL v pos ++ PF_RM v o ln ++
            [(19, 32); (23, np); (10, Z.of_nat (length (b7_name (b7_body (pf_tline (p_s v) o) ci))))]) ->
  SRr SEGS Wc (cfg_at SEGS (BASE + B7KW_LEN) rX memc mdc) (b7_post (fx := fx) B v cf nm o ln).
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf nm o ln d ci np HREFTL HSEG HC HCL HNUL HKW HSP HND HSTR HINB HRG.
destruct HC as (HB & HMID & HST & HLEN & HRGc).
pose proof (b7kw_st_of_base v pos lyc Sc Wc rX memc mdc HB) as HST0.
pose proof HB as (HCX & HFI & HOBJ & HSL & HFSH).
pose proof HFI as (HJ & Hly & HSc & HPERM & HSAV & HFLAG & HFRM & HTF & HC8 & HRG0).
destruct (b7_frame_rng B v pos lyc Sc Wc memc mdc HST0) as (F1 & F2 & F3 & F4).
pose proof alloc_ceiling_lt as HAC.
set (LINE := pf_tline (p_s v) o) in *.
set (NAME := b7_name (b7_body LINE ci)) in *.
assert (HNL : (length NAME < 512)%nat)
  by (destruct HINB as [Hb1 Hb2]; unfold b7_buf, PF_O_BUF in Hb1, Hb2; lia).
assert (HNZ : 0 <= Z.of_nat (length NAME) < 2 ^ 64) by lia.
(* the registers at B7KW_LEN *)
rewrite b7kw_rg_app in HRG. destruct HRG as (HRGa & HRGb).
rewrite b7kw_rg_app in HRGb. destruct HRGb as (HRGm & HRGx).
assert (R10 : getr rX (Z_to_bv 5 10) = w64 (Z.of_nat (length NAME)))
  by (apply (b7kw_rg rX _ 10 _ HRGx); b7kw_in).
(* the seed *)
pose proof (b7kw_seed0 Wc rX memc B7KW_LEN) as HS.
set (E := Eimg (Ereg rX [])) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr rX r)
  by (intros k r Hk; subst E; apply ew_Eimg_Ereg_nat; exact Hk).
assert (E10 : ew E 10 = Z_to_bv 64 (Z.of_nat (length NAME)))
  by (rewrite (EE 10%nat (Z_to_bv 5 10) eq_refl); exact R10).
unfold cfg_at. change (w64 (BASE + B7KW_LEN)) with (Z_to_bv 64 (BASE + B7KW_LEN)).
(* 0x887b8 li a1,16, then the branch 0x887bc *)
paj_run_sh RUNP HS HJ.
{ intros a (r & Hr & _). cbn [b7kw_ss0 ss_mem In] in Hr. destruct Hr. }
cbn [ms_mem mkst] in HFr, HG, HF.
b7kw_clear_md.
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha. apply (kept_of_frame (segs := SEGS) E (ss_mem (b7kw_ss0 B7KW_LEN)) (w_H Wc) memc (ms_mem ms)
    (fun _ => False) HFr); [|exact Ha | tauto].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'. destruct Hin'. }
clear HFr HG HF.
psrr_branch_pi RUNP BR HS.
- (* taken: |NAME| < 16, to SEG 0x88ca0 *)
  assert (HLT : (length NAME < 16)%nat).
  { rewrite branch_ltu_U, (U_atom E 10 _ E10 HNZ), (U_lit E 16 ltac:(lia)) in Hc.
    apply Z.ltb_lt in Hc. lia. }
  clear Hc.
  paj_run_to_sh RUNTOP HS HJ PF_SEG.
  { intros a (r & Hr & _). cbn [add_cond b7kw_ss0 ss_mem In] in Hr.
    first [destruct Hr | vm_compute in Hr; destruct Hr]. }
  cbn [ms_mem mkst] in HFr, HG, HF.
  b7kw_clear_md.
  assert (K2 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms0) a = rdW Wc (ms_mem ms) a).
  { intros a Ha. lazymatch type of HFr with frame_of ?Ex ?rs _ _ =>
    apply (kept_of_frame (segs := SEGS) Ex rs (w_H Wc) (ms_mem ms) (ms_mem ms0) (fun _ => False) HFr);
      [|exact Ha | tauto] end.
    intros b wlo whi a' Hin' Hrr. vm_compute in Hin'. destruct Hin'. }
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms0) a = rdW Wc memc a)
    by (intros a Ha; rewrite (K2 a Ha); exact (K1 a Ha)).
  clear HFr HG HF.
  assert (QK : forall r, In r [2; 3; 4; 8; 9; 20; 18; 21; 26; 25; 22; 19; 23] ->
      getr (ms_regs ms0) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
  { intros r Hr. cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr]; [b7kw_rreg HS; rewrite b7kw_den_atom0; apply EE; reflexivity |]).
    destruct Hr. }
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?kk)) ?mm ?rom) ?mdx) _ =>
    change (mkCfg (mkst rg (Z_to_bv 64 (BASE + kk)) mm rom) mdx) with (cfg_at SEGS (BASE + PF_SEG) rg mm mdx) end.
  unfold b7_post, pf_postm.
  rewrite (b7kw_post_seg cf nm (ln + 1) (pf_tline (p_s v) o) ci HCL HNUL HKW HSP HND HLT).
  apply (HSEG fx v pos lyc Sc Wc (ms_regs ms0) (ms_mem ms0) mdv0 cf nm o ln d np NAME).
  split; [|split; [exact HMID|split; [|split; [|split; [|split]]]]].
  + apply (b7kw_base_same v pos lyc Sc Wc rX memc mdc PF_SC_LINE (ms_regs ms0) (ms_mem ms0) mdv0 HB HJ).
    * intros a Ha _. exact (KM a Ha).
    * intros r Hr. apply QK. cbn [In] in Hr |- *. tauto.
  + apply (b7kw_st0_keep v pos lyc Sc Wc memc mdc _ cf nm _ (b7_buf v pos) HST0 ltac:(lia));
      [intros a Ha _; apply KM; lia | exact HST].
  + apply (reac_segconf_parse.sa_str_low (rdW Wc memc) _ np NAME HSTR);
      [destruct HINB; unfold b7_buf, PF_O_BUF in *; lia
       |destruct HINB; unfold b7_buf, PF_O_BUF in *; lia
       |intros a Ha; apply KM; lia].
  + exact HINB.
  + exact (b7kw_name_len NAME HND HLT).
  + unfold pf_rg. rewrite !Forall_app. split; [|split].
    * unfold PF_RL. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
        (rewrite QK; [apply (b7kw_rg rX _ _ _ HRGa); b7kw_in | b7kw_in]).
    * unfold PF_RM. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
        (rewrite QK; [apply (b7kw_rg rX _ _ _ HRGm); b7kw_in | b7kw_in]).
    * repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
        (rewrite QK; [apply (b7kw_rg rX _ _ _ HRGx); b7kw_in | b7kw_in]).
- (* not taken: 16 <= |NAME|, 0x887c0 .. 0x887c8 then REFTL 0x887cc *)
  assert (HGE : (16 <= length NAME)%nat).
  { rewrite branch_ltu_U, (U_atom E 10 _ E10 HNZ), (U_lit E 16 ltac:(lia)) in Hc.
    apply Z.ltb_ge in Hc. lia. }
  clear Hc.
  paj_run_to_sh RUNTOP HS HJ PF_REFTL.
  { intros a (r & Hr & _). cbn [add_cond b7kw_ss0 ss_mem In] in Hr.
    first [destruct Hr | vm_compute in Hr; destruct Hr]. }
  cbn [ms_mem mkst] in HFr, HG, HF.
  b7kw_clear_md.
  assert (K2 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms0) a = rdW Wc (ms_mem ms) a).
  { intros a Ha. lazymatch type of HFr with frame_of ?Ex ?rs _ _ =>
    apply (kept_of_frame (segs := SEGS) Ex rs (w_H Wc) (ms_mem ms) (ms_mem ms0) (fun _ => False) HFr);
      [|exact Ha | tauto] end.
    intros b wlo whi a' Hin' Hrr. vm_compute in Hin'. destruct Hin'. }
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms0) a = rdW Wc memc a)
    by (intros a Ha; rewrite (K2 a Ha); exact (K1 a Ha)).
  clear HFr HG HF.
  assert (QK : forall r, In r [2; 3; 4; 8; 9; 20; 18; 21; 26; 25; 22; 23] ->
      getr (ms_regs ms0) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
  { intros r Hr. cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr]; [b7kw_rreg HS; rewrite b7kw_den_atom0; apply EE; reflexivity |]).
    destruct Hr. }
  assert (Q12 : getr (ms_regs ms0) (Z_to_bv 5 12) = w64 (seg_litA_rc F_toolong)).
  { b7kw_rreg HS. rewrite b7kw_den_atom0. apply b7kw_lit_toolong; exact HEI. }
  assert (Q14 : getr (ms_regs ms0) (Z_to_bv 5 14) = w64 15).
  { b7kw_rreg HS.
    first [reflexivity | vm_compute; reflexivity]. }
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?kk)) ?mm ?rom) ?mdx) _ =>
    change (mkCfg (mkst rg (Z_to_bv 64 (BASE + kk)) mm rom) mdx) with (cfg_at SEGS (BASE + PF_REFTL) rg mm mdx) end.
  unfold b7_post, pf_postm.
  rewrite (b7kw_post_toolong cf nm (ln + 1) (pf_tline (p_s v) o) ci HCL HNUL HKW HSP HND HGE).
  apply (HREFTL fx v pos lyc Sc Wc (ms_regs ms0) (ms_mem ms0) mdv0 cf nm o ln d F_toolong
           (seg_litA_rc F_toolong) 15 np NAME).
  pose proof HMID as (Ho & Hn & HCTX).
  pose proof (pf_next_skipn_lt (p_s v) o Ho) as HNX.
  pose proof HST as (HRC & HNM & HCNT).
  split; [|split; [exact HMID|split; [|split; [|split; [|split; [|split]]]]]].
  + apply (b7kw_base_same v pos lyc Sc Wc rX memc mdc PF_SC_LINE (ms_regs ms0) (ms_mem ms0) mdv0 HB HJ).
    * intros a Ha _. exact (KM a Ha).
    * intros r Hr. apply QK. cbn [In] in Hr |- *. tauto.
  + assert (HCNT2 : pf_cnt cf (length (skipn (pf_next (p_s v) o) (p_s v))))
      by (apply (pf_cnt_mono cf (length (skipn o (p_s v)))); [lia | exact HCNT]).
    apply (b7kw_st0_keep v pos lyc Sc Wc memc mdc _ cf nm _ (b7_buf v pos) HST0 ltac:(lia));
      [intros a Ha _; apply KM; lia | exact (conj HRC (conj HNM HCNT2))].
  + unfold pf_cnt in HCNT. lia.
  + split; [left; split; reflexivity | reflexivity].
  + apply (reac_segconf_parse.sa_str_low (rdW Wc memc) _ np NAME HSTR);
      [destruct HINB; unfold b7_buf, PF_O_BUF in *; lia
       |destruct HINB; unfold b7_buf, PF_O_BUF in *; lia
       |intros a Ha; apply KM; lia].
  + exact HINB.
  + unfold pf_rg. rewrite !Forall_app. split; [|split].
    * unfold PF_RL. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
        (rewrite QK; [apply (b7kw_rg rX _ _ _ HRGa); b7kw_in | b7kw_in]).
    * unfold PF_RM. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
        (rewrite QK; [apply (b7kw_rg rX _ _ _ HRGm); b7kw_in | b7kw_in]).
    * repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
        first [exact Q12 | exact Q14 | (rewrite QK; [apply (b7kw_rg rX _ _ _ HRGx); b7kw_in | b7kw_in])].
Qed.

(** ** 5. 0x88790 .. 0x887b4: s7 = the name, the check B#21 on *name, the empty-name test, strlen(name) *)
Lemma b7kw_name_stretch : forall (n : nat) (v : pfv) pos lyc Sc (Wc : world SEGS) rX memc mdc cf nm o ln d ci np,
  HA_NONAME B n -> HA_REFTL B n -> HA_SEG B n ->
  b7_core (fx := fx) B n v pos lyc Sc Wc rX memc mdc cf nm o ln d ->
  strchr (pf_tline (p_s v) o) RBR = Some ci ->
  nth (S ci) (pf_tline (p_s v) o) 0 = 0 ->
  strncasecmp (b7_body (pf_tline (p_s v) o) ci) S_segment 7 = 0 ->
  (nth 7 (b7_body (pf_tline (p_s v) o) ci) 0 = 32 \/ nth 7 (b7_body (pf_tline (p_s v) o) ci) 0 = 9) ->
  sa_str (rdW Wc memc) np (b7_name (b7_body (pf_tline (p_s v) o) ci)) ->
  pf_inb (b7_buf v pos) np (b7_name (b7_body (pf_tline (p_s v) o) ci)) ->
  getr rX (Z_to_bv 5 10) = w64 np ->
  SRr SEGS Wc (cfg_at SEGS (BASE + B7KW_NAME) rX memc mdc) (b7_post (fx := fx) B v cf nm o ln).
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf nm o ln d ci np HNONAME HREFTL HSEG HC HCL HNUL HKW HSP HSTR HINB R10.
destruct HC as (HB & HMID & HST & HLEN & HRGc).
pose proof (b7kw_st_of_base v pos lyc Sc Wc rX memc mdc HB) as HST0.
pose proof HB as (HCX & HFI & HOBJ & HSL & HFSH).
pose proof HFI as (HJ & Hly & HSc & HPERM & HSAV & HFLAG & HFRM & HTF & HC8 & HRG0).
destruct (b7_frame_rng B v pos lyc Sc Wc memc mdc HST0) as (F1 & F2 & F3 & F4).
destruct (b7_stk B v pos lyc Sc Wc memc mdc HST0) as (Hsp16 & Hceil & Hslo & Hs32 & Hs1rng & Ho16).
pose proof alloc_ceiling_lt as HAC.
pose proof asan_consts as (AC1 & AC2 & AC3 & AC4 & AC5).
destruct (b7k_cx B v HCX) as (Hc0 & Hc16 & HLS & HDJ & Hceil2 & Hslo2 & H47 & Hsp16b).
pose proof STK_values as (STR & _ & _ & SPF & _).
set (LINE := pf_tline (p_s v) o) in *.
set (NAME := b7_name (b7_body LINE ci)) in *.
pose proof HINB as [HIB1 HIB2]. unfold b7_buf, PF_O_BUF in HIB1, HIB2.
assert (HNL : (length NAME < 512)%nat) by lia.
assert (HNZ : 0 <= Z.of_nat (length NAME) < 2 ^ 64) by lia.
assert (R2 : getr rX (Z_to_bv 5 2) = w64 (pf_s1 v)) by (apply (b7kw_rg rX _ 2 _ HRG0); b7kw_in).
assert (R3 : getr rX (Z_to_bv 5 3) = w64 (as_gp B)) by (apply (b7kw_rg rX _ 3 _ HRG0); b7kw_in).
assert (R4 : getr rX (Z_to_bv 5 4) = w64 (as_tp B)) by (apply (b7kw_rg rX _ 4 _ HRG0); b7kw_in).
(* the byte *name *)
pose proof (b7kw_name_hd (rdW Wc memc) np NAME HSTR) as HB0.
pose proof (sa_aview_rng _ _ _ _ _ HB0) as HB0r.
(* the seed *)
pose proof (b7kw_seed1 v pos lyc Sc Wc rX memc mdc B7KW_NAME 10%nat (Z_to_bv 5 10) np 0 (hd0 NAME) HB
  eq_refl R10 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite Z.add_0_r; exact HB0)) as HS.
set (E0 := Eimg (Ereg rX [Z_to_bv 64 (hd0 NAME)])) in HS.
assert (HEI : img_env VAL A_LIM E0) by (subst E0; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E0 k = getr rX r)
  by (intros k r Hk; subst E0; apply ew_Eimg_Ereg_nat; exact Hk).
assert (HA0 : env_agree 32 (Ereg rX [Z_to_bv 64 (hd0 NAME)]) E0)
  by (split; [intros k Hk; subst E0; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]).
assert (E10 : ew E0 10 = Z_to_bv 64 np) by (rewrite (EE 10%nat (Z_to_bv 5 10) eq_refl); exact R10).
assert (E20 : ew E0 20 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (EE 20%nat (Z_to_bv 5 20) eq_refl); apply (b7kw_rg rX _ 20 _ HRG0); b7kw_in).
assert (E32 : ew E0 32 = Z_to_bv 64 (hd0 NAME)).
{ subst E0. rewrite Eimg_low by (unfold A_TEXT; lia).
  change 32%nat with (32 + 0)%nat. rewrite (ew_Ereg_extra rX [Z_to_bv 64 (hd0 NAME)] 0). reflexivity. }
assert (SHOK : sh_ok SEGS b7kw_Bx [] E0 (mrestrict (w_H Wc) memc)) by constructor.
pose proof (env_agree_refl 33 E0) as HAE.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc a = rdW Wc memc a) by (intros; reflexivity).
assert (KP : forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) memc a) by (intros; assumption).
unfold cfg_at. change (w64 (BASE + B7KW_NAME)) with (Z_to_bv 64 (BASE + B7KW_NAME)).
(* 0x88790 .. 0x887ac: s7 = a0, the check B#21, *name, s3 = 32, the empty test *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ cbn [ms_mem]. unfold b7kw_Bx.
  rewrite (U_atom _ 20 _ E20) by (unfold SHADOW_OFF; lia).
  rewrite (U_atom _ 10 _ E10) by lia.
  destruct (b7_addr_buf B v pos lyc Sc Wc memc mdc np 1 HST0 ltac:(unfold b7_buf, PF_O_BUF; lia) ltac:(lia)
           ltac:(unfold b7_buf, PF_O_BUF; lia)) as (_ & _ & _ & HRA & _). exact HRA. }
{ b7kw_awr. }
b7kw_after E0 HAE KM KP.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* taken: hd0 NAME = 0, the empty name: NONAME 0x88c88 *)
  assert (HE0 : hd0 NAME = 0).
  { rewrite branch_eq_U, (U_atom _ 32 _ (b7kw_ag E0 _ 32 _ HAE eq_refl E32)) in Hc by lia.
    rewrite U_lit in Hc by lia. apply Z.eqb_eq in Hc. exact Hc. }
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan B7_NONAME. { b7kw_awr. }
  b7kw_after E0 HAE KM KP.
  pose proof (regs_kept_of_st_ok_pi _ _ _ rX _ (map (Z_to_bv 5) [2; 3; 4; 8; 9; 20; 18; 21; 26; 25; 22]) HS
    (b7kw_ag32 _ _ _ HA0 HAE) ltac:(vm_compute; reflexivity)) as HK.
  cbn [ms_regs restrict] in HK.
  assert (QK : forall r, In r [2; 3; 4; 8; 9; 20; 18; 21; 26; 25; 22] ->
      getr (ms_regs ms0) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r))
    by (intros r Hr; apply HK; apply in_map; exact Hr).
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?kk)) ?mm ?rom) ?mdx) _ =>
    change (mkCfg (mkst rg (Z_to_bv 64 (BASE + kk)) mm rom) mdx)
      with (cfg_at SEGS (BASE + B7_NONAME) rg mm mdx) end.
  apply (HNONAME fx v pos lyc Sc Wc (ms_regs ms0) (ms_mem ms0) mdv0 cf nm o ln d).
  split; [split; [|split; [exact HMID|split; [|split; [exact HLEN|]]]]|].
  + apply (b7kw_base_same v pos lyc Sc Wc rX memc mdc PF_SC_LINE (ms_regs ms0) (ms_mem ms0) mdv0 HB HJ).
    * intros a Ha _. exact (KM a Ha).
    * intros r Hr. apply QK. cbn [In] in Hr |- *. tauto.
  + apply (b7kw_st0_keep v pos lyc Sc Wc memc mdc _ cf nm _ (b7_buf v pos) HST0 ltac:(lia));
      [intros a Ha _; apply KM; lia | exact HST].
  + unfold pf_rg. rewrite Forall_app. split.
    * unfold PF_RL. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
        (rewrite QK; [apply (b7kw_rg rX _ _ _ (proj1 (proj1 (b7kw_rg_app rX _ _) HRGc))); b7kw_in | b7kw_in]).
    * unfold PF_RM. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
        (rewrite QK; [apply (b7kw_rg rX _ _ _ (proj2 (proj1 (b7kw_rg_app rX _ _) HRGc))); b7kw_in | b7kw_in]).
  + exact (b7kw_post_noname cf nm (ln + 1) (pf_tline (p_s v) o) ci HCL HNUL HKW HSP HE0).
- (* not taken: the name is not empty; 0x887b0 mv a0,s7 and the call 0x887b4 *)
  assert (HE0 : hd0 NAME <> 0).
  { rewrite branch_eq_U, (U_atom _ 32 _ (b7kw_ag E0 _ 32 _ HAE eq_refl E32)) in Hc by lia.
    rewrite U_lit in Hc by lia. intros HH. rewrite HH, Z.eqb_refl in Hc. discriminate. }
  clear Hc.
  paj_run_tok RUN HS HJ SHOK Bspan. { b7kw_awr. }
  assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms0) a = rdW Wc memc a).
  { intros a Ha. lazymatch type of HFr with frame_of ?Eo ?rs _ _ =>
    rewrite (kept_of_frame (segs := SEGS) Eo rs (w_H Wc) (ms_mem ms) (ms_mem ms0) (fun _ => False) HFr) end;
      [ exact (KM a Ha)
      | intros bb wlo whi a' Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia |]);
        destruct Hin
      | exact Ha | tauto ]. }
  assert (KP1 : forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) (ms_mem ms0) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG (KP a Ha))).
  lazymatch type of HS with st_ok _ ?En _ _ =>
    assert (HAE1 : env_agree 33 E0 En) by (env_agree_chain HAE) end.
  clear HFr HG HF.
  set (mdv1 := with_vm_backing _ _ _) in *; clearbody mdv1.
  pmkst HS.
  prreg HS (1%bv : bv 5) N1. prreg HS (2%bv : bv 5) N2. prreg HS (3%bv : bv 5) N3.
  prreg HS (4%bv : bv 5) N4. prreg HS (10%bv : bv 5) N10.
  prreg HS (19%bv : bv 5) N19. prreg HS (23%bv : bv 5) N23.
  assert (M2 : getr (ms_regs ms0) 2 = w64 (pf_s1 v)).
  { rewrite N2. apply (b7kw_ag E0 _ 2 _ HAE1 eq_refl).
    rewrite (EE 2%nat (Z_to_bv 5 2) eq_refl). exact R2. }
  assert (Hsp : spZ (ms_regs ms0) = pf_sp0 v + (pf_s1 v - pf_sp0 v)).
  { unfold spZ. rewrite M2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
  assert (HraT : YK0s.ret_ok (getr (ms_regs ms0) 1)) by (rewrite N1; apply ret_ok_codeptr_v; [lia | reflexivity]).
  assert (N3' : getr (ms_regs ms0) 3 = w64 (as_gp B)).
  { rewrite N3. apply (b7kw_ag E0 _ 3 _ HAE1 eq_refl).
    rewrite (EE 3%nat (Z_to_bv 5 3) eq_refl). exact R3. }
  assert (N4' : getr (ms_regs ms0) 4 = w64 (as_tp B)).
  { rewrite N4. apply (b7kw_ag E0 _ 4 _ HAE1 eq_refl).
    rewrite (EE 4%nat (Z_to_bv 5 4) eq_refl). exact R4. }
  assert (N10' : getr (ms_regs ms0) 10 = w64 np).
  { rewrite N10. apply (b7kw_ag E0 _ 10 _ HAE1 eq_refl). exact E10. }
  (* the cut facts at the call's memory *)
  assert (HST1 : b7_st B v pos lyc Sc Wc (ms_mem ms0) mdv1).
  { apply (b7_keep_art B v pos lyc Sc Wc memc mdc (ms_mem ms0) mdv1 0 0 HST0 HJ ltac:(rewrite SPF; lia)).
    intros a Ha _ _. exact (KM1 a Ha). }
  assert (HSTR1 : sa_str (rdW Wc (ms_mem ms0)) np NAME).
  { apply (reac_segconf_parse.sa_str_low (rdW Wc memc) _ np NAME HSTR); [lia | lia |].
    intros a Ha. apply KM1. lia. }
  destruct (b7_strlen_pre_887b4 B v pos lyc Sc Wc (ms_mem ms0) mdv1 (ms_regs ms0) np NAME HST1
    ltac:(rewrite Hsp; lia) HraT N3' N4' N10' HSTR1 ltac:(unfold pf_inb, PF_O_BUF; lia))
    as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
  eapply SRr_bind.
  { eapply (aj_art_at SEGS B LAWS pa_segs_low (pal_env B TL) ESTACK (fun _ => False)
      (SIG SS___interceptor_trampoline_strlen) Wc (ms_regs ms0) (ms_mem ms0) STK_reac_segconf_parse_file
      (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc
      mdv1 0 (pf_s1 v - pf_sp0 v) (Z_to_bv 64 (BASE + B7KW_LEN)) _ HJ Hsp Ho16 ltac:(lia)
      ltac:(unfold ESTACK; lia) ltac:(rewrite SPF; unfold ESTACK; lia) N1
      (fun a (HH : False) => False_ind _ HH)).
    exact (ASTRLEN fx lyc Sc Wc (ms_regs ms0) (ms_mem ms0) mdv1 np (seg_spec.zb NAME) P1 P2 P3 P4 P5 P6 P7). }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha02 & HK2).
  change (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + B7KW_LEN)) mem2 (seg_rom SEGS)) md2)
    with (cfg_at SEGS (BASE + B7KW_LEN) regs2 mem2 md2).
  assert (KM2 : forall a, 0 <= a < 2 ^ 64 -> a < alloc_ceiling \/ pf_s1 v <= a ->
      rdW Wc mem2 a = rdW Wc memc a).
  { intros a Ha Hlo. rewrite HK2; [exact (KM1 a Ha) | exact Ha | unfold ESTACK in *; lia | tauto]. }
  assert (QK2 : forall r, In r [2; 3; 4; 8; 9; 20; 18; 19; 21; 22; 23; 25; 26] ->
      getr regs2 (Z_to_bv 5 r) = getr (ms_regs ms0) (Z_to_bv 5 r)).
  { intros r Hr. apply HP2. unfold acallee_saved. cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr]; [lia |]). destruct Hr. }
  assert (QKc : forall r, In r [2; 3; 4; 8; 9; 20; 18; 21; 26; 25; 22] ->
      getr regs2 (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
  { intros r Hr. rewrite QK2 by (cbn [In] in Hr |- *; tauto).
    pose proof (regs_kept_of_st_ok SEGS _ _ _ rX _ (map (Z_to_bv 5) [2; 3; 4; 8; 9; 20; 18; 21; 26; 25; 22]) HS
      (b7kw_ag32 _ _ _ HA0 HAE1) ltac:(vm_compute; reflexivity)) as HK.
    cbn [ms_regs restrict] in HK. apply HK. apply in_map. exact Hr. }
  assert (R19 : getr regs2 (Z_to_bv 5 19) = w64 32).
  { rewrite QK2 by b7kw_in.
    replace (Z_to_bv 5 19) with (19%bv : bv 5) by (apply bv_eq; reflexivity). rewrite N19.
    first [reflexivity | vm_compute; reflexivity]. }
  assert (R23 : getr regs2 (Z_to_bv 5 23) = w64 np).
  { rewrite QK2 by b7kw_in.
    replace (Z_to_bv 5 23) with (23%bv : bv 5) by (apply bv_eq; reflexivity). rewrite N23.
    apply (b7kw_ag E0 _ 10 _ HAE1 eq_refl). exact E10. }
  assert (R10' : getr regs2 (Z_to_bv 5 10) = w64 (Z.of_nat (length NAME))).
  { replace (Z_to_bv 5 10) with (10%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Ha02. unfold astr_len, seg_spec.zb. rewrite length_map. reflexivity. }
  apply (b7kw_len n v pos lyc Sc Wc regs2 mem2 md2 cf nm o ln d ci np HREFTL HSEG).
  + split; [|split; [exact HMID|split; [|split; [exact HLEN|]]]].
    * apply (b7kw_base_same v pos lyc Sc Wc rX memc mdc PF_SC_LINE regs2 mem2 md2 HB HJ2).
      -- exact KM2.
      -- intros r Hr. apply QKc. cbn [In] in Hr |- *. tauto.
    * apply (b7kw_st0_keep v pos lyc Sc Wc memc mdc _ cf nm _ (b7_buf v pos) HST0 ltac:(lia));
        [intros a Ha _; apply KM2; lia | exact HST].
    * unfold pf_rg. rewrite Forall_app. split.
      -- unfold PF_RL. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
           (rewrite QKc; [apply (b7kw_rg rX _ _ _ (proj1 (proj1 (b7kw_rg_app rX _ _) HRGc))); b7kw_in | b7kw_in]).
      -- unfold PF_RM. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
           (rewrite QKc; [apply (b7kw_rg rX _ _ _ (proj2 (proj1 (b7kw_rg_app rX _ _) HRGc))); b7kw_in | b7kw_in]).
  + exact HCL.
  + exact HNUL.
  + exact HKW.
  + exact HSP.
  + exact HE0.
  + apply (reac_segconf_parse.sa_str_low (rdW Wc memc) _ np NAME HSTR); [lia | lia |].
    intros a Ha. apply KM2; lia.
  + exact HINB.
  + unfold pf_rg. rewrite !Forall_app. split; [|split].
    * unfold PF_RL. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
        (rewrite QKc; [apply (b7kw_rg rX _ _ _ (proj1 (proj1 (b7kw_rg_app rX _ _) HRGc))); b7kw_in | b7kw_in]).
    * unfold PF_RM. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
        (rewrite QKc; [apply (b7kw_rg rX _ _ _ (proj2 (proj1 (b7kw_rg_app rX _ _) HRGc))); b7kw_in | b7kw_in]).
    * repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
        first [exact R19 | exact R23 | exact R10'].
Qed.

(** a byte of a live heap block is below the ceiling and off the class-5 frame *)
Lemma b7kw_heap_out : forall v pos lyc Sc Wc memc mdc q n a, b7_st B v pos lyc Sc Wc memc mdc ->
  sa_heap B lyc Sc q n -> 0 <= n -> q <= a < q + n ->
  4096 <= a < alloc_ceiling /\ ~ (pf_F v pos <= a < pf_F v pos + 2048).
Proof.
intros v pos lyc Sc Wc memc mdc q n a H Hh Hn Ha.
pose proof (b7_AR B v pos lyc Sc Wc memc mdc H) as HAR.
pose proof (b7_fin B v pos lyc Sc Wc memc mdc H) as Hfin.
pose proof H as [_ _ HLY _ _ _].
destruct Hh as (b & m & Hin & Hb & Hm).
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hin) as (_ & H4096 & Hceil & _ & _ & _ & Hmm).
pose proof (req_size_pos m ltac:(lia)) as [_ Hrq].
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ b m 5 pos HAR Hin Hfin) as Hsep.
unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. rewrite b7_fb5 in Hsep.
replace (frame_addr lyc 5 pos) with (pf_F v pos) in Hsep by (unfold pf_F; rewrite HLY; reflexivity).
split; [lia | lia].
Qed.
(** an image byte is off the class-5 frame *)
Lemma b7kw_img_out : forall v pos lyc Sc Wc memc mdc a, b7_st B v pos lyc Sc Wc memc mdc ->
  in_img SEGS a -> ~ (pf_F v pos <= a < pf_F v pos + 2048).
Proof.
intros v pos lyc Sc Wc memc mdc a H Hi.
pose proof (b7_AR B v pos lyc Sc Wc memc mdc H) as HAR.
pose proof (b7_fin B v pos lyc Sc Wc memc mdc H) as Hfin.
pose proof H as [_ _ HLY _ _ _].
pose proof (frm_img SEGS B LAWS lyc Sc Wc memc mdc 5 pos a HAR Hfin) as Hf.
replace (frame_addr lyc 5 pos) with (pf_F v pos) in Hf by (unfold pf_F; rewrite HLY; reflexivity).
rewrite b7_fb5 in Hf. intros Ha. exact (Hf Ha Hi).
Qed.

(** ** 6. 0x8878c: trim(body + 7), then the name stretch *)
Lemma b7kw_trim_stretch : forall (n : nat) (v : pfv) pos lyc Sc (Wc : world SEGS) rX memc mdc cf nm o ln d ci bp,
  HA_NONAME B n -> HA_REFTL B n -> HA_SEG B n ->
  b7_core (fx := fx) B n v pos lyc Sc Wc rX memc mdc cf nm o ln d ->
  strchr (pf_tline (p_s v) o) RBR = Some ci ->
  nth (S ci) (pf_tline (p_s v) o) 0 = 0 ->
  strncasecmp (b7_body (pf_tline (p_s v) o) ci) S_segment 7 = 0 ->
  (nth 7 (b7_body (pf_tline (p_s v) o) ci) 0 = 32 \/ nth 7 (b7_body (pf_tline (p_s v) o) ci) 0 = 9) ->
  sa_str (rdW Wc memc) bp (b7_body (pf_tline (p_s v) o) ci) ->
  pf_inb (b7_buf v pos) bp (b7_body (pf_tline (p_s v) o) ci) ->
  getr rX (Z_to_bv 5 10) = w64 (bp + 7) ->
  SRr SEGS Wc (cfg_at SEGS (BASE + B7KW_TRIM) rX memc mdc) (b7_post (fx := fx) B v cf nm o ln).
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf nm o ln d ci bp HNONAME HREFTL HSEG HC HCL HNUL HKW HSP HSTR HINB R10.
pose proof HC as (HB & HMID & HST & HLEN & HRGc).
pose proof (b7kw_st_of_base v pos lyc Sc Wc rX memc mdc HB) as HST0.
pose proof HB as (HCX & HFI & HOBJ & HSL & HFSH).
pose proof HFI as (HJ & Hly & HSc & HPERM & HSAV & HFLAG & HFRM & HTF & HC8 & HRG0).
destruct (b7_frame_rng B v pos lyc Sc Wc memc mdc HST0) as (F1 & F2 & F3 & F4).
destruct (b7_stk B v pos lyc Sc Wc memc mdc HST0) as (Hsp16 & Hceil & Hslo & Hs32 & Hs1rng & Ho16).
pose proof alloc_ceiling_lt as HAC.
pose proof asan_consts as (AC1 & AC2 & AC3 & AC4 & AC5).
destruct (b7k_cx B v HCX) as (Hc0 & Hc16 & HLS & HDJ & Hceil2 & Hslo2 & H47 & Hsp16b).
pose proof STK_values as (STR & _ & _ & SPF & _).
set (LINE := pf_tline (p_s v) o) in *.
set (BODY := b7_body LINE ci) in *.
set (NAME := b7_name BODY) in *.
assert (HBN : ~ In 0 BODY) by (unfold BODY; apply b7_body_nul).
assert (H7 : (7 <= length BODY)%nat) by exact (b7_kw_len7 BODY HBN HKW).
pose proof HINB as [HIB1 HIB2]. unfold b7_buf, PF_O_BUF in HIB1, HIB2.
assert (R2 : getr rX (Z_to_bv 5 2) = w64 (pf_s1 v)) by (apply (b7kw_rg rX _ 2 _ HRG0); b7kw_in).
assert (R3 : getr rX (Z_to_bv 5 3) = w64 (as_gp B)) by (apply (b7kw_rg rX _ 3 _ HRG0); b7kw_in).
assert (R4 : getr rX (Z_to_bv 5 4) = w64 (as_tp B)) by (apply (b7kw_rg rX _ 4 _ HRG0); b7kw_in).
assert (R8 : getr rX (Z_to_bv 5 8) = w64 (pf_sp0 v)) by (apply (b7kw_rg rX _ 8 _ HRG0); b7kw_in).
(* the string trim is given, and where its NUL lands *)
assert (HS7 : sa_str (rdW Wc memc) (bp + 7) (skipn 7 BODY)) by exact (b7kw_skip7_str _ bp BODY HSTR H7).
set (e := trim_end_addr (bp + 7) (skipn 7 BODY)) in *.
destruct (b7kw_name_facts BODY HBN) as (HNF1 & HNF2 & HNF3).
rewrite length_skipn in HNF1.
assert (HeV : e = b7kw_np bp BODY + Z.of_nat (length NAME)).
{ unfold e, trim_end_addr, b7kw_np, NAME, b7_name. lia. }
assert (HeB : pf_F v pos + 0x40 <= e < pf_F v pos + 0x40 + 512).
{ rewrite HeV. unfold b7kw_np. unfold NAME, b7_name in *. lia. }
(* the seed at the jal *)
pose proof (b7kw_seed0 Wc rX memc B7KW_TRIM) as HS.
set (E := Eimg (Ereg rX [])) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr rX r)
  by (intros k r Hk; subst E; apply ew_Eimg_Ereg_nat; exact Hk).
unfold cfg_at. change (w64 (BASE + B7KW_TRIM)) with (Z_to_bv 64 (BASE + B7KW_TRIM)).
paj_run_shc RUNP RUNC HS HJ.
{ intros a (r & Hr & _). cbn [b7kw_ss0 ss_mem In] in Hr. destruct Hr. }
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha. apply (kept_of_frame (segs := SEGS) E (ss_mem (b7kw_ss0 B7KW_TRIM)) (w_H Wc) memc (ms_mem ms)
    (fun _ => False) HFr); [|exact Ha | tauto].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'. destruct Hin'. }
clear HFr HG HF.
set (mdv := with_vm_backing _ _ _) in *; clearbody mdv.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10.
assert (HA0 : env_agree 32 (Ereg rX []) E)
  by (split; [intros k Hk; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]).
assert (QK : forall r, In r [2; 3; 4; 8; 9; 10; 20; 18; 19; 21; 22; 23; 24; 25; 26; 27] ->
    getr (ms_regs ms) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
{ intros r Hr.
  pose proof (regs_kept_of_st_ok SEGS _ _ _ rX _
    (map (Z_to_bv 5) [2; 3; 4; 8; 9; 10; 20; 18; 19; 21; 22; 23; 24; 25; 26; 27]) HS HA0
    ltac:(vm_compute; reflexivity)) as HK.
  cbn [ms_regs restrict] in HK. apply HK. apply in_map. exact Hr. }
assert (HB1 : pf_base (fx := fx) B v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv PF_SC_LINE).
{ apply (b7kw_base_same v pos lyc Sc Wc rX memc mdc PF_SC_LINE (ms_regs ms) (ms_mem ms) mdv HB HJ).
  - intros a Ha _. exact (KM1 a Ha).
  - intros r Hr. apply QK. cbn [In] in Hr |- *. tauto. }
pose proof (b7kw_st_of_base v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv HB1) as HST1.
assert (Q2' : getr (ms_regs ms) 2 = w64 (pf_s1 v)).
{ replace (2%bv : bv 5) with (Z_to_bv 5 2) by (apply bv_eq; reflexivity).
  rewrite QK by b7kw_in. exact R2. }
assert (Q3' : getr (ms_regs ms) 3 = w64 (as_gp B)).
{ replace (3%bv : bv 5) with (Z_to_bv 5 3) by (apply bv_eq; reflexivity).
  rewrite QK by b7kw_in. exact R3. }
assert (Q4' : getr (ms_regs ms) 4 = w64 (as_tp B)).
{ replace (4%bv : bv 5) with (Z_to_bv 5 4) by (apply bv_eq; reflexivity).
  rewrite QK by b7kw_in. exact R4. }
assert (Q8' : getr (ms_regs ms) 8 = w64 (pf_sp0 v)).
{ replace (8%bv : bv 5) with (Z_to_bv 5 8) by (apply bv_eq; reflexivity).
  rewrite QK by b7kw_in. exact R8. }
assert (Q10' : getr (ms_regs ms) 10 = w64 (bp + 7)).
{ replace (10%bv : bv 5) with (Z_to_bv 5 10) by (apply bv_eq; reflexivity).
  rewrite QK by b7kw_in. exact R10. }
assert (Hsp : spZ (ms_regs ms) = pf_sp0 v + (pf_s1 v - pf_sp0 v)).
{ unfold spZ. rewrite Q2'. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (HS7' : sa_str (rdW Wc (ms_mem ms)) (bp + 7) (skipn 7 BODY)).
{ apply (reac_segconf_parse.sa_str_low (rdW Wc memc) _ (bp + 7) (skipn 7 BODY) HS7);
    [lia | rewrite length_skipn; lia |]. intros a Ha. apply KM1. lia. }
destruct (b7_trim_site_8878c B v pos lyc Sc Wc (ms_mem ms) mdv (ms_regs ms) o ci bp HST1
  HINB HKW Q10' HS7') as (HROD & _ & Hp64 & HTP & HEV).
destruct (b7_chain B v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv PF_SC_LINE HB1) as [ch1 HCH1].
pmkst HS.
rewrite (SIGP SS_trim ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_trim) with AF_trim by (vm_compute; reflexivity).
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS Wc (ms_regs ms) (ms_mem ms) _ STK_reac_segconf_parse_file (pf_sp0 v)
    (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc mdv 0
    STK_trim [(e, e + 1)] EV_trim (pf_s1 v - pf_sp0 v) (Z_to_bv 64 (BASE + B7KW_NAME)) ch1
    (fun ly2 S2 W2 regs2 mem2 md2 =>
       getr regs2 10 = w64 (bp + 7 + Z.of_nat (seg_spec.trim_lead (skipn 7 BODY))) /\
       sa_bytes (rdW W2 mem2) (bp + 7)
         (seg_spec.zb (firstn (seg_spec.trim_lead (skipn 7 BODY) + length (r_trim (skipn 7 BODY)))
            (skipn 7 BODY)) ++ [seg_spec.ZERO]) /\
       sa_kept SEGS Wc (ms_mem ms) W2 mem2 (ms_regs ms) STK_trim (fun a => a = e) /\
       sa_noalloc B lyc Sc ly2 S2) HJ Hsp Ho16).
  - lia.
  - rewrite STR. lia.
  - rewrite STR, SPF. lia.
  - exact Q3'.
  - exact Q4'.
  - exact Q1.
  - apply ret_ok_codeptr_v; [unfold B7KW_NAME, AF_reac_segconf_parse_file; lia | reflexivity].
  - assert (HKN : 0 <= B7KW_NAME < 2 ^ 40) by (unfold B7KW_NAME, AF_reac_segconf_parse_file; lia).
    pose proof pa_B_ok as HBo. pose proof pa_base_lo as HBlo.
    rewrite unsigned_lit_small by lia. lia.
  - replace (pf_sp0 v + (pf_s1 v - pf_sp0 v)) with (pf_s1 v) by lia.
    unfold s0Z. rewrite Q8'. unfold w64. rewrite unsigned_lit_small by lia. exact HCH1.
  - intros HPRE1. eapply SRr_mono.
    { exact (TRIM fx lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv ch1 (bp + 7) (skipn 7 BODY) HPRE1 HROD Q10'
        Hp64 HTP HEV). }
    cbv beta. intros W' c' _ (ly' & S' & regs' & mem' & md' & -> & HJ' & HP' & HQ').
    exists ly', S', regs', mem', md'. split; [rewrite Q1; reflexivity|].
    split; [exact HJ'|]. split; [exact HP' | exact HQ'].
  - intros a (r & Hr & Ha). destruct Hr as [<- | []]. cbn [fst snd] in Ha.
    right; right; right; left. exists 5, pos. split; [left; reflexivity|]. left.
    unfold in_zr. cbn [fst snd].
    replace (frame_addr lyc 5 pos) with (pf_F v pos) by (unfold pf_F; rewrite Hly; reflexivity).
    rewrite b7_fb5. lia.
  - intros ly2 S2 W2 regs2 mem2 md2 _ a (r & Hr & Ha) Hw _. exfalso.
    destruct Hr as [<- | []]. cbn [fst snd] in Ha. rewrite SPF in Hw. lia. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJo & HJi & HP & (Ha0 & HBY & HKP & HNA)).
destruct HNA as (HPerm & -> & HSf).
change (0 + EV_trim) with 0 in HJo.
change (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + B7KW_NAME)) mem2 (seg_rom SEGS)) md2)
  with (cfg_at SEGS (BASE + B7KW_NAME) regs2 mem2 md2).
(* what trim kept: every byte off its window below s1 and off its NUL *)
assert (KM0 : forall a, 0 <= a < 2 ^ 64 -> ~ (pf_s1 v - STK_trim <= a < pf_s1 v) -> a <> e ->
    rdW W2 mem2 a = rdW Wc memc a).
{ intros a Ha Hw Hne. rewrite HKP; [exact (KM1 a Ha) | exact Ha | | exact Hne].
  unfold spZ. rewrite Q2'. unfold w64. rewrite unsigned_lit_small by lia. exact Hw. }
assert (KLOW : forall a, 0 <= a < alloc_ceiling -> a <> e -> rdW W2 mem2 a = rdW Wc memc a).
{ intros a Ha Hne. apply KM0; [lia | rewrite STR; lia | exact Hne]. }
assert (HKE : b7kw_keeps_e v pos Wc memc W2 mem2 e).
{ pose proof HOBJ as (_ & _ & HTH & _ & HCH & _).
  split; [|split; [|split]].
  - intros a Ha. apply KM0; [lia | lia |]. unfold b7_buf, PF_O_BUF in HeB. lia.
  - intros i Hi. apply KLOW.
    + destruct (b7kw_heap_out v pos lyc Sc Wc memc mdc (p_t v) (pf_len v) (p_t v + i) HST0 HTH
        ltac:(unfold pf_len; lia) ltac:(unfold pf_len; lia)) as (HA1 & _). lia.
    + destruct (b7kw_heap_out v pos lyc Sc Wc memc mdc (p_t v) (pf_len v) (p_t v + i) HST0 HTH
        ltac:(unfold pf_len; lia) ltac:(unfold pf_len; lia)) as (_ & HA2).
      unfold b7_buf, PF_O_BUF in HeB. lia.
  - intros a Ha _ _. pose proof (pa_img_range a Ha) as Hrg. unfold kImgEnd in Hrg.
    apply KLOW; [lia|].
    pose proof (b7kw_img_out v pos lyc Sc Wc memc mdc a HST0 Ha) as Hout.
    unfold b7_buf, PF_O_BUF in HeB. lia.
  - intros a Ha Hne. apply KLOW; [|exact Hne].
    destruct Ha as [Ha | Ha]; [rewrite b7_fb5 in Ha; lia|].
    rewrite b7_fb5 in Ha. change (2048 / 8) with 256 in Ha.
    pose proof (Z.div_lt_upper_bound (pf_F v pos) 8 (2 ^ 44 - 256) ltac:(lia) ltac:(lia)).
    pose proof (Z.div_pos (pf_F v pos) 8 ltac:(lia) ltac:(lia)).
    unfold pf_SH, shadow_addr, SHADOW_OFF in Ha. lia. }
assert (QK2 : forall r, In r [2; 3; 4; 8; 9; 20; 18; 19; 21; 22; 23; 24; 25; 26; 27] ->
    getr regs2 (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
{ intros r Hr. rewrite <- (QK r ltac:(cbn [In] in Hr |- *; tauto)). apply HP.
  unfold acallee_saved. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [lia |]). destruct Hr. }
assert (HB2 : pf_base (fx := fx) B v pos lyc S2 W2 regs2 mem2 md2 PF_SC_LINE).
{ apply (b7kw_base_move_e fx v pos lyc Sc Wc rX memc mdc lyc S2 W2 regs2 mem2 md2 e HB (fxrel_refl fx) HJo
    eq_refl HSf HPerm ltac:(unfold b7_buf, PF_O_BUF; lia) HKE).
  intros r Hr. apply QK2. cbn [In] in Hr |- *. tauto. }
assert (HSTRN : sa_str (rdW W2 mem2) (b7kw_np bp BODY) NAME).
{ apply (b7kw_name_str SEGS (w_H Wc) memc (w_H W2) mem2 bp BODY HSTR H7 HBY).
  intros a Ha1 Ha2. change (b7_name BODY) with NAME in Ha1.
  pose proof (Z.mod_pos_bound (bp + Z.of_nat (length BODY)) 8 ltac:(lia)) as HM8.
  apply KM0; [lia | rewrite STR; lia | rewrite HeV; lia]. }
apply (b7kw_name_stretch n v pos lyc S2 W2 regs2 mem2 md2 cf nm o ln d ci (b7kw_np bp BODY)
  HNONAME HREFTL HSEG).
- split; [exact HB2|split; [exact HMID|split; [|split; [exact HLEN|]]]].
  + apply (b7kw_st0_keep v pos lyc Sc Wc memc mdc _ cf nm _ e HST0 ltac:(unfold b7_buf, PF_O_BUF; lia));
      [intros a Ha Hne; apply KLOW; [lia | exact Hne] | exact HST].
  + unfold pf_rg. rewrite Forall_app. split.
    * unfold PF_RL. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
        (rewrite QK2; [apply (b7kw_rg rX _ _ _ (proj1 (proj1 (b7kw_rg_app rX _ _) HRGc))); b7kw_in | b7kw_in]).
    * unfold PF_RM. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
        (rewrite QK2; [apply (b7kw_rg rX _ _ _ (proj2 (proj1 (b7kw_rg_app rX _ _) HRGc))); b7kw_in | b7kw_in]).
- exact HCL.
- exact HNUL.
- exact HKW.
- exact HSP.
- exact HSTRN.
- exact (b7kw_name_inb (b7_buf v pos) bp BODY HINB HBN H7).
- replace (Z_to_bv 5 10) with (10%bv : bv 5) by (apply bv_eq; reflexivity).
  rewrite Ha0. unfold b7kw_np. reflexivity.
Qed.

(** ** 7. KWOK 0x88764 .. 0x88788: the trap T19, body[7] (check B#20) and the blank test *)
Lemma b7kw_kwok : forall n, HA_UNK B n -> HA_NONAME B n -> HA_REFTL B n -> HA_SEG B n -> H_KWOK (fx := fx) B n.
Proof.
intros n HUNK HNONAME HREFTL HSEG v pos lyc Sc Wc rX memc mdc cf nm o ln d ci bp HI.
destruct HI as (HC & HCL & HNUL & HKW & HSTR & HINB & HRG).
pose proof HC as (HB & HMID & HST & HLEN & HRGc).
pose proof (b7kw_st_of_base v pos lyc Sc Wc rX memc mdc HB) as HST0.
pose proof HB as (HCX & HFI & HOBJ & HSL & HFSH).
pose proof HFI as (HJ & Hly & HSc & HPERM & HSAV & HFLAG & HFRM & HTF & HC8 & HRG0).
destruct (b7_frame_rng B v pos lyc Sc Wc memc mdc HST0) as (F1 & F2 & F3 & F4).
pose proof alloc_ceiling_lt as HAC.
pose proof asan_consts as (AC1 & AC2 & AC3 & AC4 & AC5).
set (LINE := pf_tline (p_s v) o) in *.
set (BODY := b7_body LINE ci) in *.
assert (HBN : ~ In 0 BODY) by (unfold BODY; apply b7_body_nul).
assert (H7 : (7 <= length BODY)%nat) by exact (b7_kw_len7 BODY HBN HKW).
pose proof HINB as [HIB1 HIB2]. unfold PF_O_BUF in HIB1, HIB2.
assert (R19 : getr rX (Z_to_bv 5 19) = w64 bp) by (apply (b7kw_rg rX _ 19 _ HRG); b7kw_in).
assert (R27 : getr rX (Z_to_bv 5 27) = w64 9) by (apply (b7kw_rg rX _ 27 _ HRG); b7kw_in).
assert (R24 : getr rX (Z_to_bv 5 24) = w64 32) by (apply (b7kw_rg rX _ 24 _ HRG); b7kw_in).
assert (HB7 : rdW Wc memc (bp + 7) = Some (nth 7 BODY 0)) by exact (b7kw_byte7 _ bp BODY HSTR H7).
pose proof (sa_aview_rng _ _ _ _ _ HB7) as HB7r.
(* the seed with body[7] as the one byte region *)
pose proof (b7kw_seed1 v pos lyc Sc Wc rX memc mdc B7_KWOK 19%nat (Z_to_bv 5 19) bp 7 (nth 7 BODY 0) HB
  eq_refl R19 ltac:(lia) ltac:(lia) ltac:(lia) HB7) as HS.
set (E0 := Eimg (Ereg rX [Z_to_bv 64 (nth 7 BODY 0)])) in HS.
assert (HEI : img_env VAL A_LIM E0) by (subst E0; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E0 k = getr rX r)
  by (intros k r Hk; subst E0; apply ew_Eimg_Ereg_nat; exact Hk).
assert (HA0 : env_agree 32 (Ereg rX [Z_to_bv 64 (nth 7 BODY 0)]) E0)
  by (split; [intros k Hk; subst E0; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]).
assert (E19 : ew E0 19 = Z_to_bv 64 bp) by (rewrite (EE 19%nat (Z_to_bv 5 19) eq_refl); exact R19).
assert (E27 : ew E0 27 = Z_to_bv 64 9) by (rewrite (EE 27%nat (Z_to_bv 5 27) eq_refl); exact R27).
assert (E24 : ew E0 24 = Z_to_bv 64 32) by (rewrite (EE 24%nat (Z_to_bv 5 24) eq_refl); exact R24).
assert (E20 : ew E0 20 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (EE 20%nat (Z_to_bv 5 20) eq_refl); apply (b7kw_rg rX _ 20 _ HRG0); b7kw_in).
assert (E32 : ew E0 32 = Z_to_bv 64 (nth 7 BODY 0)).
{ subst E0. rewrite Eimg_low by (unfold A_TEXT; lia).
  change 32%nat with (32 + 0)%nat. rewrite (ew_Ereg_extra rX [Z_to_bv 64 (nth 7 BODY 0)] 0). reflexivity. }
assert (SHOK : sh_ok SEGS b7kw_Bx [] E0 (mrestrict (w_H Wc) memc)) by constructor.
pose proof (env_agree_refl 33 E0) as HAE.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc a = rdW Wc memc a) by (intros; reflexivity).
assert (KP : forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) memc a) by (intros; assumption).
unfold cfg_at. change (w64 (BASE + B7_KWOK)) with (Z_to_bv 64 (BASE + B7_KWOK)).
(* 0x88764 .. 0x88784: the trap T19, the check B#20, body[7] *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ cbn [ms_mem]. unfold b7kw_Bx.
  rewrite (U_atom _ 20 _ E20) by (unfold SHADOW_OFF; lia).
  rewrite (U_atom_off _ 19 _ 7 E19) by lia.
  destruct (b7_addr_buf B v pos lyc Sc Wc memc mdc (bp + 7) 1 HST0 ltac:(unfold b7_buf, PF_O_BUF; lia)
    ltac:(lia) ltac:(unfold b7_buf, PF_O_BUF; lia)) as (_ & _ & _ & HRA & _). exact HRA. }
{ b7kw_awr. }
b7kw_after E0 HAE KM KP.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* body[7] = 9 (TAB): the blank test holds, on to the trim call *)
  assert (HT9 : nth 7 BODY 0 = 9).
  { rewrite branch_eq_U, (U_atom _ 32 _ (b7kw_ag E0 _ 32 _ HAE eq_refl E32)),
      (U_atom _ 27 _ (b7kw_ag E0 _ 27 _ HAE eq_refl E27)) in Hc by lia.
    apply Z.eqb_eq in Hc. exact Hc. }
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan B7KW_TRIM. { b7kw_awr. }
  b7kw_after E0 HAE KM KP.
  pose proof (regs_kept_of_st_ok_pi _ _ _ rX _
    (map (Z_to_bv 5) [2; 3; 4; 8; 9; 20; 18; 19; 21; 26; 25; 22]) HS (b7kw_ag32 _ _ _ HA0 HAE)
    ltac:(vm_compute; reflexivity)) as HK.
  cbn [ms_regs restrict] in HK.
  assert (QK : forall r, In r [2; 3; 4; 8; 9; 20; 18; 19; 21; 26; 25; 22] ->
      getr (ms_regs ms0) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r))
    by (intros r Hr; apply HK; apply in_map; exact Hr).
  lazymatch type of HS with st_ok_pi _ _ ?En _ _ =>
    assert (E19n : ew En 19 = Z_to_bv 64 bp) by (apply (b7kw_ag E0 _ 19 _ HAE eq_refl); exact E19) end.
  assert (R10n : getr (ms_regs ms0) (Z_to_bv 5 10) = w64 (bp + 7)).
  { b7kw_rreg HS. cbn [sv_denot]. rewrite E19n. rewrite b7kw_w64_off. reflexivity. }
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?kk)) ?mm ?rom) ?mdx) _ =>
    change (mkCfg (mkst rg (Z_to_bv 64 (BASE + kk)) mm rom) mdx)
      with (cfg_at SEGS (BASE + B7KW_TRIM) rg mm mdx) end.
  apply (b7kw_trim_stretch n v pos lyc Sc Wc (ms_regs ms0) (ms_mem ms0) mdv0 cf nm o ln d ci bp
    HNONAME HREFTL HSEG).
  * split; [|split; [exact HMID|split; [|split; [exact HLEN|]]]].
    -- apply (b7kw_base_same v pos lyc Sc Wc rX memc mdc PF_SC_LINE (ms_regs ms0) (ms_mem ms0) mdv0 HB HJ).
       ++ intros a Ha _. exact (KM a Ha).
       ++ intros r Hr. apply QK. cbn [In] in Hr |- *. tauto.
    -- apply (b7kw_st0_keep v pos lyc Sc Wc memc mdc _ cf nm _ (b7_buf v pos) HST0 ltac:(lia));
         [intros a Ha _; apply KM; lia | exact HST].
    -- unfold pf_rg. rewrite Forall_app. split.
       ++ unfold PF_RL. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
            (rewrite QK; [apply (b7kw_rg rX _ _ _ (proj1 (proj1 (b7kw_rg_app rX _ _) HRGc))); b7kw_in | b7kw_in]).
       ++ unfold PF_RM. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
            (rewrite QK; [apply (b7kw_rg rX _ _ _ (proj2 (proj1 (b7kw_rg_app rX _ _) HRGc))); b7kw_in | b7kw_in]).
  * exact HCL.
  * exact HNUL.
  * exact HKW.
  * right. exact HT9.
  * apply (reac_segconf_parse.sa_str_low (rdW Wc memc) _ bp BODY HSTR); [lia | lia |].
    intros a Ha. apply KM. lia.
  * exact HINB.
  * exact R10n.
- (* body[7] <> 9: the second test *)
  assert (HT9 : nth 7 BODY 0 <> 9).
  { rewrite branch_eq_U, (U_atom _ 32 _ (b7kw_ag E0 _ 32 _ HAE eq_refl E32)),
      (U_atom _ 27 _ (b7kw_ag E0 _ 27 _ HAE eq_refl E27)) in Hc by lia.
    intros HH. rewrite HH, Z.eqb_refl in Hc. discriminate. }
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan B7KW_BNE. { b7kw_awr. }
  b7kw_after E0 HAE KM KP.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* body[7] <> 32 either: the F_unknown refusal at UNK 0x88508 *)
    assert (HT32 : nth 7 BODY 0 <> 32).
    { rewrite branch_ne_U, (U_atom _ 32 _ (b7kw_ag E0 _ 32 _ HAE eq_refl E32)),
        (U_atom _ 24 _ (b7kw_ag E0 _ 24 _ HAE eq_refl E24)) in Hc by lia.
      apply Bool.negb_true_iff, Z.eqb_neq in Hc. exact Hc. }
    clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan B7_UNK. { b7kw_awr. }
    b7kw_after E0 HAE KM KP.
    pose proof (regs_kept_of_st_ok_pi _ _ _ rX _
      (map (Z_to_bv 5) [2; 3; 4; 8; 9; 20; 18; 19; 21; 26; 25; 22]) HS (b7kw_ag32 _ _ _ HA0 HAE)
      ltac:(vm_compute; reflexivity)) as HK.
    cbn [ms_regs restrict] in HK.
    assert (QK : forall r, In r [2; 3; 4; 8; 9; 20; 18; 19; 21; 26; 25; 22] ->
        getr (ms_regs ms1) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r))
      by (intros r Hr; apply HK; apply in_map; exact Hr).
    pmkst HS.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?kk)) ?mm ?rom) ?mdx) _ =>
      change (mkCfg (mkst rg (Z_to_bv 64 (BASE + kk)) mm rom) mdx)
        with (cfg_at SEGS (BASE + B7_UNK) rg mm mdx) end.
    apply (HUNK fx v pos lyc Sc Wc (ms_regs ms1) (ms_mem ms1) mdv1 cf nm o ln d bp BODY).
    split; [split; [|split; [exact HMID|split; [|split; [exact HLEN|]]]]|split; [|split; [|split]]].
    * apply (b7kw_base_same v pos lyc Sc Wc rX memc mdc PF_SC_LINE (ms_regs ms1) (ms_mem ms1) mdv1 HB HJ).
      -- intros a Ha _. exact (KM a Ha).
      -- intros r Hr. apply QK. cbn [In] in Hr |- *. tauto.
    * apply (b7kw_st0_keep v pos lyc Sc Wc memc mdc _ cf nm _ (b7_buf v pos) HST0 ltac:(lia));
        [intros a Ha _; apply KM; lia | exact HST].
    * unfold pf_rg. rewrite Forall_app. split.
      -- unfold PF_RL. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
           (rewrite QK; [apply (b7kw_rg rX _ _ _ (proj1 (proj1 (b7kw_rg_app rX _ _) HRGc))); b7kw_in | b7kw_in]).
      -- unfold PF_RM. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
           (rewrite QK; [apply (b7kw_rg rX _ _ _ (proj2 (proj1 (b7kw_rg_app rX _ _) HRGc))); b7kw_in | b7kw_in]).
    * apply (reac_segconf_parse.sa_str_low (rdW Wc memc) _ bp BODY HSTR); [lia | lia |].
      intros a Ha. apply KM. lia.
    * exact HINB.
    * exact (b7kw_post_unk cf nm (ln + 1) (pf_tline (p_s v) o) ci HCL HNUL HT32 HT9).
    * unfold pf_rg. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd].
      rewrite QK; [exact R19 | b7kw_in].
  + (* body[7] = 32 (SP): the blank test holds, on to the trim call *)
    assert (HT32 : nth 7 BODY 0 = 32).
    { rewrite branch_ne_U, (U_atom _ 32 _ (b7kw_ag E0 _ 32 _ HAE eq_refl E32)),
        (U_atom _ 24 _ (b7kw_ag E0 _ 24 _ HAE eq_refl E24)) in Hc by lia.
      apply Bool.negb_false_iff, Z.eqb_eq in Hc. exact Hc. }
    clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan B7KW_TRIM. { b7kw_awr. }
    b7kw_after E0 HAE KM KP.
    pose proof (regs_kept_of_st_ok_pi _ _ _ rX _
      (map (Z_to_bv 5) [2; 3; 4; 8; 9; 20; 18; 19; 21; 26; 25; 22]) HS (b7kw_ag32 _ _ _ HA0 HAE)
      ltac:(vm_compute; reflexivity)) as HK.
    cbn [ms_regs restrict] in HK.
    assert (QK : forall r, In r [2; 3; 4; 8; 9; 20; 18; 19; 21; 26; 25; 22] ->
        getr (ms_regs ms1) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r))
      by (intros r Hr; apply HK; apply in_map; exact Hr).
    lazymatch type of HS with st_ok_pi _ _ ?En _ _ =>
      assert (E19n : ew En 19 = Z_to_bv 64 bp) by (apply (b7kw_ag E0 _ 19 _ HAE eq_refl); exact E19) end.
    assert (R10n : getr (ms_regs ms1) (Z_to_bv 5 10) = w64 (bp + 7)).
    { b7kw_rreg HS. cbn [sv_denot]. rewrite E19n. rewrite b7kw_w64_off. reflexivity. }
    pmkst HS.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?kk)) ?mm ?rom) ?mdx) _ =>
      change (mkCfg (mkst rg (Z_to_bv 64 (BASE + kk)) mm rom) mdx)
        with (cfg_at SEGS (BASE + B7KW_TRIM) rg mm mdx) end.
    apply (b7kw_trim_stretch n v pos lyc Sc Wc (ms_regs ms1) (ms_mem ms1) mdv1 cf nm o ln d ci bp
      HNONAME HREFTL HSEG).
    * split; [|split; [exact HMID|split; [|split; [exact HLEN|]]]].
      -- apply (b7kw_base_same v pos lyc Sc Wc rX memc mdc PF_SC_LINE (ms_regs ms1) (ms_mem ms1) mdv1 HB HJ).
         ++ intros a Ha _. exact (KM a Ha).
         ++ intros r Hr. apply QK. cbn [In] in Hr |- *. tauto.
      -- apply (b7kw_st0_keep v pos lyc Sc Wc memc mdc _ cf nm _ (b7_buf v pos) HST0 ltac:(lia));
           [intros a Ha _; apply KM; lia | exact HST].
      -- unfold pf_rg. rewrite Forall_app. split.
         ++ unfold PF_RL. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
              (rewrite QK; [apply (b7kw_rg rX _ _ _ (proj1 (proj1 (b7kw_rg_app rX _ _) HRGc))); b7kw_in | b7kw_in]).
         ++ unfold PF_RM. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
              (rewrite QK; [apply (b7kw_rg rX _ _ _ (proj2 (proj1 (b7kw_rg_app rX _ _) HRGc))); b7kw_in | b7kw_in]).
    * exact HCL.
    * exact HNUL.
    * exact HKW.
    * left. exact HT32.
    * apply (reac_segconf_parse.sa_str_low (rdW Wc memc) _ bp BODY HSTR); [lia | lia |].
      intros a Ha. apply KM. lia.
    * exact HINB.
    * exact R10n.
Qed.

End x.

(** the piece of pf_seg_B7_m.v at every FP state *)
Theorem b7kw_ok : B7_S_KWOK B.
Proof. intros f0 n HU HN HR HS. exact (b7kw_kwok (fx := f0) n HU HN HR HS). Qed.
End d.
