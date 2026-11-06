(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColB/W_set0A.v, with its module paths and module names changed; 604 of its 627 lines of code are new or changed and 122 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_scene/lib/Prog/check_step.v, with its module paths and module names changed; 407 of its 449 lines of code are new or changed and 585 lines of the source are left out. *)
(* Pure facts for segment S3 of the ASan walk of check_step (fuzz_scene.asan-ubsan): the 50-byte frame object that
   the two __asan_memcpy calls build, what reac_ctrl_parse's model returns on it, and the 32 control-block bytes
   frame[18..50) that reac_ctrl_checksum_verify sums (the pure part: no kit, no Section). The asan copy is
   lib/A/P_check_step_S3_aux.v (at 8cb4af36d62); only the cut module changes.
   After the pure part, a Section with S3's hypothesis names proves s3u_tail (a Theorem Labs lane's TAIL.md): the walk from
   reac_ctrl_parse's return 0x836a0 to the cut 0x836d4 (the five checks, reac_ctrl_checksum_verify through cl_callS,
   cs_st4), with its helper s3t_after (the call and the rest).
   The frame in asan-ubsan: 0x8365c __asan_memcpy(F + 32, __const.check_step.frame (0x20da0), 50) writes
   frame[0..50) = cs_frame_init; then 0x83674 __asan_memcpy(F + 48, blk, 34) writes frame[16..50) = scene_block b k.
   So the frame is firstn 16 cs_frame_init ++ scene_block b k, as in asan (where the first copy is 16 bytes); the
   AU cs_frame_init (AU/P_check_step_cut.v:75-76) is the same text as the asan one.
   scene_fields_length, scene_block_length, cks_sum and byte_sum_nonneg are copies of lib/Prog/check_step.v:33-57
   (that file is not Required here). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog Require Import SceneBlock RcModel RcKind RcParse.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import P_check_step_cut.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Local Ltac norm_nat_lits :=
  repeat match goal with
  | H : context [Nat.of_num_uint ?u] |- _ =>
      let v := eval vm_compute in (Nat.of_num_uint u) in change (Nat.of_num_uint u) with v in H
  end.
(* Copies of lib/Prog/check_step.v:33-57. *)
Lemma scene_fields_length : forall b k, length b = 8904%nat -> 0 <= k <= 342 -> length (scene_fields b k) = 31%nat.
Proof.
  intros b k Hb Hk. norm_nat_lits. unfold scene_fields, scene_payload, scene_off.
  destruct (Z.eqb_spec k 0); [subst; cbn [length app]; rewrite length_firstn, Hb; reflexivity|].
  destruct (Z.eqb_spec k 342).
  - cbn [length app]. rewrite length_app, length_firstn, length_skipn, Hb. reflexivity.
  - cbn [length app]. rewrite length_firstn, length_skipn, Hb. lia.
Qed.
Lemma scene_block_length : forall b k, length b = 8904%nat -> 0 <= k <= 342 -> length (scene_block b k) = 34%nat.
Proof.
  intros b k Hb Hk. unfold scene_block. rewrite !length_app, scene_fields_length by assumption. reflexivity.
Qed.
Lemma cks_sum : forall S, 0 <= S -> (S + bv_unsigned (Z_to_bv 8 ((256 - S mod 256) mod 256))) mod 256 = 0.
Proof.
  intros S HS. rewrite Z_to_bv_unsigned. change (bv_wrap 8 ?x) with (x mod 2^8).
  Z.div_mod_to_equations. lia.
Qed.
Lemma byte_sum_nonneg : forall l, 0 <= byte_sum l.
Proof.
  induction l as [|x l IH]; cbn [byte_sum fold_right]; [lia|].
  pose proof (bv_unsigned_in_range 8 x). unfold byte_sum in IH. lia.
Qed.
(* The frame object at the parse call. *)
Definition s3_fr (b : list byte) (k : Z) : list byte := firstn 16 cs_frame_init ++ scene_block b k.
Definition s3_bs (b : list byte) (k : Z) : list Z := map (fun i => cp_v (s3_fr b k) (18 + i)) (seq 0 32).
(* firstn 16 cs_frame_init, spelled out. *)
Definition cs_hd16 : list byte :=
  [Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 255; Z_to_bv 8 0; Z_to_bv 8 64;
   Z_to_bv 8 171; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 136; Z_to_bv 8 25; Z_to_bv 8 0; Z_to_bv 8 0].
Lemma s3_fr_eq : forall b k, s3_fr b k = cs_hd16 ++ scene_block b k.
Proof. intros b k. reflexivity. Qed.
Lemma bvu8 : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact Hz.
Qed.
Lemma nth_map_seq : forall (f : nat -> Z) n m d, (m < n)%nat -> nth m (map f (seq 0 n)) d = f m.
Proof.
  intros f n m d Hm. rewrite (nth_indep _ d (f 0%nat)) by (rewrite length_map, length_seq; exact Hm).
  rewrite map_nth, seq_nth by exact Hm. reflexivity.
Qed.
Lemma byte_sum_app : forall l1 l2, byte_sum (l1 ++ l2) = byte_sum l1 + byte_sum l2.
Proof.
  intros l1 l2. induction l1 as [|x l1 IH]; unfold byte_sum in *; cbn [app fold_right] in *; lia.
Qed.
Lemma byte_sum_one : forall x, byte_sum [x] = bv_unsigned x.
Proof. intros x. unfold byte_sum. cbn [fold_right]. lia. Qed.
Lemma psum_app_le : forall l l' n, (n <= length l)%nat -> psum (l ++ l') n = psum l n.
Proof.
  intros l l' n. induction n as [|n IH]; intros H; cbn [psum]; [reflexivity|].
  rewrite IH by lia. rewrite app_nth1 by lia. reflexivity.
Qed.
Lemma psum_byte_sum : forall l, psum l (length l) = byte_sum l.
Proof.
  induction l as [|x l IH] using rev_ind; [reflexivity|].
  rewrite length_app. cbn [length]. rewrite Nat.add_1_r. cbn [psum].
  rewrite psum_app_le by lia. rewrite IH, nth_middle, byte_sum_app, byte_sum_one. reflexivity.
Qed.
(* The statements S3 uses. *)
Lemma s3_fr_length : forall b k, length b = 8904%nat -> 0 <= k <= 342 -> length (s3_fr b k) = 50%nat.
Proof.
  intros b k Hb Hk. rewrite s3_fr_eq, length_app, scene_block_length by assumption. reflexivity.
Qed.
Lemma s3_fr_lo : forall b k i, (i < 16)%nat -> cp_b (s3_fr b k) i = nth i cs_frame_init (Z_to_bv 8 0).
Proof.
  intros b k i Hi. unfold cp_b. rewrite s3_fr_eq.
  do 16 (destruct i as [|i]; [reflexivity|]). lia.
Qed.
Lemma s3_fr_hi : forall b k i, length b = 8904%nat -> 0 <= k <= 342 -> (16 <= i < 50)%nat ->
  cp_b (s3_fr b k) i = nth (i - 16) (scene_block b k) (Z_to_bv 8 0).
Proof.
  intros b k i Hb Hk Hi. unfold cp_b. rewrite s3_fr_eq.
  rewrite app_nth2 by (unfold cs_hd16; cbn [length]; lia).
  replace (i - length cs_hd16)%nat with (i - 16)%nat by reflexivity. reflexivity.
Qed.
Lemma s3_fr_v : forall b k,
  cp_v (s3_fr b k) 12 = 0x88 /\ cp_v (s3_fr b k) 13 = 0x19 /\ cp_v (s3_fr b k) 16 = 0xcd /\
  cp_v (s3_fr b k) 17 = 0xea /\ cp_v (s3_fr b k) 18 = 1 /\ cp_v (s3_fr b k) 22 = 0.
Proof.
  intros b k. unfold cp_v, cp_b. rewrite s3_fr_eq. unfold cs_hd16, scene_block, scene_fields. cbn [nth app].
  rewrite !bvu8 by lia. repeat split; reflexivity.
Qed.
Lemma s3_fr_parse : forall b k, length b = 8904%nat -> 0 <= k <= 342 ->
  let P := ctrlparse 50 (s3_fr b k) in
  fst P = 2 /\ nth 22 (snd P) cp_z = Z_to_bv 8 1 /\ nth 23 (snd P) cp_z = Z_to_bv 8 (scene_seg k) /\
  nth 24 (snd P) cp_z = Z_to_bv 8 (scene_len k) /\ nth 25 (snd P) cp_z = Z_to_bv 8 0 /\ nth 26 (snd P) cp_z = Z_to_bv 8 0.
Proof.
  intros b k Hb Hk. cbv zeta.
  destruct (s3_fr_v b k) as (V12 & V13 & V16 & V17 & V18 & V22).
  assert (Hhdr : cp_hdr 50 (s3_fr b k) = true) by (unfold cp_hdr; rewrite V12, V13; reflexivity).
  assert (Hkind : cp_kind (s3_fr b k) = 2) by (unfold cp_kind, cp_type; rewrite V16, V17, V18, V22; reflexivity).
  unfold ctrlparse. rewrite Hhdr, Hkind. cbn [fst snd]. split; [reflexivity|].
  unfold cp_struct. cbn [nth app].
  unfold cp_b. rewrite s3_fr_eq. unfold cs_hd16, scene_block, scene_fields. cbn [nth app].
  repeat split; reflexivity.
Qed.
Lemma s3_bs_map : forall b k, length b = 8904%nat -> 0 <= k <= 342 ->
  map (Z_to_bv 8) (s3_bs b k) =
  scene_fields b k ++ [Z_to_bv 8 ((256 - byte_sum (scene_fields b k) mod 256) mod 256)].
Proof.
  intros b k Hb Hk. apply nth_ext with (d := Z_to_bv 8 0) (d' := Z_to_bv 8 0).
  - unfold s3_bs. rewrite length_map, length_map, length_seq, length_app, scene_fields_length by assumption.
    reflexivity.
  - intros n Hn. unfold s3_bs in *. rewrite length_map, length_map, length_seq in Hn.
    rewrite (map_nth (Z_to_bv 8)). rewrite nth_map_seq by exact Hn.
    unfold cp_v. rewrite Z_to_bv_bv_unsigned. unfold cp_b. rewrite s3_fr_eq. unfold cs_hd16, scene_block.
    cbn [nth app Nat.add]. reflexivity.
Qed.
Lemma s3_bs_ok : forall b k, length b = 8904%nat -> 0 <= k <= 342 ->
  length (s3_bs b k) = 32%nat /\ (forall j, (j < 32)%nat -> 0 <= nth j (s3_bs b k) 0 < 256) /\
  blocksum (map (Z_to_bv 8) (s3_bs b k)) = 0.
Proof.
  intros b k Hb Hk. split; [unfold s3_bs; rewrite length_map, length_seq; reflexivity|]. split.
  - intros j Hj. unfold s3_bs. rewrite nth_map_seq by exact Hj. unfold cp_v.
    pose proof (bv_unsigned_in_range 8 (cp_b (s3_fr b k) (18 + j))) as R. change (bv_modulus 8) with 256 in R. lia.
  - unfold blocksum. rewrite (s3_bs_map b k Hb Hk).
    set (F := scene_fields b k).
    replace 32%nat with (length (F ++ [Z_to_bv 8 ((256 - byte_sum F mod 256) mod 256)]))
      by (rewrite length_app; unfold F; rewrite scene_fields_length by assumption; reflexivity).
    rewrite psum_byte_sum, byte_sum_app, byte_sum_one.
    exact (cks_sum (byte_sum F) (byte_sum_nonneg F)).
Qed.
(* ---- s3u_tail: the second half of cs_S3 (a Theorem Labs lane), the walk from reac_ctrl_parse's return 0x836a0
   (AF_check_step + 0x40c) to the S3 -> S4 cut 0x836d4 (CS_PC4). The five checks of the parse result
   (0x836a0 a0 = 2; 0x836a4 o[22] = 1; 0x836b0 o[23] = s5; 0x836b8 o[26] = 0; 0x836c0 o[24..25] = s8) are decided
   by the run: k splits into k = 0 / k = 342 / else, where scene_seg k, scene_len k are the literals 1, 24 / 2, 14 /
   0, 26 (SceneBlock.v:6-7); s4, s5, s8 and a0 are pinned to those literals and the o region (s7 = F + 128) holds the
   parse result's bytes 22..26 (s3_fr_parse) as literal chunks. The call 0x836cc reac_ctrl_checksum_verify(f = s6 =
   F + 32) goes through cl_callS (AU/Prog/YC85.v:384, o = -128, TCKV_STK, EV1 = 0) with CKV; its achain is
   achain_push of the entry chain with the saved ra / s0 slots (cs_saved j = 0, 1); its afobj is afobj_of_own; its
   32 bytes frame[18..50) are s3_bs b k, whose blocksum is 0 (s3_bs_ok), so a0 = 0 and `bnez a0` 0x836d0 falls
   through to the cut. The cut's memory facts (flag word, saved slots) are carried over the call by the callee's
   journal (frames of S2 outside FP1 = []; addresses >= alloc_ceiling outside the callee window). *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import NArith Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00 YI16.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import YCbq.  (* image-specific: lib.AU (gate 6o) *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0s YG0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaRun PaShadow SceneSyms SceneList ScenePa.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaJournal ScenePaLib SceneBase SceneRo SceneFrame YC1h YC85.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import YC1g YC45 YC88.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import P_reac_ctrl_checksum_verify P_reac_ctrl_parse.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import P_check_step_frame.
Open Scope Z_scope.
(* The symbolic state at 0x836a0: atoms 0..31 the registers at the parse return; a0, s4, s5, s8 pinned to literals;
   the o region (s7, atom 23) with the parse result's bytes 22..26. *)
Definition S3T_PC : Z := AF_check_step + 0x40c.
Definition S3T_RET : Z := AF_check_step + 0x43c.
Definition s3t_o (seg len : Z) : YP09.region :=
YP09.mkRegion (Some 23%nat) 0 36 0 0
[YP09.mkChunk 22 (CVal 1 (SLit 1)); YP09.mkChunk 23 (CVal 1 (SLit seg)); YP09.mkChunk 24 (CVal 2 (SLit len));
 YP09.mkChunk 26 (CVal 1 (SLit 0))].
Definition s3t_facts : facts := mkFacts [(23%nat, mkAF 4096 (2 ^ 47) 3)] [] [].
Definition s3t_r1 : list sv := sr_set sr_atoms 10%bv (SLit 2).
Definition s3t_r2 : list sv := sr_set s3t_r1 20%bv (SLit 2).
Definition s3t_r3 (seg : Z) : list sv := sr_set s3t_r2 21%bv (SLit seg).
Definition s3t_r4 (seg len : Z) : list sv := sr_set (s3t_r3 seg) 24%bv (SLit len).
Definition ss_s3t (seg len : Z) : sstate := mkSS S3T_PC (s3t_r4 seg len) [s3t_o seg len] None s3t_facts.
(* x mod d = 0 with 8 | d and 8 | c gives (x + c) mod 8 = 0 (the kit turns lia's mod handling off). *)
Lemma s3t_mod8_of : forall x d c, 0 < d -> x mod d = 0 -> d mod 8 = 0 -> c mod 8 = 0 -> (x + c) mod 8 = 0.
Proof.
intros x d c Hd Hx Hd8 Hc. apply Z.mod_divide in Hx; [|lia]. apply Z.mod_divide in Hd8; [|lia]. apply Z.mod_divide in Hc; [|lia].
destruct Hx as [p ->]. destruct Hd8 as [q ->]. destruct Hc as [r ->]. apply Z.mod_divide; [lia|]. exists (p * q + r). nia.
Qed.
(* One register at the cut: read from the symbolic state, then the callee-saved chain regs4 = regs3 = regsc = regs2. *)
Local Ltac s3t_reg HS EE HP3 Hpres r z :=
let Hr := fresh "Hr" in prreg HS r Hr; rewrite Hr; clear Hr;
let n := eval vm_compute in (Z.to_nat z) in rewrite (EE n r eq_refl);
etransitivity; [exact (HP3 z ltac:(unfold acallee_saved; lia))|];
etransitivity; [exact (Hpres z ltac:(unfold acallee_saved; lia))|].
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* The sink head is an explicit Section Context the glue instantiates with scene's own (a Theorem Labs lane 22:57Z): never chosen by
   instance search (a global src0_sink_head comes into scope with the relocated core's YI5b). *)
Context (SK : YI16.sink_head). #[local] Existing Instance SK.
Section f.
Context {PI : PAImg scene_listing}.
#[local] Notation SEGS := (@pa_segs _ scene_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ scene_listing PI).
#[local] Notation VAL := (@pa_val _ scene_listing PI).
#[local] Notation BASE := (@pa_val _ scene_listing PI A_TEXT).
Section h.
Variable B : asyms.
(* The hypotheses of lib/AU/P_check_step_S3.v that this part uses, with the same names and text. *)
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
(* reac_ctrl_checksum_verify (a Theorem Labs lane 33d26845cd2). *)
Hypothesis CKV : tctrl_checksum_verify_spec (SK := SK) B.
Let RUNP := SRr_run_pi_AJ (PL := PL_scene) (PI := PI) B LAWS.
Let RUNC := SRr_run_pi_AJ_call (PL := PL_scene) (PI := PI) B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ (PL := PL_scene) (PI := PI) B LAWS.
(* The call and the rest: from the entry of reac_ctrl_checksum_verify (regs at the jal) to the cut. *)
Lemma s3t_after : forall ly S W (regs : bvmap 5 word) mem md ch (blk body k : Z) (b : list byte) (fpos : Z)
  ly2 S2 (W2 : world SEGS) (regs2 : bvmap 5 word) mem2 md2 (regsc : bvmap 5 word) mdc,
  cs_pre B ly S W regs mem md ch blk body k b ->
  cs_frame SK B regs ly S W mem md fpos ly2 S2 W2 regs2 mem2 md2 ->
  (forall i, (i < 50)%nat -> aview SEGS (w_H W2) mem2 (frame_addr ly2 CS_CID fpos + 32 + Z.of_nat i) =
     Some (cp_v (s3_fr b k) i)) ->
  range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF (frame_addr ly2 CS_CID fpos + 32) 50 ->
  getr regsc 10 = w64 (frame_addr ly2 CS_CID fpos + 32) ->
  getr regsc 1 = Z_to_bv 64 (BASE + S3T_RET) ->
  aregs_preserved regs2 regsc ->
  ajournal SEGS B TCHECK_STEP_STK (spZ regs) [] ly S W mem md [(CS_CID, fpos)] ly2 S2 W2 mem2 mdc 0 ->
  SRr SEGS W2 (mkCfg (mkst regsc (Z_to_bv 64 (BASE + AF_reac_ctrl_checksum_verify)) mem2 (seg_rom SEGS)) mdc)
    (fun W3 c3 => exists ly3 S3 regs3 mem3 md3, c3 = cfg_at SEGS CS_PC4 regs3 mem3 md3 /\
       cs_st4 SK B ly S W regs mem md ch blk body k b fpos ly3 S3 W3 regs3 mem3 md3).
Proof.
intros ly S W regs mem md ch blk body k b fpos ly2 S2 W2 regs2 mem2 md2 regsc mdc HP HFR HFB HRA Ra0 Rra Hpres HJc.
pose proof pa_B_ok as HBASE. pose proof (pa_base_lo (PL := PL_scene)) as HBLO.
pose proof HP as (HPRE & Hal32 & Htop32 & Hfr7 & HROD & H10 & H11 & H12 & Hk & HFO & Hbody & Hlen & Hbb & Hblk & Hev & Hlive).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HFR as (HJ & Hablk & Hflagw & Hsaved & Q2 & Q3 & Q4 & Q8 & Q18 & Q25 & Q26 & Q27).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (FFS : TCHECK_STEP_STK = 8496) by reflexivity.
change (Z.to_nat CS_BODY_LEN) with 8904%nat in Hlen. unfold CS_LAST in Hk.
pose proof HJ as (HAR2 & HLY & _ & _ & _ & Hfrs2 & _ & _ & HK1 & _).
pose proof HLY as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
assert (Hin2 : In (CS_CID, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR2 Hin2) as (HFal & HFapp & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ _ _ HAR2 Hin2) as (HF4096 & HFceil & _).
change (fs_frame_bytes CS_CID) with 256 in *.
remember (frame_addr ly2 CS_CID fpos) as F eqn:EF.
remember (flag_addr ly2 CS_CID fpos) as FL eqn:EFL.
pose proof alloc_ceiling_lt as Hac47.
assert (Hp2 : getr regsc 2%bv = getr regs2 2%bv) by exact (Hpres 2 ltac:(unfold acallee_saved; lia)).
assert (Hp3 : getr regsc 3%bv = getr regs2 3%bv) by exact (Hpres 3 ltac:(unfold acallee_saved; lia)).
assert (Hp4 : getr regsc 4%bv = getr regs2 4%bv) by exact (Hpres 4 ltac:(unfold acallee_saved; lia)).
assert (Hp8 : getr regsc 8%bv = getr regs2 8%bv) by exact (Hpres 8 ltac:(unfold acallee_saved; lia)).
assert (Hsp1 : spZ regsc = spZ regs + -128).
{ unfold spZ at 1. rewrite Hp2, Q2. unfold w64, CHECK_STEP_FRAME. rewrite unsigned_lit_small by lia. lia. }
(* the entry chain pushed with check_step's own record (sp0, ra, s0) *)
assert (Hch1 : achain ly2 (aview SEGS (w_H W2) mem2) (spZ regs + -128) (s0Z regsc) ((spZ regs, raZ regs, s0Z regs) :: ch)).
{ unfold s0Z at 1. rewrite Hp8, Q8. unfold w64. rewrite unsigned_lit_small by lia.
  apply (achain_ly_top ly ly2); [exact Etop|].
  apply (achain_push ly (aview SEGS (w_H W) mem) (aview SEGS (w_H W2) mem2) (spZ regs) (s0Z regs) (raZ regs) ch (spZ regs + -128) Hch).
  - lia.
  - intros a Ha. apply HK1; lia.
  - replace (spZ regs - 8) with (spZ regs - 8 - 8 * Z.of_nat 0) by lia. exact (Hsaved 0%nat ltac:(lia)).
  - replace (spZ regs - 16) with (spZ regs - 8 - 8 * Z.of_nat 1) by lia. exact (Hsaved 1%nat ltac:(lia)).
  - exact Hra4.
  - lia.
  - rewrite <- (Z.add_0_r (spZ regs)). exact (s3t_mod8_of (spZ regs) 16 0 ltac:(lia) Hal16 eq_refl eq_refl).
  - lia.
  - lia. }
(* f = F + 32: a frame object of the own frame, and its 32 control-block bytes *)
assert (HOBJ : afobj SEGS B ly2 S2 W2 mem2 (F + 32) 50).
{ apply (afobj_of_own SK SEGS B TCHECK_STEP_STK (spZ regs) [] ly S W mem md [(CS_CID, fpos)] ly2 S2 W2 mem2 mdc 0 CS_CID fpos (F + 32) 50 HJc).
  - left; reflexivity.
  - unfold CS_CID; lia.
  - rewrite <- EF; lia.
  - rewrite <- EF; change (fs_frame_bytes CS_CID) with 256; lia.
  - exact (s3t_mod8_of F 32 32 ltac:(lia) HFal eq_refl eq_refl).
  - exact HRA. }
destruct (s3_bs_ok b k Hlen Hk) as (HBSl & HBSr & HBS0).
assert (HG : garr8 SEGS (mrestrict (w_H W2) mem2) (F + 32 + 18) (s3_bs b k)).
{ intros j Hj. rewrite HBSl in Hj. unfold s3_bs. rewrite nth_map_seq by exact Hj.
  replace (F + 32 + 18 + Z.of_nat j) with (F + 32 + Z.of_nat (18 + j)) by lia.
  apply (val_mem1_of_aview SEGS). apply HFB. lia. }
eapply SRr_bind.
{ eapply (cl_callS B LAWS W2 regsc mem2 (Z_to_bv 64 (BASE + AF_reac_ctrl_checksum_verify)) TCHECK_STEP_STK (spZ regs) []
    ly S W mem md [(CS_CID, fpos)] ly2 S2 mdc 0 TCKV_STK [] 0 (-128) (getr regsc 1) ((spZ regs, raZ regs, s0Z regs) :: ch)
    (fun ly' S' W' regs' mem' md' => ly' = ly2 /\ S' = S2 /\ W' = W2 /\
       getr regs' 10 = w64 (if blocksum (map (Z_to_bv 8) (s3_bs b k)) =? 0 then 0 else -1)) HJc).
  - exact Hsp1.
  - reflexivity.
  - lia.
  - unfold TCKV_STK; lia.
  - unfold TCKV_STK; rewrite FFS; lia.
  - rewrite Hp3, Q3. exact Hgp.
  - rewrite Hp4, Q4. exact Htp.
  - reflexivity.
  - rewrite Rra. apply ret_ok_codeptr_v; [unfold S3T_RET, AF_check_step; lia | reflexivity].
  - rewrite Rra, unsigned_lit_small by (unfold S3T_RET, AF_check_step; lia). unfold S3T_RET, AF_check_step. lia.
  - exact Hch1.
  - intros HPRE1.
    pose proof (CKV ly2 S2 W2 regsc mem2 mdc ((spZ regs, raZ regs, s0Z regs) :: ch) (F + 32) (s3_bs b k) HPRE1 Ra0 HOBJ HG HBSl) as CALL.
    unfold cfg_at, apost_base, A_ctrl_checksum_verifyP in CALL. exact CALL.
  - intros a Ha. destruct (inFP_nil a Ha). }
cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJo & HJi & HP3 & (-> & -> & -> & R10)).
rewrite HBS0 in R10. cbn [Z.eqb] in R10.
rewrite Rra.
(* the return site 0x836d0: a0 pinned to 0, no region *)
remember (Eimg (Ereg regs3 [])) as E3 eqn:HE3.
assert (HEI3 : img_env VAL A_LIM E3) by (subst E3; apply Eimg_env).
assert (EE3 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E3 n = getr regs3 r)
  by (intros n r Hn; subst E3; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HS3 : st_ok_pi SEGS VAL E3 (mkSS S3T_RET (sr_set sr_atoms 10%bv (SLit 0)) [] None (mkFacts [] [] []))
  (restrict (w_H W2) (mkst regs3 (Z_to_bv 64 (BASE + S3T_RET)) mem3 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx.
  apply (ast_ok_pi_set_reg_fp E3 (mkSS S3T_RET sr_atoms [] None (mkFacts [] [] [])) _ 10%bv (SLit 0));
    [| reflexivity | cbn [sv_denot ms_regs mkst]; rewrite R10; reflexivity].
  apply pa_entry_st_ok_full.
  - rewrite HE3. apply regs_ok_Eimg_Ereg.
  - reflexivity.
  - constructor.
  - exact I.
  - split; [exact I | split; exact I]. }
clear HE3.
paj_run_to_shc RUNTOP HS3 HJo 0xe30. { apply awr_ok_nil. }
lazymatch goal with HS3 : st_ok_pi _ _ _ _ (restrict _ ?msx) |- _ => rename msx into ms4 end.
assert (Em4 : ms_mem ms4 = mem3).
{ apply functional_extensionality. intros x.
  lazymatch goal with HF : frame_of _ _ mem3 (ms_mem ms4) |- _ => refine (frame_of_ro _ _ _ _ _ HF x); reflexivity end. }
apply SRr_ret. pmkst HS3. rewrite Em4. rewrite Em4 in HJo.
lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?R _ _ _) ?MD = _ /\ _ => exists ly2, S2, R, mem3, MD end.
split.
{ unfold cfg_at, CS_PC4, A_check_step, AF_check_step.
  lazymatch goal with |- mkCfg (mkst _ ?p1 _ _) _ = mkCfg (mkst _ ?p2 _ _) _ => replace p2 with p1 by (unfold w64; f_equal; lia) end.
  reflexivity. }
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & HKi1 & _ & _ & HKifr & _).
unfold cs_st4, cs_frame. rewrite <- EF, <- EFL.
split; [exact HP|].
split; [exact HJo|]. split; [exact Hablk|].
split.
{ rewrite (rdword_ext (aview SEGS (w_H W2) mem2) (aview SEGS (w_H W2) mem3)); [exact Hflagw|].
  intros kk Hkk. apply (HKifr CS_CID fpos); [exact Hin2 | | apply inFP_nil].
  left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite <- EF. change (fs_frame_bytes CS_CID) with 256. lia. }
split.
{ intros j Hj.
  rewrite (rdword_ext (aview SEGS (w_H W2) mem2) (aview SEGS (w_H W2) mem3)); [exact (Hsaved j Hj)|].
  intros kk Hkk. apply HKi1; unfold TCKV_STK; lia. }
(* the registers: callee-saved over the call, unchanged by the pre-call run and the branch *)
split; [s3t_reg HS3 EE3 HP3 Hpres (2%bv : bv 5) 2; exact Q2|].
split; [s3t_reg HS3 EE3 HP3 Hpres (3%bv : bv 5) 3; exact Q3|].
split; [s3t_reg HS3 EE3 HP3 Hpres (4%bv : bv 5) 4; exact Q4|].
split; [s3t_reg HS3 EE3 HP3 Hpres (8%bv : bv 5) 8; exact Q8|].
split; [s3t_reg HS3 EE3 HP3 Hpres (18%bv : bv 5) 18; exact Q18|].
split; [s3t_reg HS3 EE3 HP3 Hpres (25%bv : bv 5) 25; exact Q25|].
split; [s3t_reg HS3 EE3 HP3 Hpres (26%bv : bv 5) 26; exact Q26 | s3t_reg HS3 EE3 HP3 Hpres (27%bv : bv 5) 27; exact Q27].
Qed.
(* s3u_tail: the second half of cs_S3, at the exact text of TAIL.md (sha256 6abba4a46cee; internal record). *)
Lemma s3u_tail : forall ly S W (regs : bvmap 5 word) mem md ch (blk body k : Z) (b : list byte) (fpos : Z)
  ly2 S2 (W2 : world SEGS) (regs2 : bvmap 5 word) mem2 md2,
  cs_pre B ly S W regs mem md ch blk body k b ->
  cs_frame SK B regs ly S W mem md fpos ly2 S2 W2 regs2 mem2 md2 ->
  getr regs2 10 = w64 2 -> getr regs2 20 = w64 2 ->
  getr regs2 21 = w64 (scene_seg k) -> getr regs2 24 = w64 (scene_len k) ->
  getr regs2 22 = w64 (frame_addr ly2 CS_CID fpos + 32) -> getr regs2 23 = w64 (frame_addr ly2 CS_CID fpos + 128) ->
  (forall i, (i < 36)%nat -> aview SEGS (w_H W2) mem2 (frame_addr ly2 CS_CID fpos + 128 + Z.of_nat i) =
     Some (bv_unsigned (nth i (snd (ctrlparse 50 (s3_fr b k))) cp_z))) ->
  (forall i, (i < 50)%nat -> aview SEGS (w_H W2) mem2 (frame_addr ly2 CS_CID fpos + 32 + Z.of_nat i) =
     Some (cp_v (s3_fr b k) i)) ->
  range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF (frame_addr ly2 CS_CID fpos + 32) 50 ->
  SRr SEGS W2 (cfg_at SEGS (A_check_step + 0x40c) regs2 mem2 md2)
    (fun W3 c3 => exists ly3 S3 regs3 mem3 md3, c3 = cfg_at SEGS CS_PC4 regs3 mem3 md3 /\
       cs_st4 SK B ly S W regs mem md ch blk body k b fpos ly3 S3 W3 regs3 mem3 md3).
Proof.
intros ly S W regs mem md ch blk body k b fpos ly2 S2 W2 regs2 mem2 md2 HP HFR R10 R20 R21 R24 R22 R23 HO HFB HRA.
pose proof pa_B_ok as HBASE. pose proof (pa_base_lo (PL := PL_scene)) as HBLO.
pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & Hk & _ & _ & Hlen & _).
change (Z.to_nat CS_BODY_LEN) with 8904%nat in Hlen. unfold CS_LAST in Hk.
pose proof HFR as (HJ & _).
pose proof HJ as (HAR2 & _ & _ & _ & _ & Hfrs2 & _).
assert (Hin2 : In (CS_CID, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR2 Hin2) as (HFal & _ & _ & _).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ _ _ HAR2 Hin2) as (HF4096 & HFceil & _).
change (fs_frame_bytes CS_CID) with 256 in *.
pose proof alloc_ceiling_lt as Hac47.
destruct (s3_fr_parse b k Hlen Hk) as (_ & P22 & P23 & P24 & P25 & P26).
set (F := frame_addr ly2 CS_CID fpos) in *.
assert (O22 : aview SEGS (w_H W2) mem2 (F + 128 + 22) = Some 1)
  by (pose proof (HO 22%nat ltac:(lia)) as X; rewrite P22 in X; exact X).
assert (O23 : aview SEGS (w_H W2) mem2 (F + 128 + 23) = Some (bv_unsigned (Z_to_bv 8 (scene_seg k))))
  by (pose proof (HO 23%nat ltac:(lia)) as X; rewrite P23 in X; exact X).
assert (O24 : aview SEGS (w_H W2) mem2 (F + 128 + 24) = Some (bv_unsigned (Z_to_bv 8 (scene_len k))))
  by (pose proof (HO 24%nat ltac:(lia)) as X; rewrite P24 in X; exact X).
assert (O25 : aview SEGS (w_H W2) mem2 (F + 128 + 25) = Some 0)
  by (pose proof (HO 25%nat ltac:(lia)) as X; rewrite P25 in X; exact X).
assert (O26 : aview SEGS (w_H W2) mem2 (F + 128 + 26) = Some 0)
  by (pose proof (HO 26%nat ltac:(lia)) as X; rewrite P26 in X; exact X).
remember (Eimg (Ereg regs2 [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U23 : bv_unsigned (ew E 23) = F + 128)
  by (rewrite (EE 23%nat 23%bv eq_refl), R23; unfold w64; apply unsigned_lit_small; lia).
unfold cfg_at.
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ ?pcw _ _) _) _ =>
  replace pcw with (Z_to_bv 64 (BASE + S3T_PC)) by (unfold S3T_PC, A_check_step, w64; rewrite Z.add_assoc; reflexivity) end.
assert (Hcase : (scene_seg k = 1 /\ scene_len k = 24) \/ (scene_seg k = 2 /\ scene_len k = 14) \/
  (scene_seg k = 0 /\ scene_len k = 26)).
{ unfold scene_seg, scene_len. destruct (k =? 0); [left; split; reflexivity|].
  destruct (k =? 342); [right; left; split; reflexivity | right; right; split; reflexivity]. }
destruct Hcase as [[Es El] | [[Es El] | [Es El]]]; rewrite Es in R21, O23; rewrite El in R24, O24;
idtac.
(* each case: the run from the parse return to the call, with (scene_seg k, scene_len k) a literal pair *)
all: lazymatch goal with R21x : getr _ 21 = w64 ?seg, R24x : getr _ 24 = w64 ?len |- _ =>
assert (HS : st_ok_pi SEGS VAL E (ss_s3t seg len)
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + S3T_PC)) mem2 (seg_rom SEGS))));
[ rewrite restrict_mkst_fx; unfold ss_s3t, s3t_r4, s3t_r3, s3t_r2, s3t_r1;
  apply (ast_ok_pi_set_reg_fp E (mkSS S3T_PC (sr_set (sr_set (sr_set sr_atoms 10%bv (SLit 2)) 20%bv (SLit 2)) 21%bv (SLit seg))
    [s3t_o seg len] None s3t_facts) _ 24%bv (SLit len)); [| reflexivity | cbn [sv_denot ms_regs mkst]; rewrite R24; reflexivity];
  apply (ast_ok_pi_set_reg_fp E (mkSS S3T_PC (sr_set (sr_set sr_atoms 10%bv (SLit 2)) 20%bv (SLit 2))
    [s3t_o seg len] None s3t_facts) _ 21%bv (SLit seg)); [| reflexivity | cbn [sv_denot ms_regs mkst]; rewrite R21; reflexivity];
  apply (ast_ok_pi_set_reg_fp E (mkSS S3T_PC (sr_set sr_atoms 10%bv (SLit 2))
    [s3t_o seg len] None s3t_facts) _ 20%bv (SLit 2)); [| reflexivity | cbn [sv_denot ms_regs mkst]; rewrite R20; reflexivity];
  apply (ast_ok_pi_set_reg_fp E (mkSS S3T_PC sr_atoms [s3t_o seg len] None s3t_facts) _ 10%bv (SLit 2));
    [| reflexivity | cbn [sv_denot ms_regs mkst]; rewrite R10; reflexivity];
  apply pa_entry_st_ok_full;
  [ rewrite HE; apply regs_ok_Eimg_Ereg
  | vm_compute; reflexivity
  | apply Forall_cons; [|apply Forall_nil];
    unfold region_ok, s3t_o; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
    rewrite U23; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
    apply Forall_cons;
    [ apply (chunk_ok_val SEGS E _ (F + 128) 22 1 (SLit 1) 1); [reflexivity | cbn; lia | cbn; lia |];
      exact (proj1 (val_mem1_of_aview SEGS _ _ _ _ O22)) |];
    apply Forall_cons;
    [ apply (chunk_ok_val SEGS E _ (F + 128) 23 1 (SLit seg) seg); [reflexivity | cbn; lia | cbn; lia |];
      exact (proj1 (val_mem1_of_aview SEGS _ _ _ _ O23)) |];
    apply Forall_cons;
    [ apply (chunk_ok_val SEGS E _ (F + 128) 24 2 (SLit len) len); [reflexivity | cbn; lia | cbn; lia |];
      let kk := fresh "kk" in let Hkk := fresh "Hkk" in let X := fresh "X" in
      intros kk Hkk; destruct kk as [|[|kk]];
      [ pose proof (proj1 (val_mem1_of_aview SEGS _ _ _ _ O24) 0%nat ltac:(lia)) as X; rewrite X; vm_compute; reflexivity
      | pose proof (proj1 (val_mem1_of_aview SEGS _ _ _ _ O25) 0%nat ltac:(lia)) as X;
        replace (F + 128 + 24 + Z.of_nat 1) with (F + 128 + 25 + Z.of_nat 0) by lia; rewrite X; vm_compute; reflexivity
      | cbn in Hkk; lia ] |];
    apply Forall_cons;
    [ apply (chunk_ok_val SEGS E _ (F + 128) 26 1 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |];
      exact (proj1 (val_mem1_of_aview SEGS _ _ _ _ O26)) |];
    apply Forall_nil
  | split; exact I
  | split; [|split; exact I]; cbn [s3t_facts f_atoms atoms_ok]; split; [|exact I];
    unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U23; change (2 ^ 3) with 8;
    split; [lia|]; split; [exact (s3t_mod8_of F 32 128 ltac:(lia) HFal eq_refl eq_refl) | lia] ]
| ];
paj_run_shc RUNP RUNC HS HJ;
[ unfold ss_s3t; cbn [ss_mem]; apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]
| lazymatch goal with HSx : st_ok _ _ _ (restrict _ ?msx) |- _ => rename msx into msC; rename HSx into HSC end;
  let EmC := fresh "EmC" in
  assert (EmC : ms_mem msC = mem2);
  [ apply functional_extensionality; let x := fresh "x" in intros x;
    lazymatch goal with HF : frame_of _ _ _ (ms_mem _) |- _ => refine (frame_of_ro _ _ _ _ _ HF x); reflexivity end
  | ];
  pmkst HSC; rewrite EmC;
  rewrite EmC in HJ;
  lazymatch goal with |- SRr _ _ (mkCfg (mkst _ ?p _ _) _) _ =>
    replace p with (Z_to_bv 64 (BASE + AF_reac_ctrl_checksum_verify))
      by (cbv [ss_pc setpc]; rewrite pa_sigma_reac_ctrl_checksum_verify; reflexivity) end;
  apply (s3t_after ly S W regs mem md ch blk body k b fpos ly2 S2 W2 regs2 mem2 md2 (ms_regs msC) _ HP HFR HFB HRA);
  [ let X := fresh "X" in prreg HSC (10%bv : bv 5) X; rewrite X; rewrite (EE 22%nat 22%bv eq_refl); exact R22
  | let X := fresh "X" in prreg HSC (1%bv : bv 5) X; rewrite X; unfold S3T_RET, AF_check_step; reflexivity
  | apply aregs_preserved_eqs;
    lazymatch goal with |- getr _ ?r = _ =>
      let X := fresh "X" in prreg HSC r X; rewrite X;
      first [ apply EE; reflexivity | rewrite R20; reflexivity | rewrite R21; reflexivity | rewrite R24; reflexivity ] end
  | exact HJ ] ]
end.
Qed.
End h.
End f.
End d.
Print Assumptions s3u_tail.
