(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/B's walk of pcap_source_open in the asan-ubsan instance of fuzz_pcap
   (libreac v1.9.0; pin fuzz_pcap.asan-ubsan, sha256 9e66f771f22a...; function at 0x811e0 =
   BASE + AF_pcap_source_open, AF = 0xa58), proving lib/A's image-generic contract tpcap_source_open_specX
   (lib/A/Prog/PcapSourceOpenDefs.v) at SEGS = pa_segs, rlo / rhi = pa_relro_lo / pa_relro_hi,
   apath / alen / afile = VAL (A_OBJ 3) / VAL (A_OBJ 4) / VAL (A_OBJ 2) (0x20d00 "<fuzz-input>", g_file_len
   0x5d3e40, g_file 0x5d3e60), with FM_RA and roimg as parameters. At ossv/recipes 25e3d17bdb50 (2026-10-29), there was no released proof of this function at
   this image (rule 24 lookup, a Theorem Labs lane, 22:35Z): the v1.8 ubsan proof (lib/U/Prog/pcap_source_open.v at
   origin/ossv/recipes c8557374ad2e) serves only as the template for the UBSan guards.

   The code. Up to the fopen call it is lib/A's ASan code byte for byte at
   other pcs (asan 0x8145c.. = asan-ubsan 0x811e0..): the prologue saves ra, s0 .. s9 (0x811e0..0x81210) and
   realigns s1 = sp = (sp - 96) & -32 (0x81218); the use-after-return flag is read through the GOT (0x81228
   auipc / 0x8122c ld, listing object 0 = 0x99750) from the runtime cell at 0x81234 (object 16 = 0xa17c0): the
   walk takes it as 1 (the kit's AR_const_law through al_const, with uar_cell_regionP (A_OBJ 16) holding SLit 1;
   the pin's file holds 0 and the runtime sets 1 at init), so 0x81240 `beqz a2` is not taken;
   __asan_stack_malloc_1(0x60) at 0x81248 returns the class-1 frame F (aj_stack_malloc_atS, YC85.v:292), whose
   two caller premises are discharged at op_to_call's frame request: count_cid 1 (frames Sc) < fs_frames 1 from
   op_pre's length (frames Sc) <= 7 through count_cid_le_length and 8 <= fs_frames 1, and the apath premise by
   op_SMP (stack_malloc_progressP from lib/Reusable/YG05.v:70, as cgif_file_fuzzer lib/A/ACed.v:129-130), so
   F >= 4096, 0x8125c `bnez s2` is taken and the machine-frame arm 0x81260..0x81278 is dead; then *(s1) = F
   (0x8127c), the header (0x41b58ab3, objects 10 and 11; 0x812a4..0x812ac), the twelve shadow bytes
   (0x812b8..0x812e4: 0xf1 x4, 0xf8 x3, 0xf3 x5), the mode literal "rb" (object 12, 0x812e8 / 0x812ec; HMODE)
   and the call of libreac_fuzz_fopen (0x812f4) through cl_callS (YC85.v:383) with FOPEN as the callee.

   The cut. This file walks the head: entry -> op_to_call (a Qed checkpoint at the call, op_at_call) ->
   head_to_fopen, which makes the call and establishes PcapSourceOpenPhF.v's op_fopen_ret at the return
   0x812f8. From there PcapSourceOpenPhM.v (op_from_fopen) walks to the two cuts of PcapSourceOpenPh.v and
   PcapSourceOpenB.v (op_from_null / op_from_read) to the return; pb_pcap_source_openX composes the three.
   The three UBSan guards are therefore decided outside this file, at these pcs and against these template lines:
   in PcapSourceOpenPhM.v 0x812f8 `beqz s3` (ps = 0, not taken: ps >= 4096 from op_pre's frame bounds; template
   :114 / :334, premise :93 / :290) and 0x81300 / 0x81304 `andi a0,s3,7; bnez a0` (ps mod 8 <> 0, not taken:
   op_pre's ps mod 8 = 0; template :115 / :335); in PcapSourceOpenB.v 0x81390 / 0x81394 `addi a0,zero,-3;
   bgeu s4,a0` (F + 32 >=u 2^64 - 3, not taken: F + 128 <= alloc_ceiling < 2^47; template :408-412, premise
   :291 and :295-299); all three
   go to the `unimp` at 0x8153c, and every ASan report path 0x81540..0x815b4 is dead because ps's 24 bytes are
   addressable and ps mod 8 = 0. In the head, op_at_call carries what those walks need: ps unwritten and still
   range_addressable, and op_fopen_ret's FILE-block footprint fact for the fclose of the tail.

   The callee hypotheses, used at this image as Section hypotheses: FOPEN : tlibreac_fuzz_fopen_specX
   (lib/A/Prog/PcapFuzzFopenDefs.v), AFREAD : afread_spec (lib/A/Stdio/PFreadISpec.v:138), AFCLOSE :
   afclose_source_spec (lib/A/Stdio/PFclose.v:209), ASM1 : astack_malloc_realizes (lib/Reusable/YG0d.v:285),
   ASF : astack_free_law (lib/Reusable/YG0d.v:301) and FFL : frame_flag_lawP (lib/Reusable/YCbq.v:797), the meter laws MLAW / MLAWF /
   FM, ASIL : asource_img_laws, and the kit's LAWS / TL / TLF / ML. Four instance obligations beyond the kit:
   ROK (roimg reads only image bytes outside the runtime's statics, errno and the open-file list head; applied at
   the fopen call to carry roimg from the entry memory across the prologue and the frame setup), HPATH (the path
   literal's shadow, as a law of every AR state: the frame request's kept clauses do not keep a global's shadow,
   YG0n.v:241 makes it aowned; discharged by the instance through AR_zshadow_law, YG0d.v:435-438), HGX (g_file_len
   and g_file are image bytes outside the runtime's statics and errno; the gx_ok shape of
   lib/A/Prog/PcapEntryDefs.v:366, 395, discharged by the harness), and RO : ro_below_ofl (as
   lib/A/Prog/PcapHarnessTail.v:37). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/B/Prog/PcapSourceOpen.v, with its module paths, module names and numbers changed; 574 of its 653 lines of code are new or changed and 1472 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/model_writeHead.v, with its module names changed; 706 of its 776 lines of code are new or changed and 583 lines of the source are left out. *)
(* text_of (fuzz_link.asan 0x87dc0) on image A: the HEAD of its walk, from the contract's entry to the TABLE cut
   (lib/A/Prog/text_ofDefs.v, +0x144) and the U16 cut (lib/A/Prog/text_ofKit.v, +0x1a8)
   (listing (internal path) (internal record, sha256 1c4fdcbb52aa)):
     +0x00..+0x28  the 64-byte frame and the shadow base (a token run over the frame, the .got word and the cell)
     +0x2c..       the cursor's checks and loads, by the count c1 (the cases 0, 1, 2 and >= 3 fix how many input bytes
                   the code may read):
                   c1 = 0: +0x4c taken, +0x12c..+0x140, the TABLE cut;
                   c1 > 0: b0 := the input's first byte, *own := 0, +0xa4 `bgez`: b0 < 128 -> the TABLE cut;
                   b0 >= 128: up to two more bytes (+0xa8..+0x128 / +0x1a0 / +0x1a4), the U16 cut.
   Each input byte the code reads enters the symbolic state when its count case allows it: a one-byte region
   (to_rIb) and a token shadow entry (to_sh_add), both from the Pre's input facts carried across the stores
   (to_KSI: the low shadow and the input are outside the frame, the cursor and *own). Every leaf states the cut's
   common part through `to_core_of` (tactic to_core_leaf), then the cut's own registers and cursor.

   Section hypotheses: LAWS, TL (PALib), LV (LinkVals).

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b YC88.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem LinkWalk link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkPi LinkWalkCall LinkWalkNoWrite LinkWalkSide.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import model_writeArmsA model_writeSendA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import text_of_c text_ofDefs text_ofKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

Definition TOBx : sv := SOff 32 0.
(* phase 1: the frame, the .got word and the cell; p (atom 10) and o (atom 11) bounded by to_happ *)
Definition to_fA0 : list (nat * afact) :=
  [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
   (10%nat, mkAF 0 (2 ^ 47 - 17) 3); (11%nat, mkAF 0 (2 ^ 47 - 9) 0)].
Definition to_ss0 : sstate :=
  mkSS AF_text_of sr_atoms [stack_region TO_FRAME; got_regionP; bcell_regionP 32] None (mkFacts to_fA0 [] []).
Definition to_SH0 : list shent := [mkSHE 10 0 16; mkSHE 11 0 8].
(* the extra words: the shadow base, the cursor's two words, the input's first three bytes *)
Definition to_extra (c0 c1 : Z) (inp : list byte) : list word :=
  [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 c0; Z_to_bv 64 c1; Z_to_bv 64 (bz inp 0); Z_to_bv 64 (bz inp 1);
   Z_to_bv 64 (bz inp 2)].
(* phase 2's regions: the cursor (atom 10, its words atoms 33 and 34), *own (atom 11) *)
Definition to_rP : YP09.region := YP09.mkRegion (Some 10%nat) 0 16 0 16
  [YP09.mkChunk 0 (CVal 8 (SOff 33 0)); YP09.mkChunk 8 (CVal 8 (SOff 34 0))].
Definition to_rO : YP09.region := YP09.mkRegion (Some 11%nat) 0 8 0 8 [].
(* the input byte at c0 + i (atom 33 the base c0), its value atom n *)
Definition to_rIb (i : Z) (n : nat) : YP09.region :=
  YP09.mkRegion (Some 33%nat) i (i + 1) 0 0 [YP09.mkChunk i (CVal 1 (SOff n 0))].

(* the disjointness of a new region from the state's regions, the atoms' values substituted *)
Ltac to_disj :=
  lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy =>
    let rs2 := eval vm_compute in rsy in let r2 := eval vm_compute in ry in change (all_disjoint Ey r2 rs2) end;
  cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].

(* a run's write permission: the frame's window, the cursor and *own (write-set bytes, apre's ajw) *)
Ltac to_awr Hajw Usp Up Uo :=
  lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ =>
    let rs' := eval vm_compute in rs in change rs with rs' end;
  repeat (apply awr_ok_x_cons;
    [ intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx; rewrite ?Usp, ?Up, ?Uo in Hx;
      first [ lia
            | left; split; [left; lia | lia]
            | apply Hajw; eexists; split; [left; reflexivity | cbn [fst snd]; lia]
            | apply Hajw; eexists; split; [right; left; reflexivity | cbn [fst snd]; lia] ]
    |]);
  apply awr_ok_x_nil.

(* ---- separations, each in its own small context (lia over the walk's context splits every disjunction) ---- *)
(* an input byte is outside the frame, the cursor and *own *)
Lemma to_nZ_in : forall sp p o c0 c1 a,
  c0 + c1 <= sp - 16448 \/ sp <= c0 -> c0 + c1 <= p \/ p + 16 <= c0 -> c0 + c1 <= o \/ o + 8 <= c0 ->
  c0 <= a < c0 + c1 -> ~ (sp - 64 <= a < sp \/ p <= a < p + 16 \/ o <= a < o + 8).
Proof. intros. lia. Qed.
(* a low-shadow byte is outside the frame, the cursor and *own *)
Lemma to_nZ_sh : forall sp p o a,
  0x7fff7f800000 <= sp - 64 ->
  p + 16 <= 0x7fff8000 - 1 \/ (0x10007fff8000 <= p /\ p + 16 <= 0x800000000000 - 1) ->
  o + 8 <= 0x7fff8000 - 1 \/ (0x10007fff8000 <= o /\ o + 8 <= 0x800000000000 - 1) ->
  0x7fff8000 <= a < 0x7fff8000 + 2 ^ 44 -> ~ (sp - 64 <= a < sp \/ p <= a < p + 16 \/ o <= a < o + 8).
Proof. intros. lia. Qed.
(* byte i of [a, a + n) against [b, b + k) *)
Lemma to_apart_at : forall a n b k i, a + n <= b \/ b + k <= a -> 0 <= i < n -> a + i + 1 <= b \/ b + k <= a + i.
Proof. intros. lia. Qed.

(* an atom plus a constant, as a number *)
Lemma to_sv_off : forall Ex n v k, ew Ex n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + k < 2 ^ 64 ->
  bv_unsigned (sv_denot Ex (SOff n k)) = v + k.
Proof. intros Ex n v k H Hv Hk. cbn [sv_denot]. rewrite H, (unsigned_lit_small v Hv). apply unsigned_lit_small. exact Hk. Qed.

(* the shadow address of an atom plus a constant (srli 3, add s4) *)
Lemma to_shadow_sv : forall Ev n k v, bv_unsigned (ew Ev n) = v -> 0 <= v + k < 2 ^ 64 ->
  bv_unsigned (ew Ev 32) = SHADOW_OFF ->
  sv_denot Ev (SAlu ALU_ADD (SAlu ALU_SRL (SOff n k) (SLit 3)) (SOff 32 0)) = Z_to_bv 64 (SHADOW_OFF + (v + k) / 8).
Proof.
  intros Ev n k v H Hk H32.
  rewrite (denot_lit_U Ev (SAlu ALU_ADD (SAlu ALU_SRL (SOff n k) (SLit 3)) (SOff 32 0))).
  rewrite U_SAlu, U_SAlu, !U_SOff, U_SLit. cbn [zalu_raw]. rewrite H, H32. unfold zcanon, M64.
  f_equal. rewrite (Z.mod_small (v + k)) by lia. change (Z.land (3 mod 2 ^ 64) 63) with 3.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  rewrite Z.add_0_r, (Z.mod_small SHADOW_OFF) by (unfold SHADOW_OFF; lia).
  rewrite (Z.mod_small ((v + k) / 8)) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  assert (Hd : 0 <= (v + k) / 8 < 2 ^ 61) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite Z.mod_small; [lia|]. unfold SHADOW_OFF. lia.
Qed.

(* beqz on an atom plus a constant *)
Lemma to_beqz_off : forall Ev n v k, ew Ev n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + k < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot Ev (SOff n k)) (sv_denot Ev (SLit 0)) = (v + k =? 0).
Proof.
  intros Ev n v k H Hv Hk. rewrite branch_eq_U, U_SLit. unfold U. rewrite (to_sv_off Ev n v k H Hv Hk).
  reflexivity.
Qed.

(* the byte b of atom 35, sign-extended (+0x9c lb), against 0 (+0xa4 bgez) *)
Lemma to_sext8 : forall Ev b, ew Ev 35 = Z_to_bv 64 b -> 0 <= b < 256 ->
  branch_taken BC_GE (sv_denot Ev (SExt true 8 (SOff 35 0))) (sv_denot Ev (SLit 0)) = (b <? 128) /\
  (b < 128 -> sv_denot Ev (SExt true 8 (SOff 35 0)) = Z_to_bv 64 b).
Proof.
  intros Ev b H Hb.
  assert (HU : U Ev (SExt true 8 (SOff 35 0)) = zcanon (bv_swrap 8 b)).
  { rewrite U_SExt, (U_atom Ev 35 b H) by lia. change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_small by lia. reflexivity. }
  assert (HS8 : bv_swrap 8 b = if b <? 128 then b else b - 256).
  { unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 8) with 256.
    change (256 `div` 2) with 128. destruct (Z.ltb_spec b 128); lia. }
  split.
  - cbn [branch_taken]. rewrite bv_lts_signed.
    change (bv_signed (sv_denot Ev (SExt true 8 (SOff 35 0)))) with (Sg Ev (SExt true 8 (SOff 35 0))).
    change (bv_signed (sv_denot Ev (SLit 0))) with (Sg Ev (SLit 0)).
    rewrite S_SLit, S_of_U, HU, HS8.
    unfold zcanon, M64, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
    change (2 ^ 64 `div` 2) with (2 ^ 63).
    destruct (Z.ltb_spec b 128) as [Hl | Hl]; cbn [negb];
      [apply Bool.negb_true_iff, Z.ltb_ge | apply Bool.negb_false_iff, Z.ltb_lt]; lia.
  - intros Hl. rewrite (denot_lit_U Ev (SExt true 8 (SOff 35 0))), HU, HS8. f_equal.
    destruct (Z.ltb_spec b 128); [|lia]. apply zcanon_id. unfold M64. lia.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation VAL := (@pa_val _ link_listing PI).
#[local] Notation BASE := (@pa_val _ link_listing PI A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Variable CTX : list (list Z).
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis LV : LinkVals.

(* fold a run's frame and growth onto the bytes kept since the call (outside Zs) *)
Ltac to_fold UN GR Zs Usp Up Uo :=
  lazymatch type of UN with forall a, _ -> _ -> aview ?sg (w_H ?Wx) ?mOld a = aview _ _ ?m0 a =>
  lazymatch goal with
  | HFrx : frame_of ?Ex ?rsx (mrestrict (w_H Wx) mOld) (mrestrict (w_H Wx) ?mNew),
    HGx : mem_grows (mrestrict (w_H Wx) mOld) (mrestrict (w_H Wx) ?mNew) |- _ =>
    let UNk := fresh "UNk" in
    pose proof (kept_of_frame (segs := sg) Ex rsx (w_H Wx) mOld mNew Zs HFrx
      ltac:(intros bbW wloW whiW aW HinW HrrW; vm_compute in HinW;
            repeat (destruct HinW as [HqW | HinW]; [injection HqW as <- <- <-; cbn [base_val] in HrrW;
                    rewrite ?Usp, ?Up, ?Uo in HrrW; unfold Zs; lia|]); destruct HinW)) as UNk;
    let UN' := fresh "UN" in
    assert (UN' : forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview sg (w_H Wx) mNew a = aview sg (w_H Wx) m0 a)
      by (intros a Ha Hn; rewrite (UNk a Ha Hn); exact (UN a Ha Hn));
    let GR' := fresh "GR" in
    assert (GR' : mem_grows (mrestrict (w_H Wx) m0) (mrestrict (w_H Wx) mNew)) by exact (mem_grows_trans _ _ _ GR HGx);
    clear UN GR UNk HFrx HGx; rename UN' into UN; rename GR' into GR;
    try match goal with HFx : forall x : word, _ -> mNew x = mOld x |- _ => clear HFx end
  end end.

Lemma to_obj_vals : VAL (A_OBJ 1) = 0xa19d0 /\ VAL (A_OBJ 64) = 0xaa438 /\ VAL A_TEXT = 0x821cc.
Proof.
  repeat split; first [rewrite (lv_text LV); reflexivity | rewrite (lv_obj LV) by (vm_compute; lia); reflexivity].
Qed.

(* an 8-byte chunk of a region, as the word its value denotes *)
Lemma to_word_of_region : forall Ex m (r : YP09.region) (n : nat) bv off e,
  region_ok SEGS Ex m r -> YP09.r_base r = Some n -> bv_unsigned (ew Ex n) = bv ->
  In (YP09.mkChunk off (CVal 8 e)) (YP09.r_chunks r) ->
  val_mem SEGS m (bv + off) 8 (bv_unsigned (sv_denot Ex e)).
Proof.
  intros Ex m [rb lo hi wlo whi cs] n bv off e HR Hb Hbv Hin. cbn [YP09.r_base YP09.r_chunks] in Hb, Hin. subst rb.
  pose proof (bv_unsigned_in_range 64 (sv_denot Ex e)) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
  exact (field_of_region Ex m n bv cs lo hi wlo whi off 8%N e (bv_unsigned (sv_denot Ex e)) HR Hbv Hin
    (eq_sym (Z_to_bv_bv_unsigned 64 (sv_denot Ex e))) ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Hr) ltac:(cbn; lia)).
Qed.

Lemma to_awrange_grows : forall (m m' : word -> option byte) b n,
  awrange SEGS m b n -> mem_grows m m' -> awrange SEGS m' b n.
Proof. intros m m' b n H HG i Hi. exact (wview_grows SEGS m m' _ HG (H i Hi)). Qed.

Lemma to_abuf16 : forall (m : word -> option byte) b v0 v1, 0 <= b -> b + 16 <= 2 ^ 64 ->
  val_mem SEGS m b 8 v0 -> val_mem SEGS m (b + 8) 8 v1 -> awrange SEGS m b 16 -> abuf SEGS m b 16.
Proof.
  intros m b v0 v1 H0 H1 V0 V1 HW. exists (Z_to_le_bytes 8 v0 ++ Z_to_le_bytes 8 v1).
  rewrite length_app, !length_Z_to_le_bytes. split; [reflexivity|]. split; [|exact HW].
  apply (mw_abytes_cat SEGS m b (b + 8)); [apply mw_abytes_le; [lia | lia | exact V0] | rewrite length_Z_to_le_bytes; lia |].
  apply mw_abytes_le; [lia | lia | exact V1].
Qed.

Lemma to_abuf8 : forall (m : word -> option byte) b v0, 0 <= b -> b + 8 <= 2 ^ 64 ->
  val_mem SEGS m b 8 v0 -> awrange SEGS m b 8 -> abuf SEGS m b 8.
Proof.
  intros m b v0 H0 H1 V0 HW. exists (Z_to_le_bytes 8 v0).
  rewrite length_Z_to_le_bytes. split; [reflexivity|]. split; [|exact HW].
  apply mw_abytes_le; [lia | lia | exact V0].
Qed.

Lemma to_grow : forall (H : word -> bool) (m m' : word -> option byte),
  mem_grows (mrestrict H m) (mrestrict H m') -> forall a, apresent H m a -> apresent H m' a.
Proof.
  intros H m m' HG a (Hh & b & Hb). split; [exact Hh|].
  assert (Hm : mrestrict H m (Z_to_bv 64 a) <> None) by (unfold mrestrict; rewrite Hh, Hb; discriminate).
  specialize (HG _ Hm). unfold mrestrict in HG. rewrite Hh in HG.
  destruct (m' (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity | exfalso; exact (HG eq_refl)].
Qed.

(* byte i of bytes at a, as a 1-byte value *)
Lemma to_byte_val : forall (m : word -> option byte) a (inp : list byte) i,
  (i < length inp)%nat -> abytes SEGS m a inp -> val_mem SEGS m (a + Z.of_nat i) 1 (bz inp i).
Proof.
  intros m a inp i Hi (_ & _ & Hb) kk Hk. assert (kk = 0%nat) as -> by lia.
  rewrite Z.add_0_r, (Hb i Hi), (nth_error_nth' _ (Z_to_bv 8 0) Hi). f_equal.
  unfold bz. pose proof (bv_unsigned_in_range 8 (nth i inp (Z_to_bv 8 0))) as Hr.
  change (bv_modulus 8) with 256 in Hr.
  assert (Hle : YO0f.le_byte (bv_unsigned (nth i inp (Z_to_bv 8 0))) 1 0 = bv_unsigned (nth i inp (Z_to_bv 8 0))).
  { unfold YO0f.le_byte. replace (2 ^ (8 * Z.of_nat 1)) with 256 by reflexivity.
    replace (8 * Z.of_nat 0) with 0 by reflexivity. rewrite Z.shiftr_0_r. rewrite !Z.mod_small by lia. reflexivity. }
  rewrite Hle. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

(* an 8-byte chunk of a region based at an atom, read back as a word of the view *)
Lemma to_region_word : forall Ex H m (r : YP09.region) (b : nat) bv off (n : nat),
  region_ok SEGS Ex (mrestrict H m) r -> YP09.r_base r = Some b -> bv_unsigned (ew Ex b) = bv ->
  In (YP09.mkChunk off (CVal 8 (SOff n 0))) (YP09.r_chunks r) ->
  rdword (aview SEGS H m) (bv + off) = Some (bv_unsigned (ew Ex n)).
Proof.
  intros Ex H m [rb lo hi wlo whi cs] b bv off n HR Hb Hbv Hin. cbn [YP09.r_base YP09.r_chunks] in Hb, Hin. subst rb.
  pose proof (bv_unsigned_in_range 64 (ew Ex n)) as Hr.
  apply (rdword_of_val_mem SEGS); [| change (bv_modulus 64) with (2 ^ 64) in Hr; exact Hr].
  exact (field_of_region Ex (mrestrict H m) b bv cs lo hi wlo whi off 8%N (SOff n 0) (bv_unsigned (ew Ex n)) HR Hbv Hin
    ltac:(cbn [sv_denot]; rewrite Z.add_0_r; reflexivity)
    ltac:(change (2 ^ (8 * Z.of_N 8)) with (bv_modulus 64); exact Hr) ltac:(cbn; lia)).
Qed.

Lemma to_sv_off0 : forall Ex n v, ew Ex n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (sv_denot Ex (SOff n 0)) = v.
Proof. intros Ex n v H Hv. cbn [sv_denot]. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned. apply unsigned_lit_small. exact Hv. Qed.

(* every cut before the malloc, from what a leaf of the run shows *)
Lemma to_core_of : forall cx (ms3 : machine_state) md3 pcv v0 v1,
  to_pre SK B MT CTX cx ->
  ms3 = mkst (ms_regs ms3) pcv (ms_mem ms3) (seg_rom SEGS) ->
  ajournal_gx SEGS B (to_G cx) (to_XO cx) (to_OUT cx) (to_STK cx) (to_sp0 cx) (to_FP cx)
    (to_ly cx) (to_S cx) (to_W0 cx) (to_mem0 cx) (to_md0 cx) (to_own cx)
    (to_lyc cx) (to_Sc cx) (to_W cx) (ms_mem ms3) md3 (to_k cx) ->
  m_fds md3 = m_fds (to_mdc cx) -> m_fs md3 = m_fs (to_mdc cx) ->
  getr (ms_regs ms3) 2 = w64 (to_sp cx - TO_FRAME) -> getr (ms_regs ms3) 8 = w64 (to_o cx) ->
  getr (ms_regs ms3) 20 = w64 SHADOW_OFF ->
  (forall r, In r TO_UNTOUCHED -> getr (ms_regs ms3) (Z_to_bv 5 r) = getr (to_regs cx) (Z_to_bv 5 r)) ->
  (forall j, (j < 7)%nat ->
     rdword (aview SEGS (w_H (to_W cx)) (ms_mem ms3)) (to_sp cx - 8 - 8 * Z.of_nat j)
     = Some (bv_unsigned (getr (to_regs cx) (Z_to_bv 5 (nth j TO_SAVED 0))))) ->
  (forall a, 0 <= a < 2 ^ 64 ->
     ~ (to_sp cx - 64 <= a < to_sp cx \/ to_p cx <= a < to_p cx + 16 \/ to_o cx <= a < to_o cx + 8) ->
     aview SEGS (w_H (to_W cx)) (ms_mem ms3) a = aview SEGS (w_H (to_W cx)) (to_memc cx) a) ->
  mem_grows (rdW (to_W cx) (to_memc cx)) (rdW (to_W cx) (ms_mem ms3)) ->
  au64_at SEGS (rdW (to_W cx) (ms_mem ms3)) (to_p cx) v0 ->
  au64_at SEGS (rdW (to_W cx) (ms_mem ms3)) (to_p cx + 8) v1 ->
  au64_at SEGS (rdW (to_W cx) (ms_mem ms3)) (to_o cx) 0 ->
  to_core SK B cx ms3 md3.
Proof.
  intros cx ms3 md3 pcv v0 v1 HPX Hms HJ Hfd Hfs R2 R8 R20 RU SV UN GR V0 V1 VO.
  destruct (ms_shape_mkst SEGS ms3 _ _ _ Hms) as (Hr & Hsv & Hrom & Hfr & Hfc & _).
  pose proof (to_win SK B MT CTX cx HPX) as (_ & _ & _ & Hw1 & Hw2).
  pose proof (to_pre_P SK B MT CTX cx HPX) as
    (c0 & c1 & inp & _ & _ & _ & _ & Hbufp & _ & _ & _ & _ & Hbufo & _).
  assert (HK : TEXT_OF_AK = 16448) by reflexivity.
  unfold to_core. cbv zeta.
  do 13 (split; [assumption|]).
  split.
  { intros a Ha Hw HE. apply UN; [exact Ha|]. intros [Hq | [Hq | Hq]].
    - apply Hw. rewrite HK. lia.
    - apply HE. unfold to_E, inFP, to_wr, text_of_awr. exists (to_p cx, to_p cx + 16).
      split; [left; reflexivity | cbn [fst snd]; exact Hq].
    - apply HE. unfold to_E, inFP, to_wr, text_of_awr. exists (to_o cx, to_o cx + 8).
      split; [right; left; reflexivity | cbn [fst snd]; exact Hq]. }
  split; [intros a Ha; exact (to_grow _ _ _ GR a Ha)|].
  split.
  { intros a Ha. apply (aj_gx_present SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia. }
  destruct Hbufp as (jp & Hjp & (Hp0 & Hp1 & _) & Hwp). rewrite Hjp in Hp1.
  destruct Hbufo as (jo & Hjo & (Ho0 & Ho1 & _) & Hwo). rewrite Hjo in Ho1.
  rewrite Hjp in Hwp. rewrite Hjo in Hwo.
  split; [apply (to_abuf16 _ _ v0 v1 Hp0 Hp1 V0 V1); exact (to_awrange_grows _ _ _ _ Hwp GR)|].
  split; [exact VO|].
  apply (to_abuf8 _ _ 0 Ho0 Ho1 VO); exact (to_awrange_grows _ _ _ _ Hwo GR).
Qed.

(* the TABLE cut from a cut before the malloc, the selector and the cursor *)
Lemma to_gi_table_of : forall cx (ms3 : machine_state) md3,
  to_pre SK B MT CTX cx ->
  ms_pc_val ms3 = w64 (BASE + TO_CUT_TABLE) ->
  to_core SK B cx ms3 md3 ->
  (exists b, getr (ms_regs ms3) 11 = w64 b /\ 0 <= b < 128) ->
  (forall c0 c1, au64_at SEGS (to_m0 cx) (to_p cx) c0 -> au64_at SEGS (to_m0 cx) (to_p cx + 8) c1 ->
     0 <= c0 < 2 ^ 64 -> 0 <= c1 < 2 ^ 64 ->
     exists adv, 0 <= adv <= c1 /\ au64_at SEGS (rdW (to_W cx) (ms_mem ms3)) (to_p cx) (c0 + adv) /\
       au64_at SEGS (rdW (to_W cx) (ms_mem ms3)) (to_p cx + 8) (c1 - adv)) ->
  to_gi_table SK B cx ms3 md3.
Proof.
  intros cx ms3 md3 HPX Hpc HC Hsel Hcur.
  destruct HC as (Hr & Hsv & Hrom & Hfr & Hfc & HJ & Hfd & Hfs & R2 & R8 & R20 & RU & SV & UN & PR & WP & BP & VO & BO).
  destruct (to_table_part SK B MT CTX cx ms3 HPX (to_pre_happ SK B MT CTX cx HPX) UN) as (TR & TE).
  unfold to_gi_table. cbv zeta.
  repeat (split; [eassumption|]). exact TE.
Qed.

(* the U16 cut from a cut before the malloc, the input consumed and the registers the u16 path reads *)
Lemma to_gi_u16_of : forall cx (ms3 : machine_state) md3 c0 c1 inp adv,
  ms_pc_val ms3 = w64 (BASE + TO_CUT_U16) ->
  to_core SK B cx ms3 md3 ->
  to_inp cx c0 c1 inp ->
  1 <= adv <= 3 -> adv <= c1 -> (adv < 3 -> adv = c1) -> 128 <= bz inp 0 ->
  getr (ms_regs ms3) 10 = w64 (to_p cx + 8) -> getr (ms_regs ms3) 12 = w64 (to_p cx) ->
  getr (ms_regs ms3) 14 = w64 (SHADOW_OFF + (to_p cx + 8) / 8) ->
  getr (ms_regs ms3) 15 = w64 (SHADOW_OFF + to_p cx / 8) ->
  getr (ms_regs ms3) 21 = w64 (SHADOW_OFF + to_o cx / 8) ->
  getr (ms_regs ms3) 16 = w64 (if 2 <=? adv then bz inp 1 else 0) ->
  getr (ms_regs ms3) 11 = w64 (if adv =? 3 then bz inp 2 else 0) ->
  au64_at SEGS (rdW (to_W cx) (ms_mem ms3)) (to_p cx) (c0 + adv) ->
  au64_at SEGS (rdW (to_W cx) (ms_mem ms3)) (to_p cx + 8) (c1 - adv) ->
  to_gi_u16 SK B cx ms3 md3.
Proof.
  intros. unfold to_gi_u16. cbv zeta. exists c0, c1, inp, adv. repeat (split; [eassumption|]). assumption.
Qed.

(* the input byte i as a region of a state whose memory m shows the call's input bytes *)
Lemma to_rIb_ok : forall Ev (m m0 : word -> option byte) c0 c1 inp i n,
  bv_unsigned (ew Ev 33) = c0 -> ew Ev n = Z_to_bv 64 (bz inp (Z.to_nat i)) -> 0 <= i < c1 ->
  abytes SEGS m0 c0 inp -> Z.of_nat (length inp) = c1 ->
  (forall a, c0 <= a < c0 + c1 -> mbyte SEGS m a = mbyte SEGS m0 a) ->
  region_ok SEGS Ev m (to_rIb i n).
Proof.
  intros Ev m m0 c0 c1 inp i n U33 En Hi Hinp Hlen KI.
  pose proof Hinp as (Ha0 & Ha1 & _).
  unfold region_ok, to_rIb. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U33. split; [lia|]. split; [lia|]. split; [intros o' Ho'; lia|].
  apply Forall_cons; [|apply Forall_nil].
  pose proof (bz_rng inp (Z.to_nat i)) as Hb.
  apply (chunk_ok_val SEGS _ _ c0 i 1 (SOff n 0) (bz inp (Z.to_nat i))).
  - cbn [sv_denot]. rewrite En, Z.add_0_r, unsigned_lit_small by lia. reflexivity.
  - cbn. lia.
  - cbn. lia.
  - intros j Hj. cbn in Hj. rewrite KI by lia.
    pose proof (to_byte_val m0 c0 inp (Z.to_nat i) ltac:(lia) Hinp j Hj) as V.
    rewrite Z2Nat.id in V by lia. exact V.
Qed.

(* the input byte i's shadow entry, at a memory m whose low shadow is the call's *)
Lemma to_sh_add : forall Ev (m m0 : word -> option byte) SH c0 c1 i,
  bv_unsigned (ew Ev 33) = c0 -> bv_unsigned (ew Ev 32) = SHADOW_OFF -> 0 <= i < c1 ->
  range_addressable (ard SEGS m0) SHADOW_OFF c0 c1 -> amem_range c0 c1 ->
  (forall a, SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44 -> mbyte SEGS m a = mbyte SEGS m0 a) ->
  sh_ok SEGS TOBx SH Ev m -> sh_ok SEGS TOBx (mkSHE 33 i (i + 1) :: SH) Ev m.
Proof.
  intros Ev m m0 SH c0 c1 i U33 U32 Hi Hra Ham KS HSH.
  pose proof (bv_unsigned_in_range 64 (ew Ev 33)) as Hc0. rewrite U33 in Hc0. change (bv_modulus 64) with (2 ^ 64) in Hc0.
  apply Forall_cons; [|exact HSH].
  unfold shent_ok, app_apart; cbn [she_m she_lo she_hi]; unfold TOBx; rewrite !lf_U_reg, U32, U33.
  rewrite Z.min_l, Z.max_r by lia.
  unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham.
  split.
  - intros x Hx. destruct (Hra x ltac:(lia)) as (s & Hs & Hok). exists s. split; [|exact Hok].
    unfold rd_of. rewrite KS; [exact Hs|]. unfold shadow_of_addr, SHADOW_OFF. split; [|lia].
    pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). lia.
  - intros a Ha. unfold SHADOW_OFF. lia.
Qed.

(* the low shadow and the input bytes are the call's while only the frame, the cursor and *own change *)
Ltac to_KSI UN KS KI W memc regs p o c0 c1 HSP HAp HAo Hafi Hapip Hapio :=
  lazymatch type of UN with forall a, _ -> _ -> aview _ _ ?mN a = _ =>
  assert (KS : forall a, SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44 -> mbyte SEGS (rdW W mN) a = mbyte SEGS (rdW W memc) a)
    by (intros a Ha; apply (mbyte_of_aview_eq SEGS); apply UN;
        [unfold SHADOW_OFF in Ha; lia | exact (to_nZ_sh (spZ regs) p o a HSP HAp HAo Ha)]);
  assert (KI : forall a, c0 <= a < c0 + c1 -> mbyte SEGS (rdW W mN) a = mbyte SEGS (rdW W memc) a)
    by (intros a Ha; apply (mbyte_of_aview_eq SEGS); apply UN;
        [lia | exact (to_nZ_in (spZ regs) p o c0 c1 a Hafi Hapip Hapio Ha)]) end.

Fixpoint to_ridx (n : nat) (rs : list YP09.region) (i : nat) : nat :=
  match rs with
  | [] => i
  | r :: rs' => match YP09.r_base r with
                | Some m => if Nat.eqb m n then i else to_ridx n rs' (S i)
                | None => to_ridx n rs' (S i) end
  end.
(* the region of a state based at atom n *)
Ltac to_region HS n HR :=
  lazymatch type of HS with st_ok_pi _ _ _ ?ss _ =>
    let i := eval vm_compute in (to_ridx n (ss_mem ss) 0%nat) in spregion HS i HR end.
(* a register of an st_ok_pi state as the denotation of its symbolic value, at the state's environment *)
Ltac to_reg_raw HS r Q :=
  lazymatch type of HS with st_ok_pi _ _ ?Ev ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H Ev ss ms r HS) as Q;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Q end.
(* one saved word of the prologue, read off the frame region (atom 2) *)
Ltac to_save HRs Usp EREG :=
  lazymatch goal with |- rdword _ (?sp - 8 - 8 * Z.of_nat ?j) = Some (bv_unsigned (getr ?rg (Z_to_bv 5 (nth ?j TO_SAVED 0)))) =>
    let e := eval vm_compute in (nth j TO_SAVED 0) in
    let n := eval vm_compute in (Z.to_nat e) in
    let off := eval vm_compute in (-8 - 8 * Z.of_nat j) in
    replace (sp - 8 - 8 * Z.of_nat j) with (sp + off) by lia;
    replace (Z_to_bv 5 (nth j TO_SAVED 0)) with (Z_to_bv 5 (Z.of_nat n)) by reflexivity;
    rewrite <- (EREG n ltac:(lia));
    rewrite (to_region_word _ _ _ _ 2%nat sp off n HRs eq_refl Usp
      ltac:(cbn [YP09.r_chunks]; repeat (first [left; reflexivity | right])));
    reflexivity
  end.

(* the facts of the entry environment E0, restated at the environment of HS (fresh atoms only at 512 and up) *)
Ltac to_envs HS E0 Usp U10 U11 E32 EREG AG Usp' U10' U11' E32' EREG' :=
  lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
    assert (AG : forall n, (n < 512)%nat -> ew Ev n = ew E0 n)
      by (intros ? ?; repeat rewrite ew_ewset_other by lia; reflexivity);
    pose proof Usp as Usp'; rewrite <- (AG 2%nat ltac:(lia)) in Usp';
    pose proof U10 as U10'; rewrite <- (AG 10%nat ltac:(lia)) in U10';
    pose proof U11 as U11'; rewrite <- (AG 11%nat ltac:(lia)) in U11';
    pose proof E32 as E32'; rewrite <- (AG 32%nat ltac:(lia)) in E32';
    pose proof (fun r (Hr : (r < 32)%nat) => eq_trans (AG r ltac:(lia)) (EREG r Hr)) as EREG'
  end.

(* to_core at a leaf: the run's state HS, the journal HJ, the bytes kept UN and the growth GR; the registers read
   back at the entry environment (EREG0 Usp0 E320: prreg normalizes the fresh atoms away), the regions at HS's
   (EREGx Uspx U10x U11x) *)
Ltac to_core_leaf cx regs W o HPX HS HJ UN GR EREG0 Usp0 E320 EREGx Uspx U10x U11x :=
  let Hms := fresh "Hms" in
  pose proof (st_ok_pi_restrict_mkst _ _ _ _ HS eq_refl) as Hms; cbn [ss_pc] in Hms;
  let Q2 := fresh "Q" in let Q8 := fresh "Q" in let Q20 := fresh "Q" in
  prreg HS (2%bv : bv 5) Q2; prreg HS (8%bv : bv 5) Q8; prreg HS (20%bv : bv 5) Q20;
  let HRs := fresh "HRs" in let HRp := fresh "HRp" in let HRo := fresh "HRo" in
  to_region HS 2%nat HRs; to_region HS 10%nat HRp; to_region HS 11%nat HRo;
  eapply (to_core_of cx _ _ _ _ _ HPX Hms HJ);
  [ repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity
  | repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity
  | refine (eq_trans Q2 _); rewrite Usp0; change (to_sp cx) with (spZ regs); unfold w64, TO_FRAME; f_equal; lia
  | refine (eq_trans Q8 _); rewrite (EREG0 11%nat ltac:(lia)); change (to_o cx) with o;
    unfold w64, o, aarg, argZ; rewrite Z_to_bv_bv_unsigned; reflexivity
  | refine (eq_trans Q20 _); rewrite E320; reflexivity
  | let r := fresh "r" in let Hr := fresh "Hr" in
    intros r Hr; unfold TO_UNTOUCHED in Hr; cbn [In] in Hr; change (to_regs cx) with regs;
    repeat (destruct Hr as [<- | Hr];
      [ lazymatch goal with |- getr _ (Z_to_bv 5 ?c) = _ =>
          let Q := fresh "Q" in prreg HS (Z_to_bv 5 c) Q; refine (eq_trans Q _);
          let nn := eval vm_compute in (Z.to_nat c) in exact (EREG0 nn ltac:(lia)) end
      | ]);
    destruct Hr
  | let j := fresh "j" in let Hj := fresh "Hj" in
    intros j Hj; change (to_sp cx) with (spZ regs); change (to_regs cx) with regs; change (to_W cx) with W;
    destruct j as [|[|[|[|[|[|[|j]]]]]]]; [to_save HRs Uspx EREGx .. | lia]
  | exact UN
  | exact GR
  | let V := fresh "V" in
    pose proof (to_word_of_region _ _ _ 10%nat _ 0 _ HRp eq_refl U10x
      ltac:(cbn [YP09.r_chunks]; repeat (first [left; reflexivity | right]))) as V; rewrite Z.add_0_r in V; exact V
  | exact (to_word_of_region _ _ _ 10%nat _ 8 _ HRp eq_refl U10x
      ltac:(cbn [YP09.r_chunks]; repeat (first [left; reflexivity | right])))
  | let V := fresh "V" in
    pose proof (to_word_of_region _ _ _ 11%nat _ 0 _ HRo eq_refl U11x
      ltac:(cbn [YP09.r_chunks]; repeat (first [left; reflexivity | right]))) as V; rewrite Z.add_0_r in V;
    cbn [sv_denot] in V; exact V ].

(* the U16 cut at a leaf of the run, adv input bytes consumed (nadv = - adv); the leaf's environment facts
   AGn Uspn U10n U11n EREGn, then the walk's names (Ltac takes no free hypothesis names) *)
Ltac to_u16_leaf adv nadv AGn Uspn U10n U11n EREGn
    HS HJ UN GR U16 cx HPX c0 c1 inp regs W p o EREG Usp E32 U10 U32 E33 E34 E36 E37 Hc0r Hc1r PREI Hc :=
  let U32n := fresh "U32n" in pose proof U32 as U32n; rewrite <- (AGn 32%nat ltac:(lia)) in U32n;
  let E33n := fresh "E33n" in pose proof E33 as E33n; rewrite <- (AGn 33%nat ltac:(lia)) in E33n;
  let E34n := fresh "E34n" in pose proof E34 as E34n; rewrite <- (AGn 34%nat ltac:(lia)) in E34n;
  let HRp := fresh "HRp" in to_region HS 10%nat HRp;
  let Q10 := fresh "Q" in let Q12 := fresh "Q" in let Q16 := fresh "Q" in let Q11 := fresh "Q" in
  prreg HS (10%bv : bv 5) Q10; prreg HS (12%bv : bv 5) Q12; prreg HS (16%bv : bv 5) Q16; prreg HS (11%bv : bv 5) Q11;
  let Q14 := fresh "Q" in let Q15 := fresh "Q" in let Q21 := fresh "Q" in
  to_reg_raw HS (14%bv : bv 5) Q14; to_reg_raw HS (15%bv : bv 5) Q15; to_reg_raw HS (21%bv : bv 5) Q21;
  lazymatch goal with |- SRr _ _ {| cfg_ms := ?msF; cfg_model := ?mdF |} _ =>
    apply (U16 cx msF mdF HPX); apply (to_gi_u16_of cx msF mdF c0 c1 inp adv) end;
  [ let Hms := fresh "Hms" in let Hpc := fresh "Hpc" in
    pose proof (st_ok_pi_restrict_mkst _ _ _ _ HS eq_refl) as Hms; cbn [ss_pc] in Hms;
    destruct (ms_shape_mkst SEGS _ _ _ _ Hms) as (_ & _ & _ & _ & _ & Hpc); rewrite Hpc;
    unfold w64; apply (f_equal (Z_to_bv 64)); unfold TO_CUT_U16, AF_text_of; lia
  | to_core_leaf cx regs W o HPX HS HJ UN GR EREG Usp E32 EREGn Uspn U10n U11n
  | exact PREI
  | lia | lia | intros; lia | exact Hc
  | refine (eq_trans Q10 _); rewrite U10; reflexivity
  | refine (eq_trans Q12 _); rewrite (EREG 10%nat ltac:(lia)); change (to_p cx) with p;
    unfold w64, p, aarg, argZ; rewrite Z_to_bv_bv_unsigned; reflexivity
  | refine (eq_trans Q14 _); rewrite (to_shadow_sv _ 10 8 p U10n ltac:(lia) U32n); reflexivity
  | refine (eq_trans Q15 _); rewrite (to_shadow_sv _ 10 0 p U10n ltac:(lia) U32n), Z.add_0_r; reflexivity
  | refine (eq_trans Q21 _); rewrite (to_shadow_sv _ 11 0 o U11n ltac:(lia) U32n), Z.add_0_r; reflexivity
  | refine (eq_trans Q16 _); first [reflexivity | rewrite E36; reflexivity]
  | refine (eq_trans Q11 _); first [reflexivity | rewrite E37; reflexivity]
  | let V := fresh "V" in
    pose proof (to_word_of_region _ _ _ 10%nat p 0 _ HRp eq_refl U10n
      ltac:(cbn [YP09.r_chunks]; repeat (first [left; reflexivity | right]))) as V; rewrite Z.add_0_r in V;
    rewrite (to_sv_off _ 33 c0 adv E33n Hc0r ltac:(lia)) in V; exact V
  | let V := fresh "V" in
    pose proof (to_word_of_region _ _ _ 10%nat p 8 _ HRp eq_refl U10n
      ltac:(cbn [YP09.r_chunks]; repeat (first [left; reflexivity | right]))) as V;
    rewrite (to_sv_off _ 34 c1 nadv E34n Hc1r ltac:(lia)) in V; replace (c1 - adv) with (c1 + nadv) by lia; exact V ].

Theorem to_head : to_table_obl SK B MT CTX -> to_u16_obl SK B MT CTX ->
  forall rlo rhi, text_of_acontract SK SEGS rlo rhi B MT CTX.
Proof.
intros TAB U16 rlo rhi. unfold text_of_acontract, aleaf_alloc_rd.
intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch HA HRD Hlive Hmo Hch HCTX HLP HP.
set (cx := mkTOCX rlo rhi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch).
assert (HPX : to_pre SK B MT CTX cx)
  by exact (conj HA (conj HRD (conj Hlive (conj Hmo (conj Hch (conj HCTX (conj HLP HP))))))).
change (SRr SEGS W (cfg_at SEGS TEXT_OF_A regs memc mdc) (to_post SK B MT cx)).
pose proof (to_pre_happ SK B MT CTX cx HPX) as HH. pose proof HH as (HAp & HAo).
pose proof HA as (HJ & HGok & HROD & Hraw & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev & Hside & Hajw & Hro).
pose proof (to_win SK B MT CTX cx HPX) as (Hceil & H47 & _ & _ & _). change (to_sp cx) with (spZ regs) in *.
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
assert (HK : TEXT_OF_AK = 16448) by reflexivity.
destruct HP as (c0 & c1 & inp & Hc0 & Hc1 & Hc0r & Hc1r & Hbufp & Hp8 & Hrap & _ & Hafp & Hbufo & Hrao & _ & _ & Hafo & Hapo
  & Haep & Hinp & Hlen & Hrai & Hpos & Hvis & Hword & HraT & HapT & HaoT & HentT & HTR).
set (p := aarg regs 0) in *. set (o := aarg regs 1) in *.
assert (Hp0 : 0 <= p < 2 ^ 64) by (unfold p, aarg, argZ; apply bv_unsigned_in_range).
assert (Ho0 : 0 <= o < 2 ^ 64) by (unfold o, aarg, argZ; apply bv_unsigned_in_range).
unfold amem_range in HAp, HAo. change (to_p cx) with p in HAp. change (to_o cx) with o in HAo.
(* the entry state *)
set (E := Eimg (Ereg regs (to_extra c0 c1 inp))).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EREG : forall r : nat, (r < 32)%nat -> ew E r = getr regs (Z_to_bv 5 (Z.of_nat r))).
{ intros r Hr. subst E. apply ew_Eimg_Ereg_nat.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 5) with 32.
  symmetry. apply Z.mod_small. lia. }
assert (EX : forall j, (j < 6)%nat -> ew E (32 + j) = nth j (to_extra c0 c1 inp) (Z_to_bv 64 0))
  by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ j)).
assert (E2 : ew E 2 = getr regs 2) by exact (EREG 2%nat ltac:(lia)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (U10 : bv_unsigned (ew E 10) = p) by (rewrite (EREG 10%nat ltac:(lia)); reflexivity).
assert (U11 : bv_unsigned (ew E 11) = o) by (rewrite (EREG 11%nat ltac:(lia)); reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by exact (EX 0%nat ltac:(lia)).
assert (E33 : ew E 33 = Z_to_bv 64 c0) by exact (EX 1%nat ltac:(lia)).
assert (E34 : ew E 34 = Z_to_bv 64 c1) by exact (EX 2%nat ltac:(lia)).
assert (E35 : ew E 35 = Z_to_bv 64 (bz inp 0)) by exact (EX 3%nat ltac:(lia)).
assert (E36 : ew E 36 = Z_to_bv 64 (bz inp 1)) by exact (EX 4%nat ltac:(lia)).
assert (E37 : ew E 37 = Z_to_bv 64 (bz inp 2)) by exact (EX 5%nat ltac:(lia)).
assert (U32 : bv_unsigned (ew E 32) = SHADOW_OFF) by (rewrite E32; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (HCFG : cfg_at SEGS TEXT_OF_A regs memc mdc
             = mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_text_of)) memc (seg_rom SEGS)) mdc).
{ unfold cfg_at, w64. rewrite (lv_text LV). reflexivity. }
rewrite HCFG. clear HCFG.
pose proof (aj_gx_present SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HJpres.
pose proof (aj_window_bounds SK SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (HwC & Hw47 & HSTK & HXO).
(* ---- the entry state ---- *)
assert (HS : st_ok_pi SEGS VAL E to_ss0
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_text_of)) memc (seg_rom SEGS)))).
{ destruct (aj_gx_const_cells SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ)
    as (_ & _ & Kcell & Kgot).
  rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
  destruct to_obj_vals as (V1 & V64 & _).
  assert (EO : forall i, (i < 66)%nat -> ew E (A_OBJ i) = Z_to_bv 64 (VAL (A_OBJ i)))
    by (intros i Hi; subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (VB : forall nn v, ew E nn = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some nn) = v).
  { intros nn v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
  pose proof (EO 1%nat ltac:(lia)) as EO1. pose proof (EO 64%nat ltac:(lia)) as EO64.
  rewrite V1 in EO1, Kgot. rewrite V64 in EO64, Kgot, Kcell.
  rewrite restrict_mkst_fx. unfold to_ss0. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold stack_region, got_regionP, bcell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + cbn [base_val]. rewrite Usp. split; [unfold TO_FRAME; lia|]. split; [lia|]. split; [|constructor].
      intros o' Ho'. apply (apresent_writable SEGS). apply HJpres. unfold TO_FRAME in Ho'. lia.
    + rewrite (VB (A_OBJ 1) 0xa19d0 EO1 ltac:(lia)).
      split; [lia|]. split; [lia|]. split; [intros o' Ho'; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ 0xa19d0 0 8 (SOff (A_OBJ 64) 0) 0xaa438);
        [cbn [sv_denot]; rewrite EO64, Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kgot).
    + rewrite (VB (A_OBJ 64) 0xaa438 EO64 ltac:(lia)).
      split; [lia|]. split; [lia|]. split; [intros o' Ho'; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ 0xaa438 0 8 (SOff 32 0) SHADOW_OFF);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r; reflexivity | cbn; unfold SHADOW_OFF; lia | cbn; lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kcell).
  - apply pairwise_disjoint_of_extents.
    unfold stack_region, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 1) 0xa19d0 EO1 ltac:(lia)), (VB (A_OBJ 64) 0xaa438 EO64 ltac:(lia)).
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj, TO_FRAME. cbn [fst snd].
    repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [to_fA0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, U32, U10, U11. change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
    unfold SHADOW_OFF in *.
    repeat match goal with |- _ /\ _ => split end; first [exact I | exact Hal16 | exact Hp8 | lia]. }
assert (SHOK : sh_ok SEGS TOBx to_SH0 E (rdW W memc)).
{ unfold to_SH0. repeat apply Forall_cons; try apply Forall_nil; unfold shent_ok, app_apart; cbn [she_m she_lo she_hi];
    unfold TOBx; rewrite !lf_U_reg, ?U32, ?U10, ?U11; cbn [Z.min Z.max]; rewrite ?Z.add_0_r, ?Z.sub_0_r.
  - split; [exact Hrap|]. intros a Ha. unfold SHADOW_OFF in *. lia.
  - split; [exact Hrao|]. intros a Ha. unfold SHADOW_OFF in *. lia. }
pose (RUNTO := paj_run_to_x SK B LAWS G HGok XO OUT).
(* ---- +0x00 .. +0x28: the frame and the shadow base ---- *)
paj_run_to_tok RUNTO HS HJ SHOK Bspan (AF_text_of + 0x2c).
{ unfold to_ss0. cbn [ss_mem].
  repeat (apply awr_ok_x_cons; [intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val stack_region got_regionP
      bcell_regionP] in Hx;
    first [lia | rewrite Usp in Hx; left; split; [left; unfold TO_FRAME in Hx; lia | lia]] |]).
  apply awr_ok_x_nil. }
(* the bytes outside the frame are the call's *)
pose proof (kept_of_frame (segs := SEGS) E _ (w_H W) memc (ms_mem ms) (fun a => spZ regs - 64 <= a < spZ regs) HFr
  ltac:(intros bbW wloW whiW aW HinW HrrW; vm_compute in HinW;
        repeat (destruct HinW as [HqW | HinW]; [injection HqW as <- <- <-; cbn [base_val] in HrrW;
                rewrite ?Usp in HrrW; cbv beta; lia|]); destruct HinW)) as UN1.
assert (KB1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 64 <= a < spZ regs) ->
          mbyte SEGS (rdW W (ms_mem ms)) a = mbyte SEGS (rdW W memc) a)
  by (intros a Ha Hn; exact (mbyte_of_aview_eq SEGS _ _ _ _ a a (UN1 a Ha Hn))).
assert (WR1 : forall a, writable_at SEGS (rdW W memc) a -> writable_at SEGS (rdW W (ms_mem ms)) a)
  by (intros a Ha; exact (wview_grows SEGS _ _ _ HG Ha)).
set (Zs0 := fun a : Z => spZ regs - 64 <= a < spZ regs \/ p <= a < p + 16 \/ o <= a < o + 8).
assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ Zs0 a -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) memc a)
  by (intros a Ha Hn; apply UN1; [exact Ha | intros Hw; apply Hn; left; exact Hw]).
rename HG into GR. clear HFr.
(* ---- phase 2's regions: the frame only, then the cursor and *own ---- *)
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
  let rs := eval vm_compute in (ss_mem ssx) in
  let rs' := eval vm_compute in (pick rs [0]%nat) in
  pose proof (st_ok_pi_submem Ex ssx msx rs' HS ltac:(cbn [ss_mem]; submem_to)
    ltac:(vm_compute; reflexivity)) as HS2; clear HS; rename HS2 into HS end.
cbn [ss_pc ss_regs ss_resv ss_facts] in HS.
assert (Hp16 : p + 16 <= spZ regs - TEXT_OF_AK \/ spZ regs <= p) by exact Hafp.
assert (Ho16 : o - 16 + 24 <= spZ regs - TEXT_OF_AK \/ spZ regs <= o - 16) by exact Hafo.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ to_rP HS eq_refl
  ltac:(unfold region_ok, to_rP; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val
          ms_mem restrict mkst];
        rewrite U10; split; [lia|]; split; [lia|]; split;
        [ intros o' Ho'; apply WR1; destruct Hbufp as (jk & Hjk & _ & Hwr); apply Hwr; lia
        | apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
          [ apply (chunk_ok_val SEGS _ _ p 0 8 (SOff 33 0) c0);
              [cbn [sv_denot]; rewrite E33, Z.add_0_r, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |];
            intros j Hj; rewrite KB1 by (cbn in Hj; lia); rewrite Z.add_0_r; exact (Hc0 j Hj)
          | apply (chunk_ok_val SEGS _ _ p 8 8 (SOff 34 0) c1);
              [cbn [sv_denot]; rewrite E34, Z.add_0_r, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |];
            intros j Hj; rewrite KB1 by (cbn in Hj; lia); exact (Hc1 j Hj) ] ])
  ltac:(to_disj; rewrite U10, Usp; split; [lia | exact I]))
  as HS3 end.
clear HS; rename HS3 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ to_rO HS eq_refl
  ltac:(unfold region_ok, to_rO; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val
          ms_mem restrict mkst];
        rewrite U11; split; [lia|]; split; [lia|]; split;
        [ intros o' Ho'; apply WR1; destruct Hbufo as (jk & Hjk & _ & Hwr); apply Hwr; lia | apply Forall_nil ])
  ltac:(to_disj; rewrite U10, U11, Usp; unfold apart in *; split; [lia | split; [lia | exact I]]))
  as HS3 end.
clear HS; rename HS3 into HS.
pose (RUN := paj_run_x SK B LAWS G HGok XO OUT).
pose proof (paj_branch (PI := PI)) as BR.
change (text_of_awr regs (rdW W memc)) with [(p, p + 16); (o, o + 8)] in Hajw.
destruct (Z.eq_dec c1 0) as [C0 | C0].
{ (* ==== c1 = 0: +0x4c taken, +0x12c .. +0x140, the TABLE cut ==== *)
  add_fact HS 34%nat (mkAF 0 0 0)
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E34, unsigned_lit_small by lia;
          rewrite Z.pow_0_r, Z.mod_1_r; lia).
  paj_run_tok RUN HS HJ SHOK Bspan; [to_awr Hajw Usp U10 U11 |].
  to_fold UN GR Zs0 Usp U10 U11.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  2: { exfalso. rewrite branch_eq_U, lf_U_reg, U_SLit in Hc. rewrite ?ew_ewset_other in Hc by lia.
       rewrite E34, unsigned_lit_small in Hc by lia. change (zcanon 0) with 0 in Hc. apply Z.eqb_neq in Hc. lia. }
  paj_run_to_tok RUNTO HS HJ SHOK Bspan TO_CUT_TABLE; [to_awr Hajw Usp U10 U11 |].
  to_fold UN GR Zs0 Usp U10 U11.
  prreg HS (11%bv : bv 5) Q11. to_region HS 10%nat HRp.
  lazymatch goal with |- SRr _ _ {| cfg_ms := ?msF; cfg_model := ?mdF |} _ =>
    apply (TAB cx msF mdF HPX); apply (to_gi_table_of cx msF mdF HPX) end.
  { pose proof (st_ok_pi_restrict_mkst _ _ _ _ HS eq_refl) as Hms. cbn [ss_pc] in Hms.
    destruct (ms_shape_mkst SEGS _ _ _ _ Hms) as (_ & _ & _ & _ & _ & Hpc). rewrite Hpc.
    unfold w64. apply (f_equal (Z_to_bv 64)). unfold TO_CUT_TABLE, AF_text_of. lia. }
  { to_core_leaf cx regs W o HPX HS HJ UN GR EREG Usp E32 EREG Usp U10 U11. }
  { exists 0. split; [refine (eq_trans Q11 _); reflexivity | lia]. }
  { intros c0' c1' H0 H1 R0 R1. exists 0.
    pose proof (mw_au64_det SEGS _ _ _ _ H0 Hc0 R0 Hc0r) as ->.
    pose proof (mw_au64_det SEGS _ _ _ _ H1 Hc1 R1 Hc1r) as ->.
    rewrite Z.add_0_r, Z.sub_0_r. split; [lia|]. split.
    - pose proof (to_word_of_region _ _ _ 10%nat p 0 _ HRp eq_refl U10
        ltac:(cbn [YP09.r_chunks]; repeat (first [left; reflexivity | right]))) as V. rewrite Z.add_0_r in V.
      rewrite (to_sv_off0 _ 33 c0 E33 Hc0r) in V. exact V.
    - pose proof (to_word_of_region _ _ _ 10%nat p 8 _ HRp eq_refl U10
        ltac:(cbn [YP09.r_chunks]; repeat (first [left; reflexivity | right]))) as V.
      rewrite (to_sv_off0 _ 34 c1 E34 Hc1r) in V. exact V. }
}
(* ==== c1 > 0: the input byte b0 at c0, its shadow check, the stores of the cursor and *own ==== *)
assert (C1 : 1 <= c1) by lia.
destruct (Hpos ltac:(lia)) as (Hhull & Ham & Hafi & Hapip & Hapio & Hio).
assert (U33 : bv_unsigned (ew E 33) = c0) by (rewrite E33; apply unsigned_lit_small; lia).
assert (HCB : 0 <= c0 /\ c0 + c1 <= 2 ^ 47 - 1)
  by (clear - Ham Hc0r; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham; lia).
assert (HSP : 0x7fff7f800000 <= spZ regs - 64) by (change TEXT_OF_AK with 16448 in Hceil; lia).
to_KSI UN KS KI W memc regs p o c0 c1 HSP HAp HAo Hafi Hapip Hapio.
add_fact HS 34%nat (mkAF 1 (2 ^ 64 - 1) 0)
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E34, unsigned_lit_small by lia;
        rewrite Z.pow_0_r, Z.mod_1_r; lia).
add_fact HS 33%nat (mkAF 0 (2 ^ 47 - 2) 0)
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U33; rewrite Z.pow_0_r, Z.mod_1_r; lia).
add_fact HS 35%nat (mkAF 0 255 0)
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; pose proof (bz_rng inp 0) as Hb;
        rewrite E35, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia).
assert (D0o : c0 + 0 + 1 <= o \/ o + 8 <= c0 + 0) by exact (to_apart_at c0 c1 o 8 0 Hapio ltac:(lia)).
assert (D0p : c0 + 0 + 1 <= p \/ p + 16 <= c0 + 0) by exact (to_apart_at c0 c1 p 16 0 Hapip ltac:(lia)).
assert (D0s : c0 + 0 + 1 <= spZ regs - TEXT_OF_AK \/ spZ regs - TEXT_OF_AK + TEXT_OF_AK <= c0 + 0)
  by (apply (to_apart_at c0 c1 (spZ regs - TEXT_OF_AK) TEXT_OF_AK 0); [unfold apart_frame in Hafi; lia | lia]).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (to_rIb 0 35) HS eq_refl
  ltac:(cbn [ms_mem restrict mkst]; exact (to_rIb_ok Ev _ _ c0 c1 inp 0 35 U33 E35 ltac:(lia) Hinp Hlen KI))
  ltac:(to_disj; rewrite U33, U10, U11, Usp; change TEXT_OF_AK with 16448 in D0s;
        repeat (split; [clear - D0o D0p D0s; lia|]); exact I))
  as HS3 end.
clear HS; rename HS3 into HS.
pose proof (to_sh_add E _ _ to_SH0 c0 c1 0 U33 U32 ltac:(lia) Hrai Ham KS SHOK) as SHOK1.
clear SHOK; rename SHOK1 into SHOK. cbn [Z.add] in SHOK.
paj_run_tok RUN HS HJ SHOK Bspan; [to_awr Hajw Usp U10 U11 |].
to_fold UN GR Zs0 Usp U10 U11.
to_envs HS E Usp U10 U11 E32 EREG AG1 Usp1 U101 U111 E321 EREG1.
pose proof (bz_rng inp 0) as Hb0.
pose proof E35 as E351. rewrite <- (AG1 35%nat ltac:(lia)) in E351.
destruct (to_sext8 _ (bz inp 0) E351 Hb0) as (Hge & _).
psrr_branch_tok RUN BR HS SHOK Bspan.
{ (* ==== b0 < 128: +0xa4 taken, the TABLE cut with the selector b0 ==== *)
  rewrite Hge in Hc. apply Z.ltb_lt in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan TO_CUT_TABLE; [to_awr Hajw Usp1 U101 U111 |].
  to_fold UN GR Zs0 Usp1 U101 U111.
  to_envs HS E Usp U10 U11 E32 EREG AG2 Usp2 U102 U112 E322 EREG2.
  to_reg_raw HS (11%bv : bv 5) Q11. to_region HS 10%nat HRp.
  lazymatch goal with |- SRr _ _ {| cfg_ms := ?msF; cfg_model := ?mdF |} _ =>
    apply (TAB cx msF mdF HPX); apply (to_gi_table_of cx msF mdF HPX) end.
  { pose proof (st_ok_pi_restrict_mkst _ _ _ _ HS eq_refl) as Hms. cbn [ss_pc] in Hms.
    destruct (ms_shape_mkst SEGS _ _ _ _ Hms) as (_ & _ & _ & _ & _ & Hpc). rewrite Hpc.
    unfold w64. apply (f_equal (Z_to_bv 64)). unfold TO_CUT_TABLE, AF_text_of. lia. }
  { to_core_leaf cx regs W o HPX HS HJ UN GR EREG Usp E32 EREG2 Usp2 U102 U112. }
  { exists (bz inp 0). split; [|lia]. refine (eq_trans Q11 _).
    pose proof E35 as E352. rewrite <- (AG2 35%nat ltac:(lia)) in E352.
    destruct (to_sext8 _ (bz inp 0) E352 Hb0) as (_ & Hv). rewrite (Hv Hc). reflexivity. }
  { intros c0' c1' H0 H1 R0 R1. exists 1.
    pose proof (mw_au64_det SEGS _ _ _ _ H0 Hc0 R0 Hc0r) as ->.
    pose proof (mw_au64_det SEGS _ _ _ _ H1 Hc1 R1 Hc1r) as ->.
    pose proof E33 as E332. rewrite <- (AG2 33%nat ltac:(lia)) in E332.
    pose proof E34 as E342. rewrite <- (AG2 34%nat ltac:(lia)) in E342.
    split; [lia|]. split.
    - pose proof (to_word_of_region _ _ _ 10%nat p 0 _ HRp eq_refl U102
        ltac:(cbn [YP09.r_chunks]; repeat (first [left; reflexivity | right]))) as V. rewrite Z.add_0_r in V.
      rewrite (to_sv_off _ 33 c0 1 E332 Hc0r ltac:(lia)) in V. exact V.
    - pose proof (to_word_of_region _ _ _ 10%nat p 8 _ HRp eq_refl U102
        ltac:(cbn [YP09.r_chunks]; repeat (first [left; reflexivity | right]))) as V.
      rewrite (to_sv_off _ 34 c1 (-1) E342 Hc1r ltac:(lia)) in V. replace (c1 - 1) with (c1 + -1) by lia. exact V. } }
(* ==== b0 >= 128: +0xa8 .. +0xb4, c1 - 1 = 0 or not ==== *)
rewrite Hge in Hc. apply Z.ltb_ge in Hc.
assert (PREI : to_inp cx c0 c1 inp) by exact (conj Hc0 (conj Hc1 (conj Hc0r (conj Hc1r (conj Hinp Hlen))))).
paj_run_tok RUN HS HJ SHOK Bspan; [to_awr Hajw Usp1 U101 U111 |].
to_fold UN GR Zs0 Usp1 U101 U111.
to_envs HS E Usp U10 U11 E32 EREG AG2 Usp2 U102 U112 E322 EREG2.
pose proof E34 as E342. rewrite <- (AG2 34%nat ltac:(lia)) in E342.
psrr_branch_tok RUN BR HS SHOK Bspan.
{ (* ==== c1 = 1: +0xb4 taken, +0x1a0 a6 := 0, a1 := 0, the U16 cut with adv = 1 ==== *)
  lazymatch goal with H : branch_taken _ _ _ = _ |- _ => rename H into HB end.
  rewrite (to_beqz_off _ 34 c1 (-1) E342 Hc1r ltac:(lia)) in HB. apply Z.eqb_eq in HB.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan TO_CUT_U16; [to_awr Hajw Usp2 U102 U112 |].
  to_fold UN GR Zs0 Usp2 U102 U112.
  to_envs HS E Usp U10 U11 E32 EREG AG3 Usp3 U103 U113 E323 EREG3.
  to_u16_leaf 1 (-1) AG3 Usp3 U103 U113 EREG3 HS HJ UN GR U16 cx HPX c0 c1 inp regs W p o EREG Usp E32 U10 U32 E33 E34 E36 E37 Hc0r Hc1r PREI Hc. }
(* ==== c1 >= 2: the input byte b1 at c0 + 1 ==== *)
lazymatch goal with H : branch_taken _ _ _ = _ |- _ => rename H into HB end.
rewrite (to_beqz_off _ 34 c1 (-1) E342 Hc1r ltac:(lia)) in HB. apply Z.eqb_neq in HB.
norm_pi HS.
to_KSI UN KS1 KI1 W memc regs p o c0 c1 HSP HAp HAo Hafi Hapip Hapio.
pose proof U33 as U332. rewrite <- (AG2 33%nat ltac:(lia)) in U332.
pose proof U32 as U322. rewrite <- (AG2 32%nat ltac:(lia)) in U322.
pose proof E36 as E362. rewrite <- (AG2 36%nat ltac:(lia)) in E362.
add_fact HS 36%nat (mkAF 0 255 0)
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; pose proof (bz_rng inp 1) as Hb;
        rewrite E362, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia).
assert (D1o : c0 + 1 + 1 <= o \/ o + 8 <= c0 + 1) by exact (to_apart_at c0 c1 o 8 1 Hapio ltac:(lia)).
assert (D1p : c0 + 1 + 1 <= p \/ p + 16 <= c0 + 1) by exact (to_apart_at c0 c1 p 16 1 Hapip ltac:(lia)).
assert (D1s : c0 + 1 + 1 <= spZ regs - TEXT_OF_AK \/ spZ regs - TEXT_OF_AK + TEXT_OF_AK <= c0 + 1)
  by (apply (to_apart_at c0 c1 (spZ regs - TEXT_OF_AK) TEXT_OF_AK 1); [unfold apart_frame in Hafi; lia | lia]).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (to_rIb 1 36) HS eq_refl
  ltac:(cbn [ms_mem restrict mkst]; exact (to_rIb_ok Ev _ _ c0 c1 inp 1 36 U332 E362 ltac:(lia) Hinp Hlen KI1))
  ltac:(to_disj; rewrite U332, U102, U112, Usp2; change TEXT_OF_AK with 16448 in D1s;
        repeat (split; [clear - D1o D1p D1s; lia|]); exact I))
  as HS3 end.
clear HS; rename HS3 into HS.
pose proof (to_sh_add _ _ _ _ c0 c1 1 U332 U322 ltac:(lia) Hrai Ham KS1 SHOK) as SHOK1.
clear SHOK; rename SHOK1 into SHOK. cbn [Z.add] in SHOK.
paj_run_tok RUN HS HJ SHOK Bspan; [to_awr Hajw Usp2 U102 U112 |].
to_fold UN GR Zs0 Usp2 U102 U112.
to_envs HS E Usp U10 U11 E32 EREG AG3 Usp3 U103 U113 E323 EREG3.
pose proof E34 as E343. rewrite <- (AG3 34%nat ltac:(lia)) in E343.
psrr_branch_tok RUN BR HS SHOK Bspan.
{ (* ==== c1 = 2: +0xf0 taken, +0x1a4 a1 := 0, the U16 cut with adv = 2 ==== *)
  lazymatch goal with H : branch_taken _ _ _ = _ |- _ => rename H into HB2 end.
  rewrite (to_beqz_off _ 34 c1 (-2) E343 Hc1r ltac:(lia)) in HB2. apply Z.eqb_eq in HB2.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan TO_CUT_U16; [to_awr Hajw Usp3 U103 U113 |].
  to_fold UN GR Zs0 Usp3 U103 U113.
  to_envs HS E Usp U10 U11 E32 EREG AG4 Usp4 U104 U114 E324 EREG4.
  to_u16_leaf 2 (-2) AG4 Usp4 U104 U114 EREG4 HS HJ UN GR U16 cx HPX c0 c1 inp regs W p o EREG Usp E32 U10 U32 E33 E34 E36 E37 Hc0r Hc1r PREI Hc. }
(* ==== c1 >= 3: the input byte b2 at c0 + 2, the U16 cut with adv = 3 ==== *)
lazymatch goal with H : branch_taken _ _ _ = _ |- _ => rename H into HB2 end.
rewrite (to_beqz_off _ 34 c1 (-2) E343 Hc1r ltac:(lia)) in HB2. apply Z.eqb_neq in HB2.
norm_pi HS.
to_KSI UN KS2 KI2 W memc regs p o c0 c1 HSP HAp HAo Hafi Hapip Hapio.
pose proof U33 as U333. rewrite <- (AG3 33%nat ltac:(lia)) in U333.
pose proof U32 as U323. rewrite <- (AG3 32%nat ltac:(lia)) in U323.
pose proof E37 as E373. rewrite <- (AG3 37%nat ltac:(lia)) in E373.
add_fact HS 37%nat (mkAF 0 255 0)
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; pose proof (bz_rng inp 2) as Hb;
        rewrite E373, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia).
(* c0 + 2's shadow cell inside the token span: c0 <= 2 ^ 47 - 4 now that c1 >= 3 *)
add_fact HS 33%nat (mkAF 0 (2 ^ 47 - 4) 0)
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U333; rewrite Z.pow_0_r, Z.mod_1_r; lia).
assert (D2o : c0 + 2 + 1 <= o \/ o + 8 <= c0 + 2) by exact (to_apart_at c0 c1 o 8 2 Hapio ltac:(lia)).
assert (D2p : c0 + 2 + 1 <= p \/ p + 16 <= c0 + 2) by exact (to_apart_at c0 c1 p 16 2 Hapip ltac:(lia)).
assert (D2s : c0 + 2 + 1 <= spZ regs - TEXT_OF_AK \/ spZ regs - TEXT_OF_AK + TEXT_OF_AK <= c0 + 2)
  by (apply (to_apart_at c0 c1 (spZ regs - TEXT_OF_AK) TEXT_OF_AK 2); [unfold apart_frame in Hafi; lia | lia]).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (to_rIb 2 37) HS eq_refl
  ltac:(cbn [ms_mem restrict mkst]; exact (to_rIb_ok Ev _ _ c0 c1 inp 2 37 U333 E373 ltac:(lia) Hinp Hlen KI2))
  ltac:(to_disj; rewrite U333, U103, U113, Usp3; change TEXT_OF_AK with 16448 in D2s;
        repeat (split; [clear - D2o D2p D2s; lia|]); exact I))
  as HS3 end.
clear HS; rename HS3 into HS.
pose proof (to_sh_add _ _ _ _ c0 c1 2 U333 U323 ltac:(lia) Hrai Ham KS2 SHOK) as SHOK1.
clear SHOK; rename SHOK1 into SHOK. cbn [Z.add] in SHOK.
paj_run_to_tok RUNTO HS HJ SHOK Bspan TO_CUT_U16; [to_awr Hajw Usp3 U103 U113 |].
to_fold UN GR Zs0 Usp3 U103 U113.
to_envs HS E Usp U10 U11 E32 EREG AG4 Usp4 U104 U114 E324 EREG4.
to_u16_leaf 3 (-3) AG4 Usp4 U104 U114 EREG4 HS HJ UN GR U16 cx HPX c0 c1 inp regs W p o EREG Usp E32 U10 U32 E33 E34 E36 E37 Hc0r Hc1r PREI Hc.
Qed.

About to_head.
Print Assumptions to_head.

End b.
End a.
