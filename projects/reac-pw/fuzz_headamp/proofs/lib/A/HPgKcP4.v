(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgScanHead.v at cdde2c4d95be for
   reac-pw/fuzz_rate's image A: role's pcs (C3 0x820c4, the memcpy return 0x820e4, the parse return 0x8210c, E
   0x8212c, MAL 0x823fc, T 0x82408) become rate's (0x828b8, 0x828dc, 0x8290c, E 0x82930, MAL 0x82c9c, A 0x82ca8);
   the registers are renamed as rate's code has them (pod s2 -> s6, &cell s6 -> s5 = &hz, flags & 1 s4 -> s3, the
   frame's shadow base s3 -> s4, the shadow offset s7 -> s2, len s8 -> s10, pp + 0x4d18 s10 -> s9); F is read from
   the cell R+0x78 (blocks A and C: a read-only region at R), the hz cell takes the 4-byte 0x5a5a5a5a, block B also
   stores pod into R+0x138 (a writable window of the region at R) and reloads the flags byte into s10; the memcpy call
   is lib/A/RtPgSteps.v rts_intrin_at (role's hd_memcpy dropped), the .rodata zone is [0x10000, 0x22000), the cut file
   is lib/A/RtPgSeg.v (rl_ -> rt_, e_ -> q_, the role cell -> rs_hz_at, the frame pattern at the exits rs_PZ), the
   entry-state and list lemmas come from lib/A/RtPgScanKit.v and the memory facts from lib/A/RtPgMem.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgScanHead.v, with its module paths and module names changed; 189 of its 245 lines of code are new or changed and 975 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgScanF.v (rk_skipn_cons, rk_pairs_skip,
   rk_pairs_run, rk_pairs_last) and proofs/reac-pw/fuzz_role/lib/A/RPgScanOuter.v and RPgScanInner.v
   (ro_post, ro_post_intro, ro_at_get, ro_at_sub, ro_at_keep, ro_chk_base, ro_denot0, ro_bge and the run tactics) at
   e39c26ea588; module paths fuzz_role -> fuzz_headamp, the rk_ / ro_ / si_ prefixes -> hb_, the cut lists and the
   cut base restated over headamp's lib/A/HPgSeg.v and HPgSegM.v (hs_at, hq_base3), the record facts restated over
   headamp's fold (Pod/Headamp.v ha_fold) instead of role's role_of_pairs. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/A/HPgM3bBase.v, with its module paths and module names changed; 1126 of its 1182 lines of code are new or changed and 189 lines of the source are left out. *)
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; every address below is measured on the
   unstripped twin b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, whose loaded sections are
   byte-equal to the pin's except .note.gnu.build-id): part 4 of the piece "the key and the channel" of the walk of LLVMFuzzerTestOneInput
   (lib/A/HPgKcCut.v hk_P4_stmt), DOT 0x832b0 -> VAL 0x83364 / RF 0x83460. Proves no function (kind: segment lemma).

   THE CODE (fuzz_headamp.c:86-138; at DOT s2 = the key + d, a0 = nd >= 1, a1 = d, a2 = 0 for '-', a3 = the byte
   after the digits, t1 = acc, t4 = big, t3 = BAD_KEY)
     0x832b0 beqz a0 (dead: nd >= 1); 0x832b4 bnez a2 / neg t1 (the sign); 0x832bc neg a1; 0x832c0 beq a1,a0
       (dead: -d <> nd); 0x832c8 bne a3,'.' -> RF (no '.': BAD_KEY)
     0x832cc sd t4,0x98(s1); sd t1,0xa0(s1) (big and ch in the real frame); s2 := s2 + a0 + 14 (the name)
     0x832e8 / 0x832fc / 0x83310 strcmp(s2, 0x21340 "phantom" / 0x21360 "pad" / 0x21380 "sens") at the wrapper
       0x41ba0 (lib/A/HPgKcStr.v); 0 -> a3, s2 := (0, 1) / (1, 1) / (2, 0x37); after "sens" t2, t6 reloaded and
       t3 := BAD_KEY, no name -> RF
     0x8334c t3 := OUT_OF_RANGE; a1 := ch, a0 := big (reloads); bnez a0 -> RF; bltu 47,a1 -> RF; else VAL.

   HOW. Five block lemmas over the token engine (lib/Reusable YCbn.v / YCbq.v, the pattern of role's
   lib/A/RPgScanInner.v), each stated for any float state with the post kp_post (the world and the journal's end
   state kept, the registers outside clob, the bytes outside a write set, the arm's values): kp_dot_blk
   (0x832b0 .. 0x832c8, no region), kp_call1_blk (the two saves through a writable region based at s1 = R, with the
   fact on R the engine's static check asks), kp_test_ph / kp_test_pad (after the first two strcmps; a read-only
   region gives t6 / t2 from R+0xd8 / R+0xe0), kp_test_sens (after the third), kp_tail_blk (0x8334c .. 0x83360, big
   and ch from R+0x98 / R+0xa0). Between them the three strcmps go through HPgKcStr.hks_strcmp_call at the cut's
   float state. kp_mid carries, relative to the DOT cut, the journal at the cut's end state, the I/O state, sp / gp /
   tp and the callee-saved registers of hk_L, and every byte outside the callees' stack [R - 2 ESTACK, R) and the
   saves [R+0x98, R+0xa8); hk_base3_kept rebuilds hq_base3 from it, kp_L3_kept the cut lists, kp_x_kept x's bytes.
   The model: kp_key_eq (read_channel's answer from the DOT cut and the name give expect_key), the strcmp answers
   give param_of_name of the name (Cursor.cstr of the key's tail after the '.').

   Section hypotheses: errno_low (as lib/A/HPgKcLib.v, whose hk_base3_kept and hk_cstr_now take it) and STRCMP (the
   strcmp wrapper's contract at 0x41ba0 at every float state, HPgKcStr.v's text at segs = rsegs). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Cursor Model Layout Accessors.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgImgA HPgCalls HPgSeg HPgSegM.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgKcCut HPgKcLib HPgKcStr HPgSteps.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require HPgMem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================== the code table ======================================== *)
Definition KP_CALL1 : Z := 0x832cc.   (* the '.' is found: the saves of big and ch, then the first strcmp *)
Definition KP_TAIL : Z := 0x8334c.    (* a name was found: t3 := 5, the reloads of ch and big, the range tests *)
Definition kp_tbl : ctable := build_table rsegs HK_DOT 45 TEmpty.
Lemma kp_tbl_ok : table_ok rsegs kp_tbl.
Proof. apply build_table_ok0. unfold HK_DOT. lia. Qed.
Definition KBx : sv := SOff 23 0.
Definition KBspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).

Ltac kp_io := let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio.
Ltac kp_run := lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
  aj_run_tok kp_tbl_ok HS HJ SHOK KBspan; [awr_ok_tac | ] end.
Ltac kp_run_to pc := lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
  aj_run_to_tok kp_tbl_ok HS HJ SHOK KBspan pc; [awr_ok_tac | ] end.
Ltac kp_branch Hc := lazymatch goal with HS : st_ok _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
  srr_branch_tok kp_tbl_ok HS SHOK KBspan end;
  lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end.
(* the memory after a run over read-only regions is the memory before it *)
Ltac kp_mem :=
lazymatch goal with HF : frame_of ?E0 ?rs0 ?m0 (ms_mem ?ms1) |- _ =>
  let H := fresh "HMn" in
  pose proof (frame_of_read_only E0 rs0 m0 (ms_mem ms1) eq_refl HF) as H;
  first [ match goal with HM0 : ms_mem ?ms0 = _ |- _ =>
            lazymatch ms0 with ms1 => fail | _ => rewrite HM0 in H; clear HM0 end end
        | idtac ];
  let HM := fresh "HM" in rename H into HM end;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Ltac kp_sv :=
lazymatch goal with |- sv_denot _ (sr_get (ss_regs ?ss) ?r) = _ =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e end.

Section blk. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.

Definition kp_kept (regs regs2 : bvmap 5 word) (clob : list (bv 5)) : Prop :=
  forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob -> getr regs2 r = getr regs r.

(* the state at a block's end pc: the world and the journal's end state as at its start, the I/O state, the
   registers outside clob, every byte outside Wr, and what Rg says of the new registers and memory *)
Definition kp_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate) (W : world rsegs)
(memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word) (pc : Z) (clob : list (bv 5))
(Wr : Z -> Prop) (Rg : bvmap 5 word -> (word -> option byte) -> Prop) : world rsegs -> config -> Prop :=
fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = cfg_at rsegs pc regs2 mem2 md2 /\
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\ same_io mdc md2 /\
kp_kept regs regs2 clob /\
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) memc a) /\
Rg regs2 mem2.

Lemma kp_post_intro : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pc clob Wr Rg E' ss' ms md',
st_ok rsegs E' ss' (restrict (w_H W) ms) -> ss_resv ss' = None -> ss_pc ss' = pc ->
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms) md' k -> same_io mdc md' ->
kp_kept regs (ms_regs ms) clob ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) memc a) ->
Rg (ms_regs ms) (ms_mem ms) ->
kp_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pc clob Wr Rg W (mkCfg ms md').
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pc clob Wr Rg E' ss' ms md' HS Hr Hpc HJ Hio Hk Hm HR.
split; [reflexivity|]. exists (ms_regs ms), (ms_mem ms), md'.
split; [|split; [exact HJ|]; split; [exact Hio|]; split; [exact Hk|]; split; [exact Hm | exact HR]].
rewrite (st_ok_restrict_mkst rsegs (w_H W) E' ss' ms HS Hr) at 1. rewrite Hpc. reflexivity.
Qed.

Lemma kp_sub_neg : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
sv_denot E (SAlu ALU_SUB (SLit 0) (SOff n 0)) = w64 (- v).
Proof.
intros E n v H Hv. rewrite denot_lit_U. unfold w64. rewrite U_SAlu, U_SLit, (U_atom E n v H Hv).
cbn [zalu_raw]. change (zcanon 0) with 0. unfold zcanon, M64. rewrite Z.sub_0_l. apply Z_to_bv_mod64.
Qed.

Lemma kp_denot0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

(* `neg a1,a1; beq a1,a0` at 0x832bc: -d is never nd (0 <= d, 1 <= nd, both small) *)
Lemma kp_neg_ne : forall d nd, 0 <= d <= 45 -> 1 <= nd <= 45 -> (0 - d) mod 2 ^ 64 <> nd.
Proof.
intros d nd Hd Hn H. destruct (Z.eq_dec d 0) as [->|Hd0].
- rewrite Z.mod_0_l in H by lia. lia.
- rewrite <- (Z.mod_add (0 - d) 1 (2 ^ 64)) in H by lia. rewrite Z.mod_small in H by lia. lia.
Qed.

(* a register's value at a leaf: the engine's sv of it *)
Ltac kp_reg := lazymatch goal with HS : st_ok _ ?E' ?ss' (restrict ?H ?ms) |- getr (ms_regs ?ms) _ = _ =>
  rewrite (st_ok_restrict_reg rsegs H E' ss' ms _ HS); kp_sv end.
(* the registers outside clob: their sv is still their own atom *)
Ltac kp_keep := lazymatch goal with HS : st_ok _ ?E' ?ss' (restrict ?H ?ms), HAE : env_agree 32 (Ereg ?rg ?ex) _
  |- kp_kept _ _ ?cl =>
  exact (regs_kept_of_st_ok rsegs E' ss' ms rg ex H cl HS HAE ltac:(vm_compute; reflexivity)) end.
(* a leaf of a block whose regions are read-only: kp_post from the run's last state *)
Ltac kp_leaf rgtac :=
  lazymatch goal with HS : st_ok _ ?E' ?ss' (restrict _ ?ms), HM : ms_mem ?ms = _,
    HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    eapply kp_post_intro;
    [ exact HS | vm_compute; reflexivity | vm_compute; reflexivity | exact HJ | kp_io | kp_keep
    | intros ? _ _; rewrite HM; reflexivity
    | rgtac ]
  end.
(* the dead `beq a1,a0` 0x832c0 and the '.' test 0x832c8, from the state after the sign *)
Ltac kp_dot_tail rgtac :=
  kp_run; kp_mem;
  lazymatch goal with E10 : ew ?E 10 = Z_to_bv 64 ?nd, E11 : ew ?E 11 = Z_to_bv 64 ?d,
    E13 : ew ?E 13 = Z_to_bv 64 ?c |- _ =>
  let Hb2 := fresh "Hb2" in
  kp_branch Hb2; rewrite branch_eq_U, U_SAlu, (U_lit E 0), (U_atom E 11 d E11), (U_atom E 10 nd E10) in Hb2 by lia;
  cbn [zalu_raw] in Hb2; unfold zcanon, M64 in Hb2;
  [ exfalso; apply Z.eqb_eq in Hb2; exact (kp_neg_ne d nd ltac:(lia) ltac:(lia) Hb2)
  | kp_run; kp_mem;
    let Hb3 := fresh "Hb3" in
    kp_branch Hb3; rewrite branch_ne_U, (U_atom E 13 c E13), (U_lit E 46) in Hb3 by lia;
    [ apply negb_true_iff, Z.eqb_neq in Hb3; kp_run; kp_mem; apply SRr_ret; cbv beta; left; split; [exact Hb3|];
      kp_leaf ltac:(exact I)
    | apply negb_false_iff, Z.eqb_eq in Hb3; kp_run_to KP_CALL1; kp_mem; apply SRr_ret; cbv beta; right;
      split; [exact Hb3|]; kp_leaf ltac:(kp_reg; rgtac) ] ]
  end.

(* ---------------- DOT 0x832b0 .. 0x832c8: the dead `beqz`, the sign, the dead `beq`, the '.' test ---------------- *)
Lemma kp_dot_blk : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (d nd acc c sg : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 10) = w64 nd -> getr regs (Z_to_bv 5 11) = w64 d -> getr regs (Z_to_bv 5 12) = w64 sg ->
getr regs (Z_to_bv 5 13) = w64 c -> getr regs (Z_to_bv 5 6) = w64 acc ->
1 <= nd <= 45 -> 0 <= d <= 45 -> (sg = 0 \/ sg = 1) -> 0 <= c < 256 -> 0 <= acc < 2 ^ 63 ->
SRr rsegs W (cfg_at rsegs HK_DOT regs memc mdc)
(fun W2 c2 =>
 (c <> 46 /\ kp_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HQ_RF [6; 11]%bv (fun _ => False)
   (fun _ _ => True) W2 c2) \/
 (c = 46 /\ kp_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs KP_CALL1 [6; 11]%bv (fun _ => False)
   (fun regs2 _ => getr regs2 (Z_to_bv 5 6) = w64 (if sg =? 0 then - acc else acc)) W2 c2)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs d nd acc c sg HJ H10 H11 H12 H13 H6
  Hnd Hd Hsg Hc Hacc.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs. pose proof (AR_laws_ok rsegs B) as LAWS.
assert (EA : forall (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (Ereg regs []) n = getr regs r)
  by (intros n r Hr; exact (ew_Ereg_nat regs _ n r Hr)).
assert (E10 : ew (Ereg regs []) 10 = Z_to_bv 64 nd) by (rewrite (EA 10%nat (Z_to_bv 5 10) eq_refl); exact H10).
assert (E11 : ew (Ereg regs []) 11 = Z_to_bv 64 d) by (rewrite (EA 11%nat (Z_to_bv 5 11) eq_refl); exact H11).
assert (E12 : ew (Ereg regs []) 12 = Z_to_bv 64 sg) by (rewrite (EA 12%nat (Z_to_bv 5 12) eq_refl); exact H12).
assert (E13 : ew (Ereg regs []) 13 = Z_to_bv 64 c) by (rewrite (EA 13%nat (Z_to_bv 5 13) eq_refl); exact H13).
assert (E6 : ew (Ereg regs []) 6 = Z_to_bv 64 acc) by (rewrite (EA 6%nat (Z_to_bv 5 6) eq_refl); exact H6).
assert (HS : st_ok rsegs (Ereg regs []) (mkSS HK_DOT sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 HK_DOT) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply entry_st_ok_full.
  - apply regs_ok_Ereg.
  - reflexivity.
  - constructor.
  - cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
assert (SHOK : sh_ok rsegs KBx [] (Ereg regs []) (mrestrict (w_H W) memc)) by constructor.
remember (Ereg regs []) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs []) E) by (subst E; apply env_agree_refl).
clear HE EA.
unfold cfg_at. change (w64 HK_DOT) with (Z_to_bv 64 HK_DOT).
(* 0x832b0 beqz a0 (nd >= 1: not taken) *)
kp_run. kp_mem.
kp_branch Hb0; rewrite branch_eq_U, (U_atom E 10 nd E10), (U_lit E 0) in Hb0 by lia.
{ exfalso. apply Z.eqb_eq in Hb0. lia. }
kp_run. kp_mem.
(* 0x832b4 bnez a2: the sign *)
kp_branch Hb1; rewrite branch_ne_U, (U_atom E 12 sg E12), (U_lit E 0) in Hb1 by lia.
- (* a2 = 1: no `neg` *)
  apply negb_true_iff, Z.eqb_neq in Hb1.
  assert (Hs1 : sg = 1) by lia. subst sg.
  kp_dot_tail ltac:(rewrite kp_denot0, E6; reflexivity).
- (* a2 = 0: t1 := -t1 *)
  apply negb_false_iff, Z.eqb_eq in Hb1. subst sg.
  kp_dot_tail ltac:(rewrite (kp_sub_neg E 6 acc E6) by lia; reflexivity).
Qed.

(* a 64-bit chunk of a region holds its value *)
Lemma kp_chunk_val : forall E m b (cs : list YP09.chunk) o e v,
Forall (YP09.chunk_ok rsegs E m b) cs -> In (YP09.mkChunk o (CVal 8 e)) cs ->
sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> val_mem rsegs m (b + o) 8 v.
Proof.
intros E m b cs o e v Hcs Hin He Hv.
exact (val_of_chunk_ok rsegs E m b o 8 e v (proj1 (Forall_forall _ _) Hcs _ Hin) He ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.

(* ---------------- 0x832cc .. 0x832e8: the saves of big and ch, the name, the first strcmp's arguments ---------------- *)
Definition kp_R1 : YP09.region := YP09.mkRegion (Some 9%nat) 0x98 0xa8 0x98 0xa8 [].
Definition kp_wr1 (R : Z) : Z -> Prop := fun a => R + 0x98 <= a < R + 0xa8.
(* the real frame's base R (s1, atom 9) lies above the allocator's ceiling plus the callees' stack, far from the
   shadow band: what the token engine's static check asks of a writable region based at s1 *)
Definition kp_G9 : facts := mkFacts [(9%nat, mkAF 0x7fff7f804000 (2 ^ 47) 0)] [] [].
Lemma kp_call1_blk : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (R keyd nd tb chw : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 9) = w64 R -> getr regs (Z_to_bv 5 18) = w64 keyd -> getr regs (Z_to_bv 5 10) = w64 nd ->
getr regs (Z_to_bv 5 29) = w64 tb -> getr regs (Z_to_bv 5 6) = w64 chw ->
0x7fff7f804000 <= R -> sp0 - STK <= R + 0x98 -> R + 0xa8 <= sp0 -> R <= 2 ^ 47 ->
0 <= keyd -> 0 <= nd -> keyd + nd + 14 < 2 ^ 64 -> 0 <= tb < 2 ^ 64 -> 0 <= chw < 2 ^ 64 ->
SRr rsegs W (cfg_at rsegs KP_CALL1 regs memc mdc)
(kp_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A_STRCMP [1; 10; 11; 18]%bv (kp_wr1 R)
  (fun regs2 mem2 => getr regs2 (Z_to_bv 5 1) = w64 RA_STRCMP1 /\
    getr regs2 (Z_to_bv 5 10) = w64 (keyd + nd + 14) /\ getr regs2 (Z_to_bv 5 18) = w64 (keyd + nd + 14) /\
    getr regs2 (Z_to_bv 5 11) = w64 A_HPH /\
    val_mem rsegs (mrestrict (w_H W) mem2) (R + 0x98) 8 tb /\
    val_mem rsegs (mrestrict (w_H W) mem2) (R + 0xa0) 8 chw)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R keyd nd tb chw HJ H9 H18 H10 H29 H6
  HR0 Hlo Hhi H47 Hk0 Hn0 Hkn Htb Hch.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs. pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
assert (EA : forall (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (Ereg regs []) n = getr regs r)
  by (intros n r Hr; exact (ew_Ereg_nat regs _ n r Hr)).
assert (E9 : ew (Ereg regs []) 9 = Z_to_bv 64 R) by (rewrite (EA 9%nat (Z_to_bv 5 9) eq_refl); exact H9).
assert (E18 : ew (Ereg regs []) 18 = Z_to_bv 64 keyd) by (rewrite (EA 18%nat (Z_to_bv 5 18) eq_refl); exact H18).
assert (E10 : ew (Ereg regs []) 10 = Z_to_bv 64 nd) by (rewrite (EA 10%nat (Z_to_bv 5 10) eq_refl); exact H10).
assert (E29 : ew (Ereg regs []) 29 = Z_to_bv 64 tb) by (rewrite (EA 29%nat (Z_to_bv 5 29) eq_refl); exact H29).
assert (E6 : ew (Ereg regs []) 6 = Z_to_bv 64 chw) by (rewrite (EA 6%nat (Z_to_bv 5 6) eq_refl); exact H6).
assert (U9 : bv_unsigned (ew (Ereg regs []) 9) = R) by (rewrite E9; apply unsigned_lit_small; lia).
assert (HS : st_ok rsegs (Ereg regs []) (mkSS KP_CALL1 sr_atoms [kp_R1] None kp_G9)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 KP_CALL1) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply entry_st_ok_full.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold kp_R1.
    apply (HPgMem.hm_rw_region rsegs _ (w_H W) memc 9 R); [exact U9 | lia | lia | | constructor].
    intros o Ho. apply Hpres. lia.
  - cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [kp_G9 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U9. change (2 ^ 0) with 1. rewrite Z.mod_1_r. repeat split; lia. }
assert (SHOK : sh_ok rsegs KBx [] (Ereg regs []) (mrestrict (w_H W) memc)) by constructor.
remember (Ereg regs []) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs []) E) by (subst E; apply env_agree_refl).
clear HE EA.
unfold cfg_at. change (w64 KP_CALL1) with (Z_to_bv 64 KP_CALL1).
aj_run_tok kp_tbl_ok HS HJ SHOK KBspan.
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp ?fp ?b0 ?bc ?ly0 ?own0 =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp fp b0 bc ly0 own0) end.
  apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (R - sp0)); [reflexivity | rewrite U9; ring | cbn; lia
  | cbn; lia | apply awr_ok_nil]. }
lazymatch goal with HS : st_ok _ ?E' ?ss' (restrict _ ?ms), HFr : frame_of _ _ (mrestrict _ memc) _ |- _ =>
  pose proof (st_ok_region_at _ _ _ 0%nat _ HS ltac:(vm_compute; reflexivity)) as HRg;
  destruct HRg as (_ & _ & _ & Hch0);
  cbn [YP09.r_base YP09.r_chunks base_val] in Hch0; rewrite U9 in Hch0;
  apply SRr_ret; eapply kp_post_intro;
  [ exact HS | vm_compute; reflexivity | vm_compute; reflexivity | eassumption | kp_io | kp_keep
  | intros a Ha Hw; unfold aview, mbyte; rewrite (HFr (Z_to_bv 64 a)); [reflexivity|];
    intros (rg & Hin & Hr); cbn [In] in Hin; destruct Hin as [<-|[]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val kp_R1] in Hr; rewrite U9 in Hr;
    rewrite unsigned_lit_small in Hr by lia; apply Hw; unfold kp_wr1; lia
  | ]
end.
split; [kp_reg; reflexivity|].
split; [kp_reg; rewrite denot_lit_U; unfold w64; f_equal; rewrite U_SAlu, (U_atom_off E 10 nd 14 E10), (U_atom E 18 keyd E18) by lia;
  cbn [zalu_raw]; unfold zcanon, M64; rewrite Z.mod_small by lia; lia|].
split; [kp_reg; rewrite denot_lit_U; unfold w64; f_equal; rewrite U_SAlu, (U_atom_off E 10 nd 14 E10), (U_atom E 18 keyd E18) by lia;
  cbn [zalu_raw]; unfold zcanon, M64; rewrite Z.mod_small by lia; lia|].
split; [kp_reg; reflexivity|].
split.
- replace (R + 0x98) with (R + 152) by reflexivity.
  apply (kp_chunk_val _ _ R _ 152 (SOff 29 0) tb Hch0); [cbn; tauto | rewrite kp_denot0; exact E29 | exact Htb].
- replace (R + 0xa0) with (R + 160) by reflexivity.
  apply (kp_chunk_val _ _ R _ 160 (SOff 6 0) chw Hch0); [cbn; tauto | rewrite kp_denot0; exact E6 | exact Hch].
Qed.

(* ---------------- after a strcmp: the reloads of t2 / t6 and the range tail read the real frame ---------------- *)
(* R+0xd8 = t6's value (atom 32), R+0xe0 = t2's (atom 33) *)
Definition kp_Rd : YP09.region := YP09.mkRegion (Some 9%nat) 0xd8 0xe8 0 0
  [YP09.mkChunk 0xd8 (CVal 8 (SOff 32 0)); YP09.mkChunk 0xe0 (CVal 8 (SOff 33 0))].
Definition kp_ss_d (pc : Z) : sstate := mkSS pc sr_atoms [kp_Rd] None (mkFacts [] [] []).

Lemma kp_entry_d : forall (W : world rsegs) (regs : bvmap 5 word) memc pc (R t6v t2v : Z),
getr regs (Z_to_bv 5 9) = w64 R -> 0 <= R -> R + 0xe8 <= 2 ^ 64 ->
0 <= t6v < 2 ^ 64 -> 0 <= t2v < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xd8) 8 t6v -> val_mem rsegs (mrestrict (w_H W) memc) (R + 0xe0) 8 t2v ->
st_ok rsegs (Ereg regs [w64 t6v; w64 t2v]) (kp_ss_d pc) (restrict (w_H W) (mkst regs (Z_to_bv 64 pc) memc (seg_rom rsegs))).
Proof.
intros W regs memc pc R t6v t2v H9 HR0 HR1 Ht6 Ht2 V6 V2.
assert (U9 : bv_unsigned (ew (Ereg regs [w64 t6v; w64 t2v]) 9) = R).
{ rewrite (ew_Ereg_nat regs _ 9 (Z_to_bv 5 9) eq_refl), H9. apply unsigned_lit_small. lia. }
rewrite restrict_mkst_fx. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor]. unfold kp_Rd.
  apply (HPgMem.hm_ro_region rsegs _ (w_H W) memc 9 R); [exact U9 | lia | lia |].
  constructor; [|constructor; [|constructor]].
  + apply (chunk_ok_val rsegs _ _ R 0xd8 8 (SOff 32 0) t6v); [| cbn; lia | cbn; lia | exact V6].
    rewrite kp_denot0. change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. reflexivity.
  + apply (chunk_ok_val rsegs _ _ R 0xe0 8 (SOff 33 0) t2v); [| cbn; lia | cbn; lia | exact V2].
    rewrite kp_denot0. change 33%nat with (32 + 1)%nat. rewrite ew_Ereg_extra. reflexivity.
- cbn. tauto.
- split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I.
Qed.

(* the strcmp against "phantom" (0x832ec) or "pad" (0x83300) has returned v: v = 0 sets a3 = p, s2 = smax, reloads
   t2 and t6 and goes to the tail; else the next strcmp's arguments (a0 = the name, a1 = lit, ra) *)
Definition kp_test_stmt (pc0 ra lit p smax : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (R v t6v t2v : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 9) = w64 R -> getr regs (Z_to_bv 5 10) = w64 v ->
0 <= R -> R + 0xe8 <= 2 ^ 64 -> 0 <= v < 2 ^ 64 -> 0 <= t6v < 2 ^ 64 -> 0 <= t2v < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xd8) 8 t6v -> val_mem rsegs (mrestrict (w_H W) memc) (R + 0xe0) 8 t2v ->
SRr rsegs W (cfg_at rsegs pc0 regs memc mdc)
(fun W2 c2 =>
 (v = 0 /\ kp_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs KP_TAIL [7; 13; 18; 31]%bv (fun _ => False)
   (fun regs2 _ => getr regs2 (Z_to_bv 5 13) = w64 p /\ getr regs2 (Z_to_bv 5 18) = w64 smax /\
      getr regs2 (Z_to_bv 5 7) = w64 t2v /\ getr regs2 (Z_to_bv 5 31) = w64 t6v) W2 c2) \/
 (v <> 0 /\ kp_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A_STRCMP [1; 10; 11]%bv (fun _ => False)
   (fun regs2 _ => getr regs2 (Z_to_bv 5 1) = w64 ra /\ getr regs2 (Z_to_bv 5 10) = getr regs (Z_to_bv 5 18) /\
      getr regs2 (Z_to_bv 5 11) = w64 lit) W2 c2)).

Ltac kp_test_proof pc0 :=
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R v t6v t2v HJ H9 H10 HR0 HR1 Hv Ht6 Ht2 V6 V2;
pose proof img_wx as Hwx; pose proof img_segs_low as Hsegs; pose proof (AR_laws_ok rsegs B) as LAWS;
pose proof (kp_entry_d W regs memc pc0 R t6v t2v H9 HR0 HR1 Ht6 Ht2 V6 V2) as HS;
assert (E10 : ew (Ereg regs [w64 t6v; w64 t2v]) 10 = Z_to_bv 64 v)
  by (rewrite (ew_Ereg_nat regs _ 10 (Z_to_bv 5 10) eq_refl); exact H10);
assert (E18 : ew (Ereg regs [w64 t6v; w64 t2v]) 18 = getr regs (Z_to_bv 5 18))
  by exact (ew_Ereg_nat regs _ 18 (Z_to_bv 5 18) eq_refl);
assert (E32 : ew (Ereg regs [w64 t6v; w64 t2v]) 32 = w64 t6v) by exact (ew_Ereg_extra regs _ 0);
assert (E33 : ew (Ereg regs [w64 t6v; w64 t2v]) 33 = w64 t2v) by exact (ew_Ereg_extra regs _ 1);
assert (SHOK : sh_ok rsegs KBx [] (Ereg regs [w64 t6v; w64 t2v]) (mrestrict (w_H W) memc)) by constructor;
remember (Ereg regs [w64 t6v; w64 t2v]) as E eqn:HE;
assert (HAE : env_agree 32 (Ereg regs [w64 t6v; w64 t2v]) E) by (subst E; apply env_agree_refl);
clear HE;
unfold cfg_at; change (w64 pc0) with (Z_to_bv 64 pc0);
kp_run; kp_mem;
let Hb := fresh "Hb" in
kp_branch Hb; rewrite branch_eq_U, (U_atom E 10 v E10), (U_lit E 0) in Hb by lia;
[ apply Z.eqb_eq in Hb; kp_run_to KP_TAIL; kp_mem; apply SRr_ret; cbv beta; left; split; [exact Hb|];
  kp_leaf ltac:(split; [kp_reg; reflexivity|]; split; [kp_reg; reflexivity|];
    split; kp_reg; rewrite kp_denot0; assumption)
| apply Z.eqb_neq in Hb; kp_run; kp_mem; apply SRr_ret; cbv beta; right; split; [exact Hb|];
  kp_leaf ltac:(split; [kp_reg; reflexivity|]; split; [kp_reg; rewrite kp_denot0; exact E18 | kp_reg; reflexivity]) ].

Lemma kp_test_ph : kp_test_stmt RA_STRCMP1 RA_STRCMP2 A_HPAD HA_PHANTOM 1.
Proof. unfold kp_test_stmt. kp_test_proof RA_STRCMP1. Qed.
Lemma kp_test_pad : kp_test_stmt RA_STRCMP2 RA_STRCMP3 A_HSENS HA_PAD 1.
Proof. unfold kp_test_stmt. kp_test_proof RA_STRCMP2. Qed.

(* the strcmp against "sens" (0x83314) has returned v: t2 and t6 reloaded, t3 := BAD_KEY; v <> 0 goes to RF, v = 0
   sets a3 = SENS, s2 = SENS_MAX and goes to the tail *)
Lemma kp_test_sens : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (R v t6v t2v : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 9) = w64 R -> getr regs (Z_to_bv 5 10) = w64 v ->
0 <= R -> R + 0xe8 <= 2 ^ 64 -> 0 <= v < 2 ^ 64 -> 0 <= t6v < 2 ^ 64 -> 0 <= t2v < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xd8) 8 t6v -> val_mem rsegs (mrestrict (w_H W) memc) (R + 0xe0) 8 t2v ->
SRr rsegs W (cfg_at rsegs RA_STRCMP3 regs memc mdc)
(fun W2 c2 =>
 (v <> 0 /\ kp_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HQ_RF [7; 28; 31]%bv (fun _ => False)
   (fun regs2 _ => getr regs2 (Z_to_bv 5 28) = w64 REFUSE_BAD_KEY /\
      getr regs2 (Z_to_bv 5 7) = w64 t2v /\ getr regs2 (Z_to_bv 5 31) = w64 t6v) W2 c2) \/
 (v = 0 /\ kp_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs KP_TAIL [7; 13; 18; 28; 31]%bv
   (fun _ => False)
   (fun regs2 _ => getr regs2 (Z_to_bv 5 13) = w64 HA_SENS /\ getr regs2 (Z_to_bv 5 18) = w64 HA_SENS_MAX /\
      getr regs2 (Z_to_bv 5 7) = w64 t2v /\ getr regs2 (Z_to_bv 5 31) = w64 t6v) W2 c2)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R v t6v t2v HJ H9 H10 HR0 HR1 Hv Ht6 Ht2 V6 V2.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs. pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof (kp_entry_d W regs memc RA_STRCMP3 R t6v t2v H9 HR0 HR1 Ht6 Ht2 V6 V2) as HS.
assert (E10 : ew (Ereg regs [w64 t6v; w64 t2v]) 10 = Z_to_bv 64 v)
  by (rewrite (ew_Ereg_nat regs _ 10 (Z_to_bv 5 10) eq_refl); exact H10).
assert (E32 : ew (Ereg regs [w64 t6v; w64 t2v]) 32 = w64 t6v) by exact (ew_Ereg_extra regs _ 0).
assert (E33 : ew (Ereg regs [w64 t6v; w64 t2v]) 33 = w64 t2v) by exact (ew_Ereg_extra regs _ 1).
assert (SHOK : sh_ok rsegs KBx [] (Ereg regs [w64 t6v; w64 t2v]) (mrestrict (w_H W) memc)) by constructor.
remember (Ereg regs [w64 t6v; w64 t2v]) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs [w64 t6v; w64 t2v]) E) by (subst E; apply env_agree_refl).
clear HE.
unfold cfg_at. change (w64 RA_STRCMP3) with (Z_to_bv 64 RA_STRCMP3).
kp_run. kp_mem.
kp_branch Hb; rewrite branch_ne_U, (U_atom E 10 v E10), (U_lit E 0) in Hb by lia.
- apply negb_true_iff, Z.eqb_neq in Hb. kp_run. kp_mem. apply SRr_ret; cbv beta; left; split; [exact Hb|].
  kp_leaf ltac:(split; [kp_reg; reflexivity|]; split; kp_reg; rewrite kp_denot0; assumption).
- apply negb_false_iff, Z.eqb_eq in Hb. kp_run_to KP_TAIL. kp_mem. apply SRr_ret; cbv beta; right; split; [exact Hb|].
  kp_leaf ltac:(split; [kp_reg; reflexivity|]; split; [kp_reg; reflexivity|];
    split; kp_reg; rewrite kp_denot0; assumption).
Qed.

(* ---------------- the tail 0x8334c .. 0x83360: t3 := OUT_OF_RANGE, big and ch reloaded and tested ---------------- *)
Definition kp_Rt : YP09.region := YP09.mkRegion (Some 9%nat) 0x98 0xa8 0 0
  [YP09.mkChunk 0x98 (CVal 8 (SOff 32 0)); YP09.mkChunk 0xa0 (CVal 8 (SOff 33 0))].
Lemma kp_tail_blk : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (R tb chw : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 9) = w64 R -> 0 <= R -> R + 0xa8 <= 2 ^ 64 -> 0 <= tb < 2 ^ 64 -> 0 <= chw < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x98) 8 tb -> val_mem rsegs (mrestrict (w_H W) memc) (R + 0xa0) 8 chw ->
SRr rsegs W (cfg_at rsegs KP_TAIL regs memc mdc)
(fun W2 c2 =>
 ((tb <> 0 \/ 47 < chw) /\ kp_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HQ_RF [10; 11; 28]%bv
   (fun _ => False) (fun regs2 _ => getr regs2 (Z_to_bv 5 28) = w64 REFUSE_OUT_OF_RANGE) W2 c2) \/
 (tb = 0 /\ chw <= 47 /\ kp_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HQ_VAL [10; 11; 28]%bv
   (fun _ => False) (fun regs2 _ => getr regs2 (Z_to_bv 5 28) = w64 REFUSE_OUT_OF_RANGE) W2 c2)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R tb chw HJ H9 HR0 HR1 Htb Hch Vb Vc.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs. pose proof (AR_laws_ok rsegs B) as LAWS.
assert (U9 : bv_unsigned (ew (Ereg regs [w64 tb; w64 chw]) 9) = R).
{ rewrite (ew_Ereg_nat regs _ 9 (Z_to_bv 5 9) eq_refl), H9. apply unsigned_lit_small. lia. }
assert (E32 : ew (Ereg regs [w64 tb; w64 chw]) 32 = Z_to_bv 64 tb) by exact (ew_Ereg_extra regs _ 0).
assert (E33 : ew (Ereg regs [w64 tb; w64 chw]) 33 = Z_to_bv 64 chw) by exact (ew_Ereg_extra regs _ 1).
assert (HS : st_ok rsegs (Ereg regs [w64 tb; w64 chw]) (mkSS KP_TAIL sr_atoms [kp_Rt] None (mkFacts [] [] []))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 KP_TAIL) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply entry_st_ok_full.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold kp_Rt.
    apply (HPgMem.hm_ro_region rsegs _ (w_H W) memc 9 R); [exact U9 | lia | lia |].
    constructor; [|constructor; [|constructor]].
    + apply (chunk_ok_val rsegs _ _ R 0x98 8 (SOff 32 0) tb); [rewrite kp_denot0; exact E32 | cbn; lia | cbn; lia | exact Vb].
    + apply (chunk_ok_val rsegs _ _ R 0xa0 8 (SOff 33 0) chw); [rewrite kp_denot0; exact E33 | cbn; lia | cbn; lia | exact Vc].
  - cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
assert (SHOK : sh_ok rsegs KBx [] (Ereg regs [w64 tb; w64 chw]) (mrestrict (w_H W) memc)) by constructor.
remember (Ereg regs [w64 tb; w64 chw]) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs [w64 tb; w64 chw]) E) by (subst E; apply env_agree_refl).
clear HE.
unfold cfg_at. change (w64 KP_TAIL) with (Z_to_bv 64 KP_TAIL).
kp_run. kp_mem.
kp_branch Hb; rewrite branch_ne_U, (U_atom E 32 tb E32), (U_lit E 0) in Hb by lia.
- apply negb_true_iff, Z.eqb_neq in Hb. kp_run. kp_mem. apply SRr_ret; cbv beta; left; split; [left; exact Hb|].
  kp_leaf ltac:(kp_reg; reflexivity).
- apply negb_false_iff, Z.eqb_eq in Hb. kp_run. kp_mem.
  kp_branch Hc; rewrite branch_ltu_U, (U_atom E 33 chw E33), (U_lit E 47) in Hc by lia.
  + apply Z.ltb_lt in Hc. kp_run. kp_mem. apply SRr_ret; cbv beta; left; split; [right; exact Hc|].
    kp_leaf ltac:(kp_reg; reflexivity).
  + apply Z.ltb_ge in Hc. kp_run. kp_mem. apply SRr_ret; cbv beta; right; split; [exact Hb|]; split; [exact Hc|].
    kp_leaf ltac:(kp_reg; reflexivity).
Qed.

End blk.

(* ======================================== the model ======================================== *)
Lemma kp_cstr_id : forall l, ~ In Cursor.NUL l -> Cursor.cstr l = l.
Proof.
induction l as [|x l IH]; intros H; [reflexivity|].
unfold Cursor.cstr in *. cbn [Cursor.nul_idx].
destruct (Z.eqb_spec (bv_unsigned x) 0) as [E|E].
- exfalso. apply H. left. apply bv_eq. rewrite E. reflexivity.
- cbn [firstn]. f_equal. apply IH. intros Hin. apply H. right. exact Hin.
Qed.

Lemma kp_expect_key_eq : forall rest u ch big, read_channel rest = (u, ch, big) ->
expect_key rest =
  if (u =? 0)%nat || negb (bv_unsigned (nth u rest Cursor.NUL) =? 46) then KBad
  else match param_of_name (Cursor.cstr (skipn (S u) rest)) with
       | None => KBad
       | Some p => if big || (ch <? 0) || (HA_CHANNELS <=? ch) then KRange else KCell ch p
       end.
Proof. intros rest u ch big H. unfold expect_key. rewrite H. reflexivity. Qed.

Lemma kp_cell_bad : forall k v, expect_key (skipn (length HA_PREFIX) k) = KBad -> expect_cell k v = inl REFUSE_BAD_KEY.
Proof. intros k v H. unfold expect_cell. rewrite H. reflexivity. Qed.
Lemma kp_cell_range : forall k v, expect_key (skipn (length HA_PREFIX) k) = KRange ->
expect_cell k v = inl REFUSE_OUT_OF_RANGE.
Proof. intros k v H. unfold expect_cell. rewrite H. reflexivity. Qed.

Lemma kp_param_none : forall nb, nb <> NAME_PHANTOM -> nb <> NAME_PAD -> nb <> NAME_SENS -> param_of_name nb = None.
Proof.
intros nb H1 H2 H3. unfold param_of_name.
destruct (Cursor.bytes_eqb nb NAME_PHANTOM) eqn:E1; [apply Cursor.bytes_eqb_eq in E1; contradiction|].
destruct (Cursor.bytes_eqb nb NAME_PAD) eqn:E2; [apply Cursor.bytes_eqb_eq in E2; contradiction|].
destruct (Cursor.bytes_eqb nb NAME_SENS) eqn:E3; [apply Cursor.bytes_eqb_eq in E3; contradiction|].
reflexivity.
Qed.
Lemma kp_param_ph : param_of_name NAME_PHANTOM = Some HA_PHANTOM.
Proof. vm_compute. reflexivity. Qed.
Lemma kp_param_pad : param_of_name NAME_PAD = Some HA_PAD.
Proof. vm_compute. reflexivity. Qed.
Lemma kp_param_sens : param_of_name NAME_SENS = Some HA_SENS.
Proof. vm_compute. reflexivity. Qed.

(* the bytes read_channel's answer takes lie inside the string *)
Lemma kp_sign_le : forall t, (snd (rc_sign t) <= length t)%nat.
Proof. intros [|b t]; cbn; [lia|]. destruct (_ || _); cbn; lia. Qed.
Lemma kp_digits_le : forall s acc big, (snd (rc_digits acc big s) <= length s)%nat.
Proof.
induction s as [|b s IH]; intros acc big; cbn; [lia|].
destruct (rc_digit b); cbn; [|lia].
destruct (1000000 <? acc); cbn; [specialize (IH acc true) | specialize (IH (acc * 10 + (bv_unsigned b - 48)) big)]; lia.
Qed.
Lemma kp_d_le : forall rest, (hk_d rest <= length rest)%nat.
Proof.
intros rest. unfold hk_d. pose proof (hk_rc_blanks_le rest) as H1.
pose proof (kp_sign_le (skipn (rc_blanks rest) rest)) as H2. rewrite length_skipn in H2. lia.
Qed.
Lemma kp_used_le : forall rest nd ch big, (1 <= nd)%nat ->
read_channel rest = ((hk_d rest + nd)%nat, ch, big) -> (hk_d rest + nd <= length rest)%nat.
Proof.
intros rest nd ch big Hnd H. unfold read_channel in H. cbv zeta in H.
change (rc_blanks rest + snd (rc_sign (skipn (rc_blanks rest) rest)))%nat with (hk_d rest) in H.
pose proof (kp_digits_le (skipn (hk_d rest) rest) 0 false) as Hd. rewrite length_skipn in Hd.
pose proof (kp_d_le rest) as Hle.
destruct (Nat.eqb_spec (snd (rc_digits 0 false (skipn (hk_d rest) rest))) 0) as [E|E].
- injection H as H _ _. lia.
- injection H as H _ _. lia.
Qed.

(* the name after the '.' is a suffix of the key *)
Lemma kp_garr8_suffix : forall (m : word -> option byte) a (k : list byte) j,
garr8 rsegs m a (hd_zbytes k ++ [0]) -> (j <= length k)%nat ->
garr8 rsegs m (a + Z.of_nat j) (hd_zbytes (skipn j k) ++ [0]).
Proof.
intros m a k j H Hj. rewrite <- (firstn_skipn j k) in H. unfold hd_zbytes in *.
rewrite map_app, <- app_assoc in H. apply garr8_app in H as [_ H].
rewrite length_map, length_firstn in H. replace (Nat.min j (length k)) with j in H by lia. exact H.
Qed.
Lemma kp_notin_skipn : forall (x : byte) l j, ~ In x l -> ~ In x (skipn j l).
Proof. intros x l j H Hin. apply H. rewrite <- (firstn_skipn j l). apply in_or_app. right. exact Hin. Qed.

(* the 64-bit word of a channel ch with |ch| <= 10000009: unsigned <= 47 exactly when 0 <= ch <= 47 *)
Lemma kp_chw : forall ch, -10000009 <= ch <= 10000009 -> (ch mod 2 ^ 64 <= 47 <-> 0 <= ch <= 47).
Proof.
intros ch H. destruct (Z_lt_le_dec ch 0) as [Hn|Hp].
- rewrite <- (Z.mod_add ch 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia.
- rewrite Z.mod_small by lia. lia.
Qed.
Lemma kp_res_word : forall c1 c2, bv_unsigned (w64 (hks_res c1 c2)) = 0 <-> hks_res c1 c2 = 0.
Proof.
intros c1 c2. destruct (hks_res_range c1 c2) as [E|[E|E]]; rewrite E; vm_compute; split; intros H; try discriminate H; reflexivity.
Qed.

Section main. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis errno_low : api_env rsegs B.
(* The strcmp wrapper's contract at 0x41ba0, at every float state: lib/A/HPgKcStr.v's Section hypothesis STRCMP at
   segs = rsegs (libreac/fuzz_identity lib/Reusable/AStrcmpDef.v astrcmp_realizes rsegs B 0x41ba0 at
   origin/ossv/recipes 2d2ff01bb6f, str_meet and strcmp_res unfolded and beta-reduced). *)
Hypothesis STRCMP : forall fx' : YK11.FPState,
  forall ly S W regs mem md x y k c1 c2,
  ecall_pre rsegs B ly S W regs mem md ->
  ly_stk_lo ly + 2 * ESTACK <= spZ regs -> (forall a, spZ regs - 2 * ESTACK <= a < spZ regs -> apresent (w_H W) mem a) ->
  getr regs 10 = w64 x -> getr regs 11 = w64 y -> 0 < x -> 0 < y ->
  k + 1 < 2 ^ 32 -> x + k + 1 <= 2 ^ 63 -> y + k + 1 <= 2 ^ 63 ->
  (0 <= k /\
   (forall i, 0 <= i < k -> exists b, aview rsegs (w_H W) mem (x + i) = Some b /\
                                      aview rsegs (w_H W) mem (y + i) = Some b /\ b <> 0) /\
   aview rsegs (w_H W) mem (x + k) = Some c1 /\ aview rsegs (w_H W) mem (y + k) = Some c2 /\
   (c1 <> c2 \/ c1 = 0)) ->
  src_ok rsegs W regs mem x (k + 1) -> src_ok rsegs W regs mem y (k + 1) ->
  (forall a, x <= a <= x + k -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) ->
  (forall a, y <= a <= y + k -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) ->
  amem_range x (k + 1) -> amem_range y (k + 1) ->
  range_addressable (aview rsegs (w_H W) mem) SHADOW_OFF x (k + 1) -> shadow_hull_vis (aview rsegs (w_H W) mem) x (k + 1) ->
  range_addressable (aview rsegs (w_H W) mem) SHADOW_OFF y (k + 1) -> shadow_hull_vis (aview rsegs (w_H W) mem) y (k + 1) ->
  SRr rsegs W (@cfg_at fx' rsegs A_STRCMP regs mem md)
    (fun W' c' => W' = W /\ exists regs' mem' md',
       c' = @cfg_at fx' rsegs (raZ regs) regs' mem' md' /\
       AR rsegs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
       getr regs' 10 = w64 (if c1 =? c2 then 0 else if c1 <? c2 then -1 else 1) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) ->
          aview rsegs (w_H W) mem' a = aview rsegs (w_H W) mem a) /\
       (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).

(* ---------------- the shared lemmas of HPgKcLib, as this file uses them ---------------- *)
Lemma kp_base3_kept : forall cx ev fx2 r sh ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3,
@hq_start_M03 fx rc SK rsegs B cx r ev ->
@hq_base3 fx rc SK rsegs B MT cx fx2 r sh ly2 S2 W2 regs2 mem2 md2 ->
length sh = 80%nat ->
ajournal rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
  (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly2 S2 W2 mem3 md3 (x_k rsegs cx) ->
(forall q : Z, q = 2 \/ q = 3 \/ q = 4 -> getr regs3 (Z_to_bv 5 q) = getr regs2 (Z_to_bv 5 q)) ->
same_io md2 md3 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e rsegs cx) - T_SEG_STK <= a < e_R (x_e rsegs cx)) -> ~ hk_wr cx a ->
 aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a) ->
@hq_base3 fx rc SK rsegs B MT cx fx2 r sh ly2 S2 W2 regs3 mem3 md3.
Proof. intros. eapply (hk_base3_kept (fx := fx)); eassumption. Qed.

Lemma kp_cstr_now : forall cx ev fx2 r sh ly2 S2 W2 regs2 mem2 md2 a s,
@hq_start_M03 fx rc SK rsegs B cx r ev ->
@hq_base3 fx rc SK rsegs B MT cx fx2 r sh ly2 S2 W2 regs2 mem2 md2 ->
In (a, s) (hi_strs headamp_himg_A) ->
hd_cstr rsegs (w_H W2) mem2 a s.
Proof. intros. eapply (hk_cstr_now (fx := fx)); eassumption. Qed.

Lemma kp_keymem : forall cx ev fx2 r sh ly2 S2 W2 regs2 mem2 md2 (m : nat) k,
@hq_start_M03 fx rc SK rsegs B cx r ev ->
@hq_base3 fx rc SK rsegs B MT cx fx2 r sh ly2 S2 W2 regs2 mem2 md2 ->
(m < length (Model.ents r))%nat ->
Accessors.key_of (nth m (Model.ents r) (Model.Ent 0 0 [])) = Some k ->
(length k <= 44)%nat /\ ~ In Cursor.NUL k /\
garr8 rsegs (mrestrict (w_H W2) mem2) (hk_kaddr rsegs cx m) (hd_zbytes k ++ [0]) /\
In (e_pp (x_e rsegs cx), Layout.PP_SIZE) (ablocks B ly2 S2) /\
4096 <= e_pp (x_e rsegs cx) /\ e_pp (x_e rsegs cx) + Layout.PP_SIZE <= alloc_ceiling.
Proof.
intros cx ev fx2 r sh ly2 S2 W2 regs2 mem2 md2 m k HS Hb Hm Hk.
edestruct (hk_keymem (fx := fx) B MT) as (H1 & H2 & _ & H4 & _ & H6 & H7 & H8 & _).
all: try eassumption.
exact (conj H1 (conj H2 (conj H4 (conj H6 (conj H7 H8))))).
Qed.

(* ---------------- the segment's start facts ---------------- *)
Lemma kp_start : forall cx r ev, @hq_start_M03 fx rc SK rsegs B cx r ev -> hs_pre rsegs B cx (hi_shA headamp_himg_A).
Proof. intros cx r ev HS. destruct HS as (H & _). exact H. Qed.

Lemma kp_geo : forall cx r ev, @hq_start_M03 fx rc SK rsegs B cx r ev ->
e_R (x_e rsegs cx) + 0x1e0 <= x_sp0 rsegs cx /\
x_sp0 rsegs cx - x_STK rsegs cx <= e_R (x_e rsegs cx) - T_SEG_STK /\
4096 <= e_F (x_e rsegs cx) /\ e_F (x_e rsegs cx) + 1024 <= alloc_ceiling /\
alloc_ceiling + T_SEG_STK <= e_R (x_e rsegs cx) /\ 0x7fff7f804000 <= e_R (x_e rsegs cx) /\ e_R (x_e rsegs cx) <= 2 ^ 47.
Proof.
intros cx r ev HS. pose proof (kp_start cx r ev HS) as Hpre.
pose proof Hpre as HC0. apply hc_core_of_seg_pre_A in HC0.
apply hc_core_R in HC0 as (HRc & HR47 & _).
unfold hs_pre, hd_seg_pre in Hpre.
destruct Hpre as (HJ0 & _ & _ & _ & _ & HS0 & _ & HRr & Hwin & Hown & HF & _).
change (hi_rsz headamp_himg_A) with 0x1e0 in HRr.
change (hi_cid headamp_himg_A) with 4 in Hown, HF.
pose proof (hc_frm_low rsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0 Hown) as (Hf4 & Hfl).
rewrite <- HF in Hf4.
rewrite hc_fb in Hfl. unfold HC_FB in Hfl. rewrite <- HF in Hfl.
pose proof asan_consts as (C1 & _). assert (Hts : T_SEG_STK = 16384) by reflexivity.
repeat split; lia.
Qed.

Lemma kp_core : forall cx r ev fx2 sh ly2 S2 W2 regs2 mem2 md2,
@hq_start_M03 fx rc SK rsegs B cx r ev ->
@hq_base3 fx rc SK rsegs B MT cx fx2 r sh ly2 S2 W2 regs2 mem2 md2 ->
hc_core rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
  (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) (x_k rsegs cx) ly2 S2 W2 mem2 md2 regs2 (e_R (x_e rsegs cx)).
Proof.
intros cx r ev fx2 sh ly2 S2 W2 regs2 mem2 md2 HS Hb.
pose proof (kp_start cx r ev HS) as HC0. apply hc_core_of_seg_pre_A in HC0.
destruct HC0 as (_ & Hnev & H2 & H3 & H4 & Hal & Hwin & HRs).
destruct Hb as ((HJ2 & Hr & _) & _).
split; [exact HJ2|]. split; [exact Hnev|].
split; [rewrite <- H2; exact (Hr 2 ltac:(lia))|].
split; [rewrite <- H3; exact (Hr 3 ltac:(lia))|].
split; [rewrite <- H4; exact (Hr 4 ltac:(lia))|].
split; [exact Hal|]. split; [exact Hwin | exact HRs].
Qed.

(* a value of a cut list *)
Lemma kp_at_reg : forall cx (W : world rsegs) mem regs L r v,
hs_at_cx rsegs cx W mem regs L -> In (LReg r, v) L -> getr regs (Z_to_bv 5 r) = w64 v.
Proof. intros cx W mem regs L r v H Hin. exact (proj1 (Forall_forall _ _) H _ Hin). Qed.
Lemma kp_at_cell : forall cx (W : world rsegs) mem regs L o v,
hs_at_cx rsegs cx W mem regs L -> In (LCell XR o, v) L ->
val_mem rsegs (mrestrict (w_H W) mem) (e_R (x_e rsegs cx) + o) 8 (v mod 2 ^ 64).
Proof. intros cx W mem regs L o v H Hin. exact (proj1 (Forall_forall _ _) H _ Hin). Qed.
Ltac kp_in := unfold hk_L, hq_L_seg, hq_L_frame, hq_L_loopc, hq_L_body; cbn [app In];
  repeat (first [left; reflexivity | right]).

(* ---------------- what a cut's facts keep across the part ---------------- *)
Lemma kp_keeps_cell : forall (W : world rsegs) mem mem' (regs regs' : bvmap 5 word) e o,
(forall a, 0 <= a < 2 ^ 64 -> ~ (e_R e - 2 * ESTACK <= a < e_R e) -> ~ kp_wr1 (e_R e) a ->
 aview rsegs (w_H W) mem' a = aview rsegs (w_H W) mem a) ->
0 <= e_R e -> e_R e + 0x120 <= 2 ^ 64 ->
(0 <= o /\ o + 8 <= 0x98) \/ (0xa8 <= o /\ o + 8 <= 0x120) ->
HPgMem.hm_keeps rsegs (w_H W) mem (w_H W) mem' regs regs' e (LCell XR o).
Proof.
intros W mem mem' regs regs' e o Hm HR0 HR1 Ho. cbn [HPgMem.hm_keeps hd_xv]. intros i Hi.
assert (Hes : ESTACK = 4096) by reflexivity.
apply Hm; [lia | lia | unfold kp_wr1; lia].
Qed.

Lemma kp_L3_kept : forall cx r (W : world rsegs) mem mem' (regs regs' : bvmap 5 word),
hs_at_cx rsegs cx W mem regs (hq_L_seg rsegs cx ++ hq_L_loopc rsegs cx ++ hq_L_body rsegs cx r) ->
(forall q, In q [8; 9; 19; 23; 22; 24; 25; 26; 27] -> getr regs' (Z_to_bv 5 q) = getr regs (Z_to_bv 5 q)) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e rsegs cx) - 2 * ESTACK <= a < e_R (x_e rsegs cx)) ->
 ~ kp_wr1 (e_R (x_e rsegs cx)) a -> aview rsegs (w_H W) mem' a = aview rsegs (w_H W) mem a) ->
0 <= e_R (x_e rsegs cx) -> e_R (x_e rsegs cx) + 0x120 <= 2 ^ 64 ->
hs_at_cx rsegs cx W mem' regs' (hq_L_seg rsegs cx ++ hq_L_loopc rsegs cx ++ hq_L_body rsegs cx r).
Proof.
intros cx r W mem mem' regs regs' H Hr Hm HR0 HR1. unfold hs_at_cx, hs_at in *.
eapply HPgMem.hm_atl_kept; [exact H|]. intros f Hf.
unfold hq_L_seg, hq_L_frame, hq_L_loopc, hq_L_body in Hf. cbn [app In] in Hf.
repeat (destruct Hf as [<-|Hf];
  [ first [ cbn [fst HPgMem.hm_keeps]; apply Hr; cbn [In]; repeat (first [left; reflexivity | right])
          | apply kp_keeps_cell; [exact Hm | exact HR0 | exact HR1 | lia] ] |]).
destruct Hf.
Qed.

Lemma kp_x_kept : forall cx (W : world rsegs) mem mem' cs keys rf,
hq_x_at rsegs cx W mem cs keys rf ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e rsegs cx) - 2 * ESTACK <= a < e_R (x_e rsegs cx)) ->
 ~ kp_wr1 (e_R (x_e rsegs cx)) a -> aview rsegs (w_H W) mem' a = aview rsegs (w_H W) mem a) ->
0 <= e_F (x_e rsegs cx) -> e_F (x_e rsegs cx) + 1024 + 2 * ESTACK <= e_R (x_e rsegs cx) -> e_R (x_e rsegs cx) <= 2 ^ 47 ->
hq_x_at rsegs cx W mem' cs keys rf.
Proof.
intros cx W mem mem' cs keys rf (Hg & Hl & Hrest) Hm HF0 HF1 HR1.
split; [|split; [exact Hl | exact Hrest]].
pose proof (hq_x_open_len cs keys rf Hl) as Hlen.
assert (Hes : ESTACK = 4096) by reflexivity.
apply (HPgMem.hm_bytes_kept rsegs (w_H W) mem (w_H W) mem' _ _ Hg).
intros x Hx. rewrite Hlen in Hx. unfold HQ_XO in Hx. apply Hm; [lia | lia | unfold kp_wr1; lia].
Qed.

(* ---------------- the state of the part relative to the DOT cut ---------------- *)
(* the journal at the cut's end state, its I/O state, sp / gp / tp and the callee-saved registers of hk_L, and every
   byte outside the callees' stack [R - 2 ESTACK, R) and the two saves [R+0x98, R+0xa8) *)
Definition kp_cs : list Z := [2; 3; 4; 8; 9; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Definition kp_mid (cx : hs_scx rsegs) ly2 S2 (W2 : world rsegs) (regs2 : bvmap 5 word) (mem2 : word -> option byte)
(md2 : Model) (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) : Prop :=
ajournal rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
  (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly2 S2 W2 mem3 md3 (x_k rsegs cx) /\
same_io md2 md3 /\
(forall q, In q kp_cs -> getr regs3 (Z_to_bv 5 q) = getr regs2 (Z_to_bv 5 q)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e rsegs cx) - 2 * ESTACK <= a < e_R (x_e rsegs cx)) ->
 ~ kp_wr1 (e_R (x_e rsegs cx)) a -> aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a).

Lemma kp_kept_cs : forall regs3 regs4 clob, kp_kept regs3 regs4 clob ->
forallb (fun q => negb (existsb (fun c => bv_eqb c (Z_to_bv 5 q)) clob)) kp_cs = true ->
forall q, In q kp_cs -> getr regs4 (Z_to_bv 5 q) = getr regs3 (Z_to_bv 5 q).
Proof.
intros regs3 regs4 clob Hk Hb q Hq. apply Hk.
- unfold kp_cs in Hq. cbn [In] in Hq.
  repeat (destruct Hq as [<-|Hq]; [intros Hz; cbv in Hz; discriminate Hz|]). destruct Hq.
- intros Hin. pose proof (proj1 (forallb_forall _ _) Hb q Hq) as Hq'. cbv beta in Hq'.
  apply negb_true_iff in Hq'.
  assert (Ht : existsb (fun c => bv_eqb c (Z_to_bv 5 q)) clob = true).
  { apply existsb_exists. exists (Z_to_bv 5 q). split; [exact Hin|]. apply bv_eqb_eq. reflexivity. }
  rewrite Ht in Hq'. discriminate Hq'.
Qed.

Lemma kp_mid_refl : forall cx ev fx2 r sh ly2 S2 W2 regs2 mem2 md2,
@hq_start_M03 fx rc SK rsegs B cx r ev ->
@hq_base3 fx rc SK rsegs B MT cx fx2 r sh ly2 S2 W2 regs2 mem2 md2 ->
kp_mid cx ly2 S2 W2 regs2 mem2 md2 regs2 mem2 md2.
Proof.
intros cx ev fx2 r sh ly2 S2 W2 regs2 mem2 md2 HS Hb. destruct Hb as ((HJ2 & _) & _).
split; [exact HJ2|]. split; [apply same_io_refl|]. split; [reflexivity|]. intros; reflexivity.
Qed.

Lemma kp_mid_step : forall cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 regs4 mem4 md4,
kp_mid cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 ->
ajournal rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
  (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly2 S2 W2 mem4 md4 (x_k rsegs cx) ->
same_io md3 md4 ->
(forall q, In q kp_cs -> getr regs4 (Z_to_bv 5 q) = getr regs3 (Z_to_bv 5 q)) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e rsegs cx) - 2 * ESTACK <= a < e_R (x_e rsegs cx)) ->
 ~ kp_wr1 (e_R (x_e rsegs cx)) a -> aview rsegs (w_H W2) mem4 a = aview rsegs (w_H W2) mem3 a) ->
kp_mid cx ly2 S2 W2 regs2 mem2 md2 regs4 mem4 md4.
Proof.
intros cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 regs4 mem4 md4 (HJ3 & Hio3 & Hr3 & Hm3) HJ4 Hio4 Hr4 Hm4.
split; [exact HJ4|]. split; [eapply same_io_trans; [exact Hio3 | exact Hio4]|].
split; [intros q Hq; rewrite (Hr4 q Hq); exact (Hr3 q Hq)|].
intros a Ha H1 H2. rewrite (Hm4 a Ha H1 H2). exact (Hm3 a Ha H1 H2).
Qed.

(* a call: the callee-saved registers and every byte outside the callees' stack *)
Lemma kp_mid_call : forall cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 regs4 mem4 md4,
kp_mid cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 ->
hc_core rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
  (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) (x_k rsegs cx) ly2 S2 W2 mem4 md4 regs4 (e_R (x_e rsegs cx)) ->
aregs_preserved regs3 regs4 -> same_io md3 md4 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e rsegs cx) - 2 * ESTACK <= a < e_R (x_e rsegs cx)) ->
 aview rsegs (w_H W2) mem4 a = aview rsegs (w_H W2) mem3 a) ->
kp_mid cx ly2 S2 W2 regs2 mem2 md2 regs4 mem4 md4.
Proof.
intros cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 regs4 mem4 md4 HM HC HP Hio Hm.
apply (kp_mid_step cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 regs4 mem4 md4 HM); [exact (proj1 HC) | exact Hio | |].
- intros q Hq. apply HP. unfold kp_cs in Hq. unfold acallee_saved. cbn [In] in Hq. lia.
- intros a Ha H1 _. exact (Hm a Ha H1).
Qed.

Lemma kp_mid_post : forall cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 regs4 mem4 md4 clob (Wr : Z -> Prop),
kp_mid cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 ->
ajournal rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
  (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly2 S2 W2 mem4 md4 (x_k rsegs cx) ->
same_io md3 md4 -> kp_kept regs3 regs4 clob ->
forallb (fun q => negb (existsb (fun c => bv_eqb c (Z_to_bv 5 q)) clob)) kp_cs = true ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview rsegs (w_H W2) mem4 a = aview rsegs (w_H W2) mem3 a) ->
(forall a, Wr a -> kp_wr1 (e_R (x_e rsegs cx)) a) ->
kp_mid cx ly2 S2 W2 regs2 mem2 md2 regs4 mem4 md4.
Proof.
intros cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 regs4 mem4 md4 clob Wr HM HJ Hio Hk Hb Hm HW.
apply (kp_mid_step cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 regs4 mem4 md4 HM HJ Hio).
- exact (kp_kept_cs regs3 regs4 clob Hk Hb).
- intros a Ha _ H2. apply Hm; [exact Ha|]. intros Hw. exact (H2 (HW a Hw)).
Qed.

Lemma kp_core_mid : forall cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3,
hc_core rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
  (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) (x_k rsegs cx) ly2 S2 W2 mem2 md2 regs2 (e_R (x_e rsegs cx)) ->
kp_mid cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 ->
hc_core rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
  (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) (x_k rsegs cx) ly2 S2 W2 mem3 md3 regs3 (e_R (x_e rsegs cx)).
Proof.
intros cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 (_ & Hnev & H2 & H3 & H4 & Hal & Hwin & HRs) (HJ3 & _ & Hr & _).
split; [exact HJ3|]. split; [exact Hnev|].
split; [rewrite <- H2; exact (Hr 2 ltac:(cbn; tauto))|].
split; [rewrite <- H3; exact (Hr 3 ltac:(cbn; tauto))|].
split; [rewrite <- H4; exact (Hr 4 ltac:(cbn; tauto))|].
split; [exact Hal|]. split; [exact Hwin | exact HRs].
Qed.

Lemma kp_base3_mid : forall cx ev fx2 r ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3,
@hq_start_M03 fx rc SK rsegs B cx r ev ->
@hq_base3 fx rc SK rsegs B MT cx fx2 r hq_shX ly2 S2 W2 regs2 mem2 md2 ->
kp_mid cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 ->
@hq_base3 fx rc SK rsegs B MT cx fx2 r hq_shX ly2 S2 W2 regs3 mem3 md3.
Proof.
intros cx ev fx2 r ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 HS Hb (HJ3 & Hio & Hr & Hm).
apply (kp_base3_kept cx ev fx2 r hq_shX ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 HS Hb hq_shX_len HJ3); [| exact Hio |].
- intros q Hq. apply Hr. unfold kp_cs. cbn [In]. lia.
- intros a Ha H1 H2. assert (Hes : ESTACK = 4096) by reflexivity. assert (Hts : T_SEG_STK = 16384) by reflexivity.
  apply Hm; [exact Ha | lia |]. intros Hw. apply H2. left. unfold kp_wr1 in Hw. lia.
Qed.

Lemma kp_val_step : forall (W : world rsegs) m1 m2 R a v,
val_mem rsegs (mrestrict (w_H W) m1) a 8 v ->
(forall x, 0 <= x < 2 ^ 64 -> ~ (R - 2 * ESTACK <= x < R) -> aview rsegs (w_H W) m2 x = aview rsegs (w_H W) m1 x) ->
0 <= R -> R <= a -> a + 8 <= 2 ^ 64 -> val_mem rsegs (mrestrict (w_H W) m2) a 8 v.
Proof.
intros W m1 m2 R a v H Hm HR Ha Ha8. eapply val_mem_kept; [|exact H]. intros i Hi.
assert (Hes : ESTACK = 4096) by reflexivity. apply Hm; [lia | lia].
Qed.
Lemma kp_val_eq : forall (W : world rsegs) m1 m2 a v,
val_mem rsegs (mrestrict (w_H W) m1) a 8 v ->
(forall x, 0 <= x < 2 ^ 64 -> ~ False -> aview rsegs (w_H W) m2 x = aview rsegs (w_H W) m1 x) ->
0 <= a -> a + 8 <= 2 ^ 64 -> val_mem rsegs (mrestrict (w_H W) m2) a 8 v.
Proof.
intros W m1 m2 a v H Hm Ha Ha8. eapply val_mem_kept; [|exact H]. intros i Hi. apply Hm; [lia | tauto].
Qed.

Lemma kp_cell_mid : forall cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 o v,
kp_mid cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 ->
val_mem rsegs (mrestrict (w_H W2) mem2) (e_R (x_e rsegs cx) + o) 8 v ->
0 <= e_R (x_e rsegs cx) -> e_R (x_e rsegs cx) <= 2 ^ 47 -> 0xa8 <= o -> o + 8 <= 0x120 ->
val_mem rsegs (mrestrict (w_H W2) mem3) (e_R (x_e rsegs cx) + o) 8 v.
Proof.
intros cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 o v (_ & _ & _ & Hm) H HR0 HR1 Ho1 Ho2.
eapply val_mem_kept; [|exact H]. intros i Hi. assert (Hes : ESTACK = 4096) by reflexivity.
apply Hm; [lia | lia | unfold kp_wr1; lia].
Qed.

Ltac kp_incs := unfold kp_cs; cbn [In]; repeat (first [left; reflexivity | right]).
Ltac kp_nz := let H := fresh in intros H; cbv in H; discriminate H.
Ltac kp_nin := let H := fresh in intros H; cbn [In] in H;
  repeat (destruct H as [H|H]; [apply (f_equal (@bv_unsigned 5)) in H; cbv in H; discriminate H|]); exact H.

(* ======================================== the part from the DOT cut ======================================== *)
Section dot.
Variable cx : hs_scx rsegs.
Variable r : Model.pod_rec.
Variable POST : world rsegs -> config -> Prop.
Variable ev : Z.
Variables at0 m : nat.
Hypothesis HS : @hq_start_M03 fx rc SK rsegs B cx r ev.
Hypothesis HVAL : @hq_from_VAL fx rc SK rsegs B MT cx r POST at0 m.
Hypothesis HRF : @hq_from_RF fx rc SK rsegs B MT cx r POST at0 m.
Variable fx2 : YK11.FPState.
Variables (ly2 : alayout) (S2 : astate) (W2 : world rsegs) (regs2 : bvmap 5 word) (mem2 : word -> option byte)
  (md2 : Model).
Variables (k : list byte) (cs : list cell) (keys rf : Z) (nd : nat) (acc : Z) (big : bool).
Hypothesis HC : @hk_cut_DOT fx rc SK rsegs B MT cx fx2 r at0 m k cs keys rf nd acc big ly2 S2 W2 regs2 mem2 md2.

Lemma kp_HI : @hk_inv fx rc SK rsegs B MT cx fx2 r at0 m k cs keys rf ly2 S2 W2 regs2 mem2 md2.
Proof. exact (proj1 HC). Qed.

(* the cut's RF exit: the refusal fold with t3 = bad *)
Lemma kp_rf_leaf : forall regs3 mem3 md3 bad,
kp_mid cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 ->
getr regs3 (Z_to_bv 5 31) = getr regs2 (Z_to_bv 5 31) -> getr regs3 (Z_to_bv 5 7) = getr regs2 (Z_to_bv 5 7) ->
getr regs3 (Z_to_bv 5 28) = w64 bad ->
expect_cell k (nth (S m) (Model.ents r) (Model.Ent 0 0 [])) = inl bad ->
(bad = REFUSE_BAD_KEY \/ bad = REFUSE_OUT_OF_RANGE) ->
SRr rsegs W2 (@cfg_at fx2 rsegs HQ_RF regs3 mem3 md3) POST.
Proof.
intros regs3 mem3 md3 bad HM H31 H7 H28 Hcell Hbad.
pose proof kp_HI as (Hb & Hat & Hfs9 & Hfs18 & Hlive & Hat0 & Hkey & Hpair & Hx & Hcs).
pose proof (kp_geo cx r ev HS) as (HRs & Hwin & HF4 & HFc & HRc & HR0 & HR47).
pose proof HM as (HJ3 & Hio3 & Hr3 & Hm3).
assert (Hes : ESTACK = 4096) by reflexivity. assert (Hts : T_SEG_STK = 16384) by reflexivity.
assert (HL3 : hs_at_cx rsegs cx W2 mem2 regs2 (hq_L_seg rsegs cx ++ hq_L_loopc rsegs cx ++ hq_L_body rsegs cx r)).
{ unfold hs_at_cx, hs_at in *. unfold hk_L in Hat. rewrite app_assoc, app_assoc in Hat.
  apply Forall_app in Hat as [Hat _]. rewrite <- app_assoc in Hat. exact Hat. }
apply (HRF fx2 ly2 S2 W2 regs3 mem3 md3 k (nth (S m) (Model.ents r) (Model.Ent 0 0 [])) bad cs keys rf).
split; [exact (kp_base3_mid cx ev fx2 r ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 HS Hb HM)|].
split.
{ unfold hs_at_cx, hs_at. rewrite app_assoc, app_assoc. apply Forall_app. split.
  - rewrite <- app_assoc.
    exact (kp_L3_kept cx r W2 mem2 mem3 regs2 regs3 HL3 ltac:(intros q Hq; apply Hr3; unfold kp_cs; cbn [In] in *; lia)
      Hm3 ltac:(lia) ltac:(lia)).
  - repeat apply Forall_cons; [..|apply Forall_nil]; cbv beta; cbn [fst snd hd_at].
    + rewrite H31. exact (kp_at_reg _ _ _ _ _ 31 _ Hat ltac:(kp_in)).
    + rewrite H7. exact (kp_at_reg _ _ _ _ _ 7 _ Hat ltac:(kp_in)).
    + rewrite (Hr3 21 ltac:(kp_incs)). exact (kp_at_reg _ _ _ _ _ 21 _ Hat ltac:(kp_in)).
    + exact H28. }
split; [exact Hfs9|]. split; [exact Hfs18|]. split; [exact Hlive|]. split; [exact Hat0|].
split; [exact Hcell|]. split; [exact Hbad|]. split; [exact Hpair|].
exact (kp_x_kept cx W2 mem2 mem3 cs (keys + 1) rf Hx Hm3 ltac:(lia) ltac:(lia) HR47).
Qed.

(* the cut's VAL exit *)
Lemma kp_val_leaf : forall regs3 mem3 md3 ch p,
kp_mid cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 ->
getr regs3 (Z_to_bv 5 31) = getr regs2 (Z_to_bv 5 31) -> getr regs3 (Z_to_bv 5 7) = getr regs2 (Z_to_bv 5 7) ->
getr regs3 (Z_to_bv 5 13) = w64 p -> getr regs3 (Z_to_bv 5 18) = w64 (if p =? HA_SENS then HA_SENS_MAX else 1) ->
getr regs3 (Z_to_bv 5 28) = w64 REFUSE_OUT_OF_RANGE ->
val_mem rsegs (mrestrict (w_H W2) mem3) (e_R (x_e rsegs cx) + 0xa0) 8 (ch mod 2 ^ 64) ->
expect_key (skipn (length HA_PREFIX) k) = KCell ch p ->
SRr rsegs W2 (@cfg_at fx2 rsegs HQ_VAL regs3 mem3 md3) POST.
Proof.
intros regs3 mem3 md3 ch p HM H31 H7 H13 H18 H28 Vc Hkey.
pose proof kp_HI as (Hb & Hat & Hfs9 & Hfs18 & Hlive & Hat0 & Hkey0 & Hpair & Hx & Hcs).
pose proof (kp_geo cx r ev HS) as (HRs & Hwin & HF4 & HFc & HRc & HR0 & HR47).
pose proof HM as (HJ3 & Hio3 & Hr3 & Hm3).
assert (Hes : ESTACK = 4096) by reflexivity. assert (Hts : T_SEG_STK = 16384) by reflexivity.
assert (HL3 : hs_at_cx rsegs cx W2 mem2 regs2 (hq_L_seg rsegs cx ++ hq_L_loopc rsegs cx ++ hq_L_body rsegs cx r)).
{ unfold hs_at_cx, hs_at in *. unfold hk_L in Hat. rewrite app_assoc, app_assoc in Hat.
  apply Forall_app in Hat as [Hat _]. rewrite <- app_assoc in Hat. exact Hat. }
apply (HVAL fx2 ly2 S2 W2 regs3 mem3 md3 k (nth (S m) (Model.ents r) (Model.Ent 0 0 [])) ch p cs keys rf).
split; [exact (kp_base3_mid cx ev fx2 r ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 HS Hb HM)|].
split.
{ unfold hs_at_cx, hs_at. rewrite app_assoc, app_assoc. apply Forall_app. split.
  - rewrite <- app_assoc.
    exact (kp_L3_kept cx r W2 mem2 mem3 regs2 regs3 HL3 ltac:(intros q Hq; apply Hr3; unfold kp_cs; cbn [In] in *; lia)
      Hm3 ltac:(lia) ltac:(lia)).
  - repeat apply Forall_cons; [..|apply Forall_nil]; cbv beta; cbn [fst snd hd_at hd_xv].
    + rewrite H31. exact (kp_at_reg _ _ _ _ _ 31 _ Hat ltac:(kp_in)).
    + rewrite H7. exact (kp_at_reg _ _ _ _ _ 7 _ Hat ltac:(kp_in)).
    + exact H13.
    + exact H18.
    + rewrite (Hr3 20 ltac:(kp_incs)). exact (kp_at_reg _ _ _ _ _ 20 _ Hat ltac:(kp_in)).
    + rewrite (Hr3 21 ltac:(kp_incs)). exact (kp_at_reg _ _ _ _ _ 21 _ Hat ltac:(kp_in)).
    + exact H28.
    + exact Vc. }
split; [exact Hfs9|]. split; [exact Hfs18|]. split; [exact Hlive|]. split; [exact Hat0|].
split; [exact Hkey|]. split; [exact Hpair|]. split; [exact Hcs|].
exact (kp_x_kept cx W2 mem2 mem3 cs (keys + 1) rf Hx Hm3 ltac:(lia) ltac:(lia) HR47).
Qed.

(* the tail 0x8334c from a found name with param p: big or ch out of range go to RF, else VAL *)
Lemma kp_tail_case : forall regs3 mem3 md3 p chv,
kp_mid cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 ->
getr regs3 (Z_to_bv 5 31) = getr regs2 (Z_to_bv 5 31) -> getr regs3 (Z_to_bv 5 7) = getr regs2 (Z_to_bv 5 7) ->
getr regs3 (Z_to_bv 5 13) = w64 p -> getr regs3 (Z_to_bv 5 18) = w64 (if p =? HA_SENS then HA_SENS_MAX else 1) ->
val_mem rsegs (mrestrict (w_H W2) mem3) (e_R (x_e rsegs cx) + 0x98) 8 (Z.b2z big) ->
val_mem rsegs (mrestrict (w_H W2) mem3) (e_R (x_e rsegs cx) + 0xa0) 8 (chv mod 2 ^ 64) ->
-10000009 <= chv <= 10000009 ->
expect_key (skipn (length HA_PREFIX) k) =
  (if big || (chv <? 0) || (HA_CHANNELS <=? chv) then KRange else KCell chv p) ->
SRr rsegs W2 (@cfg_at fx2 rsegs KP_TAIL regs3 mem3 md3) POST.
Proof.
intros regs3 mem3 md3 p chv HM H31 H7 H13 H18 Vb Vc Hch Hkey.
pose proof kp_HI as (Hb & Hat & _).
pose proof (kp_geo cx r ev HS) as (_ & _ & _ & _ & _ & HR0 & HR47).
pose proof HM as (HJ3 & _ & Hr3 & _).
assert (H9 : getr regs3 (Z_to_bv 5 9) = w64 (e_R (x_e rsegs cx))).
{ rewrite (Hr3 9 ltac:(kp_incs)). exact (kp_at_reg _ _ _ _ _ 9 _ Hat ltac:(kp_in)). }
eapply SRr_bind.
{ apply (kp_tail_blk (fx := fx2) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs3 (e_R (x_e rsegs cx)) (Z.b2z big) (chv mod 2 ^ 64)
    HJ3 H9); [lia | lia | destruct big; cbn; lia | apply Z.mod_pos_bound; lia | exact Vb | exact Vc]. }
intros W4 c4 _ [(Hc & HP) | (Hb0 & Hc & HP)];
  destruct HP as (-> & regs4 & mem4 & md4 & -> & HJ4 & Hio4 & Hk4 & Hm4 & Hr4).
- assert (HM4 : kp_mid cx ly2 S2 W2 regs2 mem2 md2 regs4 mem4 md4)
    by (apply (kp_mid_post cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 regs4 mem4 md4 _ (fun _ => False) HM HJ4 Hio4 Hk4
          ltac:(vm_compute; reflexivity) Hm4); intros a []).
  apply (kp_rf_leaf regs4 mem4 md4 REFUSE_OUT_OF_RANGE HM4).
  + rewrite (Hk4 (Z_to_bv 5 31) ltac:(kp_nz) ltac:(kp_nin)). exact H31.
  + rewrite (Hk4 (Z_to_bv 5 7) ltac:(kp_nz) ltac:(kp_nin)). exact H7.
  + exact Hr4.
  + apply kp_cell_range. rewrite Hkey.
    destruct Hc as [Hc|Hc].
    * destruct big; [reflexivity | cbn in Hc; lia].
    * assert (Hn : ~ (0 <= chv <= 47)) by (rewrite <- (kp_chw chv Hch); lia).
      destruct (Z.ltb_spec chv 0); [rewrite orb_true_r; reflexivity|].
      destruct (Z.leb_spec HA_CHANNELS chv) as [Hl|Hl]; [rewrite !orb_true_r; reflexivity|].
      unfold HA_CHANNELS in Hl. lia.
  + right; reflexivity.
- assert (HM4 : kp_mid cx ly2 S2 W2 regs2 mem2 md2 regs4 mem4 md4)
    by (apply (kp_mid_post cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 regs4 mem4 md4 _ (fun _ => False) HM HJ4 Hio4 Hk4
          ltac:(vm_compute; reflexivity) Hm4); intros a []).
  assert (Hbig : big = false) by (destruct big; [cbn in Hb0; lia | reflexivity]). rewrite Hbig in Hkey.
  assert (Hr : 0 <= chv <= 47) by (apply (kp_chw chv Hch); exact Hc).
  apply (kp_val_leaf regs4 mem4 md4 chv p HM4).
  + rewrite (Hk4 (Z_to_bv 5 31) ltac:(kp_nz) ltac:(kp_nin)). exact H31.
  + rewrite (Hk4 (Z_to_bv 5 7) ltac:(kp_nz) ltac:(kp_nin)). exact H7.
  + rewrite (Hk4 (Z_to_bv 5 13) ltac:(kp_nz) ltac:(kp_nin)). exact H13.
  + rewrite (Hk4 (Z_to_bv 5 18) ltac:(kp_nz) ltac:(kp_nin)). exact H18.
  + exact Hr4.
  + exact (kp_val_eq W2 mem3 mem4 _ _ Vc Hm4 ltac:(lia) ltac:(lia)).
  + rewrite Hkey. destruct (Z.ltb_spec chv 0) as [Hl|Hl]; [lia|].
    destruct (Z.leb_spec HA_CHANNELS chv) as [Hl2|Hl2]; [unfold HA_CHANNELS in Hl2; lia | reflexivity].
Qed.

(* the name after the channel's '.': its address (s2 := s2 + a0 + 14 at 0x832d4 .. 0x832d8) and its bytes *)
Definition kp_name : Z := hk_kaddr rsegs cx m + Z.of_nat (hk_d (hk_rest k)) + Z.of_nat nd + 14.
Definition kp_nb : list byte := skipn (S (hk_d (hk_rest k) + nd)) (hk_rest k).
Definition kp_chv : Z := if hk_neg (hk_rest k) then - acc else acc.

Lemma kp_prefix_len : length HA_PREFIX = 13%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma kp_nb_nul : ~ In Cursor.NUL kp_nb.
Proof.
pose proof kp_HI as (Hb & _ & _ & _ & _ & _ & Hkey & Hpair & _).
pose proof Hpair as (_ & _ & HSm & _).
destruct (kp_keymem cx ev fx2 r hq_shX ly2 S2 W2 regs2 mem2 md2 m k HS Hb ltac:(lia) Hkey) as (_ & Hnul & _).
unfold kp_nb, hk_rest. apply kp_notin_skipn, kp_notin_skipn. exact Hnul.
Qed.

(* read_channel's answer and the name give expect_key *)
Lemma kp_key_eq : bv_unsigned (nth (hk_d (hk_rest k) + nd) (hk_rest k) Cursor.NUL) = 46 ->
expect_key (skipn (length HA_PREFIX) k) =
  match param_of_name kp_nb with
  | None => KBad
  | Some p => if big || (kp_chv <? 0) || (HA_CHANNELS <=? kp_chv) then KRange else KCell kp_chv p
  end.
Proof.
intros Hdot. pose proof HC as (_ & _ & Hnd & Hrc & _).
change (skipn (length HA_PREFIX) k) with (hk_rest k). rewrite (kp_expect_key_eq _ _ _ _ Hrc).
replace ((hk_d (hk_rest k) + nd =? 0)%nat) with false by (symmetry; apply Nat.eqb_neq; lia).
rewrite Hdot. cbn [orb negb Z.eqb Pos.eqb].
change (skipn (S (hk_d (hk_rest k) + nd)) (hk_rest k)) with kp_nb. fold kp_chv.
rewrite (kp_cstr_id _ kp_nb_nul). reflexivity.
Qed.

(* the strcmp at the name in the continuation form: the walk continues at ret with the part's facts, the
   callee-saved registers, the bytes outside the callees' stack and a0 = v, v = 0 exactly when the name is lit *)
Lemma kp_call : forall regs3 mem3 md3 ret alit lit,
kp_mid cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 ->
getr regs3 (Z_to_bv 5 1) = w64 ret -> 0 <= ret < 2 ^ 64 -> ret mod 2 = 0 ->
getr regs3 (Z_to_bv 5 10) = w64 kp_name -> getr regs3 (Z_to_bv 5 11) = w64 alit ->
In (alit, hd_zbytes lit) (hi_strs headamp_himg_A) ->
bv_unsigned (nth (hk_d (hk_rest k) + nd) (hk_rest k) Cursor.NUL) = 46 ->
(forall regs4 mem4 md4, kp_mid cx ly2 S2 W2 regs2 mem2 md2 regs4 mem4 md4 -> aregs_preserved regs3 regs4 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e rsegs cx) - 2 * ESTACK <= a < e_R (x_e rsegs cx)) ->
   aview rsegs (w_H W2) mem4 a = aview rsegs (w_H W2) mem3 a) ->
  (exists v, getr regs4 (Z_to_bv 5 10) = w64 v /\ 0 <= v < 2 ^ 64 /\ (v = 0 <-> kp_nb = lit)) ->
  SRr rsegs W2 (@cfg_at fx2 rsegs ret regs4 mem4 md4) POST) ->
SRr rsegs W2 (@cfg_at fx2 rsegs A_STRCMP regs3 mem3 md3) POST.
Proof.
intros regs3 mem3 md3 ret alit lit HM H1 Hret Hret2 H10 H11 Hin Hdot K.
pose proof kp_HI as (Hb & _ & _ & _ & _ & _ & Hkey & Hpair & _).
pose proof Hpair as (_ & _ & HSm & _).
pose proof (hk_start_wf (fx := fx) rsegs B cx r ev HS) as Hwf.
pose proof (Model.ents_wf r Hwf) as (Hn32 & _).
pose proof (kp_core cx r ev fx2 hq_shX ly2 S2 W2 regs2 mem2 md2 HS Hb) as HC2.
pose proof (kp_core_mid cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 HC2 HM) as HC3.
pose proof (kp_base3_mid cx ev fx2 r ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 HS Hb HM) as Hb3.
destruct (kp_keymem cx ev fx2 r hq_shX ly2 S2 W2 regs3 mem3 md3 m k HS Hb3 ltac:(lia) Hkey)
  as (Hk44 & Hnul & Hg & Hpp & Hpp1 & Hpp2).
pose proof (kp_cstr_now cx ev fx2 r hq_shX ly2 S2 W2 regs3 mem3 md3 alit (hd_zbytes lit) HS Hb3 Hin) as Hlit.
assert (Hlr : length (hk_rest k) = (length k - 13)%nat)
  by (unfold hk_rest; rewrite length_skipn, kp_prefix_len; reflexivity).
assert (Hu : (hk_d (hk_rest k) + nd < length (hk_rest k))%nat).
{ destruct (Nat.lt_ge_cases (hk_d (hk_rest k) + nd) (length (hk_rest k))) as [Hl|Hl]; [exact Hl|].
  rewrite nth_overflow in Hdot by exact Hl. cbv in Hdot. discriminate Hdot. }
assert (Hnb : kp_nb = skipn (S (hk_d (hk_rest k) + nd) + 13) k)
  by (unfold kp_nb, hk_rest; rewrite skipn_skipn, kp_prefix_len; reflexivity).
assert (Hlnb : length kp_nb = (length k - (S (hk_d (hk_rest k) + nd) + 13))%nat) by (rewrite Hnb; apply length_skipn).
pose proof (kp_garr8_suffix _ _ k (S (hk_d (hk_rest k) + nd) + 13) Hg ltac:(lia)) as Hgn.
rewrite <- Hnb in Hgn.
replace (hk_kaddr rsegs cx m + Z.of_nat (S (hk_d (hk_rest k) + nd) + 13)) with kp_name in Hgn
  by (unfold kp_name; lia).
assert (Hkd : hk_kaddr rsegs cx m = e_pp (x_e rsegs cx) + 0x401c + 104 * Z.of_nat m) by reflexivity.
assert (Hrq : req_size Layout.PP_SIZE = 19744) by reflexivity.
assert (HPP : Layout.PP_SIZE = 19744) by reflexivity.
apply (hks_strcmp_call (fx := fx2) rsegs B img_segs_low STRCMP POST ret alit lit (x_STK rsegs cx) (x_sp0 rsegs cx)
  (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx)
  (x_k rsegs cx) ly2 S2 W2 mem3 md3 regs3 (e_R (x_e rsegs cx)) kp_name (e_pp (x_e rsegs cx)) Layout.PP_SIZE kp_nb
  HC3 H1 Hret Hret2 H10 H11 Hpp).
- unfold kp_name. lia.
- rewrite Hrq, Hlnb. unfold kp_name. lia.
- exact Hgn.
- exact kp_nb_nul.
- exact Hlit.
- intros regs4 mem4 md4 HC4 HP4 Hio4 Hm4 (c1 & c2 & Hv & Hres). apply K.
  + exact (kp_mid_call cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 regs4 mem4 md4 HM HC4 HP4 Hio4 Hm4).
  + exact HP4.
  + exact Hm4.
  + exists (bv_unsigned (w64 (hks_res c1 c2))). split; [|split].
    * etransitivity; [exact Hv|]. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity.
    * pose proof (bv_unsigned_in_range _ (w64 (hks_res c1 c2))) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr. lia.
    * rewrite kp_res_word. exact Hres.
Qed.

Ltac kp_lit := cbv [hi_strs headamp_himg_A headamp_A_strs]; repeat (first [left; reflexivity | right]).
Ltac kp_keep1 Hk q := rewrite (Hk (Z_to_bv 5 q) ltac:(kp_nz) ltac:(kp_nin)).

(* the whole part from DOT *)
Lemma kp_main : SRr rsegs W2 (@cfg_at fx2 rsegs HK_DOT regs2 mem2 md2) POST.
Proof.
pose proof HC as (HI & Hat & Hnd & Hrc & Hacc).
pose proof HI as (Hb & HatL & _ & _ & _ & _ & Hkey & Hpair & _).
pose proof Hb as ((HJ2 & _) & _).
pose proof (kp_geo cx r ev HS) as (HRs & Hwin & HF4 & HFc & HRc & HR0 & HR47).
pose proof Hpair as (_ & _ & HSm & _).
pose proof (hk_start_wf (fx := fx) rsegs B cx r ev HS) as Hwf.
pose proof (Model.ents_wf r Hwf) as (Hn32 & _).
pose proof (hk_inv_key_len (fx := fx) rsegs B MT cx fx2 r at0 m k cs keys rf ly2 S2 W2 regs2 mem2 md2 Hwf HI) as Hk45.
pose proof (kp_used_le (hk_rest k) nd _ _ Hnd Hrc) as Hused.
pose proof (hk_rest_len k) as Hrl.
destruct (kp_keymem cx ev fx2 r hq_shX ly2 S2 W2 regs2 mem2 md2 m k HS Hb ltac:(lia) Hkey) as (_ & _ & _ & _ & Hpp1 & Hpp2).
pose proof (kp_mid_refl cx ev fx2 r hq_shX ly2 S2 W2 regs2 mem2 md2 HS Hb) as HM2.
assert (Hes : ESTACK = 4096) by reflexivity. assert (Hts : T_SEG_STK = 16384) by reflexivity.
assert (Hkd : hk_kaddr rsegs cx m = e_pp (x_e rsegs cx) + 0x401c + 104 * Z.of_nat m) by reflexivity.
assert (HPP : Layout.PP_SIZE = 19744) by reflexivity.
pose proof asan_consts as (C1 & _).
(* the cut's registers and cells *)
pose proof (kp_at_reg _ _ _ _ _ 18 _ Hat ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) as R18.
pose proof (kp_at_reg _ _ _ _ _ 10 _ Hat ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) as R10.
pose proof (kp_at_reg _ _ _ _ _ 11 _ Hat ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) as R11.
pose proof (kp_at_reg _ _ _ _ _ 12 _ Hat ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) as R12.
pose proof (kp_at_reg _ _ _ _ _ 13 _ Hat ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) as R13.
pose proof (kp_at_reg _ _ _ _ _ 6 _ Hat ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) as R6.
pose proof (kp_at_reg _ _ _ _ _ 29 _ Hat ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) as R29.
pose proof (kp_at_reg _ _ _ _ _ 28 _ Hat ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) as R28.
pose proof (kp_at_reg _ _ _ _ _ 9 _ HatL ltac:(kp_in)) as R9.
pose proof (kp_at_reg _ _ _ _ _ 31 _ HatL ltac:(kp_in)) as R31.
pose proof (kp_at_reg _ _ _ _ _ 7 _ HatL ltac:(kp_in)) as R7.
pose proof (kp_at_cell _ _ _ _ _ 0xd8 _ HatL ltac:(kp_in)) as Cd8.
pose proof (kp_at_cell _ _ _ _ _ 0xe0 _ HatL ltac:(kp_in)) as Ce0.
pose proof (Cursor.byte_range (nth (hk_d (hk_rest k) + nd) (hk_rest k) Cursor.NUL)) as Hc256.
assert (Hchv : -10000009 <= kp_chv <= 10000009) by (unfold kp_chv; destruct (hk_neg (hk_rest k)); lia).
(* DOT 0x832b0 .. 0x832c8 *)
eapply SRr_bind.
{ apply (kp_dot_blk (fx := fx2) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 (Z.of_nat (hk_d (hk_rest k))) (Z.of_nat nd) acc
    (bv_unsigned (nth (hk_d (hk_rest k) + nd) (hk_rest k) Cursor.NUL)) (if hk_neg (hk_rest k) then 0 else 1)
    HJ2 R10 R11 R12 R13 R6); [lia | lia | destruct (hk_neg (hk_rest k)); [left | right]; reflexivity | exact Hc256 | lia]. }
intros W3 c3 _ [(Hc & HP) | (Hc & HP)]; destruct HP as (-> & regs3 & mem3 & md3 & -> & HJ3 & Hio3 & Hk3 & Hm3 & Hr3);
  (assert (HM3 : kp_mid cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3)
     by (apply (kp_mid_post cx ly2 S2 W2 regs2 mem2 md2 regs2 mem2 md2 regs3 mem3 md3 _ (fun _ => False) HM2 HJ3 Hio3
           Hk3 ltac:(vm_compute; reflexivity) Hm3); intros a [])).
{ (* no '.' after the digits: RF with BAD_KEY *)
  apply (kp_rf_leaf regs3 mem3 md3 REFUSE_BAD_KEY HM3).
  - kp_keep1 Hk3 31. reflexivity.
  - kp_keep1 Hk3 7. reflexivity.
  - kp_keep1 Hk3 28. exact R28.
  - apply kp_cell_bad. change (skipn (length HA_PREFIX) k) with (hk_rest k). rewrite (kp_expect_key_eq _ _ _ _ Hrc).
    replace (bv_unsigned (nth (hk_d (hk_rest k) + nd) (hk_rest k) Cursor.NUL) =? 46) with false
      by (symmetry; apply Z.eqb_neq; exact Hc).
    rewrite orb_true_r. reflexivity.
  - left; reflexivity. }
(* the '.': the saves, the name, the first strcmp's arguments *)
assert (R6' : getr regs3 (Z_to_bv 5 6) = w64 (kp_chv mod 2 ^ 64)).
{ rewrite Hr3. unfold kp_chv, w64. rewrite Z_to_bv_mod64. destruct (hk_neg (hk_rest k)); reflexivity. }
eapply SRr_bind.
{ apply (kp_call1_blk (fx := fx2) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs3 (e_R (x_e rsegs cx))
    (hk_kaddr rsegs cx m + Z.of_nat (hk_d (hk_rest k))) (Z.of_nat nd) (Z.b2z big) (kp_chv mod 2 ^ 64) HJ3).
  - kp_keep1 Hk3 9. exact R9.
  - kp_keep1 Hk3 18. exact R18.
  - kp_keep1 Hk3 10. exact R10.
  - kp_keep1 Hk3 29. exact R29.
  - exact R6'.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - destruct big; cbn; lia.
  - apply Z.mod_pos_bound. lia. }
intros W4 c4 _ HP. destruct HP as (-> & regs4 & mem4 & md4 & -> & HJ4 & Hio4 & Hk4 & Hm4 & (H1_4 & H10_4 & H18_4 & H11_4 & Vb4 & Vc4)).
assert (HM4 : kp_mid cx ly2 S2 W2 regs2 mem2 md2 regs4 mem4 md4)
  by (apply (kp_mid_post cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 regs4 mem4 md4 _ _ HM3 HJ4 Hio4 Hk4
        ltac:(vm_compute; reflexivity) Hm4); intros a Ha; exact Ha).
assert (Hname : getr regs4 (Z_to_bv 5 18) = w64 kp_name) by (rewrite H18_4; unfold w64, kp_name; f_equal; lia).
(* strcmp(name, "phantom") *)
apply (kp_call regs4 mem4 md4 RA_STRCMP1 A_HPH NAME_PHANTOM HM4 H1_4 ltac:(unfold RA_STRCMP1; lia) eq_refl
  ltac:(rewrite H10_4; unfold w64, kp_name; f_equal; lia) H11_4 ltac:(kp_lit) Hc).
intros regs5 mem5 md5 HM5 HP5 Hm5 (v5 & H10_5 & Hv5 & Hiff5).
pose proof (kp_val_step W2 mem4 mem5 _ _ _ Vb4 Hm5 ltac:(lia) ltac:(lia) ltac:(lia)) as Vb5.
pose proof (kp_val_step W2 mem4 mem5 _ _ _ Vc4 Hm5 ltac:(lia) ltac:(lia) ltac:(lia)) as Vc5.
assert (H18_5 : getr regs5 (Z_to_bv 5 18) = w64 kp_name) by (rewrite (HP5 18 ltac:(unfold acallee_saved; lia)); exact Hname).
pose proof HM5 as (HJ5 & _ & Hr5 & _).
eapply SRr_bind.
{ apply (kp_test_ph (fx := fx2) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs5 (e_R (x_e rsegs cx)) v5
    ((e_pp (x_e rsegs cx) + HQ_ENT0) mod 2 ^ 64) (hq_nent r mod 2 ^ 64) HJ5
    ltac:(rewrite (Hr5 9 ltac:(kp_incs)); exact R9) H10_5);
  [lia | lia | exact Hv5 | apply Z.mod_pos_bound; lia | apply Z.mod_pos_bound; lia
  | exact (kp_cell_mid cx ly2 S2 W2 regs2 mem2 md2 regs5 mem5 md5 0xd8 _ HM5 Cd8 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
  | exact (kp_cell_mid cx ly2 S2 W2 regs2 mem2 md2 regs5 mem5 md5 0xe0 _ HM5 Ce0 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))]. }
intros W6 c6 _ [(Hv0 & HP) | (Hv0 & HP)]; destruct HP as (-> & regs6 & mem6 & md6 & -> & HJ6 & Hio6 & Hk6 & Hm6 & Hr6);
  (assert (HM6 : kp_mid cx ly2 S2 W2 regs2 mem2 md2 regs6 mem6 md6)
     by (apply (kp_mid_post cx ly2 S2 W2 regs2 mem2 md2 regs5 mem5 md5 regs6 mem6 md6 _ (fun _ => False) HM5 HJ6 Hio6
           Hk6 ltac:(vm_compute; reflexivity) Hm6); intros a []));
  pose proof (kp_val_eq W2 mem5 mem6 _ _ Vb5 Hm6 ltac:(lia) ltac:(lia)) as Vb6;
  pose proof (kp_val_eq W2 mem5 mem6 _ _ Vc5 Hm6 ltac:(lia) ltac:(lia)) as Vc6.
{ (* the name is "phantom" *)
  destruct Hr6 as (H13_6 & H18_6 & H7_6 & H31_6).
  assert (Hnb : kp_nb = NAME_PHANTOM) by (apply Hiff5; exact Hv0).
  apply (kp_tail_case regs6 mem6 md6 HA_PHANTOM kp_chv HM6).
  - rewrite H31_6, R31. unfold w64. apply Z_to_bv_mod64.
  - rewrite H7_6, R7. unfold w64. apply Z_to_bv_mod64.
  - exact H13_6.
  - exact H18_6.
  - exact Vb6.
  - exact Vc6.
  - exact Hchv.
  - rewrite (kp_key_eq Hc), Hnb, kp_param_ph. reflexivity. }
(* not "phantom": strcmp(name, "pad") *)
destruct Hr6 as (H1_6 & H10_6 & H11_6).
assert (Hnph : kp_nb <> NAME_PHANTOM) by (intros E; apply Hv0; apply Hiff5; exact E).
apply (kp_call regs6 mem6 md6 RA_STRCMP2 A_HPAD NAME_PAD HM6 H1_6 ltac:(unfold RA_STRCMP2; lia) eq_refl
  ltac:(rewrite H10_6; exact H18_5) H11_6 ltac:(kp_lit) Hc).
intros regs7 mem7 md7 HM7 HP7 Hm7 (v7 & H10_7 & Hv7 & Hiff7).
pose proof (kp_val_step W2 mem6 mem7 _ _ _ Vb6 Hm7 ltac:(lia) ltac:(lia) ltac:(lia)) as Vb7.
pose proof (kp_val_step W2 mem6 mem7 _ _ _ Vc6 Hm7 ltac:(lia) ltac:(lia) ltac:(lia)) as Vc7.
assert (H18_7 : getr regs7 (Z_to_bv 5 18) = w64 kp_name)
  by (rewrite (HP7 18 ltac:(unfold acallee_saved; lia)); kp_keep1 Hk6 18; exact H18_5).
pose proof HM7 as (HJ7 & _ & Hr7 & _).
eapply SRr_bind.
{ apply (kp_test_pad (fx := fx2) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs7 (e_R (x_e rsegs cx)) v7
    ((e_pp (x_e rsegs cx) + HQ_ENT0) mod 2 ^ 64) (hq_nent r mod 2 ^ 64) HJ7
    ltac:(rewrite (Hr7 9 ltac:(kp_incs)); exact R9) H10_7);
  [lia | lia | exact Hv7 | apply Z.mod_pos_bound; lia | apply Z.mod_pos_bound; lia
  | exact (kp_cell_mid cx ly2 S2 W2 regs2 mem2 md2 regs7 mem7 md7 0xd8 _ HM7 Cd8 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
  | exact (kp_cell_mid cx ly2 S2 W2 regs2 mem2 md2 regs7 mem7 md7 0xe0 _ HM7 Ce0 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))]. }
intros W8 c8 _ [(Hv1 & HP) | (Hv1 & HP)]; destruct HP as (-> & regs8 & mem8 & md8 & -> & HJ8 & Hio8 & Hk8 & Hm8 & Hr8);
  (assert (HM8 : kp_mid cx ly2 S2 W2 regs2 mem2 md2 regs8 mem8 md8)
     by (apply (kp_mid_post cx ly2 S2 W2 regs2 mem2 md2 regs7 mem7 md7 regs8 mem8 md8 _ (fun _ => False) HM7 HJ8 Hio8
           Hk8 ltac:(vm_compute; reflexivity) Hm8); intros a []));
  pose proof (kp_val_eq W2 mem7 mem8 _ _ Vb7 Hm8 ltac:(lia) ltac:(lia)) as Vb8;
  pose proof (kp_val_eq W2 mem7 mem8 _ _ Vc7 Hm8 ltac:(lia) ltac:(lia)) as Vc8.
{ (* the name is "pad" *)
  destruct Hr8 as (H13_8 & H18_8 & H7_8 & H31_8).
  assert (Hnb : kp_nb = NAME_PAD) by (apply Hiff7; exact Hv1).
  apply (kp_tail_case regs8 mem8 md8 HA_PAD kp_chv HM8).
  - rewrite H31_8, R31. unfold w64. apply Z_to_bv_mod64.
  - rewrite H7_8, R7. unfold w64. apply Z_to_bv_mod64.
  - exact H13_8.
  - exact H18_8.
  - exact Vb8.
  - exact Vc8.
  - exact Hchv.
  - rewrite (kp_key_eq Hc), Hnb, kp_param_pad. reflexivity. }
(* not "pad": strcmp(name, "sens") *)
destruct Hr8 as (H1_8 & H10_8 & H11_8).
assert (Hnpad : kp_nb <> NAME_PAD) by (intros E; apply Hv1; apply Hiff7; exact E).
apply (kp_call regs8 mem8 md8 RA_STRCMP3 A_HSENS NAME_SENS HM8 H1_8 ltac:(unfold RA_STRCMP3; lia) eq_refl
  ltac:(rewrite H10_8; exact H18_7) H11_8 ltac:(kp_lit) Hc).
intros regs9 mem9 md9 HM9 HP9 Hm9 (v9 & H10_9 & Hv9 & Hiff9).
pose proof (kp_val_step W2 mem8 mem9 _ _ _ Vb8 Hm9 ltac:(lia) ltac:(lia) ltac:(lia)) as Vb9.
pose proof (kp_val_step W2 mem8 mem9 _ _ _ Vc8 Hm9 ltac:(lia) ltac:(lia) ltac:(lia)) as Vc9.
pose proof HM9 as (HJ9 & _ & Hr9 & _).
eapply SRr_bind.
{ apply (kp_test_sens (fx := fx2) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs9 (e_R (x_e rsegs cx)) v9
    ((e_pp (x_e rsegs cx) + HQ_ENT0) mod 2 ^ 64) (hq_nent r mod 2 ^ 64) HJ9
    ltac:(rewrite (Hr9 9 ltac:(kp_incs)); exact R9) H10_9);
  [lia | lia | exact Hv9 | apply Z.mod_pos_bound; lia | apply Z.mod_pos_bound; lia
  | exact (kp_cell_mid cx ly2 S2 W2 regs2 mem2 md2 regs9 mem9 md9 0xd8 _ HM9 Cd8 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
  | exact (kp_cell_mid cx ly2 S2 W2 regs2 mem2 md2 regs9 mem9 md9 0xe0 _ HM9 Ce0 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))]. }
intros W10 c10 _ [(Hv2 & HP) | (Hv2 & HP)]; destruct HP as (-> & regs10 & mem10 & md10 & -> & HJ10 & Hio10 & Hk10 & Hm10 & Hr10).
- (* no name: RF with BAD_KEY *)
  assert (HM10 : kp_mid cx ly2 S2 W2 regs2 mem2 md2 regs10 mem10 md10)
    by (apply (kp_mid_post cx ly2 S2 W2 regs2 mem2 md2 regs9 mem9 md9 regs10 mem10 md10 _ (fun _ => False) HM9 HJ10 Hio10
          Hk10 ltac:(vm_compute; reflexivity) Hm10); intros a []).
  destruct Hr10 as (H28_10 & H7_10 & H31_10).
  assert (Hnsens : kp_nb <> NAME_SENS) by (intros E; apply Hv2; apply Hiff9; exact E).
  apply (kp_rf_leaf regs10 mem10 md10 REFUSE_BAD_KEY HM10).
  + rewrite H31_10, R31. unfold w64. apply Z_to_bv_mod64.
  + rewrite H7_10, R7. unfold w64. apply Z_to_bv_mod64.
  + exact H28_10.
  + apply kp_cell_bad. rewrite (kp_key_eq Hc), (kp_param_none kp_nb Hnph Hnpad Hnsens). reflexivity.
  + left; reflexivity.
- (* the name is "sens" *)
  assert (HM10 : kp_mid cx ly2 S2 W2 regs2 mem2 md2 regs10 mem10 md10)
    by (apply (kp_mid_post cx ly2 S2 W2 regs2 mem2 md2 regs9 mem9 md9 regs10 mem10 md10 _ (fun _ => False) HM9 HJ10 Hio10
          Hk10 ltac:(vm_compute; reflexivity) Hm10); intros a []).
  destruct Hr10 as (H13_10 & H18_10 & H7_10 & H31_10).
  assert (Hnb : kp_nb = NAME_SENS) by (apply Hiff9; exact Hv2).
  apply (kp_tail_case regs10 mem10 md10 HA_SENS kp_chv HM10).
  + rewrite H31_10, R31. unfold w64. apply Z_to_bv_mod64.
  + rewrite H7_10, R7. unfold w64. apply Z_to_bv_mod64.
  + exact H13_10.
  + exact H18_10.
  + exact (kp_val_eq W2 mem9 mem10 _ _ Vb9 Hm10 ltac:(lia) ltac:(lia)).
  + exact (kp_val_eq W2 mem9 mem10 _ _ Vc9 Hm10 ltac:(lia) ltac:(lia)).
  + exact Hchv.
  + rewrite (kp_key_eq Hc), Hnb, kp_param_sens. reflexivity.
Qed.

End dot.

(* part 4 of M3c: DOT 0x832b0 -> VAL 0x83364 / RF 0x83460 *)
Theorem hk_P4 : hk_P4_stmt rsegs B MT.
Proof.
unfold hk_P4_stmt. intros cx POST r ev at0 m HS HVAL HRF.
unfold hk_from_DOT. intros fx2 ly2 S2 W2 regs2 mem2 md2 k cs keys rf nd acc big HC.
eapply kp_main; eassumption.
Qed.

End main.

Print Assumptions kp_dot_blk.
Print Assumptions kp_call1_blk.
Print Assumptions kp_test_ph.
Print Assumptions kp_test_pad.
Print Assumptions kp_test_sens.
Print Assumptions kp_tail_blk.
Print Assumptions hk_P4.
