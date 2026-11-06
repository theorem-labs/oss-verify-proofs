(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of proofs/reac-pw/fuzz_role/lib/A/RPgX01.v at 9bffaa83ff88
   [Apache-2.0] (rx_reg_atom / rx_reg_ext / rx_ew_reg / rx_st_region / rx_chunk_zero / rx_flag0_of, the saved-slot
   chunk list rx_sv_chunks, the numeral tactics z5 / z5g and the flag-store tactic rx_run_flag, which passes
   aj_flag_store its sixteen journal arguments) and of proofs/reac-pw/fuzz_role/lib/A/RPgCheck.v at 77f59d02b018
   [Apache-2.0] (the shape of a `ret` leaf into a callee post), for reac-pw/fuzz_rate's image A: the walk is
   check_csv's release and epilogue, the side-stack class is 2 instead of 3, and the post is RtPgCSpec.rt_cpost_o,
   whose owned-set conjunct is discharged from the cut's layout, chunk and frame equalities. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCcsvS3.v, with its module names changed; 277 of its 306 lines of code are new or changed and 297 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6aKind.v at f6a13f6f19c8 for reac-pw/fuzz_rate's
   image A: module paths changed; the image is fuzz_rate.asan (images.Asan); every pc and register is rate's (in.n is
   the register s8 itself instead of the frame cell [R+0xf8], so the entry state has no frame region and the in.n = 0
   arm writes nothing; the shadow offset is s2; the cursor stays in s9; a5 keeps in.n of the kind read; the dispatch
   block writes s6); the post and the chaining are RtPgSteps.v's rts_blk_post / rts_blk_seq / rts_jt_block. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW6aKind.v at 88912827c774 for the same unit's
   image B (fuzz_rate.asan-ubsan): images.AsanUbsan, lib/AU/RtPgW6aBaseB.v and lib/AU/RtPgStepsB.v (rtsb_blk_post /
   rtsb_blk_seq / rtsb_jt_block) instead of image A's files; every pc is image B's; in.n is s9, the cursor s10 and the
   shadow offset s4; the run passes the pointer-overflow test `bltu a6,s2` 0x813f4 (decided by the engine from the
   cursor atom's range); kind % 10 ends with `subw` / `zext.b` (the engine's range test makes the `subw` a 64-bit
   subtraction, so a1's sv is A's); the kind block writes s2, a6, t1 and s6 and keeps s10; one clobber list for
   both outcomes. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; addresses measured on the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1, same loaded bytes): the block lemma w6b_kind of
   lib/AU/RtPgW6aBaseB.v, 0x813e8 .. the case entry of ent_build's `switch (kind % 10)` (pod.h:279-281, fuzz.h:37-43).
     0x813e8  beqz s9 -> 0x814d0                     in.n = 0: stop at 0x814d0, nothing written
     0x813ec  s2 := s10 + 1; a6 := 1; 0x813f4 bltu a6,s2 -> 0x813fc (the other arm 0x813f8 `j 0x83098` is never
              taken: the cursor atom lies in [1, 2^47 - 2], so s2 >= 2)
     0x813fc  t1 := s9; 0x81400 .. 0x8140c the instrumented check of s10 (slow block 0x8221c .. 0x82224)
     0x81410  lbu a0,0(s10); 0x81414 .. 0x8142c a1 := kind % 10 (205 multiply, `srli 11`, `subw`, `zext.b`)
     0x81430  s6 := t1 - 1; a2 := 8; 0x81438 bltu a2,a1 -> 0x81a94 (case 9), else 0x8143c
     0x8143c .. 0x8145c  RtPgStepsB.rtsb_jt_block, chained by rtsb_blk_seq.
   The engine's entry state: when r = [] the register s9 pinned to the literal 0 and no region; when r = b :: r'
   the one-byte read-only region at the cursor s10 holding b (atom 32), the fact 1 <= s9 on s9's own atom 25 and the
   cursor atom 26 in [1, 2^47 - 2] (closed numerals); the shadow base is s4 itself (SOff 20 0). The engine follows
   the check's slow block and leaves one obligation, paid from w6b_in's range_addressable. Proves no function (kind:
   segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Cursor Tables.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgStepsB RtPgW6aBaseB.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* image B's loaded segments; an abbreviation, so every statement names the image module's own term (as
   RtPgStepsB.v) *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

(* ======================================== kind % 10 ======================================== *)
(* the engine's a1 at 0x81438, over the kind byte's atom 32 (the `subw` 0x81428 is a 64-bit subtraction for the
   engine: YP0e's aluw_is_alu finds the difference of the operands' ranges within 32 bits, so the sv is A's) *)
Definition kd_a1 : sv :=
  SAlu ALU_AND
    (SAlu ALU_SUB (SOff 32 0)
       (SMd M_MUL (SAlu ALU_SRL (SMd M_MUL (SOff 32 0) (SLit 205)) (SLit 11)) (SLit 10)))
    (SLit 255).
Definition kd_env (b : Z) : env := mkEnv (fun _ => Z_to_bv 64 b) (fun _ => []).
Lemma kd_all256 : forall (P : Z -> bool), forallb P (map Z.of_nat (seq 0 256)) = true ->
  forall c, 0 <= c < 256 -> P c = true.
Proof.
intros P H c Hc. rewrite forallb_forall in H. apply H. apply in_map_iff. exists (Z.to_nat c).
split; [lia|]. apply in_seq. lia.
Qed.
Lemma kd_a1_env : forall E b, ew E 32 = Z_to_bv 64 b -> sv_denot E kd_a1 = sv_denot (kd_env b) kd_a1.
Proof. intros E b H. unfold kd_a1. cbn [sv_denot]. rewrite H. reflexivity. Qed.
Lemma kd_a1_mod : forall E b, ew E 32 = Z_to_bv 64 b -> 0 <= b < 256 -> sv_denot E kd_a1 = Z_to_bv 64 (b mod 10).
Proof.
intros E b H Hb. rewrite (kd_a1_env E b H). apply bv_eq. apply Z.eqb_eq.
exact (kd_all256 (fun b => bv_unsigned (sv_denot (kd_env b) kd_a1) =? bv_unsigned (Z_to_bv 64 (b mod 10)))
  ltac:(vm_compute; reflexivity) b Hb).
Qed.

(* ======================================== the entry states ======================================== *)
Definition kd_byte : YP09.region := YP09.mkRegion (Some 26%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
(* closed numerals: s4 = SHADOW_OFF, in.n in [1, 2^63], the cursor in [1, 2^47 - 2], the kind byte in [0, 255] *)
Definition kd_G : facts :=
  mkFacts [(20%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (25%nat, mkAF 1 9223372036854775808 0);
           (26%nat, mkAF 1 140737488355326 0); (32%nat, mkAF 0 255 0)] [] [].
Definition kd_ss1 : sstate := mkSS W6B_RET sr_atoms [kd_byte] None kd_G.
Definition kd_Bx : sv := SOff 20 0.
Definition kd_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition kd_extra (b : Z) : list word := [w64 b].
Definition kd_clob : list (bv 5) := [6; 10; 11; 12; 16; 18; 22]%bv.
(* the registers the run to 0x81a94 / 0x8143c sets: a0 = b, a1 = b mod 10, a2 = 8, s2 = the cursor after the kind
   byte, a6 = 1, t1 = in.n, s6 = in.n - 1 *)
Definition kd_Rc (b cur nl' : Z) (regs2 : bvmap 5 word) : Prop :=
getr regs2 10 = w64 b /\ getr regs2 11 = w64 (b mod 10) /\ getr regs2 12 = w64 8 /\
getr regs2 18 = w64 (cur + 1) /\ getr regs2 16 = w64 1 /\ getr regs2 6 = w64 (nl' + 1) /\
getr regs2 22 = w64 nl'.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.

(* a block post with fewer clobbered registers and a stronger R is a block post *)
Lemma kd_blk_post_mono : forall STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc clob clob'
  (R R' : bvmap 5 word -> Prop) W2 c2,
  incl clob clob' ->
  (forall regs2, (forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob -> getr regs2 r = getr regs r) -> R regs2 -> R' regs2) ->
  rtsb_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc clob R W2 c2 ->
  rtsb_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc clob' R' W2 c2.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc clob clob' R R' W2 c2 Hi HR
  (ly2 & S2 & regs2 & mem2 & md2 & Ec & HJ & Hr & Hf & Hp & Hio & Hmo & Hm & HR2).
exists ly2, S2, regs2, mem2, md2. split; [exact Ec|]. split; [exact HJ|].
split; [intros r Hr0 Hn; apply Hr; [exact Hr0 | intros X; apply Hn; apply Hi; exact X]|].
split; [exact Hf|]. split; [exact Hp|]. split; [exact Hio|]. split; [exact Hmo|]. split; [exact Hm|].
exact (HR regs2 Hr HR2).
Qed.

(* ---- the case r = []: s9 = 0, `beqz s9` taken, nothing written ---- *)
Lemma kd_nil : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) R F pos,
  w6b_ctx B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
  getr regs 25 = w64 0 ->
  SRr rsegs W (cfg_at rsegs W6B_RET regs memc mdc)
  (rtsb_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc W6B_D0E [] (fun _ => True)).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos Hctx H25.
pose proof Hctx as (HJ & _).
pose proof rtsb_wx as Hwx. pose proof rtsb_segs_low as Hsegs.
assert (HS0 : st_ok rsegs (Ereg regs []) (mkSS W6B_RET sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 W6B_RET) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - cbn. tauto.
  - split; [exact I | split; exact I]. }
pose proof (st_ok_pin_lit rsegs _ _ _ (25%bv : bv 5) 0 HS0 eq_refl H25) as HS. clear HS0.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
assert (SHOK : sh_ok rsegs kd_Bx [] (Ereg regs []) (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 (Ereg regs []) (Ereg regs [])) by apply env_agree_refl.
unfold cfg_at. change (w64 W6B_RET) with (Z_to_bv 64 W6B_RET).
aj_run_to_tok w6b_tbl_ok HS HJ SHOK kd_span W6B_D0E;
[ awr_ok_tac | ].
apply SRr_ret. red. exists lyc, Sc, (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy mdc) mat mdc).
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|].
split; [exact HJ|].
split;
[ eapply (regs_kept_of_st_ok_pins rsegs _ _ ms regs [] (w_H W) _ [((25%bv : bv 5), SLit 0)] HS HAE);
  [ intros rr e Hp; destruct Hp as [Hp|[]]; inversion Hp; subst; cbn [sv_denot]; symmetry; exact H25
  | vm_compute; reflexivity ]
|].
split; [reflexivity|].
split; [apply Permutation_refl|].
split; [apply same_io_wvb|].
split; [apply mo_le_refl; assumption|].
split; [|exact I].
intros a; unfold aview, mbyte; rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
intros (rr & Hin & Hr); simpl in Hin; destruct Hin.
Qed.

(* ---- the case r = b :: r': the run to 0x81438, the branch on b mod 10, the run to its target ---- *)
Ltac kd_finish ms2 HS HJ HAE2 HFr1 HFr lyc Sc regs W :=
  apply SRr_ret;
  lazymatch goal with |- _ (mkCfg ms2 ?md2) => red; exists lyc, Sc, (ms_regs ms2), (ms_mem ms2), md2 end;
  split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms2 HS eq_refl) at 1; reflexivity|];
  split; [exact HJ|];
  split; [eapply (regs_kept_of_st_ok rsegs _ _ ms2 regs _ (w_H W) _ HS HAE2); vm_compute; reflexivity|];
  split; [reflexivity|];
  split; [apply Permutation_refl|];
  split; [let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio|];
  split; [apply mo_le_refl; assumption|];
  split;
  [ let a := fresh "a" in
    intros a; unfold aview, mbyte; rewrite (HFr (Z_to_bv 64 a)); [rewrite (HFr1 (Z_to_bv 64 a)); [reflexivity|]|];
    let rr := fresh "rr" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
    intros (rr & Hin & Hr); cbv [In ss_mem add_cond kd_ss1] in Hin; destruct Hin as [<-|[]]; cbn in Hr; lia
  | unfold kd_Rc; rewrite !(st_ok_restrict_reg rsegs (w_H W) _ _ ms2 _ HS);
    lazymatch type of HS with st_ok _ _ ?ssf _ =>
      let e6 := eval vm_compute in (sr_get (ss_regs ssf) (6%bv : bv 5)) in
      let e10 := eval vm_compute in (sr_get (ss_regs ssf) (10%bv : bv 5)) in
      let e12 := eval vm_compute in (sr_get (ss_regs ssf) (12%bv : bv 5)) in
      let e16 := eval vm_compute in (sr_get (ss_regs ssf) (16%bv : bv 5)) in
      let e18 := eval vm_compute in (sr_get (ss_regs ssf) (18%bv : bv 5)) in
      let e22 := eval vm_compute in (sr_get (ss_regs ssf) (22%bv : bv 5)) in
      change (sr_get (ss_regs ssf) (6%bv : bv 5)) with e6;
      change (sr_get (ss_regs ssf) (10%bv : bv 5)) with e10;
      change (sr_get (ss_regs ssf) (11%bv : bv 5)) with kd_a1;
      change (sr_get (ss_regs ssf) (12%bv : bv 5)) with e12;
      change (sr_get (ss_regs ssf) (16%bv : bv 5)) with e16;
      change (sr_get (ss_regs ssf) (18%bv : bv 5)) with e18;
      change (sr_get (ss_regs ssf) (22%bv : bv 5)) with e22 end ].

(* the seven register values of kd_Rc, from the entry atoms *)
Ltac kd_regs b HA2 E32 E25 E26 E32' :=
  split; [cbn [sv_denot]; rewrite (HA2 32%nat) by lia; rewrite E32, unsigned_lit_small by lia; unfold w64; f_equal; lia|];
  split; [exact (kd_a1_mod _ b (E32' _ HA2) ltac:(lia))|];
  split; [reflexivity|];
  split; [cbn [sv_denot]; rewrite (HA2 26%nat) by lia; rewrite E26, unsigned_lit_small by lia; unfold w64; f_equal; lia|];
  split; [reflexivity|];
  split; [cbn [sv_denot]; rewrite (HA2 25%nat) by lia; rewrite E25, unsigned_lit_small by lia; unfold w64; f_equal; lia|];
  cbn [sv_denot]; rewrite (HA2 25%nat) by lia; rewrite E25, unsigned_lit_small by lia; unfold w64; f_equal; lia.

Lemma kd_cons : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) R F pos cur
  (bb : byte) (r' : list byte),
  w6b_ctx B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
  getr regs 20 = w64 SHADOW_OFF -> getr regs 26 = w64 cur -> getr regs 25 = w64 (Z.of_nat (length (bb :: r'))) ->
  w6b_in W memc R cur (bb :: r') ->
  SRr rsegs W (cfg_at rsegs W6B_RET regs memc mdc)
  (rtsb_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc
    (if bv_unsigned bb mod 10 =? 9 then W6B_D9 else JTB_PC) kd_clob
    (kd_Rc (bv_unsigned bb) cur (Z.of_nat (length r')))).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur bb r' Hctx H20 H26 H25 Hin.
pose proof Hctx as (HJ & _).
pose proof rtsb_wx as Hwx. pose proof rtsb_segs_low as Hsegs.
pose proof (Cursor.byte_range bb) as Hb.
destruct Hin as (Hg & Hra & Hc0 & Hc1 & Hamem & _).
remember (Z.of_nat (length (bb :: r'))) as n eqn:Hneq.
assert (Hn1 : n = 1 + Z.of_nat (length r')) by (rewrite Hneq; cbn [length]; lia).
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamem.
destruct (Hg 0%nat ltac:(cbn [length map]; lia)) as [Hv0 _]. clear Hg.
cbn [nth map Z.of_nat] in Hv0. rewrite Z.add_0_r in Hv0.
remember (bv_unsigned bb) as b eqn:Hbeq.
pose proof (Z.mod_pos_bound b 10 ltac:(lia)) as Hm.
assert (E20 : ew (Ereg regs (kd_extra b)) 20 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl); exact H20).
assert (E25 : ew (Ereg regs (kd_extra b)) 25 = Z_to_bv 64 n)
  by (rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact H25).
assert (E26 : ew (Ereg regs (kd_extra b)) 26 = Z_to_bv 64 cur)
  by (rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact H26).
assert (E32 : ew (Ereg regs (kd_extra b)) 32 = Z_to_bv 64 b) by exact (ew_Ereg_extra regs (kd_extra b) 0).
assert (HS : st_ok rsegs (Ereg regs (kd_extra b)) kd_ss1
  (restrict (w_H W) (mkst regs (Z_to_bv 64 W6B_RET) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    unfold region_ok, kd_byte. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E26, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val rsegs _ _ cur 0 1 (SOff 32 0) b);
      [cbn [sv_denot]; rewrite E32, unsigned_lit_small, Z.add_0_r by lia; reflexivity
      | change (2 ^ (8 * Z.of_N 1)) with 256; lia | lia | rewrite Z.add_0_r; exact Hv0].
  - cbn. tauto.
  - assert (HF20 : afact_ok (Ereg regs (kd_extra b)) 20 (mkAF SHADOW_OFF SHADOW_OFF 0)).
    { unfold afact_ok; cbn [af_lo af_hi af_al2]. rewrite E20, unsigned_lit_small by (unfold SHADOW_OFF; lia).
      split; [lia|]. split; [apply Z.mod_1_r | lia]. }
    assert (HF25 : afact_ok (Ereg regs (kd_extra b)) 25 (mkAF 1 9223372036854775808 0)).
    { unfold afact_ok; cbn [af_lo af_hi af_al2]. rewrite E25, unsigned_lit_small by lia.
      split; [lia|]. split; [apply Z.mod_1_r | lia]. }
    assert (HF26 : afact_ok (Ereg regs (kd_extra b)) 26 (mkAF 1 140737488355326 0)).
    { unfold afact_ok; cbn [af_lo af_hi af_al2]. rewrite E26, unsigned_lit_small by lia.
      split; [lia|]. split; [apply Z.mod_1_r | lia]. }
    assert (HF32 : afact_ok (Ereg regs (kd_extra b)) 32 (mkAF 0 255 0)).
    { unfold afact_ok; cbn [af_lo af_hi af_al2]. rewrite E32, unsigned_lit_small by lia.
      split; [lia|]. split; [apply Z.mod_1_r | lia]. }
    exact (conj (conj HF20 (conj HF25 (conj HF26 (conj HF32 I)))) (conj I I)). }
assert (SHOK : sh_ok rsegs kd_Bx [] (Ereg regs (kd_extra b)) (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 33 (Ereg regs (kd_extra b)) (Ereg regs (kd_extra b))) by apply env_agree_refl.
unfold cfg_at. change (w64 W6B_RET) with (Z_to_bv 64 W6B_RET).
aj_run_to_tok w6b_tbl_ok HS HJ SHOK kd_span JTB_PC.
{ eapply obl_of_range; [exact Hra | | |].
  - unfold kd_Bx. apply (U_atom _ 20 SHADOW_OFF E20). unfold SHADOW_OFF. lia.
  - rewrite (U_atom _ 26 cur E26) by lia. lia.
  - rewrite (U_atom _ 26 cur E26) by lia. lia. }
{ awr_ok_tac. }
rename HFr into HFr1.
lazymatch type of HS with st_ok _ ?E1 _ _ =>
  assert (HAE1 : env_agree 33 (Ereg regs (kd_extra b)) E1) by env_agree_chain HAE end.
pose proof HAE1 as [HA1 _].
assert (E32' : forall E', (forall i, (i < 33)%nat -> ew E' i = ew (Ereg regs (kd_extra b)) i) ->
  ew E' 32 = Z_to_bv 64 b) by (intros E' HE'; rewrite (HE' 32%nat) by lia; exact E32).
srr_branch_tok w6b_tbl_ok HS SHOK kd_span.
- fold kd_a1 in Hc. rewrite branch_ltu_U in Hc. unfold U in Hc.
  rewrite (kd_a1_mod _ b (E32' _ HA1) ltac:(lia)) in Hc. cbn [sv_denot] in Hc.
  rewrite !unsigned_lit_small in Hc by lia.
  apply Z.ltb_lt in Hc.
  assert (Hm9 : b mod 10 = 9) by lia. rewrite (proj2 (Z.eqb_eq _ _) Hm9).
  aj_run_to_tok w6b_tbl_ok HS HJ SHOK kd_span W6B_D9.
  { awr_ok_tac. }
  lazymatch type of HS with st_ok _ ?E2 _ (restrict _ ?ms2) =>
    assert (HAE2 : env_agree 33 (Ereg regs (kd_extra b)) E2) by env_agree_chain HAE;
    assert (HAE2' : env_agree 32 (Ereg regs (kd_extra b)) E2) by (eapply env_agree_le; [|exact HAE2]; lia);
    pose proof HAE2 as [HA2 _];
    kd_finish ms2 HS HJ HAE2' HFr1 HFr lyc Sc regs W end.
  kd_regs b HA2 E32 E25 E26 E32'.
- fold kd_a1 in Hc. rewrite branch_ltu_U in Hc. unfold U in Hc.
  rewrite (kd_a1_mod _ b (E32' _ HA1) ltac:(lia)) in Hc. cbn [sv_denot] in Hc.
  rewrite !unsigned_lit_small in Hc by lia.
  apply Z.ltb_ge in Hc.
  assert (Hm9 : b mod 10 <> 9) by lia. rewrite (proj2 (Z.eqb_neq _ _) Hm9).
  aj_run_to_tok w6b_tbl_ok HS HJ SHOK kd_span JTB_PC.
  { awr_ok_tac. }
  lazymatch type of HS with st_ok _ ?E2 _ (restrict _ ?ms2) =>
    assert (HAE2 : env_agree 33 (Ereg regs (kd_extra b)) E2) by env_agree_chain HAE;
    assert (HAE2' : env_agree 32 (Ereg regs (kd_extra b)) E2) by (eapply env_agree_le; [|exact HAE2]; lia);
    pose proof HAE2 as [HA2 _];
    kd_finish ms2 HS HJ HAE2' HFr1 HFr lyc Sc regs W end.
  kd_regs b HA2 E32 E25 E26 E32'.
Qed.

(* ======================================== the theorem ======================================== *)
Theorem w6b_kind : w6b_kind_stmt B MT.
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur r Hctx H20 H26 H25 Hin.
destruct r as [|bb r'].
- eapply SRr_mono; [exact (kd_nil STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos Hctx H25)|].
  intros W2 c2 _ HP. left. split; [reflexivity | exact HP].
- assert (Hrom : rom_view rsegs W memc) by (destruct Hctx as (_ & _ & _ & _ & _ & _ & X); exact X).
  pose proof (kd_cons STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur bb r'
    Hctx H20 H26 H25 Hin) as H1.
  pose proof (Cursor.byte_range bb) as Hb.
  remember (bv_unsigned bb) as b eqn:Hbeq.
  remember (Z.of_nat (length r')) as nl eqn:Hnl.
  pose proof (Z.mod_pos_bound b 10 ltac:(lia)) as Hm.
  eapply SRr_mono; [| intros W2 c2 _ HP; right; exists bb, r'; split; [reflexivity | rewrite <- Hbeq, <- Hnl; exact HP]].
  unfold w6b_case_pc.
  destruct (Z.eqb_spec (b mod 10) 9) as [E9|E9].
  + eapply SRr_mono; [exact H1|]. intros W2 c2 _ HP.
    apply kd_blk_post_mono with (clob := kd_clob) (R := kd_Rc b cur nl);
      [intros x Hx; cbv [kd_clob w6b_kind_clob In] in Hx |- *; tauto | | exact HP].
    intros regs2 _ (R10 & R11 & R12 & R18 & R16 & R6 & R22).
    unfold w6b_kind_R. rewrite (proj2 (Z.eqb_eq _ _) E9).
    repeat split; assumption.
  + eapply SRr_mono.
    * eapply (rtsb_blk_seq B MT MTL STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc W6B_RET JTB_PC
        (jtb_tgt (b mod 10)) kd_clob [10; 11; 12; 13]%bv (kd_Rc b cur nl) (w6b_kind_R b cur nl)).
      { exact H1. }
      intros W1 ly1 S1 regs1 mem1 md1 Hw1 HJ1 Hr1 Hf1 Hp1 Hio1 Hmo1 Hm1 (R10 & R11 & R12 & R18 & R16 & R6 & R22).
      assert (Hrom1 : rom_view rsegs W1 mem1) by (intros a Ha; rewrite Hm1; exact (Hrom a Ha)).
      eapply SRr_mono;
        [exact (rtsb_jt_block B MT MTL LAWS STK sp0 FP ly S W0 mem0 md0 own ly1 S1 W1 mem1 md1 k regs1 (b mod 10)
                  HJ1 ltac:(lia) R11 Hrom1)|].
      intros W2 c2 _ HP.
      apply kd_blk_post_mono with (clob := [10; 11; 12; 13]%bv) (R := jtb_R (b mod 10) regs1);
        [apply incl_refl | | exact HP].
      intros regs2 Hk (J11 & J12 & J10 & J13).
      rewrite R10 in J10, J13. unfold w64 in J10, J13. rewrite unsigned_lit_small in J10, J13 by lia.
      rewrite (Z.mod_small b 256) in J13 by lia.
      unfold w6b_kind_R. rewrite (proj2 (Z.eqb_neq _ _) E9).
      rewrite !Hk by (cbv; first [discriminate | intros [X|[X|[X|[X|[]]]]]; discriminate X]).
      repeat split; assumption.
    * intros W2 c2 _ HP. cbv beta iota.
      apply kd_blk_post_mono with (clob := kd_clob ++ [10; 11; 12; 13]%bv) (R := w6b_kind_R b cur nl);
        [| intros regs2 _ X; exact X | exact HP].
      intros x Hx. apply in_app_or in Hx. cbv [kd_clob w6b_kind_clob In] in Hx |- *. tauto.
Qed.

End d.
End b.

Print Assumptions w6b_kind.
