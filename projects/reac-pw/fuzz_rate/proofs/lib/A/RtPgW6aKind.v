(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (entry state, region and fact proofs, the run/branch loop and its leaf) with the caller-journal leaf of lib/A/ACeu.v rfc_A_ok, aview_frame_off of lib/A/AD28.v (as kept_step) and frm_off_img of lib/A/ACeh.v (as frame_not_img) at c8557374ad2e to libreac/fuzz_knock: lib_asan3_0_listing -> knock_asan_listing, AF_asan3_cmpPixel -> AF_asan_reac_knock_step, tcmp_spec / tcmp_post -> tknock_step_specX / kn_post_step of lib/A/APgCSpec.v, cmp_entry / cmp_regions / cmp_facts / ss_cmp / cmp_SH / cmp_extra / EC / CBx / CBspan / pb_cmpPixel -> step_entry / step_regions / step_facts / ss_step / step_SH / step_extra / EK / KBx / KBspan / pb_knock_stepX; constants: TCMP_STK 16 + ESTACK -> T_step_STK 16, shadow-base atom 42 -> 39, GOT shadow slot / shadow-base cell A_OBJ 0 / A_OBJ 12 -> A_OBJ 1 / A_OBJ 7 (lib/Reusable/YC1f.v got_regionP / bcell_regionP / PALib), image bounds only through lib/Reusable/YImgTop.v (knock's 0x10000 .. 0x5f3000); the struct kp lies in a caller frame (cid, pos) of any class, written through awr_byte's in_frames case by In (cid, pos) own. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/reac-pw/fuzz_qdisc/lib/A/QPgCheck.v at 236fd9c95ca (itself made from proofs/libreac/fuzz_knock/lib/A/APgStep.v at origin/ossv/recipes 6ebe35ba632: the save-slot region, its write obligation awr_stk / kwr_stk, the run / keep / leaf chain) with the kit-only plumbing of lib/A/RPgCfgChanges.v at 964efd2f474 (the image's own code table, cfg_wx / cfg_segs_low, kept_run, the leaf into lib/A/RPgCSpec.v's rl_post) for reac-pw/fuzz_role's image A (fuzz_role.asan): it walks check_absent 0x82bb4, check_role 0x82bdc and check_malformed 0x82c04 against rl_check_absent_specX / rl_check_role_specX / rl_check_malformed_specX on the concrete image lib/A/Img0.v rsegs; the entry state carries the registers the contract fixes (a0, a1, and a2 = a1 for check_role) as literals or as the atom they equal, so the engine decides every abort branch itself; qdisc's divisor-constant region, its arithmetic lemmas and its branch splits are dropped. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgCheck.v at 77f59d02b018 for reac-pw/fuzz_rate's
   image A (fuzz_rate.asan): module paths changed; the image is images.Asan's loaded segments instead of a lib/A/Img0
   module; the contracts are lib/A/RtPgCSpec.v's rt_check_absent_specX / rt_check_rate_specX / rt_check_malformed_specX
   (rt_cpre / rt_cpost, the same texts as role's rl_pre / rl_post) at rate's addresses; check_absent's and
   check_malformed's second literal is 0x5a5a5a5a (`lui` + `addiw`) where role's is 0x5a; check_decide (a0 = a1, the
   override a1 := the atom of a0) is added; the code table covers the four functions; the call-cut plumbing of
   proofs/reac-pw/fuzz_role/lib/A/RPgCheckStr.v at 77f59d02b018 (cs_eq, cs_eq_trans, cs_eq_of_pres, cs_eq_of_st_ok,
   sp_of_st_ok, L_ANS, L_ANS_cs, pres_of_cs) is added for the walks with a call. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCheck.v; 270 of its 306 lines of code are new or changed and 254 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6aKind.v at f6a13f6f19c8 for reac-pw/fuzz_rate's
   image A: module paths changed; the image is fuzz_rate.asan (images.Asan); every pc and register is rate's (in.n is
   the register s8 itself instead of the frame cell [R+0xf8], so the entry state has no frame region and the in.n = 0
   arm writes nothing; the shadow offset is s2; the cursor stays in s9; a5 keeps in.n of the kind read; the dispatch
   block writes s6); the post and the chaining are RtPgSteps.v's rts_blk_post / rts_blk_seq / rts_jt_block. *)
(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; addresses measured on the unstripped twin
   0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3, same loaded bytes): the block lemma w6_kind of
   lib/A/RtPgW6aBase.v, 0x812c4 .. the case entry of ent_build's `switch (kind % 10)` (pod.h:279-281, fuzz.h:37-43).
     0x812c4  beqz s8 -> 0x813a0                     in.n = 0: stop at 0x813a0, nothing written
     0x812c8 .. 0x812d4  the shadow check of s9 (NE-SLOW, slow block 0x820dc .. 0x820e4)
     0x812d8  lbu a0,0(s9); a5 := s8; s8 := s8 - 1
     0x812e4 .. 0x812fc  a1 := (b - 10 ((b * 0xcd) >> 11)) & 0xff = b mod 10; a7 := 10
     0x81300  a4 := s9; s9 += 1; a2 := 8; 0x8130c bltu a2,a1 -> 0x81954 (case 9), else 0x81310
     0x81310 .. 0x81330  RtPgSteps.rts_jt_block, chained by rts_blk_seq.
   The engine's entry state: when r = [] the register s8 pinned to the literal 0 and no region; when r = b :: r'
   the one-byte read-only region at the cursor s9 holding b (atom 32), and the fact 1 <= s8 on s8's own atom 24; the
   shadow base is s2 itself (SOff 18 0). The engine follows the check's slow block and leaves one obligation, paid
   from w6_in's range_addressable. Proves no function (kind: segment lemma). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgSteps RtPgW6aBase.
Require OSSVerify.reac_pw.fuzz_rate.images.Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* image A's loaded segments; an abbreviation, so every statement names the image module's own term (as
   RtPgSteps.v) *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.Asan.M.loaded_segments.

(* ======================================== kind % 10 ======================================== *)
(* the engine's a1 at 0x8130c, over the kind byte's atom 32 *)
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
Definition kd_byte : YP09.region := YP09.mkRegion (Some 25%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition kd_G : facts :=
  mkFacts [(18%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (24%nat, mkAF 1 (2 ^ 63) 0); (25%nat, mkAF 1 (2 ^ 47 - 2) 0);
           (32%nat, mkAF 0 255 0)] [] [].
Definition kd_ss1 : sstate := mkSS W6_RET sr_atoms [kd_byte] None kd_G.
Definition kd_Bx : sv := SOff 18 0.
Definition kd_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition kd_extra (b : Z) : list word := [w64 b].
Definition kd_clob : list (bv 5) := [10; 11; 12; 14; 15; 17; 24; 25]%bv.
(* the registers the run to 0x81954 / 0x81310 sets: a0 = b, a1 = b mod 10, a2 = 8, a4 = the kind's address,
   s9 = the cursor after it, s8 = in.n - 1, a5 = in.n, a7 = 10 *)
Definition kd_Rc (b cur nl' : Z) (regs2 : bvmap 5 word) : Prop :=
getr regs2 10 = w64 b /\ getr regs2 11 = w64 (b mod 10) /\ getr regs2 12 = w64 8 /\ getr regs2 14 = w64 cur /\
getr regs2 25 = w64 (cur + 1) /\ getr regs2 24 = w64 nl' /\ getr regs2 15 = w64 (nl' + 1) /\
getr regs2 17 = w64 10.

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
  rts_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc clob R W2 c2 ->
  rts_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc clob' R' W2 c2.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc clob clob' R R' W2 c2 Hi HR
  (ly2 & S2 & regs2 & mem2 & md2 & Ec & HJ & Hr & Hf & Hp & Hio & Hmo & Hm & HR2).
exists ly2, S2, regs2, mem2, md2. split; [exact Ec|]. split; [exact HJ|].
split; [intros r Hr0 Hn; apply Hr; [exact Hr0 | intros X; apply Hn; apply Hi; exact X]|].
split; [exact Hf|]. split; [exact Hp|]. split; [exact Hio|]. split; [exact Hmo|]. split; [exact Hm|].
exact (HR regs2 Hr HR2).
Qed.

(* ---- the case r = []: s8 = 0, `beqz s8` taken, nothing written ---- *)
Lemma kd_nil : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) R F pos,
  w6_ctx B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
  getr regs 24 = w64 0 ->
  SRr rsegs W (cfg_at rsegs W6_RET regs memc mdc)
  (rts_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc W6_D0E [] (fun _ => True)).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos Hctx H24.
pose proof Hctx as (HJ & _).
pose proof rts_wx as Hwx. pose proof rts_segs_low as Hsegs.
assert (HS0 : st_ok rsegs (Ereg regs []) (mkSS W6_RET sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 W6_RET) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - cbn. tauto.
  - split; [exact I | split; exact I]. }
pose proof (st_ok_pin_lit rsegs _ _ _ (24%bv : bv 5) 0 HS0 eq_refl H24) as HS. clear HS0.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
assert (SHOK : sh_ok rsegs kd_Bx [] (Ereg regs []) (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 (Ereg regs []) (Ereg regs [])) by apply env_agree_refl.
unfold cfg_at. change (w64 W6_RET) with (Z_to_bv 64 W6_RET).
aj_run_to_tok w6_tbl_ok HS HJ SHOK kd_span W6_D0E;
[ awr_ok_tac | ].
apply SRr_ret. red. exists lyc, Sc, (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy mdc) mat mdc).
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|].
split; [exact HJ|].
split;
[ eapply (regs_kept_of_st_ok_pins rsegs _ _ ms regs [] (w_H W) _ [((24%bv : bv 5), SLit 0)] HS HAE);
  [ intros rr e Hp; destruct Hp as [Hp|[]]; inversion Hp; subst; cbn [sv_denot]; symmetry; exact H24
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

(* ---- the case r = b :: r': the run to 0x8130c, the branch on b mod 10, the run to its target ---- *)
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
      let e10 := eval vm_compute in (sr_get (ss_regs ssf) (10%bv : bv 5)) in
      let e12 := eval vm_compute in (sr_get (ss_regs ssf) (12%bv : bv 5)) in
      let e14 := eval vm_compute in (sr_get (ss_regs ssf) (14%bv : bv 5)) in
      let e15 := eval vm_compute in (sr_get (ss_regs ssf) (15%bv : bv 5)) in
      let e17 := eval vm_compute in (sr_get (ss_regs ssf) (17%bv : bv 5)) in
      let e24 := eval vm_compute in (sr_get (ss_regs ssf) (24%bv : bv 5)) in
      let e25 := eval vm_compute in (sr_get (ss_regs ssf) (25%bv : bv 5)) in
      change (sr_get (ss_regs ssf) (10%bv : bv 5)) with e10;
      change (sr_get (ss_regs ssf) (11%bv : bv 5)) with kd_a1;
      change (sr_get (ss_regs ssf) (12%bv : bv 5)) with e12;
      change (sr_get (ss_regs ssf) (14%bv : bv 5)) with e14;
      change (sr_get (ss_regs ssf) (15%bv : bv 5)) with e15;
      change (sr_get (ss_regs ssf) (17%bv : bv 5)) with e17;
      change (sr_get (ss_regs ssf) (24%bv : bv 5)) with e24;
      change (sr_get (ss_regs ssf) (25%bv : bv 5)) with e25 end ].

Lemma kd_cons : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) R F pos cur
  (bb : byte) (r' : list byte),
  w6_ctx B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
  getr regs 18 = w64 SHADOW_OFF -> getr regs 25 = w64 cur -> getr regs 24 = w64 (Z.of_nat (length (bb :: r'))) ->
  w6_in W memc R cur (bb :: r') ->
  SRr rsegs W (cfg_at rsegs W6_RET regs memc mdc)
  (rts_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc
    (if bv_unsigned bb mod 10 =? 9 then W6_D9 else JT_PC) kd_clob
    (kd_Rc (bv_unsigned bb) cur (Z.of_nat (length r')))).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur bb r' Hctx H18 H25 H24 Hin.
pose proof Hctx as (HJ & _).
pose proof rts_wx as Hwx. pose proof rts_segs_low as Hsegs.
pose proof (Cursor.byte_range bb) as Hb.
destruct Hin as (Hg & Hra & Hc0 & Hc1 & Hamem & _).
remember (Z.of_nat (length (bb :: r'))) as n eqn:Hneq.
assert (Hn1 : n = 1 + Z.of_nat (length r')) by (rewrite Hneq; cbn [length]; lia).
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamem.
destruct (Hg 0%nat ltac:(cbn [length map]; lia)) as [Hv0 _]. clear Hg.
cbn [nth map Z.of_nat] in Hv0. rewrite Z.add_0_r in Hv0.
remember (bv_unsigned bb) as b eqn:Hbeq.
pose proof (Z.mod_pos_bound b 10 ltac:(lia)) as Hm.
assert (E18 : ew (Ereg regs (kd_extra b)) 18 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact H18).
assert (E24 : ew (Ereg regs (kd_extra b)) 24 = Z_to_bv 64 n)
  by (rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact H24).
assert (E25 : ew (Ereg regs (kd_extra b)) 25 = Z_to_bv 64 cur)
  by (rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact H25).
assert (E32 : ew (Ereg regs (kd_extra b)) 32 = Z_to_bv 64 b) by exact (ew_Ereg_extra regs (kd_extra b) 0).
assert (HS : st_ok rsegs (Ereg regs (kd_extra b)) kd_ss1
  (restrict (w_H W) (mkst regs (Z_to_bv 64 W6_RET) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    unfold region_ok, kd_byte. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E25, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val rsegs _ _ cur 0 1 (SOff 32 0) b);
      [cbn [sv_denot]; rewrite E32, unsigned_lit_small, Z.add_0_r by lia; reflexivity
      | change (2 ^ (8 * Z.of_N 1)) with 256; lia | lia | rewrite Z.add_0_r; exact Hv0].
  - cbn. tauto.
  - assert (HF18 : afact_ok (Ereg regs (kd_extra b)) 18 (mkAF SHADOW_OFF SHADOW_OFF 0)).
    { unfold afact_ok; cbn [af_lo af_hi af_al2]. rewrite E18, unsigned_lit_small by (unfold SHADOW_OFF; lia).
      split; [lia|]. split; [apply Z.mod_1_r | lia]. }
    assert (HF24 : afact_ok (Ereg regs (kd_extra b)) 24 (mkAF 1 (2 ^ 63) 0)).
    { unfold afact_ok; cbn [af_lo af_hi af_al2]. rewrite E24, unsigned_lit_small by lia.
      split; [lia|]. split; [apply Z.mod_1_r | lia]. }
    assert (HF25 : afact_ok (Ereg regs (kd_extra b)) 25 (mkAF 1 (2 ^ 47 - 2) 0)).
    { unfold afact_ok; cbn [af_lo af_hi af_al2]. rewrite E25, unsigned_lit_small by lia.
      split; [lia|]. split; [apply Z.mod_1_r | lia]. }
    assert (HF32 : afact_ok (Ereg regs (kd_extra b)) 32 (mkAF 0 255 0)).
    { unfold afact_ok; cbn [af_lo af_hi af_al2]. rewrite E32, unsigned_lit_small by lia.
      split; [lia|]. split; [apply Z.mod_1_r | lia]. }
    exact (conj (conj HF18 (conj HF24 (conj HF25 (conj HF32 I)))) (conj I I)). }
assert (SHOK : sh_ok rsegs kd_Bx [] (Ereg regs (kd_extra b)) (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 33 (Ereg regs (kd_extra b)) (Ereg regs (kd_extra b))) by apply env_agree_refl.
unfold cfg_at. change (w64 W6_RET) with (Z_to_bv 64 W6_RET).
aj_run_to_tok w6_tbl_ok HS HJ SHOK kd_span JT_PC.
{ eapply obl_of_range; [exact Hra | | |].
  - unfold kd_Bx. apply (U_atom _ 18 SHADOW_OFF E18). unfold SHADOW_OFF. lia.
  - rewrite (U_atom _ 25 cur E25) by lia. lia.
  - rewrite (U_atom _ 25 cur E25) by lia. lia. }
{ awr_ok_tac. }
rename HFr into HFr1.
lazymatch type of HS with st_ok _ ?E1 _ _ =>
  assert (HAE1 : env_agree 33 (Ereg regs (kd_extra b)) E1) by env_agree_chain HAE end.
pose proof HAE1 as [HA1 _].
assert (E32' : forall E', (forall i, (i < 33)%nat -> ew E' i = ew (Ereg regs (kd_extra b)) i) ->
  ew E' 32 = Z_to_bv 64 b) by (intros E' HE'; rewrite (HE' 32%nat) by lia; exact E32).
srr_branch_tok w6_tbl_ok HS SHOK kd_span.
- fold kd_a1 in Hc. rewrite branch_ltu_U in Hc. unfold U in Hc.
  rewrite (kd_a1_mod _ b (E32' _ HA1) ltac:(lia)) in Hc. cbn [sv_denot] in Hc.
  rewrite !unsigned_lit_small in Hc by lia.
  apply Z.ltb_lt in Hc.
  assert (Hm9 : b mod 10 = 9) by lia. rewrite (proj2 (Z.eqb_eq _ _) Hm9).
  aj_run_to_tok w6_tbl_ok HS HJ SHOK kd_span W6_D9.
  { awr_ok_tac. }
  lazymatch type of HS with st_ok _ ?E2 _ (restrict _ ?ms2) =>
    assert (HAE2 : env_agree 33 (Ereg regs (kd_extra b)) E2) by env_agree_chain HAE;
    assert (HAE2' : env_agree 32 (Ereg regs (kd_extra b)) E2) by (eapply env_agree_le; [|exact HAE2]; lia);
    pose proof HAE2 as [HA2 _];
    kd_finish ms2 HS HJ HAE2' HFr1 HFr lyc Sc regs W end.
  split; [cbn [sv_denot]; rewrite (HA2 32%nat) by lia; rewrite E32, unsigned_lit_small by lia; unfold w64; f_equal; lia|].
  split; [exact (kd_a1_mod _ b (E32' _ HA2) ltac:(lia))|].
  split; [reflexivity|].
  cbn [sv_denot]. rewrite (HA2 24%nat), (HA2 25%nat) by lia. rewrite E24, E25, !unsigned_lit_small by lia.
  unfold w64. split; [f_equal; lia|]. split; [f_equal; lia|]. split; [f_equal; lia|]. split; [f_equal; lia | reflexivity].
- fold kd_a1 in Hc. rewrite branch_ltu_U in Hc. unfold U in Hc.
  rewrite (kd_a1_mod _ b (E32' _ HA1) ltac:(lia)) in Hc. cbn [sv_denot] in Hc.
  rewrite !unsigned_lit_small in Hc by lia.
  apply Z.ltb_ge in Hc.
  assert (Hm9 : b mod 10 <> 9) by lia. rewrite (proj2 (Z.eqb_neq _ _) Hm9).
  aj_run_to_tok w6_tbl_ok HS HJ SHOK kd_span JT_PC.
  { awr_ok_tac. }
  lazymatch type of HS with st_ok _ ?E2 _ (restrict _ ?ms2) =>
    assert (HAE2 : env_agree 33 (Ereg regs (kd_extra b)) E2) by env_agree_chain HAE;
    assert (HAE2' : env_agree 32 (Ereg regs (kd_extra b)) E2) by (eapply env_agree_le; [|exact HAE2]; lia);
    pose proof HAE2 as [HA2 _];
    kd_finish ms2 HS HJ HAE2' HFr1 HFr lyc Sc regs W end.
  split; [cbn [sv_denot]; rewrite (HA2 32%nat) by lia; rewrite E32, unsigned_lit_small by lia; unfold w64; f_equal; lia|].
  split; [exact (kd_a1_mod _ b (E32' _ HA2) ltac:(lia))|].
  split; [reflexivity|].
  cbn [sv_denot]. rewrite (HA2 24%nat), (HA2 25%nat) by lia. rewrite E24, E25, !unsigned_lit_small by lia.
  unfold w64. split; [f_equal; lia|]. split; [f_equal; lia|]. split; [f_equal; lia|]. split; [f_equal; lia | reflexivity].
Qed.

(* ======================================== the theorem ======================================== *)
Theorem w6_kind : w6_kind_stmt B MT.
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur r Hctx H18 H25 H24 Hin.
destruct r as [|bb r'].
- eapply SRr_mono; [exact (kd_nil STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos Hctx H24)|].
  intros W2 c2 _ HP. left. split; [reflexivity | exact HP].
- assert (Hrom : rom_view rsegs W memc) by (destruct Hctx as (_ & _ & _ & _ & _ & _ & X); exact X).
  pose proof (kd_cons STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur bb r'
    Hctx H18 H25 H24 Hin) as H1.
  pose proof (Cursor.byte_range bb) as Hb.
  remember (bv_unsigned bb) as b eqn:Hbeq.
  remember (Z.of_nat (length r')) as nl eqn:Hnl.
  pose proof (Z.mod_pos_bound b 10 ltac:(lia)) as Hm.
  eapply SRr_mono; [| intros W2 c2 _ HP; right; exists bb, r'; split; [reflexivity | rewrite <- Hbeq, <- Hnl; exact HP]].
  unfold w6_case_pc, w6_kind_clob.
  destruct (Z.eqb_spec (b mod 10) 9) as [E9|E9].
  + eapply SRr_mono; [exact H1|]. intros W2 c2 _ HP.
    apply kd_blk_post_mono with (clob := kd_clob) (R := kd_Rc b cur nl); [apply incl_refl | | exact HP].
    intros regs2 _ (R10 & R11 & R12 & R14 & R25 & R24 & R15 & R17).
    unfold w6_kind_R. rewrite (proj2 (Z.eqb_eq _ _) E9). rewrite E9 in R11.
    repeat split; assumption.
  + eapply SRr_mono.
    * eapply (rts_blk_seq B MT MTL STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc W6_RET JT_PC
        (jt_tgt (b mod 10)) kd_clob [10; 11; 12; 22]%bv (kd_Rc b cur nl) (w6_kind_R b cur nl)).
      { exact H1. }
      intros W1 ly1 S1 regs1 mem1 md1 Hw1 HJ1 Hr1 Hf1 Hp1 Hio1 Hmo1 Hm1 (R10 & R11 & R12 & R14 & R25 & R24 & R15 & R17).
      assert (Hrom1 : rom_view rsegs W1 mem1) by (intros a Ha; rewrite Hm1; exact (Hrom a Ha)).
      eapply SRr_mono;
        [exact (rts_jt_block B MT MTL LAWS STK sp0 FP ly S W0 mem0 md0 own ly1 S1 W1 mem1 md1 k regs1 (b mod 10)
                  HJ1 ltac:(lia) R11 Hrom1)|].
      intros W2 c2 _ HP.
      apply kd_blk_post_mono with (clob := [10; 11; 12; 22]%bv) (R := jt_R (b mod 10) regs1);
        [apply incl_refl | | exact HP].
      intros regs2 Hk (J11 & J12 & J10 & J22).
      rewrite R10 in J10, J22. unfold w64 in J10, J22. rewrite unsigned_lit_small in J10, J22 by lia.
      rewrite (Z.mod_small b 256) in J22 by lia.
      unfold w6_kind_R. rewrite (proj2 (Z.eqb_neq _ _) E9).
      rewrite !Hk by (cbv; first [discriminate | intros [X|[X|[X|[X|[]]]]]; discriminate X]).
      repeat split; assumption.
    * intros W2 c2 _ HP. cbv beta iota.
      apply kd_blk_post_mono with (clob := kd_clob ++ [10; 11; 12; 22]%bv) (R := w6_kind_R b cur nl);
        [| intros regs2 _ X; exact X | exact HP].
      intros x Hx. apply in_app_or in Hx. cbn [kd_clob In] in Hx |- *. tauto.
Qed.

End d.
End b.

Print Assumptions w6_kind.
