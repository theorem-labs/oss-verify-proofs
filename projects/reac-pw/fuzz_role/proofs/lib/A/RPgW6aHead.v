(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/Reusable/YCbq.v aj_intrin_at (lines 2155-2206) restated as w7_memcpy_at for image A's __asan_memcpy 0x510d4, with the wrapper's same_but_materialized kept in the post as same_io; the rest of the file is new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/A/RPgW7bKit.v, with its module names changed; 255 of its 317 lines of code are new or changed and 115 lines of the source are left out. *)
(* reac-pw/fuzz_role image A (fuzz_role.asan, pinned sha256
   614cffc0864cc31d9d1ced61322c4efd567b64bc89fe09a227a05b5126e0debb; addresses measured on the unstripped twin
   6da77bafc5c050954dd89149e1e55a24064c2211e3cbd351822d1c0a20900ad6, same loaded bytes): the block lemma w6_head of
   lib/A/RPgW6aBase.v, the pod loop's head C 0x80a80 of LLVMFuzzerTestOneInput through the memset of e (pod.h:279):
     0x80a80  sd a1,0xd8(s1)                  [R+0xd8] := k
     0x80a84 .. 0x80ab4  13 x sb zero,o(s3)   shadow_addr F + 0x1e .. 0x2a := 0
     0x80ab8  addi a2,zero,0x68; 0x80abc ld a0,0xf0(s1); 0x80ac0 mv a1,zero
     0x80ac4  jal 0x51570                      __asan_memset(F + 0xf0, 0, 104), back at 0x80ac8
   HOW. One engine run (lib/Reusable/YCbq.v aj_run_to over w6_tbl) from 0x80a80 to the callee's entry 0x51570, over
   two regions: the real frame's cells [R+0xd8, R+0xf8) based at the s1 atom (write window [0xd8, 0xe0): the callers'
   stack window of the journal), whose chunk at 0xf0 is the address of e held in the extra env slot 32; and the 13
   shadow bytes [0x1e, 0x2b) of the frame (3, pos) based at the s3 atom (write window: the frame's shadow, in_frames).
   No instrumented check is in the block. The call is the Section hypothesis AMEMSET (the kernel's contract of
   __asan_memset, lib/Reusable/YG0d.v aintrin_realizes OSet), applied through w6h_intrin (lib/Reusable/YCbq.v
   aj_intrin_at, which also keeps the callee's same_but_materialized); its destination e lies in the owned frame, its
   shadow is the 13 zero bytes just stored, and the callee's stack [R - ESTACK, R) lies in the journal's window. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import Img0 RPgBase RPgCSpec RPgSteps RPgW6aBase.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require RPgCfgChanges.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the entry state of the run ---- *)
(* env slot 32 = F + 0xf0, the address of e that [R+0xf0] holds *)
Definition w6h_extra (F : Z) : list word := [w64 (F + 0xf0)].
Definition w6h_rR : YP09.region := YP09.mkRegion (Some 9%nat) 0xd8 0xf8 0xd8 0xe0 [YP09.mkChunk 0xf0 (CVal 8 (SOff 32 0))].
Definition w6h_rS : YP09.region := YP09.mkRegion (Some 19%nat) 0x1e 0x2b 0x1e 0x2b [].
Definition w6h_ss0 : sstate := mkSS W6_C sr_atoms [w6h_rR; w6h_rS] None (mkFacts [] [] []).

(* ---- arithmetic of the frame address (F mod 32 = 0, no division left for lia) ---- *)
Lemma w6h_div : forall F, F mod 32 = 0 -> F = 32 * (F / 32) /\ shadow_addr F = SHADOW_OFF + 4 * (F / 32).
Proof.
intros F H. pose proof (Z.div_mod F 32 ltac:(lia)) as E. rewrite H, Z.add_0_r in E.
split; [exact E|]. unfold shadow_addr. f_equal. remember (F / 32) as q eqn:Hq. clear Hq. rewrite E.
replace (32 * q) with ((4 * q) * 8) by ring. apply Z.div_mul. lia.
Qed.
Lemma w6h_sh_e : forall F, F mod 32 = 0 -> shadow_of_addr SHADOW_OFF (F + 0xf0) = shadow_addr F + 0x1e.
Proof.
intros F H. destruct (w6h_div F H) as [E1 E2]. rewrite E2. unfold shadow_of_addr.
remember (F / 32) as q eqn:Hq. clear Hq. rewrite E1.
replace (32 * q + 0xf0) with ((4 * q + 30) * 8) by ring. rewrite Z.div_mul by lia. ring.
Qed.
Lemma w6h_e_mod8 : forall F, F mod 32 = 0 -> (F + 0xf0) mod 8 = 0.
Proof.
intros F H. destruct (w6h_div F H) as [E1 _]. remember (F / 32) as q eqn:Hq. clear Hq. rewrite E1.
replace (32 * q + 0xf0) with ((4 * q + 30) * 8) by ring. apply Z_mod_mult.
Qed.
Lemma w6h_hull : forall F, F mod 32 = 0 -> forall s,
shadow_addr (F + 0xf0) / 8 * 8 <= s < shadow_addr (F + 0xf0 + 104 - 1) / 8 * 8 + 8 ->
shadow_addr F + 16 <= s < shadow_addr F + 56.
Proof.
intros F H s Hs. destruct (w6h_div F H) as [E1 E2]. rewrite E2. remember (F / 32) as q eqn:Hq. clear Hq.
assert (A1 : shadow_addr (F + 0xf0) = SHADOW_OFF + 4 * q + 30).
{ unfold shadow_addr. rewrite E1. replace (32 * q + 0xf0) with ((4 * q + 30) * 8) by ring. rewrite Z.div_mul by lia. ring. }
assert (A2 : shadow_addr (F + 0xf0 + 104 - 1) = SHADOW_OFF + 4 * q + 42).
{ unfold shadow_addr. rewrite E1. replace (32 * q + 0xf0 + 104 - 1) with ((4 * q + 42) * 8 + 7) by ring.
  rewrite Z.div_add_l by lia. change (7 / 8) with 0. ring. }
rewrite A1, A2 in Hs. clear A1 A2 E1 E2.
pose proof (Z.div_mod (SHADOW_OFF + 4 * q + 30) 8 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (SHADOW_OFF + 4 * q + 30) 8 ltac:(lia)) as M1.
pose proof (Z.div_mod (SHADOW_OFF + 4 * q + 42) 8 ltac:(lia)) as D2.
pose proof (Z.mod_pos_bound (SHADOW_OFF + 4 * q + 42) 8 ltac:(lia)) as M2.
lia.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* the frame (class 3, 512 bytes) of an in_app address F: its bounds, its shadow below the ceiling, apart from F *)
Lemma w6h_bounds : forall F, F mod 32 = 0 -> in_app F 512 ->
4096 <= F /\ F + 512 <= alloc_ceiling /\ 0 <= shadow_addr F /\ shadow_addr F + 64 <= alloc_ceiling /\
(F + 512 <= shadow_addr F \/ shadow_addr F + 64 <= F) /\ amem_range (F + 0xf0) 104.
Proof.
intros F Hm Ha. destruct (w6h_div F Hm) as [E1 E2]. pose proof asan_consts as (C1 & _). rewrite E2.
remember (F / 32) as q eqn:Hq. clear Hq.
unfold in_app, amem_range, SHADOW_OFF, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *.
lia.
Qed.
(* a register the state holds as its own atom *)
Lemma w6h_den_atom : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof.
intros E n v H Hv. apply bv_eq. rewrite denot_SOff, H, Z.add_0_r. rewrite !unsigned_lit_small by exact Hv.
apply zcanon_id. unfold M64. lia.
Qed.
(* the callee-saved registers are exactly the nonzero registers outside w6_caller_saved *)
Lemma w6h_callee : forall r : bv 5, bv_unsigned r <> 0 -> ~ In r w6_caller_saved -> acallee_saved (bv_unsigned r).
Proof.
intros r H0 Hn. pose proof (in_nz_regs r H0) as Hin. cbv [nz_regs In] in Hin.
repeat (destruct Hin as [<- | Hin];
[ first
  [ (lazymatch goal with |- context [bv_unsigned ?x] => let v := eval vm_compute in (bv_unsigned x) in
       change (bv_unsigned x) with v end; unfold acallee_saved; lia)
  | (exfalso; apply Hn; cbv [w6_caller_saved In]; repeat (first [left; apply bv_eq; reflexivity | right])) ]
| ]).
destruct Hin.
Qed.
(* an aview value kept, as a val_mem *)
Lemma w6h_val_kept : forall H (m m' : word -> option byte) a n v,
(forall k, 0 <= k < Z.of_nat n -> aview rsegs H m' (a + k) = aview rsegs H m (a + k)) ->
val_mem rsegs (mrestrict H m) a n v -> val_mem rsegs (mrestrict H m') a n v.
Proof. intros H m m' a n v Hk Hv. exact (val_mem_kept rsegs H H m m' a n v Hk Hv). Qed.
(* a one-byte chunk of value 0 *)
Lemma w6h_chunk0 : forall E H mem base o,
YP09.chunk_ok rsegs E (mrestrict H mem) base (YP09.mkChunk o (CVal 1 (SLit 0))) -> aview rsegs H mem (base + o) = Some 0.
Proof.
intros E H mem base o Hc. destruct (Hc 0 ltac:(cbn; lia)) as (b & Hb1 & Hb2).
assert (Hb3 : mbyte rsegs (mrestrict H mem) (base + o) = Some b) by (rewrite <- Hb2; f_equal; cbn; ring).
unfold aview. rewrite Hb3. cbn [cbyte YP09.c_val] in Hb1. injection Hb1 as <-.
first [reflexivity | (vm_compute; reflexivity)].
Qed.
(* a region of a run's state, and its chunks [lib/A/RPgCheckStr.v st_ok_region_nth / field_of_region] *)
Lemma w6h_region_nth : forall E ss ms i r (H : word -> bool),
st_ok rsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r -> region_ok rsegs E (mrestrict H (ms_mem ms)) r.
Proof.
intros E ss ms i r H HS Hi. destruct (st_ok_mem_ok rsegs E ss (restrict H ms) HS) as (_ & Hrs & _).
exact (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)).
Qed.
Lemma w6h_chunks : forall E m n b cs lo hi wlo whi,
region_ok rsegs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = b ->
forall c, In c cs -> YP09.chunk_ok rsegs E m b c.
Proof.
intros E m n b cs lo hi wlo whi (_ & _ & _ & Hcs) Hn c Hc.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck. exact Hck.
Qed.

Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.
(* __asan_memset at 0x51570: the kernel's contract of the intrinsic *)
Hypothesis AMEMSET : aintrin_realizes rsegs B OSet W6_MEMSET.

(* lib/Reusable/YCbq.v aj_intrin_at for OSet, also keeping the callee's same_but_materialized (for same_io) *)
Lemma w6h_intrin : forall pc, aintrin_realizes rsegs B OSet pc ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d x n (o : Z) raw,
ajournal rsegs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 d -> getr regsT 11 = w64 x -> getr regsT 12 = w64 n -> 0 <= n < 2 ^ 32 -> 0 <= d -> d + n <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
(forall a, d <= a < d + n -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ ~ (sp0 + o - ESTACK <= a < sp0 + o)) ->
amem_range d n ->
range_addressable (aview rsegs (w_H W) memT) SHADOW_OFF d n ->
(0 < n -> shadow_hull_vis (aview rsegs (w_H W) memT) d n) ->
SRr rsegs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom rsegs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom rsegs)) md2 /\
ajournal rsegs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ same_but_materialized mdc md2 /\ getr regs2 10 = w64 d /\
(forall i, 0 <= i < n -> aview rsegs (w_H W) mem2 (d + i) = Some (x mod 256)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (sp0 + o - ESTACK <= a < sp0 + o) ->
 aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) memT a)).
Proof using LAWS.
intros pc AI W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d x n o raw
HJ Ha0 Ha1 Ha2 Hn Hd0 Hdn Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hdest Hamr Hra_d Hhull.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
assert (HPRE : ecall_pre rsegs B lyc Sc W regsT memT mdc).
{ eapply ecall_pre_at with (o := o); try eassumption. rewrite Hra. exact Hraw. }
assert (HDEST : dest_ok rsegs B lyc Sc W regsT memT d n).
{ intros a Ha. destruct (Hdest a Ha) as [Hw Hns].
  assert (Hpa : apresent (w_H W) memT a /\ ~ aowned B lyc Sc a) by (eapply awr_byte_present; eassumption).
  destruct Hpa as [Hp Hno]. rewrite Hsp'.
  split; [apply (apresent_writable rsegs); exact Hp | auto]. }
eapply SRr_mono.
{ exact (AI lyc Sc W regsT memT mdc d x n HPRE Ha0 Ha1 Ha2 Hn Hd0 Hdn HDEST Hamr Hra_d Hhull I). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Heff & Hfr & Hpres2).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write rsegs B LAWS RPgCfgChanges.cfg_segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
  (fun a => (d <= a < d + n) \/ (sp0 + o - ESTACK <= a < sp0 + o)) Sc own HJ).
  - intros a Ha Hna. apply (Hfr a Ha); intros H'; apply Hna; [left | right]; exact H'.
  - exact Hpres2.
  - exact Hsame.
  - intros a [Ha | Ha]; left; [exact (proj1 (Hdest a Ha)) | left; lia].
  - exact HAR2.
  - reflexivity. - reflexivity. - lia. - exact Hfrs. - exact HQT. }
split; [exact HP|]. split; [exact Hsame|]. split; [exact Hres|]. split; [exact Heff | exact Hfr].
Qed.

Theorem w6_head : w6_head_stmt B MT.
Proof using MTL LAWS AMEMSET.
unfold w6_head_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos kk pat
(HJ & HR16 & HRs & HRlo & Hown & HF & Hrom) H2 H9 H19 H3 H4 H11 Hvf _ _.
pose proof RPgCfgChanges.cfg_wx as Hwx. pose proof RPgCfgChanges.cfg_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
assert (Hes : ESTACK = 4096) by reflexivity.
unfold T_SEG_STK, ASTACK in HRlo.
assert (Hin3 : In (3, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (al_frames _ _ LAWS lyc Sc W memc mdc 3 pos HAR Hin3) as (Hal32 & Happ & _ & Hfsh).
rewrite <- HF in Hal32, Happ, Hfsh.
change (fs_frame_bytes 3) with 512 in Happ. change (fs_frame_bytes 3 / 8) with 64 in Hfsh.
destruct (w6h_bounds F Hal32 Happ) as (HF0 & HFc & Hsa0 & Hsac & Hsep & Hamr).
clear HAR.
(* the entry state *)
assert (U9 : bv_unsigned (ew (Ereg regs (w6h_extra F)) 9) = R).
{ rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), H9. unfold w64. apply unsigned_lit_small. lia. }
assert (U19 : bv_unsigned (ew (Ereg regs (w6h_extra F)) 19) = shadow_addr F).
{ rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl), H19. unfold w64. apply unsigned_lit_small. lia. }
assert (E32 : ew (Ereg regs (w6h_extra F)) 32 = w64 (F + 0xf0)) by exact (ew_Ereg_extra regs (w6h_extra F) 0).
assert (E11 : ew (Ereg regs (w6h_extra F)) 11 = Z_to_bv 64 (kk mod 2 ^ 64)).
{ rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl), H11. unfold w64. symmetry. apply Z_to_bv_mod64. }
assert (HS : st_ok rsegs (Ereg regs (w6h_extra F)) w6h_ss0
  (restrict (w_H W) (mkst regs (Z_to_bv 64 W6_C) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold w6h_ss0. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold region_ok, w6h_rR.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
      split; [lia|]. split; [lia|]. split.
      * intros o Ho. apply (apresent_writable rsegs). apply Hpres. lia.
      * apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val rsegs _ _ R 0xf0 8 (SOff 32 0) (F + 0xf0)); [| cbn; lia | cbn; lia | exact Hvf].
        apply w6h_den_atom; [exact E32 | lia].
    + unfold region_ok, w6h_rS.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U19.
      split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable rsegs). exact (proj1 (Hfsh o ltac:(lia))).
  - cbn [pairwise_disjoint all_disjoint]. split; [split; [|exact I] | split; [exact I | exact I]].
    unfold extent_disjoint, w6h_rR, w6h_rS. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U19. lia.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
remember (Ereg regs (w6h_extra F)) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs (w6h_extra F)) E) by (subst E; apply env_agree_refl).
clear HE.
unfold cfg_at. change (w64 W6_C) with (Z_to_bv 64 W6_C).
(* 0x80a80 .. 0x80ac4 jal: stop at the callee's entry 0x51570 *)
aj_run_to w6_tbl_ok HS HJ W6_MEMSET.
{ (* the two write windows: the real frame's cell in the callers' stack window, e's shadow in the frame (3, pos) *)
  change (ss_mem w6h_ss0) with [w6h_rR; w6h_rS]. unfold w6h_rR, w6h_rS.
  apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (R - sp0));
  [reflexivity | rewrite U9; ring | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |].
  apply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 19%nat (shadow_addr F)); [reflexivity | exact U19 | | apply awr_ok_nil].
  cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. right; right; right. exists 3, pos. split; [exact Hown|]. right.
  unfold in_zr; cbn [fst snd]. rewrite <- HF. change (fs_frame_bytes 3 / 8) with 64. lia. }
(* after the run: registers, the stored bytes, the bytes kept *)
rreg HS (10%bv : bv 5) Ga0. rreg HS (11%bv : bv 5) Ga1. rreg HS (12%bv : bv 5) Ga2. rreg HS (1%bv : bv 5) Gra.
lazymatch type of HS with st_ok _ _ ?ss (restrict _ ?ms) =>
  pose proof (regs_kept_of_st_ok rsegs E ss ms regs (w6h_extra F) (w_H W) [1; 10; 11; 12]%bv HS HAE
    ltac:(vm_compute; reflexivity)) as RK;
  let rR := eval vm_compute in (nth_error (ss_mem ss) 0) in
  let rS := eval vm_compute in (nth_error (ss_mem ss) 1) in
  lazymatch rR with Some ?r1 => lazymatch rS with Some ?r2 =>
    pose proof (w6h_region_nth E ss ms 0 r1 (w_H W) HS ltac:(vm_compute; reflexivity)) as HRR;
    pose proof (w6h_region_nth E ss ms 1 r2 (w_H W) HS ltac:(vm_compute; reflexivity)) as HRS
  end end;
  rewrite (st_ok_restrict_mkst rsegs (w_H W) E ss ms HS eq_refl) at 1;
  replace (ss_pc ss) with W6_MEMSET by (vm_compute; reflexivity)
end.
assert (NK : forall r : bv 5, existsb (fun c => bv_eqb c r) [1; 10; 11; 12]%bv = false -> ~ In r [1; 10; 11; 12]%bv).
{ intros r Hb Hin. assert (Ht : existsb (fun c => bv_eqb c r) [1; 10; 11; 12]%bv = true)
    by (apply existsb_exists; exists r; split; [exact Hin | apply bv_eqb_refl]).
  rewrite Hb in Ht. discriminate Ht. }
assert (RK2 : getr (ms_regs ms) 2 = getr regs 2)
  by (apply RK; [vm_compute; intros X; discriminate X | apply NK; vm_compute; reflexivity]).
assert (RK3 : getr (ms_regs ms) 3 = getr regs 3)
  by (apply RK; [vm_compute; intros X; discriminate X | apply NK; vm_compute; reflexivity]).
assert (RK4 : getr (ms_regs ms) 4 = getr regs 4)
  by (apply RK; [vm_compute; intros X; discriminate X | apply NK; vm_compute; reflexivity]).
(* [R+0xd8] = k and the 13 zero shadow bytes, from the run's last regions *)
assert (VD : val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) (R + 0xd8) 8 (kk mod 2 ^ 64)).
{ pose proof (w6h_chunks E _ 9%nat _ _ _ _ _ _ HRR U9 (YP09.mkChunk 0xd8 (CVal 8 (SOff 11 0))) ltac:(cbn; tauto)) as Hc.
  exact (val_of_chunk_ok rsegs E _ R 0xd8 8 (SOff 11 0) (kk mod 2 ^ 64) Hc
    (w6h_den_atom E 11 _ E11 (Z.mod_pos_bound kk (2 ^ 64) ltac:(lia))) (Z.mod_pos_bound kk (2 ^ 64) ltac:(lia)) ltac:(cbn; lia)). }
assert (Z13 : forall i, 0 <= i < 13 -> aview rsegs (w_H W) (ms_mem ms) (shadow_addr F + 0x1e + i) = Some 0).
{ intros i Hi. rewrite <- Z.add_assoc. apply (w6h_chunk0 E).
  apply (w6h_chunks E _ 19%nat _ _ _ _ _ _ HRS U19).
  assert (Hc : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/
    i = 11 \/ i = 12) by lia.
  repeat (destruct Hc as [Hc | Hc]; [subst i; cbn [In]; repeat (first [left; reflexivity | right]) |]).
  subst i; cbn [In]; repeat (first [left; reflexivity | right]). }
assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (R + 0xd8 <= a < R + 0xe0) -> ~ (shadow_addr F + 0x1e <= a < shadow_addr F + 0x2b) ->
  aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) memc a).
{ intros a Ha Ha1 Ha2. apply (aview_eq_of rsegs). apply HFr. rewrite unsigned_lit_small by exact Ha.
  intros (r & Hin & Hr). change (ss_mem w6h_ss0) with [w6h_rR; w6h_rS] in Hin. unfold w6h_rR, w6h_rS in Hin.
  cbn [In] in Hin. destruct Hin as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
  [rewrite U9 in Hr | rewrite U19 in Hr]; lia. }
clear HRR HRS.
(* the frame's shadow is present at the run's last memory (the journal's AR) *)
pose proof HJ as (HAR2 & _).
destruct (al_frames _ _ LAWS lyc Sc W _ _ 3 pos HAR2 Hin3) as (_ & _ & _ & Hfsh2).
rewrite <- HF in Hfsh2. change (fs_frame_bytes 3 / 8) with 64 in Hfsh2.
(* __asan_memset(F + 0xf0, 0, 104) at 0x51570 *)
eapply SRr_bind.
{ apply (w6h_intrin W6_MEMSET AMEMSET W (ms_regs ms) (ms_mem ms) STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k
    (F + 0xf0) 0 104 (R - sp0) (w64 W6_RET) HJ).
  - rewrite Ga0, E32. reflexivity.
  - rewrite Ga1. reflexivity.
  - rewrite Ga2. reflexivity.
  - lia.
  - lia.
  - lia.
  - unfold spZ. rewrite RK2, H2. unfold w64. rewrite unsigned_lit_small by lia. ring.
  - rewrite Zminus_mod, HR16, Hsp0al. reflexivity.
  - lia.
  - rewrite Hes. lia.
  - rewrite RK3. exact H3.
  - rewrite RK4. exact H4.
  - rewrite Gra. reflexivity.
  - unfold YK0s.ret_ok. apply bv_eq. vm_compute. reflexivity.
  - intros a Ha. split.
    + right; right; right. exists 3, pos. split; [exact Hown|]. left.
      unfold in_zr; cbn [fst snd]. rewrite <- HF. change (fs_frame_bytes 3) with 512. lia.
    + rewrite Hes. lia.
  - exact Hamr.
  - apply zero_shadow_range; [exact (w6h_e_mod8 F Hal32) | reflexivity |].
    intros i Hi. change (104 / 8) with 13 in Hi. rewrite (w6h_sh_e F Hal32). exact (Z13 i Hi).
  - intros _ s Hs. destruct (w6h_hull F Hal32 s Hs) as [Hs1 Hs2].
    replace s with (shadow_addr F + (s - shadow_addr F)) by ring.
    apply (aview_some_of_apresent rsegs). exact (proj1 (Hfsh2 (s - shadow_addr F) ltac:(lia))). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hsame & H10 & HSET & KM).
apply SRr_ret.
unfold w6_post. exists lyc, Sc, regs2, mem2, md2.
split; [reflexivity|].
split; [exact HJ2|].
split.
{ intros r Hr0 Hn. rewrite <- (Z_to_bv_bv_unsigned 5 r). rewrite (HP2 (bv_unsigned r) (w6h_callee r Hr0 Hn)).
  rewrite Z_to_bv_bv_unsigned. apply RK; [exact Hr0|]. intros X. apply Hn. cbv [w6_caller_saved In] in X |- *. tauto. }
split; [reflexivity|].
split; [apply Permutation_refl|].
split; [eapply same_io_trans; [apply RPgCfgChanges.same_io_wvb | apply same_io_materialized; exact Hsame]|].
split; [apply mo_le_refl; assumption|].
split.
{ intros a Ha Hn. unfold w6_head_wr in Hn.
  rewrite (KM a Ha ltac:(intros X; apply Hn; right; right; right; lia) ltac:(intros X; apply Hn; left; lia)).
  apply KR; [exact Ha | intros X; apply Hn; right; left; exact X | intros X; apply Hn; right; right; left; exact X]. }
split; [exact H10|].
split.
{ apply (w6h_val_kept (w_H W) (ms_mem ms) mem2 (R + 0xd8) 8 (kk mod 2 ^ 64)); [|exact VD].
  intros j Hj. change (Z.of_nat 8) with 8 in Hj. apply KM; [lia | lia | rewrite Hes; lia]. }
split.
{ intros i Hi. rewrite KM; [exact (Z13 i Hi) | lia | lia | rewrite Hes; lia]. }
intros i Hi. rewrite (HSET i Hi). reflexivity.
Qed.
End d.
End b.

Print Assumptions w6_head.
Check w6_head.
