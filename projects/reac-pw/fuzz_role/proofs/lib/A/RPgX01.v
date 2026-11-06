(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of proofs/cgif/cgif_file_fuzzer/lib/A/AC8v.v:120-122
   [Apache-2.0]; proofs/cgif/cgif_file_fuzzer/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   proofs/cgif/cgif_rgb_fuzzer/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v at origin/ossv/recipes 6ebe35ba632; its three generic lemmas L_set_shadow_at, L_fresh and L_chain are kept as rx_set_shadow_at, rx_fresh and rx_chain (rx_set_shadow_at takes the kit's ajournal_after_write, which the strong shadow-fill text allows, in place of L_after_write_win), module paths changed to reac_pw.fuzz_role; the segment walk of reac-pw/fuzz_role's image A below is new. *)
(* reac-pw/fuzz_role image A (fuzz_role.asan, pinned sha256
   614cffc0864cc31d9d1ced61322c4efd567b64bc89fe09a227a05b5126e0debb; every address measured on the unstripped twin
   6da77bafc5c050954dd89149e1e55a24064c2211e3cbd351822d1c0a20900ad6, same loaded bytes): SEGMENT S_X01 of the walk
   of LLVMFuzzerTestOneInput (0x7ff88), from K82478 (0x82478, after check_code returns) to the return.
   Proves lib/A/RPgHarn.v rh_S_X01_stmt at Img0.rsegs (kind: segment lemma).

   THE CODE (86 words 0x82478 .. 0x825cc, all 4-byte encodings):
     run 1  0x82478 mv a0,s2; 0x8247c jal 0x52424          free(pod) through the free trampoline, ra 0x82480
     run 2  0x82480 mv a0,s11; 0x82484 jal 0x52424         free(pp), ra 0x82488
     run 3  0x82488 addi a0,zero,-8; 0x8248c sb a0,0x30(s3) the role granule back to 0xf8
            0x82490 ld s6,8(s1)                            s6 = F (the cell R+8)
            0x82494 lui/addiw a0 = 0x45e0360e; 0x8249c sd a0,0(s9)   F[0] := the retirement word
            0x824a0 beqz s6,0x824bc                        NOT taken: s6 = F >= 4096 (an atom fact), so the 52
                                                           stores of the real-stack arm 0x824bc .. 0x82588 are dead
            0x824a4 addi a1,zero,0x40; 0x824a8 mv a0,s3; 0x824ac jal 0x5409c   __asan_set_shadow_f5(shadow F, 64)
     run 4  0x824b0 ld a0,0x1f8(s6); 0x824b4 sb zero,0(a0)  the flag byte of the class-3 frame := 0 (the release)
            0x824b8 j 0x8258c; 0x8258c mv a0,zero; 0x82590 addi sp,s0,-0x1a0; 13 restores 0x82594 .. 0x825c4
            (ra, s0, s1, s2 .. s11 from S-8 .. S-0x68); 0x825c8 addi sp,sp,0x1a0; 0x825cc ret.
   The two frees go through the kit's aj_free_at (YCbq.v) with the allocator's afree_realizes; the shadow fill
   through rx_set_shadow_at with the strong aset_shadow_realizes text (lib/Reusable/SetShadowDef.v); the flag
   store through aj_run_flag (YCbq.v aj_flag_store, with astack_free_law_ok and the frame flag law), which drops
   the frame from the journal's own list; the return through SRr_ret_at. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05 YG0q YG0t.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YG0s YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import SetShadowDef.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Layout.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import Img0 RPgBase RPgCSpec RPgImgA RPgHarn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require RPgCfgChanges.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ============================================ the image ============================================ *)
Definition RX_NW : nat := 86.
Definition rx_tbl : ctable := build_table rsegs RH_C4 RX_NW TEmpty.
Lemma rx_tbl_ok : table_ok rsegs rx_tbl.
Proof. apply build_table_ok0. unfold RH_C4. lia. Qed.
Definition RX_FREE : Z := 0x52424.      (* __interceptor_trampoline_free *)
Definition RX_SSF5 : Z := 0x5409c.      (* __asan_set_shadow_f5 *)
Definition RX_RA1 : Z := 0x82480.       (* free(pod)'s return *)
Definition RX_RA2 : Z := 0x82488.       (* free(pp)'s return *)
Definition RX_RA3 : Z := 0x824b0.       (* __asan_set_shadow_f5's return *)

(* ======================================= generic lemmas ======================================= *)
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section w.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Local Notation ajournal := (ajournal segs B).

(* __asan_set_shadow_XX over a range of one of the caller's own side-stack frames' shadow, in journal form
   (identity's L_set_shadow_at; the journal step is ajournal_after_write, the post keeping every present byte). *)
Lemma rx_set_shadow_at : forall pc v, aset_shadow_realizes segs B pc v ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k cid pos q n (o : Z) raw,
ajournal STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
In (cid, pos) own ->
getr regsT 10 = w64 q -> getr regsT 11 = w64 n -> 0 < n ->
shadow_addr (frame_addr lyc cid pos) <= q -> q + n <= shadow_addr (frame_addr lyc cid pos) + fs_frame_bytes cid / 8 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ AR segs B lyc Sc W mem2 md2 /\
(forall i, 0 <= i < n -> aview segs (w_H W) mem2 (q + i) = Some v) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (q <= a < q + n) -> aview segs (w_H W) mem2 a = aview segs (w_H W) memT a)).
Proof.
intros pc v ASS W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k cid pos q n o raw
HJ Hown Ha0 Ha1 Hn Hq1 Hq2 Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & _ & HQT).
assert (HPRE : ecall_pre segs B lyc Sc W regsT memT mdc).
{ eapply ecall_pre_at; try eassumption. rewrite Hra. exact Hraw. }
assert (Hin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
eapply SRr_mono.
{ exact (ASS lyc Sc W regsT memT mdc cid pos q n HPRE Hin Ha0 Ha1 Hn Hq1 Hq2). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Heff & Hfr & Hpres2 & Hkp).
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write segs B LAWS segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
    (fun a => q <= a < q + n) Sc own HJ).
  - intros a Ha Hna. apply (Hfr a Ha Hna).
  - exact Hkp.
  - exact Hsame.
  - intros a Ha. left. right. right. right. exists cid, pos. split; [exact Hown|]. right. unfold in_zr. cbn [fst snd]. lia.
  - exact HAR2.
  - reflexivity. - reflexivity. - lia. - exact Hfrs. - exact HQT. }
split; [exact HP|]. split; [exact HAR2|]. split; [exact Heff | exact Hfr].
Qed.
End w.

(* A block of the run's own list is not one of the entry's blocks: the allocator's blocks are pairwise apart
   (identity's L_fresh). *)
Lemma rx_fresh : forall segs B (LAWS : AR_laws segs B) ly S W mem md (x : Z * Z) l0 E0,
AR segs B ly S W mem md -> Permutation (ablocks B ly S) (l0 ++ E0) -> In x l0 -> 0 <= snd x -> ~ In x E0.
Proof.
intros segs B LAWS ly S W mem md x l0 E0 HAR HP Hx Hn HxE.
assert (Hz : ~ zdisjoint (block_rng x) (block_rng x)).
{ destruct x as [p m]. unfold zdisjoint, block_rng. cbn [fst snd] in *. pose proof (req_size_pos m Hn). lia. }
apply in_split in Hx as (h1 & h2 & ->). apply in_split in HxE as (e1 & e2 & ->).
assert (Hin : In x (ablocks B ly S)).
{ eapply Permutation_in; [apply Permutation_sym; exact HP|]. apply in_or_app. left. apply in_or_app. right. left. reflexivity. }
apply in_split in Hin as (a1 & a2 & Ea). rewrite Ea in HP.
replace ((h1 ++ x :: h2) ++ e1 ++ x :: e2) with (h1 ++ x :: (h2 ++ e1 ++ x :: e2)) in HP by (rewrite <- app_assoc; reflexivity).
pose proof (Permutation_app_inv a1 a2 h1 (h2 ++ e1 ++ x :: e2) x HP) as HP2.
assert (Hin2 : In x (a1 ++ a2)).
{ eapply Permutation_in; [apply Permutation_sym; exact HP2|]. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. left. reflexivity. }
apply in_app_or in Hin2 as [Hin2 | Hin2]; apply in_split in Hin2 as (b1 & b2 & ->).
- apply Hz. apply (sep_blocks_pos segs B LAWS ly S W mem md x x b1 b2 a2 HAR). rewrite Ea. rewrite <- app_assoc. reflexivity.
- apply Hz. apply (sep_blocks_pos segs B LAWS ly S W mem md x x a1 b1 b2 HAR). exact Ea.
Qed.

(* The call chain at a call the entry makes from its own frame (identity's L_chain). *)
Lemma rx_chain : forall ly (rd rdE : reader) (regsT : bvmap 5 word) sp0 mf ra s0e lyE,
spZ regsT = mf -> s0Z regsT = sp0 -> 4096 <= raZ regsT ->
alloc_ceiling <= mf -> mf + 16 <= sp0 -> sp0 mod 16 = 0 ->
rdword rd (sp0 - 8) = Some ra -> rdword rd (sp0 - 16) = Some s0e -> 4096 <= ra ->
achain lyE rdE sp0 s0e [] -> ly_top lyE = ly_top ly -> ly_top ly <= 2 ^ 47 ->
(forall a, sp0 <= a < 2 ^ 64 -> rd a = rdE a) ->
exists ch, chain_pre ly rd regsT ch /\ (ch = [] \/ exists fp v, ch = [(fp, ra, v)]).
Proof.
intros ly rd rdE regsT sp0 mf ra s0e lyE Hsp Hs0 Hra4 Hce Hmf Hal Hrd1 Hrd2 Hra Hach Etop Htop47 Hab.
unfold chain_pre.
destruct (frame0_ok ly regsT) eqn:Ef0.
2: { exists []. split; [split; [exact Hra4 | reflexivity] | left; reflexivity]. }
destruct (bad_next (spZ regsT) (ly_top ly) (s0Z regsT)) eqn:Ebn.
{ exists []. split; [split; [exact Hra4 | reflexivity] | left; reflexivity]. }
exists [(sp0, ra, s0e)]. split; [| right; exists sp0, s0e; reflexivity].
split; [exact Hra4|]. rewrite Hsp, Hs0. split; [lia|].
cbn [fpchain]. split; [reflexivity|].
split; [pose proof (Z.div_mod sp0 16 ltac:(lia)) as D; rewrite Hal, Z.add_0_r in D; rewrite D;
replace (16 * (sp0 / 16)) with ((2 * (sp0 / 16)) * 8) by lia; apply Z_mod_mult|].
split; [exact Hrd1|]. split; [exact Hrd2|]. split; [exact Hra|].
destruct (bad_next sp0 (ly_top ly) s0e) eqn:Ebn2; [reflexivity|].
unfold bad_next in Ebn2. apply Bool.orb_false_iff in Ebn2 as [Ebn2 E3]. apply Bool.orb_false_iff in Ebn2 as [E1 E2].
apply Z.leb_gt in E1. apply Z.leb_gt in E2. apply Bool.negb_false_iff in E3. apply Z.eqb_eq in E3.
unfold achain in Hach. destruct Hach as [(Hbad & _) | (Hlo & Hhi & Hal8 & Hfp & _)].
- exfalso. rewrite Etop in Hbad. lia.
- cbn [fpchain] in Hfp |- *. destruct Hfp as (r & Hr & Hrr). exists r. split; [|exact Hrr].
rewrite <- Hr. apply rdword_ext. intros kk Hkk. apply Hab. rewrite Etop in Hhi. clear - Hlo Hhi Hkk Htop47. lia.
Qed.

(* the 8 bytes of a cell, read back as a word *)
Lemma rx_rdword_of_val : forall segs H mem a v, 0 <= v < 2 ^ 64 ->
val_mem segs (mrestrict H mem) a 8 v -> rdword (aview segs H mem) a = Some v.
Proof.
intros segs H mem a v Hv Hm.
assert (A : forall k, (k < 8)%nat -> aview segs H mem (a + Z.of_nat k) = Some (YO0f.le_byte v 8 k)).
{ intros k Hk. unfold aview. rewrite (Hm k Hk). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  unfold YO0f.le_byte. apply Z.mod_mod. lia. }
unfold rdword.
pose proof (A 0%nat ltac:(lia)) as A0. pose proof (A 1%nat ltac:(lia)) as A1. pose proof (A 2%nat ltac:(lia)) as A2.
pose proof (A 3%nat ltac:(lia)) as A3. pose proof (A 4%nat ltac:(lia)) as A4. pose proof (A 5%nat ltac:(lia)) as A5.
pose proof (A 6%nat ltac:(lia)) as A6. pose proof (A 7%nat ltac:(lia)) as A7.
cbv [Z.of_nat Pos.of_succ_nat Pos.succ] in A0, A1, A2, A3, A4, A5, A6, A7. rewrite Z.add_0_r in A0.
rewrite A0, A1, A2, A3, A4, A5, A6, A7. f_equal. apply YG0s.le_bytes8. exact Hv.
Qed.

(* a region of the symbolic state is ok for the machine's memory *)
Lemma rx_st_region : forall segs E ss ms r, st_ok segs E ss ms -> In r (ss_mem ss) -> region_ok segs E (ms_mem ms) r.
Proof.
intros segs E ss ms r (_ & _ & _ & _ & _ & _ & _ & (_ & Hok & _) & _) Hin.
exact (proj1 (Forall_forall _ _) Hok r Hin).
Qed.
(* the byte a chunk holding the literal 0 shows *)
Lemma rx_chunk_zero : forall segs E m base off n,
YP09.chunk_ok segs E m base (YP09.mkChunk off (CVal n (SLit 0))) -> (1 <= n)%N ->
mbyte segs m (base + off) = Some (Z_to_bv 8 0).
Proof.
intros segs E m base off n Hc Hn. destruct (Hc 0 ltac:(cbn [YP09.c_len YP09.c_val YP09.cv_len]; lia)) as (b & Hb & Hm).
cbn [YP09.c_off YP09.c_val YP09.cbyte] in Hm, Hb. rewrite !Z.add_0_r in Hm. rewrite Hm. injection Hb as <-.
first [reflexivity | f_equal; vm_compute; reflexivity].
Qed.
(* a register the run did not touch, or a literal, or an extra atom *)
Lemma rx_reg_atom : forall segs E ss ms H regs extra (r r' : bv 5) (n : nat),
st_ok segs E ss (restrict H ms) -> E = Ereg regs extra -> sr_get (ss_regs ss) r = SOff n 0 ->
Z.of_nat n = bv_unsigned r' -> getr (ms_regs ms) r = getr regs r'.
Proof.
intros segs E ss ms H regs extra r r' n HS -> Hg Hn. rewrite (st_ok_restrict_reg segs H _ ss ms r HS), Hg.
cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact (ew_Ereg_nat regs extra n r' Hn).
Qed.
(* the eight registers the segment reads from its start values: sp, gp, tp, s0 = S, s1 = R, s3 = the frame's
   shadow base, s9 = F, s11 = pp *)
Definition rx_regs (regs : bvmap 5 word) (R gp tp S shF F pp : Z) : Prop :=
getr regs (Z_to_bv 5 2) = w64 R /\ getr regs (Z_to_bv 5 3) = w64 gp /\ getr regs (Z_to_bv 5 4) = w64 tp /\
getr regs (Z_to_bv 5 8) = w64 S /\ getr regs (Z_to_bv 5 9) = w64 R /\ getr regs (Z_to_bv 5 19) = w64 shF /\
getr regs (Z_to_bv 5 25) = w64 F /\ getr regs (Z_to_bv 5 27) = w64 pp.
Lemma rx_regs_pres : forall r1 r2 R gp tp S shF F pp,
aregs_preserved r1 r2 -> rx_regs r1 R gp tp S shF F pp -> rx_regs r2 R gp tp S shF F pp.
Proof.
intros r1 r2 R gp tp S shF F pp HP (A2 & A3 & A4 & A8 & A9 & A19 & A25 & A27).
unfold rx_regs. rewrite !HP by (unfold acallee_saved; lia). repeat split; assumption.
Qed.
Lemma rx_regs_run : forall segs ss ms H regs extra R gp tp S shF F pp,
st_ok segs (Ereg regs extra) ss (restrict H ms) ->
forallb (fun k : Z => sv_eqb (sr_get (ss_regs ss) (Z_to_bv 5 k)) (SOff (Z.to_nat k) 0)) [2; 3; 4; 8; 9; 19; 25; 27] = true ->
rx_regs regs R gp tp S shF F pp -> rx_regs (ms_regs ms) R gp tp S shF F pp.
Proof.
intros segs ss ms H regs extra R gp tp S shF F pp HS Hck (A2 & A3 & A4 & A8 & A9 & A19 & A25 & A27).
assert (K : forall k, In k [2; 3; 4; 8; 9; 19; 25; 27] -> getr (ms_regs ms) (Z_to_bv 5 k) = getr regs (Z_to_bv 5 k)).
{ intros k Hk. pose proof (proj1 (forallb_forall _ _) Hck k Hk) as Hq. cbn beta in Hq. apply sv_eqb_eq in Hq.
  eapply (rx_reg_atom segs _ ss ms H regs extra _ _ (Z.to_nat k) HS eq_refl Hq).
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32.
  cbn [In] in Hk. rewrite Z.mod_small by lia. lia. }
unfold rx_regs. rewrite !K by (cbn [In]; tauto). repeat split; assumption.
Qed.
(* the memory a run with no write window leaves *)
Lemma rx_aview_same : forall segs H (m m' : word -> option byte) a, (forall x, m' x = m x) ->
aview segs H m' a = aview segs H m a.
Proof. intros segs H m m' a Hm. apply aview_eq_of. unfold mrestrict. rewrite Hm. reflexivity. Qed.
(* the flag byte after `sb zero,0(a0)` *)
Lemma rx_flag0_of : forall segs E ss ms n,
st_ok segs E ss ms -> In (YP09.mkRegion (Some n) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SLit 0))]) (ss_mem ss) ->
mbyte segs (ms_mem ms) (bv_unsigned (ew E n)) = Some (Z_to_bv 8 0).
Proof.
intros segs E ss ms n HS Hin. pose proof (rx_st_region segs E ss ms _ HS Hin) as (_ & _ & _ & Hc).
cbn [YP09.r_chunks YP09.r_base base_val] in Hc. inversion Hc as [|c l Hc0 _]; subst.
rewrite <- (Z.add_0_r (bv_unsigned (ew E n))). exact (rx_chunk_zero segs E _ _ 0 1 Hc0 ltac:(lia)).
Qed.
Lemma rx_reg_ext : forall segs E ss ms H regs extra (r : bv 5) (j : nat),
st_ok segs E ss (restrict H ms) -> E = Ereg regs extra -> sr_get (ss_regs ss) r = SOff (32 + j) 0 ->
getr (ms_regs ms) r = nth j extra (Z_to_bv 64 0).
Proof.
intros segs E ss ms H regs extra r j HS -> Hg. rewrite (st_ok_restrict_reg segs H _ ss ms r HS), Hg.
cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact (ew_Ereg_extra regs extra j).
Qed.
Lemma rx_reg_lit : forall segs E ss ms H (r : bv 5) z,
st_ok segs E ss (restrict H ms) -> sr_get (ss_regs ss) r = SLit z -> getr (ms_regs ms) r = Z_to_bv 64 z.
Proof. intros segs E ss ms H r z HS Hg. rewrite (st_ok_restrict_reg segs H _ ss ms r HS), Hg. reflexivity. Qed.
Lemma rx_ew_reg : forall regs extra (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r ->
bv_unsigned (ew (Ereg regs extra) n) = bv_unsigned (getr regs r).
Proof. intros regs extra n r Hn. rewrite (ew_Ereg_nat regs extra n r Hn). reflexivity. Qed.
(* the fresh symbolic state of a cut or a call return with no region *)
Lemma rx_entry0 : forall pc (W : world rsegs) regs mem,
st_ok rsegs (Ereg regs []) (mkSS pc sr_atoms [] None (mkFacts [] [] []))
(restrict (w_H W) (mkst regs (Z_to_bv 64 pc) mem (seg_rom rsegs))).
Proof.
intros pc W regs mem. rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- cbn. exact I.
- split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I.
Qed.

Section f.
Variable B : asyms.
Hypothesis FFL : frame_flag_lawP rsegs B.
(* every journal from the entry keeps ly_F, so a frame's and its flag's addresses are the entry layout's *)
Lemma rx_jF : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k c q,
ajournal rsegs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
frame_addr ly' c q = frame_addr ly c q /\ flag_addr ly' c q = flag_addr ly c q.
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k c q (_ & Hly & _).
destruct Hly as (_ & _ & _ & _ & _ & EF & _). unfold frame_addr, flag_addr. rewrite EF. split; reflexivity.
Qed.
(* the frame for locals (class 3, 512 bytes, 64 shadow bytes) and its flag at a state of the journal *)
Lemma rx_ffacts : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k pos,
ajournal rsegs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k -> In (3, pos) (frames S') ->
frame_addr ly 3 pos mod 32 = 0 /\ in_app (frame_addr ly 3 pos) 512 /\
4096 <= frame_addr ly 3 pos /\ frame_addr ly 3 pos + 512 <= alloc_ceiling /\
(forall a, frame_addr ly 3 pos <= a < frame_addr ly 3 pos + 512 -> apresent (w_H W') mem' a /\ ~ aowned B ly' S' a) /\
(forall i, 0 <= i < 64 -> apresent (w_H W') mem' (shadow_addr (frame_addr ly 3 pos) + i)) /\
apresent (w_H W') mem' (flag_addr ly 3 pos) /\ aowned B ly' S' (flag_addr ly 3 pos) /\
4096 <= flag_addr ly 3 pos < alloc_ceiling.
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k pos HJ Hin.
pose proof (AR_laws_ok rsegs B) as HL. pose proof (proj1 HJ) as HAR.
destruct (rx_jF STK sp0 FP ly S W mem md own ly' S' W' mem' md' k 3 pos HJ) as [EFA EFL].
destruct (al_frames _ _ HL _ _ _ _ _ 3 pos HAR Hin) as (HFal & HFapp & HFpres & HFSpres).
destruct (frames_bounds rsegs B HL _ _ _ _ _ 3 pos HAR Hin) as (HF4096 & HFceil & _).
destruct (FFL _ _ _ _ _ 3 pos HAR Hin) as (HFLp & HFLo & _ & (HFL4096 & _ & HFLceil)).
rewrite EFA in HFal, HFapp, HFpres, HFSpres, HF4096, HFceil. rewrite EFL in HFLp, HFLo, HFL4096, HFLceil.
change (fs_frame_bytes 3) with 512 in *. change (512 / 8) with 64 in HFSpres.
split; [exact HFal|]. split; [exact HFapp|]. split; [exact HF4096|]. split; [exact HFceil|].
split; [exact HFpres|]. split; [intros i Hi; exact (proj1 (HFSpres i Hi))|].
split; [exact HFLp|]. split; [exact HFLo|]. lia.
Qed.
End f.
End a.

(* the value of a register after a run, from the symbolic state *)
Ltac rx_atom HS r r' H :=
lazymatch type of HS with st_ok ?segs (Ereg ?rg ?ex) ?ss (restrict ?Hh ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
lazymatch e with SOff ?n 0 =>
assert (H : getr (ms_regs ms) r = getr rg r')
  by (apply (rx_reg_atom segs (Ereg rg ex) ss ms Hh rg ex r r' n HS eq_refl); vm_compute; reflexivity) end end.
Ltac rx_lit HS r H :=
lazymatch type of HS with st_ok ?segs ?E ?ss (restrict ?Hh ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
lazymatch e with SLit ?z =>
assert (H : getr (ms_regs ms) r = Z_to_bv 64 z)
  by (apply (rx_reg_lit segs E ss ms Hh r z HS); vm_compute; reflexivity) end end.
(* a register index as the numeral the kit's texts write (getr regs 2, ...) *)
Ltac z5 H := repeat match type of H with context [Z_to_bv 5 ?k] =>
  replace (Z_to_bv 5 k) with (@BV 5 k I) in H by (apply bv_eq; reflexivity) end.
Ltac z5g := repeat match goal with |- context [Z_to_bv 5 ?k] =>
  replace (Z_to_bv 5 k) with (@BV 5 k I) by (apply bv_eq; reflexivity) end.
Ltac rx_mach HS m := lazymatch type of HS with st_ok _ _ _ (restrict _ ?x) => rename x into m end.

Ltac rx_ext HS r H :=
lazymatch type of HS with st_ok ?segs (Ereg ?rg ?ex) ?ss (restrict ?Hh ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
lazymatch e with SOff ?n 0 =>
let j := eval vm_compute in (n - 32)%nat in
assert (H : getr (ms_regs ms) r = nth j ex (Z_to_bv 64 0))
  by (apply (rx_reg_ext segs (Ereg rg ex) ss ms Hh rg ex r j HS eq_refl); vm_compute; reflexivity) end end.
(* the flag-store run (YCbq.v aj_flag_store), applied with its sixteen journal arguments STK .. pos Q. The kit's
   aj_run_flag (YCbq.v:3076) passes fifteen underscores there, one short; that elaborates only where the shifted
   argument happens to unify (it does in released walks) and did not here, so this file carries the full count. *)
Ltac rx_run_flag HS HJ HL Hsegs ML Hwx HASF FFL :=
lazymatch type of HS with st_ok ?segs ?E ?ss (restrict (w_H ?W) ?ms) =>
let r := eval vm_compute in (sym_runN segs rx_tbl FUEL ss) in
lazymatch r with (?ss', ?st) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_runN segs rx_tbl FUEL ss = (ss', st)) by (vm_compute; reflexivity);
eapply (aj_flag_store segs _ HL Hsegs ML rx_tbl rx_tbl_ok Hwx HASF FFL W FUEL E ss ss' st ms
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS Hrun I HJ);
[ clear Hrun | clear Hrun | clear Hrun | clear Hrun HS HJ; aj_after_run HS HJ ] end end.
(* the release's symbolic state: the flag pointer word F+0x1f8 (atom 32 = the flag address), the flag byte, and the
   13 saves at S-8 .. S-0x68 (atom 33 + j = the entry's j-th saved register) *)
Definition rx_sv_chunks : list YP09.chunk :=
map (fun j => YP09.mkChunk (-8 - 8 * Z.of_nat j) (CVal 8 (SOff (32 + Nat.succ j) 0))) (seq 0 13).
Definition rx_X7 {fx : YK11.FPState} (fl : Z) (regs : bvmap 5 word) : list word :=
Z_to_bv 64 fl :: map (fun r => getr regs r) rh_saved_regs.

(* ======================================= the segment ======================================= *)
Section m. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK : Z.
(* the allocator's laws and its free operation, the side stack's flag law, the shadow fill, the image's free entry
   and the call traces of the two free sites, the harness's stack and event budgets *)
Hypothesis ML : model_laws (as_universe B).
Hypothesis HAPI : api_env rsegs B.
Hypothesis AFREE : afree_realizes rsegs B.
Hypothesis FFL : frame_flag_lawP rsegs B.
Hypothesis ASHF5 : aset_shadow_realizes rsegs B RX_SSF5 0xf5.
Hypothesis HFREE : pc_wrap_free (as_code B) = RX_FREE.
Hypothesis HTRACE : forall c, In c [[RX_RA1]; [RX_RA1; RA_LLVMF]; [RX_RA2]; [RX_RA2; RA_LLVMF]] ->
In (firstn kUnwindMax (pc_free_ra0 (as_code B) :: flat_map (fun r => if r =? pc_free_ra0 (as_code B) then [] else [r]) c))
(as_universe B).
Hypothesis HSTK : ASTACK + 0x1b0 <= LLVMF_STK.
Hypothesis HEV : 4 <= EV_LIB.

Theorem rx_S_X01 : rh_S_X01_stmt rsegs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
Proof.
unfold rh_S_X01_stmt.
intros hx pos e ly4 S4 W4 regs4 mem4 md4 HB HC.
destruct hx as [ly S W regs mem md p n pl].
unfold rh_ret. unfold rh_base in HB. unfold rh_cut_C4, rh_j, rh_geo, rh_kept in HC.
cbn [h_ly h_S h_W h_regs h_mem h_md h_p h_n h_pl] in HB, HC |- *.
destruct HB as (HPRE & Hra & _ & _ & _ & _ & _ & Hfr0 & Hev0 & _ & _).
destruct HC as (HJ & HPerm & Hnpp & Hnpod & R2 & R3 & R4 & (ES & ER & EF) & Hlen & Hpp0 & Hpod0 & HCUT & _ & HKEPT).
pose proof RPgCfgChanges.cfg_wx as Hwx. pose proof RPgCfgChanges.cfg_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as HL. pose proof (astack_free_law_ok rsegs B) as HASF.
pose proof HPRE as (HAR0 & Hraok & Hra4 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
pose proof Hstk0 as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Has : ASTACK = 16384) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
unfold RH_CID, RH_RSZ in *.
(* ---- the cut's quantities ---- *)
set (S0 := spZ regs) in *.
set (F := frame_addr ly 3 pos) in *.
set (FL := flag_addr ly 3 pos) in *.
set (R := e_R e) in *. set (pp := e_pp e) in *. set (pod := e_pod e) in *. set (len := e_len e) in *.
assert (HS064 : 0 <= S0 < 2 ^ 64) by (subst S0; unfold spZ; pose proof (bv_unsigned_in_range 64 (getr regs 2)) as X;
  change (bv_modulus 64) with (2 ^ 64) in X; lia).
assert (HR : R mod 16 = 0 /\ S0 - 0x1b0 <= R <= S0 - 0x1a0).
{ rewrite ER, ES.
  pose proof (Z.div_mod (S0 - 416) 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (S0 - 416) 32 ltac:(lia)) as M.
  pose proof (Z.div_mod S0 16 ltac:(lia)) as D16. rewrite Hal16, Z.add_0_r in D16.
  set (q := (S0 - 416) / 32) in *. set (r := (S0 - 416) mod 32) in *. set (u := S0 / 16) in *.
  split; [replace (32 * q) with ((2 * q) * 16) by lia; apply Z_mod_mult | lia]. }
destruct HR as (HR16 & HRlo & HRhi).
assert (HRc : alloc_ceiling + ASTACK <= R) by lia.
assert (Ho16 : (R - S0) mod 16 = 0) by (rewrite Zminus_mod, HR16, Hal16; reflexivity).
(* ---- the frame for locals and its flag ---- *)
assert (Hfin4 : In (3, pos) (frames S4)).
{ pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _). rewrite Hfrs, Hfr0. left. reflexivity. }
destruct (rx_ffacts B FFL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ pos HJ Hfin4)
  as (HFal & HFapp & HF4096 & HFceil & HFpres4 & HFSpres4 & HFLp4 & HFLo4 & HFLr).
fold F FL in HFal, HFapp, HF4096, HFceil, HFpres4, HFSpres4, HFLp4, HFLo4, HFLr.
set (shF := shadow_addr F) in *.
assert (HshF : shF = SHADOW_OFF + F / 8) by reflexivity.
pose proof (Z.div_mod F 8 ltac:(lia)) as D8. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as M8.
assert (HdFS : shF + 64 <= F \/ F + 512 <= shF).
{ rewrite HshF. unfold SHADOW_OFF.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. destruct HFapp as (_ & [Hlow | [Hhi1 Hhi2]]); [right; lia | left; lia]. }
assert (HshC : 0 <= shF /\ shF + 64 <= alloc_ceiling) by (rewrite HshF; unfold SHADOW_OFF; lia).
assert (HdFFL : FL + 1 <= F \/ F + 512 <= FL).
{ destruct (Z_lt_ge_dec FL F) as [Hlt|Hge]; [left; lia|].
  destruct (Z_lt_ge_dec FL (F + 512)) as [Hlt2|Hge2]; [exfalso | right; lia].
  exact (proj2 (HFpres4 FL ltac:(lia)) HFLo4). }
(* ---- the cut's registers and cells ---- *)
unfold rl_cut in HCUT. cbn [hi_L4 role_himg_A] in HCUT. rewrite !Forall_cons_iff in HCUT.
destruct HCUT as (C18 & C8 & C9 & C19 & C25 & C27 & C8c & _).
cbn [fst snd rl_at rl_xv] in C18, C8, C9, C19, C25, C27, C8c.
fold R pp pod in C18, C9, C27, C8c. rewrite ES in C8. rewrite EF in C19, C25, C8c. fold F shF in C19, C25, C8c.
rewrite Z.add_0_r in C27.
unfold rh_cells in HKEPT. apply Forall_app in HKEPT as [HKS HKF].
assert (HSV4 : forall j, (j < 13)%nat -> val_mem rsegs (mrestrict (w_H W4) mem4) (S0 + (-8 - 8 * Z.of_nat j)) 8
  (bv_unsigned (getr regs (nth j rh_saved_regs 0%bv)))).
{ intros j Hj. unfold rh_saves_L in HKS. rewrite Forall_map in HKS.
  pose proof (proj1 (Forall_forall _ _) HKS j ltac:(apply in_seq; lia)) as X. cbn [fst snd rl_at rl_xv] in X.
  rewrite ES in X. rewrite Z.mod_small in X; [exact X|]. pose proof (bv_unsigned_in_range 64 (getr regs (nth j rh_saved_regs 0%bv))) as Y.
  change (bv_modulus 64) with (2 ^ 64) in Y. exact Y. }
clear HKS.
assert (HFW4 : val_mem rsegs (mrestrict (w_H W4) mem4) (F + 0x1f8) 8 FL).
{ apply Forall_cons_iff in HKF as [X _]. cbn [fst snd rl_at rl_xv] in X. rewrite EF in X. fold F FL in X.
  rewrite Z.mod_small in X by lia. exact X. }
clear HKF.
assert (HC8 : val_mem rsegs (mrestrict (w_H W4) mem4) (R + 8) 8 F) by (rewrite Z.mod_small in C8c by lia; exact C8c).
clear C8c.
assert (RG4 : rx_regs regs4 R (as_gp B) (as_tp B) S0 shF F pp).
{ unfold rx_regs. z5g. repeat split; first [exact R2 | exact R3 | exact R4 | (z5 C8; exact C8) | (z5 C9; exact C9)
  | (z5 C19; exact C19) | (z5 C25; exact C25) | (z5 C27; exact C27)]. }
clear R2 R3 R4 C8 C9 C19 C25 C27.
(* ---- run 1: 0x82478 .. the jal of free(pod) ---- *)
unfold cfg_at. change (w64 RH_C4) with (Z_to_bv 64 RH_C4).
pose proof (rx_entry0 RH_C4 W4 regs4 mem4) as HS.
aj_run rx_tbl_ok HS HJ.
{ apply awr_ok_nil. }
rx_mach HS msA.
assert (HmA : forall x, ms_mem msA x = mem4 x) by (intros x; apply HF; intros (r & Hr & _); cbn in Hr; destruct Hr).
clear HF HFr HG.
rx_atom HS (10%bv : bv 5) (18%bv : bv 5) Ra0. z5 C18. rewrite C18 in Ra0.
rx_lit HS (1%bv : bv 5) Rra.
pose proof (rx_regs_run rsegs _ msA (w_H W4) regs4 [] _ _ _ _ _ _ _ HS ltac:(vm_compute; reflexivity) RG4) as RGA.
pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hra64. change (bv_modulus 64) with (2 ^ 64) in Hra64.
pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hs064. change (bv_modulus 64) with (2 ^ 64) in Hs064.
pose proof HJ as (_ & Hly4 & _). destruct Hly4 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop4 & _).
(* the saves read back as words, at a memory that agrees with the cut's on the save area *)
assert (HRD : forall (W' : world rsegs) m', (forall a, S0 - 0x68 <= a < S0 -> aview rsegs (w_H W') m' a = aview rsegs (w_H W4) mem4 a) ->
  rdword (aview rsegs (w_H W') m') (S0 - 8) = Some (raZ regs) /\ rdword (aview rsegs (w_H W') m') (S0 - 16) = Some (s0Z regs)).
{ intros W' m' Hk. split.
  - apply rx_rdword_of_val; [unfold raZ; lia|].
    apply (val_mem_kept rsegs (w_H W4) (w_H W') mem4 m'); [intros k Hk'; apply Hk; lia|].
    pose proof (HSV4 0%nat ltac:(lia)) as X. replace (S0 + (-8 - 8 * Z.of_nat 0)) with (S0 - 8) in X by lia. exact X.
  - apply rx_rdword_of_val; [unfold s0Z; lia|].
    apply (val_mem_kept rsegs (w_H W4) (w_H W') mem4 m'); [intros k Hk'; apply Hk; lia|].
    pose proof (HSV4 1%nat ltac:(lia)) as X. replace (S0 + (-8 - 8 * Z.of_nat 1)) with (S0 - 16) in X by lia. exact X. }
(* ---- free(pod) at 0x52424, ra 0x82480 ---- *)
pose proof RGA as (QA2 & QA3 & QA4 & QA8 & _ & _ & _ & _). z5 QA2. z5 QA3. z5 QA4. z5 QA8.
assert (EspA : spZ (ms_regs msA) = R) by (unfold spZ; rewrite QA2; unfold w64; apply unsigned_lit_small; lia).
assert (Es0A : s0Z (ms_regs msA) = S0) by (unfold s0Z; rewrite QA8; unfold w64; apply unsigned_lit_small; lia).
assert (EraA : raZ (ms_regs msA) = RX_RA1) by (unfold raZ, RX_RA1; rewrite Rra; apply unsigned_lit_small; lia).
assert (KA : forall a, aview rsegs (w_H W4) (ms_mem msA) a = aview rsegs (w_H W4) mem4 a) by (intros a; apply rx_aview_same; exact HmA).
destruct (HRD W4 (ms_mem msA) ltac:(intros a _; apply KA)) as [HRD1 HRD2].
destruct (rx_chain ly4 (aview rsegs (w_H W4) (ms_mem msA)) (aview rsegs (w_H W) mem) (ms_regs msA) S0 R (raZ regs) (s0Z regs) ly
  EspA Es0A ltac:(rewrite EraA; unfold RX_RA1; lia) ltac:(lia) ltac:(lia) Hal16 HRD1 HRD2 Hra4 Hch0
  ltac:(symmetry; exact Etop4) ltac:(rewrite Etop4; lia)) as (ch & Hch & Hchs).
{ intros a Ha. pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & J1 & _). apply J1; lia. }
assert (Hpod4 : In (pod, len) (ablocks B ly4 S4)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_or_app. right. right. left. reflexivity. }
eapply SRr_bind.
{ rewrite (st_ok_restrict_mkst rsegs (w_H W4) _ _ msA HS eq_refl) at 1. cbn [ss_pc].
  replace (Z_to_bv 64 336932) with (Z_to_bv 64 (pc_wrap_free (as_code B))) by (rewrite HFREE; reflexivity).
  eapply (aj_free_at rsegs B HL Hsegs HAPI ML AFREE W4 (ms_regs msA) (ms_mem msA) LLVMF_STK S0 [] ly S W mem md
    [(3, pos)] ly4 S4 _ 2 pod len (R - S0) (Z_to_bv 64 RX_RA1) ch HJ).
  - exact Hpod4.
  - exact Ra0.
  - lia.
  - exact Ho16.
  - lia.
  - lia.
  - exact QA3.
  - exact QA4.
  - exact Rra.
  - apply ret_ok_even. vm_compute. reflexivity.
  - pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _). lia.
  - exact Hch.
  - rewrite call_trace_of_spine, EraA. destruct Hchs as [-> | (fp & v & ->)].
    + apply (HTRACE [RX_RA1]). cbn [In]. left. reflexivity.
    + rewrite Hra. apply (HTRACE [RX_RA1; RA_LLVMF]). cbn [In]. right. left. reflexivity.
  - intros Hin. exfalso. exact (Hnpod Hin). }
cbv beta. intros W5 c5 Hwle5 (ly5 & S5 & regs5 & mem5 & md5 & -> & HJ5 & HP5 & (l1 & l2 & E1 & E2) & Hfrs5 & HK5).
clear HS Hch Hchs ch HRD1 HRD2.
pose proof (rx_regs_pres _ _ _ _ _ _ _ _ _ HP5 RGA) as RG5.
assert (HPerm5 : Permutation (ablocks B ly5 S5) (ablocks B ly S ++ [(pp, Layout.PP_SIZE)])).
{ rewrite E2. rewrite E1 in HPerm.
  replace (ablocks B ly S ++ [(pp, Layout.PP_SIZE); (pod, len)]) with ((ablocks B ly S ++ [(pp, Layout.PP_SIZE)]) ++ (pod, len) :: [])
    in HPerm by (rewrite <- app_assoc; reflexivity).
  rewrite <- (app_nil_r (ablocks B ly S ++ [(pp, Layout.PP_SIZE)])). exact (Permutation_app_inv l1 l2 _ [] (pod, len) HPerm). }
assert (Hfin5 : In (3, pos) (frames S5)) by (rewrite Hfrs5; exact Hfin4).
destruct (rx_jF B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 3 pos HJ) as [EFA4 EFL4].
pose proof (sep_block_frame rsegs B HL ly4 S4 W4 (ms_mem msA) _ pod len 3 pos (proj1 HJ) Hpod4 Hfin4) as Hdpod.
rewrite EFA4 in Hdpod. fold F in Hdpod. unfold zdisjoint in Hdpod. cbn [fst snd] in Hdpod. change (fs_frame_bytes 3) with 512 in Hdpod.
pose proof (req_size_pos len ltac:(lia)) as Hrq.
(* what the first free kept: the saves, the cell R+8 and the flag pointer word *)
assert (K5 : forall a, (S0 - 0x68 <= a < S0 \/ R + 8 <= a < R + 16 \/ F + 0x1f8 <= a < F + 0x200) ->
  aview rsegs (w_H W5) mem5 a = aview rsegs (w_H W4) mem4 a).
{ intros a Ha. rewrite <- (KA a). destruct HK5 as (K1 & _ & _ & K4 & _).
  destruct Ha as [Ha | [Ha | Ha]].
  - apply K1; lia.
  - apply K1; lia.
  - apply (K4 3 pos a Hfin4); [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite EFA4; change (fs_frame_bytes 3) with 512; fold F; lia | lia]. }
clear HK5.
(* ---- run 2: 0x82480 .. the jal of free(pp) ---- *)
pose proof (rx_entry0 RX_RA1 W5 regs5 mem5) as HS.
aj_run rx_tbl_ok HS HJ5.
{ apply awr_ok_nil. }
rx_mach HS msB.
assert (HmB : forall x, ms_mem msB x = mem5 x) by (intros x; apply HF; intros (r & Hr & _); cbn in Hr; destruct Hr).
clear HF HFr HG.
rx_atom HS (10%bv : bv 5) (27%bv : bv 5) Rb0. pose proof RG5 as (_ & _ & _ & _ & _ & _ & _ & Q27). z5 Q27. rewrite Q27 in Rb0.
rx_lit HS (1%bv : bv 5) Rrb.
pose proof (rx_regs_run rsegs _ msB (w_H W5) regs5 [] _ _ _ _ _ _ _ HS ltac:(vm_compute; reflexivity) RG5) as RGB.
pose proof RGB as (QB2 & QB3 & QB4 & QB8 & _ & _ & _ & _). z5 QB2. z5 QB3. z5 QB4. z5 QB8.
assert (EspB : spZ (ms_regs msB) = R) by (unfold spZ; rewrite QB2; unfold w64; apply unsigned_lit_small; lia).
assert (Es0B : s0Z (ms_regs msB) = S0) by (unfold s0Z; rewrite QB8; unfold w64; apply unsigned_lit_small; lia).
assert (EraB : raZ (ms_regs msB) = RX_RA2) by (unfold raZ, RX_RA2; rewrite Rrb; apply unsigned_lit_small; lia).
assert (KB : forall a, (S0 - 0x68 <= a < S0 \/ R + 8 <= a < R + 16 \/ F + 0x1f8 <= a < F + 0x200) ->
  aview rsegs (w_H W5) (ms_mem msB) a = aview rsegs (w_H W4) mem4 a)
  by (intros a Ha; rewrite (rx_aview_same rsegs _ _ _ a HmB); exact (K5 a Ha)).
destruct (HRD W5 (ms_mem msB) ltac:(intros a Ha; apply KB; lia)) as [HRD1 HRD2].
pose proof HJ5 as (_ & Hly5 & _). destruct Hly5 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop5 & _).
destruct (rx_chain ly5 (aview rsegs (w_H W5) (ms_mem msB)) (aview rsegs (w_H W) mem) (ms_regs msB) S0 R (raZ regs) (s0Z regs) ly
  EspB Es0B ltac:(rewrite EraB; unfold RX_RA2; lia) ltac:(lia) ltac:(lia) Hal16 HRD1 HRD2 Hra4 Hch0
  ltac:(symmetry; exact Etop5) ltac:(rewrite Etop5; lia)) as (ch & Hch & Hchs).
{ intros a Ha. pose proof HJ5 as (_ & _ & _ & _ & _ & _ & _ & _ & J1 & _). apply J1; lia. }
assert (Hpp5 : In (pp, Layout.PP_SIZE) (ablocks B ly5 S5)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm5|]. apply in_or_app. right. left. reflexivity. }
eapply SRr_bind.
{ rewrite (st_ok_restrict_mkst rsegs (w_H W5) _ _ msB HS eq_refl) at 1. cbn [ss_pc].
  replace (Z_to_bv 64 336932) with (Z_to_bv 64 (pc_wrap_free (as_code B))) by (rewrite HFREE; reflexivity).
  eapply (aj_free_at rsegs B HL Hsegs HAPI ML AFREE W5 (ms_regs msB) (ms_mem msB) LLVMF_STK S0 [] ly S W mem md
    [(3, pos)] ly5 S5 _ 3 pp Layout.PP_SIZE (R - S0) (Z_to_bv 64 RX_RA2) ch HJ5).
  - exact Hpp5.
  - exact Rb0.
  - lia.
  - exact Ho16.
  - lia.
  - lia.
  - exact QB3.
  - exact QB4.
  - exact Rrb.
  - apply ret_ok_even. vm_compute. reflexivity.
  - pose proof HJ5 as (_ & _ & _ & _ & _ & _ & Hnev & _). lia.
  - exact Hch.
  - rewrite call_trace_of_spine, EraB. destruct Hchs as [-> | (fp & v & ->)].
    + apply (HTRACE [RX_RA2]). cbn [In]. right. right. left. reflexivity.
    + rewrite Hra. apply (HTRACE [RX_RA2; RA_LLVMF]). cbn [In]. right. right. right. left. reflexivity.
  - intros Hin. exfalso. exact (Hnpp Hin). }
cbv beta. intros W6 c6 Hwle6 (ly6 & S6 & regs6 & mem6 & md6 & -> & HJ6 & HP6 & (m1 & m2 & E3 & E4) & Hfrs6 & HK6).
clear HS Hch Hchs ch HRD1 HRD2.
pose proof (rx_regs_pres _ _ _ _ _ _ _ _ _ HP6 RGB) as RG6.
assert (HPerm6 : Permutation (ablocks B ly6 S6) (ablocks B ly S)).
{ rewrite E4. rewrite E3 in HPerm5. rewrite <- (app_nil_r (ablocks B ly S)).
  exact (Permutation_app_inv m1 m2 _ [] (pp, Layout.PP_SIZE) HPerm5). }
assert (Hfin6 : In (3, pos) (frames S6)) by (rewrite Hfrs6; exact Hfin5).
destruct (rx_jF B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 3 pos HJ5) as [EFA5 EFL5].
pose proof (sep_block_frame rsegs B HL ly5 S5 W5 (ms_mem msB) _ pp Layout.PP_SIZE 3 pos (proj1 HJ5) Hpp5 Hfin5) as Hdpp.
rewrite EFA5 in Hdpp. fold F in Hdpp. unfold zdisjoint in Hdpp. cbn [fst snd] in Hdpp. change (fs_frame_bytes 3) with 512 in Hdpp.
pose proof (req_size_pos Layout.PP_SIZE ltac:(unfold Layout.PP_SIZE; lia)) as Hrq2.
assert (K6 : forall a, (S0 - 0x68 <= a < S0 \/ R + 8 <= a < R + 16 \/ F + 0x1f8 <= a < F + 0x200) ->
  aview rsegs (w_H W6) mem6 a = aview rsegs (w_H W4) mem4 a).
{ intros a Ha. rewrite <- (KB a Ha). destruct HK6 as (K1 & _ & _ & K4 & _).
  destruct Ha as [Ha | [Ha | Ha]].
  - apply K1; lia.
  - apply K1; lia.
  - apply (K4 3 pos a Hfin5); [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite EFA5; change (fs_frame_bytes 3) with 512; fold F; lia | lia]. }
clear HK6.
(* ---- run 3: 0x82488 .. the jal of __asan_set_shadow_f5 ---- *)
destruct (rx_ffacts B FFL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ pos HJ6 Hfin6)
  as (_ & _ & _ & _ & HFpres6 & HFSpres6 & _ & _ & _).
fold F FL shF in HFpres6, HFSpres6.
destruct (rx_jF B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 3 pos HJ6) as [EFA6 EFL6]. fold F FL in EFA6, EFL6.
pose proof RG6 as (Q62 & Q63 & Q64 & Q68 & Q69 & Q619 & Q625 & Q627).
assert (B19 : bv_unsigned (ew (Ereg regs6 []) 19) = shF)
  by (rewrite (rx_ew_reg regs6 [] 19 (Z_to_bv 5 19) ltac:(vm_compute; reflexivity)), Q619; apply unsigned_lit_small; lia).
assert (B9 : bv_unsigned (ew (Ereg regs6 []) 9) = R)
  by (rewrite (rx_ew_reg regs6 [] 9 (Z_to_bv 5 9) ltac:(vm_compute; reflexivity)), Q69; apply unsigned_lit_small; lia).
assert (B25 : bv_unsigned (ew (Ereg regs6 []) 25) = F)
  by (rewrite (rx_ew_reg regs6 [] 25 (Z_to_bv 5 25) ltac:(vm_compute; reflexivity)), Q625; apply unsigned_lit_small; lia).
assert (HS : st_ok rsegs (Ereg regs6 [])
  (mkSS RX_RA2 sr_atoms
     [ YP09.mkRegion (Some 19%nat) 0x30 0x31 0x30 0x31 [];
       YP09.mkRegion (Some 9%nat) 8 16 0 0 [YP09.mkChunk 8 (CVal 8 (SOff 25 0))];
       YP09.mkRegion (Some 25%nat) 0 8 0 8 [] ]
     None (mkFacts [(25%nat, mkAF 4096 (2 ^ 47) 5)] [] []))
  (restrict (w_H W6) (mkst regs6 (Z_to_bv 64 RX_RA2) mem6 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite B19. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable rsegs). apply HFSpres6. lia.
    + rewrite B9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val rsegs _ _ R 8 8 (SOff 25 0) F).
      * cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ew_Ereg_nat regs6 [] 25 (Z_to_bv 5 25) ltac:(vm_compute; reflexivity)).
        exact Q625.
      * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
      * cbn. lia.
      * change (N.to_nat 8) with 8%nat.
        apply (val_mem_kept rsegs (w_H W4) (w_H W6) mem4 mem6); [intros k Hk; apply K6; lia | exact HC8].
    + rewrite B25. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable rsegs). apply (proj1 (HFpres6 (F + o) ltac:(lia))).
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite B19, B9, B25.
    repeat split; first [exact I | lia].
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. split; [|exact I].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite B25. change (2 ^ 5) with 32. lia. }
change (w64 RX_RA2) with (Z_to_bv 64 RX_RA2).
aj_run rx_tbl_ok HS HJ6.
{ eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 19%nat shF); [reflexivity | exact B19 | |].
  { cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. right. right. right. exists 3, pos. split; [left; reflexivity|]. right.
    unfold in_zr. cbn [fst snd]. rewrite EFA6. change (fs_frame_bytes 3 / 8) with 64. fold shF. lia. }
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 25%nat F); [reflexivity | exact B25 | |].
  { cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. right. right. right. exists 3, pos. split; [left; reflexivity|]. left.
    unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA6. change (fs_frame_bytes 3) with 512. lia. }
  apply awr_ok_nil. }
rx_mach HS msC.
assert (KC : forall a, 0 <= a < 2 ^ 64 -> ~ (shF + 0x30 <= a < shF + 0x31) -> ~ (F <= a < F + 8) ->
  aview rsegs (w_H W6) (ms_mem msC) a = aview rsegs (w_H W6) mem6 a).
{ intros a Ha H1 H2. apply aview_eq_of. apply HFr. rewrite unsigned_lit_small by lia. intros (r & Hin & Hw).
  cbn in Hin. destruct Hin as [<-|[<-|[<-|[]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
  rewrite ?B19, ?B9, ?B25 in Hw; lia. }
clear HF HFr HG.
rx_atom HS (10%bv : bv 5) (Z_to_bv 5 19) Rc0. rewrite Q619 in Rc0.
rx_atom HS (22%bv : bv 5) (Z_to_bv 5 25) Rc22. rewrite Q625 in Rc22.
rx_lit HS (11%bv : bv 5) Rc1.
rx_lit HS (1%bv : bv 5) Rrc.
pose proof (rx_regs_run rsegs _ msC (w_H W6) regs6 [] _ _ _ _ _ _ _ HS ltac:(vm_compute; reflexivity) RG6) as RGC.
pose proof RGC as (QC2 & QC3 & QC4 & _ & _ & _ & _ & _). z5 QC2. z5 QC3. z5 QC4.
assert (EspC : spZ (ms_regs msC) = R) by (unfold spZ; rewrite QC2; unfold w64; apply unsigned_lit_small; lia).
(* ---- __asan_set_shadow_f5(shadow F, 64) at 0x5409c, ra 0x824b0 ---- *)
eapply SRr_bind.
{ rewrite (st_ok_restrict_mkst rsegs (w_H W6) _ _ msC HS eq_refl) at 1. cbn [ss_pc].
  replace (Z_to_bv 64 344220) with (Z_to_bv 64 RX_SSF5) by reflexivity.
  eapply (rx_set_shadow_at rsegs B HL Hsegs RX_SSF5 0xf5 ASHF5 W6 (ms_regs msC) (ms_mem msC) LLVMF_STK S0 [] ly S W mem md
    [(3, pos)] ly6 S6 _ 4 3 pos shF 64 (R - S0) (Z_to_bv 64 RX_RA3) HJ6).
  - left. reflexivity.
  - exact Rc0.
  - exact Rc1.
  - lia.
  - rewrite EFA6. fold shF. lia.
  - rewrite EFA6. fold shF. change (fs_frame_bytes 3 / 8) with 64. lia.
  - lia.
  - exact Ho16.
  - lia.
  - lia.
  - exact QC3.
  - exact QC4.
  - exact Rrc.
  - apply ret_ok_even. vm_compute. reflexivity. }
cbv beta. intros W7 c7 Hwle7 (-> & regs7 & mem7 & md7 & -> & HJ7 & HP7 & HAR7 & Hf5 & Hk7).
clear HS.
clear K5 KB KA HmA HmB Ra0 Rb0 Rra Rrb HRD Hdpod Hdpp Hrq Hrq2 E1 E2 E3 E4 HPerm HPerm5 Hpod4 Hpp5 RGA RGB RG5 Q62 Q63 Q64 Q68 Q69 Q619 Q625 Q627 B19 B9 B25 HFpres4 HFSpres4 HFpres6 HFSpres6 HC8 EFA4 EFL4 EFA5 EFL5 Hwle5 Hwle6 Hwle7 HAR7 Hf5 Hfin4 Hfin5 HJ HJ5 HJ6 QA2 QA3 QA4 QA8 QB2 QB3 QB4 QB8 EspA Es0A EraA EspB Es0B EraB Etop4 Etop5 Rc0 Rc1 Rrc HP5 HP6 C18 HFLp4 HFLo4.
(* ---- run 4: 0x824b0 .. the ret: the flag byte, a0 = 0, the epilogue ---- *)
pose proof (rx_regs_pres _ _ _ _ _ _ _ _ _ HP7 RGC) as RG7.
assert (R722 : getr regs7 (Z_to_bv 5 22) = w64 F) by (rewrite (HP7 22 ltac:(unfold acallee_saved; lia)); z5g; exact Rc22).
assert (K7 : forall a, (S0 - 0x68 <= a < S0 \/ F + 0x1f8 <= a < F + 0x200) ->
  aview rsegs (w_H W6) mem7 a = aview rsegs (w_H W4) mem4 a).
{ intros a Ha. rewrite (Hk7 a ltac:(lia) ltac:(lia)). rewrite (KC a ltac:(lia) ltac:(lia) ltac:(lia)). apply K6. lia. }
destruct (rx_ffacts B FFL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ pos HJ7 Hfin6) as (_ & _ & _ & _ & _ & _ & HFLp7 & _ & _).
fold F FL in HFLp7.
pose proof RG7 as (_ & Q73 & Q74 & Q78 & _ & _ & _ & _).
assert (B22 : bv_unsigned (ew (Ereg regs7 (rx_X7 FL regs)) 22) = F)
  by (rewrite (rx_ew_reg regs7 _ 22 (Z_to_bv 5 22) ltac:(vm_compute; reflexivity)), R722; apply unsigned_lit_small; lia).
assert (B8 : bv_unsigned (ew (Ereg regs7 (rx_X7 FL regs)) 8) = S0)
  by (rewrite (rx_ew_reg regs7 _ 8 (Z_to_bv 5 8) ltac:(vm_compute; reflexivity)), Q78; apply unsigned_lit_small; lia).
assert (E32 : ew (Ereg regs7 (rx_X7 FL regs)) 32 = Z_to_bv 64 FL) by exact (ew_Ereg_extra regs7 (rx_X7 FL regs) 0).
assert (B32 : bv_unsigned (ew (Ereg regs7 (rx_X7 FL regs)) 32) = FL) by (rewrite E32; apply unsigned_lit_small; lia).
assert (HS : st_ok rsegs (Ereg regs7 (rx_X7 FL regs))
  (mkSS RX_RA3 sr_atoms
     [ YP09.mkRegion (Some 22%nat) 0x1f8 0x200 0 0 [YP09.mkChunk 0x1f8 (CVal 8 (SOff 32 0))];
       YP09.mkRegion (Some 32%nat) 0 1 0 1 [];
       YP09.mkRegion (Some 8%nat) (-104) 0 0 0 rx_sv_chunks ]
     None (mkFacts [] [] []))
  (restrict (w_H W6) (mkst regs7 (Z_to_bv 64 RX_RA3) mem7 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite B22. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val rsegs _ _ F 0x1f8 8 (SOff 32 0) FL).
      * cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E32.
      * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
      * cbn. lia.
      * change (N.to_nat 8) with 8%nat.
        apply (val_mem_kept rsegs (w_H W4) (w_H W6) mem4 mem7); [intros k Hk; apply K7; lia | exact HFW4].
    + rewrite B32. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. replace (FL + o) with FL by lia. apply (apresent_writable rsegs). exact HFLp7.
    + rewrite B8. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      unfold rx_sv_chunks. rewrite Forall_map. apply Forall_forall. intros j Hj. apply in_seq in Hj.
      apply (chunk_ok_val rsegs _ _ S0 (-8 - 8 * Z.of_nat j) 8 (SOff (32 + Nat.succ j) 0)
        (bv_unsigned (getr regs (nth j rh_saved_regs 0%bv)))).
      * cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ew_Ereg_extra regs7 (rx_X7 FL regs) (Nat.succ j)).
        unfold rx_X7. cbn [nth]. rewrite Z_to_bv_bv_unsigned. destruct Hj as [_ Hj]. unfold rh_saved_regs.
        do 13 (destruct j as [|j]; [reflexivity|]). lia.
      * pose proof (bv_unsigned_in_range 64 (getr regs (nth j rh_saved_regs 0%bv))) as Y.
        change (bv_modulus 64) with (2 ^ 64) in Y. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
      * cbn. lia.
      * change (N.to_nat 8) with 8%nat.
        apply (val_mem_kept rsegs (w_H W4) (w_H W6) mem4 mem7); [intros k Hk; apply K7; lia | apply HSV4; lia].
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite B22, B32, B8.
    repeat split; first [exact I | lia].
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
change (Z_to_bv 64 RX_RA3) with (Z_to_bv 64 RX_RA3).
rx_run_flag HS HJ7 HL Hsegs ML Hwx HASF FFL.
- lia.
- intros a (r & Hin & Ha). cbn [ss_mem In] in Hin.
  destruct Hin as [<-|[<-|[<-|[]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
  rewrite ?B22, ?B32, ?B8 in Ha; [exfalso; lia | right; rewrite EFL6; lia | exfalso; lia].
- intros msr HSr. rewrite EFL6, <- B32. apply (rx_flag0_of rsegs _ _ msr 32 HSr). cbn [ss_mem In]. right. left. reflexivity.
- rx_mach HS msD.
  eapply (SRr_ret_at rsegs rx_tbl rx_tbl_ok Hwx W6 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'. cbv beta.
  rx_ext HS (1%bv : bv 5) Rf1. unfold rx_X7 in Rf1. cbn [nth map rh_saved_regs] in Rf1.
  rx_lit HS (10%bv : bv 5) Rf10.
  lazymatch goal with |- exists _ _ _ _ _ _, mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ =>
    exists ly6, (stack_free_state 3 pos S6), rg, mm, mdx, 4 end.
  split.
  { unfold cfg_at. rewrite Rf1. unfold YK0s.ret_ok in Hraok. rewrite Hraok.
    unfold w64. rewrite <- Hra. unfold raZ. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  split.
  { unfold rh_j. cbn [h_ly h_S h_W h_regs h_mem h_md]. apply (ajournal_materialize rsegs B HL Hsegs). exact HJ7. }
  split; [unfold RH_EV; lia|].
  split.
  { intros r Hr. unfold acallee_saved in Hr.
    assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
      r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    clear Hr. z5 Q78. z5 Q73. z5 Q74.
    destruct Hr' as [->|[->|[->|Hr']]].
    - z5g. rx_atom HS (2%bv : bv 5) (8%bv : bv 5) Hx. rewrite Hx, Q78.
      change S0 with (spZ regs). unfold spZ, w64. apply Z_to_bv_bv_unsigned.
    - z5g. rx_atom HS (3%bv : bv 5) (3%bv : bv 5) Hx. rewrite Hx, Q73. symmetry. exact Hgp0.
    - z5g. rx_atom HS (4%bv : bv 5) (4%bv : bv 5) Hx. rewrite Hx, Q74. symmetry. exact Htp0.
    - destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]; z5g;
      lazymatch goal with |- getr _ ?rr = _ => rx_ext HS rr Hx end;
      rewrite Hx; unfold rx_X7; reflexivity. }
  split; [rewrite Rf10; reflexivity|].
  unfold ablocks. rewrite blocks_stack_free_state. fold (ablocks B ly6 S6). exact HPerm6.
Qed.
End m.

Print Assumptions rx_S_X01.
