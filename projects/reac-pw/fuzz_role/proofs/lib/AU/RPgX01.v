(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of proofs/cgif/cgif_file_fuzzer/lib/A/AC8v.v:120-122
   [Apache-2.0]; proofs/cgif/cgif_file_fuzzer/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   proofs/cgif/cgif_rgb_fuzzer/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v at origin/ossv/recipes 6ebe35ba632; its three generic lemmas L_set_shadow_at, L_fresh and L_chain are kept as rx_set_shadow_at, rx_fresh and rx_chain (rx_set_shadow_at takes the kit's ajournal_after_write, which the strong shadow-fill text allows, in place of L_after_write_win), module paths changed to reac_pw.fuzz_role; the segment walk of reac-pw/fuzz_role's image A below is new. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgX01.v at 9bffaa83ff88; module paths changed to reac_pw.fuzz_rate and the prefix rx_ to rtx_; the segment is reac-pw/fuzz_rate's image A (K82ed4 -> the return: three frees, the first from s5 and the other two from real-frame cells, three scope stores, F loaded from the real-frame cells R+0x18 / R+0x78, the shadow fill, the flag byte, the epilogue), stated by lib/A/RtPgSeg.v S_X01 with the float state the cut carries; the allocator's free and the shadow fill are Section hypotheses at every float state; rx_fresh, unused, is dropped. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgX01.v at e12d19af3990 for image B (fuzz_rate.asan-ubsan) as lib/AU/RtPgX01B.v: the prefix rtx_ to rtxb_, image B's pcs, its free trampoline and shadow-fill entry, its real-frame cells (F from R+0x10 / R+0x60, pp R+0x168, pod R+0x178) and real frame (0x220 bytes), the frame for locals of class 4 (1024 bytes, 128 shadow bytes, the flag pointer word at F+0x3f8, the frame's shadow base in s3), one scope store (hz) in place of three, stated by lib/AU/RtPgSegB.v S_X01. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/RtPgX01B.v at 520bcea9ec2f for reac-pw/fuzz_role's image B (fuzz_role.asan-ubsan) as lib/AU/RPgX01.v: module paths changed to reac_pw.fuzz_role and the prefix rtxb_ to rx_; role's segment C4 -> the return: two frees from the registers s2 (pod) and s6 (pp), as lib/A/RPgX01.v has them, in place of three (two of them from real-frame cells); one scope store (the role cell's granule 84); F read from the real-frame cell R+0x20 into s7 and the retirement word stored through s10 = F; the real frame is 0x200 bytes; the four events of role's run; image B's pcs, free trampoline 0x524bc and shadow-fill entry 0x54134; stated by lib/AU/RPgHarn.v S_X01 with lib/AU/RPgImgA.v role_himg_B. *)
(* reac-pw/fuzz_role image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; every address measured on the unstripped twin
   dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a, same loaded bytes): SEGMENT S_X01 of the walk
   of LLVMFuzzerTestOneInput (0x80020), from C4 = 0x82570 (after check_code returns) through J8258c to the return.
   Proves lib/AU/RPgHarn.v S_X01 at image B's segments (kind: segment lemma).

   THE CODE (37 words 0x82570 .. 0x82600, all 4-byte encodings; the three words 0x825b4 .. 0x825bc are dead):
     run 1  0x82570 mv a0,s2; 0x82574 jal 0x524bc            free(pod) through the free trampoline, ra 0x82578
     run 2  0x82578 mv a0,s6; 0x8257c jal 0x524bc            free(pp), ra 0x82580
     run 3  0x82580 addi a0,zero,-8; 0x82584 sb a0,0x54(s3)  the role cell's shadow byte (granule 84) back to 0xf8
            0x82588 ld s7,0x20(s1)                          s7 = F (the cell R+0x20)
            0x8258c lui/addiw a0 = 0x45e0360e; 0x82594 sd a0,0(s10)   F[0] := the retirement word (J8258c; s10 = F)
            0x82598 beqz s7,0x825b4                         NOT taken: s7 = F >= 4096 (an atom fact), so the
                                                            real-stack arm 0x825b4 .. 0x825bc (li a1,88; mv a0,s3;
                                                            jal __asan_set_shadow_00 0x5402c) is dead
            0x8259c addi a1,zero,0x80; 0x825a0 mv a0,s3; 0x825a4 jal 0x54134   __asan_set_shadow_f5(shadow F, 128)
     run 4  0x825a8 ld a0,0x3f8(s7); 0x825ac sb zero,0(a0)  the flag byte of the class-4 frame := 0 (the release)
            0x825b0 j 0x825c0; 0x825c0 addi a0,zero,0; 0x825c4 addi sp,s0,-0x200; 13 restores 0x825c8 .. 0x825f8
            (ra, s0, s1, s2 .. s11 from S-8 .. S-0x68); 0x825fc addi sp,sp,0x200; 0x82600 ret.
   The two frees go through the kit's aj_free_at (YCbq.v) with the allocator's afree_realizes; the shadow fill
   through rx_set_shadow_at with the strong shadow-fill text (lib/Reusable/SetShadowDef.v); the flag store through
   rx_run_flag (YCbq.v aj_flag_store, with astack_free_law_ok and the frame flag law), which drops the frame from
   the journal's own list; the return through SRr_ret_at. The walk runs at the float state fx the cut C4 carries
   (no instruction of the segment reads or writes a float register or fcsr, and its callees' contracts keep the
   configuration's float state), and that fx is the return's. No branch of the segment reaches an `unimp` word or
   an error-path call: its one conditional branch, `beqz s7` 0x82598, is decided by the fact F >= 4096. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import SetShadowDef.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YG0s YO0f YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Layout.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import RPgImgA RPgHarn RPgSteps.
Require OSSVerify.reac_pw.fuzz_role.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* image B's loaded segments, the term lib/AU/RPgSteps.v names *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_role.images.AsanUbsan.M.loaded_segments.

(* ============================================ the image ============================================ *)
Definition RX_NW : nat := 37.
Definition rx_tbl : ctable := build_table rsegs RH_C4 RX_NW TEmpty.
Lemma rx_tbl_ok : table_ok rsegs rx_tbl.
Proof. apply build_table_ok0. unfold RH_C4. lia. Qed.
Definition RX_FREE : Z := 0x524bc.      (* __interceptor_trampoline_free *)
Definition RX_SSF5 : Z := 0x54134.      (* __asan_set_shadow_f5 *)
Definition RX_RA1 : Z := 0x82578.       (* free(pod)'s return *)
Definition RX_RA2 : Z := 0x82580.       (* free(pp)'s return *)
Definition RX_RA3 : Z := 0x825a8.       (* __asan_set_shadow_f5's return *)

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
(* the eight registers the segment reads from its start values: sp, gp, tp, s0 = S, s1 = R, s3 = the frame's shadow
   base, s6 = pp, s10 = F *)
Definition rx_regs (regs : bvmap 5 word) (R gp tp S shF pp F : Z) : Prop :=
getr regs (Z_to_bv 5 2) = w64 R /\ getr regs (Z_to_bv 5 3) = w64 gp /\ getr regs (Z_to_bv 5 4) = w64 tp /\
getr regs (Z_to_bv 5 8) = w64 S /\ getr regs (Z_to_bv 5 9) = w64 R /\ getr regs (Z_to_bv 5 19) = w64 shF /\
getr regs (Z_to_bv 5 22) = w64 pp /\ getr regs (Z_to_bv 5 26) = w64 F.
Lemma rx_regs_pres : forall r1 r2 R gp tp S shF pp F,
aregs_preserved r1 r2 -> rx_regs r1 R gp tp S shF pp F -> rx_regs r2 R gp tp S shF pp F.
Proof.
intros r1 r2 R gp tp S shF pp F HP (A2 & A3 & A4 & A8 & A9 & A19 & A22 & A26).
unfold rx_regs. rewrite !HP by (unfold acallee_saved; lia). repeat split; assumption.
Qed.
Lemma rx_regs_run : forall segs ss ms H regs extra R gp tp S shF pp F,
st_ok segs (Ereg regs extra) ss (restrict H ms) ->
forallb (fun k : Z => sv_eqb (sr_get (ss_regs ss) (Z_to_bv 5 k)) (SOff (Z.to_nat k) 0)) [2; 3; 4; 8; 9; 19; 22; 26]
  = true ->
rx_regs regs R gp tp S shF pp F -> rx_regs (ms_regs ms) R gp tp S shF pp F.
Proof.
intros segs ss ms H regs extra R gp tp S shF pp F HS Hck (A2 & A3 & A4 & A8 & A9 & A19 & A22 & A26).
assert (K : forall k, In k [2; 3; 4; 8; 9; 19; 22; 26] -> getr (ms_regs ms) (Z_to_bv 5 k) = getr regs (Z_to_bv 5 k)).
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
(* the 64-bit word of a cell value read modulo 2^64 *)
Lemma rx_w64_mod : forall x, Z_to_bv 64 (x mod 2 ^ 64) = Z_to_bv 64 x.
Proof.
intros x. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
apply Z.mod_mod. lia.
Qed.
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
(* the symbolic state of a call return whose run loads one 8-byte cell R + off (s1 = R) holding v (atom 32) *)
Lemma rx_entry_cell : forall pc (W : world rsegs) regs mem R off v,
getr regs (Z_to_bv 5 9) = w64 R -> 0 <= R -> R + off + 8 <= 2 ^ 64 -> 0 <= off -> 0 <= v < 2 ^ 64 ->
regions_wf [YP09.mkRegion (Some 9%nat) off (off + 8) 0 0 [YP09.mkChunk off (CVal 8 (SOff 32 0))]] = true ->
val_mem rsegs (mrestrict (w_H W) mem) (R + off) 8 v ->
st_ok rsegs (Ereg regs [Z_to_bv 64 v])
(mkSS pc sr_atoms [YP09.mkRegion (Some 9%nat) off (off + 8) 0 0 [YP09.mkChunk off (CVal 8 (SOff 32 0))]]
   None (mkFacts [] [] []))
(restrict (w_H W) (mkst regs (Z_to_bv 64 pc) mem (seg_rom rsegs))).
Proof.
intros pc W regs mem R off v H9 HR0 HRhi HRlo Hv Hwf Hval.
assert (B9 : bv_unsigned (ew (Ereg regs [Z_to_bv 64 v]) 9) = R).
{ rewrite (rx_ew_reg regs _ 9 (Z_to_bv 5 9) ltac:(vm_compute; reflexivity)), H9. apply unsigned_lit_small. lia. }
rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
- apply regs_ok_Ereg.
- exact Hwf.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite B9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val rsegs _ _ R off 8 (SOff 32 0) v).
  + cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact (ew_Ereg_extra regs [Z_to_bv 64 v] 0).
  + change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact Hv.
  + cbn. lia.
  + change (N.to_nat 8) with 8%nat. exact Hval.
- cbn [pairwise_disjoint all_disjoint]. tauto.
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
(* the frame for locals (class 4, 1024 bytes, 128 shadow bytes) and its flag at a state of the journal *)
Lemma rx_ffacts : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k pos,
ajournal rsegs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k -> In (4, pos) (frames S') ->
frame_addr ly 4 pos mod 32 = 0 /\ in_app (frame_addr ly 4 pos) 1024 /\
4096 <= frame_addr ly 4 pos /\ frame_addr ly 4 pos + 1024 <= alloc_ceiling /\
(forall a, frame_addr ly 4 pos <= a < frame_addr ly 4 pos + 1024 -> apresent (w_H W') mem' a /\ ~ aowned B ly' S' a) /\
(forall i, 0 <= i < 128 -> apresent (w_H W') mem' (shadow_addr (frame_addr ly 4 pos) + i)) /\
apresent (w_H W') mem' (flag_addr ly 4 pos) /\ aowned B ly' S' (flag_addr ly 4 pos) /\
4096 <= flag_addr ly 4 pos < alloc_ceiling.
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k pos HJ Hin.
pose proof (AR_laws_ok rsegs B) as HL. pose proof (proj1 HJ) as HAR.
destruct (rx_jF STK sp0 FP ly S W mem md own ly' S' W' mem' md' k 4 pos HJ) as [EFA EFL].
destruct (al_frames _ _ HL _ _ _ _ _ 4 pos HAR Hin) as (HFal & HFapp & HFpres & HFSpres).
destruct (frames_bounds rsegs B HL _ _ _ _ _ 4 pos HAR Hin) as (HF4096 & HFceil & _).
destruct (FFL _ _ _ _ _ 4 pos HAR Hin) as (HFLp & HFLo & _ & (HFL4096 & _ & HFLceil)).
rewrite EFA in HFal, HFapp, HFpres, HFSpres, HF4096, HFceil. rewrite EFL in HFLp, HFLo, HFL4096, HFLceil.
change (fs_frame_bytes 4) with 1024 in *. change (1024 / 8) with 128 in HFSpres.
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
   argument happens to unify, so this file carries the full count. *)
Ltac rx_run_flag HS HJ HL Hsegs ML Hwx HASF FFL :=
lazymatch type of HS with st_ok ?segs ?E ?ss (restrict (w_H ?W) ?ms) =>
let r := eval vm_compute in (sym_runN segs rx_tbl FUEL ss) in
lazymatch r with (?ss', ?st) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_runN segs rx_tbl FUEL ss = (ss', st)) by (vm_compute; reflexivity);
eapply (aj_flag_store segs _ HL Hsegs ML rx_tbl rx_tbl_ok Hwx HASF FFL W FUEL E ss ss' st ms
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS Hrun I HJ);
[ clear Hrun | clear Hrun | clear Hrun | clear Hrun HS HJ; aj_after_run HS HJ ] end end.
(* the release's symbolic state: the flag pointer word F+0x3f8 (atom 32 = the flag address), the flag byte, and the
   13 saves at S-8 .. S-0x68 (atom 33 + j = the entry's j-th saved register) *)
Definition rx_sv_chunks : list YP09.chunk :=
map (fun j => YP09.mkChunk (-8 - 8 * Z.of_nat j) (CVal 8 (SOff (32 + Nat.succ j) 0))) (seq 0 13).
Definition rx_X8 (fl : Z) (regs : bvmap 5 word) : list word :=
Z_to_bv 64 fl :: map (fun r => getr regs r) rh_saved_regs.

(* ======================================= the segment ======================================= *)
Section m. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK : Z.
(* the allocator's laws and its free operation (at every float state, as YG0d.AsanAPI's aa_free states it), the
   side stack's flag law, the shadow fill (at every float state), the image's free entry and the call traces of the
   two free sites, the harness's stack and event budgets *)
Hypothesis ML : model_laws (as_universe B).
Hypothesis HAPI : api_env rsegs B.
Hypothesis AFREE : forall {fx : YK11.FPState}, afree_realizes rsegs B.
Hypothesis FFL : frame_flag_lawP rsegs B.
Hypothesis ASHF5 : forall {fx : YK11.FPState}, aset_shadow_realizes rsegs B RX_SSF5 0xf5.
Hypothesis HFREE : pc_wrap_free (as_code B) = RX_FREE.
Hypothesis HTRACE : forall c,
In c [[RX_RA1]; [RX_RA1; RA_LLVMF]; [RX_RA2]; [RX_RA2; RA_LLVMF]] ->
In (firstn kUnwindMax (pc_free_ra0 (as_code B) :: flat_map (fun r => if r =? pc_free_ra0 (as_code B) then [] else [r]) c))
(as_universe B).
Hypothesis HSTK : ASTACK + RH_RSZ + 16 <= LLVMF_STK.
Hypothesis HEV : 4 <= EV_LIB.

Theorem rx_S_X01_B : S_X01 rsegs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
Proof.
unfold S_X01, rh_from_C4.
intros hx HB fx pos e rest ly4 S4 W4 regs4 mem4 md4 HC.
destruct hx as [ly S W regs mem md p n pl].
unfold rh_ret. unfold rh_base in HB. unfold rh_cut_C4, rh_common, rh_j, rh_geo, rh_kept in HC.
cbn [h_ly h_S h_W h_regs h_mem h_md h_p h_n h_pl] in HB, HC |- *.
destruct HB as (HPRE & Hra & _ & _ & _ & _ & _ & Hfr0 & Hev0 & _ & _).
destruct HC as ((HJ & Hfrs4 & HPerm & Hfresh & R2 & R3 & R4 & (ES & ER & EF) & _ & _ & HCUT & HKEPT) &
  Hnpp & Hnpod & _ & Hfrm).
pose proof rl_wx as Hwx. pose proof rl_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as HL. pose proof (astack_free_law_ok rsegs B) as HASF.
pose proof (@AFREE fx) as HAFREE. pose proof (@ASHF5 fx) as HASHF5.
pose proof HPRE as (HAR0 & Hraok & Hra4 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
pose proof Hstk0 as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Has : ASTACK = 16384) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
unfold RH_CID, RH_RSZ in *.
rewrite !Forall_cons_iff in Hfresh. destruct Hfresh as (Hnpp0 & Hnpod0 & _).
(* ---- the cut's quantities ---- *)
set (S0 := spZ regs) in *.
set (F := frame_addr ly 4 pos) in *.
set (FL := flag_addr ly 4 pos) in *.
set (R := e_R e) in *. set (pp := e_pp e) in *. set (pod := e_pod e) in *.
set (len := e_len e) in *.
assert (HS064 : 0 <= S0 < 2 ^ 64) by (subst S0; unfold spZ; pose proof (bv_unsigned_in_range 64 (getr regs 2)) as X;
  change (bv_modulus 64) with (2 ^ 64) in X; lia).
assert (HR : R mod 16 = 0 /\ S0 - 0x210 <= R <= S0 - 0x200).
{ rewrite ER, ES.
  pose proof (Z.div_mod (S0 - 512) 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (S0 - 512) 32 ltac:(lia)) as M.
  pose proof (Z.div_mod S0 16 ltac:(lia)) as D16. rewrite Hal16, Z.add_0_r in D16.
  set (q := (S0 - 512) / 32) in *. set (r := (S0 - 512) mod 32) in *. set (u := S0 / 16) in *.
  split; [replace (32 * q) with ((2 * q) * 16) by lia; apply Z_mod_mult | lia]. }
destruct HR as (HR16 & HRlo & HRhi).
assert (HRc : alloc_ceiling + ASTACK <= R) by lia.
assert (Ho16 : (R - S0) mod 16 = 0) by (rewrite Zminus_mod, HR16, Hal16; reflexivity).
(* ---- the frame for locals and its flag ---- *)
assert (Hfin4 : In (4, pos) (frames S4)) by (rewrite Hfrs4; left; reflexivity).
destruct (rx_ffacts B FFL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ pos HJ Hfin4)
  as (HFal & HFapp & HF4096 & HFceil & HFpres4 & HFSpres4 & HFLp4 & HFLo4 & HFLr).
fold F FL in HFal, HFapp, HF4096, HFceil, HFpres4, HFSpres4, HFLp4, HFLo4, HFLr.
set (shF := shadow_addr F) in *.
assert (HshF : shF = SHADOW_OFF + F / 8) by reflexivity.
pose proof (Z.div_mod F 8 ltac:(lia)) as D8. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as M8.
assert (HdFS : shF + 128 <= F \/ F + 1024 <= shF).
{ rewrite HshF. unfold SHADOW_OFF.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. destruct HFapp as (_ & [Hlow | [Hhi1 Hhi2]]); [right; lia | left; lia]. }
assert (HshC : 0 <= shF /\ shF + 128 <= alloc_ceiling) by (rewrite HshF; unfold SHADOW_OFF; lia).
assert (HdFFL : FL + 1 <= F \/ F + 1024 <= FL).
{ destruct (Z_lt_ge_dec FL F) as [Hlt|Hge]; [left; lia|].
  destruct (Z_lt_ge_dec FL (F + 1024)) as [Hlt2|Hge2]; [exfalso | right; lia].
  exact (proj2 (HFpres4 FL ltac:(lia)) HFLo4). }
(* ---- the cut's registers and cells (role_himg_B's hi_L4: s2 = pod, s0 = S, s1 = R, s3 = shF, s6 = pp, s10 = F,
   and the cell R+0x20 = F) ---- *)
unfold rl_cut in HCUT. cbn [hi_L4 role_himg_B] in HCUT. rewrite !Forall_cons_iff in HCUT.
destruct HCUT as (C18 & C8 & C9 & C19 & C22 & C26 & C20c & _).
cbn [fst snd rl_at rl_xv] in C18, C8, C9, C19, C22, C26, C20c.
fold R pp pod in C18, C9, C22, C20c. rewrite ES in C8. rewrite EF in C19, C26, C20c.
fold F shF in C19, C26, C20c.
rewrite Z.add_0_r in C22.
assert (HC20 : val_mem rsegs (mrestrict (w_H W4) mem4) (R + 0x20) 8 F) by (rewrite Z.mod_small in C20c by lia; exact C20c).
clear C20c.
unfold rh_cells in HKEPT. apply Forall_app in HKEPT as [HKS HKF].
assert (HSV4 : forall j, (j < 13)%nat -> val_mem rsegs (mrestrict (w_H W4) mem4) (S0 + (-8 - 8 * Z.of_nat j)) 8
  (bv_unsigned (getr regs (nth j rh_saved_regs 0%bv)))).
{ intros j Hj. unfold rh_saves_L in HKS. rewrite Forall_map in HKS.
  pose proof (proj1 (Forall_forall _ _) HKS j ltac:(apply in_seq; lia)) as X. cbn [fst snd rl_at rl_xv] in X.
  rewrite ES in X. rewrite Z.mod_small in X; [exact X|]. pose proof (bv_unsigned_in_range 64 (getr regs (nth j rh_saved_regs 0%bv))) as Y.
  change (bv_modulus 64) with (2 ^ 64) in Y. exact Y. }
clear HKS.
assert (HFW4 : val_mem rsegs (mrestrict (w_H W4) mem4) (F + 0x3f8) 8 FL).
{ apply Forall_cons_iff in HKF as [X _]. cbn [fst snd rl_at rl_xv] in X. rewrite EF in X. fold F FL in X.
  rewrite Z.mod_small in X by lia. exact X. }
clear HKF.
assert (RG4 : rx_regs regs4 R (as_gp B) (as_tp B) S0 shF pp F).
{ unfold rx_regs. z5g. repeat split; first [exact R2 | exact R3 | exact R4 | (z5 C8; exact C8) | (z5 C9; exact C9)
  | (z5 C19; exact C19) | (z5 C22; exact C22) | (z5 C26; exact C26)]. }
clear R2 R3 R4 C8 C9 C19 C22 C26.
pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hra64. change (bv_modulus 64) with (2 ^ 64) in Hra64.
pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hs064. change (bv_modulus 64) with (2 ^ 64) in Hs064.
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
(* ---- run 1: 0x82570 .. the jal of free(pod), a0 = s2 ---- *)
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
pose proof HJ as (_ & Hly4 & _). destruct Hly4 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop4 & _).
(* ---- free(pod) at 0x524bc, ra 0x82578 ---- *)
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
destruct (rx_jF B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 4 pos HJ) as [EFA4 EFL4].
pose proof (sep_block_frame rsegs B HL ly4 S4 W4 (ms_mem msA) _ pod len 4 pos (proj1 HJ) Hpod4 Hfin4) as Hdpod.
rewrite EFA4 in Hdpod. fold F in Hdpod. unfold zdisjoint in Hdpod. cbn [fst snd] in Hdpod. change (fs_frame_bytes 4) with 1024 in Hdpod.
eapply SRr_bind.
{ rewrite (st_ok_restrict_mkst rsegs (w_H W4) _ _ msA HS eq_refl) at 1. cbn [ss_pc].
  replace (Z_to_bv 64 0x524bc) with (Z_to_bv 64 (pc_wrap_free (as_code B))) by (rewrite HFREE; reflexivity).
  eapply (aj_free_at rsegs B HL Hsegs HAPI ML HAFREE W4 (ms_regs msA) (ms_mem msA) LLVMF_STK S0 [] ly S W mem md
    [(4, pos)] ly4 S4 _ 2 pod len (R - S0) (Z_to_bv 64 RX_RA1) ch HJ).
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
  - intros Hin. exfalso. exact (Hnpod0 Hin). }
cbv beta. intros W5 c5 Hwle5 (ly5 & S5 & regs5 & mem5 & md5 & -> & HJ5 & HP5 & (l1 & l2 & E1 & E2) & Hfrs5 & HK5).
clear HS Hch Hchs ch HRD1 HRD2.
pose proof (rx_regs_pres _ _ _ _ _ _ _ _ _ HP5 RGA) as RG5.
assert (HPerm5 : Permutation (ablocks B ly5 S5) (ablocks B ly S ++ [(pp, Layout.PP_SIZE)])).
{ rewrite E2. rewrite E1 in HPerm.
  replace (ablocks B ly S ++ [(pp, Layout.PP_SIZE); (pod, len)])
    with ((ablocks B ly S ++ [(pp, Layout.PP_SIZE)]) ++ (pod, len) :: []) in HPerm
    by (rewrite <- app_assoc; reflexivity).
  rewrite <- (app_nil_r (ablocks B ly S ++ [(pp, Layout.PP_SIZE)])).
  exact (Permutation_app_inv l1 l2 _ [] (pod, len) HPerm). }
assert (Hfin5 : In (4, pos) (frames S5)) by (rewrite Hfrs5; exact Hfin4).
(* what the first free kept: the real frame [R, S) (the saves and the cell of F) and the flag pointer word *)
assert (K5 : forall a, (R <= a < S0 \/ F + 0x3f8 <= a < F + 0x400) ->
  aview rsegs (w_H W5) mem5 a = aview rsegs (w_H W4) mem4 a).
{ intros a Ha. rewrite <- (KA a). destruct HK5 as (K1 & _ & _ & K4 & _).
  destruct Ha as [Ha | Ha].
  - apply K1; lia.
  - apply (K4 4 pos a Hfin4); [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite EFA4; change (fs_frame_bytes 4) with 1024; fold F; lia | lia]. }
clear HK5.
(* ---- run 2: 0x82578 .. the jal of free(pp), a0 = s6 ---- *)
pose proof (rx_entry0 RX_RA1 W5 regs5 mem5) as HS.
change (w64 RX_RA1) with (Z_to_bv 64 RX_RA1).
aj_run rx_tbl_ok HS HJ5.
{ apply awr_ok_nil. }
rx_mach HS msC.
assert (HmC : forall x, ms_mem msC x = mem5 x) by (intros x; apply HF; intros (r & Hr & _); cbn in Hr; destruct Hr).
clear HF HFr HG.
pose proof RG5 as (_ & _ & _ & _ & _ & _ & Q522 & _).
rx_atom HS (10%bv : bv 5) (22%bv : bv 5) Rc0. z5 Q522. rewrite Q522 in Rc0.
rx_lit HS (1%bv : bv 5) Rrc.
pose proof (rx_regs_run rsegs _ msC (w_H W5) regs5 [] _ _ _ _ _ _ _ HS ltac:(vm_compute; reflexivity) RG5) as RGC.
pose proof RGC as (QC2 & QC3 & QC4 & QC8 & _ & _ & _ & _). z5 QC2. z5 QC3. z5 QC4. z5 QC8.
assert (EspC : spZ (ms_regs msC) = R) by (unfold spZ; rewrite QC2; unfold w64; apply unsigned_lit_small; lia).
assert (Es0C : s0Z (ms_regs msC) = S0) by (unfold s0Z; rewrite QC8; unfold w64; apply unsigned_lit_small; lia).
assert (EraC : raZ (ms_regs msC) = RX_RA2) by (unfold raZ, RX_RA2; rewrite Rrc; apply unsigned_lit_small; lia).
assert (KC : forall a, (R <= a < S0 \/ F + 0x3f8 <= a < F + 0x400) ->
  aview rsegs (w_H W5) (ms_mem msC) a = aview rsegs (w_H W4) mem4 a)
  by (intros a Ha; rewrite (rx_aview_same rsegs _ _ _ a HmC); exact (K5 a Ha)).
destruct (HRD W5 (ms_mem msC) ltac:(intros a Ha; apply KC; lia)) as [HRD1 HRD2].
pose proof HJ5 as (_ & Hly5 & _). destruct Hly5 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop5 & _).
destruct (rx_chain ly5 (aview rsegs (w_H W5) (ms_mem msC)) (aview rsegs (w_H W) mem) (ms_regs msC) S0 R (raZ regs) (s0Z regs) ly
  EspC Es0C ltac:(rewrite EraC; unfold RX_RA2; lia) ltac:(lia) ltac:(lia) Hal16 HRD1 HRD2 Hra4 Hch0
  ltac:(symmetry; exact Etop5) ltac:(rewrite Etop5; lia)) as (ch & Hch & Hchs).
{ intros a Ha. pose proof HJ5 as (_ & _ & _ & _ & _ & _ & _ & _ & J1 & _). apply J1; lia. }
assert (Hpp5 : In (pp, Layout.PP_SIZE) (ablocks B ly5 S5)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm5|]. apply in_or_app. right. left. reflexivity. }
destruct (rx_jF B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 4 pos HJ5) as [EFA5 EFL5].
pose proof (sep_block_frame rsegs B HL ly5 S5 W5 (ms_mem msC) _ pp Layout.PP_SIZE 4 pos (proj1 HJ5) Hpp5 Hfin5) as Hdpp.
rewrite EFA5 in Hdpp. fold F in Hdpp. unfold zdisjoint in Hdpp. cbn [fst snd] in Hdpp. change (fs_frame_bytes 4) with 1024 in Hdpp.
eapply SRr_bind.
{ rewrite (st_ok_restrict_mkst rsegs (w_H W5) _ _ msC HS eq_refl) at 1. cbn [ss_pc].
  replace (Z_to_bv 64 0x524bc) with (Z_to_bv 64 (pc_wrap_free (as_code B))) by (rewrite HFREE; reflexivity).
  eapply (aj_free_at rsegs B HL Hsegs HAPI ML HAFREE W5 (ms_regs msC) (ms_mem msC) LLVMF_STK S0 [] ly S W mem md
    [(4, pos)] ly5 S5 _ 3 pp Layout.PP_SIZE (R - S0) (Z_to_bv 64 RX_RA2) ch HJ5).
  - exact Hpp5.
  - exact Rc0.
  - lia.
  - exact Ho16.
  - lia.
  - lia.
  - exact QC3.
  - exact QC4.
  - exact Rrc.
  - apply ret_ok_even. vm_compute. reflexivity.
  - pose proof HJ5 as (_ & _ & _ & _ & _ & _ & Hnev & _). lia.
  - exact Hch.
  - rewrite call_trace_of_spine, EraC. destruct Hchs as [-> | (fp & v & ->)].
    + apply (HTRACE [RX_RA2]). cbn [In]. right. right. left. reflexivity.
    + rewrite Hra. apply (HTRACE [RX_RA2; RA_LLVMF]). cbn [In]. right. right. right. left. reflexivity.
  - intros Hin. exfalso. exact (Hnpp0 Hin). }
cbv beta. intros W7 c7 Hwle7 (ly7 & S7 & regs7 & mem7 & md7 & -> & HJ7 & HP7 & (n1 & n2 & E5 & E6) & Hfrs7 & HK7).
clear HS Hch Hchs ch HRD1 HRD2.
pose proof (rx_regs_pres _ _ _ _ _ _ _ _ _ HP7 RGC) as RG7.
assert (HPerm7 : Permutation (ablocks B ly7 S7) (ablocks B ly S)).
{ rewrite E6. rewrite E5 in HPerm5. rewrite <- (app_nil_r (ablocks B ly S)).
  exact (Permutation_app_inv n1 n2 _ [] (pp, Layout.PP_SIZE) HPerm5). }
assert (Hfin7 : In (4, pos) (frames S7)) by (rewrite Hfrs7; exact Hfin5).
assert (K7 : forall a, (R <= a < S0 \/ F + 0x3f8 <= a < F + 0x400) ->
  aview rsegs (w_H W7) mem7 a = aview rsegs (w_H W4) mem4 a).
{ intros a Ha. rewrite <- (KC a Ha). destruct HK7 as (K1 & _ & _ & K4 & _).
  destruct Ha as [Ha | Ha].
  - apply K1; lia.
  - apply (K4 4 pos a Hfin5); [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite EFA5; change (fs_frame_bytes 4) with 1024; fold F; lia | lia]. }
clear HK7.
clear K5 KA KC HmA HmC Ra0 Rc0 Rra Rrc Hdpod Hdpp E1 E2 E5 E6 HPerm HPerm5
  Hpod4 Hpp5 RGA RG4 RG5 EFA4 EFL4 EFA5 EFL5 Hwle5 Hwle7 HJ HJ5
  QA2 QA3 QA4 QA8 QC2 QC3 QC4 QC8 EspA Es0A EraA EspC Es0C EraC Etop4 Etop5
  HP5 HP7 Q522 C18 HFpres4 HFSpres4 HFLp4 HFLo4.
(* ---- run 3: 0x82580 .. the jal of __asan_set_shadow_f5: the role cell's scope store, F from R+0x20 into s7,
   F[0] := 0x45e0360e through s10, the side-stack test ---- *)
destruct (rx_ffacts B FFL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ pos HJ7 Hfin7)
  as (_ & _ & _ & _ & HFpres7 & HFSpres7 & _ & _ & _).
fold F FL shF in HFpres7, HFSpres7.
destruct (rx_jF B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 4 pos HJ7) as [EFA7 EFL7]. fold F FL in EFA7, EFL7.
pose proof RG7 as (Q72 & Q73 & Q74 & Q78 & Q79 & Q719 & Q722 & Q726).
assert (B19 : bv_unsigned (ew (Ereg regs7 [Z_to_bv 64 F]) 19) = shF)
  by (rewrite (rx_ew_reg regs7 _ 19 (Z_to_bv 5 19) ltac:(vm_compute; reflexivity)), Q719; apply unsigned_lit_small; lia).
assert (B9 : bv_unsigned (ew (Ereg regs7 [Z_to_bv 64 F]) 9) = R)
  by (rewrite (rx_ew_reg regs7 _ 9 (Z_to_bv 5 9) ltac:(vm_compute; reflexivity)), Q79; apply unsigned_lit_small; lia).
assert (B26 : bv_unsigned (ew (Ereg regs7 [Z_to_bv 64 F]) 26) = F)
  by (rewrite (rx_ew_reg regs7 _ 26 (Z_to_bv 5 26) ltac:(vm_compute; reflexivity)), Q726; apply unsigned_lit_small; lia).
assert (E32F : ew (Ereg regs7 [Z_to_bv 64 F]) 32 = Z_to_bv 64 F) by exact (ew_Ereg_extra regs7 [Z_to_bv 64 F] 0).
assert (B32 : bv_unsigned (ew (Ereg regs7 [Z_to_bv 64 F]) 32) = F) by (rewrite E32F; apply unsigned_lit_small; lia).
assert (HS : st_ok rsegs (Ereg regs7 [Z_to_bv 64 F])
  (mkSS RX_RA2 sr_atoms
     [ YP09.mkRegion (Some 19%nat) 0x54 0x55 0x54 0x55 [];
       YP09.mkRegion (Some 9%nat) 0x20 0x28 0 0 [YP09.mkChunk 0x20 (CVal 8 (SOff 32 0))];
       YP09.mkRegion (Some 26%nat) 0 8 0 8 [] ]
     None (mkFacts [(32%nat, mkAF 4096 0x800000000000 5)] [] []))
  (restrict (w_H W7) (mkst regs7 (Z_to_bv 64 RX_RA2) mem7 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite B19. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable rsegs). apply HFSpres7. lia.
    + rewrite B9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val rsegs _ _ R 0x20 8 (SOff 32 0) F).
      * cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E32F.
      * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
      * cbn. lia.
      * change (N.to_nat 8) with 8%nat.
        apply (val_mem_kept rsegs (w_H W4) (w_H W7) mem4 mem7); [intros k Hk; apply K7; lia | exact HC20].
    + rewrite B26. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable rsegs). apply (proj1 (HFpres7 (F + o) ltac:(lia))).
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite B19, B9, B26.
    repeat split; first [exact I | lia].
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. split; [|exact I].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite B32. change (2 ^ 5) with 32. lia. }
change (w64 RX_RA2) with (Z_to_bv 64 RX_RA2).
aj_run rx_tbl_ok HS HJ7.
{ eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 19%nat shF); [reflexivity | exact B19 | |].
  { cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. right. right. right. exists 4, pos. split; [left; reflexivity|]. right.
    unfold in_zr. cbn [fst snd]. rewrite EFA7. change (fs_frame_bytes 4 / 8) with 128. fold shF. lia. }
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 26%nat F); [reflexivity | exact B26 | |].
  { cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. right. right. right. exists 4, pos. split; [left; reflexivity|]. left.
    unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA7. change (fs_frame_bytes 4) with 1024. lia. }
  apply awr_ok_nil. }
rx_mach HS msD.
assert (KD : forall a, 0 <= a < 2 ^ 64 -> ~ (shF + 0x54 <= a < shF + 0x55) -> ~ (F <= a < F + 8) ->
  aview rsegs (w_H W7) (ms_mem msD) a = aview rsegs (w_H W7) mem7 a).
{ intros a Ha H1 H2. apply aview_eq_of. apply HFr. rewrite unsigned_lit_small by lia. intros (r & Hin & Hw).
  cbn in Hin. destruct Hin as [<-|[<-|[<-|[]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
  rewrite ?B19, ?B9, ?B26 in Hw; lia. }
clear HF HFr HG.
rx_atom HS (10%bv : bv 5) (Z_to_bv 5 19) Rd0. rewrite Q719 in Rd0.
rx_ext HS (23%bv : bv 5) Rd23. cbn [nth] in Rd23.
rx_lit HS (11%bv : bv 5) Rd1.
rx_lit HS (1%bv : bv 5) Rrd.
pose proof (rx_regs_run rsegs _ msD (w_H W7) regs7 _ _ _ _ _ _ _ _ HS ltac:(vm_compute; reflexivity) RG7) as RGD.
pose proof RGD as (QD2 & QD3 & QD4 & _ & _ & _ & _ & _). z5 QD2. z5 QD3. z5 QD4.
assert (EspD : spZ (ms_regs msD) = R) by (unfold spZ; rewrite QD2; unfold w64; apply unsigned_lit_small; lia).
(* ---- __asan_set_shadow_f5(shadow F, 128) at 0x54134, ra 0x825a8 ---- *)
eapply SRr_bind.
{ rewrite (st_ok_restrict_mkst rsegs (w_H W7) _ _ msD HS eq_refl) at 1. cbn [ss_pc].
  replace (Z_to_bv 64 0x54134) with (Z_to_bv 64 RX_SSF5) by reflexivity.
  eapply (rx_set_shadow_at rsegs B HL Hsegs RX_SSF5 0xf5 HASHF5 W7 (ms_regs msD) (ms_mem msD) LLVMF_STK S0 [] ly S W mem md
    [(4, pos)] ly7 S7 _ 4 4 pos shF 128 (R - S0) (Z_to_bv 64 RX_RA3) HJ7).
  - left. reflexivity.
  - exact Rd0.
  - exact Rd1.
  - lia.
  - rewrite EFA7. fold shF. lia.
  - rewrite EFA7. fold shF. change (fs_frame_bytes 4 / 8) with 128. lia.
  - lia.
  - exact Ho16.
  - lia.
  - lia.
  - exact QD3.
  - exact QD4.
  - exact Rrd.
  - apply ret_ok_even. vm_compute. reflexivity. }
cbv beta. intros W8 c8 Hwle8 (-> & regs8 & mem8 & md8 & -> & HJ8 & HP8 & HAR8 & Hf5 & Hk8).
clear HS.
(* ---- run 4: 0x825a8 .. the ret: the flag byte through s7 = F, a0 = 0, the epilogue ---- *)
pose proof (rx_regs_pres _ _ _ _ _ _ _ _ _ HP8 RGD) as RG8.
assert (R823 : getr regs8 (Z_to_bv 5 23) = w64 F) by (rewrite (HP8 23 ltac:(unfold acallee_saved; lia)); z5g; exact Rd23).
assert (K8 : forall a, (S0 - 0x68 <= a < S0 \/ F + 0x3f8 <= a < F + 0x400) ->
  aview rsegs (w_H W7) mem8 a = aview rsegs (w_H W4) mem4 a).
{ intros a Ha. rewrite (Hk8 a ltac:(lia) ltac:(lia)). rewrite (KD a ltac:(lia) ltac:(lia) ltac:(lia)). apply K7. lia. }
destruct (rx_ffacts B FFL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ pos HJ8 Hfin7) as (_ & _ & _ & _ & _ & _ & HFLp8 & _ & _).
fold F FL in HFLp8.
pose proof RG8 as (_ & Q83 & Q84 & Q88 & _ & _ & _ & _).
assert (B23 : bv_unsigned (ew (Ereg regs8 (rx_X8 FL regs)) 23) = F)
  by (rewrite (rx_ew_reg regs8 _ 23 (Z_to_bv 5 23) ltac:(vm_compute; reflexivity)), R823; apply unsigned_lit_small; lia).
assert (B8 : bv_unsigned (ew (Ereg regs8 (rx_X8 FL regs)) 8) = S0)
  by (rewrite (rx_ew_reg regs8 _ 8 (Z_to_bv 5 8) ltac:(vm_compute; reflexivity)), Q88; apply unsigned_lit_small; lia).
assert (E32 : ew (Ereg regs8 (rx_X8 FL regs)) 32 = Z_to_bv 64 FL) by exact (ew_Ereg_extra regs8 (rx_X8 FL regs) 0).
assert (B32' : bv_unsigned (ew (Ereg regs8 (rx_X8 FL regs)) 32) = FL) by (rewrite E32; apply unsigned_lit_small; lia).
assert (HS : st_ok rsegs (Ereg regs8 (rx_X8 FL regs))
  (mkSS RX_RA3 sr_atoms
     [ YP09.mkRegion (Some 23%nat) 0x3f8 0x400 0 0 [YP09.mkChunk 0x3f8 (CVal 8 (SOff 32 0))];
       YP09.mkRegion (Some 32%nat) 0 1 0 1 [];
       YP09.mkRegion (Some 8%nat) (-104) 0 0 0 rx_sv_chunks ]
     None (mkFacts [] [] []))
  (restrict (w_H W7) (mkst regs8 (Z_to_bv 64 RX_RA3) mem8 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite B23. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val rsegs _ _ F 0x3f8 8 (SOff 32 0) FL).
      * cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E32.
      * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
      * cbn. lia.
      * change (N.to_nat 8) with 8%nat.
        apply (val_mem_kept rsegs (w_H W4) (w_H W7) mem4 mem8); [intros k Hk; apply K8; lia | exact HFW4].
    + rewrite B32'. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. replace (FL + o) with FL by lia. apply (apresent_writable rsegs). exact HFLp8.
    + rewrite B8. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      unfold rx_sv_chunks. rewrite Forall_map. apply Forall_forall. intros j Hj. apply in_seq in Hj.
      apply (chunk_ok_val rsegs _ _ S0 (-8 - 8 * Z.of_nat j) 8 (SOff (32 + Nat.succ j) 0)
        (bv_unsigned (getr regs (nth j rh_saved_regs 0%bv)))).
      * cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ew_Ereg_extra regs8 (rx_X8 FL regs) (Nat.succ j)).
        unfold rx_X8. cbn [nth]. rewrite Z_to_bv_bv_unsigned. destruct Hj as [_ Hj]. unfold rh_saved_regs.
        do 13 (destruct j as [|j]; [reflexivity|]). lia.
      * pose proof (bv_unsigned_in_range 64 (getr regs (nth j rh_saved_regs 0%bv))) as Y.
        change (bv_modulus 64) with (2 ^ 64) in Y. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
      * cbn. lia.
      * change (N.to_nat 8) with 8%nat.
        apply (val_mem_kept rsegs (w_H W4) (w_H W7) mem4 mem8); [intros k Hk; apply K8; lia | apply HSV4; lia].
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite B23, B32', B8.
    repeat split; first [exact I | lia].
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
change (w64 RX_RA3) with (Z_to_bv 64 RX_RA3).
rx_run_flag HS HJ8 HL Hsegs ML Hwx HASF FFL.
- lia.
- intros a (r & Hin & Ha). cbn [ss_mem In] in Hin.
  destruct Hin as [<-|[<-|[<-|[]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
  rewrite ?B23, ?B32', ?B8 in Ha; [exfalso; lia | right; rewrite EFL7; lia | exfalso; lia].
- intros msr HSr. rewrite EFL7, <- B32'. apply (rx_flag0_of rsegs _ _ msr 32 HSr). cbn [ss_mem In]. right. left. reflexivity.
- rx_mach HS msE.
  eapply (SRr_ret_at rsegs rx_tbl rx_tbl_ok Hwx W7 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'. cbv beta.
  rx_ext HS (1%bv : bv 5) Rf1. unfold rx_X8 in Rf1. cbn [nth map rh_saved_regs] in Rf1.
  rx_lit HS (10%bv : bv 5) Rf10.
  lazymatch goal with |- exists _ _ _ _ _ _ _, mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ =>
    exists fx, ly7, (stack_free_state 4 pos S7), rg, mm, mdx, 4 end.
  split.
  { unfold cfg_at. rewrite Rf1. unfold YK0s.ret_ok in Hraok. rewrite Hraok.
    unfold w64. rewrite <- Hra. unfold raZ. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  split; [exact Hfrm|].
  split.
  { unfold rh_j. cbn [h_ly h_S h_W h_regs h_mem h_md]. apply (ajournal_materialize rsegs B HL Hsegs). exact HJ8. }
  split; [unfold RH_EV; lia|].
  split.
  { intros r Hr. unfold acallee_saved in Hr.
    assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
      r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    clear Hr. z5 Q88. z5 Q83. z5 Q84.
    destruct Hr' as [->|[->|[->|Hr']]].
    - z5g. rx_atom HS (2%bv : bv 5) (8%bv : bv 5) Hx. rewrite Hx, Q88.
      change S0 with (spZ regs). unfold spZ, w64. apply Z_to_bv_bv_unsigned.
    - z5g. rx_atom HS (3%bv : bv 5) (3%bv : bv 5) Hx. rewrite Hx, Q83. symmetry. exact Hgp0.
    - z5g. rx_atom HS (4%bv : bv 5) (4%bv : bv 5) Hx. rewrite Hx, Q84. symmetry. exact Htp0.
    - destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]; z5g;
      lazymatch goal with |- getr _ ?rr = _ => rx_ext HS rr Hx end;
      rewrite Hx; unfold rx_X8; reflexivity. }
  split; [rewrite Rf10; reflexivity|].
  unfold ablocks. rewrite blocks_stack_free_state. fold (ablocks B ly7 S7). exact HPerm7.
Qed.
End m.
