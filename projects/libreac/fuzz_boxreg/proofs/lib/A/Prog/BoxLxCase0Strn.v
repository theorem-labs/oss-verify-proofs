(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntrySetGa0), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntrySetGa0.v, with its module paths and module names changed; 671 of its 703 lines of code are new or changed and 147 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput's case 0 (declare, fuzz_boxreg.c:262-268) on the ASan build: the piece B -> S between the
   inner cuts of BoxLxCase0Defs.v. From the cut B (0x809d8, bcmp returned 0 for a placed row) the code checks the new
   row against Pau's model and calls strncmp on its name:
     0x809d8  bnez a0 -> 0x80f60            a0 = 0 at B (pinned to the literal, so the engine takes no branch);
     0x809dc  the pinned field (row + 0x14), its shadow test (slow path 0x80d90 -> report 0x80fd0) decided by the
              row's shadow entry (the block law), then `bne` -> 0x80f60 refuted by declare_placed: pinned = (base >= 0);
     0x80a00  bltz s10 (s10 = base << 56): base < 0 skips the base test; else the base field (row + 8) with its
              shadow test (slow path 0x80ddc -> report 0x80fe4) and `bne a0, s11` -> 0x80f60 refuted (the row's base is
              the given base);
     0x80a20  a1 = the name (slot 0x58), or "" (A_OBJ 5) when op & 8; s3 = r + 56 idx, a0 = s3 + 0x18 (the row's
              name field), a2 = 31; `jal` the strncmp trampoline (return 0x80a4c = C0_S).
   The call is applied through c0s_strncmp_at, the composition of StrncmpDef.v's astrncmp_realizes with the caller's
   journal (Reusable/YCbq.v aj_bcmp_at's shape). The field holds the first 31 characters of the name and a NUL
   (name_field), the second string is the name (or ""), so the two agree on 31 bytes and the answer is 0.
   The strncmp statement's read-only views: fm_rom_viewN (every read-only byte that is no owned static and no errno
   byte reads as the image byte) comes at the call from the arodata_okP of gb_base, carried by the journal
   (BoxBase.v arodata_ok_journalP, with the RO context) and read by pa's lib/A/Rt/StrncmpView.v fm_rom_viewN_of_arodata;
   fm_rom_viewO (the owned statics) is the Section hypothesis HROMO, true in every AR state. HEMP5 is the "" global in
   the asn_rom_str form: its NUL is a read-only image byte (no owned static, no errno byte), read through fm_rom_viewN;
   the rest of the NUL's 8-byte word are image bytes (owned right redzone), present through any overlay. *)

From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YI16 YC5d YM05 YG0s YImgTop.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal BoxSyms BoxList BoxPa BoxPaLib BoxBase.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import YC4b YC1g YC1h YC85 BoxFrame BoxCJ BoxRo.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import ReacBoxregInit BoxLxDefs ReadName.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require Import SnprintfDef StrncmpDef StrncmpView.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Boxreg BoxregUpd LLVMFuzzerTestOneInput_inv.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require LLVMFuzzerTestOneInput_case0 LLVMFuzzerTestOneInput_rn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require read_name_c reac_boxreg_declare_c printf_facts_c.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import BoxLxCase0Defs.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require LowestFreeBase BoxTailVis.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg box_listing}.
Context {RO : ro_below_ofl (@pa_segs _ box_listing PI) pa_relro_lo pa_relro_hi}.
#[local] Notation SEGS := (@pa_segs _ box_listing PI).
#[local] Notation VAL := (@pa_val _ box_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ box_listing PI).
#[local] Notation BASE := (@pa_val _ box_listing PI A_TEXT).
Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ASTRNCMP : astrncmp_realizes SEGS B (SIGMA BS___interceptor_trampoline_strncmp).
Hypothesis HISV : img_shadow_vis SEGS B.
Hypothesis HGLOB : globs_marked SEGS B BX_G.
Hypothesis HMRG : Forall (fun g => IMG_LO + 64 <= fst g /\ fst g + snd g + 64 <= IMG_HI) BX_G.
Hypothesis HEMP5 : asn_rom_str SEGS B (VAL (A_OBJ 5)) [].
Hypothesis HROMO : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> fm_rom_viewO SEGS B W mem.

(* The strncmp wrapper called inside the caller's journal (the shape of Reusable/YCbq.v aj_bcmp_at): its window
   [sp - 2 ESTACK, sp) is present and below the caller's frame, so ecall_pre comes from the journal
   (ecall_pre_at) and the write set is that window (ajournal_after_write). *)
Lemma c0s_strncmp_at : forall pc, astrncmp_realizes SEGS B pc ->
  forall W (regsT : bvmap 5 word) memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y n (l1 l2 : list Z) (o : Z) raw,
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
  getr regsT 10 = w64 x -> getr regsT 11 = w64 y -> getr regsT 12 = w64 n -> 0 <= n < 2 ^ 63 ->
  fm_rom_viewN SEGS B W memT -> fm_rom_viewO SEGS B W memT ->
  fm_cstr_ok SEGS W memT x l1 -> fm_cstr_ok SEGS W memT y l2 ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom SEGS)) mdc)
  (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2 (v : Z),
     c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
     ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
     aregs_preserved regsT regs2 /\ getr regs2 10 = w64 v /\ 0 <= v < 2 ^ 64 /\
     (v = 0 <-> fm_strn_eq (Z.to_nat n) l1 l2) /\
     (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) ->
        aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) /\
     (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros pc AS W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y n l1 l2 o raw
  HJ Hsp Hal Hneg Hbud Hgp Htp Hra Hraw Ha0 Ha1 Ha2 Hn Hrom Hclean Hc1 Hc2.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HPRE : ecall_pre SEGS B lyc Sc W regsT memT mdc).
{ eapply (ecall_pre_at SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o); try eassumption; [lia|].
  rewrite Hra. exact Hraw. }
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (HPREK : fm_ecall_pre_k SEGS B FM_STK_RT_STR lyc Sc W regsT memT mdc).
{ unfold fm_ecall_pre_k, FM_STK_RT_STR. split; [exact HPRE|].
  split; [rewrite Eslo; unfold ASAN_CEIL; lia|]. split; [rewrite Eslo, Hsp; lia|].
  intros a Ha. apply Hpres. rewrite Hsp in Ha. lia. }
eapply SRr_mono.
{ exact (AS lyc Sc W regsT memT mdc x y n l1 l2 HPREK Hrom Hclean Ha0 Ha1 Ha2 Hn Hc1 Hc2). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HAR2 & HP & Hsame & Hres & Hvr & Hiff & Hfr & Hpres2).
unfold FM_STK_RT_STR in Hfr. rewrite Hsp in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2, v.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write SEGS B LAWS pa_segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
    (fun a => sp0 + o - 2 * ESTACK <= a < sp0 + o) Sc own HJ).
  - intros a Ha Hna. apply (Hfr a Ha). exact Hna.
  - exact Hpres2.
  - exact Hsame.
  - intros a Ha; left; left; lia.
  - exact HAR2.
  - reflexivity. - reflexivity. - lia. - exact Hfrs. - exact HQT. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hvr|]. split; [exact Hiff|]. split; [exact Hfr | exact Hpres2].
Qed.

Lemma c0s_skipn_cons : forall {A} (l : list A) k d, (k < length l)%nat -> skipn k l = nth k l d :: skipn (S k) l.
Proof.
intros A l. induction l as [|x l IH]; intros k d Hk; cbn [length] in Hk; [lia|].
destruct k as [|k]; [reflexivity|]. cbn [skipn nth]. apply IH. lia.
Qed.
Lemma c0s_bsub1 : forall (l : list byte) o, 0 <= o -> (Z.to_nat o < length l)%nat ->
  Boxreg.bsub l o 1 = [nth (Z.to_nat o) l (Z_to_bv 8 0)].
Proof.
intros l o Ho Hl. unfold Boxreg.bsub. change (Z.to_nat 1) with 1%nat.
rewrite (c0s_skipn_cons l (Z.to_nat o) (Z_to_bv 8 0) Hl). reflexivity.
Qed.
Lemma c0s_placed_eq : forall bs b k p s, c0_placed bs b k p s = reac_boxreg_declare_c.decl_bytes bs b k p s.
Proof. intros. reflexivity. Qed.
Lemma c0s_rd_pin : forall bs b k p s, length bs = 288%nat -> 0 <= Boxreg.bx_n bs <= 4 -> -2^31 <= p < 2^31 ->
  Boxreg.rd4 (c0_placed bs b k p s) (56 * Boxreg.bx_n bs + 20) = p.
Proof.
intros bs b k p s HL Hn Hp. rewrite c0s_placed_eq. apply BoxregUpd.rd4_le4; [exact Hp|].
rewrite LLVMFuzzerTestOneInput_case0.c0_row_bsub by lia. reflexivity.
Qed.
Lemma c0s_rd_base : forall bs b k p s, length bs = 288%nat -> 0 <= Boxreg.bx_n bs <= 4 -> -2^31 <= b < 2^31 ->
  Boxreg.rd4 (c0_placed bs b k p s) (56 * Boxreg.bx_n bs + 8) = b.
Proof.
intros bs b k p s HL Hn Hb. rewrite c0s_placed_eq. apply BoxregUpd.rd4_le4; [exact Hb|].
rewrite LLVMFuzzerTestOneInput_case0.c0_row_bsub by lia. reflexivity.
Qed.

Lemma c0s_name_byte : forall bs b k p s j, length bs = 288%nat -> 0 <= Boxreg.bx_n bs <= 4 -> 0 <= j < 32 ->
  nth (Z.to_nat (56 * Boxreg.bx_n bs + 24 + j)) (c0_placed bs b k p s) (Z_to_bv 8 0) =
  nth (Z.to_nat j) (reac_boxreg_declare_c.name_field s) (Z_to_bv 8 0).
Proof.
intros bs b k p s j HL Hn Hj.
pose proof (LLVMFuzzerTestOneInput_case0.c0_row_bsub bs b k p s (24 + j) 1 HL Hn ltac:(lia) ltac:(lia) ltac:(lia)) as E.
rewrite <- c0s_placed_eq in E.
assert (HL' : length (c0_placed bs b k p s) = 288%nat) by (apply LLVMFuzzerTestOneInput_case0.c0_decl_length; lia).
assert (HR : length (reac_boxreg_declare_c.decl_row b k p s) = 56%nat).
{ unfold reac_boxreg_declare_c.decl_row, reac_boxreg_declare_c.name_field, printf_facts_c.pf_bytes.
  rewrite !length_app, repeat_length, !Mem.length_le4, length_map, repeat_length, length_firstn. lia. }
rewrite Z.add_assoc in E.
rewrite !c0s_bsub1 in E by (try rewrite HL'; try rewrite HR; lia). injection E as E. rewrite E.
replace (Z.to_nat (24 + j)) with (24 + Z.to_nat j)%nat by lia. reflexivity.
Qed.

Definition C0S_SB : Z := 0x7fff8000.
Definition C0S_SPAN : Z * Z := (C0S_SB, C0S_SB + 2 ^ 44 - 1).
Definition C0S_R58 : YP09.region := YP09.mkRegion (Some 9%nat) 0x58 0x60 0 0 [YP09.mkChunk 0x58 (CVal 8 (SOff 32 0))].
Definition C0S_ROW : YP09.region :=
  YP09.mkRegion (Some 22%nat) 8 24 0 0 [YP09.mkChunk 8 (CVal 4 (SOff 33 0)); YP09.mkChunk 20 (CVal 4 (SOff 34 0))].
Definition C0S_SH : list shent := [mkSHE 22 0 56].
Definition C0S_F : facts := mkFacts [(18%nat, mkAF C0S_SB C0S_SB 0); (22%nat, mkAF 4096 0x7fffff800000 3)] [] [].

Lemma c0s_pb : forall bs k base b p, reac_boxreg_declare_c.declare_placed bs k base b p -> Boxreg.boxreg_B2 bs ->
  0 <= b <= 40 /\ ((p = 1 /\ b = base /\ 0 <= base) \/ (p = 0 /\ base < 0)).
Proof.
intros bs k base b p ((Hev & Hk & Hkf) & Hn & HP) HB2. unfold Boxreg.boxreg_B2 in HB2.
destruct HP as [(H0 & -> & -> & H1 & H2 & _) | (H0 & -> & H1 & [(H2 & _) | (H2 & H3 & _)])]; lia.
Qed.

Lemma c0s_swrap64 : forall z, -2 ^ 63 <= z < 2 ^ 63 -> bv_swrap 64 (zcanon z) = z.
Proof.
intros z Hz. unfold zcanon, M64, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64). change (2 ^ 64 / 2) with (2 ^ 63). Z.div_mod_to_equations. lia.
Qed.
Lemma c0s_U_atom : forall E m v, ew E m = Z_to_bv 64 v -> -2 ^ 63 <= v < 2 ^ 63 -> U E (SOff m 0) = zcanon v.
Proof.
intros E m v F Hv. rewrite U_SOff, F, Z.add_0_r. unfold zcanon, M64. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. lia.
Qed.
Lemma c0s_pin_cond : forall E p base, ew E 34 = Z_to_bv 64 p -> ew E 27 = Z_to_bv 64 base ->
  0 <= p <= 1 -> -128 <= base < 128 ->
  branch_taken BC_NE (sv_denot E (SExt true 32 (SOff 34 0)))
    (sv_denot E (SAlu ALU_XOR (SAlu ALU_SLT (SOff 27 0) (SLit 0)) (SLit 1))) = negb (p =? (if base <? 0 then 0 else 1)).
Proof.
intros E p base F34 F27 Hp Hb.
rewrite branch_ne_U, U_SExt, !U_SAlu. rewrite (c0s_U_atom E 34 p F34) by lia. rewrite (c0s_U_atom E 27 base F27) by lia. rewrite !U_SLit.
rewrite (c0_zcanon_in p) by lia. change (zcanon 0) with 0. change (zcanon 1) with 1.
cbn [zalu_raw]. rewrite (c0s_swrap64 base) by lia. change (bv_swrap 64 0) with 0.
rewrite (Z.mod_small p) by (change (2 ^ Z.of_N 32) with (2 ^ 32); lia).
assert (Hsw : bv_swrap 32 p = p) by (unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus; change (2 ^ Z.of_N 32) with (2 ^ 32);
  change (2 ^ 32 / 2) with (2 ^ 31); Z.div_mod_to_equations; lia).
rewrite Hsw, (c0_zcanon_in p) by lia.
destruct (Z.ltb_spec base 0); cbn [Z.lxor]; [change (zcanon (Z.lxor 1 1)) with 0 | change (zcanon (Z.lxor 0 1)) with 1]; reflexivity.
Qed.

Lemma c0s_lt_cond : forall E base, ew E 26 = Z_to_bv 64 (base * 2 ^ 56) -> -128 <= base < 128 ->
  branch_taken BC_LT (sv_denot E (SOff 26 0)) (sv_denot E (SLit 0)) = (base <? 0).
Proof.
intros E base F26 Hb. cbn [branch_taken]. rewrite c0_denot_off0, F26. cbn [sv_denot].
apply LLVMFuzzerTestOneInput_case0.c0_lts56. exact Hb.
Qed.
Lemma c0s_base_cond : forall E b base, ew E 33 = Z_to_bv 64 b -> ew E 27 = Z_to_bv 64 base ->
  0 <= b <= 40 -> -128 <= base < 128 ->
  branch_taken BC_NE (sv_denot E (SExt true 32 (SOff 33 0))) (sv_denot E (SOff 27 0)) = negb (b =? base).
Proof.
intros E b base F33 F27 Hb Hbase.
rewrite branch_ne_U, U_SExt. rewrite (c0s_U_atom E 33 b F33) by lia. rewrite (c0s_U_atom E 27 base F27) by lia.
rewrite (c0_zcanon_in b) by lia.
rewrite (Z.mod_small b) by (change (2 ^ Z.of_N 32) with (2 ^ 32); lia).
assert (Hsw : bv_swrap 32 b = b) by (unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus; change (2 ^ Z.of_N 32) with (2 ^ 32);
  change (2 ^ 32 / 2) with (2 ^ 31); Z.div_mod_to_equations; lia).
rewrite Hsw, (c0_zcanon_in b) by lia.
destruct (Z.ltb_spec base 0).
- rewrite (c0_zcanon_neg base) by lia. destruct (Z.eqb_spec b (base + 2 ^ 64)); destruct (Z.eqb_spec b base); try reflexivity; lia.
- rewrite (c0_zcanon_in base) by lia. reflexivity.
Qed.

Lemma c0s_frame_eq : forall E rs (m m' : word -> option byte), frame_of E rs m m' ->
  forallb (fun rr => YP09.r_whi rr <=? YP09.r_wlo rr) rs = true -> forall x, m' x = m x.
Proof.
intros E rs m m' HF Hw x. apply HF. intros (rr & Hin & Ha).
rewrite forallb_forall in Hw. specialize (Hw rr Hin). apply Z.leb_le in Hw. lia.
Qed.
Ltac c0s_mem ms3 MALL :=
  match goal with HF : frame_of _ _ (ms_mem ?o) (ms_mem ?nw) |- _ =>
    let M := fresh "M" in
    let Q := fresh "Q" in
    pose proof (c0s_frame_eq _ _ _ _ HF) as Q;
    specialize (Q ltac:(vm_compute; reflexivity));
    assert (M : forall x, ms_mem nw x = ms_mem ms3 x) by (intros x; rewrite (Q x); apply MALL);
    clear MALL HF Q; rename M into MALL end;
  repeat match goal with
  | H : frame_of _ _ _ _ |- _ => clear H
  | H : mem_grows _ _ |- _ => clear H
  end.

(* A block of at most 48 bytes is a primary chunk: it lies in a 2 ^ 32 region of the high memory whose end is below
   the allocator's ceiling (case 3's c3_margin argument, with the region's lower bound kept). *)
Lemma c0s_margin : forall ly S W mem md p n,
  AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n <= 48 ->
  kHighMemBeg <= p /\ p + 65536 <= alloc_ceiling.
Proof.
  intros ly S W mem md p n (M & _) Hin Hn.
  apply In_ablocks in Hin as (k & Hk & Hst & Hu & Hnk).
  pose proof (chunk_facts B ly S _ k M Hk) as CF. unfold cfacts in CF.
  destruct CF as (Happ & Hceil & Hb16 & Husr & Hrz & Hrzm & Hreq & Hroom & Hcase).
  pose proof (am_layout _ _ _ _ M) as LO.
  pose proof (req_size_pos (ck_req k) ltac:(lia)) as [Hq1 _].
  remember (ck_beg k) as bg eqn:Eb. destruct bg as [|off|rr o|cc q]; try (solve [destruct Hcase]).
  - destruct Hcase as (Hc & Hfp & Hcl & Hext & Hbase & Hx0 & Hxa & Hxs & Hra).
    pose proof (region_in_prim ly (prim_class off) LO ltac:(lia)) as (R1 & R2 & R3 & R4 & R5).
    unfold ASAN_CEIL in R5. rewrite <- Hu, Husr, Hbase. lia.
  - destruct Hcase as (Ho & Hfp & _). exfalso. rewrite Hnk in Hfp.
    unfold from_primary, needed_primary, rounded_size, rz_size, kMaxSize, round_up in Hfp.
    replace (rz_log n) with 0 in Hfp by (unfold rz_log; replace (n <=? 48) with true by (symmetry; apply Z.leb_le; lia); reflexivity).
    rewrite Z.shiftl_0_r in Hfp. apply Z.leb_gt in Hfp.
    assert (Hm : Z.max n 8 <= 48) by lia.
    assert (Hd : (Z.max n 8 + 8 - 1) / 8 * 8 <= 48) by (Z.div_mod_to_equations; lia). lia.
Qed.

Lemma c0s_u8 : forall c, 0 <= c < 256 -> bv_unsigned (Z_to_bv 8 c) = c.
Proof. intros c Hc. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact Hc. Qed.

Lemma c0s_val_mem1 : forall H (m : word -> option byte) a v,
  aview SEGS H m a = Some v -> val_mem SEGS (mrestrict H m) a 1 v.
Proof.
intros H m a v Hv j Hj.
destruct (aview_byte SEGS H m a v Hv) as (b & Hm & Hbv & Hr).
assert (j = 0%nat) as -> by lia. rewrite Z.add_0_r, Hm. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
unfold YO0f.le_byte. change (8 * Z.of_nat 0) with 0. change (2 ^ (8 * Z.of_nat 1)) with 256.
rewrite Z.shiftr_0_r, !Z.mod_mod by lia. rewrite Z.mod_small by lia. symmetry. exact Hbv.
Qed.
Lemma c0s_garr8 : forall H (m : word -> option byte) p (l : list Z),
  (forall j, 0 <= j < Z.of_nat (length l) -> aview SEGS H m (p + j) = Some (nth (Z.to_nat j) l 0)) ->
  garr8 SEGS (mrestrict H m) p l.
Proof.
intros H m p l Hv j Hj. pose proof (Hv (Z.of_nat j) ltac:(lia)) as Hj'. rewrite Nat2Z.id in Hj'.
split; [exact (c0s_val_mem1 H m _ _ Hj')|].
destruct (aview_byte SEGS H m _ _ Hj') as (b & _ & _ & Hr). exact Hr.
Qed.
Lemma c0s_firstn_nz : forall (s : list Z), Forall (fun c => 0 < c < 256) s -> Forall (fun c => c <> 0) (firstn 31 s).
Proof.
intros s Hs. apply Forall_forall. intros c Hc. rewrite <- (firstn_skipn 31 s) in Hs.
apply Forall_app in Hs as [Hs _]. rewrite Forall_forall in Hs. specialize (Hs c Hc). lia.
Qed.
Lemma c0s_strn_eq : forall s : list Z, fm_strn_eq 31 (firstn 31 s) s.
Proof.
  intros s. unfold fm_strn_eq.
  rewrite !firstn_app, firstn_firstn, length_firstn.
  destruct (Nat.le_gt_cases 31 (length s)) as [Hs|Hs].
  - rewrite (Nat.min_l 31 (length s)) by lia. rewrite Nat.min_id, Nat.sub_diag.
    replace (31 - length s)%nat with 0%nat by lia. reflexivity.
  - rewrite (Nat.min_r 31 (length s)) by lia. rewrite Nat.min_id. reflexivity.
Qed.
(* The name field of the placed row: the first 31 characters of s, then a NUL, inside the block r. *)
Lemma c0s_cstr_row : forall ly S W mem md r (bs' : list byte) n (s : list Z),
  AR SEGS B ly S W mem md -> In (r, REG_SIZE) (ablocks B ly S) ->
  (forall i, 0 <= i < REG_SIZE -> aview SEGS (w_H W) mem (r + i) = Some (bv_unsigned (nth (Z.to_nat i) bs' (Z_to_bv 8 0)))) ->
  (forall j, 0 <= j < 32 -> nth (Z.to_nat (56 * n + 24 + j)) bs' (Z_to_bv 8 0) =
     nth (Z.to_nat j) (reac_boxreg_declare_c.name_field s) (Z_to_bv 8 0)) ->
  0 <= n <= 4 -> Forall (fun c => 0 < c < 256) s ->
  fm_cstr_ok SEGS W mem (r + 56 * n + 24) (firstn 31 s).
Proof.
intros ly S W mem md r bs' n s HAR Hin HRB HNF Hn Hs.
destruct (al_blocks _ _ LAWS _ _ _ _ _ r REG_SIZE HAR Hin) as (Hr16 & Hr4096 & Hrceil & Hria & Hrpres & _).
change (req_size REG_SIZE) with 288 in *.
set (L := Z.of_nat (length (firstn 31 s))).
assert (HL : 0 <= L <= 31) by (unfold L; rewrite length_firstn; lia).
assert (Hnz : Forall (fun c => c <> 0) (firstn 31 s)) by (apply c0s_firstn_nz; exact Hs).
assert (Hfr : Forall (fun c => 0 < c < 256) (firstn 31 s)).
{ apply Forall_forall. intros c Hc. rewrite <- (firstn_skipn 31 s) in Hs.
  apply Forall_app in Hs as [Hs _]. rewrite Forall_forall in Hs. exact (Hs c Hc). }
assert (HB : forall j, 0 <= j <= L -> aview SEGS (w_H W) mem (r + 56 * n + 24 + j) =
   Some (nth (Z.to_nat j) (firstn 31 s ++ [0]) 0)).
{ intros j Hj. replace (r + 56 * n + 24 + j) with (r + (56 * n + 24 + j)) by lia.
  rewrite HRB by (unfold REG_SIZE; lia). rewrite HNF by lia. f_equal.
  unfold reac_boxreg_declare_c.name_field, printf_facts_c.pf_bytes.
  destruct (Z.lt_ge_cases j L) as [Hlt | Hge].
  - rewrite app_nth1 by (rewrite length_map; unfold L in Hlt; lia).
    rewrite app_nth1 by (unfold L in Hlt; lia).
    rewrite (map_nth (Z_to_bv 8) (firstn 31 s) 0 (Z.to_nat j)).
    assert (Hc : 0 < nth (Z.to_nat j) (firstn 31 s) 0 < 256).
    { rewrite Forall_forall in Hfr. apply Hfr. apply nth_In. unfold L in Hlt. lia. }
    rewrite c0s_u8 by lia. reflexivity.
  - assert (Hj' : Z.to_nat j = length (firstn 31 s)) by (unfold L in *; lia).
    rewrite app_nth2 by (rewrite length_map; lia). rewrite app_nth2 by lia.
    rewrite length_map, Hj', Nat.sub_diag. cbn [nth].
    destruct (32 - Nat.min (length s) 31)%nat as [|q] eqn:Eq; [lia|]. cbn [repeat nth]. rewrite c0s_u8 by lia. reflexivity. }
split; [split; [apply c0s_garr8; rewrite length_app; cbn [length]; intros j Hj; apply HB; unfold L; lia | exact Hnz]|].
split; [lia|]. split; [unfold ASAN_CEIL; fold L; lia|]. split; [fold L; lia|].
split; [fold L; apply (amem_range_of_block SEGS B LAWS ly S W mem md r REG_SIZE); [exact HAR | exact Hin | lia | change (req_size REG_SIZE) with 288; lia]|].
split; [fold L; apply (range_addressable_of_block SEGS B LAWS ly S W mem md r REG_SIZE); [exact HAR | exact Hin | lia | change (req_size REG_SIZE) with 288; lia]|].
split; [fold L; apply (shadow_hull_vis_of_block SEGS B LAWS ly S W mem md r REG_SIZE); [exact HAR | exact Hin | lia | change (req_size REG_SIZE) with 288; lia | lia]|].
fold L. intros a Ha. pose proof (Z.mod_pos_bound (r + 56 * n + 24 + L) 8 ltac:(lia)).
replace a with (r + (a - r)) by lia. rewrite HRB by (unfold REG_SIZE; lia). discriminate.
Qed.

(* A C string s with its NUL at the start of a heap block of at most 48 bytes. *)
Lemma c0s_cstr_blk : forall ly S W mem md p m (s : list Z),
  AR SEGS B ly S W mem md -> In (p, m) (ablocks B ly S) -> 0 <= m <= 48 ->
  (forall j, 0 <= j <= Z.of_nat (length s) -> aview SEGS (w_H W) mem (p + j) = Some (nth (Z.to_nat j) (s ++ [0]) 0)) ->
  Z.of_nat (length s) + 1 <= m -> Forall (fun c => 0 < c < 256) s ->
  fm_cstr_ok SEGS W mem p s.
Proof.
intros ly S W mem md p m s HAR Hin Hm HB Hl Hs.
destruct (al_blocks _ _ LAWS _ _ _ _ _ p m HAR Hin) as (Hp16 & Hp4096 & Hpceil & Hpia & Hppres & _).
pose proof (req_size_pos m ltac:(lia)) as [_ Hrq].
assert (Hrq' : req_size m = m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
rewrite Hrq' in Hppres, Hpceil.
destruct (c0s_margin ly S W mem md p m HAR Hin Hm) as (Hhi & Hmg).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (L := Z.of_nat (length s)) in *.
split; [split; [apply c0s_garr8; rewrite length_app; cbn [length]; intros j Hj; apply HB; unfold L; lia|]|].
{ apply Forall_forall. intros c Hc. rewrite Forall_forall in Hs. specialize (Hs c Hc). lia. }
split; [lia|]. split; [unfold ASAN_CEIL; lia|]. split; [lia|].
split; [apply amem_range_high; [lia | right; lia | lia]|].
split; [apply (range_addressable_of_block SEGS B LAWS ly S W mem md p m); [exact HAR | exact Hin | lia | rewrite Hrq'; lia]|].
split; [apply (shadow_hull_vis_of_block SEGS B LAWS ly S W mem md p m); [exact HAR | exact Hin | lia | rewrite Hrq'; lia | lia]|].
intros a Ha.
destruct (Z.lt_ge_cases a (p + m)) as [Hlt | Hge].
- apply aview_some_of_apresent. apply (proj1 (Hppres a ltac:(lia))).
- apply (BoxTailVis.asn_blk_tail_vis_ok SEGS B ly S W mem md p m a HAR Hin). split; [exact Hge|].
  unfold round_up.
  assert (Hp8 : p mod 8 = 0).
  { pose proof (Z.div_mod p 16 ltac:(lia)) as Hd. rewrite Hp16, Z.add_0_r in Hd. rewrite Hd.
    replace (16 * (p / 16)) with ((p / 16 * 2) * 8) by lia. apply Z_mod_mult. }
  assert (Em : (p + L) mod 8 = L mod 8) by (rewrite Z.add_mod, Hp8 by lia; rewrite Z.add_0_l, Z.mod_mod by lia; reflexivity).
  change (Z.of_nat (length s)) with L in Ha. rewrite Em in Ha.
  assert (Hdl : L - L mod 8 + 8 <= (m + 8 - 1) / 8 * 8) by (Z.div_mod_to_equations; lia).
  lia.
Qed.
(* The "" at A_OBJ 5: one NUL byte of the read-only image, a registered global. *)
Lemma c0s_cstr_emp : forall ly S W mem md, AR SEGS B ly S W mem md -> fm_rom_viewN SEGS B W mem ->
  fm_cstr_ok SEGS W mem (VAL (A_OBJ 5)) [].
Proof.
intros ly S W mem md HAR HRV.
destruct HEMP5 as (H0 & HT).
pose proof HMRG as HM. rewrite Forall_forall in HM. specialize (HM (VAL (A_OBJ 5), 1) ltac:(cbn; tauto)). cbn [fst snd] in HM.
unfold IMG_HI in HM.
destruct (H0 0 ltac:(cbn; lia)) as (Hro & Hown & Herr & Hv). rewrite Z.add_0_r in Hro, Hown, Herr, Hv.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold fm_cstr_ok, fm_cstr.
cbn [length app Z.of_nat]. rewrite !Z.add_0_r.
split; [split; [apply c0s_garr8; cbn [length]; intros j Hj; assert (j = 0) as -> by lia; rewrite Z.add_0_r, (HRV _ Hro Hown Herr), Hv; reflexivity | constructor]|].
split; [lia|]. split; [unfold ASAN_CEIL; lia|]. split; [lia|].
split; [unfold amem_range; left; lia|].
destruct (ro_read_ok_glob SEGS B BX_G ly S W mem md (VAL (A_OBJ 5)) 1 (VAL (A_OBJ 5)) 1 HGLOB ltac:(cbn; tauto) HISV HAR)
  as (HRA & HHV); [lia | lia | lia | lia | unfold IMG_HI; lia |].
split; [exact HRA|]. split; [exact HHV|].
intros a Ha. destruct (HT a) as (_ & Hsa); [unfold asn_word_end; cbn [length Z.of_nat]; rewrite Z.add_0_r; exact Ha|].
exact (aview_some_of_rom SEGS (w_H W) mem a Hsa).
Qed.

(* The name block holds the C string c0_s and its NUL first (read_name's bytes, Pau's nm_split). *)
Lemma c0s_name_str : forall cx (W : world SEGS) ms pos nm, c0_name cx W ms pos nm ->
  (forall j, 0 <= j <= Z.of_nat (length (c0_s cx pos)) ->
     aview SEGS (w_H W) (ms_mem ms) (nm + j) = Some (nth (Z.to_nat j) (c0_s cx pos ++ [0]) 0)) /\
  Z.of_nat (length (c0_s cx pos)) + 1 <= c0_nk cx pos + 1 /\ 0 <= c0_nk cx pos <= 47 /\
  Forall (fun c => 0 < c < 256) (c0_s cx pos).
Proof.
intros cx W ms pos nm HN.
set (l := Boxreg.bsub (c0_pl2 cx pos) 1 (c0_nk cx pos)).
assert (Enb : c0_nb cx pos = l ++ [Z_to_bv 8 0]) by reflexivity.
assert (Es : c0_s cx pos = LLVMFuzzerTestOneInput_rn.nm_str (l ++ [Z_to_bv 8 0])) by reflexivity.
pose proof (LLVMFuzzerTestOneInput_rn.nm_split l) as Hsp. rewrite <- Es in Hsp.
pose proof (LLVMFuzzerTestOneInput_rn.rn_name_len (c0_pl2 cx pos)) as Hll. fold l in Hll.
pose proof (LLVMFuzzerTestOneInput_rn.rn_k_range (c0_pl2 cx pos)) as Hk.
change (read_name_c.rn_k (c0_pl2 cx pos)) with (c0_nk cx pos) in Hll, Hk.
change (Boxreg.bsub (c0_pl2 cx pos) 1 (c0_nk cx pos)) with l in Hll.
pose proof (LLVMFuzzerTestOneInput_rn.nm_str_ok (l ++ [Z_to_bv 8 0])) as Hok. rewrite <- Es in Hok.
assert (Hlen : (length (c0_s cx pos) + 1 <= length (l ++ [Z_to_bv 8 0]))%nat).
{ rewrite Hsp, length_app. unfold printf_facts_c.pf_bytes. rewrite length_map, length_app. cbn [length]. lia. }
rewrite length_app in Hlen. cbn [length] in Hlen.
split; [|split; [lia | split; [lia | exact Hok]]].
intros j Hj. rewrite (HN j) by lia. rewrite Enb, Hsp.
rewrite app_nth1 by (unfold printf_facts_c.pf_bytes; rewrite length_map, length_app; cbn [length]; lia).
unfold printf_facts_c.pf_bytes. rewrite (map_nth (Z_to_bv 8) (c0_s cx pos ++ [0]) 0 (Z.to_nat j)).
assert (Hc : 0 <= nth (Z.to_nat j) (c0_s cx pos ++ [0]) 0 < 256).
{ destruct (Nat.lt_ge_cases (Z.to_nat j) (length (c0_s cx pos))) as [Hlt | Hge].
  - rewrite app_nth1 by lia. rewrite Forall_forall in Hok. pose proof (Hok _ (nth_In _ 0 Hlt)). lia.
  - rewrite app_nth2 by lia. replace (Z.to_nat j - length (c0_s cx pos))%nat with 0%nat by lia. cbn [nth]. lia. }
rewrite c0s_u8 by exact Hc. reflexivity.
Qed.

Lemma c0s_ms_mkst19 : forall cx fp pc (regs regs0 : bvmap 5 word) mem pcv,
  gregs cx fp (mkst regs0 pcv mem (seg_rom SEGS)) ->
  (forall r : bv 5, acallee_saved (bv_unsigned r) -> bv_unsigned r <> 19 -> getr regs r = getr regs0 r) ->
  c0_ms cx fp pc (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS)).
Proof.
intros cx fp pc regs regs0 mem pcv HG KP. apply (c0_ms_mkst cx fp pc regs regs mem (Z_to_bv 64 0)); [|intros; reflexivity].
destruct HG as (G2 & G8 & G9 & G3 & G4 & G18 & G24). cbn [ms_regs mkst] in *. unfold gregs. cbn [ms_regs mkst].
split; [rewrite KP; [exact G2 | c0_cs | c0_cs]|]. split; [rewrite KP; [exact G8 | c0_cs | c0_cs]|].
split; [rewrite KP; [exact G9 | c0_cs | c0_cs]|]. split; [rewrite KP; [exact G3 | c0_cs | c0_cs]|].
split; [rewrite KP; [exact G4 | c0_cs | c0_cs]|]. split; [rewrite KP; [exact G18 | c0_cs | c0_cs]|].
rewrite KP; [exact G24 | c0_cs | c0_cs].
Qed.

Lemma c0s_den_row : forall E r n off, ew E 20 = Z_to_bv 64 r -> ew E 23 = Z_to_bv 64 n ->
  0 <= r -> 0 <= n <= 4 -> 0 <= off -> r + 56 * n + off < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SOff 20 off) (SMd M_MUL (SOff 23 0) (SLit 56))) = Z_to_bv 64 (r + 56 * n + off).
Proof.
intros E r n off H20 H23 Hr Hn Ho Hlt. rewrite denot_lit_U. f_equal.
rewrite U_SAlu, U_SMd. cbn [zalu_raw zmd_raw]. rewrite (U_atom E 23 n H23) by lia. rewrite U_SOff, H20, U_SLit.
rewrite unsigned_lit_small by lia.
rewrite (zcanon_id 56) by (unfold M64; lia). rewrite (zcanon_id (r + off)) by (unfold M64; lia).
rewrite (zcanon_id (n * 56)) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Definition c0s_csl19 : list (bv 5) := [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv].
Lemma c0s_cs_in19 : forall r : bv 5, acallee_saved (bv_unsigned r) -> bv_unsigned r <> 19 -> In r c0s_csl19.
Proof.
intros r H H19. rewrite <- (Z_to_bv_bv_unsigned _ r). unfold acallee_saved in H.
assert (Hc : bv_unsigned r = 2 \/ bv_unsigned r = 3 \/ bv_unsigned r = 4 \/ bv_unsigned r = 8 \/ bv_unsigned r = 9 \/
  bv_unsigned r = 18 \/ bv_unsigned r = 20 \/ bv_unsigned r = 21 \/ bv_unsigned r = 22 \/
  bv_unsigned r = 23 \/ bv_unsigned r = 24 \/ bv_unsigned r = 25 \/ bv_unsigned r = 26 \/ bv_unsigned r = 27) by lia.
repeat (destruct Hc as [Hc|Hc]; [rewrite Hc; cbn [c0s_csl19 In]; repeat (first [left; apply bv_eq; reflexivity | right])|]).
rewrite Hc; cbn [c0s_csl19 In]; repeat (first [left; apply bv_eq; reflexivity | right]).
Qed.

Lemma c0s_alu_row : forall E r n off, ew E 20 = Z_to_bv 64 r -> ew E 23 = Z_to_bv 64 n ->
  0 <= r -> 0 <= n <= 4 -> 0 <= off -> r + 56 * n + off < 2 ^ 64 ->
  alu64 ALU_ADD (Z_to_bv 64 (bv_unsigned (ew E 20) + off)) (mul_div M_MUL (ew E 23) (Z_to_bv 64 56)) = Z_to_bv 64 (r + 56 * n + off).
Proof.
intros E r n off H20 H23 Hr Hn Ho Hlt. rewrite <- (c0s_den_row E r n off H20 H23 Hr Hn Ho Hlt).
cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma c0s_alu_row0 : forall E r n, ew E 20 = Z_to_bv 64 r -> ew E 23 = Z_to_bv 64 n ->
  0 <= r -> 0 <= n <= 4 -> r + 56 * n < 2 ^ 64 ->
  alu64 ALU_ADD (ew E 20) (mul_div M_MUL (ew E 23) (Z_to_bv 64 56)) = Z_to_bv 64 (r + 56 * n).
Proof.
intros E r n H20 H23 Hr Hn Hlt.
rewrite <- (Z.add_0_r (r + 56 * n)). rewrite <- (c0s_alu_row E r n 0 H20 H23 Hr Hn ltac:(lia) ltac:(lia)).
rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma c0s_s9_cond : forall E op, ew E 25 = Z_to_bv 64 (Z.land op 8) ->
  branch_taken BC_EQ (sv_denot E (SOff 25 0)) (sv_denot E (SLit 0)) = (Z.land op 8 =? 0).
Proof.
intros E op F25. rewrite branch_eq_U, U_SLit. change (zcanon 0) with 0.
destruct (LLVMFuzzerTestOneInput_case0.c0_op8 op) as [H | H]; rewrite H in *;
  rewrite (U_atom E 25 _ F25) by lia; reflexivity.
Qed.


Theorem c0_strn : forall i POST, gb_from B MT POST (C0_S B MT i) -> gb_from B MT POST (C0_B B MT i).
Proof.
intros i POST HNEXT cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HI.
destruct HI as (r & bs & pos & op & nm & want & b & p & HMS & HTURN & HWANT & Hwant & H30 & H58 & HPL & HREG &
  R10 & R19 & R22 & R23 & R25 & R26 & R27).
pose proof HTURN as (HMF & Hi & Hk & Hacc & HBL & HINV & Hpos & HCUR & Hnm & HNAME & Hop & Hop3 & R20).
pose proof HMS as (_ & _ & _ & _ & _ & _ & (G2 & G8 & G9 & G3 & G4 & G18 & G24)).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBok.
pose proof (pa_base_lo (PL := PL_box) (PI := PI)) as HBLO.
pose proof (c0_sp cx HB) as (Hsp & Hsp1 & Hsp32 & Hsp16). unfold GB_STK in Hsp.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR3 & _).
pose proof HINV as ((HL & HB1 & HB2 & _) & _).
pose proof (c0s_pb bs _ _ b p HPL HB2) as (Hb & Hpb).
unfold Boxreg.boxreg_B1 in HB1. unfold Boxreg.boxreg_B2 in HB2.
pose proof HPL as (_ & Hn5 & _).
assert (Hn : 0 <= Boxreg.bx_n bs <= 4) by lia.
pose proof (LLVMFuzzerTestOneInput_case0.c0_base_range (c0_pl cx pos)) as Hbase.
change (LLVMFuzzerTestOneInput_case0.c0_base (c0_pl cx pos)) with (c0_base cx pos) in Hbase.
destruct HREG as (Hrin & HLb' & HRB).
destruct (al_blocks _ _ LAWS _ _ _ _ _ r REG_SIZE HAR3 Hrin) as (Hr16 & Hr4096 & Hrceil & Hria & Hrpres & _).
change (req_size REG_SIZE) with 288 in *.
set (n := Boxreg.bx_n bs) in *.
set (s := c0_gs cx pos op) in *.
set (bs' := c0_placed bs b (c0_nch cx pos) p s) in *.
assert (Hnm64 : 0 <= nm < 2 ^ 64).
{ assert (Hin : In (nm, c0_nk cx pos + 1) (ablocks B ly3 S3)) by (rewrite HBL; apply in_or_app; right; right; left; reflexivity).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin) as (_ & _ & Hc & _). pose proof (req_size_pos (c0_nk cx pos + 1) ltac:(pose proof (LLVMFuzzerTestOneInput_rn.rn_k_range (c0_pl2 cx pos)); unfold c0_nk; lia)). lia. }

assert (CALL : forall (regs : bvmap 5 word) (mem : word -> option byte) mdc,
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(GB_CID, fp)] ly3 S3 W3 mem mdc k ->
  (forall x, mem x = ms_mem ms3 x) ->
  getr regs 10 = w64 (r + 56 * n + 24) ->
  getr regs 11 = w64 (if Z.land op 8 =? 0 then nm else VAL (A_OBJ 5)) ->
  getr regs 12 = w64 31 ->
  getr regs 1 = Z_to_bv 64 (BASE + GC_S) ->
  getr regs 19 = w64 (r + 56 * n) ->
  (forall q : bv 5, acallee_saved (bv_unsigned q) -> bv_unsigned q <> 19 -> getr regs q = getr (ms_regs ms3) q) ->
  SRr SEGS W3 (mkCfg (mkst regs (Z_to_bv 64 (SIGMA BS___interceptor_trampoline_strncmp)) mem (seg_rom SEGS)) mdc) (POST cx)).
{ intros regs mem mdc HJc MEQ A0 A1 A2 RA S19 KP.
  assert (AV : forall a, aview SEGS (w_H W3) mem a = aview SEGS (w_H W3) (ms_mem ms3) a)
    by (intros a; unfold aview, YP09.mbyte, mrestrict; rewrite !MEQ; reflexivity).
  pose proof HJc as (HARc & _).
  pose proof HB as (HPRE0 & _). pose proof HPRE0 as (_ & _ & _ & Hgp & Htp & _).
  (* the read-only view at the call: gb_base's arodata_okP, carried by the journal *)
  assert (ROMN : fm_rom_viewN SEGS B W3 mem).
  { pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & HRO0 & _).
    pose proof (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc HRO0)
      as HROc.
    exact (fm_rom_viewN_of_arodata SEGS B _ _ W3 mem HROc). }
  assert (Usp : spZ regs = c_sp1 cx) by (unfold spZ; rewrite KP by c0_cs; rewrite G2; unfold w64; apply unsigned_lit_small; lia).
  pose proof (c0s_name_str cx W3 ms3 pos nm HNAME) as (HNS & HNL & HNK & HNOK).
  assert (HSOK : Forall (fun c => 0 < c < 256) s) by (subst s; unfold c0_gs; destruct (Z.land op 8 =? 0); [exact HNOK | constructor]).
  assert (HX : fm_cstr_ok SEGS W3 mem (r + 56 * n + 24) (firstn 31 s)).
  { apply (c0s_cstr_row ly3 S3 W3 mem mdc r bs' n s HARc Hrin); [| | exact Hn | exact HSOK].
    - intros q Hq. rewrite AV. exact (HRB q Hq).
    - intros j Hj. apply c0s_name_byte; [exact HL | exact Hn | exact Hj]. }
  assert (HY : fm_cstr_ok SEGS W3 mem (if Z.land op 8 =? 0 then nm else VAL (A_OBJ 5)) s).
  { subst s. unfold c0_gs. destruct (Z.eqb_spec (Z.land op 8) 0) as [E8 | E8].
    - assert (Hnmin : In (nm, c0_nk cx pos + 1) (ablocks B ly3 S3)) by (rewrite HBL; apply in_or_app; right; right; left; reflexivity).
      apply (c0s_cstr_blk ly3 S3 W3 mem mdc nm (c0_nk cx pos + 1) (c0_s cx pos) HARc Hnmin); [lia | | lia | exact HNOK].
      intros j Hj. rewrite AV. exact (HNS j Hj).
    - exact (c0s_cstr_emp ly3 S3 W3 mem mdc HARc ROMN). }
  eapply SRr_bind.
  { refine (c0s_strncmp_at _ ASTRNCMP W3 regs mem GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
      [(GB_CID, fp)] ly3 S3 mdc k (r + 56 * n + 24) _ 31 (firstn 31 s) s (c_sp1 cx - spZ (c_regs cx)) _ HJc
      _ _ _ _ _ _ RA _ A0 A1 A2 _ ROMN (HROMO _ _ _ _ _ HARc) HX HY).
    - rewrite Usp. lia.
    - apply c0_sub_mod16; [exact Hsp32 | exact Hsp16].
    - lia.
    - change ESTACK with 4096. unfold GB_STK. lia.
    - rewrite KP by c0_cs. rewrite G3. exact Hgp.
    - rewrite KP by c0_cs. rewrite G4. exact Htp.
    - apply ret_ok_codeptr_v; [unfold GC_S; lia | reflexivity].
    - lia. }
  cbv beta. intros W2 c2 Hwle (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP & R10' & Hv & Hiff & Hfr & Hpres2).

  assert (Hv0 : v = 0) by (apply Hiff; apply c0s_strn_eq).
  assert (ESTK : ESTACK = 4096) by reflexivity.
  pose proof (c0_geo LAWS cx fp k ly3 S3 W3 _ _ HB HJ HFR) as (Hinp & EgF & HF0 & HF1 & HF64 & HSH).
  assert (Hnmin : In (nm, c0_nk cx pos + 1) (ablocks B ly3 S3)) by (rewrite HBL; apply in_or_app; right; right; left; reflexivity).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hnmin) as (_ & _ & Hnmceil & _).
  pose proof (req_size_pos (c0_nk cx pos + 1) ltac:(lia)) as [_ Hnmrq].
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> (c_sp1 cx <= a \/ a < alloc_ceiling) ->
    aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { intros a Ha Hz. rewrite Hfr by (try rewrite ESTK; lia). apply AV. }
  set (msS := mkst regs2 (Z_to_bv 64 (BASE + GC_S)) mem2 (seg_rom SEGS)).
  assert (KP2 : forall q : bv 5, acallee_saved (bv_unsigned q) -> getr regs2 q = getr regs q)
    by (intros q Hq; pose proof (HP (bv_unsigned q) Hq) as X; rewrite Z_to_bv_bv_unsigned in X; exact X).
  assert (KP3 : forall q : bv 5, acallee_saved (bv_unsigned q) -> bv_unsigned q <> 19 -> getr regs2 q = getr (ms_regs ms3) q)
    by (intros q Hq H19; rewrite KP2 by exact Hq; apply KP; assumption).
  assert (KZ : forall a, c0_zone cx fp a -> aview SEGS (w_H W3) (ms_mem msS) a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { intros a Ha. pose proof (c0_zone_range cx fp a Hinp HF0 HF1 HSH ltac:(lia) Ha) as Har. apply KM; [exact Har|].
    destruct Ha as [Ha|[Ha|[Ha|Ha]]]; [left; lia | right; destruct Hinp; lia | right; lia | right].
    rewrite HSH in Ha. unfold SHADOW_OFF in *.
    pose proof (Z.div_le_upper_bound (gF cx fp) 8 (2 ^ 44) ltac:(lia) ltac:(lia)). lia. }
  assert (KS : forall off v, 0 <= off < 0x98 -> gslot cx W3 ms3 off v -> gslot cx W3 msS off v).
  { intros off v0 Hoff Hv'. unfold gslot in *. cbn [ms_mem msS mkst]. rewrite <- Hv'. apply rdword_ext.
    intros j Hj. apply KM; lia. }
  eapply (HNEXT cx fp k acc ly3 S3 W3 msS md2 HB HJ2 HFR HMO).
  exists r, bs, pos, op, nm, want, b, p.
  split; [apply (c0s_ms_mkst19 cx fp GC_S regs2 (ms_regs ms3) mem2 (Z_to_bv 64 0));
    [exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HMS)))))) | exact KP3]|].
  split.
  { split; [exact (c0_mf_keep2 i cx fp W3 W3 ms3 msS r bs HB KZ HMF)|].
    split; [exact Hi|]. split; [exact Hk|]. split; [exact Hacc|]. split; [exact HBL|]. split; [exact HINV|].
    split; [exact Hpos|].
    split; [destruct HCUR as (C0 & C88 & C90); split; [exact C0|]; split; [apply KS; [lia | exact C88] | apply KS; [lia | exact C90]]|].
    split; [exact Hnm|].
    split; [intros j Hj; cbn [ms_mem msS mkst]; rewrite KM by lia; exact (HNAME j Hj)|].
    split; [exact Hop|]. split; [exact Hop3|].
    cbn [ms_regs msS mkst]. rewrite KP3 by c0_cs. exact R20. }
  split; [exact HWANT|]. split; [exact Hwant|].
  split; [apply KS; [lia | exact H30]|]. split; [apply KS; [lia | exact H58]|].
  split; [exact HPL|].
  split; [split; [exact Hrin|]; split; [exact HLb'|]; intros q Hq; cbn [ms_mem msS mkst]; rewrite KM by (unfold REG_SIZE in Hq; lia); exact (HRB q Hq)|].
  cbn [ms_regs msS mkst].
  split; [rewrite R10', Hv0; reflexivity|].
  split; [rewrite KP2 by c0_cs; exact S19|].
  split; [rewrite KP3 by c0_cs; exact R23|].
  split; [rewrite KP3 by c0_cs; exact R25|].
  rewrite KP3 by c0_cs. exact R27.
}

set (E := Eimg (Ereg (ms_regs ms3) [Z_to_bv 64 nm; Z_to_bv 64 b; Z_to_bv 64 p])).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall q (r : bv 5), Z.of_nat q = bv_unsigned r -> ew E q = getr (ms_regs ms3) r)
  by (intros q r0 Hq; subst E; apply ew_Eimg_Ereg_nat; exact Hq).
assert (F32 : ew E 32 = Z_to_bv 64 nm) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
assert (F33 : ew E 33 = Z_to_bv 64 b) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 1)).
assert (F34 : ew E 34 = Z_to_bv 64 p) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 2)).
assert (F9 : ew E 9 = Z_to_bv 64 (c_sp1 cx)) by (rewrite (EE 9%nat 9%bv eq_refl); exact G9).
assert (F18 : ew E 18 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 18%nat 18%bv eq_refl); exact G18).
assert (F20 : ew E 20 = Z_to_bv 64 r) by (rewrite (EE 20%nat 20%bv eq_refl); exact R20).
assert (F22 : ew E 22 = Z_to_bv 64 (r + 56 * n)) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
assert (F23 : ew E 23 = Z_to_bv 64 n) by (rewrite (EE 23%nat 23%bv eq_refl); exact R23).
assert (F25 : ew E 25 = Z_to_bv 64 (Z.land op 8)) by (rewrite (EE 25%nat 25%bv eq_refl); exact R25).
assert (F26 : ew E 26 = Z_to_bv 64 (c0_base cx pos * 2 ^ 56)) by (rewrite (EE 26%nat 26%bv eq_refl); exact R26).
assert (F27 : ew E 27 = Z_to_bv 64 (c0_base cx pos)) by (rewrite (EE 27%nat 27%bv eq_refl); exact R27).
assert (F10 : ew E 10 = Z_to_bv 64 0) by (rewrite (EE 10%nat 10%bv eq_refl); exact R10).
assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx) by (rewrite F9; apply unsigned_lit_small; lia).
assert (U22 : bv_unsigned (ew E 22) = r + 56 * n) by (rewrite F22; apply unsigned_lit_small; lia).
assert (Vpin : Boxreg.rd4 bs' (56 * n + 20) = p) by (apply c0s_rd_pin; [exact HL | exact Hn | lia]).
assert (Vbase : Boxreg.rd4 bs' (56 * n + 8) = b) by (apply c0s_rd_base; [exact HL | exact Hn | lia]).
assert (HS : st_ok_pi SEGS VAL E (mkSS GC_B sr_atoms [C0S_R58; C0S_ROW] None C0S_F) (restrict (w_H W3) ms3)).
{ rewrite (c0_mkst cx fp GC_B ms3 (w_H W3) HMS). apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok, C0S_R58, C0S_ROW; cbv zeta;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS _ _ _ 0x58 8%N (SOff 32 0) nm); [rewrite c0_denot_off0; exact F32 | cbn; lia | cbn; lia |].
      apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). exact H58.
    + rewrite U22. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (chunk_ok_val SEGS _ _ _ 8 4%N (SOff 33 0) b); [rewrite c0_denot_off0; exact F33 | cbn; lia | cbn; lia |].
        replace (r + 56 * n + 8) with (r + (56 * n + 8)) by lia. rewrite <- Vbase. change (N.to_nat 4) with 4%nat.
        apply (LowestFreeBase.lfb_val_mem4 (w_H W3) (ms_mem ms3) r bs'); [exact HRB | exact HLb' | lia | lia].
      * apply (chunk_ok_val SEGS _ _ _ 20 4%N (SOff 34 0) p); [rewrite c0_denot_off0; exact F34 | cbn; lia | cbn; lia |].
        replace (r + 56 * n + 20) with (r + (56 * n + 20)) by lia. rewrite <- Vpin. change (N.to_nat 4) with 4%nat.
        apply (LowestFreeBase.lfb_val_mem4 (w_H W3) (ms_mem ms3) r bs'); [exact HRB | exact HLb' | lia | lia].
  - apply pairwise_disjoint_of_extents. unfold C0S_R58, C0S_ROW, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U22.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - split; [|split; exact I]. cbn [C0S_F f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U22, F18. unfold C0S_SB, SHADOW_OFF. rewrite unsigned_lit_small by lia.
    change (2 ^ 0) with 1. change (2 ^ 3) with 8. rewrite Z.mod_1_r.
    assert (Hal8 : (r + 56 * n) mod 8 = 0).
    { pose proof (Z.div_mod r 16 ltac:(lia)) as Hdm. rewrite Hr16 in Hdm.
      replace (r + 56 * n) with ((2 * (r / 16) + 7 * n) * 8) by lia. apply Z_mod_mult. }
    repeat split; lia. }

assert (U18 : U E (SOff 18 0) = SHADOW_OFF) by (rewrite U_SOff, F18, unsigned_lit_small by (unfold SHADOW_OFF; lia); reflexivity).
assert (UR22 : U E (SOff 22 0) = r + 56 * n) by (rewrite U_SOff, F22, unsigned_lit_small by lia; rewrite Z.add_0_r; apply c0_zcanon_in; lia).
assert (SHOK : sh_ok SEGS (SOff 18 0) C0S_SH E (mrestrict (w_H W3) (ms_mem ms3))).
{ unfold sh_ok, C0S_SH. apply Forall_cons; [|apply Forall_nil].
  unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite U18, UR22.
  rewrite <- (aview_rd_of SEGS). split.
  + eapply (range_addressable_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 r REG_SIZE (r + 56 * n + 0) (56 - 0) HAR3 Hrin);
    change (req_size REG_SIZE) with 288; lia.
  + intros a Ha. rewrite Z.min_l in Ha by lia. rewrite Z.max_r in Ha by lia.
    revert Ha. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
    revert Hria Hr4096 Hrceil Hn C1 C3 C5. clear. intros. lia. }
pose proof (st_ok_pi_pin_reg' _ _ _ (10%bv : bv 5) 0 HS ltac:(cbn [ms_regs restrict]; exact R10) eq_refl) as HS0.
clear HS. rename HS0 into HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.

assert (HAE : env_agree 32 (Ereg (ms_regs ms3) [Z_to_bv 64 nm; Z_to_bv 64 b; Z_to_bv 64 p]) E)
  by (split; [intros q Hq; subst E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (MALL : forall x, ms_mem ms3 x = ms_mem ms3 x) by reflexivity.

paj_run_tok (paj_run B LAWS) HS HJ SHOK C0S_SPAN; [awr_ok_tac|]. c0s_mem ms3 MALL.
psrr_branch_tok (paj_run B LAWS) (paj_branch (PI := PI)) HS SHOK C0S_SPAN.
- (* 0x809fc bne a0, a1 -> 0x80f60 (abort): pinned = (base >= 0), declare_placed *)
  exfalso. rewrite (c0s_pin_cond E p (c0_base cx pos) F34 F27) in Hc by lia.
  destruct Hpb as [(Hp1 & _ & Hb0) | (Hp0 & Hb0)];
  [rewrite (proj2 (Z.ltb_ge _ 0) Hb0), Hp1 in Hc | rewrite (proj2 (Z.ltb_lt _ 0) Hb0), Hp0 in Hc]; discriminate Hc.
- clear Hc.
  paj_run_tok (paj_run B LAWS) HS HJ SHOK C0S_SPAN; [awr_ok_tac|]. c0s_mem ms3 MALL.
  psrr_branch_tok (paj_run B LAWS) (paj_branch (PI := PI)) HS SHOK C0S_SPAN.

  + (* 0x80a00 bltz s10 taken: base < 0, no base check *)
    rewrite (c0s_lt_cond E (c0_base cx pos) F26 Hbase) in Hc. apply Z.ltb_lt in Hc.
    paj_run_tok (paj_run B LAWS) HS HJ SHOK C0S_SPAN; [awr_ok_tac|]. c0s_mem ms3 MALL.
    psrr_branch_tok (paj_run B LAWS) (paj_branch (PI := PI)) HS SHOK C0S_SPAN.
    * rewrite (c0s_s9_cond E op F25) in Hc0. apply Z.eqb_eq in Hc0.
  paj_run_tok (paj_run B LAWS) HS HJ SHOK C0S_SPAN; [awr_ok_tac|]. c0s_mem ms3 MALL.
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?msc) =>
  assert (KPc : forall q : bv 5, acallee_saved (bv_unsigned q) -> bv_unsigned q <> 19 -> getr (ms_regs msc) q = getr (ms_regs ms3) q)
    by (intros q Hq H19; exact (regs_kept_of_st_ok SEGS E _ (restrict (w_H W3) msc) (ms_regs ms3) _ c0s_csl19 HS HAE ltac:(vm_compute; reflexivity) q (c0s_cs_in19 q Hq H19)));
  pmkst HS;
  prreg HS (1%bv : bv 5) Q1; prreg HS (10%bv : bv 5) Q10; prreg HS (11%bv : bv 5) Q11; prreg HS (12%bv : bv 5) Q12;
  prreg HS (19%bv : bv 5) Q19;
  rewrite (c0s_alu_row E r n 24 F20 F23) in Q10 by lia;
  rewrite (c0s_alu_row0 E r n F20 F23) in Q19 by lia;
  apply CALL; [exact HJ | exact MALL | exact Q10 | | exact Q12 | unfold GC_S; exact Q1 | exact Q19 | exact KPc] end.
  rewrite Q11, F32, (proj2 (Z.eqb_eq _ _) Hc0). reflexivity.
    * rewrite (c0s_s9_cond E op F25) in Hc0. apply Z.eqb_neq in Hc0.
  paj_run_tok (paj_run B LAWS) HS HJ SHOK C0S_SPAN; [awr_ok_tac|]. c0s_mem ms3 MALL.
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?msc) =>
  assert (KPc : forall q : bv 5, acallee_saved (bv_unsigned q) -> bv_unsigned q <> 19 -> getr (ms_regs msc) q = getr (ms_regs ms3) q)
    by (intros q Hq H19; exact (regs_kept_of_st_ok SEGS E _ (restrict (w_H W3) msc) (ms_regs ms3) _ c0s_csl19 HS HAE ltac:(vm_compute; reflexivity) q (c0s_cs_in19 q Hq H19)));
  pmkst HS;
  prreg HS (1%bv : bv 5) Q1; prreg HS (10%bv : bv 5) Q10; prreg HS (11%bv : bv 5) Q11; prreg HS (12%bv : bv 5) Q12;
  prreg HS (19%bv : bv 5) Q19;
  rewrite (c0s_alu_row E r n 24 F20 F23) in Q10 by lia;
  rewrite (c0s_alu_row0 E r n F20 F23) in Q19 by lia;
  apply CALL; [exact HJ | exact MALL | exact Q10 | | exact Q12 | unfold GC_S; exact Q1 | exact Q19 | exact KPc] end.
  rewrite Q11, (proj2 (Z.eqb_neq _ _) Hc0). change 246%nat with (A_OBJ 5). subst E. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia). reflexivity.

  + (* 0x80a00 bltz s10 not taken: base >= 0, the base check *)
    rewrite (c0s_lt_cond E (c0_base cx pos) F26 Hbase) in Hc. apply Z.ltb_ge in Hc.
    paj_run_tok (paj_run B LAWS) HS HJ SHOK C0S_SPAN; [awr_ok_tac|]. c0s_mem ms3 MALL.
    psrr_branch_tok (paj_run B LAWS) (paj_branch (PI := PI)) HS SHOK C0S_SPAN.
    * (* 0x80a1c bne a0, s11 -> 0x80f60 (abort): the row's base is the given base (declare_placed, base >= 0) *)
      exfalso. rewrite (c0s_base_cond E b (c0_base cx pos) F33 F27 Hb Hbase) in Hc0.
      destruct Hpb as [(_ & Hbb & _) | (_ & Hb0)]; [rewrite Hbb, Z.eqb_refl in Hc0; discriminate Hc0 | lia].
    * clear Hc0.
      paj_run_tok (paj_run B LAWS) HS HJ SHOK C0S_SPAN; [awr_ok_tac|]. c0s_mem ms3 MALL.
      psrr_branch_tok (paj_run B LAWS) (paj_branch (PI := PI)) HS SHOK C0S_SPAN.
      -- rewrite (c0s_s9_cond E op F25) in Hc0. apply Z.eqb_eq in Hc0.
  paj_run_tok (paj_run B LAWS) HS HJ SHOK C0S_SPAN; [awr_ok_tac|]. c0s_mem ms3 MALL.
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?msc) =>
  assert (KPc : forall q : bv 5, acallee_saved (bv_unsigned q) -> bv_unsigned q <> 19 -> getr (ms_regs msc) q = getr (ms_regs ms3) q)
    by (intros q Hq H19; exact (regs_kept_of_st_ok SEGS E _ (restrict (w_H W3) msc) (ms_regs ms3) _ c0s_csl19 HS HAE ltac:(vm_compute; reflexivity) q (c0s_cs_in19 q Hq H19)));
  pmkst HS;
  prreg HS (1%bv : bv 5) Q1; prreg HS (10%bv : bv 5) Q10; prreg HS (11%bv : bv 5) Q11; prreg HS (12%bv : bv 5) Q12;
  prreg HS (19%bv : bv 5) Q19;
  rewrite (c0s_alu_row E r n 24 F20 F23) in Q10 by lia;
  rewrite (c0s_alu_row0 E r n F20 F23) in Q19 by lia;
  apply CALL; [exact HJ | exact MALL | exact Q10 | | exact Q12 | unfold GC_S; exact Q1 | exact Q19 | exact KPc] end.
  rewrite Q11, F32, (proj2 (Z.eqb_eq _ _) Hc0). reflexivity.
      -- rewrite (c0s_s9_cond E op F25) in Hc0. apply Z.eqb_neq in Hc0.
  paj_run_tok (paj_run B LAWS) HS HJ SHOK C0S_SPAN; [awr_ok_tac|]. c0s_mem ms3 MALL.
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?msc) =>
  assert (KPc : forall q : bv 5, acallee_saved (bv_unsigned q) -> bv_unsigned q <> 19 -> getr (ms_regs msc) q = getr (ms_regs ms3) q)
    by (intros q Hq H19; exact (regs_kept_of_st_ok SEGS E _ (restrict (w_H W3) msc) (ms_regs ms3) _ c0s_csl19 HS HAE ltac:(vm_compute; reflexivity) q (c0s_cs_in19 q Hq H19)));
  pmkst HS;
  prreg HS (1%bv : bv 5) Q1; prreg HS (10%bv : bv 5) Q10; prreg HS (11%bv : bv 5) Q11; prreg HS (12%bv : bv 5) Q12;
  prreg HS (19%bv : bv 5) Q19;
  rewrite (c0s_alu_row E r n 24 F20 F23) in Q10 by lia;
  rewrite (c0s_alu_row0 E r n F20 F23) in Q19 by lia;
  apply CALL; [exact HJ | exact MALL | exact Q10 | | exact Q12 | unfold GC_S; exact Q1 | exact Q19 | exact KPc] end.
  rewrite Q11, (proj2 (Z.eqb_neq _ _) Hc0). change 246%nat with (A_OBJ 5). subst E. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia). reflexivity.
Qed.

End c.
End b.
End a.
