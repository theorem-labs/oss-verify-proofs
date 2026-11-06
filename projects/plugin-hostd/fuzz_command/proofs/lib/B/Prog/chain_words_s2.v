(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment 2 of the walk of chain_words (0x8da84) on the ASan+UBSan build of
   plugin-hostd/fuzz_command (fuzz_command.asan-ubsan), from the cut point KC (+0x21c, 0x8dca0) to KL with j = 0
   (+0x278, 0x8dcfc) or to KR1 (+0x2d8, 0x8dd5c): the two spills of F at s1 + 8 and s1 + 16, the UBSan checks of
   0x8dca8 (tok >= 2^64 - 8) and 0x8dcb4 (tok + 8 misaligned), the inline load8 check of tok[1], the two reloads, the
   call of number at 0x8dcd8 with out = s1 + 52, and the set-up of the member loop. The B twin of A's segment 2
   (lib/A/Prog/chain_words_s2.v on a working branch 5e2cdad423e): the same method (a program call
   through cl_callS_wide, the symbolic state re-seated after it, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/
   ACaa.v and A/AChc.v), over B's code, which re-lays this region (B-PREP.md, section chain_words).
   The UBSan checks are decided by the symbolic run itself from the seed's atom facts: a0 = 2^64 - 8 against
   tok <= 2^47 - 32 (afobj: tok inside a live side-stack frame, below the allocator's ceiling), and tok mod 8 = 0
   (afobj) for the alignment mask. The inline shadow check reads the shadow of tok[1], marked usable by afobj's
   range_addressable, as A's does. Pass 5 (no astack_pres): number's frame chain at the call is afn_pre's own chain
   pushed by the prologue's frame record (cw2_chain, A's block), and its out cell s1 + 52 is present by the
   journal's presence clause (YCbq.v:485). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaSB PaNoChain PaLibF.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
number_c sup_chain_c sup_resp_c chain_words_c chain_words_d.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the return point of the call of number at +0x254 (0x8dcd8) *)
Definition CW2_RET : Z := AF_chain_words + 0x258.
(* the symbolic state at KC: s1 (atom 9) the realigned frame pointer, a0 (atom 10) = 2^64 - 8 from the prologue,
   s5 = tok (atom 21), s8 = the shadow base (atom 24); tok[1] (atom 32) in the token region, the 8 bytes of tok[1]
   marked usable for the inline check of +0x248, and the two spill slots [s1 + 8, s1 + 24) writable *)
Definition cw2_tokR : YP09.region := YP09.mkRegion (Some 21%nat) 8 16 0 0 [YP09.mkChunk 8 (CVal 8 (SOff 32 0))].
Definition cw2_spR : YP09.region := YP09.mkRegion (Some 9%nat) 8 24 8 24 [].
(* atom 9 (s1) lies in the real stack, above the allocator's ceiling and so apart from the shadow span: the run's
   cells_safe_b check of the writable spill window needs that range *)
Definition cw2_factsC : facts :=
  mkFacts [(9%nat, mkAF 0x7fff7f800000 (2 ^ 47 - 24) 0); (10%nat, mkAF (2 ^ 64 - 8) (2 ^ 64 - 8) 0);
           (21%nat, mkAF 4096 (2 ^ 47 - 32) 3); (24%nat, mkAF SB SB 0)] [] [].
Definition ss_cw2C : sstate := mkSS CW_KC sr_atoms [cw2_tokR; cw2_spR] None cw2_factsC.
Definition cw2_Bx : sv := SOff 24 0.
Definition cw2_SH : list shent := [mkSHE 21 8 16].
Definition cw2_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
(* after the call: registers only *)
Definition ss_cw2R : sstate := mkSS CW2_RET sr_atoms [] None (mkFacts [] [] []).

Lemma cw2_val_mem : forall segs H mem a n v,
aval_mem (aview segs H mem) a n v -> val_mem segs (mrestrict H mem) a n v.
Proof.
intros segs H mem a n v Hv k Hk. pose proof (Hv k Hk) as Hb. unfold aview in Hb.
unfold val_mem.
destruct (mbyte segs (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:Eb;
  cbn [option_map] in Hb; [|discriminate Hb].
injection Hb as Hb. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned, Hb. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
cbv [YO0f.le_byte YG0f.le_byte]. symmetry. apply Z.mod_mod. lia.
Qed.

Lemma cw2_afact : forall E m v lo hi al,
ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> lo <= v <= hi -> v mod 2 ^ al = 0 -> 0 <= al <= 64 ->
afact_ok E m (mkAF lo hi al).
Proof.
intros E m v lo hi al Hm Hv Hlh Hal Hal2. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Hm, unsigned_lit_small by exact Hv. split; [exact Hlh | split; [exact Hal | exact Hal2]].
Qed.
(* `not` (xori _, _, -1) of a 64-bit value; the bit lemma is copied from lib/B/Prog/sup_chain_aux.v
   (a working branch, scb_xor_m1) *)
Lemma cw2_xor_m1 : forall x, 0 <= x < 2 ^ 64 -> Z.lxor x (2 ^ 64 - 1) = 2 ^ 64 - 1 - x.
Proof.
intros x Hx. assert (Hones : Z.ones 64 = 2 ^ 64 - 1) by reflexivity. rewrite <- Hones.
assert (D : Z.land x (Z.lxor x (Z.ones 64)) = 0).
{ apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.lxor_spec, Z.bits_0.
  destruct (Z.lt_ge_cases n 64) as [H|H].
  - rewrite Z.testbit_ones by lia. replace (0 <=? n) with true by (symmetry; apply Z.leb_le; lia).
    replace (n <? 64) with true by (symmetry; apply Z.ltb_lt; lia). destruct (Z.testbit x n); reflexivity.
  - assert (H0 : Z.testbit x n = false).
    { rewrite <- (Z.mod_small x (2 ^ 64)) by lia. apply Z.mod_pow2_bits_high. lia. }
    rewrite H0. reflexivity. }
pose proof (Z.add_nocarry_lxor x (Z.lxor x (Z.ones 64)) D) as E.
rewrite <- (Z.lxor_assoc x x (Z.ones 64)), Z.lxor_nilpotent, Z.lxor_0_l in E. lia.
Qed.
Lemma cw2_not : forall t z, 0 <= t < 2 ^ 64 -> zcanon z = 2 ^ 64 - 1 ->
zcanon (zalu_raw 63 64 ALU_XOR t (zcanon z)) = 2 ^ 64 - 1 - t.
Proof.
intros t z Ht Hz. cbn [zalu_raw]. rewrite Hz, cw2_xor_m1 by exact Ht. apply zcanon_small. lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Definition cw2_EC (regs : bvmap 5 word) (p1 : Z) : env := Eimg (Ereg regs [w64 p1]).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the callee and the record facts, with the statement's names (chain_words_c.v:108, the brief's section 6) *)
Hypothesis NUMBER : forall fx0 : YK11.FPState, @tnumber_spec fx0 rc SK PI B MT.
Hypothesis TL : PALib B.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis TRANSP : cw_transportP B MT.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.

Lemma cw2_frame_addr_le : forall n ly ly' cid pos, layout_le n ly ly' -> frame_addr ly' cid pos = frame_addr ly cid pos.
Proof. intros n ly ly' cid pos (_ & _ & _ & _ & _ & EF & _). unfold frame_addr. rewrite EF. reflexivity. Qed.
(* a run whose regions are all read-only leaves every byte as it was *)
Lemma cw2_frame_ro : forall E rs (m m' : word -> option byte),
Forall (fun r => YP09.r_whi r <= YP09.r_wlo r) rs -> frame_of E rs m m' -> forall x, m' x = m x.
Proof.
intros E rs m m' Hro H x. apply H. intros (r & Hr & Ha).
pose proof (proj1 (Forall_forall _ _) Hro r Hr) as Hw. cbn beta in Hw. lia.
Qed.
Lemma cw2_aview_ext : forall H (m m' : word -> option byte), (forall x, m' x = m x) ->
forall a, aview SEGS H m' a = aview SEGS H m a.
Proof. intros H m m' He a. unfold aview, mbyte, mrestrict. cbv beta. rewrite (He (Z_to_bv 64 a)). reflexivity. Qed.
Lemma cw2_present_view : forall H (m : word -> option byte) a, apresent H m a -> aview SEGS H m a <> None.
Proof.
intros H m a [Hh [b Hb]]. unfold aview, mbyte, mrestrict. cbv beta. rewrite Hh, Hb. cbv beta iota. discriminate.
Qed.
Lemma cw2_pres : forall regs regs' (r : bv 5), aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) ->
getr regs' r = getr regs r.
Proof. intros regs regs' r H Hr. pose proof (H _ Hr) as E. rewrite Z_to_bv_bv_unsigned in E. exact E. Qed.
(* an 8-byte chunk of a region of the symbolic state, whose base and value are held in registers *)
Lemma cw2_rd_reg8 : forall E (H : word -> bool) ms ss i r off (rb rr : bv 5) nb n,
st_ok SEGS E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r ->
YP09.r_base r = Some nb -> sr_get (ss_regs ss) rb = SOff nb 0 ->
In (YP09.mkChunk off (CVal 8 (SOff n 0))) (YP09.r_chunks r) ->
sr_get (ss_regs ss) rr = SOff n 0 ->
rdword (aview SEGS H (ms_mem ms)) (bv_unsigned (getr (ms_regs ms) rb) + off) = Some (bv_unsigned (getr (ms_regs ms) rr)).
Proof.
intros E H ms ss i r off rb rr nb n HS Hi Hb Hrb Hin Hrr.
pose proof (st_ok_region_nth E ss (restrict H ms) i r HS Hi) as (_ & _ & _ & HC).
rewrite Forall_forall in HC. specialize (HC _ Hin).
change (ms_mem (restrict H ms)) with (mrestrict H (ms_mem ms)) in HC.
rewrite Hb in HC. cbn [base_val] in HC.
assert (D : forall m, sv_denot E (SOff m 0) = ew E m)
  by (intros m; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
rewrite (st_ok_restrict_reg SEGS H E ss ms rb HS), Hrb, (st_ok_restrict_reg SEGS H E ss ms rr HS), Hrr, !D.
pose proof (bv_unsigned_in_range 64 (ew E n)) as Rn. change (bv_modulus 64) with (2 ^ 64) in Rn.
apply rdword_of_val_mem; [|exact Rn].
apply (val_of_chunk_ok SEGS E _ _ off 8 (SOff n 0) (bv_unsigned (ew E n)) HC).
- rewrite D. symmetry. apply Z_to_bv_bv_unsigned.
- exact Rn.
- cbn. lia.
Qed.
(* the blocks the recorder owns are live blocks *)
Lemma cw2_O_blocks : forall ly S (rd : reader) R O pn, rec_repA B ly S rd R O -> In pn O -> In pn (ablocks B ly S).
Proof.
intros ly S rd R O pn (Q & HA & HO) Hin. apply HO in Hin.
destruct HA as (_ & _ & _ & (Hn & HlQ & _ & Hcalls & Hsp & _) & Hans & Hrep & _ & _).
unfold lay_blocks in Hin. apply in_app_or in Hin as [Hin | Hin].
- apply in_concat in Hin as (P & HP & Hin). apply In_nth_error in HP as (i & HPi).
  destruct (nth_error (r_calls R) i) as [cc|] eqn:Hci.
  + destruct (Hcalls i cc P Hci HPi) as ((_ & _ & HlP & _ & _ & _ & Hargs) & _).
    apply In_nth_error in Hin as (kk & Hk).
    destruct (nth_error (snd cc) kk) as [s|] eqn:Hs.
    * exact (proj1 (proj2 (proj2 (Hargs kk s pn Hs Hk)))).
    * exfalso. apply nth_error_None in Hs. assert (Hx : nth_error P kk <> None) by congruence.
      apply nth_error_Some in Hx. lia.
  + exfalso. apply nth_error_None in Hci. assert (Hx : nth_error (l_calls Q) i <> None) by congruence.
    apply nth_error_Some in Hx. lia.
- apply in_app_or in Hin as [Hin | Hin].
  + destruct Hsp as (_ & _ & HlP & _ & _ & _ & Hargs).
    apply In_nth_error in Hin as (kk & Hk).
    destruct (nth_error (snd (r_spill R)) kk) as [s|] eqn:Hs.
    * exact (proj1 (proj2 (proj2 (Hargs kk s pn Hs Hk)))).
    * exfalso. apply nth_error_None in Hs. assert (Hx : nth_error (l_spill Q) kk <> None) by congruence.
      apply nth_error_Some in Hx. lia.
  + apply in_app_or in Hin as [Hin | Hin].
    * unfold aanswer_at in Hans. destruct (l_answer Q) as [q|]; cbn [oblk In] in Hin; [|contradiction].
      destruct Hin as [<- | []]. destruct (r_answer R); [|contradiction]. exact (proj1 (proj2 (proj2 Hans))).
    * unfold areply_at in Hrep. destruct (l_reply Q) as [q|]; cbn [oblk In] in Hin; [|contradiction].
      destruct Hin as [<- | []]. destruct (r_reply R); [|contradiction].
      exact (proj1 (proj2 (proj2 (proj2 (proj2 Hrep))))).
Qed.
(* the walk's footprint lies below the allocator's ceiling: the recorder statics and the recorder's blocks *)
Lemma cw2_FP_low : forall c a, cw_pre B MT c -> inFP (cw_FP c) a -> a < alloc_ceiling.
Proof.
intros c a HP (r & Hr & Ha). pose proof asan_consts as (C1 & _).
unfold cw_FP, CHAIN_WORDS_PG in Hr. apply in_app_or in Hr as [Hr | Hr].
- cbn in Hr. destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Ha; unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Ha; lia.
- unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p n] & <- & Hin). cbn [fst snd] in Ha.
  pose proof (cw2_O_blocks _ _ _ _ _ _ (cp_rec _ _ _ HP) Hin) as Hb.
  pose proof (cp_afn _ _ _ HP) as (HAR & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hb) as (_ & _ & Hc & _). lia.
Qed.
(* the frame record the prologue wrote (ra at sp0 - 8, s0 at sp0 - 16) extends the caller's chain (A's cw2_chain) *)
Lemma cw2_chain : forall c ly3 S3 W3 (m : word -> option byte) md3 k,
cw_pre B MT c ->
ajournal SEGS B CHAIN_WORDS_STK (cw_sp0 c) (cw_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c) [(3, x_fpos c)]
  ly3 S3 W3 m md3 k ->
(forall j r, nth_error cw_saved j = Some r ->
  rdword (rdW W3 m) (cw_sp0 c - 8 - 8 * Z.of_nat j) = Some (bv_unsigned (getr (x_regs c) (Z_to_bv 5 r)))) ->
exists ch1, achain ly3 (rdW W3 m) (cw_s1 c) (cw_sp0 c) ch1.
Proof.
intros c ly3 S3 W3 m md3 k HP HJ HSV.
pose proof (cp_afn _ _ _ HP) as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & G1 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & _).
assert (FS : 176 <= CHAIN_WORDS_STK) by (unfold CHAIN_WORDS_STK, NUMBER_STK, ESTACK; lia).
destruct (cw_s1_facts c Hal16) as (Hs1m & Hs1).
unfold cw_sp0 in *.
destruct (Z_lt_le_dec (spZ (x_regs c)) (ly_top (x_ly c) - 16)) as [Hlt | Hge].
- exists ((spZ (x_regs c), raZ (x_regs c), s0Z (x_regs c)) :: x_ch c).
  apply (achain_ly_top (x_ly c) ly3 _ _ _ _ Etop).
  pose proof (HSV 0%nat 1 eq_refl) as H0. pose proof (HSV 1%nat 8 eq_refl) as H1.
  change (Z.of_nat 0) with 0 in H0. change (Z.of_nat 1) with 1 in H1.
  replace (spZ (x_regs c) - 8 - 8 * 0) with (spZ (x_regs c) - 8) in H0 by lia.
  replace (spZ (x_regs c) - 8 - 8 * 1) with (spZ (x_regs c) - 16) in H1 by lia.
  assert (Q1 : getr (x_regs c) (Z_to_bv 5 1) = getr (x_regs c) 1) by (f_equal; apply bv_eq; reflexivity).
  assert (Q8 : getr (x_regs c) (Z_to_bv 5 8) = getr (x_regs c) 8) by (f_equal; apply bv_eq; reflexivity).
  rewrite Q1 in H0. rewrite Q8 in H1.
  apply (achain_push (x_ly c) (rdW (x_W c) (x_mem c)) (rdW W3 m) (spZ (x_regs c)) (s0Z (x_regs c)) (raZ (x_regs c))
    (x_ch c) (cw_s1 c) Hch).
  + lia.
  + intros a Ha. apply G1; [lia | lia | intros HF; pose proof (cw2_FP_low c a HP HF); lia].
  + exact H0.
  + exact H1.
  + exact Hra4.
  + lia.
  + Z.div_mod_to_equations. lia.
  + lia.
  + lia.
- exists []. left. split; [right; left; rewrite Etop; lia | reflexivity].
Qed.
(* a run that writes nothing keeps the frame part and the untouched part of a cut *)
Lemma cw2_un_ext : forall c ly S W (m m' : word -> option byte), (forall x, m' x = m x) ->
cw_un B MT c ly S W m -> cw_un B MT c ly S W m'.
Proof.
intros c ly S W m m' He [U1 U2 U3 U4 U5 U6 U7 U8]. constructor; try assumption.
- intros a Ha Hb Hc. rewrite (cw2_aview_ext (w_H W) m m' He). exact (U1 a Ha Hb Hc).
- intros p n i Hp Hi. rewrite (cw2_aview_ext (w_H W) m m' He). exact (U2 p n i Hp Hi).
- intros cid pos a Hin Ha. rewrite (cw2_aview_ext (w_H W) m m' He). exact (U3 cid pos a Hin Ha).
- intros i Hi. rewrite (cw2_aview_ext (w_H W) m m' He). exact (U8 i Hi).
Qed.
Lemma cw2_fi_ext : forall c k ly S W regs (m : word -> option byte) md regs' m' md',
cw_fi B c k ly S W regs m md ->
ajournal SEGS B CHAIN_WORDS_STK (cw_sp0 c) (cw_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c) [(3, x_fpos c)]
  ly S W m' md' k ->
(forall x, m' x = m x) ->
getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 -> getr regs' 8 = getr regs 8 ->
getr regs' 9 = getr regs 9 -> getr regs' 18 = getr regs 18 -> getr regs' 24 = getr regs 24 ->
cw_fi B c k ly S W regs' m' md'.
Proof.
intros c k ly S W regs m md regs' m' md' [J1 G2 G3 G4 G8 G9 G18 G24 GNT GSV GFL] HJ He E2 E3 E4 E8 E9 E18 E24.
constructor.
- exact HJ.
- rewrite E2; exact G2.
- rewrite E3; exact G3.
- rewrite E4; exact G4.
- rewrite E8; exact G8.
- rewrite E9; exact G9.
- rewrite E18; exact G18.
- rewrite E24; exact G24.
- rewrite <- GNT. apply rdword_ext. intros kk Hk. apply (cw2_aview_ext (w_H W) m m' He).
- intros j r Hj. rewrite <- (GSV j r Hj). apply rdword_ext. intros kk Hk. apply (cw2_aview_ext (w_H W) m m' He).
- rewrite <- GFL. apply rdword_ext. intros kk Hk. apply (cw2_aview_ext (w_H W) m m' He).
Qed.
(* a shadow byte of a side-stack frame lies below the allocator's ceiling *)
Lemma cw2_shadow_low : forall f n a, 0 <= f -> 0 <= n -> f + n <= alloc_ceiling ->
in_zr a (shadow_addr f, n / 8) -> a < alloc_ceiling.
Proof.
intros f n a Hf Hn Hc Ha. pose proof asan_consts as (C1 & _). unfold in_zr, shadow_addr, SHADOW_OFF in *. cbn [fst snd] in Ha.
Z.div_mod_to_equations. lia.
Qed.
(* the run from KC writes only the two spill slots [s1 + 8, s1 + 24): every fact of the frame part and of the
   untouched part lies elsewhere (ntok at s1 + 24, the saved registers at [sp0 - 104, sp0), the frame, its shadow,
   the image and the blocks below the allocator's ceiling, which is below the real stack) *)
Lemma cw2_fi_keep : forall c k ly S W regs (m : word -> option byte) md regs' m' md',
cw_fi B c k ly S W regs m md ->
ajournal SEGS B CHAIN_WORDS_STK (cw_sp0 c) (cw_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c) [(3, x_fpos c)]
  ly S W m' md' k ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (cw_s1 c + 8 <= a < cw_s1 c + 24) -> rdW W m' a = rdW W m a) ->
getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 -> getr regs' 8 = getr regs 8 ->
getr regs' 9 = getr regs 9 -> getr regs' 18 = getr regs 18 -> getr regs' 24 = getr regs 24 ->
cw_fi B c k ly S W regs' m' md'.
Proof.
intros c k ly S W regs m md regs' m' md' [J1 G2 G3 G4 G8 G9 G18 G24 GNT GSV GFL] HJ He E2 E3 E4 E8 E9 E18 E24.
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & _).
assert (FS : 176 <= CHAIN_WORDS_STK) by (unfold CHAIN_WORDS_STK, NUMBER_STK, ESTACK; lia).
destruct (cw_s1_facts c Hal16) as (_ & Hs1).
assert (HinF : In (3, x_fpos c) (frames S)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly S W m' md' 3 (x_fpos c) HAR HinF) as (Hf0 & Hfc & _).
pose proof (cw2_frame_addr_le _ _ _ 3 (x_fpos c) Hly) as EF.
assert (F512 : fs_frame_bytes 3 = 512) by (vm_compute; reflexivity).
rewrite EF in Hf0, Hfc.
constructor.
- exact HJ.
- rewrite E2; exact G2.
- rewrite E3; exact G3.
- rewrite E4; exact G4.
- rewrite E8; exact G8.
- rewrite E9; exact G9.
- rewrite E18; exact G18.
- rewrite E24; exact G24.
- rewrite <- GNT. apply rdword_ext. intros kk Hk. apply He; lia.
- intros j r Hj. rewrite <- (GSV j r Hj). apply rdword_ext. intros kk Hk.
  assert (Hj13 : (j < length cw_saved)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
  change (length cw_saved) with 13%nat in Hj13. apply He; lia.
- rewrite <- GFL. apply rdword_ext. intros kk Hk. unfold cw_F in *. apply He; lia.
Qed.
Lemma cw2_un_keep : forall c k ly S W (m m' : word -> option byte) md',
ajournal SEGS B CHAIN_WORDS_STK (cw_sp0 c) (cw_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c) [(3, x_fpos c)]
  ly S W m' md' k ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (cw_s1 c + 8 <= a < cw_s1 c + 24) -> rdW W m' a = rdW W m a) ->
cw_un B MT c ly S W m -> cw_un B MT c ly S W m'.
Proof.
intros c k ly S W m m' md' HJ He [U1 U2 U3 U4 U5 U6 U7 U8].
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : 176 <= CHAIN_WORDS_STK) by (unfold CHAIN_WORDS_STK, NUMBER_STK, ESTACK; lia).
destruct (cw_s1_facts c Hal16) as (_ & Hs1).
assert (LOW : forall a, 0 <= a < alloc_ceiling -> rdW W m' a = rdW W m a) by (intros a Ha; apply He; lia).
constructor.
- intros a Ha Hno Her. rewrite LOW; [exact (U1 a Ha Hno Her)|]. pose proof (pa_segs_low a Ha). lia.
- intros p n i Hin Hi. rewrite LOW; [exact (U2 p n i Hin Hi)|].
  assert (Hin3 : In (p, n) (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym U4)); exact Hin).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin3) as (_ & Hp4 & Hc & _). lia.
- intros cid pos a Hin Ha. rewrite LOW; [exact (U3 cid pos a Hin Ha)|].
  assert (Hin3 : In (cid, pos) (frames S)) by (rewrite Hfrs; right; exact Hin).
  destruct (frames_bounds SEGS B LAWS ly S W m' md' cid pos HAR Hin3) as (Hf0 & Hfc & _).
  pose proof (cw2_frame_addr_le _ _ _ cid pos Hly) as EF.
  pose proof (fs_frame_bytes_nonneg cid) as Hfb.
  rewrite EF in Hf0, Hfc.
  unfold frame_rng in Ha. cbn [fst snd] in Ha. destruct Ha as [Ha | Ha].
  + unfold in_zr in Ha. cbn [fst snd] in Ha. lia.
  + pose proof (cw2_shadow_low (frame_addr (x_ly c) cid pos) (fs_frame_bytes cid) a ltac:(lia) Hfb Hfc Ha) as Hl.
    unfold in_zr, shadow_addr, SHADOW_OFF in Ha. cbn [fst snd] in Ha.
    assert (0 <= frame_addr (x_ly c) cid pos / 8) by (apply Z.div_pos; lia). lia.
- exact U4.
- exact U5.
- exact U6.
- exact U7.
- intros i Hi. rewrite LOW; [exact (U8 i Hi)|].
  assert (HinF : In (3, x_fpos c) (frames S)) by (rewrite Hfrs; left; reflexivity).
  destruct (frames_bounds SEGS B LAWS ly S W m' md' 3 (x_fpos c) HAR HinF) as (Hf0 & Hfc & _).
  pose proof (cw2_frame_addr_le _ _ _ 3 (x_fpos c) Hly) as EF.
  assert (F512 : fs_frame_bytes 3 = 512) by (vm_compute; reflexivity).
  rewrite EF in Hf0, Hfc. unfold cw_F, SB.
  assert (D0 : 0 <= frame_addr (x_ly c) 3 (x_fpos c) / 8) by (apply Z.div_pos; lia).
  assert (D8 : 8 * (frame_addr (x_ly c) 3 (x_fpos c) / 8) <= frame_addr (x_ly c) 3 (x_fpos c)) by (apply Z.mul_div_le; lia).
  lia.
Qed.
(* the frame part of a cut after the call of number, whose footprint is the cell s1 + 52 of the real frame *)
Lemma cw2_fi_call : forall c ly3 S3 W3 regs3 m3 md3 STK1 FP1 ly2 S2 W2 regs2 m2 md2 k1 k',
cw_fi B c 0 ly3 S3 W3 regs3 m3 md3 ->
ajournal SEGS B CHAIN_WORDS_STK (cw_sp0 c) (cw_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c) [(3, x_fpos c)]
  ly2 S2 W2 m2 md2 k' ->
ajournal SEGS B STK1 (cw_s1 c) FP1 ly3 S3 W3 m3 md3 [] ly2 S2 W2 m2 md2 k1 ->
(forall a, inFP FP1 a -> cw_s1 c + 32 <= a < cw_sp0 c - 104) ->
getr regs2 2 = getr regs3 2 -> getr regs2 3 = getr regs3 3 -> getr regs2 4 = getr regs3 4 ->
getr regs2 8 = getr regs3 8 -> getr regs2 9 = getr regs3 9 -> getr regs2 18 = getr regs3 18 ->
getr regs2 24 = getr regs3 24 ->
cw_fi B c k' ly2 S2 W2 regs2 m2 md2.
Proof.
intros c ly3 S3 W3 regs3 m3 md3 STK1 FP1 ly2 S2 W2 regs2 m2 md2 k1 k' [HJ G2 G3 G4 G8 G9 G18 G24 GNT GSV GFL]
  HJ2 HJc HFP E2 E3 E4 E8 E9 E18 E24.
pose proof HJ as (HAR3 & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & K1 & _ & _ & K4 & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & _).
assert (FS : 176 <= CHAIN_WORDS_STK) by (unfold CHAIN_WORDS_STK, NUMBER_STK, ESTACK; lia).
destruct (cw_s1_facts c Hal16) as (_ & Hs1).
constructor.
- exact HJ2.
- rewrite E2; exact G2.
- rewrite E3; exact G3.
- rewrite E4; exact G4.
- rewrite E8; exact G8.
- rewrite E9; exact G9.
- rewrite E18; exact G18.
- rewrite E24; exact G24.
- rewrite <- GNT. apply rdword_ext. intros kk Hk.
  apply K1; [lia | lia | intros HF; specialize (HFP _ HF); lia].
- intros j r Hj. rewrite <- (GSV j r Hj). apply rdword_ext. intros kk Hk.
  assert (Hj13 : (j < length cw_saved)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
  change (length cw_saved) with 13%nat in Hj13.
  apply K1; [lia | lia | intros HF; specialize (HFP _ HF); lia].
- rewrite <- GFL. apply rdword_ext. intros kk Hk.
  assert (Hin : In (3, x_fpos c) (frames S3)) by (rewrite Hfrs; left; reflexivity).
  destruct (frames_bounds SEGS B LAWS ly3 S3 W3 m3 md3 3 (x_fpos c) HAR3 Hin) as (Hf0 & Hfc & _).
  pose proof (cw2_frame_addr_le _ _ _ 3 (x_fpos c) Hly) as EF.
  assert (F512 : fs_frame_bytes 3 = 512) by (vm_compute; reflexivity).
  apply (K4 3 (x_fpos c)); [exact Hin | left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite EF; unfold cw_F in *; lia |].
  intros HF. specialize (HFP _ HF). rewrite EF in Hfc. unfold cw_F in *. lia.
Qed.
(* the untouched part of a cut after a program call whose footprint is a part of the real stack, which allocates
   nothing, keeps the blocks and changes only the side-stack frame state (number's frame form, number_c.v:124) *)
Lemma cw2_un_call : forall c ly3 S3 W3 m3 md3 STK1 sp1 FP1 ly2 S2 W2 m2 md2 k1 k,
ajournal SEGS B CHAIN_WORDS_STK (cw_sp0 c) (cw_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c) [(3, x_fpos c)]
  ly3 S3 W3 m3 md3 k ->
cw_un B MT c ly3 S3 W3 m3 ->
ajournal SEGS B STK1 sp1 FP1 ly3 S3 W3 m3 md3 [] ly2 S2 W2 m2 md2 k1 -> k1 <= 0 ->
(forall a, inFP FP1 a -> alloc_ceiling <= a) ->
Permutation (ablocks B ly2 S2) (ablocks B ly3 S3) ->
(exists f, S2 = set_fs f S3) ->
cw_un B MT c ly2 S2 W2 m2.
Proof.
intros c ly3 S3 W3 m3 md3 STK1 sp1 FP1 ly2 S2 W2 m2 md2 k1 k HJ [U1 U2 U3 U4 U5 U6 U7 U8] HJc Hk1 HFP HPERM HFS.
pose proof HJ as (HAR3 & Hly & _ & _ & _ & Hfrs & _).
pose proof HJc as (_ & _ & _ & _ & _ & _ & Hnev & _ & K1 & K2 & K3 & K4 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (NF : forall a, a < alloc_ceiling -> ~ inFP FP1 a) by (intros a Ha HF; specialize (HFP a HF); lia).
constructor.
- intros a Ha Hno Her. rewrite <- (U1 a Ha Hno Her). apply K3; [exact Ha | exact Hno | exact Her |].
  pose proof (pa_segs_low a Ha) as Hlow. split.
  + intros (r & Hr & H0). exfalso. apply (NF 0); [lia | exists r; split; [exact Hr | exact H0]].
  + apply NF. lia.
- intros p n i Hin Hi. rewrite <- (U2 p n i Hin Hi).
  assert (Hin3 : In (p, n) (ablocks B ly3 S3)) by (apply (Permutation_in _ (Permutation_sym U4)); exact Hin).
  assert (Hin2 : In (p, n) (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym HPERM)); exact Hin3).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin3) as (_ & _ & Hc & _).
  apply (K2 p n i Hin3 Hin2 Hi). apply NF. lia.
- intros cid pos a Hin Ha. rewrite <- (U3 cid pos a Hin Ha).
  assert (Hin3 : In (cid, pos) (frames S3)) by (rewrite Hfrs; right; exact Hin).
  destruct (frames_bounds SEGS B LAWS ly3 S3 W3 m3 md3 cid pos HAR3 Hin3) as (Hf0 & Hfc & _).
  pose proof (cw2_frame_addr_le _ _ _ cid pos Hly) as EF.
  pose proof (fs_frame_bytes_nonneg cid) as Hfb.
  apply (K4 cid pos a Hin3).
  + unfold frame_rng in *. cbn [fst snd] in *. rewrite EF. exact Ha.
  + apply NF. unfold frame_rng in Ha. cbn [fst snd] in Ha. rewrite <- EF in Ha. destruct Ha as [Ha | Ha].
    * unfold in_zr in Ha. cbn [fst snd] in Ha. lia.
    * exact (cw2_shadow_low (frame_addr ly3 cid pos) (fs_frame_bytes cid) a ltac:(lia) Hfb Hfc Ha).
- exact (Permutation_trans HPERM U4).
- lia.
- rewrite (blocks_bytes_bsum B ly2 S2), (bsum_perm _ _ HPERM), <- (blocks_bytes_bsum B ly3 S3). exact U6.
- destruct HFS as (f & ->). exact (mo_le_set_fs_r MT MTFL _ _ f 0 U7).
- intros i Hi. rewrite <- (U8 i Hi).
  assert (Hin3 : In (3, x_fpos c) (frames S3)) by (rewrite Hfrs; left; reflexivity).
  destruct (frames_bounds SEGS B LAWS ly3 S3 W3 m3 md3 3 (x_fpos c) HAR3 Hin3) as (Hf0 & Hfc & _).
  pose proof (cw2_frame_addr_le _ _ _ 3 (x_fpos c) Hly) as EF.
  assert (F512 : fs_frame_bytes 3 = 512) by (vm_compute; reflexivity).
  assert (Hsh : in_zr (SB + cw_F c / 8 + i) (shadow_addr (frame_addr ly3 3 (x_fpos c)), fs_frame_bytes 3 / 8)).
  { unfold in_zr, shadow_addr, cw_F, SB, SHADOW_OFF. cbn [fst snd]. rewrite EF, F512. change (512 / 8) with 64. lia. }
  apply (K4 3 (x_fpos c) _ Hin3); [right; exact Hsh|].
  apply NF. exact (cw2_shadow_low (frame_addr ly3 3 (x_fpos c)) (fs_frame_bytes 3) (SB + cw_F c / 8 + i)
    ltac:(lia) ltac:(rewrite F512; lia) Hfc Hsh).
Qed.
(* the symbolic state after the call: the registers only, a0 pinned to number's result *)
Definition cw2_ER (regs : bvmap 5 word) : env := Eimg (Ereg regs []).
Definition ss_cw2A (a0 : Z) : sstate := mkSS CW2_RET (sr_set sr_atoms 10 (SLit a0)) [] None (mkFacts [] [] []).
Lemma cw2_seedR : forall (W : world SEGS) mem (regs : bvmap 5 word) a0, getr regs 10 = Z_to_bv 64 a0 ->
st_ok_pi SEGS VAL (cw2_ER regs) (ss_cw2A a0)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + CW2_RET)) mem (seg_rom SEGS))) /\
sh_ok SEGS cw2_Bx [] (cw2_ER regs) (mrestrict (w_H W) mem).
Proof.
intros W mem regs a0 H10. split; [|constructor].
assert (HS : st_ok_pi SEGS VAL (cw2_ER regs) ss_cw2R
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + CW2_RET)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_cw2R. apply pa_entry_st_ok_full.
  - unfold cw2_ER. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - apply pairwise_disjoint_of_extents. cbn. exact I.
  - split; [exact I | split; exact I]. }
exact (st_ok_pi_pin_reg' _ _ _ 10%bv a0 HS H10 eq_refl).
Qed.
Lemma cw2_ER_reg : forall (regs : bvmap 5 word) m (rr : bv 5), Z.of_nat m = bv_unsigned rr ->
ew (cw2_ER regs) m = getr regs rr.
Proof.
intros regs m rr Hm. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
unfold cw2_ER. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm.
Qed.
Lemma cw2_regU : forall (H : word -> bool) E ss ms r, st_ok_pi SEGS VAL E ss (restrict H ms) ->
getr (ms_regs ms) r = Z_to_bv 64 (U E (sr_get (ss_regs ss) r)).
Proof. intros H E ss ms r HS. rewrite (st_ok_pi_restrict_reg H E ss ms r HS). unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.
(* the symbolic state at KC and its shadow entry, from the facts the cut point carries *)
Lemma cw2_seedC : forall ly S (W : world SEGS) mem md (regs : bvmap 5 word) tok ntok p1 s1,
AR SEGS B ly S W mem md ->
getr regs 9 = w64 s1 -> getr regs 10 = w64 (2 ^ 64 - 8) -> getr regs 21 = w64 tok -> getr regs 24 = w64 SB ->
afobj SEGS B ly S W mem tok (8 * ntok) -> 2 <= ntok ->
aval_mem (rdW W mem) (tok + 8) 8 p1 -> 0 <= p1 < 2 ^ 64 ->
alloc_ceiling <= s1 -> s1 + 24 <= 2 ^ 47 ->
(forall o, 8 <= o < 24 -> apresent (w_H W) mem (s1 + o)) ->
st_ok_pi SEGS VAL (cw2_EC regs p1) ss_cw2C
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + CW_KC)) mem (seg_rom SEGS))) /\
sh_ok SEGS cw2_Bx cw2_SH (cw2_EC regs p1) (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md regs tok ntok p1 s1 HAR H9 H10 H21 H24
  ((cid & pos & Hfr & Hcid & Hfa8 & Hlo & Hhi) & Htok8 & Hra) Hn HP1 Hp1 Hs1c Hs1h Hpr.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hfr) as (Hf0 & Hfc & Happ).
set (E := cw2_EC regs p1).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr).
{ intros m rr Hm. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  subst E. unfold cw2_EC. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (X32 : ew E 32 = w64 p1) by (subst E; unfold cw2_EC; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E9 : ew E 9 = Z_to_bv 64 s1) by (rewrite (EEo 9%nat 9%bv eq_refl); exact H9).
assert (E10 : ew E 10 = Z_to_bv 64 (2 ^ 64 - 8)) by (rewrite (EEo 10%nat 10%bv eq_refl); exact H10).
assert (E21 : ew E 21 = Z_to_bv 64 tok) by (rewrite (EEo 21%nat 21%bv eq_refl); exact H21).
assert (E24 : ew E 24 = Z_to_bv 64 SB) by (rewrite (EEo 24%nat 24%bv eq_refl); exact H24).
assert (U21 : base_val E (Some 21%nat) = tok).
{ cbn [base_val]. rewrite E21. apply unsigned_lit_small. lia. }
assert (U9 : base_val E (Some 9%nat) = s1).
{ cbn [base_val]. rewrite E9. apply unsigned_lit_small. lia. }
split.
- rewrite restrict_mkst_fx. unfold ss_cw2C. apply pa_entry_st_ok_full.
  + subst E. unfold cw2_EC. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold cw2_tokR, cw2_spR. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * rewrite U21. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ tok 8 8 (SOff 32 0) p1);
        [cbn [sv_denot]; rewrite X32, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
        | cbn; lia | lia | exact (cw2_val_mem SEGS (w_H W) mem _ 8%nat p1 HP1)].
    * rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpr. lia.
  + apply pairwise_disjoint_of_extents. unfold cw2_tokR, cw2_spR, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite U21, U9.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    split; [split; [left; lia | exact I] | split; exact I].
  + split; [|split; [exact I | exact I]].
    cbn [cw2_factsC f_atoms atoms_ok].
    split; [apply (cw2_afact E 9%nat s1); [exact E9 | lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]|].
    split; [apply (cw2_afact E 10%nat (2 ^ 64 - 8)); [exact E10 | lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]|].
    split; [apply (cw2_afact E 21%nat tok); [exact E21 | lia | lia | change (2 ^ 3) with 8; exact Htok8 | lia]|].
    split; [apply (cw2_afact E 24%nat SB); [exact E24 | unfold SB; lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]|].
    exact I.
- unfold sh_ok, cw2_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) mem E cw2_Bx 21 tok (8 * ntok) tok 8 16 Hra).
  + unfold cw2_Bx. apply U_atom; [exact E24 | cbv [SB SHADOW_OFF]; lia].
  + apply U_atom; [exact E21 | lia].
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold SHADOW_OFF. lia.
Qed.

(* number's post (number_c.v:117-124) at a call with word wd and result cell out *)
Definition cw2_numQ (wd : list byte) (out : Z) (W : world SEGS) (mem : word -> option byte) (ly : alayout) (S : astate)
  : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' md' =>
 match Verbs.number_m wd with
 | Some v => getr regs' 10 = w64 1 /\ aval_mem (rdW W' mem') out 4 v
 | None => getr regs' 10 = w64 0 /\ (forall i, 0 <= i < 4 -> rdW W' mem' (out + i) = rdW W mem (out + i))
 end /\
 Permutation (ablocks B ly' S') (ablocks B ly S) /\
 ly' = ly /\ (exists f, S' = set_fs f S).
Ltac cw2_q HP2 r :=
  apply (cw2_pres _ _ r HP2); cbv [acallee_saved];
  match goal with |- context [bv_unsigned ?x] => let z := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with z end;
  lia.
Ltac cw2_rr HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?E ?ss (restrict ?H ?ms) =>
    pose proof (cw2_regU H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr
  end.

Lemma cw_S2 : cw_S2P B MT.
Proof.
intros c HPRE HKR HKL0. unfold from_KC, cw_from.
intros ly3 S3 W3 regs3 mem3 md3 ((HFI & HUN) & R10 & R11 & R19 & R21 & R22 & Hn3).
pose proof (TRANSP c 0 ly3 S3 W3 regs3 mem3 md3 HPRE HFI HUN) as (HTOK & HTOKS & HCB & HREC & HROD & HRO).
pose proof HFI as [HJ F2 F3 F4 F8 F9 F18 F24 FNT FSV FFL].
pose proof (proj1 HJ) as HAR3.
pose proof (cp_ntok _ _ _ HPRE) as HN. pose proof (cp_ntokr _ _ _ HPRE) as HNR.
pose proof HTOKS as (Htk8 & Hlen & Hptr & Hwd).
destruct (nth_error (x_ptrs c) 1) as [p1|] eqn:Hp1;
  [| exfalso; apply nth_error_None in Hp1; rewrite Hlen in Hp1; lia].
destruct (nth_error (x_tks c) 1) as [wd|] eqn:Hwd1;
  [| exfalso; apply nth_error_None in Hwd1; lia].
pose proof (Hptr 1%nat p1 Hp1) as HP1. cbn [Z.of_nat Pos.of_succ_nat] in HP1.
replace (x_tok c + 8 * 1) with (x_tok c + 8) in HP1 by lia.
destruct (Hwd 1%nat p1 wd Hp1 Hwd1) as (HSTR & HWL & HCBP & HPCB).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 HCB) as (_ & Hcb4096 & Hcbc & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (req_size_pos (x_ncb c)) as Hreqcb.
assert (Hp1r : 4096 <= p1 /\ p1 + Z.of_nat (length wd) + 1 <= alloc_ceiling).
{ unfold req_size in *. destruct (x_ncb c =? 0) eqn:E0; [apply Z.eqb_eq in E0|apply Z.eqb_neq in E0]; lia. }
pose proof HJ as (_ & Hly & _ & _ & _ & Hfrs & Hnev3 & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
destruct (cw_s1_facts c Hal16) as (Hs1m & Hs1).
assert (FS : 176 + NUMBER_STK <= CHAIN_WORDS_STK) by (unfold CHAIN_WORDS_STK; lia).
assert (FN : 0 <= NUMBER_STK) by (unfold NUMBER_STK, ESTACK; lia).
assert (HinF : In (3, x_fpos c) (frames S3)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 mem3 md3 3 (x_fpos c) HAR3 HinF) as (HFa0 & HFac & _).
pose proof (cw2_frame_addr_le _ _ _ 3 (x_fpos c) Hly) as EF.
assert (HFb : 4096 <= cw_F c /\ cw_F c + 512 <= alloc_ceiling).
{ unfold cw_F. rewrite <- EF. assert (F512 : fs_frame_bytes 3 = 512) by (vm_compute; reflexivity). lia. }
pose proof HTOK as ((cidT & posT & HfrT & _ & _ & HloT & HhiT) & _ & _).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 mem3 md3 cidT posT HAR3 HfrT) as (HTa0 & HTc & _).
pose proof (cp_tok64 _ _ _ HPRE) as Htok64.
pose proof pa_B_ok as HBASE. pose proof (pa_base_lo (PL := PL_cmd)) as HBLO.
(* the run from KC (+0x21c) to the call of number (+0x254): the spills, the two UBSan checks (decided by the atom
   facts), the inline shadow check of tok[1], the reloads, the load of tok[1] *)
destruct (cw2_seedC ly3 S3 W3 mem3 md3 regs3 (x_tok c) (x_ntok c) p1 (cw_s1 c) HAR3 F9 R10 R21 F24 HTOK
  ltac:(lia) HP1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros o Ho; apply Hpres; lia)) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (cw2_EC regs3 p1)) by (unfold cw2_EC; apply Eimg_env).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew (cw2_EC regs3 p1) m = getr regs3 rr).
{ intros m rr Hm. unfold cw2_EC. rewrite Eimg_low by (pose proof (bv_unsigned_in_range 5 rr) as Hr5;
    change (bv_modulus 5) with 32 in Hr5; unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (U9 : bv_unsigned (ew (cw2_EC regs3 p1) 9) = cw_sp0 c + (cw_s1 c - cw_sp0 c)).
{ rewrite (EEo 9%nat 9%bv eq_refl), F9. unfold w64. rewrite unsigned_lit_small by lia. lia. }
unfold cfg_at, w64.
paj_run_tok RUN HS HJ SHOK cw2_Bspan.
{ unfold ss_cw2C, cw2_tokR, cw2_spR. cbn [ss_mem].
  apply (awr_ok_cons_ro SEGS B); [cbn; lia|].
  eapply (awr_ok_cons_stack_off SEGS B) with (n := 9%nat) (d := cw_s1 c - cw_sp0 c);
    [reflexivity | exact U9 | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |].
  apply (awr_ok_nil SEGS B). }
pmkst HS.
set (mdv := with_vm_backing (m_vm_lazy md3) mat md3) in *. clearbody mdv.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19. prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22.
prreg HS (24%bv : bv 5) P24.
rewrite (EEo 2%nat 2%bv eq_refl) in P2. rewrite (EEo 3%nat 3%bv eq_refl) in P3. rewrite (EEo 4%nat 4%bv eq_refl) in P4.
rewrite (EEo 8%nat 8%bv eq_refl) in P8. rewrite (EEo 9%nat 9%bv eq_refl) in P9.
rewrite (EEo 9%nat 9%bv eq_refl), F9 in P11.
rewrite (EEo 18%nat 18%bv eq_refl) in P18. rewrite (EEo 19%nat 19%bv eq_refl) in P19.
rewrite (EEo 21%nat 21%bv eq_refl) in P21. rewrite (EEo 22%nat 22%bv eq_refl) in P22.
rewrite (EEo 24%nat 24%bv eq_refl) in P24.
assert (X32 : ew (cw2_EC regs3 p1) 32 = w64 p1)
  by (unfold cw2_EC; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 0)).
rewrite X32 in P10.
assert (RA : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + CW2_RET)) by (rewrite P1; reflexivity).
(* the run wrote only the two spill slots *)
assert (HEQ : forall a, 0 <= a < 2 ^ 64 -> ~ (cw_s1 c + 8 <= a < cw_s1 c + 24) -> rdW W3 (ms_mem ms) a = rdW W3 mem3 a).
{ apply (kept_of_frame (cw2_EC regs3 p1) (ss_mem ss_cw2C) (w_H W3) mem3 (ms_mem ms)
    (fun x => cw_s1 c + 8 <= x < cw_s1 c + 24) HFr).
  intros b wlo whi a Hin Hx.
  lazymatch type of Hin with In _ (windows ?rs) => let w := eval vm_compute in (windows rs) in change (In (b, wlo, whi) w) in Hin end.
  cbn [In] in Hin. cbv beta.
  destruct Hin as [Hq | [Hq | []]]; injection Hq as <- <- <-; cbn [base_val] in Hx; [lia|].
  rewrite U9 in Hx. lia. }
pose proof (cw2_fi_keep c 0 ly3 S3 W3 regs3 mem3 md3 (ms_regs ms) (ms_mem ms) mdv HFI HJ HEQ P2 P3 P4 P8 P9 P18 P24)
  as HFIc.
pose proof (cw2_un_keep c 0 ly3 S3 W3 mem3 (ms_mem ms) mdv HJ HEQ HUN) as HUNc.
(* the two spills, read back from the stack region of the symbolic state at the call *)
assert (SPc : cw_spills c W3 (ms_mem ms)).
{ lazymatch type of HS with st_ok _ ?E ?ssx (restrict _ ?msx) =>
    let r1 := eval vm_compute in (nth 1 (ss_mem ssx) cw2_spR) in
    pose proof (cw2_rd_reg8 E (w_H W3) msx ssx 1%nat r1 8 (9%bv : bv 5) (22%bv : bv 5) 9%nat 22%nat HS
      ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity) ltac:(cbn [In YP09.r_chunks]; auto 20)
      ltac:(vm_compute; reflexivity)) as G8;
    pose proof (cw2_rd_reg8 E (w_H W3) msx ssx 1%nat r1 16 (9%bv : bv 5) (19%bv : bv 5) 9%nat 19%nat HS
      ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity) ltac:(cbn [In YP09.r_chunks]; auto 20)
      ltac:(vm_compute; reflexivity)) as G16
  end.
  rewrite P9, F9, P22, R22 in G8. rewrite P9, F9, P19, R19 in G16.
  unfold w64 in G8, G16. rewrite !unsigned_lit_small in G8 by lia. rewrite !unsigned_lit_small in G16 by lia.
  exact (conj G8 G16). }
destruct (TRANSP c 0 ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdv HPRE HFIc HUNc) as
  (HTOKc & HTOKSc & HCBc & HRECc & HRODc & HROc).
pose proof HTOKSc as (_ & _ & _ & Hwdc).
destruct (Hwdc 1%nat p1 wd Hp1 Hwd1) as (HSTRc & _ & _ & _).
pose proof HFIc as [_ _ _ _ _ _ _ _ _ FSVc _].
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresC & _).
(* number's premises at the call *)
assert (P10' : getr (ms_regs ms) 10 = w64 p1) by exact P10.
assert (P11' : getr (ms_regs ms) 11 = w64 (cw_s1 c + 52)).
{ rewrite P11. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
assert (HBLK : in_blockA (ablocks B ly3 S3) p1 (Z.of_nat (length wd) + 1)).
{ exists (x_cb c), (x_ncb c). split; [exact HCBc | lia]. }
assert (Hout4 : (cw_s1 c + 52) mod 4 = 0) by (clear - Hs1m; Z.div_mod_to_equations; lia).
assert (Ho16 : (cw_s1 c - cw_sp0 c) mod 16 = 0).
{ destruct Hs1 as [-> | ->]; [replace (cw_sp0 c - 160 - cw_sp0 c) with (-160) by lia
  | replace (cw_sp0 c - 176 - cw_sp0 c) with (-176) by lia]; reflexivity. }
assert (HSPc : spZ (ms_regs ms) = cw_sp0 c + (cw_s1 c - cw_sp0 c)).
{ unfold spZ. rewrite P2, F2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (HSTKD : ((exists cid pos, In (cid, pos) (frames S3) /\
   frame_addr ly3 cid pos <= cw_s1 c + 52 /\ cw_s1 c + 52 + 4 <= frame_addr ly3 cid pos + fs_frame_bytes cid) /\
   range_addressable (rdW W3 (ms_mem ms)) SHADOW_OFF (cw_s1 c + 52) 4) \/
  (spZ (ms_regs ms) <= cw_s1 c + 52 /\ cw_s1 c + 52 + 4 <= ly_top ly3 /\
   (forall i, 0 <= i < 4 -> apresent (w_H W3) (ms_mem ms) (cw_s1 c + 52 + i)))).
{ right. split; [rewrite HSPc; lia|]. split; [rewrite Etop; lia|]. intros i Hi. apply HpresC. lia. }
assert (HAPART : iv_apart (cw_s1 c + 52) 4 (as_errno B) 4).
{ right. pose proof (pal_env B TL) as ((He0 & He4) & _). lia. }
assert (HFR6 : Z.of_nat (length (frames S3)) <= 6).
{ rewrite Hfrs. cbn [app length]. pose proof (cp_frames _ _ _ HPRE). lia. }
assert (EVR : 0 <= EV_SUP_RESP) by (apply Z.leb_le; vm_compute; reflexivity).
assert (HNEV0 : st_nev S3 + EV_NUMBER <= EV_MAX).
{ pose proof (cp_nev _ _ _ HPRE). unfold EV_CHAIN_WORDS, EV_NUMBER in *. lia. }
(* the call of number at +0x254: the chain at the call is afn_pre's, pushed by the prologue's frame record *)
destruct (cw2_chain c ly3 S3 W3 (ms_mem ms) mdv 0 HPRE HJ FSVc) as (ch1 & HCH).
assert (HCH' : achain ly3 (rdW W3 (ms_mem ms)) (cw_sp0 c + (cw_s1 c - cw_sp0 c)) (s0Z (ms_regs ms)) ch1).
{ replace (cw_sp0 c + (cw_s1 c - cw_sp0 c)) with (cw_s1 c) by lia.
  replace (s0Z (ms_regs ms)) with (cw_sp0 c) by (unfold s0Z; rewrite P8, F8; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
  exact HCH. }
assert (P3' : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite P3; exact F3).
assert (P4' : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite P4; exact F4).
assert (HRA : YK0s.ret_ok (getr (ms_regs ms) 1)) by (rewrite RA; apply ret_ok_codeptr_v; [unfold CW2_RET, AF_chain_words; lia | reflexivity]).
assert (HRA4 : 4096 <= bv_unsigned (getr (ms_regs ms) 1)).
{ rewrite RA. unfold CW2_RET, AF_chain_words in *. rewrite unsigned_lit_small by lia. lia. }
rewrite (proj1 (cw_sig_of SIGP)).
eapply SRr_bind.
{ refine (cl_callS_wide B LAWS W3 (ms_regs ms) (ms_mem ms) (Z_to_bv 64 (BASE + AF_number)) CHAIN_WORDS_STK (cw_sp0 c)
    (cw_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c) [(3, x_fpos c)] ly3 S3 mdv 0 NUMBER_STK
    [(cw_s1 c + 52, cw_s1 c + 52 + 4)] EV_NUMBER (cw_s1 c - cw_sp0 c) (getr (ms_regs ms) 1) ch1
    (cw2_numQ wd (cw_s1 c + 52) W3 (ms_mem ms) ly3 S3)
    HJ HSPc Ho16 ltac:(lia) FN ltac:(lia) P3' P4' eq_refl HRA HRA4 HCH' _ _ _).
  - intros HPRE1. exact (NUMBER fx ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdv ch1 p1 (cw_s1 c + 52) wd HPRE1 HRODc
      P10' ltac:(lia) P11' ltac:(lia) HBLK HSTRc ltac:(unfold LMAX; lia) Hout4 HSTKD HAPART HFR6 HNEV0).
  - intros a Ha. left. apply inFP_cons in Ha as [Ha | Ha]; [lia | exfalso; exact (inFP_nil a Ha)].
  - intros ly2' S2' W2' regs2' mem2' md2' HK a Ha Hw Hn.
    unfold cw2_numQ in HK. destruct HK as (HNUM & _).
    apply inFP_cons in Ha as [Ha | Ha]; [| exfalso; exact (inFP_nil a Ha)].
    destruct (Verbs.number_m wd) as [v|].
    + destruct HNUM as (_ & HV). replace a with (cw_s1 c + 52 + Z.of_nat (Z.to_nat (a - (cw_s1 c + 52)))) by lia.
      rewrite (HV (Z.to_nat (a - (cw_s1 c + 52))) ltac:(lia)). discriminate.
    + destruct HNUM as (_ & HKP). replace a with (cw_s1 c + 52 + (a - (cw_s1 c + 52))) by lia.
      rewrite (HKP (a - (cw_s1 c + 52)) ltac:(lia)).
      apply cw2_present_view. apply HpresC. lia. }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & HK2).
replace (cw_sp0 c + (cw_s1 c - cw_sp0 c)) with (cw_s1 c) in HJc2 by lia.
rewrite RA.
unfold cw2_numQ in HK2. destruct HK2 as (HNUM & HPERM2 & Hly2 & HFS2).
assert (Q2 : getr regs2 2 = getr (ms_regs ms) 2) by cw2_q HP2 (2%bv : bv 5).
assert (Q3 : getr regs2 3 = getr (ms_regs ms) 3) by cw2_q HP2 (3%bv : bv 5).
assert (Q4 : getr regs2 4 = getr (ms_regs ms) 4) by cw2_q HP2 (4%bv : bv 5).
assert (Q8 : getr regs2 8 = getr (ms_regs ms) 8) by cw2_q HP2 (8%bv : bv 5).
assert (Q9 : getr regs2 9 = getr (ms_regs ms) 9) by cw2_q HP2 (9%bv : bv 5).
assert (Q18 : getr regs2 18 = getr (ms_regs ms) 18) by cw2_q HP2 (18%bv : bv 5).
assert (Q19 : getr regs2 19 = getr (ms_regs ms) 19) by cw2_q HP2 (19%bv : bv 5).
assert (Q21 : getr regs2 21 = getr (ms_regs ms) 21) by cw2_q HP2 (21%bv : bv 5).
assert (Q22 : getr regs2 22 = getr (ms_regs ms) 22) by cw2_q HP2 (22%bv : bv 5).
assert (Q24 : getr regs2 24 = getr (ms_regs ms) 24) by cw2_q HP2 (24%bv : bv 5).
assert (HFP1 : forall a, inFP [(cw_s1 c + 52, cw_s1 c + 52 + 4)] a -> cw_s1 c + 32 <= a < cw_sp0 c - 104).
{ intros a Ha. apply inFP_cons in Ha as [Ha | Ha]; [lia | exfalso; exact (inFP_nil a Ha)]. }
assert (HFP1c : forall a, inFP [(cw_s1 c + 52, cw_s1 c + 52 + 4)] a -> alloc_ceiling <= a).
{ intros a Ha. specialize (HFP1 a Ha). lia. }
pose proof (cw2_fi_call c ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdv NUMBER_STK [(cw_s1 c + 52, cw_s1 c + 52 + 4)]
  ly2 S2 W2 regs2 mem2 md2 EV_NUMBER (0 + EV_NUMBER) HFIc HJ2 HJc2 HFP1 Q2 Q3 Q4 Q8 Q9 Q18 Q24) as HFI2.
pose proof (cw2_un_call c ly3 S3 W3 (ms_mem ms) mdv NUMBER_STK (cw_s1 c) [(cw_s1 c + 52, cw_s1 c + 52 + 4)]
  ly2 S2 W2 mem2 md2 EV_NUMBER 0 HJ HUNc HJc2 ltac:(unfold EV_NUMBER; lia) HFP1c HPERM2 HFS2) as HUN2.
(* the spills are above number's stack pointer and outside its footprint *)
assert (SP2 : cw_spills c W2 mem2).
{ destruct SPc as (S8 & S16). pose proof HJc2 as (_ & _ & _ & _ & _ & _ & _ & _ & K1 & _).
  split; [rewrite <- S8 | rewrite <- S16]; apply rdword_ext; intros kk Hk;
    (apply K1; [lia | lia | intros HFx; specialize (HFP1 _ HFx); lia]). }
clear HS SHOK HF HFr HG HEI0.
assert (V19 : ew (cw2_ER regs2) 19 = w64 (cw_F c)) by (rewrite (cw2_ER_reg regs2 19 19%bv eq_refl), Q19, P19; exact R19).
assert (V21 : ew (cw2_ER regs2) 21 = w64 (x_tok c)) by (rewrite (cw2_ER_reg regs2 21 21%bv eq_refl), Q21, P21; exact R21).
assert (V22 : ew (cw2_ER regs2) 22 = w64 (cw_F c)) by (rewrite (cw2_ER_reg regs2 22 22%bv eq_refl), Q22, P22; exact R22).
destruct (Verbs.number_m wd) as [v|] eqn:Hnum.
- (* number accepted tks[1]: the loop set-up (+0x25c..+0x274), then KL with j = 0 *)
  destruct HNUM as (HA1 & HVAL).
  destruct (cw2_seedR W2 mem2 regs2 1 HA1) as [HS2 SHOK2].
  assert (HEI2 : img_env VAL A_LIM (cw2_ER regs2)) by (unfold cw2_ER; apply Eimg_env).
  paj_run_to_tok RUNTO HS2 HJ2 SHOK2 cw2_Bspan CW_KL.
  { apply (awr_ok_nil SEGS B). }
  pmkst HS2.
  match goal with |- context [with_vm_backing (m_vm_lazy ?m) ?t ?m] =>
    set (mdk := with_vm_backing (m_vm_lazy m) t m) in *; clearbody mdk end.
  pose proof (cw2_frame_ro (cw2_ER regs2) (ss_mem (ss_cw2A 1)) mem2 _ ltac:(constructor) HF) as HEQ2.
  prreg HS2 (2%bv : bv 5) T2. prreg HS2 (3%bv : bv 5) T3. prreg HS2 (4%bv : bv 5) T4. prreg HS2 (8%bv : bv 5) T8.
  prreg HS2 (9%bv : bv 5) T9. prreg HS2 (18%bv : bv 5) T18. prreg HS2 (24%bv : bv 5) T24.
  rewrite (cw2_ER_reg regs2 2 2%bv eq_refl) in T2. rewrite (cw2_ER_reg regs2 3 3%bv eq_refl) in T3.
  rewrite (cw2_ER_reg regs2 4 4%bv eq_refl) in T4. rewrite (cw2_ER_reg regs2 8 8%bv eq_refl) in T8.
  rewrite (cw2_ER_reg regs2 9 9%bv eq_refl) in T9. rewrite (cw2_ER_reg regs2 18 18%bv eq_refl) in T18.
  rewrite (cw2_ER_reg regs2 24 24%bv eq_refl) in T24.
  pose proof (cw2_fi_ext c 0 ly2 S2 W2 regs2 mem2 md2 _ _ mdk HFI2 HJ2 HEQ2 T2 T3 T4 T8 T9 T18 T24) as HFIk.
  pose proof (cw2_un_ext c ly2 S2 W2 mem2 _ HEQ2 HUN2) as HUNk.
  cw2_rr HS2 (19%bv : bv 5) T19. cw2_rr HS2 (20%bv : bv 5) T20. cw2_rr HS2 (21%bv : bv 5) T21.
  cw2_rr HS2 (22%bv : bv 5) T22. cw2_rr HS2 (23%bv : bv 5) T23. cw2_rr HS2 (25%bv : bv 5) T25.
  cw2_rr HS2 (26%bv : bv 5) T26. cw2_rr HS2 (27%bv : bv 5) T27.
  unfold from_KL, cw_from in HKL0.
  apply (HKL0 ly2 S2 W2 (ms_regs ms0) (ms_mem ms0) mdk). unfold INV_KL.
  split; [exact (conj HFIk HUNk)|].
  split.
  { destruct SP2 as (S8 & S16).
    split; [rewrite <- S8 | rewrite <- S16]; apply rdword_ext; intros kk Hk; apply (cw2_aview_ext (w_H W2) mem2 _ HEQ2). }
  split; [lia|].
  split; [rewrite T19; unfold w64; f_equal; rewrite U_SLit; reflexivity|].
  split; [rewrite T20; unfold w64; f_equal; rewrite U_SAlu, U_SLit, U_SOff, V22; unfold w64;
    rewrite unsigned_lit_small, (zcanon_small (cw_F c + 32)) by lia; apply cw2_not; [lia | reflexivity]|].
  split; [rewrite T21; unfold w64; f_equal; rewrite U_SOff, V21; unfold w64;
    rewrite unsigned_lit_small, zcanon_small by lia; lia|].
  split; [rewrite T22; unfold w64; f_equal; rewrite U_SOff, V22; unfold w64;
    rewrite unsigned_lit_small, zcanon_small by lia; lia|].
  split; [rewrite T23; unfold w64; f_equal; rewrite U_SLit; reflexivity|].
  split; [rewrite T25; unfold w64; f_equal; rewrite U_SLit; reflexivity|].
  split; [rewrite T26; unfold w64; f_equal; rewrite U_SAlu, U_SLit, U_SOff, V21; unfold w64;
    rewrite unsigned_lit_small, Z.add_0_r, (zcanon_small (x_tok c)) by lia; apply cw2_not; [lia | reflexivity]|].
  split; [rewrite T27; unfold w64; f_equal; rewrite U_SLit; reflexivity|].
  exists v, []. split; [replace (nth 1 (x_tks c) []) with wd by (symmetry; apply nth_error_nth; exact Hwd1); exact Hnum|].
  split; [reflexivity|]. split.
  + intros k Hk. rewrite (cw2_aview_ext (w_H W2) mem2 _ HEQ2). exact (HVAL k Hk).
  + intros i Hi. cbn [map concat length] in Hi. lia.
- (* number refused tks[1]: the jump to KR1 *)
  destruct HNUM as (HA0 & _).
  destruct (cw2_seedR W2 mem2 regs2 0 HA0) as [HS2 SHOK2].
  assert (HEI2 : img_env VAL A_LIM (cw2_ER regs2)) by (unfold cw2_ER; apply Eimg_env).
  paj_run_to_tok RUNTO HS2 HJ2 SHOK2 cw2_Bspan CW_KR1.
  { apply (awr_ok_nil SEGS B). }
  pmkst HS2.
  match goal with |- context [with_vm_backing (m_vm_lazy ?m) ?t ?m] =>
    set (mdk := with_vm_backing (m_vm_lazy m) t m) in *; clearbody mdk end.
  pose proof (cw2_frame_ro (cw2_ER regs2) (ss_mem (ss_cw2A 0)) mem2 _ ltac:(constructor) HF) as HEQ2.
  prreg HS2 (2%bv : bv 5) T2. prreg HS2 (3%bv : bv 5) T3. prreg HS2 (4%bv : bv 5) T4. prreg HS2 (8%bv : bv 5) T8.
  prreg HS2 (9%bv : bv 5) T9. prreg HS2 (18%bv : bv 5) T18. prreg HS2 (24%bv : bv 5) T24.
  rewrite (cw2_ER_reg regs2 2 2%bv eq_refl) in T2. rewrite (cw2_ER_reg regs2 3 3%bv eq_refl) in T3.
  rewrite (cw2_ER_reg regs2 4 4%bv eq_refl) in T4. rewrite (cw2_ER_reg regs2 8 8%bv eq_refl) in T8.
  rewrite (cw2_ER_reg regs2 9 9%bv eq_refl) in T9. rewrite (cw2_ER_reg regs2 18 18%bv eq_refl) in T18.
  rewrite (cw2_ER_reg regs2 24 24%bv eq_refl) in T24.
  pose proof (cw2_fi_ext c 0 ly2 S2 W2 regs2 mem2 md2 _ _ mdk HFI2 HJ2 HEQ2 T2 T3 T4 T8 T9 T18 T24) as HFIk.
  pose proof (cw2_un_ext c ly2 S2 W2 mem2 _ HEQ2 HUN2) as HUNk.
  cw2_rr HS2 (19%bv : bv 5) T19. cw2_rr HS2 (22%bv : bv 5) T22.
  (* number refused tks[1]: chain_words_m rejects, chain_run answers err_invalid_operation *)
  assert (HCR : VerbsRun.chain_run (x_R c) (tl (x_tks c)) = sup_resp_m (x_R c) Verbs.err_invalid_operation).
  { assert (HL3 : (3 <= length (x_tks c))%nat) by lia. revert Hwd1 HL3.
    destruct (x_tks c) as [|t0 [|t1 [|t2 rest]]]; cbn [length nth_error tl]; intros E1 HL; try (exfalso; lia).
    injection E1 as E1. subst t1. unfold VerbsRun.chain_run, Verbs.chain_words_m. cbv beta iota. rewrite Hnum. reflexivity. }
  unfold from_KR1, cw_from in HKR.
  apply (HKR ly2 S2 W2 (ms_regs ms0) (ms_mem ms0) mdk). unfold INV_KR1.
  split; [exact (conj HFIk HUNk)|].
  split; [rewrite T19; unfold w64; f_equal; rewrite U_SOff, V19; unfold w64;
    rewrite unsigned_lit_small, zcanon_small by lia; lia|].
  split; [rewrite T22; unfold w64; f_equal; rewrite U_SOff, V22; unfold w64;
    rewrite unsigned_lit_small, zcanon_small by lia; lia|].
  exact HCR.
Qed.
End e.
End f.
End d.
