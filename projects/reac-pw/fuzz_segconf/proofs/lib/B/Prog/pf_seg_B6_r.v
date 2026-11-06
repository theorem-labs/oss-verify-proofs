(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the boundary states and segment statements of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86530), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (the CL_*_stmtX statements: from a point of the function to its return, under the entry's context) and A/ACf5.v (rtcx, rt_base: the entry's facts bundled once). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths, module names, addresses and numbers changed; 469 of its 518 lines of code are new or changed and 289 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths and module names changed; 126 of its 152 lines of code are new or changed and 492 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/pf_a7_d.v, with its numbers changed; 295 of its 379 lines of code are new or changed and 68 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/pf_a11b_x1.v, with its module paths and module names changed; 146 of its 178 lines of code are new or changed and 347 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca): the REF3 piece
   of segment B6 of reac_segconf_parse_file's walk, b6_ref3_ok : HA_TAIL n -> H_REF3 n at every FP state.
   The B6 segment lane of the image-B G3 walk owner, 2026-10-30. proves no function (kind: segment piece of reac_segconf_parse_file's
   walk, the cut REF3 of segment B6).
   ADAPTED from the image-A G3 walk owner's image-A refuse sites lib/A/Prog/pf_a7_s.v (a working branch) through the
    image-B form of the sibling B7 segment lane (its pf_seg_B7_s.v b7_refuse_site_ok) and B11c segment lane (its
   pf_seg_B11c_r.v b11_refuse_site), and from lib/B/Prog/reac_segconf_parse.v for the shape of a program call
   (cl_callSF, the lift of apost_baseF to the FP state the callee returned).
   The code (reac_segconf_parse_file.fuzz_segconf.asan-ubsan.s), REF3 0x882b4 .. TAIL, 2 instructions, no
   inline check, no UBSan trap:
     0x882b4 jal 892f8 <refuse>     a0 = c (slot 0xc8), a1 = s6 = lineno = ln + 1, a2 = f's literal,
                                    a3 per pf_ref3 (511 for F_long from LONG, the line's pointer for F_neither
                                    from B9's `j 0x882b4` at 0x884c0); sp = s1
     0x882b8 j 0x88600              TAIL
   WHERE EACH PREMISE OF refuse_contract COMES FROM (INV_REF3's conjuncts): b6r_refuse_site below, which is
   b7_refuse_site_ok's rule over this lane's kit; the two argument shapes are pf_ref3's two disjuncts
   (F_long with args [AI 511], F_neither with args [AS x] and x a C string in buf).
   WHAT THE CUT AT TAIL IS REBUILT FROM: refuse's own ajournal (the callee journal cl_callSF returns) -- the
   slots, the saved registers and the cur slot by its above-ceiling clause, the class-5 frame, its 144 shadow
   cells and cur_name by its frames clause, the text's bytes by its blocks clause (reader_pre's sa_disj keeps
   the text's read span off the block c), the literals, the catalogue, the read-only window and the
   stack-protector cells by its image clause, the text's and the block's shadow re-derived from AR at the state
   refuse returned (b6_addr_of_heap, b6_tail_of_heap), and c's new bytes from refuse's own post.
   Section hypotheses: REFUSE (refuse_contract at image B's entry and window, at every FP state), SIGP, VRO,
   SSPX (sa_ssp at every AR state: after a refuse call the journal does not keep the guard cells' shadow, so
   the walk re-derives them from the record; the image-B G3 walk owner 18:4xZ). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq YG0d_tail.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun PaArt PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_pieces pf_seg_B6_k pf_seg_B6_a.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the two formats of the shared call 0x882b4 are refusal formats and literals of this module *)
Lemma b6r_long_fmt : In F_long seg_spec.REFUSE_FORMATS.
Proof. unfold seg_spec.REFUSE_FORMATS. cbn [In]. tauto. Qed.
Lemma b6r_neither_fmt : In F_neither seg_spec.REFUSE_FORMATS.
Proof. unfold seg_spec.REFUSE_FORMATS. cbn [In]. tauto. Qed.
Lemma b6r_long_lit : In F_long PARSE_FILE_LITS.
Proof. unfold PARSE_FILE_LITS. apply in_or_app. left. cbn [In]. tauto. Qed.
Lemma b6r_neither_lit : In F_neither PARSE_FILE_LITS.
Proof. unfold PARSE_FILE_LITS. apply in_or_app. left. cbn [In]. tauto. Qed.
Lemma b6r_long_kinds : seg_spec.conv_kinds F_long = map seg_spec.arg_is_s [AI 511].
Proof. vm_compute. reflexivity. Qed.
Lemma b6r_neither_kinds : forall x : list Z, seg_spec.conv_kinds F_neither = map seg_spec.arg_is_s [AS x].
Proof. intros x. vm_compute. reflexivity. Qed.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
(* the callee's contract at image B's entry and window, at every FP state (pf_pieces.v:861) *)
Hypothesis REFUSE : forall fx0 : YK11.FPState,
  @refuse_contract fx0 rc SK SEGS B (BASE + AF_refuse) STK_refuse RLO_A RHI_A seg_litA_rc gotwA guardA.
(* the listing's facts over the walk's abstract instance *)
Hypothesis SIGP : seg_sig_prog (PI := PI).
Hypothesis VRO : seg_val_relro (PI := PI).
(* the stack-protector cells at every AR state (the record pins them; stage 2's SegRecCells discharges it) *)
Hypothesis SSPX : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) gotwA guardA.

Section x. Context {fx : YK11.FPState}.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let b6r_RUNP := SRr_run_pi_AJ (fx := fx) B LAWS.
Let b6r_RUNC := SRr_run_pi_AJ_call (fx := fx) B LAWS.

(** ** The call site: what refuse_contract asks besides afn_pre *)
Definition b6r_refuse_call (v : pfv) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (memc : word -> option byte) (regs : bvmap 5 word) (cf : rconf) (ln : Z) (f : list Z) (args : list arg)
  : Prop :=
  arodata_okP SEGS RLO_A RHI_A B (rdW Wc memc) /\
  getr regs 10 = w64 (p_c v) /\ 0 <= p_c v < 2 ^ 64 /\
  getr regs 11 = w64 (ln + 1) /\ 0 <= ln + 1 < 2 ^ 64 /\
  getr regs 12 = w64 (seg_litA_rc f) /\ 0 <= seg_litA_rc f < 2 ^ 64 /\
  refuse_pre SEGS B seg_litA_rc gotwA guardA lyc Sc regs (rdW Wc memc) (p_c v) (ln + 1) (seg_litA_rc f)
    [getr regs 13; getr regs 14; getr regs 15; getr regs 16; getr regs 17] cf (ln + 1) f args /\
  sa_room Sc /\ st_nev Sc + EV_refuse <= EV_MAX.

(* the room for refuse's class-0 frame and the event budget, from the journal and pf_cx *)
Lemma b6r_room_ev : forall v pos lyc Sc Wc rX memc mdc sc, pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  sa_room Sc /\ st_nev Sc <= EV_MAX.
Proof.
intros v pos lyc Sc Wc rX memc mdc sc (HCX & HFI & _).
pose proof HCX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HROOM & HEV).
pose proof HFI as (HJ & _). pose proof HJ as (_ & _ & _ & _ & _ & Hfr & Hnev & _).
unfold sa_room_n in HROOM. unfold EV_reac_segconf_parse_file in HEV.
split; [|lia]. unfold sa_room. rewrite Hfr, length_app. cbn [length]. lia.
Qed.

(* the site rule: INV_REF3's facts give refuse_contract's premises besides afn_pre *)
Lemma b6r_refuse_site : forall n v pos lyc Sc Wc rX memc mdc cf cur' nm o ln d f fa args a3,
  INV_REF3 B n v pos lyc Sc Wc rX memc mdc cf cur' nm o ln d f fa args a3 ->
  b6r_refuse_call v lyc Sc Wc memc rX cf ln f args.
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf cur' nm o ln d f fa args a3 HI.
destruct HI as (HBASE & HMID & HST & HREF & HRG).
pose proof HBASE as (HCX & HFI & HOBJ & HSL & HFSH).
destruct (b6a_geo B v pos lyc Sc Wc rX memc mdc HCX HFI) as (HGEO & Hin & EF & Hfrs & HAR).
pose proof HGEO as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _).
pose proof HFI as (HJ & Hly & HSc & HPERM & HSAV & HFLAG & HFRM & HTF & HSLC & HRG0).
pose proof HTF as (C0 & C16 & TF1 & TF2 & LS).
pose proof HCX as (_ & _ & _ & HcB & _ & _ & _ & _ & _ & HROOM & HEV).
pose proof HOBJ as (_ & _ & _ & Ac & Hc & _ & LITS & HROD & SSP).
pose proof HJ as (_ & _ & _ & _ & _ & Hfr & Hnev & _ & _ & _ & _ & _ & _ & _ & HSTK & _).
destruct HSTK as (_ & _ & Hceil & _).
rewrite <- Hly in Hceil.
destruct HMID as (Ho & Hle & Hlctx).
destruct Hlctx as (Hon & _ & Hlnd & Hlno).
destruct HST as (HRC & HCUR & HNM & HCNT & HCURS).
pose proof HRC as (bs & _ & (_ & _ & _ & _ & HK8 & _)).
pose proof (b6a_le65535 _ LS) as LSZ.
assert (HLN : 0 <= ln + 1 < 2 ^ 31) by lia.
pose proof asan_consts as (AC1 & _).
assert (HF8 : pf_F v pos mod 8 = 0).
{ pose proof (Z.div_mod (pf_F v pos) 32 ltac:(lia)) as D. rewrite F3 in D.
  replace (pf_F v pos) with ((4 * (pf_F v pos / 32)) * 8) by lia. apply Z_mod_mult. }
(* the registers the cut names *)
assert (Hvalid : forall r x, In (r, x) [(10, p_c v); (11, ln + 1); (12, fa); (13, a3)] ->
    getr rX (Z_to_bv 5 r) = w64 x)
  by (intros r x Hrx; apply (b6a_rg rX _ r x HRG); apply in_or_app; right; apply in_or_app; right; exact Hrx).
assert (R10 : getr rX 10 = w64 (p_c v))
  by (apply (b6a_bvr rX _ 10); [reflexivity | apply Hvalid; b6a_in]).
assert (R11 : getr rX 11 = w64 (ln + 1))
  by (apply (b6a_bvr rX _ 11); [reflexivity | apply Hvalid; b6a_in]).
assert (R12 : getr rX 12 = w64 fa)
  by (apply (b6a_bvr rX _ 12); [reflexivity | apply Hvalid; b6a_in]).
assert (R13 : getr rX 13 = w64 a3)
  by (apply (b6a_bvr rX _ 13); [reflexivity | apply Hvalid; b6a_in]).
(* the format: either arm of pf_ref3 *)
assert (HFL : In f PARSE_FILE_LITS /\ In f seg_spec.REFUSE_FORMATS /\ fa = seg_litA_rc f).
{ destruct HREF as [(-> & -> & _ & _) | (-> & -> & _)].
  - split; [exact b6r_long_lit|]. split; [exact b6r_long_fmt | reflexivity].
  - split; [exact b6r_neither_lit|]. split; [exact b6r_neither_fmt | reflexivity]. }
destruct HFL as (HINL & HINF & HFA).
pose proof (LITS f HINL) as HLF.
pose proof HLF as (Hfp & _ & Hpin & _).
pose proof (Hpin lyc Sc Wc memc mdc HAR) as (_ & Hfp63 & _).
destruct (b6r_room_ev v pos lyc Sc Wc rX memc mdc PF_SC_LINE HBASE) as [HROOM2 HEV2].
(* the variadic registers *)
assert (HVA : sa_va_args (rdW Wc memc)
    [(ly_stk_lo lyc, spZ rX);
     (seg_spec.refusal_addr (p_c v) (length (rc_refusal cf)),
      seg_spec.refusal_addr (p_c v) (length (rc_refusal cf)) + seg_spec.RC_REFUSAL_LEN);
     (p_c v + seg_spec.RC_REFUSED, p_c v + seg_spec.RC_REFUSED + 4)]
    [getr rX 13; getr rX 14; getr rX 15; getr rX 16; getr rX 17] args /\
  refuse_va_locs (fun q n => sa_heap B lyc Sc q n \/ sa_fframe lyc Sc q n)
    [getr rX 13; getr rX 14; getr rX 15; getr rX 16; getr rX 17] args).
{ destruct HREF as [(_ & _ & -> & Ha3) | (_ & _ & (x & -> & HXS & HXI))].
  - rewrite R13, Ha3. cbn [sa_va_args refuse_va_locs sa_va_arg].
    split; [split; [split; [lia | apply b6a_w64_u; lia] | exact I] | exact I].
  - destruct HXI as [HI1 HI2].
    assert (HXL : (length x <= 65535)%nat)
      by (apply (Nat.le_trans _ 512); [unfold PF_O_BUF in HI1, HI2; lia
                                      | apply Nat.leb_le; vm_compute; reflexivity]).
    assert (VA := b6a_va_frame B v pos lyc Sc Wc memc mdc PF_SC_LINE (rdW Wc memc) a3 x
      (spZ rX) (length (rc_refusal cf)) (pf_F v pos + 0x240) HGEO HAR Hin EF HFSH HXS HXL
      ltac:(unfold PF_O_BUF in HI1; lia) ltac:(unfold PF_O_BUF in HI2; lia)
      ltac:(rewrite Zplus_mod, HF8; reflexivity) ltac:(lia)
      ltac:(intros y Hy; apply b6a_shb_line0; right;
            assert (Q1 : 8 <= (y - pf_F v pos) / 8) by (apply Z.div_le_lower_bound; unfold PF_O_BUF in HI1; lia);
            assert (Q2 : (y - pf_F v pos) / 8 < 72) by (apply Z.div_lt_upper_bound; unfold PF_O_BUF in HI2; lia);
            lia)
      Hc HK8 Hceil).
    destruct VA as [VA1 VA2].
    rewrite R13. cbn [sa_va_args refuse_va_locs sa_va_arg].
    rewrite (b6a_w64_u a3) by (unfold PF_O_BUF in HI1, HI2; lia).
    split; [split; [|exact I]|split; [right|exact I]].
    + revert VA1. cbn [sa_va_arg]. rewrite (b6a_w64_u a3) by (unfold PF_O_BUF in HI1, HI2; lia). tauto.
    + exact VA2. }
destruct HVA as [HVA1 HVA2].
unfold b6r_refuse_call.
split; [exact HROD|]. split; [exact R10|]. split; [exact HcB|].
split; [exact R11|]. split; [lia|]. split; [rewrite R12, HFA; reflexivity|]. split; [lia|].
split; [|split; [exact HROOM2 | unfold EV_refuse; lia]].
unfold refuse_pre.
split; [exact C0|]. split; [exact C16|]. split; [exact HRC|]. split; [exact Hc|]. split; [exact Ac|].
split; [destruct HCNT as [HC1 _]; lia|].
split; [exact HLN|]. split; [reflexivity|].
split; [exact HINF|].
split; [destruct HREF as [(-> & _ & -> & _) | (-> & _ & (x & -> & _))];
        [exact b6r_long_kinds | apply b6r_neither_kinds]|].
split; [lia|]. split; [reflexivity|]. split; [exact HLF|].
split; [exact HVA1|]. split; [exact HVA2|].
split; [exact HFRM|]. split; [exact SSP|].
intros y Hy. apply LITS. unfold PARSE_FILE_LITS. apply in_or_app. right. exact Hy.
Qed.
End x.
End d.
