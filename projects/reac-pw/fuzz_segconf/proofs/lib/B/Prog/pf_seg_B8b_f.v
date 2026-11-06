(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of check_round_trip on the ASan build of plugin-hostd/fuzz_command
   (0x87fd8, 286 instructions), proving tcheck_round_trip_spec (check_round_trip_c.v), in the shape of cgif_file_fuzzer's
   walks (lib/A/AChc.v, ACh1..ACh8.v, AChf.v): one statement per point between two calls (ST_B .. ST_EPI below), each
   segment proved by a run of the symbolic executor over the position-abstract listing (CmdPaLib.v) from a fresh seed,
   the inline checks removed by the shadow tokens (PaShadow.v), and the call at its end composed into the journal:
   the class-5 side-stack frame by aj_stack_malloc_atS (PaCall.v) and, from check_round_trip_k.v, aj_set_shadow_atS
   (__asan_set_shadow_f8/_00) and aj_stack_free_cls_atS (__asan_stack_free_5); the strdup wrapper by crts4_strdup_sub,
   the free wrapper by afree04_sub (PaCall.v), the strcmp wrapper by aj_art_at (PaArt.v); the program callees
   rec_calls_copy, joined, send_message and rec_calls_free by cl_callS_wide and rec_calls_equal by cl_callS_na
   (PaNoChain.v), each with its contract as a Section hypothesis. The skip path (no word, or the daemon did not act)
   joins the epilogue at 0x88314; the abort edges (0x8838c) are excluded by rt_okA and the callees' posts.
   Re-fit to statement passes 4, 4b and 5: the callee and runtime hypotheses hold at every
   FP state (forall fx0) and the segments use them at the ambient fx. send_message reaches the printf wrappers, so the
   points before its return (ST_B .. ST_F) prove the FP-existential post crt_postF (apost_baseF); crt_s6 calls
   send_message by PaFx.v's cl_callS_wideF with the rounding-mode premise HFRM and goes on at the FP state fx1 it
   returns (srr_after_callF_base). The points after it (ST_G .. ST_EPI) prove apost_base at the ambient FP state, so
   once the sections close they hold at fx1 (crt_G, used so by tcheck_round_trip_spec_holds). The skip path lifts
   ST_EPI's post by apost_baseF_of_base (crts3_skip). Pass 5 removed astack_pres: s0 is the frame pointer sp0 at every
   call, so each call's frame chain is the prologue's frame record (ra at sp0 - 8, the entry s0 at sp0 - 16, from
   crt_frame) on afn_pre's chain (achain_push, crt_chain), and chain_pre for the runtime allocation entries is
   achain_chain_pre of it. joined's new premises at its call: len's 8 bytes present (the journal's window), and
   (pass 5b) the stack from len - 16 present, from the statement's astack_pres kept by astack_pres_journal. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_round_trip.v, with its module paths, module names and numbers changed; 431 of its 470 lines of code are new or changed and 5014 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca): the FOUND
   sub-walk of segment B8b of reac_segconf_parse_file's walk, pb8b_found_holds : forall n, HA_B8B_JOIN B n ->
   H_FOUND B n (lib/B/Prog/pf_pieces.v's cut FOUND 0x88eb0, lib/B/Prog/pf_seg_B8b_d.v's cut JOIN 0x88f00).
   A B8b sub-lane of the image-B G3 walk owner, 2026-10-30.
   proves function reac_segconf_parse_file (segment B8b, piece FOUND -> JOIN). Reuse search and CONFIRM:
   the rule-24 lookup record (the rule-24 checker 2026-10-30T16:55:47Z; none released).
    ADAPTED from the image-A G3 walk owner's image-A lanes on working branches (pf_a7_u.v, the refuse call from a
    parse_file cut; pf_a6_k.v; pf_a2.v's shadow alias), in the piece form of the image-B G3 walk owner's own
   compiled image-B pieces lib/B/Prog/pf_seg_B5_r2.v (the B5 segment lane) and pf_seg_B10b_j.v (the B10b segment lane), re-derived on
   image B's code.

   THE CODE (reac_segconf_parse_file.fuzz_segconf.asan-ubsan.s), 0x88eb0 .. 0x88efc, 20 instructions:
     0x88eb0 srli a0,s7,3 ; 0x88eb4 add a0,a0,s4 ; 0x88eb8 lb a0,0(a0)   B#36, the shadow byte of
             s7 = &c->seg[i].seen_gen (s4 = SHADOW_OFF)
     0x88ebc ld a2,24(s1)        slot 0x18 = shadow_addr (c + RC_GEN)
     0x88ec0 bnez a0,0x890d4     B#36's slow arm; NOT TAKEN (the byte is 0)
     0x88ec4 lb a1,0(a2)         B#37, the shadow byte of c->gen
     0x88ec8 mv a3,s3            a3 = &c->seg[i]
     0x88ecc lw a0,352(s3)       seen_gen (sign-extended)
     0x88ed0 bnez a1,0x890e4     B#37's slow arm; NOT TAKEN
     0x88ed4 ld a1,32(s1) ; 0x88ed8 lw a1,0(a1)   c->gen through slot 0x20 = c + RC_GEN
     0x88edc ld s7,192(s1)       s7 = np, the header name in buf (slot 0xc0)
     0x88ee0 bne a0,a1,0x88f00   -> JOIN with cf2 = cf when seen_gen <> gen
     0x88ee4 auipc a0 ; 0x88ee8 addi a2,a0,1852   a2 = 0x21620 = seg_litA_rc F_twice (listing object A_OBJ 68)
     0x88eec ld a0,200(s1) (c) ; 0x88ef0 mv a1,s6 (ln + 1) ; 0x88ef4 mv a3,s7 (np)
     0x88ef8 jal refuse          returns at 0x88efc
     0x88efc mv a3,s3            -> JOIN with cf2 = refuse cf (ln + 1) F_twice [AS name]
   Checks: B#36 and B#37, both discharged because the shadow byte of each granule is 0 (pf_seg_B8b_f_k.v's
   pb8bf_sh0 over pf_obj's sa_addr of the block: the last byte of the granule is addressable, so its shadow byte
   is 0), so neither slow arm (0x890d4-0x890e0, 0x890e4-0x890f4) is reached. UBSan trap sites in this range:
   none (T34 at 0x88f08 is JOIN's, in the sibling piece). Calls: refuse at 0x88ef8 only.
   The proof: one seed at FOUND whose regions are the four spill slots the piece reads (0x18, 0x20, 0xc0, 0xc8),
   the 4 bytes of seg[i].seen_gen, the 4 bytes of c->gen and the two zero shadow bytes (the first reached through
   the alias (s7 >> 3) + s4 = atom 35, as lib/A/Prog/pf_a2.v's pa2_shx does); one plain run to the compare
   0x88ee0; psrr_branch_pi; the unequal arm steps the decided `bne` to JOIN; the equal arm runs to the call,
   steps it with PaFx.v's cl_callSF under refuse_contract, lifts the FP state with srr_apost_baseF_lift, runs
   `mv a3,s3` and gives JOIN at the state refuse returned. A run that writes nothing leaves the memory function
   itself unchanged (functional_extensionality over frame_of, as pf_a7_u.v does).
   Section hypotheses: REF (refuse_contract at BASE + AF_refuse, every FP state), SIGP, OBJ, VRO (the read-only
   range's bounds: pf_seg_B8b_f_k.v's pb8bf_in_roP_img) and SSPX (the stack-protector cells at every AR state:
   pf_seg_B8b_f_k.v's pb8bf_base_move takes sa_ssp from it at the state refuse returned). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI08 YI09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaSB
PaCall PaCallRun PaArt PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_pieces pf_seg_B8b_d pf_seg_B8b_m
pf_seg_B8b_f_k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------- tactics (lib/B/Prog/pf_seg_B5_r2.v's) ---------- *)
Ltac pb8bf_rreg HS :=
 lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
 lazymatch type of HS with
 | st_ok_pi _ _ ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_pi_restrict_reg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 | st_ok ?sg ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_restrict_reg sg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 end end.
Ltac pb8bf_clear_md := repeat match goal with |- context [with_vm_backing (m_vm_lazy ?m) ?x ?m] =>
  let mdv := fresh "mdv" in set (mdv := with_vm_backing (m_vm_lazy m) x m) in *; clearbody mdv end.
Ltac pb8bf_in := cbn [In app]; repeat first [left; reflexivity | right].
(* no region of the seed has a write window, so every write-permission goal of a run is vacuous *)
Ltac pb8bf_awr :=
  try (lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
         let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end);
  first
    [ solve [ repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil ]
    | solve [ intros ?a (?r & Hr & Ha); vm_compute in Hr;
              repeat (destruct Hr as [<- | Hr];
                [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]); destruct Hr ]
    | solve [ intros ?a (?r & Hr & Ha); vm_compute in Hr; destruct Hr ]
    | awr_ok_tac ].
(* the memory a run that writes nothing leaves is the one it started from *)
Ltac pb8bf_same_mem HF Hmem :=
  lazymatch type of HF with
  | frame_of ?Ex ?rs ?m0 ?m1 =>
    assert (Hmem : m1 = m0) by
      (apply functional_extensionality; intros x; unfold frame_of in HF; rewrite HF; [reflexivity|];
       intros (r & Hr & Ha); vm_compute in Hr;
       repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|]);
       first [destruct Hr | exact Hr])
  end.

(* ---------- the seed state at FOUND ----------
   atoms 0 .. 31 the registers (s1 = 9, s3 = 19, s4 = 20, s6 = 22, s7 = 23), then
   32 c + RC_GEN, 33 np, 34 c, 35 shadow_addr (&c->seg[i].seen_gen), 36 shadow_addr (c + RC_GEN),
   37 c->seg[i].seen_gen, 38 c->gen *)
Definition PB8BF_SHX : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 23 0) (SLit 3)) (SOff 20 0).
Definition pb8bf_regions : smem :=
  [YP09.mkRegion (Some 9%nat) 0x18 0xd0 0 0
     [YP09.mkChunk 0x18 (CVal 8 (SOff 36 0)); YP09.mkChunk 0x20 (CVal 8 (SOff 32 0));
      YP09.mkChunk 0xc0 (CVal 8 (SOff 33 0)); YP09.mkChunk 0xc8 (CVal 8 (SOff 34 0))];
   YP09.mkRegion (Some 19%nat) 352 356 0 0 [YP09.mkChunk 352 (CVal 4 (SOff 37 0))];
   YP09.mkRegion (Some 32%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 38 0))];
   YP09.mkRegion (Some 35%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))];
   YP09.mkRegion (Some 36%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))]].
Definition pb8bf_ss : sstate :=
  mkSS PF_FOUND sr_atoms pb8bf_regions None (mkFacts [] [] [(PB8BF_SHX, SOff 35 0)]).
Definition pb8bf_ex (c np g1 g2 sg : Z) : list word :=
  [w64 (c + seg_spec.RC_GEN); w64 np; w64 c; w64 (shadow_addr sg); w64 (shadow_addr (c + seg_spec.RC_GEN));
   w64 g1; w64 g2].

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
(* the program callee of this piece (pf_pieces.v's segment list for B8b), at image B's numbers, every FP state *)
Hypothesis REF : forall fx0 : YK11.FPState,
  @refuse_contract fx0 rc SK SEGS B (BASE + AF_refuse) STK_refuse RLO_A RHI_A seg_litA_rc gotwA guardA.
(* the listing's facts over the walk's abstract instance (SegObj.v; the pinned instance gives each by
   computation): the call target and the object atom of F_twice's literal *)
Hypothesis SIGP : seg_sig_prog (PI := PI).
Hypothesis OBJ : seg_val_objs (PI := PI).
(* the read-only range's bounds (SegObj.v), for the image bytes the refuse call keeps *)
Hypothesis VRO : seg_val_relro (PI := PI).
(* the stack-protector cells at every AR state (the image-A owner's route A; image B's stage-2 SegRecCells gives it), used
   only at the state refuse returned (pf_seg_B8b_f_k.v's pb8bf_base_move) *)
Hypothesis SSPX : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) gotwA guardA.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

Section x. Context {fx : YK11.FPState}.
Let RUNP := SRr_run_pi_AJ (fx := fx) B LAWS.
Let BR := paj_branch (PI := PI).

Lemma pb8b_found : forall n, HA_B8B_JOIN B n -> H_FOUND (fx := fx) B n.
Proof.
intros n JOIN v pos lyc Sc Wc rX memc mdc cf nm o ln d np name i HI.
pose proof HI as (HB & HMID & HST0 & HSTR & HINB & HNL & HFIND & HSLC & HRG).
pose proof HB as (HCX & HFI & HOBJ & HSL & HFSH).
destruct (pb8b_geo B v pos lyc Sc Wc rX memc mdc HCX HFI) as (HGEO & Hin & EF & Hfrs & HAR).
pose proof HGEO as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _).
destruct (pb8b_SHb v pos HGEO) as (ESH & SH1 & SH2 & F8).
pose proof HFI as (HJ & Hly & HSc & HPERM & HSAV & HFLAG & HFRM & HTF & HC8 & HRG0).
pose proof HST0 as (HRC & HNM & HCNT).
pose proof HMID as (Ho & Hkn & HCTX).
destruct (pb8bf_blk B v pos lyc Sc Wc rX memc mdc HCX HFI HOBJ)
  as (Hc0 & Hc16 & Hc4096 & Hcceil & Hcapp & HADDRC & (bc & mc & Hinc & Hcb1 & Hcb2)).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof STK_values as (_ & SRF & _ & SPF & _).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
(* the entry the search found and the two u32 fields it compares *)
pose proof (pb8b_find_lt (rc_seg cf) name i HFIND) as Hilt.
assert (Hi32 : (i < 32)%nat) by (destruct HRC as (bs & _ & (_ & Hs32 & _)); lia).
assert (Hi31 : Z.of_nat i <= 31) by lia.
set (g1 := rs_seen_gen (nth i (rc_seg cf) rseg_d)) in *.
set (g2 := rc_gen cf) in *.
destruct (pb8bf_seen_word Wc memc (p_c v) cf i HRC Hilt ltac:(lia)) as (Hg1r & Hg1m).
destruct (pb8bf_gen_word Wc memc (p_c v) cf HRC ltac:(lia)) as (Hg2r & Hg2m).
set (sg := seg_spec.rseg_addr (p_c v) i + seg_spec.RS_SEEN_GEN) in *.
assert (Hsg1 : p_c v <= sg)
  by (unfold sg, seg_spec.rseg_addr, seg_spec.RS_SEEN_GEN, seg_spec.RSEG_SIZE; lia).
assert (Hsg2 : sg + 8 <= p_c v + seg_spec.SEG_C_SIZE)
  by (unfold sg, seg_spec.rseg_addr, seg_spec.RS_SEEN_GEN, seg_spec.RSEG_SIZE, seg_spec.SEG_C_SIZE; lia).
assert (Hgn1 : p_c v <= p_c v + seg_spec.RC_GEN) by (unfold seg_spec.RC_GEN; lia).
assert (Hgn2 : p_c v + seg_spec.RC_GEN + 8 <= p_c v + seg_spec.SEG_C_SIZE)
  by (unfold seg_spec.RC_GEN, seg_spec.SEG_C_SIZE; lia).
pose proof HADDRC as (_ & _ & _ & HRA & _).
assert (SH0A : rdW Wc memc (SHADOW_OFF + sg / 8) = Some 0)
  by exact (pb8bf_sh0 (rdW Wc memc) (p_c v) seg_spec.SEG_C_SIZE sg HRA Hsg1 Hsg2).
assert (SH0B : rdW Wc memc (SHADOW_OFF + (p_c v + seg_spec.RC_GEN) / 8) = Some 0)
  by exact (pb8bf_sh0 (rdW Wc memc) (p_c v) seg_spec.SEG_C_SIZE (p_c v + seg_spec.RC_GEN) HRA Hgn1 Hgn2).
(* the two shadow bytes lie apart from the block and below the stack *)
destruct (pb8bf_sh_apart B v pos lyc Sc Wc rX memc mdc sg HCX HFI HOBJ Hsg1 ltac:(lia)) as (HSA1 & HSA2).
destruct (pb8bf_sh_apart B v pos lyc Sc Wc rX memc mdc (p_c v + seg_spec.RC_GEN) HCX HFI HOBJ Hgn1 ltac:(lia))
  as (HSB1 & HSB2).
assert (Hsh1 : 0 <= SHADOW_OFF + sg / 8 < 2 ^ 64) by (unfold SHADOW_OFF in *; lia).
assert (Hsh2 : 0 <= SHADOW_OFF + (p_c v + seg_spec.RC_GEN) / 8 < 2 ^ 64) by (unfold SHADOW_OFF in *; lia).
(* the registers the cut names *)
assert (R2s : getr rX (Z_to_bv 5 2) = w64 (pf_s1 v)) by (apply (pb8b_rg rX _ 2 _ HRG0); pb8bf_in).
assert (R3g : getr rX (Z_to_bv 5 3) = w64 (as_gp B)) by (apply (pb8b_rg rX _ 3 _ HRG0); pb8bf_in).
assert (R4t : getr rX (Z_to_bv 5 4) = w64 (as_tp B)) by (apply (pb8b_rg rX _ 4 _ HRG0); pb8bf_in).
assert (R8 : getr rX (Z_to_bv 5 8) = w64 (pf_sp0 v)) by (apply (pb8b_rg rX _ 8 _ HRG0); pb8bf_in).
assert (R9 : getr rX (Z_to_bv 5 9) = w64 (pf_s1 v)) by (apply (pb8b_rg rX _ 9 _ HRG0); pb8bf_in).
assert (R20 : getr rX (Z_to_bv 5 20) = w64 SHADOW_OFF) by (apply (pb8b_rg rX _ 20 _ HRG0); pb8bf_in).
assert (R19 : getr rX (Z_to_bv 5 19) = w64 (seg_spec.rseg_addr (p_c v) i))
  by (apply (pb8b_rg rX _ 19 _ HRG); unfold PF_RL, PF_RM; pb8bf_in).
assert (R23 : getr rX (Z_to_bv 5 23) = w64 sg)
  by (apply (pb8b_rg rX _ 23 _ HRG); unfold PF_RL, PF_RM, sg; pb8bf_in).
assert (R22 : getr rX (Z_to_bv 5 22) = w64 (ln + 1))
  by (apply (pb8b_rg rX _ 22 _ HRG); unfold PF_RL, PF_RM; pb8bf_in).
(* the four spill slots the piece reads *)
assert (W18 : rdword (rdW Wc memc) (pf_s1 v + 0x18) = Some (shadow_addr (p_c v + seg_spec.RC_GEN)))
  by exact (proj1 (Forall_forall _ _) HSL (0x18, shadow_addr (p_c v + seg_spec.RC_GEN))
              ltac:(unfold PF_SL; pb8bf_in)).
assert (W20 : rdword (rdW Wc memc) (pf_s1 v + 0x20) = Some (p_c v + seg_spec.RC_GEN))
  by exact (proj1 (Forall_forall _ _) HSL (0x20, p_c v + seg_spec.RC_GEN) ltac:(unfold PF_SL; pb8bf_in)).
assert (WC8 : rdword (rdW Wc memc) (pf_s1 v + 0xc8) = Some (p_c v))
  by exact (proj1 (Forall_forall _ _) HC8 (0xc8, p_c v) ltac:(pb8bf_in)).
assert (WC0 : rdword (rdW Wc memc) (pf_s1 v + 0xc0) = Some np)
  by exact (proj1 (Forall_forall _ _) HSLC (0xc0, np) ltac:(pb8bf_in)).
(* the ranges of the values the atoms take *)
assert (Hnp : 0 <= np /\ np + Z.of_nat (length name) + 8 < pf_F v pos + 2048)
  by (destruct HINB as (Hb1 & Hb2); unfold PF_O_BUF in *; lia).
assert (Hsgr : 0 <= sg /\ sg + 8 <= p_c v + seg_spec.SEG_C_SIZE) by lia.
assert (Hshsg : shadow_addr sg = SHADOW_OFF + sg / 8) by reflexivity.
assert (Hshgn : shadow_addr (p_c v + seg_spec.RC_GEN) = SHADOW_OFF + (p_c v + seg_spec.RC_GEN) / 8)
  by reflexivity.
(* the environment of the seed *)
set (E := Eimg (Ereg rX (pb8bf_ex (p_c v) np g1 g2 sg))).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr rX r)
  by (intros k r Hk; subst E; apply ew_Eimg_Ereg_nat; exact Hk).
assert (EX : forall k, (k < 7)%nat -> ew E (32 + k)%nat = nth k (pb8bf_ex (p_c v) np g1 g2 sg) (w64 0)).
{ intros k Hk. subst E. rewrite Eimg_low by (unfold A_TEXT; lia).
  exact (ew_Ereg_extra rX (pb8bf_ex (p_c v) np g1 g2 sg) k). }
assert (E32 : ew E 32 = w64 (p_c v + seg_spec.RC_GEN)) by exact (EX 0%nat ltac:(lia)).
assert (E33 : ew E 33 = w64 np) by exact (EX 1%nat ltac:(lia)).
assert (E34 : ew E 34 = w64 (p_c v)) by exact (EX 2%nat ltac:(lia)).
assert (E35 : ew E 35 = w64 (shadow_addr sg)) by exact (EX 3%nat ltac:(lia)).
assert (E36 : ew E 36 = w64 (shadow_addr (p_c v + seg_spec.RC_GEN))) by exact (EX 4%nat ltac:(lia)).
assert (E37 : ew E 37 = w64 g1) by exact (EX 5%nat ltac:(lia)).
assert (E38 : ew E 38 = w64 g2) by exact (EX 6%nat ltac:(lia)).
assert (E9 : ew E 9 = w64 (pf_s1 v)) by (rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl); exact R9).
assert (E19 : ew E 19 = w64 (seg_spec.rseg_addr (p_c v) i))
  by (rewrite (EE 19%nat (Z_to_bv 5 19) eq_refl); exact R19).
assert (E20 : ew E 20 = w64 SHADOW_OFF) by (rewrite (EE 20%nat (Z_to_bv 5 20) eq_refl); exact R20).
assert (E23 : ew E 23 = w64 sg) by (rewrite (EE 23%nat (Z_to_bv 5 23) eq_refl); exact R23).
assert (Hrsg : 0 <= seg_spec.rseg_addr (p_c v) i /\
               seg_spec.rseg_addr (p_c v) i + 356 <= p_c v + seg_spec.SEG_C_SIZE)
  by (unfold seg_spec.rseg_addr, seg_spec.RSEG_SIZE, seg_spec.SEG_C_SIZE in *; lia).
assert (U9 : bv_unsigned (ew E 9) = pf_s1 v) by (rewrite E9; unfold w64; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E 19) = seg_spec.rseg_addr (p_c v) i)
  by (rewrite E19; unfold w64; apply unsigned_lit_small; unfold seg_spec.SEG_C_SIZE in *; lia).
assert (U32 : bv_unsigned (ew E 32) = p_c v + seg_spec.RC_GEN)
  by (rewrite E32; unfold w64; apply unsigned_lit_small; unfold seg_spec.RC_GEN, seg_spec.SEG_C_SIZE in *; lia).
assert (U35 : bv_unsigned (ew E 35) = SHADOW_OFF + sg / 8).
{ rewrite E35, Hshsg. unfold w64. apply unsigned_lit_small. exact Hsh1. }
assert (U36 : bv_unsigned (ew E 36) = SHADOW_OFF + (p_c v + seg_spec.RC_GEN) / 8).
{ rewrite E36, Hshgn. unfold w64. apply unsigned_lit_small. exact Hsh2. }
assert (U37 : U E (SOff 37 0) = g1) by (apply (U_atom E 37 g1); [rewrite E37; reflexivity | lia]).
assert (U38 : U E (SOff 38 0) = g2) by (apply (U_atom E 38 g2); [rewrite E38; reflexivity | lia]).
(* the two shadow bytes as memory bytes *)
assert (MB1 : mbyte SEGS (mrestrict (w_H Wc) memc) (SHADOW_OFF + sg / 8) = Some (Z_to_bv 8 0)).
{ unfold aview in SH0A.
  destruct (mbyte SEGS (mrestrict (w_H Wc) memc) (SHADOW_OFF + sg / 8)) as [bb|] eqn:EB;
    [|cbn [option_map] in SH0A; discriminate].
  cbn [option_map] in SH0A. injection SH0A as SH0A'.
  replace (Z_to_bv 8 0) with bb by (apply bv_eq; rewrite SH0A'; reflexivity). reflexivity. }
assert (MB2 : mbyte SEGS (mrestrict (w_H Wc) memc) (SHADOW_OFF + (p_c v + seg_spec.RC_GEN) / 8)
  = Some (Z_to_bv 8 0)).
{ unfold aview in SH0B.
  destruct (mbyte SEGS (mrestrict (w_H Wc) memc) (SHADOW_OFF + (p_c v + seg_spec.RC_GEN) / 8)) as [bb|] eqn:EB;
    [|cbn [option_map] in SH0B; discriminate].
  cbn [option_map] in SH0B. injection SH0B as SH0B'.
  replace (Z_to_bv 8 0) with bb by (apply bv_eq; rewrite SH0B'; reflexivity). reflexivity. }
(* the seed *)
assert (HS : st_ok_pi SEGS VAL E pb8bf_ss
  (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + PF_FOUND)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold pb8bf_ss. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold pb8bf_regions.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U9. split; [lia|]. split; [lia|]. split; [intros oo Hoo; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val SEGS E _ _ 0x18 8 (SOff 36 0) (shadow_addr (p_c v + seg_spec.RC_GEN)));
          [ cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
          | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); rewrite Hshgn; lia
          | cbn; lia
          | exact (val_mem_of_rdword SEGS _ _ _ _ W18) ].
      * apply (chunk_ok_val SEGS E _ _ 0x20 8 (SOff 32 0) (p_c v + seg_spec.RC_GEN));
          [ cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
          | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64);
            unfold seg_spec.RC_GEN, seg_spec.SEG_C_SIZE in *; lia
          | cbn; lia
          | exact (val_mem_of_rdword SEGS _ _ _ _ W20) ].
      * apply (chunk_ok_val SEGS E _ _ 0xc0 8 (SOff 33 0) np);
          [ cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
          | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia
          | cbn; lia
          | exact (val_mem_of_rdword SEGS _ _ _ _ WC0) ].
      * apply (chunk_ok_val SEGS E _ _ 0xc8 8 (SOff 34 0) (p_c v));
          [ cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
          | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold seg_spec.SEG_C_SIZE in *; lia
          | cbn; lia
          | exact (val_mem_of_rdword SEGS _ _ _ _ WC8) ].
    + rewrite U19. split; [lia|]. split; [unfold seg_spec.SEG_C_SIZE in *; lia|].
      split; [intros oo Hoo; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ _ 352 4 (SOff 37 0) g1);
        [ cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia
        | cbn; lia
        | replace (seg_spec.rseg_addr (p_c v) i + 352)
            with (seg_spec.rseg_addr (p_c v) i + seg_spec.RS_SEEN_GEN)
            by (unfold seg_spec.RS_SEEN_GEN; lia);
          exact Hg1m ].
    + rewrite U32. split; [unfold seg_spec.RC_GEN; lia|].
      split; [unfold seg_spec.RC_GEN, seg_spec.SEG_C_SIZE in *; lia|].
      split; [intros oo Hoo; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ _ 0 4 (SOff 38 0) g2);
        [ cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia
        | cbn; lia
        | rewrite Z.add_0_r; exact Hg2m ].
    + rewrite U35. split; [unfold SHADOW_OFF; lia|]. split; [lia|].
      split; [intros oo Hoo; lia|].
      apply Forall_cons; [|apply Forall_nil].
      intros k Hk. cbn [YP09.c_len YP09.cv_len YP09.c_off YP09.c_val] in Hk |- *.
      assert (Hk0 : k = 0) by (cbn in Hk; lia). subst k. exists (Z_to_bv 8 0).
      split; [cbn [cbyte sv_denot]; first [reflexivity | (vm_compute; reflexivity)]|].
      rewrite !Z.add_0_r. exact MB1.
    + rewrite U36. split; [unfold SHADOW_OFF; lia|]. split; [lia|].
      split; [intros oo Hoo; lia|].
      apply Forall_cons; [|apply Forall_nil].
      intros k Hk. cbn [YP09.c_len YP09.cv_len YP09.c_off YP09.c_val] in Hk |- *.
      assert (Hk0 : k = 0) by (cbn in Hk; lia). subst k. exists (Z_to_bv 8 0).
      split; [cbn [cbyte sv_denot]; first [reflexivity | (vm_compute; reflexivity)]|].
      rewrite !Z.add_0_r. exact MB2.
  - apply pairwise_disjoint_of_extents. unfold pb8bf_regions, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U19, U32, U35, U36.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    assert (D1 : (p_c v + seg_spec.RC_GEN) / 8 <= p_c v + seg_spec.RC_GEN)
      by (apply Z.div_le_upper_bound; unfold seg_spec.RC_GEN; lia).
    assert (D2 : 0 <= sg / 8) by (apply Z.div_pos; lia).
    assert (D3 : sg / 8 + 1 <= (p_c v + seg_spec.RC_GEN) / 8).
    { apply Z.le_trans with ((sg + 8) / 8);
        [ replace (sg + 8) with (sg + 1 * 8) by lia; rewrite Z.div_add by lia; lia
        | apply Z.div_le_mono;
          [lia | unfold sg, seg_spec.rseg_addr, seg_spec.RSEG_SIZE, seg_spec.RS_SEEN_GEN, seg_spec.RC_GEN; lia] ]. }
    unfold seg_spec.rseg_addr, seg_spec.RSEG_SIZE, seg_spec.RC_GEN, seg_spec.SEG_C_SIZE in *.
    unfold sg, seg_spec.RS_SEEN_GEN in *.
    repeat split; lia.
  - split; [first [exact I | apply Forall_nil | constructor]|].
    split; [first [exact I | apply Forall_nil | constructor]|].
    cbn [f_alias alias_ok]. split; [|exact I]. unfold PB8BF_SHX. apply U_inj.
    rewrite U_SAlu, U_srl3.
    rewrite (U_atom E 23 sg ltac:(rewrite E23; reflexivity) ltac:(unfold seg_spec.SEG_C_SIZE in *; lia)).
    rewrite (U_atom E 20 SHADOW_OFF ltac:(rewrite E20; reflexivity) ltac:(unfold SHADOW_OFF; lia)).
    rewrite (U_atom E 35 (SHADOW_OFF + sg / 8) ltac:(rewrite E35, Hshsg; reflexivity) ltac:(lia)).
    cbn [zalu_raw]. replace (sg / 8 + SHADOW_OFF) with (SHADOW_OFF + sg / 8) by lia.
    apply zcanon_id. unfold M64. lia. }
unfold cfg_at. change (w64 (BASE + PF_FOUND)) with (Z_to_bv 64 (BASE + PF_FOUND)).
(* the post, by the model's FOUND step *)
rewrite (pb8b_step_found cf nm name (ln + 1) i HFIND). cbv zeta.
(* 0x88eb0 .. 0x88edc: the two shadow checks, the two words, the name reloaded; up to the compare 0x88ee0 *)
paj_run_sh RUNP HS HJ.
{ pb8bf_awr. }
cbn [ms_mem mkst] in HFr, HG, HF.
pb8bf_same_mem HF Hmem1.
(* the run writes nothing: Hmem1 : ms_mem ms = memc, used after each pmkst *)
pb8bf_clear_md.
clear HFr HG HF.
psrr_branch_pi RUNP BR HS.
- (* 0x88ee0 taken: seen_gen <> gen, the arm is already at JOIN with cf2 = cf *)
  assert (HNE : (g1 =? g2) = false).
  { apply Z.eqb_neq. intros Heq.
    rewrite branch_ne_U in Hc. apply Bool.negb_true_iff, Z.eqb_neq in Hc. apply Hc.
    rewrite (pb8bf_U_sext E (SOff 37 0) g1 U37 ltac:(lia)).
    rewrite (pb8bf_U_sext E (SOff 38 0) g2 U38 ltac:(lia)).
    exact (pb8bf_sext32_eq g1 g2 ltac:(lia) ltac:(lia) Heq). }
  pose proof HNE as HNE'. unfold g1, g2 in HNE'. rewrite HNE'. clear Hc HNE'.
  (* 0x88ee0 `bne`, now decided by the branch's condition: to JOIN 0x88f00 *)
  paj_run_to_sh (SRr_run_to_pi_AJ (fx := fx) B LAWS) HS HJ PF_B8B_JOIN.
  { pb8bf_awr. }
  cbn [ms_mem mkst] in HFr, HG, HF.
  pb8bf_same_mem HF Hmem2.
  assert (Hmem2' : ms_mem ms0 = memc) by (rewrite Hmem2; exact Hmem1).
  pb8bf_clear_md.
  clear HFr HG HF.
  assert (QK : forall r, In r [2; 3; 4; 8; 9; 20; 18; 21; 26; 25; 22; 19] ->
      getr (ms_regs ms0) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
  { intros r Hr. cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr]; [pb8bf_rreg HS; rewrite pb8b_den_atom0; apply EE; reflexivity |]).
    destruct Hr. }
  assert (Q13 : getr (ms_regs ms0) (Z_to_bv 5 13) = w64 (seg_spec.rseg_addr (p_c v) i))
    by (pb8bf_rreg HS; rewrite pb8b_den_atom0; exact E19).
  assert (Q23 : getr (ms_regs ms0) (Z_to_bv 5 23) = w64 np)
    by (pb8bf_rreg HS; rewrite pb8b_den_atom0; exact E33).
  pmkst HS. rewrite Hmem2'.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?k)) ?mm ?rom) ?mdx) _ =>
    change (mkCfg (mkst rg (Z_to_bv 64 (BASE + k)) mm rom) mdx)
      with (cfg_at SEGS (BASE + PF_B8B_JOIN) rg mm mdx) end.
  apply (JOIN fx v pos lyc Sc Wc (ms_regs ms0) memc _ cf nm o ln d np name i).
  (* INV_FOUND at the run's model: only pf_fi's journal names it, and the run's journal is over the cut's reader *)
  rewrite Hmem2' in HJ.
  assert (HI' : INV_FOUND (fx := fx) B n v pos lyc Sc Wc rX memc mdv0 cf nm o ln d np name i).
  { destruct HI as (HB' & HI2). split; [|exact HI2].
    destruct HB' as (HCX' & HFI' & HB3). split; [exact HCX'|]. split; [|exact HB3].
    destruct HFI' as (_ & HFI2). split; [exact HJ | exact HFI2]. }
  exact (pb8bf_join_same B fx n v pos lyc Sc Wc rX (ms_regs ms0) memc _ cf nm o ln d np name i HI' QK Q13 Q23).
- (* 0x88ee0 not taken: seen_gen = gen, the F_twice refusal at 0x88ef8, then 0x88efc and JOIN *)
  assert (HEQ : (g1 =? g2) = true).
  { apply Z.eqb_eq. rewrite branch_ne_U in Hc. apply Bool.negb_false_iff, Z.eqb_eq in Hc. revert Hc.
    rewrite (pb8bf_U_sext E (SOff 37 0) g1 U37 ltac:(lia)).
    rewrite (pb8bf_U_sext E (SOff 38 0) g2 U38 ltac:(lia)).
    intros Hu. exact (pb8bf_sext32_inj g1 g2 ltac:(lia) ltac:(lia) Hu). }
  pose proof HEQ as HEQ'. unfold g1, g2 in HEQ'. rewrite HEQ'. clear Hc HEQ'.
  (* 0x88ee4 .. 0x88ef8: the literal, c, the lineno, the name, the call *)
  paj_run_shc RUNP (SRr_run_pi_AJ_call (fx := fx) B LAWS) HS HJ.
  { pb8bf_awr. }
  pb8bf_same_mem HF Hmem2.
  assert (Hmem2' : ms_mem ms0 = memc) by (rewrite Hmem2; exact Hmem1).
  rewrite Hmem2' in HJ.
  pb8bf_clear_md.
  clear HFr HG HF.
  (* INV_FOUND at the call state's model (only pf_fi's journal names the model) *)
  assert (HI' : INV_FOUND (fx := fx) B n v pos lyc Sc Wc rX memc mdv0 cf nm o ln d np name i).
  { destruct HI as (HB' & HI2). split; [|exact HI2].
    destruct HB' as (HCX' & HFI' & HB3). split; [exact HCX'|]. split; [|exact HB3].
    destruct HFI' as (_ & HFI2). split; [exact HJ | exact HFI2]. }
  (* the call's registers *)
  assert (C1r : getr (ms_regs ms0) 1 = Z_to_bv 64 (BASE + PF_B8B_J0)).
  { pb8bf_rreg HS. rewrite (codeptr_val E _ HEI). unfold PF_B8B_J0, AF_reac_segconf_parse_file.
    first [reflexivity | f_equal; lia]. }
  assert (C10 : getr (ms_regs ms0) 10 = w64 (p_c v))
    by (pb8bf_rreg HS; rewrite pb8b_den_atom0; exact E34).
  assert (C11 : getr (ms_regs ms0) 11 = w64 (ln + 1)).
  { pb8bf_rreg HS. rewrite pb8b_den_atom0, (EE 22%nat (Z_to_bv 5 22) eq_refl). exact R22. }
  assert (C12 : getr (ms_regs ms0) 12 = w64 (seg_litA_rc F_twice)).
  { pb8bf_rreg HS. rewrite pb8b_den_atom0. change 309%nat with (A_OBJ 68). exact (pb8bf_lit OBJ E HEI). }
  assert (C13 : getr (ms_regs ms0) 13 = w64 np)
    by (pb8bf_rreg HS; rewrite pb8b_den_atom0; exact E33).
  assert (C2r : getr (ms_regs ms0) 2 = w64 (pf_s1 v)).
  { pb8bf_rreg HS. rewrite pb8b_den_atom0, (EE 2%nat (Z_to_bv 5 2) eq_refl). exact R2s. }
  assert (C3r : getr (ms_regs ms0) 3 = w64 (as_gp B)).
  { pb8bf_rreg HS. rewrite pb8b_den_atom0, (EE 3%nat (Z_to_bv 5 3) eq_refl). exact R3g. }
  assert (C4r : getr (ms_regs ms0) 4 = w64 (as_tp B)).
  { pb8bf_rreg HS. rewrite pb8b_den_atom0, (EE 4%nat (Z_to_bv 5 4) eq_refl). exact R4t. }
  assert (C8r : getr (ms_regs ms0) 8 = w64 (pf_sp0 v)).
  { pb8bf_rreg HS. rewrite pb8b_den_atom0, (EE 8%nat (Z_to_bv 5 8) eq_refl). exact R8. }
  assert (Csp : spZ (ms_regs ms0) = pf_s1 v)
    by (unfold spZ; rewrite C2r; unfold w64; apply unsigned_lit_small; lia).
  pmkst HS. rewrite Hmem2'.
  (* VERIFY rule 1j-bis at 0x88ef8: refuse_contract's premises besides afn_pre *)
  destruct (pb8bf_refuse_site B fx n v pos lyc Sc Wc rX memc mdc cf nm o ln d np name i (ms_regs ms0) HI
    C10 C11 C12 C13 Csp) as (ROD & Hc64 & Hl64 & Hf64 & RPRE & ROOM & HEV).
  destruct (pb8bf_chain B fx v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as [ch1 HCH].
  rewrite (SIGP SS_refuse ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
  replace (seg_af SS_refuse) with AF_refuse by (vm_compute; reflexivity).
  unfold pf_postm, PF_POSTr.
  eapply SRr_bind.
  { eapply (cl_callSF (fx := fx) B LAWS Wc (ms_regs ms0) memc _ STK_reac_segconf_parse_file (pf_sp0 v)
      (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc _ 0
      STK_refuse (refuse_W (p_c v) cf) EV_refuse (pf_s1 v - pf_sp0 v) (Z_to_bv 64 (BASE + PF_B8B_J0)) ch1
      (fun ly2 S2 W2 regs2 mem2 md2 =>
         sa_rconf (rdW W2 mem2) (p_c v) (refuse cf (ln + 1) F_twice [AS name]) /\ sa_noalloc B lyc Sc ly2 S2) HJ).
    - rewrite Csp. lia.
    - exact (pb8b_m16 (pf_s1 v) (pf_sp0 v) S6 S3).
    - lia.
    - rewrite SRF. lia.
    - rewrite SRF, SPF. lia.
    - exact C3r.
    - exact C4r.
    - exact C1r.
    - apply ret_ok_codeptr_v; [unfold PF_B8B_J0, AF_reac_segconf_parse_file; lia | reflexivity].
    - rewrite unsigned_lit_small by (unfold PF_B8B_J0, AF_reac_segconf_parse_file; lia).
      unfold PF_B8B_J0, AF_reac_segconf_parse_file. lia.
    - replace (pf_sp0 v + (pf_s1 v - pf_sp0 v)) with (pf_s1 v) by lia.
      unfold s0Z. rewrite C8r. unfold w64. rewrite unsigned_lit_small by lia. exact HCH.
    - intros HPRE1. eapply SRr_mono.
      { exact (REF fx lyc Sc Wc (ms_regs ms0) memc _ ch1 (p_c v) (ln + 1) (seg_litA_rc F_twice) (ln + 1)
          cf F_twice [AS name] HPRE1 ROD C10 Hc64 C11 Hl64 C12 Hf64 RPRE ROOM HEV). }
      cbv beta. intros W' c' _ (fx' & ly' & S' & regs' & mem' & md' & -> & Hf1 & Hf2 & HJ' & HP' & HK').
      exists fx', ly', S', regs', mem', md'. split; [rewrite C1r; reflexivity|].
      split; [exact Hf1|]. split; [exact Hf2|]. split; [exact HJ'|]. split; [exact HP' | exact HK'].
    - intros a Ha. left. split; [exact (pb8bf_refuse_W_sub _ _ a Ha)|].
      apply pb8bf_refuse_W_in_block in Ha. exists bc, mc. split; [exact Hinc|].
      unfold seg_spec.RC_REFUSAL, seg_spec.RC_OVERFLOW, seg_spec.SEG_C_SIZE in *. lia. }
  cbv beta. intros W2 c2 _ (fx1 & ly2 & S2r & regs2 & mem2 & md2 & Hfx1 & -> & HJ2 & HJc2 & HP2 & (HRC2 & HNA2)).
  eapply (srr_apost_baseF_lift SEGS fx1); [exact Hfx1|].
  replace (pf_sp0 v + (pf_s1 v - pf_sp0 v)) with (pf_s1 v) in HJc2 by lia.
  replace (0 + EV_refuse) with 0 in HJ2 by (unfold EV_refuse; lia).
  (* back at 0x88efc, at the FP state refuse returned: one `mv a3,s3` to JOIN *)
  jafter_call_keep_hi HS 1024%nat regs2 (mrestrict (w_H W2) mem2) HP2 (@nil nat) HS2.
  try (lazymatch type of HS2 with ?P -> _ =>
    assert (HQ : P) by (first [apply Forall_nil | exact I | constructor]); specialize (HS2 HQ); clear HQ end).
  rewrite <- restrict_mkst_fx in HS2.
  apply (st_ok_pi_restrict_xfx fx fx1) in HS2.
  pose proof (img_env_havoc_hi E 1024 (map (getr regs2) CLOB) HEI ltac:(unfold A_LIM; lia)) as HEI2.
  clear HS.
  paj_run_to_sh (SRr_run_to_pi_AJ (fx := fx1) B LAWS) HS2 HJ2 PF_B8B_JOIN.
  { pb8bf_awr. }
  cbn [ms_mem mkst] in HFr, HG, HF.
  pb8bf_same_mem HF Hmem3.
  rewrite Hmem3 in HJ2.
  pb8bf_clear_md.
  clear HFr HG HF.
  (* the registers at JOIN *)
  assert (QK2 : forall r, In r [2; 3; 4; 8; 9; 20; 18; 21; 26; 25; 22; 19] ->
      getr (ms_regs ms1) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
  { intros r Hr. cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr];
      [ pb8bf_rreg HS2; rewrite pb8b_den_atom0, ew_havoc_old by (cbn; lia); apply EE; reflexivity |]).
    destruct Hr. }
  assert (Q213 : getr (ms_regs ms1) (Z_to_bv 5 13) = w64 (seg_spec.rseg_addr (p_c v) i)).
  { pb8bf_rreg HS2. rewrite pb8b_den_atom0, ew_havoc_old by (cbn; lia). exact E19. }
  assert (Q223 : getr (ms_regs ms1) (Z_to_bv 5 23) = w64 np).
  { pb8bf_rreg HS2. rewrite pb8b_den_atom0, ew_havoc_old by (cbn; lia). exact E33. }
  pmkst HS2. rewrite Hmem3.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?k)) ?mm ?rom) ?mdx) _ =>
    change (mkCfg (mkst rg (Z_to_bv 64 (BASE + k)) mm rom) mdx)
      with (cfg_at SEGS (BASE + PF_B8B_JOIN) rg mm mdx) end.
  apply (JOIN fx1 v pos ly2 S2r W2 (ms_regs ms1) mem2 _
    (refuse cf (ln + 1) F_twice [AS name]) nm o ln d np name i).
  exact (pb8bf_join_after B VRO SSPX fx fx1 n v pos lyc Sc Wc rX memc _ cf nm o ln d np name i ly2 S2r W2
    (ms_regs ms1) mem2 _ _ HI' Hfx1 HJ2 HJc2 HNA2 HRC2 QK2 Q213 Q223).
Qed.
End x.

(** ** The piece the owner composes: FOUND -> JOIN, at every FP state *)
Section y. Context {fx : YK11.FPState}.
Theorem pb8b_found_holds : forall n, HA_B8B_JOIN B n -> H_FOUND (fx := fx) B n.
Proof. intros n HJ. exact (pb8b_found (fx := fx) n HJ). Qed.
End y.

End e.
End f.
End d.
