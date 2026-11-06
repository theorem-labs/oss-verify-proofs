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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_round_trip.v, with its module paths and module names changed; 214 of its 259 lines of code are new or changed and 5008 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca): piece PB10_S of
   segment B10b of reac_segconf_parse_file's walk, pb10_s_ok : PB10_S B (lib/B/Prog/pf_seg_B10b_k.v:
   HA_JOIN n -> H_ROLEV n; ROLEV 0x88d6c -> JOIN 0x88dc8). A B10b sub-lane of the image-B G3 walk owner, 2026-10-30.
   proves no function (kind: segment lemma of reac_segconf_parse_file's walk, piece PB10_S of segment B10b; the
   function's reuse search and CONFIRM are the rule-24 lookup record).
   ADAPTED from the B10b segment lane's lib/B/Prog/pf_seg_B10b_j.v (961c19ce3f65: the seed at a cut, the cut rebuilt),
   image B's trim walk lib/B/Prog/trim_f.v / trim_s.v (a token run with a shadow entry, an awr_ok write, a UBSan
   trap refuted after psrr_branch_tok) and 501c0d516c69 fuzz_command lib/A/Prog/check_reply_s4.v (the snprintf
   site, in pf_seg_B10b_sj.v).

   SECTION HYPOTHESES (the segment's piece list, section 3), and only these:
     ASNP  forall fx0, RtFormat.asnprintf_realizes fx0 rc SEGS B (pa_sigma SS___interceptor_trampoline_snprintf)
           gotwA guardA  (the provenance snprintf, 0x88dc4);
     OBJ   seg_val_objs (PI := PI)  (the listing's object A_OBJ 35, the literal "%s", is 0x21340 = seg_litA_rc F_s).
   No SSPX, no VRO, no IMG: sa_ssp, arodata_okP and the literals are carried by the keep lemmas
   (pf_seg_B10b_sg.v: every one of them lies outside the block c and the snprintf window).

   THE CODE (reac_segconf_parse_file.fuzz_segconf.asan-ubsan.s), ROLEV 0x88d6c .. 0x88dc4, 23 instructions:
     0x88d6c ld a0,192(s1); 0x88d70 andi a0,a0,3; 0x88d74 bnez a0 -> 0x891c8 (unimp, T30)
     0x88d78 ld a3,192(s1); 0x88d7c addi a0,a3,16; srli a1,a0,3; add a1,a1,s4; lb a1,0(a1);
       0x88d8c bnez a1 -> 0x88fcc (B#31, slow arm 0x88fcc-0x88fd8, stub 0x89288 errpath_store4)
     0x88d90 sw s3,16(a3)                                         (cur->role = r)
     0x88d94 addi a0,a3,20; srli; add s4; lb; 0x88da4 bnez a1 -> 0x88fdc (B#32, slow arm 0x88fdc-0x88fe8, stub
       0x8928c errpath_store4)
     0x88da8 li a0,1; 0x88dac sw a0,20(a3)                        (cur->role_set = 1)
     0x88db0 addi a0,a3,160; 0x88db4 auipc a1; 0x88db8 addi a2,a1,1420 (A_OBJ 35 = 0x21340 "%s"); li a1,96;
       0x88dc0 ld a3,72(s1) (slot 0x48 = c + RC_READING); 0x88dc4 jal snprintf      (returns to JOIN 0x88dc8)
   THE PROOF: a seed at ROLEV (b10s_seed: slot 0x48 and slot 0xc0 as a read-only region on s1's atom, their words
   the atoms 33 = c + RC_READING and 32 = cur; cur's two role words a writable region on atom 32; the shadow base
   s4 pinned to SHADOW_OFF; the shadow entry [cur + 16, cur + 24) on atom 32), a token run to the T30 branch, the
   branch split (psrr_branch_tok), a second token run to the call; then pf_seg_B10b_sj.v's b10s_from_call.
     T30 (0x88d74, `bnez a0` on cur & 3): taken only if cur mod 4 <> 0; cur = c + 356 gi (pf_st's slot 0xc0,
       seg_spec.rseg_addr) with c mod 16 = 0 (pf_tf in pf_fi) and 356 = 4 * 89, so cur mod 4 = 0 (b10s_cur4,
       b10s_t30): the taken side is refuted.
     B#31 (cur + 16, 0x88d7c-0x88d8c) and B#32 (cur + 20, 0x88d94-0x88da4): decided by the token executor from the
       shadow entry [cur + 16, cur + 24) (shent_ok_of_range: the 8 bytes lie in the block c, which pf_obj's
       sa_addr c SEG_C_SIZE makes addressable, gi < 32 by sa_rconf's rconf_enc; an application range, apart from
       the shadow band). B#31's shadow byte is covered (loaded as 0, the `bnez` falls through); B#32's granule check
       takes the token path through its slow arm's pattern (0x88fdc andi / addi / blt, need covered by the entry),
       so neither error stub is reached. No obligation is left.
     The two `sw` (0x88d90, 0x88dac) write the region on atom 32, inside the block c and the footprint
       RC_PARSE_W c (awr_byte's heap-in-FP case).
   Instructions walked: 0x88d6c .. 0x88dc4 (23); the cold arms 0x88fcc .. 0x88fe8 are not executed (the token run
   decides both checks on their fast path). Checks discharged: B#31, B#32. Trap discharged: T30. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtFormat.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa SegObj SegGlob SegPaLib PaCall PaDenot.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaLibG PaLibF PaLibH PaSB PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_pieces pf_seg_B10b_k pf_seg_B10b_f
  pf_seg_B10b_sg pf_seg_B10b_sj.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------- the seed at ROLEV (0x88d6c) ---------- *)
Definition b10s_regions : smem :=
  [YP09.mkRegion (Some 9%nat) 0x48 0xc8 0 0
     [YP09.mkChunk 0x48 (CVal 8 (SOff 33 0)); YP09.mkChunk 0xc0 (CVal 8 (SOff 32 0))];
   YP09.mkRegion (Some 32%nat) 16 24 16 24 []].
Definition b10s_facts : facts := mkFacts [(20%nat, mkAF SB SB 0); (32%nat, mkAF 4096 (2 ^ 47 - 4096) 0)] [] [].
Definition b10s_ss : sstate := mkSS PF_ROLEV sr_atoms b10s_regions None b10s_facts.
Definition b10s_Bx : sv := SOff 20 0.
Definition b10s_SH : list shent := [mkSHE 32 16 24].
(* a register read off a symbolic state (the B2 segment lane's pb2_rreg) *)
Ltac b10s_rreg HS :=
 lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
 lazymatch type of HS with
 | st_ok_pi _ _ ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_pi_restrict_reg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 | st_ok ?sg ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_restrict_reg sg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 end end.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
Hypothesis ASNP : forall fx0 : YK11.FPState,
  @RtFormat.asnprintf_realizes fx0 rc SEGS B (pa_sigma SS___interceptor_trampoline_snprintf) gotwA guardA.
Hypothesis OBJ : seg_val_objs (PI := PI).
Section x. Context {fx : YK11.FPState}.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).

Lemma b10s_seed : forall (Wc : world SEGS) (rX : bvmap 5 word) memc s1 cur rdg,
  getr rX (Z_to_bv 5 9) = w64 s1 -> getr rX (Z_to_bv 5 20) = w64 SHADOW_OFF ->
  0 <= s1 -> s1 + 0xc8 <= 2 ^ 64 ->
  rdword (rdW Wc memc) (s1 + 0x48) = Some rdg -> rdword (rdW Wc memc) (s1 + 0xc0) = Some cur ->
  0 <= rdg < 2 ^ 64 -> 4096 <= cur -> cur + 4096 <= 2 ^ 47 -> cur + 24 <= s1 ->
  (forall o, 16 <= o < 24 -> apresent (w_H Wc) memc (cur + o)) ->
  st_ok_pi SEGS VAL (Eimg (Ereg rX [w64 cur; w64 rdg])) b10s_ss
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + PF_ROLEV)) memc (seg_rom SEGS))).
Proof.
intros Wc rX memc s1 cur rdg R9 R20 Hs0 Hs1 W48 WC0 Hrdg Hc0 Hc1 Hc2 Hpr.
set (E := Eimg (Ereg rX [w64 cur; w64 rdg])).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr rX r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j, (j < 2)%nat -> ew E (32 + j) = nth j [w64 cur; w64 rdg] (Z_to_bv 64 0))
  by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33. cbn [Nat.add nth] in E32, E33.
assert (U9 : bv_unsigned (ew E 9) = s1)
  by (rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E 20) = SHADOW_OFF)
  by (rewrite (EE 20%nat (Z_to_bv 5 20) eq_refl), R20; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew E 32) = cur) by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = rdg) by (rewrite E33; unfold w64; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold b10s_ss. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold b10s_regions. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    * apply (chunk_ok_val SEGS E _ s1 0x48 8 (SOff 33 0) rdg).
      -- cbn [sv_denot]. rewrite U33, Z.add_0_r. reflexivity.
      -- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
      -- cbn. lia.
      -- exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ W48).
    * apply (chunk_ok_val SEGS E _ s1 0xc0 8 (SOff 32 0) cur).
      -- cbn [sv_denot]. rewrite U32, Z.add_0_r. reflexivity.
      -- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
      -- cbn. lia.
      -- exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ WC0).
  + rewrite U32. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpr. lia.
- unfold b10s_regions. cbn [YP09.pairwise_disjoint YP09.all_disjoint]. unfold YP09.extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val]. rewrite U9, U32. repeat split; lia.
- split; [|split; exact I].
  cbn [b10s_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U20, U32. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB, SHADOW_OFF in *. repeat split; lia.
Qed.

(* ---------- the piece: ROLEV -> the call -> JOIN ---------- *)
Lemma b10s_rolev : forall n, HA_JOIN B n -> H_ROLEV (fx := fx) B n.
Proof.
intros n HJN v pos lyc Sc Wc rX memc mdc cf nm o ln d gi val r HI.
pose proof HI as (HBASE & HMID & HST & HROLE & HRG).
pose proof HBASE as (HCX & HFI & HOBJ & HSL & HFSH).
destruct (b10s_geo B v pos lyc Sc Wc rX memc mdc HCX HFI) as (HGEO & Hin & EF & Hfrs & HAR).
pose proof HFI as (HJ & Hly & HSc & HPERM & HSAV & HFLAG & HFRM & HTF & HC8 & HRG0).
pose proof HST as (HRC & HCUR & HNM & HCNT & HC0).
pose proof HOBJ as (_ & _ & _ & HC4 & HC5 & _).
destruct (b10s_cblk B v pos lyc Sc Wc memc mdc HAR Hin EF HTF HC5) as (HCP & bb & mm & Hbin & Hb1 & Hb2).
pose proof HGEO as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _).
pose proof HCP as (C1 & C2 & C3 & C4 & C5 & C6).
pose proof asan_consts as (A1 & _).
assert (Hgi32 : (gi < 32)%nat) by (destruct HRC as (bs & _ & (_ & H32 & _)); unfold pf_cur_ok in HCUR; lia).
rewrite (b10b_step_some cf gi nm (ln + 1) val r HROLE).
set (cur := seg_spec.rseg_addr (p_c v) gi).
assert (Ecur : cur = p_c v + 356 * Z.of_nat gi) by reflexivity.
pose proof (b10s_cur4 (p_c v) gi C3) as Hcur4. fold cur in Hcur4.
assert (R9 : getr rX (Z_to_bv 5 9) = w64 (pf_s1 v)) by (apply (b10s_rg rX _ _ _ HRG0); b10s_in).
assert (R20 : getr rX (Z_to_bv 5 20) = w64 SHADOW_OFF) by (apply (b10s_rg rX _ _ _ HRG0); b10s_in).
assert (R19 : getr rX (Z_to_bv 5 19) = w64 r) by (apply (b10s_rg rX _ _ _ HRG); unfold PF_RL, PF_RM; b10s_in).
pose proof (b10b_role_range _ _ HROLE) as Hr04.
pose proof (proj1 (Forall_forall _ _) HSL (0x48, p_c v + seg_spec.RC_READING) ltac:(unfold PF_SL; b10s_in)) as W48.
cbn [fst snd] in W48.
change (pf_cur_ptr (p_c v) (Some gi)) with cur in HC0.
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc bb mm HAR Hbin) as (_ & _ & _ & _ & Hblk & _).
unfold seg_spec.SEG_C_SIZE, seg_spec.RC_READING in *.
pose proof (b10s_seed Wc rX memc (pf_s1 v) cur (p_c v + 16512) R9 R20 ltac:(lia) ltac:(lia) W48 HC0
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (fun o Ho => proj1 (Hblk (cur + o) ltac:(lia)))) as HS.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg rX [w64 cur; w64 (p_c v + 16512)]))) by apply Eimg_env.
assert (HA0 : env_agree 32 (Ereg rX [w64 cur; w64 (p_c v + 16512)]) (Eimg (Ereg rX [w64 cur; w64 (p_c v + 16512)])))
  by (split; [intros k Hk; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]).
assert (EE : forall k (q : bv 5), Z.of_nat k = bv_unsigned q ->
  ew (Eimg (Ereg rX [w64 cur; w64 (p_c v + 16512)])) k = getr rX q)
  by (intros k q Hk; apply ew_Eimg_Ereg_nat; exact Hk).
assert (EX : forall j, (j < 2)%nat ->
  ew (Eimg (Ereg rX [w64 cur; w64 (p_c v + 16512)])) (32 + j) = nth j [w64 cur; w64 (p_c v + 16512)] (Z_to_bv 64 0))
  by (intros j Hj; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33. cbn [Nat.add nth] in E32, E33.
pose proof (EE 9%nat (Z_to_bv 5 9) eq_refl) as E9. rewrite R9 in E9.
pose proof (EE 20%nat (Z_to_bv 5 20) eq_refl) as E20. rewrite R20 in E20.
pose proof (EE 19%nat (Z_to_bv 5 19) eq_refl) as E19. rewrite R19 in E19.
clear EX.
revert HS HEI HA0 EE E32 E33 E9 E20 E19.
generalize (Eimg (Ereg rX [w64 cur; w64 (p_c v + 16512)])) as E.
intros E HS HEI HA0 EE E32 E33 E9 E20 E19.
assert (U9 : bv_unsigned (ew E 9) = pf_s1 v) by (rewrite E9; unfold w64; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = cur) by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
assert (UB : U E b10s_Bx = SHADOW_OFF)
  by (unfold b10s_Bx; apply (U_atom E 20 SHADOW_OFF E20); unfold SHADOW_OFF; lia).
assert (UE : U E (SOff 32 0) = cur) by (apply (U_atom E 32 cur E32); lia).
(* the shadow entry of the two checks: cur + 16 .. cur + 24, inside the block c *)
pose proof HC4 as (_ & _ & _ & HRAc & _).
assert (SHOK : sh_ok SEGS b10s_Bx b10s_SH E (mrestrict (w_H Wc) memc)).
{ unfold sh_ok, b10s_SH. apply Forall_cons; [|apply Forall_nil].
  eapply (shent_ok_of_range SEGS (w_H Wc) memc E b10s_Bx 32%nat (cur + 16) 8 cur 16 24
    (range_addressable_sub _ _ (p_c v) _ (cur + 16) 8 HRAc ltac:(lia) ltac:(unfold seg_spec.SEG_C_SIZE; lia)) UB UE);
    [lia | lia |].
  intros x Hx. change (Z.min 16 24) with 16 in Hx. change (Z.max 16 24) with 24 in Hx. unfold SHADOW_OFF. lia. }
unfold cfg_at. change (w64 (BASE + PF_ROLEV)) with (Z_to_bv 64 (BASE + PF_ROLEV)).
(* 0x88d6c .. 0x88d74: cur & 3 and the T30 branch *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end.
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_gen with (n := 32%nat) (b := cur); [reflexivity | exact U32 | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; left. split.
  - exists (p_c v, p_c v + seg_spec.RC_N + 4). split; [left; reflexivity|]. cbn [fst snd]. unfold seg_spec.RC_N. lia.
  - exists bb, mm. split; [exact Hbin | lia]. }
set (mdv := with_vm_backing _ _ _) in *; clearbody mdv.
(* what the first run kept: every byte but cur's two role words (it writes none of them) *)
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> ~ (cur + 16 <= a < cur + 24) -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha Hn. apply (kept_of_frame (segs := SEGS) E _ (w_H Wc) memc (ms_mem ms) (fun a' => cur + 16 <= a' < cur + 24) HFr);
    [|exact Ha | exact Hn].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
  repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U9, ?U32 in Hrr; lia |]).
  destruct Hin'. }
assert (KP1 : forall a, rdW Wc memc a <> None -> rdW Wc (ms_mem ms) a <> None)
  by (intros a Hv; exact (aview_keeps_vis SEGS (w_H Wc) memc (ms_mem ms) a HG Hv)).
clear HF HFr HG.
(* 0x88d74 bnez a0 -> 0x891c8: T30, not taken (cur mod 4 = 0) *)
psrr_branch_tok RUN BR HS SHOK Bspan.
{ exfalso. rewrite (b10s_t30 E cur E32 ltac:(lia) Hcur4) in Hc. discriminate Hc. }
clear Hc.
(* 0x88d78 .. 0x88dc4: B#31, the role store, B#32, the role_set store, snprintf's arguments, the call *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end.
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_gen with (n := 32%nat) (b := cur); [reflexivity | exact U32 | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; left. split.
  - exists (p_c v, p_c v + seg_spec.RC_N + 4). split; [left; reflexivity|]. cbn [fst snd]. unfold seg_spec.RC_N. lia.
  - exists bb, mm. split; [exact Hbin | lia]. }
set (mdv2 := with_vm_backing _ _ _) in *; clearbody mdv2.
lazymatch type of HS with st_ok _ ?E2 _ (restrict _ ?m2) =>
  rename m2 into msc; remember E2 as Ec eqn:HEc in * end.
lazymatch type of HFr with frame_of _ _ (mrestrict _ (ms_mem ?m1)) _ => rename m1 into ms1 end.
(* what the second run kept: every byte but cur's two role words, which it wrote *)
assert (KM2 : forall a, 0 <= a < 2 ^ 64 -> ~ (cur + 16 <= a < cur + 24) -> rdW Wc (ms_mem msc) a = rdW Wc (ms_mem ms1) a).
{ intros a Ha Hn. apply (kept_of_frame (segs := SEGS) E _ (w_H Wc) (ms_mem ms1) (ms_mem msc) (fun a' => cur + 16 <= a' < cur + 24) HFr);
    [|exact Ha | exact Hn].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
  repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U9, ?U32 in Hrr; lia |]).
  destruct Hin'. }
assert (KP2 : forall a, rdW Wc (ms_mem ms1) a <> None -> rdW Wc (ms_mem msc) a <> None)
  by (intros a Hv; exact (aview_keeps_vis SEGS (w_H Wc) (ms_mem ms1) (ms_mem msc) a HG Hv)).
assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (cur + 16 <= a < cur + 24) -> rdW Wc (ms_mem msc) a = rdW Wc memc a)
  by (intros a Ha Hn; rewrite (KM2 a Ha Hn); exact (KM1 a Ha Hn)).
assert (PR : forall a, rdW Wc memc a <> None -> rdW Wc (ms_mem msc) a <> None) by (intros a Hv; exact (KP2 a (KP1 a Hv))).
(* the environment at the call: the seed's below the run's token atoms *)
assert (AG : forall k, (k < 1024)%nat -> ew Ec k = ew E k) by (intros k Hk; rewrite HEc; rewrite !ew_ewset_other by lia; reflexivity).
assert (HEIc : img_env VAL A_LIM Ec) by (intros a Ha; rewrite AG by (unfold A_LIM in *; lia); exact (HEI a Ha)).
assert (HAc : env_agree 32 (Ereg rX [w64 cur; w64 (p_c v + 16512)]) Ec).
{ destruct HA0 as [HA0a HA0b]. split; [intros k Hk; rewrite AG by lia; exact (HA0a k Hk) | rewrite HEc; exact HA0b]. }
assert (U32c : bv_unsigned (ew Ec 32) = cur) by (rewrite AG by lia; exact U32).
(* the role words the run stored *)
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msx) =>
  let r1 := eval vm_compute in (nth 1 (ss_mem ssx) got_regionP) in
  pose proof (st_ok_region_nth Ex ssx (restrict (w_H Wc) msx) 1 r1 HS ltac:(vm_compute; reflexivity)) as HR1 end.
cbn [ms_mem restrict] in HR1.
pose proof (field_of_region_any (segs := SEGS) Ec _ 32 cur _ 16 24 16 24 16 4%N (SOff 19 0) HR1 U32c
  ltac:(b10s_in) ltac:(cbn; lia)) as HV16.
pose proof (field_of_region_any (segs := SEGS) Ec _ 32 cur _ 16 24 16 24 20 4%N (SLit 1) HR1 U32c
  ltac:(b10s_in) ltac:(cbn; lia)) as HV20.
assert (Er : bv_unsigned (sv_denot Ec (SOff 19 0)) mod 2 ^ (8 * Z.of_N 4) = r).
{ cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, AG by lia. rewrite E19. unfold w64.
  rewrite unsigned_lit_small by lia. change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32). apply Z.mod_small. lia. }
assert (E1 : bv_unsigned (sv_denot Ec (SLit 1)) mod 2 ^ (8 * Z.of_N 4) = 1) by (vm_compute; reflexivity).
rewrite Er in HV16. rewrite E1 in HV20. change (N.to_nat 4) with 4%nat in HV16, HV20.
pose proof (b10s_sa_val SEGS (w_H Wc) (ms_mem msc) _ 4 r HV16) as V16.
pose proof (b10s_sa_val SEGS (w_H Wc) (ms_mem msc) _ 4 1 HV20) as V20.
(* the registers at the call *)
assert (HOBJ35 : VAL (A_OBJ 35) = 0x21340).
{ rewrite OBJ by (apply Nat.ltb_lt; vm_compute; reflexivity). vm_compute. reflexivity. }
change (A_OBJ 35) with 276%nat in HOBJ35.
assert (R1 : getr (ms_regs msc) 1 = Z_to_bv 64 (BASE + PF_JOIN)).
{ b10s_rreg HS. cbn [sv_denot]. rewrite (HEIc 240%nat ltac:(unfold A_TEXT, A_LIM; lia)). reflexivity. }
assert (R10 : getr (ms_regs msc) 10 = w64 (seg_spec.rseg_addr (p_c v) gi + 160)).
{ b10s_rreg HS. cbn [sv_denot]. rewrite U32c. reflexivity. }
assert (R11 : getr (ms_regs msc) 11 = w64 96) by (b10s_rreg HS; reflexivity).
assert (R12 : getr (ms_regs msc) 12 = w64 0x21340).
{ b10s_rreg HS. cbn [sv_denot]. rewrite (HEIc 276%nat ltac:(unfold A_TEXT, A_LIM; lia)). rewrite HOBJ35. reflexivity. }
assert (R13 : getr (ms_regs msc) 13 = w64 (p_c v + 16512)).
{ b10s_rreg HS. cbn [sv_denot]. rewrite AG by lia. rewrite E33. unfold w64. rewrite unsigned_lit_small by lia.
  rewrite Z.add_0_r. reflexivity. }
pose proof (aregs_preserved_of_st_ok SEGS (w_H Wc) Ec _ msc rX _ HS HAc ltac:(vm_compute; reflexivity)) as PRT.
pmkst HS.
exact (b10s_from_call B ASNP n HJN v pos lyc Sc Wc rX memc mdc cf nm o ln d gi val r (ms_regs msc) (ms_mem msc) mdv2
  HI HJ KR PR V16 V20 PRT R1 R10 R11 R12 R13).
Qed.
End x.

(* the piece of pf_seg_B10b_k.v at every FP state *)
Theorem pb10_s_ok : PB10_S B.
Proof. intros f0 n J. exact (b10s_rolev (fx := f0) n J). Qed.
End d.
