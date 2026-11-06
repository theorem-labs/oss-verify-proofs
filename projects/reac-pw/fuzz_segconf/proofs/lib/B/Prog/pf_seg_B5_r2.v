(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_box_catalogue on fuzz_segconf.asan-ubsan (image B, pin sha256
   c3796c0b38f3, twin 80e82127e8ca; entry 0x8a8a0, 84 bytes, 21 instructions, a 16-byte frame, no side-stack
   frame): reac_box_catalogue_contract of lib/B/Prog/reac_box_catalogue_c.v (image B's copy of the image-A owner's FINAL
   text at 6f783602b5e3) at image B's numbers, in plugin-hostd/fuzz_command's lib/A/Prog form (afn_pre at the
   entry, SRr of apost_base at the return, over `Context {PI : PAImg seg_listing}` of image B's listing,
   lib/B/Prog/SegPa.v).
   ADAPTATION (relocation + one trap) of lib/A/Prog/reac_box_catalogueA.v (the image-A m_file-family lane, commit
   434ade288123, both arms): the same entry seeds, token runs and return steps over image B's listing modules and
   B's kit copies. The UBSan alignment check is read from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_catalogue.v
   at origin/ossv/recipes 3abc3740de97 (the same image-B code but 4 pc-relative words; caller-journal form, not
   copied), whose token run decides it the same way.
   Image B's code differs from image A's by two instructions: `andi a1,a0,7` (0x8a8ac) and `bnez a1,0x8a8ec`
   (0x8a8b0) to `unimp` (0x8a8ec), the UBSan alignment check of the 8-byte store through c.
   UBSan trap branch (one): 0x8a8b0 `bnez a1` -> unimp 0x8a8ec. Not taken: the c <> 0 run's entry seed carries the
   fact (10%nat, mkAF 4096 (2 ^ 47 - 8) 3) on a0 (rbc_facts: c is 2^3-aligned, from the contract premise
   c mod 8 = 0, seeded by rbc_entry), so the token executor (paj_run_tok, its branch step under facts_ok) computes
   a1 = c & 7 = 0 and decides the branch not taken; the trap instruction is never executed. The c = 0 run leaves at
   the beqz 0x8a8a8 (a0 pinned to 0) before the check.
   c <> 0: the instrumented check of the 8-byte cell (a load of the shadow byte at (c >> 3) + the shadow base, lbu
   0x8a8c8, and a compare, bnez 0x8a8cc) reads 0, because the contract's sa_addr gives the cell addressable; so the
   error path (the call of errpath_store8 at 0x8a8f0) is not reached; the sd at 0x8a8d4 writes 11 as 8 bytes. In
   both arms a0 = fuzz_catalogue (auipc/addi 0x8a8d8-0x8a8dc, 0xa20a0). The shadow base is the word the GOT cell
   as_got_shadow B holds (image B 0xa3210, the ld at 0x8a8b8, listing object 0; its target
   __asan_shadow_memory_dynamic_address 0xac7b8, listing object 12): the walk takes both from PALib (pal_got_shadow,
   pal_cell), a listing fact, not a contract premise.
   Positional names checked against image B's own listing (lib/B/Prog/SegAddr.v seg_objs, SegList.v) by address and
   anchor symbol (twin nm): A_OBJ 0 = 0xa3210 (the .got word the ld at 0x8a8b8 reads), A_OBJ 12 = 0xac7b8
   (__asan_shadow_memory_dynamic_address), A_OBJ 77 = RBC_CAT_OBJ = 0xa20a0 (fuzz_catalogue; SegList.v
   `PAddHi (10%bv : reg) (10%bv : reg) 123 (A_OBJ 77) 0x0` at 0x8a8dc), AF_reac_box_catalogue = 0x5ae0 =
   0x8a8a0 - seg_text 0x84dc0, atom 32 = the first extra env word (the shadow base SB, rbc_extra): 5 checked, 0
   pointing elsewhere.
   Image B's numbers of the statement: the entry BASE + AF_reac_box_catalogue; STK_reac_box_catalogue = 16 (the
   contract's STK comment: its frame, 0x8a8a0 addi sp,sp,-16 released at 0x8a8e4; the unimp at 0x8a8ec and the jal
   at 0x8a8f0 are the dead trap and error arms; no callee); cat = catA = 0xa20a0. Both are lib/B/Prog/SegInstB.v's
   definitions (SegInstA's names at image B): SegInstB.STK_reac_box_catalogue and SegInstB.catA, tied to this walk
   by the lemmas STK_reac_box_catalogue_B (the value 16) and catA_B (listing object 77 of B's seg_objs). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 158 of its 204 lines of code are new or changed and 407 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3): segment B5 of reac_segconf_parse_file,
   piece R2 -> Q3 (the B5 segment lane of the image-B G3 walk owner, 2026-10-30): b5_r2_ok : H_Q3 B n -> H_R2 B n.
   ADAPTED from the image-A G3 walk owner's image-A segment lane on a working branch (pf_a5_d.v's R2 -> Q3; A has no trap
   here) and the unit owner's UBSan piece lib/U/Prog/pf_p2.v (the same C-level check, `p + len`), re-derived on image B's
   code; the cut rebuild follows the image-B G3 walk owner's B10b segment lane (pf_seg_B10b_j.v, b10j_join).
   The code (reac_segconf_parse_file.fuzz_segconf.asan-ubsan.s), reached from R1 when strchr found no '\n' and
   strlen returned a0 = LEN (the line is the rest of the text, o + LEN = length s):
     0x88224 `not a1,s11`      a1 = 2 ^ 64 - 1 - p, p = s11 = t + o
     0x88228 `bgeu a1,a0`      UBSan trap T04 (pointer overflow of `p + len`, reac_segconf.c:135): not taken only
                               when 2 ^ 64 - 1 - p < LEN; refuted: p + LEN = t + length s < 2 ^ 63 (pf_obj's
                               sa_addr t (length s + 1))
     0x8822c `j 0x891c8`       the trap's jump to the `unimp` (never reached)
     0x88230 `mv s7,a0`        s7 = LEN
     0x88234 `add s9,s11,a0`   s9 = t + o + LEN = t + pf_next s o (the line ends the text: no '\n' to skip)
   then Q3 0x88238. 4 of B5's 116 instructions walked (0x88224 .. 0x88234; 0x8822c excluded), trap T04 discharged,
   no check, no call, no write. Section hypotheses: none. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI08.
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
  PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_pieces pf_seg_B5_d pf_seg_B5_k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* a register of the state after a run, as the executor wrote it *)
Ltac b5r2_rreg HS :=
 lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
 lazymatch type of HS with
 | st_ok_pi _ _ ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_pi_restrict_reg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 end end.
Ltac b5r2_clear_md := repeat match goal with |- context [with_vm_backing (m_vm_lazy ?m) ?x ?m] =>
  let mdv := fresh "mdv" in set (mdv := with_vm_backing (m_vm_lazy m) x m) in *; clearbody mdv end.
Lemma b5r2_w64_off : forall x c, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 x) + c) = Z_to_bv 64 (x + c).
Proof.
intros x c. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
rewrite Zplus_mod_idemp_l. reflexivity.
Qed.
(* the denotation of a register term over atoms of known value *)
Ltac b5r2_den :=
  cbn [sv_denot];
  repeat match goal with H : ew ?E ?n = Z_to_bv 64 _ |- context [ew ?E ?n] => rewrite H end;
  rewrite ?b5r2_w64_off, ?alu64_add_lit, ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
  unfold w64; first [reflexivity | f_equal; lia].

(* the seed at R2: every register its own atom, no region *)
Definition b5r2_ss : sstate := mkSS B5_R2 sr_atoms [] None (mkFacts [] [] []).

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNP := SRr_run_pi_AJ (fx := fx) B LAWS.
Let RUNTO := SRr_run_to_pi_AJ (fx := fx) B LAWS.
Let BR := paj_branch (PI := PI).

Lemma b5r2_seed : forall (Wc : world SEGS) (rX : bvmap 5 word) memc,
  st_ok_pi SEGS VAL (Eimg (Ereg rX [])) b5r2_ss
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + B5_R2)) memc (seg_rom SEGS))).
Proof.
intros Wc rX memc. rewrite restrict_mkst_fx. unfold b5r2_ss. apply pa_entry_st_ok_full;
  [apply regs_ok_Eimg_Ereg | vm_compute; reflexivity | constructor | cbn; tauto | split; [exact I | split; exact I]].
Qed.

(* pf_base at the same frame state after a run that kept every byte (the cut's objects, the slots, the shadow) *)
Lemma b5r2_base_same : forall v pos lyc Sc Wc rX memc mdc sc rX' memc' mdc',
  pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc' mdc' 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc' a = rdW Wc memc a) ->
  pf_rg rX' (b5_FI B v) ->
  pf_base B v pos lyc Sc Wc rX' memc' mdc' sc.
Proof.
intros v pos lyc Sc Wc rX memc mdc sc rX' memc' mdc' HB HJ' KM HRG.
pose proof HB as (HCX & HFI & _ & _ & HFSH).
destruct (b5_geo B v pos lyc Sc Wc rX memc mdc HCX HFI) as (HG & _).
pose proof HFI as (_ & _ & (f0 & HS0) & _).
assert (K : b5_kept v pos (rdW Wc memc) (rdW Wc memc')).
{ split; [intros a Ha _; exact (KM a Ha) | intros a Ha Hv; rewrite (KM a Ha); exact Hv]. }
apply (b5_move B v pos lyc Sc Wc rX memc mdc sc Sc rX' memc' mdc' sc HB HJ').
- exists f0. rewrite HS0. rewrite b5_set_fs2. reflexivity.
- apply Permutation_refl.
- exact K.
- exact HRG.
- pose proof HG as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
  destruct (b5_SHv v pos HG) as (_ & SH1 & SH2 & _).
  intros i Hi. rewrite (KM (pf_SH v pos + i)) by lia. exact (HFSH i Hi).
Qed.

(* the trap T04 (0x88228 `bgeu a1,a0` not taken, a1 = not s11): 2 ^ 64 - 1 - p < LEN is false when p + LEN < 2 ^ 63 *)
Lemma b5r2_t04 : forall E a p len, U E a = 2 ^ 64 - 1 - p -> 0 <= p -> 0 <= len -> p + len < 2 ^ 63 ->
  forall b, U E b = len ->
  branch_taken BC_GEU (sv_denot E a) (sv_denot E b) = false -> False.
Proof.
intros E a p len Ha Hp Hl Hpl b Hb Hc. rewrite branch_geu_U, Ha, Hb in Hc.
apply Bool.negb_false_iff, Z.ltb_lt in Hc. lia.
Qed.

Lemma b5_r2_ok : forall n, H_Q3 B n -> H_R2 B n.
Proof.
intros n HQ3 v pos lyc Sc Wc rX memc mdc cf cur nm o ln d HI.
pose proof HI as (HB & HLN & HEND & HRG).
pose proof HB as (HCX & HFI & HOBJ & HSL & HFSH).
destruct (b5_geo B v pos lyc Sc Wc rX memc mdc HCX HFI) as (HGEO & Hin & EF & Hfrs & HAR).
pose proof HFI as (HJ & Hly & HSc & HPERM & HSAV & HFLAG & HFRM & HTF & HC8 & HRG0).
destruct (b5_text B v pos lyc Sc Wc rX memc mdc PF_SC_HEAD HB) as (NUL & LS & HSTR & HADDR & HTH & HCH).
pose proof HLN as (HCTX & Ho & Hk & HST).
pose proof HADDR as (Ht0 & Ht63 & _).
unfold pf_len in Ht63.
set (LEN := b5_len v o) in *.
assert (HLEN : (LEN <= length (p_s v))%nat) by lia.
(* the registers at R2 *)
rewrite b5_rg_app in HRG. destruct HRG as (HRL & HRR).
assert (R27 : getr rX (Z_to_bv 5 27) = w64 (p_t v + Z.of_nat o)) by (apply (b5_rg rX _ 27 _ HRR); b5_in).
assert (R24 : getr rX (Z_to_bv 5 24) = w64 ln) by (apply (b5_rg rX _ 24 _ HRR); b5_in).
assert (R10 : getr rX (Z_to_bv 5 10) = w64 (Z.of_nat LEN)) by (apply (b5_rg rX _ 10 _ HRR); b5_in).
(* the seed *)
pose proof (b5r2_seed Wc rX memc) as HS.
set (E := Eimg (Ereg rX [])) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr rX r)
  by (intros n0 r Hn0; subst E; apply ew_Eimg_Ereg_nat; exact Hn0).
assert (E27 : ew E 27 = Z_to_bv 64 (p_t v + Z.of_nat o)) by (rewrite (EE 27%nat (Z_to_bv 5 27) eq_refl); exact R27).
assert (E10 : ew E 10 = Z_to_bv 64 (Z.of_nat LEN)) by (rewrite (EE 10%nat (Z_to_bv 5 10) eq_refl); exact R10).
unfold cfg_at. change (w64 (BASE + B5_R2)) with (Z_to_bv 64 (BASE + B5_R2)).
(* 0x88224 `not a1,s11`, up to the branch 0x88228 *)
paj_run_sh RUNP HS HJ.
{ intros a (r & Hr & _). cbn [b5r2_ss ss_mem In] in Hr. destruct Hr. }
cbn [ms_mem mkst] in HFr, HG, HF.
b5r2_clear_md.
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha. apply (kept_of_frame (segs := SEGS) E (ss_mem b5r2_ss) (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr);
    [|exact Ha | tauto].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'. destruct Hin'. }
clear HFr HG HF.
psrr_branch_pi RUNP BR HS.
- (* taken: 2 ^ 64 - 1 - p >= LEN; 0x88230 `mv s7,a0`, 0x88234 `add s9,s11,a0`, to Q3 *)
  clear Hc.
  paj_run_to_sh RUNTO HS HJ B5_Q3.
  { intros a (r & Hr & _). cbn [add_cond b5r2_ss ss_mem In] in Hr.
    first [destruct Hr | vm_compute in Hr; destruct Hr]. }
  cbn [ms_mem mkst] in HFr, HG, HF.
  b5r2_clear_md.
  assert (K2 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms0) a = rdW Wc (ms_mem ms) a).
  { intros a Ha. lazymatch type of HFr with frame_of ?Ex ?rs _ _ =>
    apply (kept_of_frame (segs := SEGS) Ex rs (w_H Wc) (ms_mem ms) (ms_mem ms0) (fun _ => False) HFr);
      [|exact Ha | tauto] end.
    intros b wlo whi a' Hin' Hrr. vm_compute in Hin'. destruct Hin'. }
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms0) a = rdW Wc memc a)
    by (intros a Ha; rewrite (K2 a Ha); exact (K1 a Ha)).
  clear HFr HG HF.
  (* the registers at Q3 *)
  assert (QK : forall r, In r [2; 3; 4; 8; 9; 20; 18; 21; 26; 27; 24] ->
      getr (ms_regs ms0) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
  { intros r Hr. cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr]; [b5r2_rreg HS; rewrite b5_den_atom0; apply EE; reflexivity |]). destruct Hr. }
  destruct (L_next_holds (p_s v) o Ho) as (_ & _ & _ & HNX).
  assert (HNX' : pf_next (p_s v) o = (o + LEN)%nat).
  { rewrite HNX. unfold LEN, b5_len in *.
    destruct (Nat.ltb_spec (o + length (pf_line (p_s v) o)) (length (p_s v))); lia. }
  assert (Q23 : getr (ms_regs ms0) (Z_to_bv 5 23) = w64 (Z.of_nat LEN)).
  { b5r2_rreg HS. b5r2_den. }
  assert (Q25 : getr (ms_regs ms0) (Z_to_bv 5 25) = w64 (p_t v + Z.of_nat (pf_next (p_s v) o))).
  { b5r2_rreg HS. rewrite HNX'.
    b5r2_den. }
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?k)) ?mm ?rom) ?mdx) _ =>
    change (mkCfg (mkst rg (Z_to_bv 64 (BASE + k)) mm rom) mdx) with (cfg_at SEGS (BASE + B5_Q3) rg mm mdx) end.
  apply (HQ3 v pos lyc Sc Wc (ms_regs ms0) (ms_mem ms0) mdv0 cf cur nm o ln d).
  assert (KP : b5_kept v pos (rdW Wc memc) (rdW Wc (ms_mem ms0))).
  { split; [intros a Ha _; exact (KM a Ha) | intros a Ha Hv; rewrite (KM a Ha); exact Hv]. }
  split; [|split].
  + apply (b5r2_base_same v pos lyc Sc Wc rX memc mdc PF_SC_HEAD (ms_regs ms0) (ms_mem ms0) mdv0 HB HJ KM).
    unfold pf_rg, b5_FI. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
      (rewrite QK; [apply (b5_rg rX _ _ _ HRG0); b5_in | b5_in]).
  + split; [exact HCTX|]. split; [exact Ho|]. split; [exact Hk|].
    exact (b5_keep_st B v pos lyc Sc Wc memc mdc _ _ cf cur nm _ HGEO HAR Hin EF KP HCH HST).
  + unfold pf_rg. rewrite Forall_app. split.
    * unfold PF_RL. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
        (rewrite QK; [apply (b5_rg rX _ _ _ HRL); b5_in | b5_in]).
    * repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd].
      -- rewrite QK; [exact R27 | b5_in].
      -- rewrite QK; [exact R24 | b5_in].
      -- exact Q25.
      -- exact Q23.
- (* not taken: the trap T04, refuted *)
  exfalso.
  pose proof (proj1 (Nat2Z.inj_le _ _) HLEN) as HLZ.
  assert (Hp : 0 <= p_t v + Z.of_nat o) by lia.
  assert (Hpl : p_t v + Z.of_nat o + Z.of_nat LEN < 2 ^ 63) by lia.
  lazymatch type of Hc with branch_taken BC_GEU (sv_denot _ ?a) (sv_denot _ ?b) = false =>
    refine (b5r2_t04 E a (p_t v + Z.of_nat o) (Z.of_nat LEN) _ Hp ltac:(lia) Hpl b _ Hc) end.
  + apply (U_not E 27 _ E27). lia.
  + apply (U_atom E 10 _ E10). lia.
Qed.
End e.
End f.
End d.
