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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 424 of its 465 lines of code are new or changed and 412 lines of the source are left out. *)
(* reac_segconf_parse_file (image A), segment A10a: the entry ROLE 0x881d4 and the segment theorem
   pf_a10a_holds : S_A10a B (lib/A/Prog/pf_pieces.v). Segment A10a's proof, by the G3 walk owner.
     0x881d4 .. 0x881f0  low comes into scope: eight shadow cells SH + 0x50 .. SH + 0x57 set to 0
                         (a plain run: a token run may not write the shadow band)
     0x881f4 .. 0x8820c  check 16 (val[0]), the load of val[0] and of the slot s1 + 0x48 = low,
                         then `beqz`: the empty value goes to END 0x88438 with a3 = 0, else to LOOP 0x88218.
   The two exits are lib/A/Prog/pf_a10a_e.v's A10_END_stmt and A10_LOOP_at. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YO0b YO0c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaCall PaDenot.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaLibG PaLibF PaLibH PaSB PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaArt.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase SegGlob SegInstA
  refuse_c reac_segconf_parse_file_c pf_pieces pf_a10a_k pf_a10a_e.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- ROLE 0x881d4: the eight shadow stores, a plain run (the band may not be written in a token run) ---- *)
Definition ar_regions : smem := [YP09.mkRegion (Some 27%nat) 80 88 80 88 []].
Definition ar_ss : sstate := mkSS PF_ROLE sr_atoms ar_regions None (mkFacts [] [] []).

(* ---- 0x881f4: check 16, the load of val[0] (atom 32) and of the slot s1 + 0x48 = low (atom 33) ---- *)
Definition as_regions : smem :=
[ YP09.mkRegion (Some 25%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))];
  YP09.mkRegion (Some 9%nat) 72 80 0 0 [YP09.mkChunk 72 (CVal 8 (SOff 33 0))] ].
Definition as_facts : facts :=
mkFacts [ (9%nat, mkAF 4096 140737488355144 0); (22%nat, mkAF SB SB 0); (25%nat, PTR 0); (32%nat, mkAF 0 255 0);
          (33%nat, PTR 0) ]
[] [].
Definition as_ss : sstate := mkSS A10_SH16 sr_atoms as_regions None as_facts.
Definition as_SH : list shent := [mkSHE 25 0 1].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* every byte outside the eight cells survives the shadow stores *)
Lemma a10_keep_sh : forall (E : env) cs (m0 m m' : word -> option byte) (H : word -> bool) SHz,
  frame_of E [YP09.mkRegion (Some 27%nat) 80 88 80 88 cs] (mrestrict H m) (mrestrict H m') ->
  bv_unsigned (ew E 27) = SHz ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (SHz + 80 <= a < SHz + 88) -> aview SEGS H m a = aview SEGS H m0 a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (SHz + 80 <= a < SHz + 88) -> aview SEGS H m' a = aview SEGS H m0 a.
Proof.
intros E cs m0 m m' H SHz HFr H27 KM a Ha Hn.
rewrite (kept_of_frame (segs := SEGS) E _ H m m' (fun a' => SHz + 80 <= a' < SHz + 88) HFr);
  [exact (KM a Ha Hn) | | exact Ha | exact Hn].
intros b wlo whi a' Hin Hrr. cbn [windows map YP09.r_base YP09.r_wlo YP09.r_whi In] in Hin.
destruct Hin as [Hq | []]; injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite H27 in Hrr; lia.
Qed.

(* a run with no writable window keeps every byte *)
Lemma a10_keep_ro : forall (E : env) cs0 cs1 (m m' : word -> option byte) (H : word -> bool),
  frame_of E [YP09.mkRegion (Some 25%nat) 0 1 0 0 cs0; YP09.mkRegion (Some 9%nat) 72 80 0 0 cs1]
    (mrestrict H m) (mrestrict H m') ->
  forall a, 0 <= a < 2 ^ 64 -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E cs0 cs1 m m' H HFr a Ha.
apply (kept_of_frame (segs := SEGS) E _ H m m' (fun _ => False) HFr); [|exact Ha | tauto].
intros b wlo whi a' Hin Hrr. cbn [windows map YP09.r_base YP09.r_wlo YP09.r_whi In] in Hin.
destruct Hin as [Hq | [Hq | []]]; injection Hq as <- <- <-; cbn [base_val] in Hrr; lia.
Qed.

Lemma ar_entry : forall (W : world SEGS) (regs1 : bvmap 5 word) memc SHz,
getr regs1 27 = w64 SHz -> 0 <= SHz -> SHz + 256 < 2 ^ 64 ->
(forall i, 0 <= i < 256 -> apresent (w_H W) memc (SHz + i)) ->
st_ok_pi SEGS VAL (a10_E regs1 []) ar_ss
  (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + PF_ROLE)) memc (seg_rom SEGS))).
Proof.
intros W regs1 memc SHz H27 Hs1 Hs2 Hp.
assert (E27 : ew (a10_E regs1 []) 27 = Z_to_bv 64 SHz)
  by (rewrite (a10_ew regs1 _ 27 27%bv eq_refl); exact H27).
rewrite restrict_mkst_fx. unfold ar_ss. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold ar_regions. constructor; [|constructor].
  unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E27, unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [|constructor].
  intros ov Hov. apply (apresent_writable SEGS). apply Hp. lia.
- cbn. tauto.
- split; [cbn; exact I | split; cbn; exact I].
Qed.

Lemma as_entry : forall (W : world SEGS) (regs1 : bvmap 5 word) memc s1a vpa low c0,
getr regs1 9 = w64 s1a -> getr regs1 22 = w64 SB -> getr regs1 25 = w64 vpa ->
4096 <= s1a -> s1a + 184 <= 2 ^ 47 -> 4096 <= vpa -> vpa + 1 <= 140737479966720 ->
4096 <= low -> low + 64 <= 140737479966720 -> 0 <= c0 <= 255 ->
rdW W memc vpa = Some c0 ->
rdword (rdW W memc) (s1a + 72) = Some low ->
vpa + 1 <= s1a + 72 ->
st_ok_pi SEGS VAL (a10_E regs1 [w64 c0; w64 low]) as_ss
  (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + A10_SH16)) memc (seg_rom SEGS))).
Proof.
intros W regs1 memc s1a vpa low c0 H9 H22 H25 Hs1 Hs2 Hv1 Hv2 Hl1 Hl2 Hc0 Hrd Hslot Hdis.
set (E := a10_E regs1 [w64 c0; w64 low]).
assert (E9 : ew E 9 = Z_to_bv 64 s1a) by (subst E; rewrite (a10_ew regs1 _ 9 9%bv eq_refl); exact H9).
assert (E22 : ew E 22 = Z_to_bv 64 SB) by (subst E; rewrite (a10_ew regs1 _ 22 22%bv eq_refl); exact H22).
assert (E25 : ew E 25 = Z_to_bv 64 vpa) by (subst E; rewrite (a10_ew regs1 _ 25 25%bv eq_refl); exact H25).
assert (E32 : ew E 32 = Z_to_bv 64 c0)
  by (subst E; unfold a10_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 low)
  by (subst E; unfold a10_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
rewrite restrict_mkst_fx. unfold as_ss. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold as_regions. constructor; [|constructor; [|constructor]].
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E25, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros ov Hov; lia|]. constructor; [|constructor].
    unfold YP09.chunk_ok, YP09.c_len, YP09.cv_len. cbn [YP09.c_off YP09.c_val]. intros i Hi.
    assert (i = 0) as -> by lia.
    destruct (aview_byte SEGS (w_H W) memc vpa c0 Hrd) as (b & Hb & Hv & _).
    exists b. split.
    * cbn [YP09.cbyte]. f_equal. unfold YP09.byte_of_word. cbn [sv_denot]. rewrite E32.
      rewrite !Z.add_0_r, (unsigned_lit_small c0), (unsigned_lit_small c0) by lia.
      change (8 * 0) with 0. rewrite Z.shiftr_0_r. subst c0. apply Z_to_bv_bv_unsigned.
    * rewrite !Z.add_0_r. exact Hb.
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E9, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros ov Hov; lia|]. constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ s1a 72 8 (SOff 33 0) low);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, unsigned_lit_small by lia; reflexivity
      | lia | lia |].
    exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Hslot).
- unfold as_regions. cbn [YP09.pairwise_disjoint YP09.all_disjoint]. unfold YP09.extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val].
  rewrite E9, E25, !unsigned_lit_small by lia. repeat split; lia.
- split; [|split; cbn; exact I].
  cbn [as_facts f_atoms atoms_ok]. unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
  rewrite E9, E22, E25, E32, E33, !unsigned_lit_small by (unfold SB; lia).
  rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB. repeat split; lia.
Qed.

(* a register of the state after a run, read through its symbolic value *)
Lemma a10_reg_sym : forall (H : word -> bool) E ss ms r s z,
  st_ok_pi SEGS VAL E ss (restrict H ms) -> sr_get (ss_regs ss) r = s -> U E s = z -> 0 <= z < 2 ^ 64 ->
  getr (ms_regs ms) r = w64 z.
Proof.
intros H E ss ms r s z HS Hs HU Hz. rewrite (st_ok_pi_restrict_reg H E ss ms r HS), Hs. apply bv_eq.
change (bv_unsigned (sv_denot E s)) with (U E s). rewrite HU. unfold w64. rewrite unsigned_lit_small by lia.
reflexivity.
Qed.

Section e.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.

(* the two read-only runs' write check and keep (0x881f4 .. 0x8820c and on to an exit) *)
Ltac a10_ro_awr :=
  lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr0 lyx own) end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
Ltac a10_ro_keep KMn :=
  lazymatch goal with
  | HFrn : frame_of ?Eo _ (mrestrict ?H ?mprev) (mrestrict ?H (ms_mem ?msn)) |- _ =>
    pose proof (a10_keep_ro Eo _ _ mprev (ms_mem msn) H HFrn) as KMn; clear HFrn
  end.

(* the fold's state before its first byte *)
Lemma a10_mid_init : forall n v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val regs1 memc mdc,
  INV_KV B n v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val ->
  strcasecmp key S_role = 0 ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v)
    (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc mdc 0 ->
  (forall a, a10_far v pos a -> rdW Wc memc a = rdW Wc memc0 a) ->
  (forall i, 0 <= i < 8 -> rdW Wc memc (pf_SH v pos + 80 + i) = Some 0) ->
  (forall r, In r A10_KZ -> getr regs1 (Z_to_bv 5 r) = getr rX0 (Z_to_bv 5 r)) ->
  getr regs1 (Z_to_bv 5 19) = w64 (pf_F v pos + PF_O_LOW) ->
  a10_mid B n v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val regs1 memc mdc 0.
Proof.
intros n v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val regs1 memc mdc H1 H2 H3 H4 H5 H6 H7.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
split; [intros i Hi; lia|]. split; [lia|]. split; [lia|]. split; [exact H6 | exact H7].
Qed.

Lemma a10_role : forall n, A10_END_stmt B n -> (forall k, A10_LOOP_at B n k) -> H_ROLE B n.
Proof.
intros n HEND HLOOP v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val HKV Hrole.
pose proof HKV as ((HCX & HFI & HOBJ & HSL & HFSH) & HMID & HST & HKVS & HSLB & HRG).
pose proof HFI as (HJ0 & Hly & _ & _ & _ & _ & _ & HRG0).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (a10_frame B LAWS v pos lyc Sc Wc memc0 mdc0 HJ0 Hly)
  as (Hin & HAR & F32 & Fapp & Foff & F4096 & Fc & Fp & Fsh & HBLK).
assert (Happ : 4096 <= pf_F v pos /\
  (pf_F v pos + 2048 <= kLowShadowBeg \/ (kHighMemBeg <= pf_F v pos /\ pf_F v pos + 2048 <= alloc_ceiling)))
  by (unfold in_app, ASAN_CEIL in Fapp; exact Fapp).
destruct HKVS as (Hsplit & Hks & Hkb & Hvs & Hvb).
pose proof Hvs as ((HVZ & NZ) & _).
unfold pf_inb, PF_O_BUF in Hvb.
pose proof HCX as ((_ & _ & _ & _ & _ & Hstk & _) & _).
pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
assert (HSTK : STK_reac_segconf_parse_file = 12800) by reflexivity. rewrite HSTK in Hslo.
assert (HSHr : 0 <= pf_SH v pos /\ pf_SH v pos + 256 < 2 ^ 64).
{ unfold pf_SH, shadow_addr, SHADOW_OFF. pose proof (Z.div_mod (pf_F v pos) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (pf_F v pos) 8 ltac:(lia)).
  unfold kLowShadowBeg, kHighMemBeg in Happ. lia. }
(* the registers the cut gives *)
assert (R27 : getr rX0 27 = w64 (pf_SH v pos)).
{ rewrite <- (a10_getz rX0 27%bv 27 ltac:(vm_compute; reflexivity)).
  exact (pf_a5_k.a5_rg_get rX0 _ 27 (pf_SH v pos) HRG ltac:(cbn [In app PF_RL PF_RM]; tauto)). }
assert (R22 : getr rX0 22 = w64 SB).
{ rewrite SB_SHADOW_OFF. rewrite <- (a10_getz rX0 22%bv 22 ltac:(vm_compute; reflexivity)).
  exact (pf_a5_k.a5_rg_get rX0 _ 22 SHADOW_OFF HRG0 ltac:(cbn [In]; tauto)). }
assert (R9 : getr rX0 9 = w64 (pf_s1 v)).
{ rewrite <- (a10_getz rX0 9%bv 9 ltac:(vm_compute; reflexivity)).
  exact (pf_a5_k.a5_rg_get rX0 _ 9 (pf_s1 v) HRG0 ltac:(cbn [In]; tauto)). }
assert (R25 : getr rX0 25 = w64 vp).
{ rewrite <- (a10_getz rX0 25%bv 25 ltac:(vm_compute; reflexivity)).
  exact (pf_a5_k.a5_rg_get rX0 _ 25 vp HRG ltac:(cbn [In app PF_RL PF_RM]; tauto)). }
assert (Hs1 : alloc_ceiling + 12000 <= pf_s1 v /\ pf_s1 v + 184 <= 2 ^ 47).
{ unfold pf_s1, pf_sp0. pose proof (Z.mod_pos_bound (spZ (p_regs v) - 0x140) 32 ltac:(lia)). lia. }
assert (HSLOT : rdword (rdW Wc memc0) (pf_s1 v + 72) = Some (pf_F v pos + PF_O_LOW)).
{ exact (a10_sl_in (rdW Wc memc0) (pf_s1 v) (PF_SL v pos) 72 (pf_F v pos + PF_O_LOW) HSL
    ltac:(cbn [In PF_SL]; tauto)). }
set (c0 := nth 0 (val ++ [0]) 0) in *.
assert (HC0 : rdW Wc memc0 vp = Some c0)
  by (replace vp with (vp + Z.of_nat 0) by lia;
      exact (HVZ 0%nat ltac:(rewrite length_app; cbn [length]; lia))).
assert (HC0r : 0 <= c0 <= 255)
  by (destruct (aview_byte SEGS _ _ _ _ HC0) as (_ & _ & _ & Hr); lia).
(* the post of the segment, by the role branch of r_key *)
rewrite (a10_r_key_role cf gi nm (ln + 1) (pf_tline (p_s v) o) key val Hsplit Hrole).
(* ---- the plain run 0x881d4 .. 0x881f4: low comes into scope ---- *)
pose proof (ar_entry Wc rX0 memc0 (pf_SH v pos) R27 ltac:(lia) ltac:(lia)
  ltac:(intros i Hi; exact (Fsh i Hi))) as HS.
assert (HEI : img_env VAL A_LIM (a10_E rX0 [])) by (unfold a10_E; apply Eimg_env).
assert (E27 : ew (a10_E rX0 []) 27 = Z_to_bv 64 (pf_SH v pos))
  by (rewrite (a10_ew rX0 _ 27 27%bv eq_refl); exact R27).
assert (U27 : bv_unsigned (ew (a10_E rX0 []) 27) = pf_SH v pos)
  by (rewrite E27; apply unsigned_lit_small; lia).
paj_run_to_sh RUNTOP HS HJ0 A10_SH16.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in
    change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr0 lyx own) end.
  eapply awr_ok_cons_gen with (n := 27%nat) (b := pf_SH v pos);
    [reflexivity | exact U27 | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
  right; right; right; left. exists 5, pos. split; [left; reflexivity|]. right.
  unfold in_zr. cbn [fst snd]. rewrite Hly. change (fs_frame_bytes 5 / 8) with 256.
  unfold pf_SH, pf_F in Ha. lia. }
(* the eight cells of low are 0; every other byte is as at ROLE *)
assert (HA0 : env_agree 32 (Ereg rX0 []) (a10_E rX0 []))
  by (split; [intros nn Hn; unfold a10_E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]).
assert (HSHb : pf_SH v pos + 256 < kHighMemBeg).
{ unfold pf_SH, shadow_addr, SHADOW_OFF, kHighMemBeg.
  pose proof (Z.div_mod (pf_F v pos) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (pf_F v pos) 8 ltac:(lia)).
  lia. }
lazymatch goal with
| HSn : st_ok_pi _ _ ?En ?ssn (restrict _ ?msn) |- _ =>
  assert (HAE1 : env_agree 35 (a10_E rX0 []) En)
    by (env_agree_chain (env_agree_refl 35 (a10_E rX0 [])));
  assert (U27n : bv_unsigned (ew En 27) = pf_SH v pos)
    by (rewrite (a10_ag_ew (a10_E rX0 []) En 35 27 _ HAE1 ltac:(lia) E27);
        apply unsigned_lit_small; lia);
  assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> ~ (pf_SH v pos + 80 <= a < pf_SH v pos + 88) ->
      rdW Wc (ms_mem msn) a = rdW Wc memc0 a)
    by (apply (a10_keep_sh (a10_E rX0 []) _ memc0 memc0 (ms_mem msn) (w_H Wc) (pf_SH v pos) HFr U27);
        intros; reflexivity);
  assert (HFA : forallb (fun r : bv 5 =>
     sv_eqb (sr_get (ss_regs ssn) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) A10_KEPT = true)
    by (vm_compute; reflexivity);
  pose proof (regs_kept_of_st_ok_pi _ _ _ rX0 _ A10_KEPT HSn
    (a10_ag32 _ _ (a10_E rX0 []) En 35 ltac:(lia) HA0 HAE1) HFA) as HKr;
  cbn [ms_regs restrict] in HKr;
  let r := eval vm_compute in (nth_error (ss_mem ssn) 0) in
  lazymatch r with
  | Some (YP09.mkRegion (Some 27%nat) ?lo ?hi ?wlo ?whi ?cs) =>
    assert (HNTH : nth_error (ss_mem ssn) 0
       = Some (YP09.mkRegion (Some 27%nat) lo hi wlo whi cs)) by (vm_compute; reflexivity);
    assert (ZC : forall od, In (YP09.mkChunk od (CVal 1 (SLit 0))) cs ->
        rdW Wc (ms_mem msn) (pf_SH v pos + od) = Some 0)
      by (intros od Hod;
          pose proof (a10_wbyte En ssn _ _ 27%nat 0%nat lo hi wlo whi cs od (SLit 0) _ HSn HNTH Hod U27n)
            as HWx;
          rewrite HWx; f_equal; rewrite U_SLit; reflexivity);
    assert (Z0 : forall i, 0 <= i < 8 -> rdW Wc (ms_mem msn) (pf_SH v pos + 80 + i) = Some 0);
    [ intros i Hi; replace (pf_SH v pos + 80 + i) with (pf_SH v pos + (80 + i)) by lia;
      apply ZC;
      assert (Hi8 : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia;
      repeat (destruct Hi8 as [Hi8|Hi8]); subst i; cbn; tauto
    | ]
  end
end.
(* every byte of the cut that the eight cells do not cover is unchanged *)
assert (FAR : forall a, a10_far v pos a -> ~ (pf_SH v pos + 80 <= a < pf_SH v pos + 88))
  by (intros a (Ha & HnD) Hc; apply HnD; right; lia).
assert (KMf : forall a, a10_far v pos a -> rdW Wc (ms_mem ms) a = rdW Wc memc0 a)
  by (intros a Ha; apply KM1; [exact (proj1 Ha) | exact (FAR a Ha)]).
(* the registers of the cut, at the state after the stores *)
assert (Q9 : getr (ms_regs ms) 9 = w64 (pf_s1 v))
  by (rewrite <- (a10_getz (ms_regs ms) 9%bv 9 ltac:(vm_compute; reflexivity));
      rewrite (a10_kept_keep rX0 (ms_regs ms) HKr 9 ltac:(a10_inZ));
      rewrite (a10_getz rX0 9%bv 9 ltac:(vm_compute; reflexivity)); exact R9).
assert (Q22 : getr (ms_regs ms) 22 = w64 SB)
  by (rewrite <- (a10_getz (ms_regs ms) 22%bv 22 ltac:(vm_compute; reflexivity));
      rewrite (a10_kept_keep rX0 (ms_regs ms) HKr 22 ltac:(a10_inZ));
      rewrite (a10_getz rX0 22%bv 22 ltac:(vm_compute; reflexivity)); exact R22).
assert (Q25 : getr (ms_regs ms) 25 = w64 vp)
  by (rewrite <- (a10_getz (ms_regs ms) 25%bv 25 ltac:(vm_compute; reflexivity));
      rewrite (a10_kept_keep rX0 (ms_regs ms) HKr 25 ltac:(a10_inZ));
      rewrite (a10_getz rX0 25%bv 25 ltac:(vm_compute; reflexivity)); exact R25).
(* val's bytes and the slot s1 + 0x48 are off a10_D *)
assert (FV : forall x, pf_F v pos + PF_O_BUF <= x < pf_F v pos + PF_O_BUF + 512 -> a10_far v pos x).
{ intros x Hx. split; [unfold PF_O_BUF in Hx; lia|].
  apply (a10_nD_in v pos x F32 Fapp Fc). left. unfold PF_O_BUF, PF_O_LOW in *. lia. }
assert (QC0 : rdW Wc (ms_mem ms) vp = Some c0)
  by (rewrite (KMf vp (FV vp ltac:(unfold PF_O_BUF in *; lia))); exact HC0).
assert (FS : forall a, alloc_ceiling <= a < 2 ^ 64 -> a10_far v pos a).
{ intros a Ha. split; [lia|]. apply (a10_nD v pos a F32 Fapp Foff Fc). right; right; right. lia. }
assert (QSL : rdword (rdW Wc (ms_mem ms)) (pf_s1 v + 72) = Some (pf_F v pos + PF_O_LOW))
  by (exact (a10t_word (rdW Wc memc0) (rdW Wc (ms_mem ms)) (a10_far v pos) KMf _ _ HSLOT
              (fun kk Hkk => FS (pf_s1 v + 72 + kk) ltac:(lia)))).
(* the shadow cells of val's bytes: 0, as inside a line *)
assert (QBUF : forall x, pf_F v pos + PF_O_BUF <= x < pf_F v pos + PF_O_BUF + 512 ->
    rdW Wc (ms_mem ms) (shadow_of_addr SHADOW_OFF x) = Some 0).
{ intros x Hx.
  rewrite (a10_sh_of v pos x F32 ltac:(unfold PF_O_BUF in *; lia)).
  assert (Hq : 8 <= (x - pf_F v pos) / 8 < 72).
  { clear - Hx. unfold PF_O_BUF in Hx.
    pose proof (Z.div_mod (x - pf_F v pos) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (x - pf_F v pos) 8 ltac:(lia)). lia. }
  set (q := (x - pf_F v pos) / 8) in *. clearbody q.
  rewrite KMf.
  - rewrite (HFSH q ltac:(lia)). f_equal. apply a10_shb_bufline. exact Hq.
  - split; [lia|]. apply (a10_nD_in v pos _ F32 Fapp Fc). right. exists q. split; [reflexivity|]. lia. }
(* ---- the token run 0x881f4 .. 0x8820c: check 16 on val[0], a2 = val[0], s3 = low, then beqz a2 ---- *)
assert (HRA25 : range_addressable (rdW Wc (ms_mem ms)) SHADOW_OFF vp 1).
{ intros x Hx. assert (x = vp) as -> by lia. exists 0.
  split; [apply QBUF; unfold PF_O_BUF in *; lia | left; reflexivity]. }
pmkst HS.
clear HS HFr.
pose proof alloc_ceiling_value as (HCV & _).
pose proof (as_entry Wc (ms_regs ms) (ms_mem ms) (pf_s1 v) vp (pf_F v pos + PF_O_LOW) c0
  Q9 Q22 Q25 ltac:(lia) ltac:(lia) ltac:(unfold PF_O_BUF in *; lia) ltac:(unfold PF_O_BUF in *; lia)
  ltac:(unfold PF_O_LOW; lia) ltac:(unfold PF_O_LOW; lia) HC0r QC0 QSL ltac:(unfold PF_O_BUF in *; lia)) as HS2.
set (XS2 := [w64 c0; w64 (pf_F v pos + PF_O_LOW)]) in *.
assert (HEI2 : img_env VAL A_LIM (a10_E (ms_regs ms) XS2)) by (unfold a10_E; apply Eimg_env).
assert (HA02 : env_agree 32 (Ereg (ms_regs ms) XS2) (a10_E (ms_regs ms) XS2))
  by (split; [intros nn Hn; unfold a10_E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]).
assert (G22 : ew (a10_E (ms_regs ms) XS2) 22 = Z_to_bv 64 SB)
  by (rewrite (a10_ew (ms_regs ms) _ 22 22%bv eq_refl); exact Q22).
assert (G25 : ew (a10_E (ms_regs ms) XS2) 25 = Z_to_bv 64 vp)
  by (rewrite (a10_ew (ms_regs ms) _ 25 25%bv eq_refl); exact Q25).
assert (G32 : ew (a10_E (ms_regs ms) XS2) 32 = Z_to_bv 64 c0)
  by (unfold a10_E, XS2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra (ms_regs ms) _ 0)).
assert (G33 : ew (a10_E (ms_regs ms) XS2) 33 = Z_to_bv 64 (pf_F v pos + PF_O_LOW))
  by (unfold a10_E, XS2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra (ms_regs ms) _ 1)).
assert (SHOK2 : sh_ok SEGS a10_Bx as_SH (a10_E (ms_regs ms) XS2) (mrestrict (w_H Wc) (ms_mem ms))).
{ unfold sh_ok, as_SH. apply Forall_cons; [|apply Forall_nil].
  eapply (shent_ok_of_range SEGS (w_H Wc) (ms_mem ms) _ a10_Bx 25%nat vp 1 vp 0 1 HRA25);
  [ unfold a10_Bx; rewrite (U_atom _ 22 SB G22) by (unfold SB; lia); reflexivity
  | apply (U_atom _ 25 _ G25); unfold PF_O_BUF in *; lia | lia | lia |].
  intros x Hx. change (Z.min 0 1) with 0 in Hx. change (Z.max 0 1) with 1 in Hx.
  unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. unfold PF_O_BUF in *. lia. }
revert HS2 SHOK2 HEI2 HA02 G22 G25 G32 G33.
generalize (a10_E (ms_regs ms) XS2) as E2.
intros E2 HS2 SHOK2 HEI2 HA02 G22 G25 G32 G33.
pose proof (env_agree_refl 35 E2) as HAE2.
paj_run_tok RUN HS2 HJ0 SHOK2 Bspan.
{ a10_ro_awr. }
a10_ro_keep KM2.
lazymatch goal with
| HSn : st_ok_pi _ _ ?En _ _ |- _ =>
  assert (HAEb : env_agree 35 E2 En) by (env_agree_chain HAE2);
  assert (G32b : ew En 32 = Z_to_bv 64 c0) by (exact (a10_ag_ew E2 En 35 32 _ HAEb ltac:(lia) G32))
end.
psrr_branch_tok RUN BR HS2 SHOK2 Bspan.
- (* val[0] = 0: the value is empty, 0x88434 a3 = 0, then END *)
  pose proof (a10_br_eq _ 32 c0 0 _ G32b ltac:(lia) ltac:(lia) Hc) as Hc0.
  apply Z.eqb_eq in Hc0. clear Hc.
  assert (Hv0 : val = []).
  { clear - Hc0 NZ. subst c0. destruct val as [|x r]; [reflexivity|].
    exfalso. apply NZ. left. exact Hc0. }
  assert (Hm0 : length (r_low val 0 64) = 0%nat) by (rewrite Hv0; reflexivity).
  paj_run_to_tok RUNTO HS2 HJ0 SHOK2 Bspan A10_END.
  { a10_ro_awr. }
  a10_ro_keep KM3.
  lazymatch goal with
  | HSn : st_ok_pi _ _ ?En ?ssn (restrict _ ?msn) |- _ =>
    assert (HAEf : env_agree 35 E2 En) by (env_agree_chain HAE2);
    assert (HFAx : forallb (fun r : bv 5 =>
       sv_eqb (sr_get (ss_regs ssn) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) A10_KEPT = true)
      by (vm_compute; reflexivity);
    pose proof (regs_kept_of_st_ok_pi _ _ _ (ms_regs ms) _ A10_KEPT HSn
      (a10_ag32 _ _ E2 En 35 ltac:(lia) HA02 HAEf) HFAx) as HKr2;
    cbn [ms_regs restrict] in HKr2;
    assert (G33f : ew En 33 = Z_to_bv 64 (pf_F v pos + PF_O_LOW))
      by (exact (a10_ag_ew E2 En 35 33 _ HAEf ltac:(lia) G33));
    pose proof (a10_reg_sym _ _ _ _ (Z_to_bv 5 13) (SLit 0) 0 HSn ltac:(vm_compute; reflexivity)
      (U_lit En 0 ltac:(lia)) ltac:(lia)) as N13;
    pose proof (a10_reg_sym _ _ _ _ (Z_to_bv 5 19) (SOff 33 0) (pf_F v pos + PF_O_LOW) HSn
      ltac:(vm_compute; reflexivity) (U_atom _ 33 _ G33f ltac:(unfold PF_O_LOW; lia))
      ltac:(unfold PF_O_LOW; lia)) as N19;
    pmkst HSn;
    apply (HEND v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val
      (ms_regs msn) (ms_mem msn) _);
    [ rewrite Hm0;
      apply (a10_mid_init n v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val
        (ms_regs msn) (ms_mem msn) _ HKV Hrole HJ0);
      [ intros a Ha; rewrite KM3 by exact (proj1 Ha); rewrite KM2 by exact (proj1 Ha); exact (KMf a Ha)
      | intros i Hi; rewrite KM3 by lia; rewrite KM2 by lia; exact (Z0 i Hi)
      | intros r Hr; rewrite (a10_kept_keep _ _ HKr2 r Hr); exact (a10_kept_keep _ _ HKr r Hr)
      | exact N19 ]
    | rewrite Hm0; exact N13 ]
  end.
- (* val[0] <> 0: 0x88210 a0 = 0, a1 = val + 1, then LOOP *)
  pose proof (a10_br_eq _ 32 c0 0 _ G32b ltac:(lia) ltac:(lia) Hc) as Hc0.
  apply Z.eqb_neq in Hc0. clear Hc.
  assert (Hvl : (0 < length val)%nat).
  { clear - Hc0. subst c0. destruct val as [|x r]; cbn in *; lia. }
  assert (Hc0v : c0 = nth 0 val 0) by (subst c0; rewrite app_nth1 by exact Hvl; reflexivity).
  paj_run_to_tok RUNTO HS2 HJ0 SHOK2 Bspan A10_LOOP.
  { a10_ro_awr. }
  a10_ro_keep KM3.
  lazymatch goal with
  | HSn : st_ok_pi _ _ ?En ?ssn (restrict _ ?msn) |- _ =>
    assert (HAEf : env_agree 35 E2 En) by (env_agree_chain HAE2);
    assert (HFAx : forallb (fun r : bv 5 =>
       sv_eqb (sr_get (ss_regs ssn) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) A10_KEPT = true)
      by (vm_compute; reflexivity);
    pose proof (regs_kept_of_st_ok_pi _ _ _ (ms_regs ms) _ A10_KEPT HSn
      (a10_ag32 _ _ E2 En 35 ltac:(lia) HA02 HAEf) HFAx) as HKr2;
    cbn [ms_regs restrict] in HKr2;
    assert (G33f : ew En 33 = Z_to_bv 64 (pf_F v pos + PF_O_LOW))
      by (exact (a10_ag_ew E2 En 35 33 _ HAEf ltac:(lia) G33));
    assert (G25f : ew En 25 = Z_to_bv 64 vp) by (exact (a10_ag_ew E2 En 35 25 _ HAEf ltac:(lia) G25));
    assert (G32f : ew En 32 = Z_to_bv 64 c0) by (exact (a10_ag_ew E2 En 35 32 _ HAEf ltac:(lia) G32));
    pose proof (a10_reg_sym _ _ _ _ (Z_to_bv 5 10) (SLit 0) 0 HSn ltac:(vm_compute; reflexivity)
      (U_lit En 0 ltac:(lia)) ltac:(lia)) as N10;
    pose proof (a10_reg_sym _ _ _ _ (Z_to_bv 5 11) (SOff 25 1) (vp + 1) HSn ltac:(vm_compute; reflexivity)
      (U_atom_off _ 25 vp 1 G25f ltac:(unfold PF_O_BUF in *; lia) ltac:(unfold PF_O_BUF in *; lia))
      ltac:(unfold PF_O_BUF in *; lia)) as N11;
    pose proof (a10_reg_sym _ _ _ _ (Z_to_bv 5 12) (SOff 32 0) c0 HSn ltac:(vm_compute; reflexivity)
      (U_atom _ 32 _ G32f ltac:(lia)) ltac:(lia)) as N12;
    pose proof (a10_reg_sym _ _ _ _ (Z_to_bv 5 19) (SOff 33 0) (pf_F v pos + PF_O_LOW) HSn
      ltac:(vm_compute; reflexivity) (U_atom _ 33 _ G33f ltac:(unfold PF_O_LOW; lia))
      ltac:(unfold PF_O_LOW; lia)) as N19;
    pmkst HSn;
    apply (HLOOP 0%nat v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi
      kp vp key val (ms_regs msn) (ms_mem msn) _);
    [ apply (a10_mid_init n v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi kp vp key val
        (ms_regs msn) (ms_mem msn) _ HKV Hrole HJ0);
      [ intros a Ha; rewrite KM3 by exact (proj1 Ha); rewrite KM2 by exact (proj1 Ha); exact (KMf a Ha)
      | intros i Hi; rewrite KM3 by lia; rewrite KM2 by lia; exact (Z0 i Hi)
      | intros r Hr; rewrite (a10_kept_keep _ _ HKr2 r Hr); exact (a10_kept_keep _ _ HKr r Hr)
      | exact N19 ]
    | exact Hvl
    | exact N10
    | exact N11
    | rewrite Hc0v in N12; exact N12 ]
  end.
Qed.
End e.
End f.
End d.

(* the segment theorem: at every FP state, from INTENT at every FP state (HA_INTENT) *)
Section h.
Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
Variable B : asyms.
Theorem pf_a10a_holds : S_A10a B.
Proof.
intros f0 n HI.
pose proof (YG0q.AR_laws_ok SEGS B) as LAWS.
pose proof (a10_end (fx := f0) B LAWS n (HI f0)) as HE.
exact (a10_role (fx := f0) B LAWS n HE (a10_loop (fx := f0) B LAWS n HE)).
Qed.
End h.
