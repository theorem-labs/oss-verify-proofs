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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 279 of its 318 lines of code are new or changed and 414 lines of the source are left out. *)
(* reac_declared_vlan_split on fuzz_segconf image A: the point K5 (0x89cec), after the checked memcpy. `add a0,s1,s4`,
   the check of the 1-byte store to parent + di (0x89cf0-0x89cfc, killed by parent's shadow), `sb zero,0(a0)` (the
   NUL of the parent string), `mv a0,s1` and the call of name_ok (0x89d08) through its contract, then the point K6
   (0x89d0c). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YG0p YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaDenot PaSB PaLibG PaLibH PaLibF PaCallRun PaCall.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegGlob SegPgBase SegABase SegObj.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import reac_declared_vlan_split_c name_ok_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import reac_declared_vlan_split_lem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import reac_declared_vlan_split_k reac_declared_vlan_split_d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import reac_declared_vlan_split_r reac_declared_vlan_split_h.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import reac_declared_vlan_split_s6.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegInstA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the byte parent + di the `sb` writes: its region (atom 40 = parent + di, the extra word of the seed) and its check *)
Definition vs_nul_r : YP09.region := YP09.mkRegion (Some 40%nat) 0 1 0 1 [].
Definition vs_SH5 : list shent := [mkSHE 40 0 1].
Definition vs_fs5 : list (nat * afact) :=
  [(9%nat, mkAF 4096 (2 ^ 47 - 16) 0); (20%nat, mkAF 1 14 0); (40%nat, mkAF 4096 (2 ^ 47 - 1) 0)].
Lemma vs_nth_firstn : forall (l : list Z) n i, (i < n)%nat -> nth i (firstn n l) 0 = nth i l 0.
Proof.
induction l as [|x l IH]; intros n i Hi.
- destruct n; cbn [firstn]; reflexivity.
- destruct n as [|n]; [lia|]. destruct i as [|i]; [reflexivity|]. cbn [firstn nth]. apply IH. lia.
Qed.

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
Variables gotw guard : Z.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.
(* the listing's facts: every program function's call target is its entry, the relro range is the image's *)
Hypothesis SIGP : seg_sig_prog.
Hypothesis RELRO : seg_val_relro.
(* the callee: name_ok's contract at its entry, its stack window and the read-only range *)
Hypothesis NAMEOK : name_ok_contract SEGS B (BASE + AF_name_ok) STK_name_ok SEG_RLO SEG_RHI.

Lemma vs_K5 : vs_K6_stmt B gotw guard -> vs_K5_stmt B gotw guard.
Proof using SIGP RELRO NAMEOK.
intros HK6. unfold vs_K5_stmt. intros e regs' mem' md' di v HE HC Hdi Hdi0 Hne Hdig Hv Hvr R20 R21 HPB.
pose proof HE as (HPRE & HROD & H10 & B10 & H11 & B11 & H12 & H13 & B13 & HSP & Hnev).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HC as (HJ & HR & HSL & HKP & HPR).
pose proof HR as (Hsp & G3 & G4 & G8 & G9 & G18 & G19 & G22 & G27).
pose proof HSP as (Hs0 & Hstr & Hlen & Hsadd & Hamr & Hsloc & Hp0 & Hcap & Hpdst & Hpadd & Hpdisj & Hv0 & Hv2 & Hvdst & Hvadd & Hvdisj & Hssp).
assert (HVS : STK_reac_declared_vlan_split = 12352) by reflexivity.
assert (HNS : STK_name_ok = 4160) by reflexivity.
unfold e_sp in *.
(* the model *)
set (p := firstn di (e_s e)) in *.
assert (Hnul : SegModel.nulfree (e_s e)) by exact (proj2 (proj1 Hstr)).
assert (Hcopy : split_copy (e_s e) = Some di)
  by (apply vs_copy_some; [exact Hnul | exact Hlen | exact Hdi | exact Hdi0 | exact Hne | exact Hdig | unfold vs_tail in Hv; lia]).
pose proof (vs_di_lt _ _ Hnul Hdi) as Hdil.
assert (Hdi14 : 1 <= Z.of_nat di <= 14) by lia.
destruct (vs_dst_facts B _ _ _ _ _ _ _ _ 16 HAR Hstk ltac:(lia) Hpdst) as (Plo & Phi & Pplace).
destruct (vs_dst_facts B _ _ _ _ _ _ _ _ 2 HAR Hstk ltac:(lia) Hvdst) as (Vlo & Vhi & Vplace).
(* the seed: the frame, s1 = parent, s4 = di, s6 = SB, atom 40 = parent + di; the byte region and the alias *)
set (E := Eimg (Ereg regs' (vs_xs (e_regs e) ++ [Z_to_bv 64 (e_parent e + Z.of_nat di)]))).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EV : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs' r)
  by (intros n r Hn; subst E; apply vs_EE; exact Hn).
assert (E40 : ew E 40 = Z_to_bv 64 (e_parent e + Z.of_nat di))
  by (subst E; exact (vs_Ey regs' (e_regs e) _ 0 ltac:(lia))).
assert (HS : st_ok_pi SEGS VAL E (vs_ssK VS_K5 vs_fs5)
  (restrict (w_H (e_W e)) (mkst regs' (Z_to_bv 64 (BASE + VS_K5)) mem' (seg_rom SEGS)))).
{ apply vs_seedK.
  - replace (spZ regs' + 64) with (spZ (e_regs e)) by lia. exact HSL.
  - lia.
  - rewrite Hsp. replace (spZ (e_regs e) - 64) with (spZ (e_regs e) + (-4) * 16) by lia.
    rewrite Z_mod_plus_full. exact Hal16.
  - exact G22.
  - cbn [atoms_ok vs_fs5]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E.
    rewrite (EV 9%nat 9%bv eq_refl), (EV 20%nat 20%bv eq_refl), E40, G9, R20.
    unfold w64. rewrite !unsigned_lit_small by lia.
    rewrite Z.pow_0_r, Z.mod_1_r. repeat split; first [exact I | lia]. }
(* the footprint is application memory, off the shadow: parent's di + 1 bytes and, when the split succeeds, vid's 2 *)
assert (HFPw : forall x, inFP (e_FP e) x ->
  (e_parent e <= x < e_parent e + Z.of_nat di + 1) \/ (e_vid e <= x < e_vid e + 2)).
{ intros x Hx. unfold e_FP, split_W in Hx. rewrite Hcopy in Hx. cbn [app] in Hx.
  apply inFP_cons in Hx as [Hx | Hx]; [left; cbn [fst snd] in Hx; lia|].
  destruct (SegModel.vlan_split (e_s e)); [|exfalso; exact (inFP_nil x Hx)].
  apply inFP_cons in Hx as [Hx | Hx]; [right; cbn [fst snd] in Hx; lia | exfalso; exact (inFP_nil x Hx)]. }
assert (HFPs : forall x, inFP (e_FP e) x -> x < kLowShadowBeg \/ kHighShadowEnd <= x).
{ intros x Hx. destruct (HFPw x Hx) as [Hx1 | Hx1].
  - destruct Pplace as [(Hia & _) | (Hs1 & _)]; [unfold in_app, kLowShadowBeg, kHighMemBeg, kHighShadowEnd, ASAN_CEIL in *|]; unfold kLowShadowBeg, kHighShadowEnd in *; lia.
  - destruct Vplace as [(Hia & _) | (Hs1 & _)]; [unfold in_app, kLowShadowBeg, kHighMemBeg, kHighShadowEnd, ASAN_CEIL in *|]; unfold kLowShadowBeg, kHighShadowEnd in *; lia. }
pose proof (proj1 HJ) as HARc.
(* parent's bytes are present (a frame or block byte, or a present real-stack byte) *)
assert (PPc : forall i, 0 <= i < 16 -> apresent (w_H (e_W e)) mem' (e_parent e + i)).
{ apply (vs_dst_present B (e_ly e) (e_S e) (e_W e) (e_mem e) (e_regs e) (e_parent e) 16 (e_ly e) (e_S e) (e_W e) mem' md'
    Hpdst HARc eq_refl eq_refl (Permutation_refl _)).
  intros _ i Hi Hp. exact (HPR _ Hp). }
assert (BV40 : base_val E (Some 40%nat) = e_parent e + Z.of_nat di)
  by (cbn [base_val]; rewrite E40; apply unsigned_lit_small; lia).
assert (BV2 : base_val E (Some 2%nat) = spZ (e_regs e) - 64)
  by (cbn [base_val]; rewrite (EV 2%nat 2%bv eq_refl); exact Hsp).
assert (Rok : region_ok SEGS E (mrestrict (w_H (e_W e)) mem') vs_nul_r).
{ unfold region_ok, vs_nul_r. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite BV40. split; [lia|]. split; [lia|].
  split; [intros o Ho; apply (apresent_writable SEGS); replace (e_parent e + Z.of_nat di + o) with (e_parent e + (Z.of_nat di + o)) by lia;
    apply PPc; lia | constructor]. }
lazymatch type of HS with st_ok_pi _ _ _ ?ss ?msx =>
assert (Rdj : all_disjoint E vs_nul_r (ss_mem ss));
[ cbn [ss_mem vs_ssK all_disjoint]; unfold extent_disjoint; cbn [vs_nul_r vs_slots_r YP09.r_base YP09.r_lo YP09.r_hi];
  rewrite BV40, BV2; split; [|exact I]; destruct Pplace as [(_ & Hp1) | (Hp1 & _)]; lia
| pose proof (st_ok_pi_add_region E ss msx vs_nul_r HS eq_refl Rok Rdj) as HS2; clear HS; rename HS2 into HS ] end.
lazymatch type of HS with st_ok_pi _ _ _ ?ss ?msx =>
pose proof (st_ok_pi_add_alias E ss msx (SAlu ALU_ADD (SOff 9 0) (SOff 20 0)) (SOff 40 0) HS
  (vs_add_alias E 9 20 40 (e_parent e) (Z.of_nat di) ltac:(rewrite (EV 9%nat 9%bv eq_refl), G9; reflexivity) ltac:(lia)
    ltac:(rewrite (EV 20%nat 20%bv eq_refl), R20; reflexivity) ltac:(lia) ltac:(lia) E40)) as HS2; clear HS; rename HS2 into HS end.
assert (UB : U E vs_Bx = SHADOW_OFF).
{ unfold vs_Bx. apply U_atom; [rewrite (EV 22%nat 22%bv eq_refl), G22; reflexivity | unfold SHADOW_OFF; lia]. }
(* parent's shadow at this state (the journal from the entry keeps it) *)
assert (HRAp : range_addressable (rdW (e_W e) mem') SHADOW_OFF (e_parent e) 16).
{ apply (vs_dst_ra B (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) (e_regs e) STK_reac_declared_vlan_split (e_FP e) (e_ly e) (e_S e) (e_W e) mem' md' 0
    (e_parent e) 16 HAR Hstk Hpdst (proj1 (proj2 (proj2 (proj2 Hpadd)))) HJ eq_refl (Permutation_refl _) HFPs). }
assert (SHOK5 : sh_ok SEGS vs_Bx vs_SH5 E (mrestrict (w_H (e_W e)) mem')).
{ unfold sh_ok, vs_SH5. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H (e_W e)) mem' E vs_Bx 40 (e_parent e) 16 (e_parent e + Z.of_nat di) 0 1 HRAp UB).
  - apply U_atom; [exact E40 | lia].
  - lia.
  - lia.
  - intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF.
    destruct Pplace as [(Hia & _) | (Hs1 & _)]; [unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hia | ]; lia. }
unfold vs_goal, vs_cfg.
paj_run_tok RUN HS HJ SHOK5 vs_Bspan.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr0 lyx own) end.
  eapply (@awr_ok_cons_gen SEGS B _ _ _ _ _ _ _ _ _ _ _ 40%nat (e_parent e + Z.of_nat di)); [reflexivity | | |].
  - rewrite E40. apply unsigned_lit_small. lia.
  - intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
    apply (vs_dst_awr B (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) (e_regs e) _ _ (e_ly e) (e_S e) [] (e_parent e) 16 a
      HAR Hpdst eq_refl (Permutation_refl _)); [| lia].
    unfold e_FP, split_W. rewrite Hcopy. exists (e_parent e, e_parent e + Z.of_nat di + 1).
    split; [apply in_or_app; left; left; reflexivity | cbn [fst snd]; lia].
  - repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
pmkst HS.
(* what the run wrote: the byte parent + di *)
assert (EU40 : bv_unsigned (ew E 40) = e_parent e + Z.of_nat di) by (rewrite E40; apply unsigned_lit_small; lia).
set (X5 := fun a => e_parent e + Z.of_nat di <= a < e_parent e + Z.of_nat di + 1).
lazymatch goal with Hfr : frame_of E _ (mrestrict _ _) (mrestrict _ _) |- _ =>
pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ X5 Hfr
  ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?EU40 in Hrr; unfold X5; lia|]);
    destruct Hin)) as UN end.
pose proof (proj1 HJ) as HARm.
pose proof HKP as HKP0.
(* parent's bytes are no image bytes and no shadow bytes *)
assert (HPimg : forall x, e_parent e <= x < e_parent e + 16 -> ~ in_img SEGS x)
  by (intros x Hx; exact (vs_dst_not_img B _ _ _ _ _ _ _ _ _ x HAR Hstk Hpdst Hx)).
assert (HPsh : forall x, e_parent e <= x < e_parent e + 16 -> ~ (kLowShadowBeg <= x < kHighShadowEnd)).
{ intros x Hx. destruct Pplace as [(Hia & _) | (Hs1 & _)]; [unfold in_app, kHighMemBeg, ASAN_CEIL in Hia|];
  unfold kLowShadowBeg, kHighShadowEnd in *; lia. }
assert (HLM : kLowMemEnd <= spZ (e_regs e) - STK_reac_declared_vlan_split) by (unfold kLowMemEnd; lia).
assert (HSE : kHighShadowEnd <= spZ (e_regs e) - STK_reac_declared_vlan_split) by (unfold kHighShadowEnd; lia).
(* the shadow is the entry's *)
assert (HSHK : forall y, kLowShadowBeg <= y < kHighShadowEnd -> rdW (e_W e) (ms_mem ms) y = rdW (e_W e) (e_mem e) y).
{ intros y Hy. rewrite (UN y ltac:(unfold kLowShadowBeg, kHighShadowEnd in Hy; lia) ltac:(unfold X5; intros Hx; exact (HPsh y ltac:(lia) Hy))).
  apply HKP; [unfold kLowShadowBeg, kHighShadowEnd in Hy; lia | lia | cbv beta; intros Hx; exact (HPsh y ltac:(lia) Hy)]. }
(* the read-only bytes are the entry's *)
assert (HROc : arodata_okP SEGS SEG_RLO SEG_RHI B (rdW (e_W e) (ms_mem ms))).
{ intros a Hro Ho Herr. pose proof (vs_ro_img RELRO a Hro) as Hai. pose proof (pa_segs_low a Hai) as Hal.
  assert (Hnp : ~ (e_parent e <= a < e_parent e + 16)) by (intros Hp; exact (HPimg a Hp Hai)).
  rewrite (UN a ltac:(unfold kLowMemEnd in Hal; lia) ltac:(unfold X5; lia)).
  rewrite HKP; [exact (HROD a Hro Ho Herr) | unfold kLowMemEnd in Hal; lia | lia | cbv beta; lia]. }
(* the call target *)
assert (SG : SIG SS_name_ok = BASE + AF_name_ok)
  by (rewrite (SIGP SS_name_ok); [reflexivity | vm_compute; repeat (first [left; reflexivity | right])]).
rewrite SG.
(* the registers at the call *)
assert (PR : forall r : Z, acallee_saved r -> getr (ms_regs ms) (Z_to_bv 5 r) = getr regs' (Z_to_bv 5 r)).
{ intros r Hr.
  assert (Hcases : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
    r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by (unfold acallee_saved in Hr; lia).
  repeat (destruct Hcases as [-> | Hcases]); try subst r;
  lazymatch goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
    let n := eval compute in (Z.to_nat k) in
    eapply (vs_reg_atom_c _ _ _ _ _ n _ HS); [repeat (rewrite ew_ewset_other by lia); apply EV; reflexivity | vm_compute; reflexivity] end. }
assert (P10 : getr (ms_regs ms) 10 = w64 (e_parent e)).
{ lazymatch type of HS with st_ok ?sg ?Ex ?ss (restrict ?Hh ?msx) =>
    pose proof (st_ok_restrict_reg sg Hh Ex ss msx 10%bv HS) as P;
    let x := eval vm_compute in (sr_get (ss_regs ss) 10%bv) in change (sr_get (ss_regs ss) 10%bv) with x in P end.
  rewrite P. cbn [sv_denot]. rewrite !ew_ewset_other by lia. rewrite (EV 9%nat 9%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned.
  exact G9. }
assert (P1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + VS_K6)).
{ lazymatch type of HS with st_ok ?sg ?Ex ?ss (restrict ?Hh ?msx) =>
    pose proof (st_ok_restrict_reg sg Hh Ex ss msx 1%bv HS) as P;
    let x := eval vm_compute in (sr_get (ss_regs ss) 1%bv) in change (sr_get (ss_regs ss) 1%bv) with x in P end.
  rewrite P. cbn [sv_denot]. rewrite !ew_ewset_other by lia. exact (img_env_codeptr E HEI VS_K6). }
assert (Psp : spZ (ms_regs ms) = spZ (e_regs e) + (-64)).
{ pose proof Hsp as Hsp'. unfold spZ in Hsp' |- *. change (getr (ms_regs ms) 2) with (getr (ms_regs ms) (Z_to_bv 5 2)).
  rewrite (PR 2 ltac:(unfold acallee_saved; lia)). exact Hsp'. }
assert (P3 : getr (ms_regs ms) 3 = w64 (as_gp B)).
{ change (getr (ms_regs ms) 3) with (getr (ms_regs ms) (Z_to_bv 5 3)). rewrite (PR 3 ltac:(unfold acallee_saved; lia)).
  exact (eq_trans G3 Hgp). }
assert (P4 : getr (ms_regs ms) 4 = w64 (as_tp B)).
{ change (getr (ms_regs ms) 4) with (getr (ms_regs ms) (Z_to_bv 5 4)). rewrite (PR 4 ltac:(unfold acallee_saved; lia)).
  exact (eq_trans G4 Htp). }
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
assert (HRA : YK0s.ret_ok (getr (ms_regs ms) 1)) by (rewrite P1; apply ret_ok_codeptr_v; [unfold VS_K6; lia | reflexivity]).
assert (HRA4 : 4096 <= bv_unsigned (getr (ms_regs ms) 1))
  by (rewrite P1, unsigned_lit_small by (unfold VS_K6; lia); unfold VS_K6; lia).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
(* the chain of s0 = vid: none below the allocator's ceiling, the caller's stack (present from sp) above it *)
assert (Es0 : s0Z (ms_regs ms) = e_vid e).
{ unfold s0Z. change (getr (ms_regs ms) 8) with (getr (ms_regs ms) (Z_to_bv 5 8)). rewrite (PR 8 ltac:(unfold acallee_saved; lia)).
  change (getr regs' (Z_to_bv 5 8)) with (getr regs' 8). rewrite G8. unfold w64. apply unsigned_lit_small. lia. }
assert (HCH : exists ch1, achain (e_ly e) (rdW (e_W e) (ms_mem ms)) (spZ (e_regs e) + -64) (s0Z (ms_regs ms)) ch1).
{ rewrite Es0. pose proof Hvdst as HVD.
  destruct HVD as [((cid & pos & Hin & _ & H1 & H2) & _) | [((b & m & Hin & H1 & H2) & _) | (Hs1 & Hs2 & _ & HSP0)]].
  - exists []. apply achain_low. destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR Hin) as (F0 & F1 & F2). lia.
  - exists []. apply achain_low. destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hin) as (_ & _ & B1 & _ & _ & _ & Bm).
    destruct (req_size_pos m ltac:(lia)). lia.
  - apply achain_any; [| right; right; right; lia].
    apply (astack_rd_of_pres SEGS). intros a Ha.
    destruct (Z_lt_le_dec a (spZ (e_regs e))) as [Hlt | Hge].
    + exact (HJpres a ltac:(lia)).
    + exact (apresent_grows _ _ _ a HG (HPR a (HSP0 a ltac:(lia)))). }
destruct HCH as (ch1 & HCH1).
(* name_ok's precondition *)
assert (Hlp : length p = di) by (subst p; rewrite length_firstn; lia).
assert (HSAc : sa_addr (rdW (e_W e) (ms_mem ms)) (e_parent e) (Z.of_nat di + 1)).
{ apply (vs_sa_addr_sub _ _ 16); [| lia]. apply (vs_sa_addr_keep (rdW (e_W e) (e_mem e))); [exact Hpadd | lia | exact HSHK]. }
assert (HNP : name_ok_pre SEGS B (e_ly e) (e_S e) (e_W e) (ms_mem ms) (ms_regs ms) (e_parent e) p).
{ unfold name_ok_pre. rewrite Hlp. split; [exact Hp0|]. split; [|split].
  - split.
    + intros i Hi. rewrite length_app, Hlp in Hi. cbn [length] in Hi.
      destruct (Nat.lt_ge_cases i di) as [Hlt | Hge].
      * rewrite (UN (e_parent e + Z.of_nat i) ltac:(lia) ltac:(unfold X5; lia)). rewrite (HPB i Hlt).
        rewrite app_nth1 by (rewrite Hlp; exact Hlt). subst p. rewrite (vs_nth_firstn _ _ _ Hlt). reflexivity.
      * assert (Ei : i = di) by lia. subst i. rewrite app_nth2 by (rewrite Hlp; lia). rewrite Hlp, Nat.sub_diag. cbn [nth].
        lazymatch type of HS with st_ok _ ?Ex ?ss _ =>
          let r := eval vm_compute in (nth 0 (ss_mem ss) vs_nul_r) in
          pose proof (st_ok_region_nth Ex ss _ 0 r HS ltac:(vm_compute; reflexivity)) as Rv end.
        pose proof (region_ok_chunk SEGS _ _ _ (YP09.mkChunk 0 (CVal 1 (SLit 0))) Rv (or_introl eq_refl)) as Hck.
        cbn [YP09.r_base base_val] in Hck. rewrite !ew_ewset_other in Hck by lia. rewrite EU40 in Hck.
        pose proof (val_of_chunk_ok SEGS _ _ (e_parent e + Z.of_nat di) 0 1 (SLit 0) 0 Hck ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Hval.
        specialize (Hval 0%nat ltac:(cbn; lia)). cbn [ms_mem restrict] in Hval. change (Z.of_nat 0) with 0 in Hval.
        rewrite !Z.add_0_r in Hval. unfold aview. rewrite Hval. reflexivity.
    + intros Hin. apply Hnul. subst p. rewrite <- (firstn_skipn di (e_s e)). apply in_or_app. left. exact Hin.
  - exact HSAc.
  - pose proof Hpdst as HPD. destruct HPD as [(Hfr & _) | [(Hhp & _) | (Hs1 & Hs2 & Hpr & HSP0)]].
    + left. split; [|exact (proj1 (proj2 (proj2 (proj2 HSAc))))].
      destruct Hfr as (cid & pos & Hin & Hc & H1 & H2). exists cid, pos. split; [exact Hin|]. split; [exact Hc|]. lia.
    + right; left. split; [|exact (proj1 (proj2 (proj2 (proj2 HSAc))))].
      destruct Hhp as (b & m & Hin & H1 & H2). exists b, m. split; [exact Hin|]. lia.
    + right; right. split; [rewrite Psp; lia|]. split; [lia|]. split.
      * intros i Hi. exact (apresent_grows _ _ _ _ HG (HPR _ (Hpr i ltac:(lia)))).
      * intros a Ha. rewrite Psp in Ha. destruct (Z_lt_le_dec a (spZ (e_regs e))) as [Hlt | Hge].
        -- exact (HJpres a ltac:(lia)).
        -- exact (apresent_grows _ _ _ a HG (HPR a (HSP0 a ltac:(lia)))). }
assert (HEV0 : st_nev (e_S e) + EV_name_ok <= EV_MAX) by (unfold EV_name_ok; lia).
(* the call of name_ok at 0x89d08 *)
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdc := mdx) end.
eapply SRr_bind.
{ refine (cl_callS B LAWS (e_W e) (ms_regs ms) (ms_mem ms) (Z_to_bv 64 (BASE + AF_name_ok)) STK_reac_declared_vlan_split (spZ (e_regs e)) (e_FP e)
    (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [] (e_ly e) (e_S e) mdc 0 STK_name_ok [] EV_name_ok (-64)
    (getr (ms_regs ms) 1) ch1
    (fun ly' S' W' regs' mem' md' => getr regs' 10 = w64 (seg_spec.b2z (SegModel.name_ok p)) /\
      sa_kept SEGS (e_W e) (ms_mem ms) W' mem' (ms_regs ms) STK_name_ok (fun _ => False) /\ sa_noalloc B (e_ly e) (e_S e) ly' S')
    HJ Psp eq_refl ltac:(lia) ltac:(lia) ltac:(lia) P3 P4 eq_refl HRA HRA4 HCH1 _ _).
  - intros HPRE1. exact (NAMEOK (e_ly e) (e_S e) (e_W e) (ms_regs ms) (ms_mem ms) mdc ch1 (e_parent e) p HPRE1 HROc P10
      ltac:(lia) HNP HEV0).
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & (HN10 & HNK & HNA)).
change (0 + EV_name_ok) with 0 in HJ2.
rewrite P1.
assert (Q2 : forall r, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr regs' (Z_to_bv 5 r))
  by (intros r Hr; rewrite (HP2 r Hr); exact (PR r Hr)).
(* name_ok kept everything outside its window: parent, vid, the frame, the shadow *)
assert (HNW : forall a, ~ (spZ (e_regs e) - STK_reac_declared_vlan_split <= a < spZ (e_regs e)) -> ~ (spZ (ms_regs ms) - STK_name_ok <= a < spZ (ms_regs ms)))
  by (intros a Ha; rewrite Psp; lia).
assert (HSHK2 : forall y, kLowShadowBeg <= y < kHighShadowEnd -> rdW W2 mem2 y = rdW (e_W e) (e_mem e) y).
{ intros y Hy. rewrite (HNK y ltac:(unfold kLowShadowBeg, kHighShadowEnd in Hy; lia) ltac:(apply HNW; unfold kHighShadowEnd in *; lia) (fun x => x)).
  exact (HSHK y Hy). }
apply (HK6 e ly2 S2 W2 regs2 mem2 md2 di v HE HJ2).
- apply (vs_regs_pres e regs' regs2 HR Q2).
- apply (vs_slots_kept (rdW (e_W e) mem')); [exact HSL|]. intros a Ha. unfold e_sp in Ha.
  rewrite (HNK a ltac:(lia) ltac:(rewrite Psp; lia) (fun x => x)).
  exact (UN a ltac:(lia) ltac:(unfold X5; destruct Pplace as [(_ & Hp1) | (Hp1 & _)]; lia)).
- exact Hdi.
- exact Hdi0.
- exact Hne.
- exact Hdig.
- exact Hv.
- exact Hvr.
- change (getr regs2 21) with (getr regs2 (Z_to_bv 5 21)). rewrite (Q2 21 ltac:(unfold acallee_saved; lia)). exact R21.
- exact HN10.
- change (firstn di (e_s e)) with p. destruct (proj1 (proj2 HNP)) as [HZ HZn]. split; [|exact HZn]. intros i Hi.
  rewrite length_app, Hlp in Hi. cbn [length] in Hi.
  rewrite (HNK (e_parent e + Z.of_nat i) ltac:(lia) ltac:(apply HNW; destruct Pplace as [(_ & Hp1) | (Hp1 & _)]; lia) (fun x => x)).
  apply HZ. rewrite length_app, Hlp. cbn [length]. lia.
- exact HNA.
- intros i Hi. apply (apresent_transfer SEGS (w_H (e_W e)) (w_H W2) (ms_mem ms) mem2 (e_vid e + i)).
  + lia.
  + exact (vs_dst_not_img B _ _ _ _ _ _ _ _ _ (e_vid e + i) HAR Hstk Hvdst ltac:(lia)).
  + exact (HNK (e_vid e + i) ltac:(lia) ltac:(apply HNW; destruct Vplace as [(_ & Hv1) | (Hv1 & _)]; lia) (fun x => x)).
  + exact (vs_dst_present B (e_ly e) (e_S e) (e_W e) (e_mem e) (e_regs e) (e_vid e) 2 (e_ly e) (e_S e) (e_W e) (ms_mem ms) mdc
      Hvdst HARm eq_refl eq_refl (Permutation_refl _) (fun _ j Hj Hp => apresent_grows _ _ _ _ HG (HPR _ Hp)) i Hi).
- exact (proj1 (proj2 (proj2 (proj2 (vs_sa_addr_keep _ _ (e_vid e) 2 Hvadd ltac:(lia) HSHK2))))).
- apply (vs_kept_stepW _ _ (e_W e) (ms_mem ms)).
  + apply (vs_kept_stepW _ _ (e_W e) mem').
    * eapply vs_kept_ctxW; [exact HC | cbv beta; intros a Ha; lia].
    * intros a Ha Hw He. exact (UN a Ha ltac:(unfold X5; cbv beta in He; lia)).
  + intros a Ha Hw He. exact (HNK a Ha (HNW a Hw) (fun x => x)).
Qed.
End e.
End f.
End d.
