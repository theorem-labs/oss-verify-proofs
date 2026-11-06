(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/PutStringB_Base.v, with its module paths and module names changed; 374 of its 421 lines of code are new or changed and 1966 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca): stretch SB9_6 of
   segment B9 of reac_segconf_parse_file's walk (lib/B/Prog/pf_seg_B9_d.v): K5 0x88570 -> HREF 0x885ec (cur = NULL)
   or J6 0x88588 (the val spill and strcasecmp(key, "role")). A B9 sub-lane of the image-B G3 walk owner, 2026-10-30.
   proves no function (kind: segment lemma of reac_segconf_parse_file's walk: stretch SB9_6 of segment B9).
   ADAPTED from a working branch's lib/A/Prog/pf_a9_d.v (A9's K5 dispatch: the outside refusal and the first
   compare) and the image-B forms of lib/B/Prog/pf_seg_B9_s1.v (the B9 segment lane: a cut unpacked, an art call by
   aj_art_at, the next cut rebuilt by b9_move0) and pf_seg_B5_r2.v (the B5 segment lane: psrr_branch_pi, paj_run_to_sh),
   re-derived on image B's code (reac_segconf_parse_file.fuzz_segconf.asan-ubsan.s):
     K5    0x88570 beqz a5,0x885e4          a5 = cur (slot 0xc0; b9_cur_ptr_eq0: NULL exactly for cur = None)
     NULL  0x885e4 auipc a0 ; 0x885e8 addi a2,a0,284   a2 = 0x21700 = seg_litA_rc F_outside (listing object 48);
                                            falls into HREF 0x885ec with s7 = kp (the key)
     else  0x88574 sd s3,112(s1)            slot 0x70 := vp (s1 + 0x70 lies in parse_file's stack window)
           0x88578 auipc a0 ; 0x8857c addi a1,a0,488   a1 = 0x21760 = seg_litA_rc S_role (listing object 43)
           0x88580 mv a0,s7                 a0 = kp
           0x88584 jal strcasecmp           the trampoline SS___interceptor_trampoline_strcasecmp; returns to J6
   8 instructions walked: 0x88570 .. 0x88584 (6) and 0x885e4 .. 0x885e8 (2). No inline check, no UBSan trap.
   The proof: a seed at K5 (every register its own atom; slot 0x70 a writable region on s1's atom 9), the branch
   split by psrr_branch_pi on cur (each side refutes the other value of cur by b9_cur_ptr_eq0). cur = None: one run
   to HREF, H_HREF with f = F_outside, args = [AS key] (r_key's outside refusal, pf_seg_B9_f.v b9_rkey_outs). cur =
   Some gi: one run to the call (the store's word read back from the region), strcasecmp by aj_art_at with
   RtSeg.astrcasecmp_realizes (premises from pf_seg_B9_c.v b9_strcasecmp_pre), and INV_JC k = 0 at the return
   state: pf_base by b9_move0 (the writes are slot 0x70 and the callee's window below s1, both b9_Wrx), the strings
   kept (buf lies below alloc_ceiling), slot 0x70 = vp, a0 = 0 exactly when strcasecmp key "role" = 0
   (b9_strcasecmp_iff).
   Section hypotheses: ASTRCASECMP (the strcasecmp carrier at the listing's trampoline), TL (PALib: the errno cell's
   place, which the art step needs), OBJ (the listing's object atoms, for the two literal addresses). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09.
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtSeg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun PaArt.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require reac_segconf_parse.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_pieces pf_seg_B9_d pf_seg_B9_f
  pf_seg_B9_k pf_seg_B9_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------- small tools ---------- *)
Lemma b9s6_den_atom0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
(* a beq branch's condition as the values of its operands *)
Lemma b9s6_br_eq : forall E a b x z t, U E a = x -> U E b = z ->
  branch_taken BC_EQ (sv_denot E a) (sv_denot E b) = t -> (x =? z) = t.
Proof. intros E a b x z t Ha Hb Hc. rewrite branch_eq_U, Ha, Hb in Hc. exact Hc. Qed.
(* pf_seg_B9_s1.v's register and address tools *)
Lemma b9s6_bvr : forall rr (r : bv 5) k v, bv_unsigned r = k -> getr rr (Z_to_bv 5 k) = v -> getr rr r = v.
Proof. intros rr r k v Hr H. subst k. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.
Lemma b9s6_m16 : forall a b, a mod 32 = 0 -> b mod 16 = 0 -> (a - b) mod 16 = 0.
Proof.
intros a b Ha Hb. pose proof (Z.div_mod a 32 ltac:(lia)) as Da. pose proof (Z.div_mod b 16 ltac:(lia)) as Db.
rewrite Ha in Da. rewrite Hb in Db.
replace (a - b) with ((2 * (a / 32) - b / 16) * 16) by lia. apply Z_mod_mult.
Qed.
Lemma b9s6_aview_mod : forall segs H m a, aview segs H m a = aview segs H m (a mod 2 ^ 64).
Proof.
intros segs H m a. unfold aview, mbyte.
replace (Z_to_bv 64 (a mod 2 ^ 64)) with (Z_to_bv 64 a); [reflexivity|].
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N]. rewrite Zmod_mod. reflexivity.
Qed.
Ltac b9s6_in := cbn [In app]; repeat first [left; reflexivity | right].
(* a register of the state after a run, as the executor wrote it (pf_seg_B5_r2.v b5r2_rreg) *)
Ltac b9s6_rreg HS :=
 lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
 lazymatch type of HS with
 | st_ok_pi _ _ ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_pi_restrict_reg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 end end.
Ltac b9s6_clear_md := repeat match goal with |- context [with_vm_backing (m_vm_lazy ?m) ?x ?m] =>
  let mdv := fresh "mdv" in set (mdv := with_vm_backing (m_vm_lazy m) x m) in *; clearbody mdv end.

(* the seed at K5: every register its own atom; slot 0x70 of s1 a writable region on atom 9 (the val spill) *)
Definition b9s6_regions : smem := [YP09.mkRegion (Some 9%nat) 0x70 0x78 0x70 0x78 []].
Definition b9s6_ss : sstate := mkSS B9_K5 sr_atoms b9s6_regions None (mkFacts [] [] []).
(* the registers neither run of the stretch writes (the callee-saved ones and sp, gp, tp) *)
Definition B9S6_KEPT : list Z := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].

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
Hypothesis ASTRCASECMP : forall fx0 : YK11.FPState, @RtSeg.astrcasecmp_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strcasecmp).
Hypothesis TL : PALib B.
Hypothesis OBJ : seg_val_objs (PI := PI).
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let errno_low := pal_env B TL.
Let RUNP := SRr_run_pi_AJ (fx := fx) B LAWS.
Let RUNC := SRr_run_pi_AJ_call (fx := fx) B LAWS.
Let RUNTO := SRr_run_to_pi_AJ (fx := fx) B LAWS.
Let BR := paj_branch (PI := PI).

(* the two literals the code forms: listing objects 48 (.str.13, 0x21700) and 43 (.str.14, 0x21760) *)
Lemma b9s6_lit_outside : forall E, img_env VAL A_LIM E -> ew E 289%nat = w64 (seg_litA_rc F_outside).
Proof.
intros E HE. rewrite (img_env_atomP E 289%nat HE) by (unfold A_TEXT, A_LIM; lia).
change 289%nat with (A_OBJ 48). rewrite (OBJ 48%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)).
unfold w64; f_equal; vm_compute; reflexivity.
Qed.
Lemma b9s6_lit_role : forall E, img_env VAL A_LIM E -> ew E 284%nat = w64 (seg_litA_rc S_role).
Proof.
intros E HE. rewrite (img_env_atomP E 284%nat HE) by (unfold A_TEXT, A_LIM; lia).
change 284%nat with (A_OBJ 43). rewrite (OBJ 43%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)).
unfold w64; f_equal; vm_compute; reflexivity.
Qed.

(* a word read through the ASan view is a 64-bit value *)
Lemma b9s6_rdword_range : forall H mem a w, rdword (aview SEGS H mem) a = Some w -> 0 <= w < 2 ^ 64.
Proof.
intros H mem a w Hw. unfold rdword in Hw.
destruct (aview SEGS H mem a) as [b0|] eqn:E0; [|discriminate].
destruct (aview SEGS H mem (a + 1)) as [b1|] eqn:E1; [|discriminate].
destruct (aview SEGS H mem (a + 2)) as [b2|] eqn:E2; [|discriminate].
destruct (aview SEGS H mem (a + 3)) as [b3|] eqn:E3; [|discriminate].
destruct (aview SEGS H mem (a + 4)) as [b4|] eqn:E4; [|discriminate].
destruct (aview SEGS H mem (a + 5)) as [b5|] eqn:E5; [|discriminate].
destruct (aview SEGS H mem (a + 6)) as [b6|] eqn:E6; [|discriminate].
destruct (aview SEGS H mem (a + 7)) as [b7|] eqn:E7; [|discriminate].
injection Hw as <-.
destruct (aview_byte SEGS H mem _ _ E0) as (_ & _ & _ & R0). destruct (aview_byte SEGS H mem _ _ E1) as (_ & _ & _ & R1).
destruct (aview_byte SEGS H mem _ _ E2) as (_ & _ & _ & R2). destruct (aview_byte SEGS H mem _ _ E3) as (_ & _ & _ & R3).
destruct (aview_byte SEGS H mem _ _ E4) as (_ & _ & _ & R4). destruct (aview_byte SEGS H mem _ _ E5) as (_ & _ & _ & R5).
destruct (aview_byte SEGS H mem _ _ E6) as (_ & _ & _ & R6). destruct (aview_byte SEGS H mem _ _ E7) as (_ & _ & _ & R7).
lia.
Qed.

(* a word a symbolic region holds (pf_seg_B2.v's pb2_word_of_region) *)
Lemma b9s6_word_of_region : forall E H m n b lo hi wlo whi cs od e v,
  region_ok SEGS E (mrestrict H m) (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = b ->
  In (YP09.mkChunk od (CVal 8 e)) cs -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  rdword (aview SEGS H m) (b + od) = Some v.
Proof.
intros E H m n b lo hi wlo whi cs od e v HR Hb Hin He Hv.
pose proof (field_of_region_any (segs := SEGS) E (mrestrict H m) n b cs lo hi wlo whi od 8 e HR Hb Hin
  ltac:(cbn; lia)) as HV.
rewrite He, unsigned_lit_small in HV by lia. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in HV.
rewrite Z.mod_small in HV by lia. change (N.to_nat 8) with 8%nat in HV.
apply rdword_of_val_mem; [exact HV | exact Hv].
Qed.

(** ** Stretch SB9_6: from HREF and J6, the walk reaches B9's goal from K5 *)
Lemma b9_s6 : SB9_6 B.
Proof.
unfold SB9_6, from_K5, from_JC, b9_from.
intros n HHREF FJC x ei kp vp lyc Sc Wc rX memc mdc HI.
destruct x as [v pos cf cur nm o ln d lp].
unfold INV_K5, b9_core, b9_inbuf, B9_R, b9_cp in HI.
change (b9_line (mkB9X v pos cf cur nm o ln d lp)) with (pf_tline (p_s v) o) in HI.
change (b9_key (mkB9X v pos cf cur nm o ln d lp) ei) with (r_trim (firstn ei (pf_tline (p_s v) o))) in HI.
change (b9_val (mkB9X v pos cf cur nm o ln d lp) ei)
  with (r_unquote (r_trim (skipn (S ei) (pf_tline (p_s v) o)))) in HI.
change (b9_buf (mkB9X v pos cf cur nm o ln d lp)) with (pf_F v pos + PF_O_BUF) in HI.
change (b9_k (mkB9X v pos cf cur nm o ln d lp)) with (length (skipn o (p_s v))) in HI.
change (y_v (mkB9X v pos cf cur nm o ln d lp)) with v in HI.
change (y_pos (mkB9X v pos cf cur nm o ln d lp)) with pos in HI.
change (y_o (mkB9X v pos cf cur nm o ln d lp)) with o in HI.
change (y_ln (mkB9X v pos cf cur nm o ln d lp)) with ln in HI.
change (y_d (mkB9X v pos cf cur nm o ln d lp)) with d in HI.
change (y_cf (mkB9X v pos cf cur nm o ln d lp)) with cf in HI.
change (y_cur (mkB9X v pos cf cur nm o ln d lp)) with cur in HI.
change (y_nm (mkB9X v pos cf cur nm o ln d lp)) with nm in HI.
destruct HI as ((HB & HMID & HST & HLEN & HD0 & HDL) & HCH & (HKS & HKI) & (HVS & HVI) & HRG).
set (key := r_trim (firstn ei (pf_tline (p_s v) o))) in *.
set (val := r_unquote (r_trim (skipn (S ei) (pf_tline (p_s v) o)))) in *.
(* the cut's facts *)
pose proof (b9_geo B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (HAR & Hly & Hin & G & HFP & HSP).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof (b9_st_of_base B v pos lyc Sc Wc rX memc mdc HB) as HST0.
pose proof HB as (HCX & HFI & HOBJ & HSL & HFSH).
pose proof HFI as (HJ & _ & _ & _ & _ & _ & _ & HTF & _ & HRG0).
pose proof HCX as (_ & _ & _ & Hc64 & _).
pose proof HTF as (Hc0 & _).
pose proof STK_values as (_ & _ & _ & SPF & _).
pose proof asan_consts as (C1 & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
assert (HC5 : sa_heap B lyc Sc (p_c v) seg_spec.SEG_C_SIZE) by (destruct HOBJ as (_ & _ & _ & _ & H5 & _); exact H5).
pose proof HST as (HRC & HCUR & HNM & HCNT & HC0).
unfold pf_inb, PF_O_BUF in HKI, HVI.
unfold PF_RL, PF_RM in HRG. cbn [app] in HRG.
assert (Hcp0 : 0 < p_c v) by lia.
assert (Hcp : 0 <= pf_cur_ptr (p_c v) cur < 2 ^ 64) by exact (b9s6_rdword_range _ _ _ _ HC0).
assert (Hvp : 0 <= vp < 2 ^ 64) by lia.
assert (HKp0 : 0 <= kp) by lia.
assert (HKp1 : kp + Z.of_nat (length key) < alloc_ceiling) by lia.
assert (HVp1 : vp + Z.of_nat (length val) < alloc_ceiling) by lia.
assert (R9 : getr rX (Z_to_bv 5 9) = w64 (pf_s1 v)) by (apply (b9_rg_get rX _ 9 _ HRG0); b9s6_in).
assert (R15 : getr rX (Z_to_bv 5 15) = w64 (pf_cur_ptr (p_c v) cur)) by (apply (b9_rg_get rX _ 15 _ HRG); b9s6_in).
(* the seed *)
set (E := Eimg (Ereg rX [])).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr rX r)
  by (intros n0 r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HA0 : env_agree 32 (Ereg rX []) E)
  by (subst E; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E9 : ew E 9 = w64 (pf_s1 v)) by (rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl); exact R9).
assert (U9 : bv_unsigned (ew E 9) = pf_s1 v) by (rewrite E9; unfold w64; apply unsigned_lit_small; lia).
assert (E15 : ew E 15 = Z_to_bv 64 (pf_cur_ptr (p_c v) cur))
  by (rewrite (EE 15%nat (Z_to_bv 5 15) eq_refl); exact R15).
assert (HS : st_ok_pi SEGS VAL E b9s6_ss
  (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + B9_K5)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold b9s6_ss. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold b9s6_regions. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o0 Ho0. apply (apresent_writable SEGS). apply Hpres. rewrite SPF. lia.
  - cbn. tauto.
  - split; [exact I | split; exact I]. }
unfold cfg_at. change (w64 (BASE + B9_K5)) with (Z_to_bv 64 (BASE + B9_K5)).
destruct cur as [gi|].
- (* cur = Some gi *)
  psrr_branch_pi RUNP BR HS.
  + (* taken: cur would be NULL *)
    exfalso.
    lazymatch type of Hc with branch_taken BC_EQ (sv_denot _ ?a) (sv_denot _ ?b) = _ =>
      pose proof (b9s6_br_eq E a b _ 0 true ltac:(apply (U_atom E 15 _ E15); lia) ltac:(apply U_lit; lia) Hc) as L0
    end.
    apply Z.eqb_eq in L0.
    pose proof (proj1 (b9_cur_ptr_eq0 (p_c v) cf (Some gi) Hcp0 HCUR) L0) as Hn. discriminate Hn.
  + (* not taken: 0x88574 sd s3,112(s1); 0x88578 auipc; 0x8857c addi a1; 0x88580 mv a0,s7; 0x88584 jal *)
    clear Hc.
    paj_run_shc RUNP RUNC HS HJ.
    { intros a (r & Hr & Ha). vm_compute in Hr. destruct Hr as [<- | []].
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U9 in Ha. left. rewrite SPF. lia. }
    (* the store's word, read back from the region *)
    lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msx) =>
      let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
      pose proof (st_ok_region_nth (segs := SEGS) Ex ssx (restrict (w_H Wc) msx) 0 r0 HS
        ltac:(vm_compute; reflexivity)) as HR0 end.
    cbn [ms_mem restrict] in HR0.
    assert (E19 : sv_denot E (SOff 19 0) = Z_to_bv 64 vp).
    { rewrite b9s6_den_atom0, (EE 19%nat (Z_to_bv 5 19) eq_refl). apply (b9_rg_get rX _ 19 _ HRG); b9s6_in. }
    pose proof (b9s6_word_of_region E (w_H Wc) (ms_mem ms) 9 (pf_s1 v) _ _ _ _ _ 0x70 (SOff 19 0) vp HR0 U9
      ltac:(b9s6_in) E19 Hvp) as S70a.
    clear HR0.
    (* what the run kept: every byte off slot 0x70 *)
    assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (pf_s1 v + 0x70 <= a < pf_s1 v + 0x78) ->
      rdW Wc (ms_mem ms) a = rdW Wc memc a).
    { intros a Ha Hn. lazymatch type of HFr with frame_of ?Ex ?rs _ _ =>
        apply (kept_of_frame (segs := SEGS) Ex rs (w_H Wc) memc (ms_mem ms)
          (fun a => pf_s1 v + 0x70 <= a < pf_s1 v + 0x78) HFr); [|exact Ha | exact Hn] end.
      intros b wlo whi a' Hin' Hrr. vm_compute in Hin'. cbv beta.
      repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite U9 in Hrr; lia |]).
      destruct Hin'. }
    assert (KV1 : forall a, rdW Wc memc a <> None -> rdW Wc (ms_mem ms) a <> None)
      by (intros a Hv; exact (aview_keeps_vis SEGS (w_H Wc) memc (ms_mem ms) a HG Hv)).
    clear HFr HG HF.
    set (mdv := with_vm_backing _ _ _) in *; clearbody mdv.
    (* the registers at the call *)
    pose proof (regs_kept_of_st_ok SEGS _ _ _ rX [] (map (Z_to_bv 5) B9S6_KEPT) HS HA0 ltac:(vm_compute; reflexivity))
      as HK.
    cbn [ms_regs restrict] in HK.
    assert (Rz : forall k z, In k B9S6_KEPT -> getr rX (Z_to_bv 5 k) = w64 z -> getr (ms_regs ms) (Z_to_bv 5 k) = w64 z).
    { intros k z Hk Hz. rewrite (HK (Z_to_bv 5 k)); [exact Hz | apply in_map; exact Hk]. }
    prreg HS (1%bv : bv 5) R1. prreg HS (10%bv : bv 5) R10. prreg HS (11%bv : bv 5) R11.
    pmkst HS.
    assert (R2 : getr (ms_regs ms) 2 = w64 (pf_s1 v)).
    { apply (b9s6_bvr _ 2%bv 2); [reflexivity|]. apply Rz; [b9s6_in|]. exact (b9_rg_get rX _ 2 _ HRG0 ltac:(b9s6_in)). }
    assert (R3 : getr (ms_regs ms) 3 = w64 (as_gp B)).
    { apply (b9s6_bvr _ 3%bv 3); [reflexivity|]. apply Rz; [b9s6_in|]. exact (b9_rg_get rX _ 3 _ HRG0 ltac:(b9s6_in)). }
    assert (R4 : getr (ms_regs ms) 4 = w64 (as_tp B)).
    { apply (b9s6_bvr _ 4%bv 4); [reflexivity|]. apply Rz; [b9s6_in|]. exact (b9_rg_get rX _ 4 _ HRG0 ltac:(b9s6_in)). }
    assert (R23 : getr rX 23 = w64 kp).
    { apply (b9s6_bvr _ 23%bv 23); [reflexivity|]. apply (b9_rg_get rX _ 23 _ HRG); b9s6_in. }
    assert (Hsp : spZ (ms_regs ms) = pf_sp0 v + (pf_s1 v - pf_sp0 v)).
    { unfold spZ. rewrite R2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
    assert (Ho16 : (pf_s1 v - pf_sp0 v) mod 16 = 0) by (apply b9s6_m16; [exact G5 | exact G3]).
    assert (HraT : YK0s.ret_ok (getr (ms_regs ms) 1)) by (rewrite R1; apply ret_ok_codeptr_v; [lia | reflexivity]).
    assert (R10' : getr (ms_regs ms) 10 = w64 kp) by (rewrite R10, (EE 23%nat 23%bv eq_refl); exact R23).
    assert (R11' : getr (ms_regs ms) 11 = w64 (seg_litA_rc S_role)) by (rewrite R11; exact (b9s6_lit_role E HEI)).
    (* the cut's state at the call: b9_st after the store (a write inside [s1 + 0x70, s1 + 0x78)) *)
    pose proof (b9_keep_art B v pos lyc Sc Wc memc mdc (ms_mem ms) mdv (pf_s1 v - pf_sp0 v + 0x78) 8 HST0 HJ
      ltac:(rewrite SPF; lia)
      (fun a Ha Hn _ => K1 a Ha ltac:(intros Hs; apply Hn; lia))) as HST1.
    assert (HKS1 : sa_str (rdW Wc (ms_mem ms)) kp key).
    { apply (reac_segconf_parse.sa_str_low _ _ _ _ HKS HKp0 HKp1). intros a Ha. apply K1; lia. }
    destruct (b9_strcasecmp_pre B v pos lyc Sc Wc (ms_mem ms) mdv (ms_regs ms) kp key S_role HST1
      ltac:(rewrite Hsp; lia) HraT R3 R4 ltac:(b9s6_in) R10' R11' HKS1 ltac:(unfold pf_inb, PF_O_BUF; lia))
      as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14).
    (* the call *)
    eapply SRr_bind.
    { eapply (aj_art_at SEGS B LAWS pa_segs_low errno_low (2 * ESTACK) (fun _ => False)
        (SIG SS___interceptor_trampoline_strcasecmp) Wc (ms_regs ms) (ms_mem ms) STK_reac_segconf_parse_file
        (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc mdv 0
        (pf_s1 v - pf_sp0 v) (Z_to_bv 64 (BASE + B9_J6)) _ HJ Hsp Ho16 ltac:(lia) ltac:(unfold ESTACK; lia)
        ltac:(rewrite SPF; unfold ESTACK; lia) ltac:(rewrite R1; reflexivity) (fun a (H : False) => False_ind _ H)).
      exact (ASTRCASECMP fx lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv kp (seg_litA_rc S_role) (seg_spec.zb key)
        (seg_spec.zb S_role) P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14). }
    cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HQ & HK2).
    change (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + B9_J6)) mem2 (seg_rom SEGS)) md2)
      with (cfg_at SEGS (BASE + B9_JC 0) regs2 mem2 md2).
    apply (FJC (mkB9X v pos cf (Some gi) nm o ln d lp) ei kp vp gi lyc Sc Wc regs2 mem2 md2).
    (* the memory after the call: the store's off strcasecmp's window [s1 - 2 * ESTACK, s1) *)
    assert (KM2 : forall a, 0 <= a < 2 ^ 64 -> ~ (pf_s1 v - 2 * ESTACK <= a < pf_s1 v) ->
      rdW Wc mem2 a = rdW Wc (ms_mem ms) a).
    { intros a Ha Hn. apply HK2; [exact Ha | lia | tauto]. }
    assert (KW : forall a, 0 <= a < 2 ^ 64 -> ~ b9_Wrx v pos true a -> rdW Wc mem2 a = rdW Wc memc a).
    { intros a Ha Hw. rewrite KM2; [|exact Ha |].
      - apply K1; [exact Ha|]. intros Hs. apply Hw. right. left. split; [reflexivity | exact Hs].
      - intros Hn. apply Hw. left. rewrite SPF in G1 |- *. unfold ESTACK in Hn. lia. }
    assert (KV : forall a, rdW Wc memc a <> None -> rdW Wc mem2 a <> None).
    { intros a0 Hv0. apply KV1 in Hv0. rewrite b9s6_aview_mod in Hv0 |- *.
      pose proof (Z.mod_pos_bound a0 (2 ^ 64) ltac:(lia)) as Ha.
      remember (a0 mod 2 ^ 64) as a eqn:Ea. clear Ea. rename Hv0 into Hv.
      destruct (Z_lt_le_dec a (pf_s1 v - 2 * ESTACK)) as [Hlo | Hlo];
        [|destruct (Z_lt_le_dec a (pf_s1 v)) as [Hhi | Hhi]].
      - rewrite KM2; [exact Hv | exact Ha | lia].
      - pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
        apply (aview_some_of_apresent SEGS). apply Hpres2. rewrite SPF in *. unfold ESTACK in Hlo. lia.
      - rewrite KM2; [exact Hv | exact Ha | lia]. }
    assert (Hpre : forall k z, In k B9S6_KEPT -> getr rX (Z_to_bv 5 k) = w64 z -> getr regs2 (Z_to_bv 5 k) = w64 z).
    { intros k z Hk Hz. rewrite (HP2 k); [exact (Rz k z Hk Hz)|].
      unfold B9S6_KEPT in Hk. cbn [In] in Hk. unfold acallee_saved.
      repeat (destruct Hk as [<- | Hk]; [lia |]). destruct Hk. }
    assert (HFI2 : pf_rg regs2 (b9_FI B v)).
    { unfold b9_FI, pf_rg. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
        (apply Hpre; [b9s6_in | apply (b9_rg_get rX _ _ _ HRG0); b9s6_in]). }
    assert (HB2 : pf_base B v pos lyc Sc Wc regs2 mem2 md2 PF_SC_LINE).
    { eapply (b9_move0 B v pos lyc Sc Wc rX memc mdc PF_SC_LINE Sc Wc regs2 mem2 md2 PF_SC_LINE HB HJ2);
        [exists (st_fs Sc); destruct Sc; reflexivity | apply Permutation_refl | exact KW | exact KV | exact HFI2 |].
      eapply b9_keep_fsh; [exact G | exact KW | exact HFSH]. }
    unfold INV_JC, b9_core, b9_inbuf, B9_R.
    change (b9_line (mkB9X v pos cf (Some gi) nm o ln d lp)) with (pf_tline (p_s v) o).
    change (b9_key (mkB9X v pos cf (Some gi) nm o ln d lp) ei) with key.
    change (b9_val (mkB9X v pos cf (Some gi) nm o ln d lp) ei) with val.
    change (b9_buf (mkB9X v pos cf (Some gi) nm o ln d lp)) with (pf_F v pos + PF_O_BUF).
    change (b9_k (mkB9X v pos cf (Some gi) nm o ln d lp)) with (length (skipn o (p_s v))).
    change (y_v (mkB9X v pos cf (Some gi) nm o ln d lp)) with v.
    change (y_pos (mkB9X v pos cf (Some gi) nm o ln d lp)) with pos.
    change (y_o (mkB9X v pos cf (Some gi) nm o ln d lp)) with o.
    change (y_ln (mkB9X v pos cf (Some gi) nm o ln d lp)) with ln.
    change (y_d (mkB9X v pos cf (Some gi) nm o ln d lp)) with d.
    change (y_cf (mkB9X v pos cf (Some gi) nm o ln d lp)) with cf.
    change (y_cur (mkB9X v pos cf (Some gi) nm o ln d lp)) with (Some gi).
    change (y_nm (mkB9X v pos cf (Some gi) nm o ln d lp)) with nm.
    split; [|split; [reflexivity | split; [exact HCH | split; [|split; [|split; [|split; [|split]]]]]]].
    * (* b9_core *)
      split; [exact HB2|]. split; [exact HMID|].
      split; [eapply (b9_keep_st B v pos lyc Sc Wc memc mdc (rdW Wc mem2));
              first [exact G | exact HAR | exact Hin | exact Hly | exact KW | exact KV | exact HC5 | exact HST]|].
      split; [exact HLEN|]. split; [exact HD0 | exact HDL].
    * (* the key, kept *)
      split; [|unfold pf_inb, PF_O_BUF; lia].
      apply (reac_segconf_parse.sa_str_low _ _ _ _ HKS HKp0 HKp1).
      intros a Ha. rewrite KM2 by (unfold ESTACK; lia). apply K1; lia.
    * (* the value, kept *)
      split; [|unfold pf_inb, PF_O_BUF; lia].
      apply (reac_segconf_parse.sa_str_low _ _ _ _ HVS ltac:(lia) HVp1).
      intros a Ha. rewrite KM2 by (unfold ESTACK; lia). apply K1; lia.
    * (* slot 0x70 = vp *)
      unfold pf_sl. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd].
      rewrite (b9_rdword_keep (rdW Wc (ms_mem ms)) (rdW Wc mem2) (pf_s1 v + 0x70)); [exact S70a|].
      intros k Hk. apply KM2; unfold ESTACK; lia.
    * intros j Hj. lia.
    * (* a0 = 0 exactly when the key is "role" under case folding *)
      destruct (b9_astr_of_sa Wc (ms_mem ms) kp key HKS1) as (_ & _ & _ & HZS & _).
      assert (ZR : seg_spec.zs (seg_spec.zb S_role) = S_role) by (vm_compute; reflexivity).
      assert (NZK : ~ In 0 key) by (destruct HKS as ((_ & HNZ) & _); exact HNZ).
      assert (NZR : ~ In 0 S_role) by (vm_compute; intuition discriminate).
      change (map (fun b : byte => bv_unsigned b) (seg_spec.zb key)) with (seg_spec.zs (seg_spec.zb key)) in HQ.
      change (map (fun b : byte => bv_unsigned b) (seg_spec.zb S_role))
        with (seg_spec.zs (seg_spec.zb S_role)) in HQ.
      rewrite HZS, ZR in HQ.
      exact (iff_trans HQ (b9_strcasecmp_iff key S_role NZK NZR)).
    * (* the registers: B9_R and s7 kept *)
      unfold PF_RL, PF_RM, pf_rg. cbn [app].
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
        (apply Hpre; [b9s6_in | apply (b9_rg_get rX _ _ _ HRG); b9s6_in]).
- (* cur = None *)
  psrr_branch_pi RUNP BR HS.
  + (* taken: 0x885e4 auipc a0; 0x885e8 addi a2,a0,284; falls into HREF *)
    clear Hc.
    change (b9_goal B (mkB9X v pos cf None nm o ln d lp))
      with (pf_postm B v (r_key cf None nm (ln + 1) (pf_tline (p_s v) o)) o ln).
    rewrite (b9_rkey_outs cf nm (ln + 1) (pf_tline (p_s v) o) ei HCH).
    paj_run_to_sh RUNTO HS HJ PF_HREF.
    { intros a (r & Hr & Ha). vm_compute in Hr. destruct Hr as [<- | []].
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U9 in Ha. left. rewrite SPF. lia. }
    cbn [ms_mem mkst] in HFr, HG, HF.
    b9s6_clear_md.
    assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (pf_s1 v + 0x70 <= a < pf_s1 v + 0x78) ->
      rdW Wc (ms_mem ms) a = rdW Wc memc a).
    { intros a Ha Hn. lazymatch type of HFr with frame_of ?Ex ?rs _ _ =>
        apply (kept_of_frame (segs := SEGS) Ex rs (w_H Wc) memc (ms_mem ms)
          (fun a => pf_s1 v + 0x70 <= a < pf_s1 v + 0x78) HFr); [|exact Ha | exact Hn] end.
      intros b wlo whi a' Hin' Hrr. vm_compute in Hin'. cbv beta.
      repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite U9 in Hrr; lia |]).
      destruct Hin'. }
    assert (KV : forall a, rdW Wc memc a <> None -> rdW Wc (ms_mem ms) a <> None)
      by (intros a Hv; exact (aview_keeps_vis SEGS (w_H Wc) memc (ms_mem ms) a HG Hv)).
    clear HFr HG HF.
    assert (KW : forall a, 0 <= a < 2 ^ 64 -> ~ b9_Wrx v pos true a -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
    { intros a Ha Hw. apply K1; [exact Ha|]. intros Hs. apply Hw. right. left. split; [reflexivity | exact Hs]. }
    (* the registers at HREF *)
    assert (QK : forall r, In r B9S6_KEPT -> getr (ms_regs ms) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
    { intros r Hr. unfold B9S6_KEPT in Hr. cbn [In] in Hr.
      repeat (destruct Hr as [<- | Hr]; [b9s6_rreg HS; rewrite b9s6_den_atom0; apply EE; reflexivity |]).
      destruct Hr. }
    assert (Q12 : getr (ms_regs ms) (Z_to_bv 5 12) = w64 (seg_litA_rc F_outside)).
    { b9s6_rreg HS. rewrite b9s6_den_atom0. exact (b9s6_lit_outside E HEI). }
    pmkst HS.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?k)) ?mm ?rom) ?mdx) _ =>
      change (mkCfg (mkst rg (Z_to_bv 64 (BASE + k)) mm rom) mdx) with (cfg_at SEGS (BASE + PF_HREF) rg mm mdx) end.
    apply (HHREF v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv cf nm o ln d F_outside (seg_litA_rc F_outside)
      [AS key] kp).
    assert (HST2 : pf_st v pos (rdW Wc (ms_mem ms)) cf None nm (length (skipn o (p_s v)))).
    { eapply (b9_keep_st B v pos lyc Sc Wc memc mdc (rdW Wc (ms_mem ms)));
        first [exact G | exact HAR | exact Hin | exact Hly | exact KW | exact KV | exact HC5 | exact HST]. }
    split; [|split; [exact HMID | split; [|split]]].
    * eapply (b9_move0 B v pos lyc Sc Wc rX memc mdc PF_SC_LINE Sc Wc (ms_regs ms) (ms_mem ms) mdv PF_SC_LINE HB HJ);
        [exists (st_fs Sc); destruct Sc; reflexivity | apply Permutation_refl | exact KW | exact KV | |].
      -- unfold pf_rg, b9_FI. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
           (rewrite QK; [apply (b9_rg_get rX _ _ _ HRG0); b9s6_in | unfold B9S6_KEPT; b9s6_in]).
      -- eapply b9_keep_fsh; [exact G | exact KW | exact HFSH].
    * destruct HST2 as (A1 & _ & A3 & A4 & _). exact (conj A1 (conj A3 A4)).
    * split; [right; right; reflexivity|]. split; [reflexivity|].
      exists key. split; [reflexivity|]. split; [|unfold pf_inb, PF_O_BUF; lia].
      apply (reac_segconf_parse.sa_str_low _ _ _ _ HKS HKp0 HKp1).
      intros a Ha. apply K1; lia.
    * unfold pf_rg. rewrite !Forall_app. split; [|split].
      -- unfold PF_RL. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
           (rewrite QK; [apply (b9_rg_get rX _ _ _ HRG); b9s6_in | unfold B9S6_KEPT; b9s6_in]).
      -- unfold PF_RM. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
           (rewrite QK; [apply (b9_rg_get rX _ _ _ HRG); b9s6_in | unfold B9S6_KEPT; b9s6_in]).
      -- repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd].
         ++ exact Q12.
         ++ rewrite QK; [apply (b9_rg_get rX _ _ _ HRG); b9s6_in | unfold B9S6_KEPT; b9s6_in].
  + (* not taken: cur would not be NULL *)
    exfalso.
    lazymatch type of Hc with branch_taken BC_EQ (sv_denot _ ?a) (sv_denot _ ?b) = _ =>
      pose proof (b9s6_br_eq E a b _ 0 false ltac:(apply (U_atom E 15 _ E15); lia) ltac:(apply U_lit; lia) Hc) as L0
    end.
    cbn [pf_cur_ptr Z.eqb] in L0. discriminate L0.
Qed.

End e.
End f.
End d.
