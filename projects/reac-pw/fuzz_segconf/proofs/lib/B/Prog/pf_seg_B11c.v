(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca): segment B11c of
   reac_segconf_parse_file's walk (0x87e38, 1328 instructions; reac_segconf.c:264, 267, 271, the bad-model refusal
   and the scope ends of the model branch), S_B11c_holds : S_B11c B (lib/B/Prog/pf_pieces.v), Qed. The B11c segment lane
   of the image-B G3 walk owner, 2026-10-30. proves no function (kind: segment of reac_segconf_parse_file's walk).
   ADAPTED from the image-A G3 walk owner's image-A lane of segment A11b (commit 95f85b0d718c, its
   statements pf_a11b_d.v / facts pf_a11b_f.v; B11c is A11b's second half, A's KEXIT 0x886c8 .. TAIL), with the
   piece form of A10b's join (a working branch's pf_a10b_j.v), A5's transport (a working branch's
   pf_a5_k.v), A7's refuse site rule (a working branch's pf_a7_s.v) and image B's parse walk's call rule
   use (lib/B/Prog/reac_segconf_parse.v); the UBSan piece walks (working branches) carry
   no trap in this stretch (U's refusal tail has none either). Re-derived on image B's machine code.
   THE B CUT PLAN (PLAN-pf-asanubsan.md section 5.2 row B11c; pfm.md):
     entries KREFM 0x88bd0 (from B11b's `bgeu s3,a1` 0x88bb8) and LOWOUT 0x88c70 (from B11a's `j` 0x88a44; B11c
     falls into it from 0x88c6c); exit TAIL 0x88600 (`j` 0x88c7c). Range 0x88bd0-0x88c80, 44 instructions:
     0x88bd0 auipc a0 / 0x88bd4 addi a2 = 0x21880 (F_badmodel, .str.20, listing object 65); 0x88bd8 ld a0,200(s1)
     (c); 0x88bdc mv a1,s6 (lineno); 0x88be0 ld a3,64(s1) (cur_name F + 0x20); 0x88be4 ld a4,112(s1) (val);
     0x88be8 ld a5,120(s1) (known F + 0x320); 0x88bec jal refuse (0x892f8, return 0x88bf0 = BASE + 0x3e30);
     0x88bf0 li a0,-8; 0x88bf4 .. 0x88c6c 31 shadow stores (known 0x64-0x81, ntok 0x8a out of scope);
     0x88c70 .. 0x88c78 3 shadow stores (model low 0x5c-0x5e out); 0x88c7c j TAIL.
     Inline checks: none. UBSan trap branches: none (0 of the function's 34). Calls: refuse (STK_refuse 12464 at
     sp = s1; STK_reac_segconf_parse_file 12832 = 352 + 16 + 12464 covers it).
   THE PROOF, in four pieces (one file each), and this file's composition:
     pf_seg_B11c_l.v  b11_lowout_ok   LOWOUT 0x88c70 -> TAIL (HA_TAIL n -> H_LOWOUT n)
     pf_seg_B11c_o.v  b11_kout_ok     KOUT 0x88bf0 -> LOWOUT (walk-internal cut after the refusal)
     pf_seg_B11c_r.v  b11_refuse_site the call site gives refuse_contract's premises (INV_KCALL)
     pf_seg_B11c_c.v  b11_after_refuse  refuse's post and journals give INV_KOUT at the FP state refuse returned
     here             b11_krefm        KREFM 0x88bd0 -> the six loads -> the call (PaFx.cl_callSF) -> KOUT
   SECTION HYPOTHESES (pf_pieces.v's head comment: each segment file takes the program callees of its calls and the
   listing / record facts): REF (refuse_contract at BASE + AF_refuse, STK_refuse, RLO_A, RHI_A, seg_litA_rc, gotwA,
   guardA, at every FP state); SIGP, OBJ, VRO (B's SegObj.v listing facts over the walk's abstract PAImg instance,
   as lib/B/Prog/reac_segconf_parse.v takes them); SSPX (the stack-protector cells at every AR state, as
   lib/B/Prog/reac_segconf_parse.v takes it).
   POSITIONAL NAMES checked against image B's own tables: listing object 65 = 0x21880 (B SegAddr seg_objs index 65,
   F_badmodel's literal, SegInstB's table row .str.20; b11_lit_atom checks it by computation); the call target
   SS_refuse (B SegAddr 0x892f8); PF_KOUT = AF + 0xdb8 (pf_kout_pc checks 0x88bf0). No region letter or STK row of
   an A table is used. *)
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
PaCallRun PaArt PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_pieces pf_seg_B11c_k pf_seg_B11c_l
  pf_seg_B11c_o pf_seg_B11c_r pf_seg_B11c_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the register read of a state stopped at a call (st_ok, not st_ok_pi) *)
Ltac b11_rreg_ok HS :=
 lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
 lazymatch type of HS with
 | st_ok ?segs ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_restrict_reg segs Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 end end.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
(* refuse's contract at image B's entry and window (pf_pieces.v's call table), at every FP state *)
Hypothesis REF : forall fx0 : YK11.FPState, refuse_contract (fx := fx0) SEGS B (BASE + AF_refuse) STK_refuse
  RLO_A RHI_A seg_litA_rc gotwA guardA.
(* the listing's facts over the walk's abstract instance (B's SegObj.v; the pinned instance gives each by
   computation): call targets, object atoms, the read-only range *)
Hypothesis SIGP : seg_sig_prog (PI := PI).
Hypothesis OBJ : seg_val_objs (PI := PI).
Hypothesis VRO : seg_val_relro (PI := PI).
(* SSPX (the image-A G3 walk owner's hypothesis of the same name, at image B's cells): the stack-protector cells at every AR
   state, which the allocator record pins (lib/B/Prog/reac_segconf_parse.v takes the same) *)
Hypothesis SSPX : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) gotwA guardA.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(* F_badmodel's literal: listing object 65 is .str.20 (0x21880) on image B *)
Lemma b11_lit_atom : forall E, img_env VAL A_LIM E -> ew E 306%nat = w64 (seg_litA_rc F_badmodel).
Proof.
intros E HE. rewrite (img_env_atomP E 306%nat HE) by (unfold A_TEXT, A_LIM; lia).
change 306%nat with (A_OBJ 65). rewrite (OBJ 65%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)).
unfold w64; f_equal; vm_compute; reflexivity.
Qed.

Section x. Context {fx : YK11.FPState}.

(* ---------- the seed at KREFM (0x88bd0) ---------- *)
(* every register its own atom; atoms 32 .. 35 the four slot values the loads read (c, cur_name, val, known), on a
   read-only region at s1 *)
Definition b11K_E (rX : bvmap 5 word) (v : pfv) (pos vp : Z) : env :=
  Eimg (Ereg rX [w64 (p_c v); w64 (pf_F v pos + PF_O_CN); w64 vp; w64 (pf_F v pos + PF_O_KNOWN)]).
Definition b11K_regions : smem :=
  [YP09.mkRegion (Some 9%nat) 0x40 0xd0 0 0
     [YP09.mkChunk 0x40 (CVal 8 (SOff 33 0)); YP09.mkChunk 0x70 (CVal 8 (SOff 34 0));
      YP09.mkChunk 0x78 (CVal 8 (SOff 35 0)); YP09.mkChunk 0xc8 (CVal 8 (SOff 32 0))]].
Definition b11K_ss : sstate := mkSS PF_KREFM sr_atoms b11K_regions None (mkFacts [] [] []).
Lemma b11K_atoms : forall rX v pos vp,
  ew (b11K_E rX v pos vp) 32 = w64 (p_c v) /\ ew (b11K_E rX v pos vp) 33 = w64 (pf_F v pos + PF_O_CN) /\
  ew (b11K_E rX v pos vp) 34 = w64 vp /\ ew (b11K_E rX v pos vp) 35 = w64 (pf_F v pos + PF_O_KNOWN).
Proof.
intros rX v pos vp. unfold b11K_E.
rewrite !Eimg_low by (unfold A_TEXT; lia).
split; [exact (ew_Ereg_extra rX _ 0)|]. split; [exact (ew_Ereg_extra rX _ 1)|].
split; [exact (ew_Ereg_extra rX _ 2) | exact (ew_Ereg_extra rX _ 3)].
Qed.
Lemma b11K_seed : forall v pos (Wc : world SEGS) (rX : bvmap 5 word) memc vp,
  b11_geoP v pos -> 0 <= p_c v < 2 ^ 64 -> 0 <= vp < 2 ^ 64 ->
  getr rX (Z_to_bv 5 9) = w64 (pf_s1 v) ->
  pf_sl (rdW Wc memc) (pf_s1 v)
    [(0x40, pf_F v pos + PF_O_CN); (0x70, vp); (0x78, pf_F v pos + PF_O_KNOWN); (0xc8, p_c v)] ->
  st_ok_pi SEGS VAL (b11K_E rX v pos vp) b11K_ss
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + PF_KREFM)) memc (seg_rom SEGS))).
Proof.
intros v pos Wc rX memc vp HG Hc Hv R9 HSL.
pose proof HG as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _).
pose proof asan_consts as (C1 & _).
destruct (b11K_atoms rX v pos vp) as (E32 & E33 & E34 & E35).
set (E := b11K_E rX v pos vp) in *.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr rX r)
  by (intros n r Hn; subst E; unfold b11K_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U9 : bv_unsigned (ew E 9) = pf_s1 v)
  by (rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
unfold pf_sl in HSL.
pose proof (Forall_inv HSL) as W40. apply Forall_inv_tail in HSL.
pose proof (Forall_inv HSL) as W70. apply Forall_inv_tail in HSL.
pose proof (Forall_inv HSL) as W78. apply Forall_inv_tail in HSL.
pose proof (Forall_inv HSL) as WC8.
cbn [fst snd] in W40, W70, W78, WC8.
rewrite restrict_mkst_fx. unfold b11K_ss. apply pa_entry_st_ok_full.
- subst E. unfold b11K_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold b11K_regions. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  repeat apply Forall_cons; try apply Forall_nil.
  + apply (chunk_ok_val SEGS E _ (pf_s1 v) 0x40 8 (SOff 33 0) (pf_F v pos + PF_O_CN)).
    * cbn [sv_denot]. rewrite E33, b11_w64_u by (unfold PF_O_CN; lia). rewrite Z.add_0_r. reflexivity.
    * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). unfold PF_O_CN. lia.
    * cbn. lia.
    * exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ W40).
  + apply (chunk_ok_val SEGS E _ (pf_s1 v) 0x70 8 (SOff 34 0) vp).
    * cbn [sv_denot]. rewrite E34, b11_w64_u by lia. rewrite Z.add_0_r. reflexivity.
    * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
    * cbn. lia.
    * exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ W70).
  + apply (chunk_ok_val SEGS E _ (pf_s1 v) 0x78 8 (SOff 35 0) (pf_F v pos + PF_O_KNOWN)).
    * cbn [sv_denot]. rewrite E35, b11_w64_u by (unfold PF_O_KNOWN; lia). rewrite Z.add_0_r. reflexivity.
    * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). unfold PF_O_KNOWN. lia.
    * cbn. lia.
    * exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ W78).
  + apply (chunk_ok_val SEGS E _ (pf_s1 v) 0xc8 8 (SOff 32 0) (p_c v)).
    * cbn [sv_denot]. rewrite E32, b11_w64_u by lia. rewrite Z.add_0_r. reflexivity.
    * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
    * cbn. lia.
    * exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ WC8).
- cbn. tauto.
- unfold facts_ok; cbn; repeat split; first [exact I | apply Forall_nil | constructor].
Qed.

(* every byte refuse writes is in parse_file's footprint (the second range, c->refusal .. c->overflow) *)
Lemma b11_rw_pw : forall c rcs a, inFP (refuse_W c rcs) a -> inFP (seg_spec.RC_PARSE_W c) a.
Proof.
intros c rcs a (r & Hr & Ha). exists (c + seg_spec.RC_REFUSAL, c + seg_spec.RC_OVERFLOW + 4).
split; [unfold seg_spec.RC_PARSE_W; right; left; reflexivity|]. cbn [fst snd].
unfold refuse_W in Hr. apply in_app_or in Hr as [Hr|Hr].
- destruct Hr as [<- | []]. cbn [fst snd] in Ha. unfold seg_spec.RC_REFUSED, seg_spec.RC_REFUSAL, seg_spec.RC_OVERFLOW in *. lia.
- revert Hr. destruct (length (rc_refusal rcs) <? 8)%nat eqn:E; intros Hr; [|destruct Hr].
  apply Nat.ltb_lt in E.
  destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Ha;
    unfold seg_spec.refusal_addr, seg_spec.RC_REFUSAL, seg_spec.RC_REFUSAL_LEN, seg_spec.RC_NREF,
      seg_spec.RC_OVERFLOW in *; lia.
Qed.

(* ---------- the piece: KREFM -> the call -> KOUT ---------- *)
Lemma b11_krefm : forall n, HA_KOUT B n -> H_KREFM (fx := fx) B n.
Proof.
intros n KOUT v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val HI.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
destruct HI as (HBASE0 & HMID & HST & HVS & HVI & HKS & HSL70 & HRG).
destruct HBASE0 as (HCX & HFI & HOBJ & HSL & HFSH).
destruct (b11_geo B v pos lyc Sc Wc rX memc mdc HCX HFI) as (HGEO & Hin & EF & Hfrs & HAR).
pose proof HGEO as (S1 & SG2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _).
destruct (b11_SHb v pos HGEO) as (ESH & SH1 & SH2 & F8 & _).
pose proof HFI as (HJ & Hly & HSc & HPERM & HSAV & HFLAG & HFRM & HTF & HSLC & HRG0).
pose proof HCX as (_ & _ & _ & HcB & _ & _ & _ & _ & _ & _ & _).
pose proof asan_consts as (C1 & _).
pose proof STK_values as (_ & SREF & _ & SPF & _).
destruct HVI as [HV1 HV2].
unfold PF_RL, PF_RM in HRG.
assert (R9 : getr rX (Z_to_bv 5 9) = w64 (pf_s1 v)) by (apply (b11_rg rX _ 9 _ HRG0); b11_in).
assert (Hvp : 0 <= vp < 2 ^ 64) by (unfold PF_O_BUF in HV1, HV2; lia).
assert (HSL4 : pf_sl (rdW Wc memc) (pf_s1 v)
  [(0x40, pf_F v pos + PF_O_CN); (0x70, vp); (0x78, pf_F v pos + PF_O_KNOWN); (0xc8, p_c v)]).
{ unfold pf_sl in *. repeat apply Forall_cons; try apply Forall_nil.
  - exact (proj1 (Forall_forall _ _) HSL (0x40, pf_F v pos + PF_O_CN) ltac:(unfold PF_SL; b11_in)).
  - exact (Forall_inv HSL70).
  - exact (proj1 (Forall_forall _ _) HSL (0x78, pf_F v pos + PF_O_KNOWN) ltac:(unfold PF_SL; b11_in)).
  - exact (Forall_inv HSLC). }
pose proof (b11K_seed v pos Wc rX memc vp HGEO HcB Hvp R9 HSL4) as HS.
destruct (b11K_atoms rX v pos vp) as (E32 & E33 & E34 & E35).
set (E := b11K_E rX v pos vp) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold b11K_E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr rX r)
  by (intros n0 r Hn; subst E; unfold b11K_E; apply ew_Eimg_Ereg_nat; exact Hn).
unfold cfg_at. change (w64 (BASE + PF_KREFM)) with (Z_to_bv 64 (BASE + PF_KREFM)).
(* 0x88bd0 .. 0x88bec: a2 = F_badmodel, the five loads / moves, the call *)
paj_run_shc (SRr_run_pi_AJ (fx := fx) B LAWS) (SRr_run_pi_AJ_call (fx := fx) B LAWS) HS HJ.
{ intros a (r & Hr & Ha). unfold b11K_ss, b11K_regions in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | []]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. lia. }
b11_clear_md.
(* the run wrote nothing *)
assert (K0 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha. apply (kept_of_frame (segs:=SEGS) E (ss_mem b11K_ss) (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr);
    [|exact Ha | intros []].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'. cbv beta.
  destruct Hin' as [Hq | []]. injection Hq as <- <- <-. cbn [base_val] in Hrr. lia. }
assert (M1 : forall a, rdW Wc memc a <> None -> rdW Wc (ms_mem ms) a <> None)
  by (intros a Hv; exact (aview_keeps_vis SEGS (w_H Wc) memc (ms_mem ms) a HG Hv)).
assert (KP0 : b11_kept v pos (rdW Wc memc) (rdW Wc (ms_mem ms))).
{ split; [intros a Ha _; exact (K0 a Ha) | intros a _ Hv; exact (M1 a Hv)]. }
(* the registers at the call *)
prreg HS (1%bv : bv 5) Q1.
assert (QK : forall r, In r [2; 3; 4; 8; 9; 20; 18; 21; 26; 25; 22] ->
    getr (ms_regs ms) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
{ intros r Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [b11_rreg_ok HS; rewrite b11_den_atom0; apply EE; reflexivity |]). destruct Hr. }
assert (Q10 : getr (ms_regs ms) (Z_to_bv 5 10) = w64 (p_c v)) by (b11_rreg_ok HS; rewrite b11_den_atom0; exact E32).
assert (Q11 : getr (ms_regs ms) (Z_to_bv 5 11) = w64 (ln + 1)).
{ b11_rreg_ok HS; rewrite b11_den_atom0. rewrite (EE 22%nat (Z_to_bv 5 22) eq_refl).
  apply (b11_rg rX _ 22 _ HRG). b11_in. }
assert (Q12 : getr (ms_regs ms) (Z_to_bv 5 12) = w64 (seg_litA_rc F_badmodel))
  by (b11_rreg_ok HS; rewrite b11_den_atom0; exact (b11_lit_atom E HEI)).
assert (Q13 : getr (ms_regs ms) (Z_to_bv 5 13) = w64 (pf_F v pos + PF_O_CN))
  by (b11_rreg_ok HS; rewrite b11_den_atom0; exact E33).
assert (Q14 : getr (ms_regs ms) (Z_to_bv 5 14) = w64 vp) by (b11_rreg_ok HS; rewrite b11_den_atom0; exact E34).
assert (Q15 : getr (ms_regs ms) (Z_to_bv 5 15) = w64 (pf_F v pos + PF_O_KNOWN))
  by (b11_rreg_ok HS; rewrite b11_den_atom0; exact E35).
pmkst HS.
(* the state at the call: KREFM's on the call's registers (INV_KCALL) *)
assert (HK : INV_KCALL (fx := fx) B n v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv cf nm o ln d gi vp val).
{ destruct HST as (HRC & HCUR & HNM & HCNT & HCURS).
  assert (HC5 : sa_heap B lyc Sc (p_c v) seg_spec.SEG_C_SIZE) by (destruct HOBJ as (_ & _ & _ & _ & H5 & _); exact H5).
  split.
  { split; [exact HCX|].
    split.
    { split; [exact HJ|]. split; [exact Hly|]. split; [exact HSc|]. split; [exact HPERM|].
      split; [exact (b11_keep_saved v pos _ _ _ HGEO KP0 HSAV)|].
      split; [exact (b11_keep_flag v pos _ _ HGEO KP0 HFLAG)|].
      split; [exact HFRM|]. split; [exact HTF|].
      split; [apply (b11_keep_slots v pos _ _ _ HGEO KP0); [repeat constructor; cbn [fst]; lia | exact HSLC]|].
      unfold pf_rg. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
        (rewrite QK; [apply (b11_rg rX _ _ _ HRG0); b11_in | b11_in]). }
    split; [exact (b11_keep_obj B v pos lyc Sc Wc memc mdc _ _ HGEO HAR Hin EF KP0 HOBJ)|].
    split; [exact (b11_keep_sl v pos _ _ HGEO KP0 HSL)|].
    intros i Hi. rewrite K0 by lia. exact (HFSH i Hi). }
  split; [exact HMID|].
  split.
  { split; [exact (b11_keep_rconf B v pos lyc Sc Wc memc mdc _ _ _ HGEO HAR Hin EF KP0 HC5 HRC)|].
    split; [exact HCUR|]. split; [exact (b11_keep_nm v pos _ _ nm HGEO KP0 HNM)|]. split; [exact HCNT|].
    rewrite (rdword_ext (rdW Wc memc) (rdW Wc (ms_mem ms))); [exact HCURS|]. intros k Hk. apply K0. lia. }
  split.
  { apply (b11_keep_sa_str_frame v pos _ _ vp val HGEO KP0);
      [unfold PF_O_BUF in HV1; lia | unfold PF_O_BUF in HV2; lia | exact HVS]. }
  split; [exact (conj HV1 HV2)|].
  split.
  { apply (b11_keep_sa_str_frame v pos _ _ _ known HGEO KP0);
      [unfold PF_O_KNOWN; lia | rewrite b11_known_len; unfold PF_O_KNOWN; lia | exact HKS]. }
  unfold pf_rg, PF_RL, PF_RM, B11_ARGS. cbn [app]. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
    first [ exact Q10 | exact Q11 | exact Q12 | exact Q13 | exact Q14 | exact Q15
          | rewrite QK; [apply (b11_rg rX _ _ _ HRG); b11_in | b11_in] ]. }
pose proof (b11_refuse_site B n v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv cf nm o ln d gi vp val HK)
  as (HROD1 & R10 & Hc64 & R11 & Hl64 & R12 & Hf64 & HPRE1 & HROOM & HEV).
destruct (b11_chain B v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv HCX (proj1 (proj2 (proj1 HK)))) as [ch1 HCH].
assert (Qsp : spZ (ms_regs ms) = pf_sp0 v + (pf_s1 v - pf_sp0 v)).
{ unfold spZ. rewrite (b11_bvr (ms_regs ms) (2%bv : bv 5) 2 _ eq_refl
    (eq_trans (QK 2 ltac:(b11_in)) (b11_rg rX _ 2 _ HRG0 ltac:(b11_in)))).
  rewrite b11_w64_u by lia. lia. }
assert (Qgp : getr (ms_regs ms) 3 = w64 (as_gp B))
  by exact (b11_bvr (ms_regs ms) (3%bv : bv 5) 3 _ eq_refl
    (eq_trans (QK 3 ltac:(b11_in)) (b11_rg rX _ 3 _ HRG0 ltac:(b11_in)))).
assert (Qtp : getr (ms_regs ms) 4 = w64 (as_tp B))
  by exact (b11_bvr (ms_regs ms) (4%bv : bv 5) 4 _ eq_refl
    (eq_trans (QK 4 ltac:(b11_in)) (b11_rg rX _ 4 _ HRG0 ltac:(b11_in)))).
assert (Qs0 : s0Z (ms_regs ms) = pf_sp0 v).
{ unfold s0Z. rewrite (b11_bvr (ms_regs ms) (8%bv : bv 5) 8 _ eq_refl
    (eq_trans (QK 8 ltac:(b11_in)) (b11_rg rX _ 8 _ HRG0 ltac:(b11_in)))).
  apply b11_w64_u. lia. }
rewrite (SIGP SS_refuse ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_refuse) with AF_refuse by (vm_compute; reflexivity).
pose proof (proj1 (proj2 (proj2 (proj1 HK)))) as HOBJ1.
pose proof HOBJ1 as (_ & _ & _ & _ & HC1 & _).
eapply SRr_bind.
{ eapply (cl_callSF (fx := fx) B LAWS Wc (ms_regs ms) (ms_mem ms) _ STK_reac_segconf_parse_file (pf_sp0 v)
    (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc _ 0 STK_refuse
    (refuse_W (p_c v) cf) EV_refuse (pf_s1 v - pf_sp0 v) (Z_to_bv 64 (BASE + 0x3e30)) ch1
    (fun ly2 S2 W2 regs2 mem2 md2 =>
       sa_rconf (rdW W2 mem2) (p_c v) (refuse cf (ln + 1) F_badmodel [AS nm; AS val; AS known]) /\
       sa_noalloc B lyc Sc ly2 S2) HJ).
  - exact Qsp.
  - apply b11_m16; [exact S6 | exact S3].
  - lia.
  - rewrite SREF. lia.
  - rewrite SREF, SPF. lia.
  - exact Qgp.
  - exact Qtp.
  - exact Q1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite unsigned_lit_small by lia. lia.
  - replace (pf_sp0 v + (pf_s1 v - pf_sp0 v)) with (pf_s1 v) by lia. rewrite Qs0. exact HCH.
  - intros HPRE. eapply SRr_mono.
    { apply (REF fx lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv ch1 (p_c v) (ln + 1) (seg_litA_rc F_badmodel) (ln + 1) cf
        F_badmodel [AS nm; AS val; AS known] HPRE HROD1 R10 Hc64 R11 Hl64 R12 Hf64 HPRE1 HROOM HEV). }
    cbv beta. intros W' c' _ (fx' & ly' & S' & regs' & mem' & md' & -> & Hf1 & Hf2 & HJ' & HP' & HK').
    exists fx', ly', S', regs', mem', md'. split; [rewrite Q1; reflexivity|].
    split; [exact Hf1|]. split; [exact Hf2|]. split; [exact HJ'|]. split; [exact HP' | exact HK'].
  - intros a Ha. left. split; [exact (b11_rw_pw (p_c v) cf a Ha)|].
    apply b11_rw_in in Ha. destruct HC1 as (bc & mc & Hinc & Hb1 & Hb2).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ bc mc HAR Hinc) as (_ & _ & _ & _ & _ & _ & Hm).
    pose proof (req_size_pos mc (proj1 Hm)) as [_ Hrq].
    exists bc, mc. split; [exact Hinc | lia]. }
cbv beta. intros W2 c2 _ (fx1 & ly2 & S2 & regs2 & mem2 & md2 & Hfx1 & -> & HJ2 & HJc2 & HP2 & (HRC2 & HNA2)).
replace (0 + EV_refuse) with 0 in HJ2 by reflexivity.
replace (pf_sp0 v + (pf_s1 v - pf_sp0 v)) with (pf_s1 v) in HJc2 by lia.
pose proof (b11_after_refuse B VRO SSPX n v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv cf nm o ln d gi vp val
  fx1 ly2 S2 W2 regs2 mem2 md2 HK Hfx1 HJ2 HJc2 HP2 HRC2 HNA2) as HKO.
unfold pf_postm, PF_POSTr.
eapply (srr_apost_baseF_lift SEGS fx1); [exact Hfx1|].
exact (KOUT fx1 v pos ly2 S2 W2 regs2 mem2 md2 _ nm o ln d gi HKO).
Qed.
End x.

(* ---------- the segment ---------- *)
Theorem S_B11c_holds : S_B11c B.
Proof.
intros f0 n. split.
- intros TAIL. apply (b11_krefm (fx := f0) n).
  apply (b11_kout_ok B n). intros f1. exact (b11_lowout_ok B f1 n TAIL).
- intros TAIL. exact (b11_lowout_ok B f0 n TAIL).
Qed.
End d.
