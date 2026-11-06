(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the loop segment of answer's ASan walk (plugin-hostd/fuzz_command, 0x8a4c0):
   syntax_instantiate's loop from its head HEAD (0x8a670) to JOIN (0x8a734), an_head_ok : AN_JOIN_stmt ->
   AN_HEAD_stmt (lib/A/Prog/answer_s1.v), by strong induction on the bytes of the shape left, in the form of
   proofs/cgif/cgif_file_fuzzer/lib/A/AC8b.v (tcbb_loopX, a loop with inline checks, re-seeded at each iteration). The
   plain proof of the same loop is lib/Prog/answer.v:120-226 (an_loop). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/answer_l.v, with its module paths, module names and numbers changed; 490 of its 561 lines of code are new or changed and 716 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/pf_a11a_l.v, with its module paths and module names changed; 156 of its 202 lines of code are new or changed and 515 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca): stretch SB9_5 of
   segment B9 of reac_segconf_parse_file's walk, its last piece: the strip of R:83-85, from the internal cut B9S5_ST
   0x88554 (lib/B/Prog/pf_seg_B9_s5k.v: right after `add a0,s3,a1`, a0 = vp0 + |v0| - 1, v0 starts and ends with
   the quote) to K5 0x88570. A B9 sub-lane of the image-B G3 walk owner, 2026-10-30.
   proves no function (kind: segment lemma of reac_segconf_parse_file's walk: a piece of stretch SB9_5).
   ADAPTED from lib/B/Prog/trim_f.v (a store with its inline check through the token executor: the shadow entry,
   awr_ok of the byte, the byte read back) and lib/B/Prog/pf_seg_B9_s1.v (the B9 cut rebuilt), on image B's code:
     0x88554 srli a1,a0,3; 0x88558 add a1,a1,s4; 0x8855c lb a1,0(a1); 0x88560 bnez a1 -> 0x89004
                                  check B#14 (store1 at a0): the token executor with the shadow entry of a0 (a byte of
                                  buf, whose shadow cells are 0 under PF_SC_LINE); its slow arm 0x89004 andi / 0x89008
                                  blt back to 0x88564 / 0x8900c j 0x89298 errpath_store1 is not reached
     0x88564 sb zero,0(a0)        the closing quote becomes the NUL (a byte of buf: parse_file's own class-5 frame)
     0x88568 beq s3,s10 -> 0x891c8   UBSan trap T16 (vp0 + 1 wraps): decided not taken by the executor from the seed's
                                  range facts (s3 = vp0 <= 2 ^ 47 - 1, s10 = 2 ^ 64 - 1)
     0x8856c addi s3,s3,1         s3 = vp0 + 1, the value without its quotes (b9_unq_strip)
   and K5 by pf_seg_B9_s5k.v b9s5_k5 (the key below vp0 kept whole across the store).
   Instructions walked: 0x88554 .. 0x8856c (7). Check B#14, trap T16. No call. No Section hypothesis. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun PaSB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_pieces pf_seg_B9_d pf_seg_B9_f
  pf_seg_B9_k pf_seg_B9_c pf_seg_B9_s5k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Ltac b9s5s_in := cbn [In app]; repeat first [left; reflexivity | right].
(* a register the run left as its own atom: the seed's value (EE : ew E n = getr rX r) *)
Ltac b9s5s_kept HS EE :=
  lazymatch goal with |- getr _ (Z_to_bv 5 ?r) = getr _ (Z_to_bv 5 ?r) =>
    let Hk := fresh "Hk" in prreg HS (Z_to_bv 5 r) Hk; rewrite Hk; apply EE; reflexivity end.

(* the seed at B9S5_ST: every register its own atom; the byte a0 = vp0 + |v0| - 1 is a one-byte writable region of
   atom 10 (trim_f.v's tf_ss form); range facts for a0 and s3 (the check's shadow entry, the trap T16), the shadow
   base s4 = SB and s10 = 2 ^ 64 - 1 *)
Definition b9s5s_regions : smem := [YP09.mkRegion (Some 10%nat) 0 1 0 1 []].
Definition b9s5s_facts : facts :=
  mkFacts [(10%nat, mkAF 4096 (2 ^ 47 - 1) 0); (19%nat, mkAF 4096 (2 ^ 47 - 1) 0); (20%nat, mkAF SB SB 0);
           (26%nat, mkAF (2 ^ 64 - 1) (2 ^ 64 - 1) 0)] [] [].
Definition b9s5s_ss : sstate := mkSS B9S5_ST sr_atoms b9s5s_regions None b9s5s_facts.
Definition b9s5s_Bx : sv := SOff 20 0.
Definition b9s5s_SH : list shent := [mkSHE 10 0 1].
(* the registers the strip does not write *)
Definition b9s5s_keep : list Z := [2; 3; 4; 8; 9; 20; 18; 21; 26; 25; 22; 23; 15].

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.

Section x. Context {fx : YK11.FPState}.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNTO := paj_run_to (fx := fx) B LAWS.

(* the byte a run wrote into a one-byte written region (trim_f.v tr_wbyte) *)
Lemma b9s5s_wbyte : forall E ss ms (H : word -> bool) (n i : nat) Pz v,
  st_ok_pi SEGS VAL E ss (restrict H ms) ->
  nth_error (ss_mem ss) i = Some (YP09.mkRegion (Some n) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 v)]) ->
  bv_unsigned (ew E n) = Pz ->
  aview SEGS H (ms_mem ms) Pz = Some (bv_unsigned (sv_denot E v) mod 256).
Proof.
intros E ss ms H n i Pz v HS Hn HP.
pose proof (st_ok_pi_region_nth E ss (restrict H ms) i _ HS Hn) as Hr.
pose proof (field_of_region_any E _ n Pz _ 0 1 0 1 0 1%N v Hr HP (or_introl eq_refl) ltac:(lia)) as V.
cbn [ms_mem restrict] in V. rewrite Z.add_0_r in V. change (2 ^ (8 * Z.of_N 1)) with 256 in V.
apply aview_of_val_mem1; [exact V | apply Z.mod_pos_bound; lia].
Qed.

Lemma b9s5s_seed : forall (Wc : world SEGS) (rX : bvmap 5 word) memc w vp0,
  getr rX (Z_to_bv 5 10) = w64 w -> getr rX (Z_to_bv 5 19) = w64 vp0 ->
  getr rX (Z_to_bv 5 20) = w64 SHADOW_OFF -> getr rX (Z_to_bv 5 26) = w64 (-1) ->
  4096 <= w <= 2 ^ 47 - 1 -> 4096 <= vp0 <= 2 ^ 47 - 1 -> apresent (w_H Wc) memc w ->
  st_ok_pi SEGS VAL (Eimg (Ereg rX [])) b9s5s_ss
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + B9S5_ST)) memc (seg_rom SEGS))).
Proof.
intros Wc rX memc w vp0 H10 H19 H20 H26 Hw Hv Hp.
set (E := Eimg (Ereg rX [])).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr rX r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U10 : bv_unsigned (ew E 10) = w)
  by (rewrite (EE 10%nat (Z_to_bv 5 10) eq_refl), H10; unfold w64; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E 19) = vp0)
  by (rewrite (EE 19%nat (Z_to_bv 5 19) eq_refl), H19; unfold w64; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E 20) = SB)
  by (rewrite (EE 20%nat (Z_to_bv 5 20) eq_refl), H20; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF, SB; lia).
assert (U26 : bv_unsigned (ew E 26) = 2 ^ 64 - 1)
  by (rewrite (EE 26%nat (Z_to_bv 5 26) eq_refl), H26; unfold w64; vm_compute; reflexivity).
rewrite restrict_mkst_fx. unfold b9s5s_ss. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold b9s5s_regions. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U10.
  split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. assert (o = 0) as -> by lia. rewrite Z.add_0_r. apply (apresent_writable SEGS). exact Hp.
- cbn. tauto.
- split; [|split; exact I]. cbn [b9s5s_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U10, U19, U20, U26. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB. repeat split; lia.
Qed.

Lemma b9s5_strip_ok : forall n, from_K5 B n -> from_S5 B n.
Proof.
intros n HK5 q x ei kp vp0 lyc Sc Wc rX memc mdc HSI.
pose proof HSI as (HD & HL2 & Hq & Hq0 & HqN & HRG).
pose proof (b9s5_D_rng B _ _ _ _ _ _ _ _ _ _ _ HD) as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & HNZ).
pose proof HD as (HC & HCH & HKEY & HKLT & HV0).
pose proof HC as (HB & HM & HST & HL & HD0 & HDL).
destruct (b9_geo B _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hin & G & HFP & HSP).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof (b9_fi_regs B _ _ _ _ _ _ _ _ _ HB) as HFI.
pose proof HB as (HCX & (HJ & _) & _).
pose proof (b9_st_of_base B _ _ _ _ _ _ _ _ HB) as HST0.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HV0 as [HSTR _].
unfold b9_buf, PF_O_BUF in R1, R2, R4, R5.
unfold B9_R, PF_RL, PF_RM in HRG.
set (V := b9_v0 x ei) in *.
assert (Hw0 : 4096 <= vp0 + Z.of_nat (length V) - 1 <= 2 ^ 47 - 1) by lia.
(* the registers at B9S5_ST *)
assert (R10 : getr rX (Z_to_bv 5 10) = w64 (vp0 + Z.of_nat (length V) - 1))
  by (apply (b9_rg_get rX _ 10 _ HRG); b9s5s_in).
assert (R19 : getr rX (Z_to_bv 5 19) = w64 vp0) by (apply (b9_rg_get rX _ 19 _ HRG); b9s5s_in).
assert (R26 : getr rX (Z_to_bv 5 26) = w64 (-1)) by (apply (b9_rg_get rX _ 26 _ HRG); b9s5s_in).
assert (R20 : getr rX (Z_to_bv 5 20) = w64 SHADOW_OFF) by (apply (b9_rg_get rX _ 20 _ HFI); unfold b9_FI; b9s5s_in).
(* the seed *)
pose proof (b9s5s_seed Wc rX memc (vp0 + Z.of_nat (length V) - 1) vp0 R10 R19 R20 R26 Hw0 ltac:(lia)
  (HFP (vp0 + Z.of_nat (length V) - 1) ltac:(lia))) as HS.
set (E := Eimg (Ereg rX [])) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr rX r)
  by (intros n0 r Hn0; subst E; apply ew_Eimg_Ereg_nat; exact Hn0).
assert (E10 : ew E 10 = Z_to_bv 64 (vp0 + Z.of_nat (length V) - 1))
  by (rewrite (EE 10%nat (Z_to_bv 5 10) eq_refl); exact R10).
assert (E19 : ew E 19 = Z_to_bv 64 vp0) by (rewrite (EE 19%nat (Z_to_bv 5 19) eq_refl); exact R19).
assert (E20 : ew E 20 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 20%nat (Z_to_bv 5 20) eq_refl); exact R20).
clearbody E.
assert (U10 : bv_unsigned (ew E 10) = vp0 + Z.of_nat (length V) - 1) by (rewrite E10; apply unsigned_lit_small; lia).
(* the shadow entry of the byte: check B#14 *)
destruct (b9_addr_buf B _ _ _ _ _ _ _ (vp0 + Z.of_nat (length V) - 1) 1 HST0
  ltac:(unfold b9_bufp, PF_O_BUF; lia) ltac:(lia) ltac:(unfold b9_bufp, PF_O_BUF; lia)) as (_ & _ & _ & HRA & _).
assert (UB : U E b9s5s_Bx = SHADOW_OFF) by (unfold b9s5s_Bx; apply (U_atom E 20 _ E20); unfold SHADOW_OFF; lia).
assert (UW : U E (SOff 10 0) = vp0 + Z.of_nat (length V) - 1) by (apply (U_atom E 10 _ E10); lia).
assert (SHOK : sh_ok SEGS b9s5s_Bx b9s5s_SH E (mrestrict (w_H Wc) memc)).
{ unfold sh_ok, b9s5s_SH. apply Forall_cons; [|apply Forall_nil].
  eapply (shent_ok_of_range SEGS (w_H Wc) memc E b9s5s_Bx 10%nat (vp0 + Z.of_nat (length V) - 1) 1
    (vp0 + Z.of_nat (length V) - 1) 0 1 HRA UB UW); [lia | lia |].
  intros y Hy. change (Z.min 0 1) with 0 in Hy. change (Z.max 0 1) with 1 in Hy.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in G9. unfold SHADOW_OFF. lia. }
unfold cfg_at. change (w64 (BASE + B9S5_ST)) with (Z_to_bv 64 (BASE + B9S5_ST)).
(* 0x88554 .. 0x8856c: check B#14, the NUL store, the trap T16, s3 = vp0 + 1; up to K5 *)
paj_run_to_tok RUNTO HS HJ SHOK Bspan B9_K5.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end.
  eapply awr_ok_cons_gen with (n := 10%nat) (b := vp0 + Z.of_nat (length V) - 1);
    [reflexivity | exact U10 | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
  right; right; right; left. exists 5%Z, (y_pos x). split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
  rewrite Hly. change (frame_addr (p_ly (y_v x)) 5 (y_pos x)) with (pf_F (y_v x) (y_pos x)).
  change (fs_frame_bytes 5) with 2048. lia. }
set (mdv := with_vm_backing _ _ _) in *; clearbody mdv.
(* what the run kept and what it wrote *)
assert (KM : forall a, 0 <= a < 2 ^ 64 -> a <> vp0 + Z.of_nat (length V) - 1 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha Hne.
  apply (kept_of_frame (segs := SEGS) E _ (w_H Wc) memc (ms_mem ms) (fun a' => a' = vp0 + Z.of_nat (length V) - 1) HFr);
    [|exact Ha | exact Hne].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
  destruct Hin' as [Hq' | []]; injection Hq' as <- <- <-; cbn [base_val] in Hrr; rewrite U10 in Hrr; lia. }
assert (HW0 : rdW Wc (ms_mem ms) (vp0 + Z.of_nat (length V) - 1) = Some 0).
{ pose proof (b9s5s_wbyte _ _ _ _ 10%nat 0%nat (vp0 + Z.of_nat (length V) - 1) (SLit 0) HS
    ltac:(vm_compute; reflexivity)) as V0.
  rewrite V0; [reflexivity|]. cbn [extK]. exact U10. }
assert (KV : forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc a <> None -> rdW Wc (ms_mem ms) a <> None)
  by (intros a _ Hv; exact (aview_keeps_vis SEGS (w_H Wc) memc (ms_mem ms) a HG Hv)).
clear HFr HG HF.
(* the registers at K5 *)
assert (QK : forall r, In r b9s5s_keep -> getr (ms_regs ms) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
{ intros r Hr. unfold b9s5s_keep in Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [b9s5s_kept HS EE |]).
  destruct Hr. }
prreg HS (Z_to_bv 5 19) Q19.
assert (Q19' : getr (ms_regs ms) (Z_to_bv 5 19) = w64 (vp0 + 1)).
{ rewrite Q19. rewrite E19. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?k)) ?mm ?rom) ?mdx) _ =>
  change (mkCfg (mkst rg (Z_to_bv 64 (BASE + k)) mm rom) mdx) with (cfg_at SEGS (BASE + B9_K5) rg mm mdx) end.
apply (HK5 x ei kp (vp0 + 1) lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv).
apply (b9s5_k5 B n x ei kp vp0 (vp0 + 1) lyc Sc Wc rX memc mdc (ms_regs ms) (ms_mem ms) mdv
  (vp0 + Z.of_nat (length V) - 1) (vp0 + Z.of_nat (length V)) HD HJ).
- lia.
- unfold b9_buf, PF_O_BUF. lia.
- intros a Ha Hn. apply KM; [exact Ha | lia].
- exact KV.
- unfold b9_FI, pf_rg. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
    (rewrite QK; [apply (b9_rg_get rX _ _ _ HFI); unfold b9_FI; b9s5s_in | unfold b9s5s_keep; b9s5s_in]).
- unfold B9_R, PF_RL, PF_RM, pf_rg. cbn [app].
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
    first [ exact Q19'
          | rewrite QK; [apply (b9_rg_get rX _ _ _ HRG); b9s5s_in | unfold b9s5s_keep; b9s5s_in] ].
- unfold b9_val. fold V. rewrite (b9_unq_strip V q HNZ HL2 Hq Hq0 HqN).
  split.
  + apply (b9s5_strip_str (rdW Wc memc) (rdW Wc (ms_mem ms)) vp0 V HSTR HL2).
    * intros a Ha. apply KM; lia.
    * exact HW0.
    * intros a Hv. rewrite b9s5_aview_mod in Hv |- *. apply KV; [apply Z.mod_pos_bound; lia | exact Hv].
  + unfold pf_inb, b9_buf, PF_O_BUF. rewrite b9s5_slice_len by exact HL2. lia.
Qed.

End x.
End d.
