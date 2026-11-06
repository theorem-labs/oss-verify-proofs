(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8h.v:104-108;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACbk.v:76-79; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:200-203, 358-361,
   386-392, 532-535, for libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_family_stem.v, with its module paths and module names changed; 95 of its 123 lines of code are new or changed and 244 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/fuzz_catalogue_rowA.v; 391 of its 444 lines of code are new or changed and 70 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A: the loop of fuzz_catalogue_row (0x8a088 .. 0x8a0f4), one lemma per segment, in the
   form of fuzz_command's lib/A/Prog/rec_shape_of_s.v (origin/ossv/recipes 501c0d516c69; each segment seeded by the
   walk kit fuzz_catalogue_rowA_k.v and run by the token executor), with the loop invariant and the row arithmetic
   of proofs/reac-pw/fuzz_pin/lib/A/PPgRow.v (b4e9443a2b9c; rw_head_seg / rw_next_seg / rw_loop):
   HEAD -> R1  the instrumented check of row i's token-pointer word (decided by the shadow entry of the row's
               first granule, so the error path is not reached), the load of the token pointer, the strlen
               wrapper's call;
   R1 -> R2    the length compare; on a length other than n the next-row block, else the bcmp wrapper's call;
   R2          bcmp's result: 0 returns row i (row_from i sb = Some i), else the next-row block;
   NEXT        s6 -= 1, s0 / s3 += 296, s5 += 37; the head of row i + 1, or after row 10 the return of 0.
   The row index is an atom's value, so each segment runs once; fcr_loop closes the loop by induction on the rows
   left. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s YI16 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaArt.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtString.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel SegBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegInstA fuzz_catalogue_row_c fuzz_catalogue_rowA_k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* a register the run left at its seed expression keeps the value it had at the seed (rec_shape_of_s.v same_reg) *)
Ltac same_reg HS HREG r H :=
rawreg HS r H;
let H2 := fresh "H2" in pose proof (HREG r) as H2;
lazymatch type of H2 with getr _ _ = sv_denot _ (sr_get ?sr _) =>
  let e2 := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with e2 in H2 end;
rewrite <- H2 in H; clear H2.
Ltac same_regs HS HREG :=
let S2 := fresh "S2" in same_reg HS HREG (2%bv : bv 5) S2;
let S3 := fresh "S3" in same_reg HS HREG (3%bv : bv 5) S3;
let S4 := fresh "S4" in same_reg HS HREG (4%bv : bv 5) S4;
let S8 := fresh "S8" in same_reg HS HREG (8%bv : bv 5) S8;
let S9 := fresh "S9" in same_reg HS HREG (9%bv : bv 5) S9;
let S18 := fresh "S18" in same_reg HS HREG (18%bv : bv 5) S18;
let S19 := fresh "S19" in same_reg HS HREG (19%bv : bv 5) S19;
let S21 := fresh "S21" in same_reg HS HREG (21%bv : bv 5) S21;
let S22 := fresh "S22" in same_reg HS HREG (22%bv : bv 5) S22;
let S23 := fresh "S23" in same_reg HS HREG (23%bv : bv 5) S23;
let S24 := fresh "S24" in same_reg HS HREG (24%bv : bv 5) S24;
let S25 := fresh "S25" in same_reg HS HREG (25%bv : bv 5) S25;
let S26 := fresh "S26" in same_reg HS HREG (26%bv : bv 5) S26;
let S27 := fresh "S27" in same_reg HS HREG (27%bv : bv 5) S27.
(* the regs_at of the seed's registers at a state that left them as seeded *)
Ltac regs_at_same :=
unfold fcr_regs_at; repeat split;
lazymatch goal with
| S2 : getr _ 2 = getr ?r1 2, R2 : getr ?r1 2 = _ |- getr _ 2 = _ => rewrite S2; exact R2
| S3 : getr _ 3 = getr ?r1 3, R3 : getr ?r1 3 = _ |- getr _ 3 = _ => rewrite S3; exact R3
| S4 : getr _ 4 = getr ?r1 4, R4 : getr ?r1 4 = _ |- getr _ 4 = _ => rewrite S4; exact R4
| S8 : getr _ 8 = getr ?r1 8, R8 : getr ?r1 8 = _ |- getr _ 8 = _ => rewrite S8; exact R8
| S9 : getr _ 9 = getr ?r1 9, R9 : getr ?r1 9 = _ |- getr _ 9 = _ => rewrite S9; exact R9
| S18 : getr _ 18 = getr ?r1 18, R18 : getr ?r1 18 = _ |- getr _ 18 = _ => rewrite S18; exact R18
| S19 : getr _ 19 = getr ?r1 19, R19 : getr ?r1 19 = _ |- getr _ 19 = _ => rewrite S19; exact R19
| S21 : getr _ 21 = getr ?r1 21, R21 : getr ?r1 21 = _ |- getr _ 21 = _ => rewrite S21; exact R21
| S22 : getr _ 22 = getr ?r1 22, R22 : getr ?r1 22 = _ |- getr _ 22 = _ => rewrite S22; exact R22
| S23 : getr _ 23 = getr ?r1 23, R23 : getr ?r1 23 = _ |- getr _ 23 = _ => rewrite S23; exact R23
| S24 : getr _ 24 = getr ?r1 24, R24 : getr ?r1 24 = _ |- getr _ 24 = _ => rewrite S24; exact R24
| S25 : getr _ 25 = getr ?r1 25, R25 : getr ?r1 25 = _ |- getr _ 25 = _ => rewrite S25; exact R25
| S26 : getr _ 26 = getr ?r1 26, R26 : getr ?r1 26 = _ |- getr _ 26 = _ => rewrite S26; exact R26
| S27 : getr _ 27 = getr ?r1 27, R27 : getr ?r1 27 = _ |- getr _ 27 = _ => rewrite S27; exact R27
end.
(* a run that wrote nothing: every write window lies in no region *)
Ltac fcr_awr :=
lazymatch goal with |- awr_ok _ _ ?Ex ?rs _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end;
repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* after a run that wrote nothing: the memory at the stop reads as before the run, everywhere *)
Ltac fcr_after UN :=
lazymatch goal with HFr : frame_of _ _ (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun _ => False) HFr
  ltac:(let b := fresh in let wlo := fresh in let whi := fresh in let a := fresh in let Hin := fresh in let Hrr := fresh in
        intros b wlo whi a Hin Hrr; vm_compute in Hin;
        repeat (let Hq := fresh in destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia|]);
        destruct Hin)) as UN
end;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.

Section e.
Variable B : asyms.
Hypothesis TL : PALib B.
(* the two wrappers the loop calls, at their trampolines, at every FP state (the interceptor-layer owner's rows 16 and 19) *)
Hypothesis ASTRLEN : forall fx0 : YK11.FPState, @RtString.astrlen_realizes fx0 rc SEGS B (SIGMA SS___interceptor_trampoline_strlen).
Hypothesis ABCMP : forall fx0 : YK11.FPState, @abcmp_realizes fx0 rc SEGS B (SIGMA SS___interceptor_trampoline_bcmp).
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_seg) (PI := PI).
Let errno_low := pal_env B TL.

(* open a segment of iteration i at listing offset pc, whose token pointer tp is the image's word at row i
   (Htpw): the entry facts, the state, the seed *)
Ltac fcr_open i tp ly S W regs mem memc mdc regs1 pc CX MID HR Hi Htpw :=
pose proof pa_wx as Hwx; pose proof pa_segs_low as Hsegs; pose proof pa_B_ok as HBASE; pose proof pa_base_lo as HBLO;
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5);
assert (Hes : ESTACK = 4096) by reflexivity;
assert (HSTK : STK_fuzz_catalogue_row = 8256) by reflexivity;
pose proof CX as (HPRE & HROD & H10 & Hp64 & H11 & Hn64 & Hn & HSB & HSA & HLOC & HCAT);
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT);
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2);
pose proof MID as (HJ & HK & HFR);
pose proof HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R21 & R22 & R23 & R24 & R25 & R26 & R27);
set (sp0 := spZ regs) in *;
assert (Hsp0 : spZ regs = sp0) by reflexivity;
pose proof (proj1 HJ) as HAR;
pose proof HCAT as (HCP & HCI & HROWS);
pose proof (fcr_tok_len i Hi) as [Hl0 Hl11];
pose proof (fcr_row_bounds i Hi) as [Hr1 Hr2];
assert (HcA : catA = 0xa18e0) by reflexivity;
assert (HCB : pin_spec.CAT_BYTES = 3256) by reflexivity;
assert (Hlo : alloc_ceiling <= sp0 - STK_fuzz_catalogue_row) by lia;
destruct (HROWS i Hi) as (tp' & Htpw' & HLIT);
rewrite Htpw in Htpw'; injection Htpw' as Etp; subst tp';
pose proof HLIT as (Htp0 & HSTR & HPIN & HRT & HIMG);
assert (LZ : length (seg_spec.zs (pin_spec.tok_bytes i)) = length (pin_spec.tok_bytes i)) by (unfold seg_spec.zs; apply length_map);
rewrite LZ in HPIN, HRT, HIMG;
pose proof (fcr_tok_low B tp (Z.of_nat (length (pin_spec.tok_bytes i))) HIMG ltac:(lia)) as [Htp1 Htp2];
assert (Hrwc : rdword (rdW W memc) (pin_spec.row_addr catA i) = Some tp)
  by (apply (rdword_kept _ _ (sp0 - STK_fuzz_catalogue_row) sp0 _ _ HK Htpw); lia);
assert (HZc : range_addressable (rdW W memc) SHADOW_OFF (pin_spec.row_addr catA i) 8)
  by (destruct (HCP ly S W memc mdc HAR) as (_ & _ & _ & HRA & _);
      eapply range_addressable_sub; [exact HRA | lia | lia]);
destruct (fcr_seed pc W regs regs1 memc sp0 i tp Hi ltac:(lia) ltac:(lia) Hal16 HR eq_refl HFR Hrwc ltac:(lia) HZc)
  as [HS SHOK];
pose proof (fcr_regs_ok regs regs1 i tp Hi HR) as HREG;
pose proof (fcr_E32 regs regs1 i tp) as E32; pose proof (fcr_E33 regs regs1 i tp) as E33;
pose proof (fcr_E34 regs regs1 i tp) as E34; pose proof (fcr_E43 regs regs1 i tp) as E43;
pose proof (fcr_E_saved regs regs1 i tp) as ES;
set (E := fcr_E regs1 regs i tp) in *;
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold fcr_E; apply Eimg_env);
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (let n := fresh in let r := fresh in let Hn' := fresh in intros n r Hn'; apply fcr_E_reg; exact Hn');
assert (Usp : bv_unsigned (ew E 2) = sp0 - 64)
  by (rewrite (EE 2%nat 2%bv eq_refl), R2; unfold w64; apply unsigned_lit_small; lia);
unfold fcr_at.

(* the return (0x8a0f4), from a state whose a0 is shown by A0 to be the contract's value: ra, the journal, the
   callee-saved registers restored from the frame, a0, the kept memory, nothing allocated *)
Ltac fcr_fin HS W ly S regs sp0 E EE ES Usp Hsp0 Hra HJ KM R3 R4 R23 R24 R25 R26 R27 A0 :=
let Q1 := fresh "Q1" in rawreg HS (1%bv : bv 5) Q1;
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
let mat' := fresh "mat" in intros mat'; unfold fcr_post, apost_base; cbv beta;
lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly, S, r, m, d end;
refine (conj _ (conj _ (conj _ _)));
[ rewrite Q1; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
  let E0 := fresh "E0" in pose proof (ES 0%nat 1 eq_refl) as E0; change (35 + 0)%nat with 35%nat in E0; rewrite E0;
  replace (Z_to_bv 5 1) with (1%bv : bv 5) by (apply bv_eq; reflexivity);
  unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity
| apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ
| apply fcr_pres_ret;
  lazymatch goal with |- getr ?rr ?k = getr regs ?k =>
    let Q := fresh "Q" in rawreg HS k Q; rewrite Q; clear Q; cbn [sv_denot];
    first
    [ rewrite Usp; replace (sp0 - 64 + 64) with sp0 by lia; rewrite <- Hsp0; unfold spZ; apply Z_to_bv_bv_unsigned
    | rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
      lazymatch goal with |- ew _ ?nn = getr _ ?kk =>
        first
        [ let j := eval compute in (nn - 35)%nat in let rr := eval compute in (nth j fcr_saved 0) in
          etransitivity; [exact (ES j rr eq_refl)|]; f_equal; apply bv_eq; reflexivity
        | rewrite (EE nn kk eq_refl); first [exact R3 | exact R4 | exact R23 | exact R24 | exact R25 | exact R26 | exact R27] ]
      end ]
  end
| unfold fcr_Q; split; [exact A0|]; split;
  [ let a := fresh "a" in let Ha := fresh "Ha" in let Hna := fresh "Hna" in intros a Ha Hna _; exact (KM a Ha Hna)
  | split; [apply Permutation_refl | split; [reflexivity | exists (st_fs S); apply fcr_set_fs_id]] ] ].

(* HEAD -> R1 (0x8a088 .. 0x8a098): the row's instrumented check, the load of its token pointer, strlen *)
Lemma fcr_head_ok : forall i, (i < pin_spec.CAT_N)%nat -> R1_stmt B i -> HEAD_stmt B i.
Proof.
intros i Hi R1 ly S W regs mem md ch p n sb regs1 memc mdc CX MID HR UN.
pose proof CX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & HROWS0)).
destruct (HROWS0 i Hi) as (tp & Htpw & _).
fcr_open i tp ly S W regs mem memc mdc regs1 FCR_HEAD CX MID HR Hi Htpw.
paj_run_tok RUN HS HJ SHOK Bspan; [fcr_awr|].
pmkst HS. fcr_after UN1.
rawreg HS (10%bv : bv 5) Q10; rawreg HS (1%bv : bv 5) Q1; rawreg HS (2%bv : bv 5) Q2;
rawreg HS (3%bv : bv 5) Q3; rawreg HS (4%bv : bv 5) Q4.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
  assert (KM : kept_out (rdW W mem) (rdW W mm) (sp0 - STK_fuzz_catalogue_row) sp0)
    by (intros a Ha Hna; rewrite (UN1 a Ha (fun x => x)); exact (HK a Ha Hna));
  assert (Hsp : spZ rg = sp0 + -64)
    by (unfold spZ; rewrite Q2; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, Usp; lia);
  assert (QR1 : getr rg 1 = Z_to_bv 64 (BASE + FCR_R1))
    by (rewrite Q1; cbn [sv_denot]; rewrite (img_env_codeptr E HEI); reflexivity);
  assert (HraT : YK0s.ret_ok (getr rg 1))
    by (rewrite QR1; apply ret_ok_codeptr_v; [unfold FCR_R1, AF_fuzz_catalogue_row; lia | reflexivity]);
  assert (Q3' : getr rg 3 = w64 (as_gp B))
    by (rewrite Q3; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 3%nat 3%bv eq_refl), R3; exact Hgp);
  assert (Q4' : getr rg 4 = w64 (as_tp B))
    by (rewrite Q4; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 4%nat 4%bv eq_refl), R4; exact Htp);
  assert (HSTRm : astr_atR (rdW W mm) tp (pin_spec.tok_bytes i))
    by (apply (astr_atR_kept _ _ (sp0 - STK_fuzz_catalogue_row) sp0 tp _ KM); [exact (fcr_astr_of_sa _ _ _ (proj1 HSTR)) | lia | lia | lia]);
  pose proof (HPIN ly S W mm mdq (proj1 HJ)) as (Hm0 & Hm63 & Hmam & Hmra & Hmhull);
  assert (P1 : ecall_pre_stk SEGS B ESTACK ly S W rg mm mdq)
    by exact (ecall_pre_stk_at SEGS B ESTACK STK_fuzz_catalogue_row sp0 [] ly S W mem md [] ly S W mm mdq 0 rg (-64)
               HJ Hsp eq_refl ltac:(lia) ltac:(lia) ltac:(lia) HraT Q3' Q4');
  assert (P2 : getr rg 10 = w64 tp) by (rewrite Q10; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E43; reflexivity);
  assert (P4 : astr_at SEGS W mm tp (pin_spec.tok_bytes i)) by (apply astr_atR_view; exact HSTRm);
  assert (P5 : aread_ok SEGS ESTACK W rg mm tp (astr_len (pin_spec.tok_bytes i) + 1));
  [ unfold aread_ok, astr_len;
    split; [lia|]; split; [lia|]; split; [lia|]; split;
    [ intros a Ha; split;
      [ apply (abytes_some _ tp (pin_spec.tok_bytes i ++ [Z_to_bv 8 0])); [exact (proj1 HSTRm) | rewrite length_app; cbn [length]; lia]
      | unfold ascratch_stk; rewrite Hsp; lia ]
    | split; [exact Hmam|]; split; [exact Hmra | exact Hmhull] ]
  | ];
  assert (P6 : atail_vis SEGS W mm (tp + astr_len (pin_spec.tok_bytes i)))
    by (unfold astr_len; exact (sa_tail_of_romtail SEGS (w_H W) mm _ HRT));
  assert (P7 : rt_rom_view SEGS B W mm) by exact (fcr_rom_view B W mem mm (sp0 - STK_fuzz_catalogue_row) sp0 HROD KM ltac:(lia));
  eapply SRr_bind;
  [ exact (aj_art_at SEGS B LAWS pa_segs_low errno_low ESTACK (fun _ => False) (SIGMA SS___interceptor_trampoline_strlen)
      W rg mm STK_fuzz_catalogue_row sp0 [] ly S W mem md [] ly S mdq 0 (-64) (Z_to_bv 64 (BASE + FCR_R1))
      (fun regs' _ => getr regs' 10 = w64 (astr_len (pin_spec.tok_bytes i))) HJ Hsp eq_refl ltac:(lia) ltac:(lia)
      ltac:(lia) QR1 (fun a (H : False) => False_ind _ H)
      (ASTRLEN fx ly S W rg mm mdq tp (pin_spec.tok_bytes i) P1 P2 ltac:(lia) P4 P5 P6 P7))
  | ]
end.
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha0 & HK2).
same_regs HS HREG.
exact (R1 ly S W regs mem md ch p n sb regs2 mem2 md2 tp CX
  (fcr_mid_call B ly S W regs mem md memc mdc _ mem2 md2 (sp0 - 64 - ESTACK) MID (fun a Ha => UN1 a Ha (fun x => x)) HJ2
     (fun a Ha Hna => HK2 a Ha ltac:(lia) (fun x => x)) ltac:(lia))
  (fcr_regs_at_pres regs regs1 _ regs2 i HR HP2 S2 S3 S4 S8 S9 S18 S19 S21 S22 S23 S24 S25 S26 S27)
  Htpw
  ltac:(rewrite (fcr_pres_reg _ _ 20%bv HP2) by csav; rawreg HS (20%bv : bv 5) Q20;
        rewrite Q20; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E43; reflexivity)
  Ha0 UN).
Qed.

(* the facts a run that wrote nothing leaves for a next segment that starts where it stopped, with the seed's
   registers unchanged *)
Ltac fcr_same_mid HJ HK HFR UN1 memc :=
unfold fcr_mid; split; [exact HJ|]; split;
[ let a := fresh "a" in let Ha := fresh "Ha" in let Hna := fresh "Hna" in
  intros a Ha Hna; rewrite (UN1 a Ha (fun x => x)); exact (HK a Ha Hna)
| eapply (fcr_frame_kept (w_H _) (w_H _) memc _ _ _ HFR);
  let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply UN1; [lia | intros []] ].

(* R1 (0x8a09c): the length compare; a length other than n goes to the next-row block, else bcmp(tp, p, n) *)
Lemma fcr_r1_ok : forall i, (i < pin_spec.CAT_N)%nat -> R2_stmt B i -> NEXT_stmt B i -> R1_stmt B i.
Proof.
intros i Hi HR2 HNX ly S W regs mem md ch p n sb regs1 memc mdc tp CX MID HR Htpw H20 H10' UN.
fcr_open i tp ly S W regs mem memc mdc regs1 FCR_R1 CX MID HR Hi Htpw.
assert (UA : U E (SOff 10 0) = Z.of_nat (length (pin_spec.tok_bytes i)))
  by (apply U_atom; [rewrite (EE 10%nat 10%bv eq_refl); exact H10' | lia]).
assert (UB : U E (SOff 9 0) = n) by (apply U_atom; [rewrite (EE 9%nat 9%bv eq_refl), R9; exact H11 | lia]).
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* bne taken: the token's length is not n; the next row *)
  rewrite branch_ne_U, UA, UB in Hc. apply negb_true_iff, Z.eqb_neq in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan FCR_NEXT; [fcr_awr|].
  pmkst HS. fcr_after UN1.
  same_regs HS HREG.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
  apply (HNX ly S W regs mem md ch p n sb rg mm mdq CX);
  [ fcr_same_mid HJ HK HFR UN1 memc
  | regs_at_same
  | rewrite UN; apply fcr_row_skip; [exact Hi|]; intros Heq; apply Hc; rewrite Heq; lia ]
  end.
- (* not taken: the lengths agree; 0x8a0a0 .. 0x8a0ac, bcmp(tp, p, n) *)
  rewrite branch_ne_U, UA, UB in Hc. apply negb_false_iff, Z.eqb_eq in Hc.
  assert (HL : length (pin_spec.tok_bytes i) = length sb) by lia.
  paj_run_tok RUN HS HJ SHOK Bspan; [fcr_awr|].
  pmkst HS. fcr_after UN1.
  rawreg HS (10%bv : bv 5) Q10; rawreg HS (11%bv : bv 5) Q11; rawreg HS (12%bv : bv 5) Q12;
  rawreg HS (1%bv : bv 5) Q1; rawreg HS (2%bv : bv 5) Q2; rawreg HS (3%bv : bv 5) Q3; rawreg HS (4%bv : bv 5) Q4.
  pose proof (fcr_p_low B ly S W mem md p n HAR0 HLOC ltac:(lia) ltac:(lia)) as Hplow.
  pose proof HSA as (Hs0 & Hs63 & Hsam & Hsra & Hshull).
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
    assert (KM : kept_out (rdW W mem) (rdW W mm) (sp0 - STK_fuzz_catalogue_row) sp0)
      by (intros a Ha Hna; rewrite (UN1 a Ha (fun x => x)); exact (HK a Ha Hna));
    assert (Hsp : spZ rg = sp0 + -64)
      by (unfold spZ; rewrite Q2; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, Usp; lia);
    assert (QR2 : getr rg 1 = Z_to_bv 64 (BASE + FCR_R2))
      by (rewrite Q1; cbn [sv_denot]; rewrite (img_env_codeptr E HEI); reflexivity);
    assert (HraT : YK0s.ret_ok (Z_to_bv 64 (BASE + FCR_R2)))
      by (apply ret_ok_codeptr_v; [unfold FCR_R2, AF_fuzz_catalogue_row; lia | reflexivity]);
    assert (Q3' : getr rg 3 = w64 (as_gp B))
      by (rewrite Q3; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 3%nat 3%bv eq_refl), R3; exact Hgp);
    assert (Q4' : getr rg 4 = w64 (as_tp B))
      by (rewrite Q4; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 4%nat 4%bv eq_refl), R4; exact Htp);
    assert (P10 : getr rg 10 = w64 tp)
      by (rewrite Q10; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 20%nat 20%bv eq_refl); exact H20);
    assert (P11 : getr rg 11 = w64 p)
      by (rewrite Q11; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 18%nat 18%bv eq_refl), R18; exact H10);
    assert (P12 : getr rg 12 = w64 n)
      by (rewrite Q12; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 9%nat 9%bv eq_refl), R9; exact H11);
    assert (HSTRm : astr_atR (rdW W mm) tp (pin_spec.tok_bytes i))
      by (apply (astr_atR_kept _ _ (sp0 - STK_fuzz_catalogue_row) sp0 tp _ KM);
          [exact (fcr_astr_of_sa _ _ _ (proj1 HSTR)) | lia | lia | lia]);
    pose proof (HPIN ly S W mm mdq (proj1 HJ)) as (Hm0 & Hm63 & Hmam & Hmra & Hmhull);
    assert (SRCt : src_ok SEGS W rg mm tp n)
      by (intros a Ha; split;
          [ apply (abytes_some _ tp (pin_spec.tok_bytes i ++ [Z_to_bv 8 0])); [exact (proj1 HSTRm) | rewrite length_app; cbn [length]; lia]
          | rewrite Hsp; lia ]);
    assert (SRCp : src_ok SEGS W rg mm p n)
      by (intros a Ha; split;
          [ rewrite (KM a) by lia; apply (abytes_some _ p sb); [exact HSB | lia]
          | rewrite Hsp; lia ]);
    assert (RAt : range_addressable (rdW W mm) SHADOW_OFF tp n)
      by (eapply range_addressable_sub; [exact Hmra | lia | lia]);
    assert (HUt : 0 < n -> shadow_hull_vis (rdW W mm) tp n)
      by (intros Hn0; apply (fcr_hull_sub _ tp n (Z.of_nat (length (pin_spec.tok_bytes i)) + 1)); [lia | lia | lia | apply Hmhull; lia]);
    assert (RAp : range_addressable (rdW W mm) SHADOW_OFF p n)
      by exact (range_addressable_kept_win _ _ (sp0 - STK_fuzz_catalogue_row) sp0 p n KM ltac:(lia) ltac:(lia) ltac:(lia) Hsra);
    assert (HUp : 0 < n -> shadow_hull_vis (rdW W mm) p n)
      by (intros Hn0; exact (shadow_hull_vis_kept_win _ _ (sp0 - STK_fuzz_catalogue_row) sp0 p n KM ltac:(lia) ltac:(lia) ltac:(lia) Hn0 (Hshull Hn0)));
    (* bcmp's result 0 is the token's equality with sb (PPgRow.v rw_bytes_eq) *)
    assert (FB : (forall k, 0 <= k < Z.of_nat (length (pin_spec.tok_bytes i)) -> rdW W mm (tp + k) = rdW W mm (p + k))
                 <-> pin_spec.tok_bytes i = sb);
    [ apply (fcr_bytes_eq (rdW W mm) tp p (pin_spec.tok_bytes i) sb HL);
      [ intros k Hk; rewrite (proj1 HSTRm k ltac:(rewrite length_app; cbn [length]; lia)); rewrite app_nth1 by lia; reflexivity
      | intros k Hk; rewrite (KM (p + Z.of_nat k)) by lia; exact (HSB k Hk) ]
    | ];
    eapply SRr_bind;
    [ exact (aj_bcmp_at SEGS B LAWS pa_segs_low (SIGMA SS___interceptor_trampoline_bcmp) (ABCMP fx) W rg mm
        STK_fuzz_catalogue_row sp0 [] ly S W mem md [] ly S mdq 0 tp p n (-64) (Z_to_bv 64 (BASE + FCR_R2)) HJ
        P10 P11 P12 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hsp eq_refl ltac:(lia) ltac:(lia) Q3' Q4' QR2 HraT
        SRCt SRCp ltac:(intros a Ha; lia) ltac:(intros a Ha; lia) ltac:(left; lia) Hsam RAt HUt RAp HUp)
    | ]
  end.
  intros W2 c2 _ (-> & regs2 & mem2 & md2 & vv & -> & HJ2 & HP2 & Hres & Hcmp & HK2 & Hpres2).
  same_regs HS HREG. let S20 := fresh "S20" in same_reg HS HREG (20%bv : bv 5) S20.
  rewrite <- Hc in Hcmp.
  assert (HEQ : getr regs2 10 = w64 0 <-> pin_spec.tok_bytes i = sb)
    by (rewrite Hres; split; intros X; [apply (proj1 FB), (proj1 Hcmp), X | apply (proj2 Hcmp), (proj2 FB), X]).
  exact (HR2 ly S W regs mem md ch p n sb regs2 mem2 md2 tp CX
    (fcr_mid_call B ly S W regs mem md memc mdc _ mem2 md2 (sp0 - 64 - 2 * ESTACK) MID (fun a Ha => UN1 a Ha (fun x => x)) HJ2
       (fun a Ha Hna => HK2 a Ha ltac:(lia)) ltac:(lia))
    (fcr_regs_at_pres regs regs1 _ regs2 i HR HP2 S2 S3 S4 S8 S9 S18 S19 S21 S22 S23 S24 S25 S26 S27)
    Htpw
    ltac:(rewrite (fcr_pres_reg _ _ 20%bv HP2) by csav; rewrite S20; exact H20)
    HEQ UN).
Qed.

(* R2 (0x8a0b0): bcmp's result; 0 returns row i (0x8a0cc a0 = s0, the epilogue), else the next-row block *)
Lemma fcr_r2_ok : forall i, (i < pin_spec.CAT_N)%nat -> NEXT_stmt B i -> R2_stmt B i.
Proof.
intros i Hi HNX ly S W regs mem md ch p n sb regs1 memc mdc tp CX MID HR Htpw H20 HEQ UN.
fcr_open i tp ly S W regs mem memc mdc regs1 FCR_R2 CX MID HR Hi Htpw.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* beqz taken: bcmp gave 0, so row i's token is sb: return row i *)
  rewrite branch_eq_U in Hc. apply Z.eqb_eq in Hc.
  assert (Heq : pin_spec.tok_bytes i = sb).
  { apply (proj1 HEQ). rewrite <- (EE 10%nat 10%bv eq_refl). apply bv_eq.
    rewrite U_SOff, U_SLit, Z.add_0_r in Hc.
    rewrite (YP0m.zcanon_small (bv_unsigned (ew E 10))) in Hc by (pose proof (bv_unsigned_in_range 64 (ew E 10)) as Hr; exact Hr).
    rewrite Hc. reflexivity. }
  paj_run_tok RUN HS HJ SHOK Bspan; [fcr_awr|].
  fcr_after UN1.
  lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?ms) |- _ =>
    assert (KM : kept_out (rdW W mem) (rdW W (ms_mem ms)) (sp0 - STK_fuzz_catalogue_row) sp0)
      by (intros a Ha Hna; rewrite (UN1 a Ha (fun x => x)); exact (HK a Ha Hna));
    assert (A0 : getr (ms_regs ms) 10 = w64 (seg_spec.cat_ptr catA (SegModel.cat_row (seg_spec.zs sb))))
      by (rewrite <- SegBridge.bridge_cat_row; unfold pin_spec.row_ptr; rewrite UN, (fcr_row_hit i sb Hi Heq);
          let Q10 := fresh "Q10" in rawreg HS (10%bv : bv 5) Q10; rewrite Q10; cbn [sv_denot];
          rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E33; reflexivity)
  end.
  fcr_fin HS W ly S regs sp0 E EE ES Usp Hsp0 Hra HJ KM R3 R4 R23 R24 R25 R26 R27 A0.
- (* not taken: row i's token is not sb; the next row *)
  rewrite branch_eq_U in Hc. apply Z.eqb_neq in Hc.
  assert (Hne : pin_spec.tok_bytes i <> sb)
    by (intros Heq; apply Hc; rewrite U_SOff, U_SLit, (EE 10%nat 10%bv eq_refl), (proj2 HEQ Heq); reflexivity).
  paj_run_to_tok RUNTO HS HJ SHOK Bspan FCR_NEXT; [fcr_awr|].
  pmkst HS. fcr_after UN1.
  same_regs HS HREG.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
  apply (HNX ly S W regs mem md ch p n sb rg mm mdq CX);
  [ fcr_same_mid HJ HK HFR UN1 memc
  | regs_at_same
  | rewrite UN; apply fcr_row_skip; [exact Hi | exact Hne] ]
  end.
Qed.

(* NEXT (0x8a0b4): s6 -= 1, s3 / s0 += 296, s5 += 37, bnez s6; the head of row i + 1, or after row 10 the
   return of 0 (0x8a0c8 s0 = 0, a0 = s0, the epilogue) *)
Lemma fcr_next_ok : forall i, (i < pin_spec.CAT_N)%nat ->
((Datatypes.S i < pin_spec.CAT_N)%nat -> HEAD_stmt B (Datatypes.S i)) -> NEXT_stmt B i.
Proof.
intros i Hi HH ly S W regs mem md ch p n sb regs1 memc mdc CX MID HR UN.
pose proof CX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & HROWS0)).
destruct (HROWS0 i Hi) as (tp & Htpw & _).
fcr_open i tp ly S W regs mem memc mdc regs1 FCR_NEXT CX MID HR Hi Htpw.
assert (HSBv : SB = 0x7fff8000) by reflexivity.
assert (HCN : pin_spec.CAT_N = 11%nat) by reflexivity.
paj_run_tok RUN HS HJ SHOK Bspan; [fcr_awr|].
fcr_after UN1.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* bnez taken: rows are left; the head of row i + 1 *)
  rewrite branch_ne_U, (U_SOff_v E 34 (11 - Z.of_nat i) (-1) E34 ltac:(lia)), U_lit in Hc by lia.
  rewrite Z.mod_small in Hc by lia. apply negb_true_iff, Z.eqb_neq in Hc.
  assert (Hsi : (Datatypes.S i < pin_spec.CAT_N)%nat) by (unfold pin_spec.CAT_N in *; lia).
  paj_run_to_tok RUNTO HS HJ SHOK Bspan FCR_HEAD; [fcr_awr|].
  pmkst HS. fcr_after UN2.
  let S2 := fresh "S2" in same_reg HS HREG (2%bv : bv 5) S2.
  let S3 := fresh "S3" in same_reg HS HREG (3%bv : bv 5) S3.
  let S4 := fresh "S4" in same_reg HS HREG (4%bv : bv 5) S4.
  let S9 := fresh "S9" in same_reg HS HREG (9%bv : bv 5) S9.
  let S18 := fresh "S18" in same_reg HS HREG (18%bv : bv 5) S18.
  let S23 := fresh "S23" in same_reg HS HREG (23%bv : bv 5) S23.
  let S24 := fresh "S24" in same_reg HS HREG (24%bv : bv 5) S24.
  let S25 := fresh "S25" in same_reg HS HREG (25%bv : bv 5) S25.
  let S26 := fresh "S26" in same_reg HS HREG (26%bv : bv 5) S26.
  let S27 := fresh "S27" in same_reg HS HREG (27%bv : bv 5) S27.
  rawreg HS (8%bv : bv 5) Q8; rawreg HS (19%bv : bv 5) Q19; rawreg HS (21%bv : bv 5) Q21; rawreg HS (22%bv : bv 5) Q22.
  pose proof (fcr_row_next i) as Hrn.
  assert (Hd : 0 <= pin_spec.row_addr catA i / 8 <= 2 ^ 60)
    by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
  apply (HH Hsi ly S W regs mem md ch p n sb rg mm mdq CX);
  [ unfold fcr_mid; split; [exact HJ|]; split;
    [ intros a Ha Hna; rewrite (UN2 a Ha (fun x => x)), (UN1 a Ha (fun x => x)); exact (HK a Ha Hna)
    | eapply (fcr_frame_kept (w_H W) (w_H W) memc _ _ _ HFR); intros a Ha;
      rewrite (UN2 a ltac:(lia) (fun x => x)); apply UN1; [lia | intros []] ]
  | unfold fcr_regs_at; repeat split;
    [ rewrite S2; exact R2 | rewrite S3; exact R3 | rewrite S4; exact R4
    | rewrite Q8; cbn [sv_denot]; rewrite E33, unsigned_lit_small by lia; rewrite Hrn; reflexivity
    | rewrite S9; exact R9 | rewrite S18; exact R18
    | rewrite Q19; cbn [sv_denot]; rewrite E33, unsigned_lit_small by lia; rewrite Hrn; reflexivity
    | rewrite Q21, denot_lit_U; unfold w64; f_equal; rewrite U_SAlu; cbn [zalu_raw];
      change (SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SRL (SOff 33 0) (SLit 3))) with fshx;
      rewrite (U_fshx E _ E32 E33) by lia; rewrite U_lit by lia; rewrite Hrn, fcr_div37, Z.add_assoc;
      apply zcanon_small; lia
    | rewrite Q22; cbn [sv_denot]; rewrite E34, unsigned_lit_small by lia; unfold w64; f_equal; lia
    | rewrite S23; exact R23 | rewrite S24; exact R24 | rewrite S25; exact R25 | rewrite S26; exact R26
    | rewrite S27; exact R27 ]
  | exact UN ]
  end.
- (* not taken: row 10 was the last; 0x8a0c8 s0 = 0, a0 = s0 = 0 = row_ptr cat sb, the return *)
  rewrite branch_ne_U, (U_SOff_v E 34 (11 - Z.of_nat i) (-1) E34 ltac:(lia)), U_lit in Hc by lia.
  rewrite Z.mod_small in Hc by lia. apply negb_false_iff, Z.eqb_eq in Hc.
  assert (Hi10 : i = 10%nat) by lia. subst i.
  paj_run_tok RUN HS HJ SHOK Bspan; [fcr_awr|].
  fcr_after UN2.
  lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?ms) |- _ =>
    assert (KM : kept_out (rdW W mem) (rdW W (ms_mem ms)) (sp0 - STK_fuzz_catalogue_row) sp0)
      by (intros a Ha Hna; rewrite (UN2 a Ha (fun x => x)), (UN1 a Ha (fun x => x)); exact (HK a Ha Hna));
    assert (A0 : getr (ms_regs ms) 10 = w64 (seg_spec.cat_ptr catA (SegModel.cat_row (seg_spec.zs sb))))
      by (rewrite <- SegBridge.bridge_cat_row; unfold pin_spec.row_ptr;
          rewrite UN, (pin_spec.row_from_end sb : pin_spec.row_from (Datatypes.S 10) sb = None);
          let Q10 := fresh "Q10" in rawreg HS (10%bv : bv 5) Q10; rewrite Q10; reflexivity)
  end.
  fcr_fin HS W ly S regs sp0 E EE ES Usp Hsp0 Hra HJ KM R3 R4 R23 R24 R25 R26 R27 A0.
Qed.

(* the loop: the head of every row, by induction on the rows left (PPgRow.v rw_loop) *)
Lemma fcr_heads : forall k i, (i + k = pin_spec.CAT_N)%nat -> (i < pin_spec.CAT_N)%nat -> HEAD_stmt B i.
Proof.
induction k as [|k IH]; intros i Hik Hi; [unfold pin_spec.CAT_N in *; lia|].
assert (NX : NEXT_stmt B i) by (apply (fcr_next_ok i Hi); intros Hsi; apply (IH (Datatypes.S i)); [lia | exact Hsi]).
apply (fcr_head_ok i Hi). apply (fcr_r1_ok i Hi); [apply (fcr_r2_ok i Hi NX) | exact NX].
Qed.
End e.
End f.
End d.
