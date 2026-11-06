(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the narrowing of image B's snprintf site contract (W_sites.v asnprintf_realizes,
   W_sites_x.v asnprintf_realizes_x: the format, M1, M3 and M2 premises, the ruling, SNP-ROUTE.md (sha256 5a5fabe9f628; internal record)
   section 7.5) is SATISFIED at its three walked applications, each premise from the facts the application itself
   holds there.
   - W_LLVMFuzzerTestOneInput_gone_p1.v (AR at PB_fr) and W_LLVMFuzzerTestOneInput_gone_p1_x.v (ARx at PB_fr):
     san_M1, san_M3, san_M2_AR and san_M2_x, SnpAssembly's sanity section on image A, a working branch
     8f558767590a lib/A/RT_pf_snp_srr.v:125-247 (with pf_unparse_piece, pf_unparse, pf_parse_unparse, snp_fmtb,
     snp_ps, snp_fmt_eq), re-pointed to image B: the format .str.9 is A_OBJ 17 and the %s string .str.5
     "param_gesture" is A_lit_gesture = A_OBJ 18 (at the same addresses as image A's, 0x20f80 and 0x20f20), B's GOT
     word FR_GOT_GUARD = 0x9ebd8, and B's image top PF_GLOBALS_TOP = 0x5fc000 (W_sites.v).
   - W_rig_top_calls.v snp_call_tail (relay_instance_gone's call at 0x82eb8), which is generic over the placement PI:
     san_M1_pi, san_M3_pi and san_M2_AR_pi state the same facts at any PI.  At a generic PI the two literals'
     location is not known, so M1 and M3 take it from W_rig_top_calls.v's Section hypothesis HLITGOT, which
     HLITGOT_PB_fr proves at the real placement (image A's design, lib/A/SnpNarrowSites.v, at B's objects).
   - W_rig_top_calls.v is over ARx: san_M2_x_pi is san_M2_AR_pi's fact over any ARx with its laws and the walk's image
     cover IMGC (a Theorem Labs lane's ruling 14:16Z: the ARx twin lives here; image A's san_M2_x_pi with B's top 0x5fc000). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_img W_journal W_contract W_sites.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require printf_facts_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_img_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require RT_pf_Tbl.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* the contract's image top is lib/B/RT_pf_Tbl.v's PF_GLOBALS_TOP (GXA's GLOBALS_TOP at B's A_img), the one
   RT_pf_snp_srr.v's asnprintf_realizes_xn names *)
Lemma PF_GLOBALS_TOP_tbl : PF_GLOBALS_TOP = RT_pf_Tbl.PF_GLOBALS_TOP.
Proof. reflexivity. Qed.

(* ---- the one format: the parser is injective ---- *)
Module PFC := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.printf_facts_c.

Definition pf_unparse_piece (p : PFC.pf_piece) : list Z :=
  match p with
  | PFC.PLit b => [b] | PFC.Pd => [37; 100] | PFC.Pc => [37; 99] | PFC.Px04 => [37; 48; 52; 120]
  | PFC.Px02 => [37; 48; 50; 120] | PFC.Pllu => [37; 108; 108; 117] | PFC.Ps => [37; 115]
  | PFC.Pps => [37; 46; 42; 115]
  end.
Definition pf_unparse (ps : list PFC.pf_piece) : list Z := flat_map pf_unparse_piece ps.

Lemma pf_parse_unparse : forall n f ps, (length f <= n)%nat -> PFC.pf_parse f = Some ps -> f = pf_unparse ps.
Proof.
induction n as [|n IH]; intros f ps Hn H.
- destruct f as [|b r]; [cbn in H; injection H as <-; reflexivity | cbn in Hn; lia].
- destruct f as [|b r]; [cbn in H; injection H as <-; reflexivity|]. cbn [length] in Hn.
  cbn [PFC.pf_parse] in H. destruct (b =? 37) eqn:E37.
  + apply Z.eqb_eq in E37. subst b. destruct r as [|c r1]; [discriminate H|]. cbn [length] in Hn.
    assert (OM : forall (p : PFC.pf_piece) l rest, (length l <= n)%nat ->
              option_map (cons p) (PFC.pf_parse l) = Some ps -> 37 :: c :: rest = pf_unparse_piece p ++ l ->
              37 :: c :: rest = pf_unparse ps).
    { intros p l rest Hl Ho Er. destruct (PFC.pf_parse l) as [ps'|] eqn:El; [|discriminate Ho].
      cbn in Ho. injection Ho as <-. rewrite Er, (IH l ps' Hl El). reflexivity. }
    destruct (c =? 100) eqn:Ec1; [apply Z.eqb_eq in Ec1; subst c; exact (OM PFC.Pd r1 r1 ltac:(lia) H eq_refl)|].
    destruct (c =? 99) eqn:Ec2; [apply Z.eqb_eq in Ec2; subst c; exact (OM PFC.Pc r1 r1 ltac:(lia) H eq_refl)|].
    destruct (c =? 115) eqn:Ec3; [apply Z.eqb_eq in Ec3; subst c; exact (OM PFC.Ps r1 r1 ltac:(lia) H eq_refl)|].
    destruct (c =? 48) eqn:Ec4.
    { apply Z.eqb_eq in Ec4. subst c. destruct r1 as [|c2 [|c3 r3]]; try discriminate H. cbn [length] in Hn.
      destruct ((c2 =? 52) && (c3 =? 120)) eqn:E2.
      - apply andb_prop in E2 as [E2a E2b]. apply Z.eqb_eq in E2a, E2b. subst c2 c3.
        exact (OM PFC.Px04 r3 _ ltac:(lia) H eq_refl).
      - destruct ((c2 =? 50) && (c3 =? 120)) eqn:E3; [|discriminate H].
        apply andb_prop in E3 as [E3a E3b]. apply Z.eqb_eq in E3a, E3b. subst c2 c3.
        exact (OM PFC.Px02 r3 _ ltac:(lia) H eq_refl). }
    destruct (c =? 108) eqn:Ec5.
    { apply Z.eqb_eq in Ec5. subst c. destruct r1 as [|c2 [|c3 r3]]; try discriminate H. cbn [length] in Hn.
      destruct ((c2 =? 108) && (c3 =? 117)) eqn:E2; [|discriminate H].
      apply andb_prop in E2 as [E2a E2b]. apply Z.eqb_eq in E2a, E2b. subst c2 c3.
      exact (OM PFC.Pllu r3 _ ltac:(lia) H eq_refl). }
    destruct (c =? 46) eqn:Ec6; [|discriminate H].
    apply Z.eqb_eq in Ec6. subst c. destruct r1 as [|c2 [|c3 r3]]; try discriminate H. cbn [length] in Hn.
    destruct ((c2 =? 42) && (c3 =? 115)) eqn:E2; [|discriminate H].
    apply andb_prop in E2 as [E2a E2b]. apply Z.eqb_eq in E2a, E2b. subst c2 c3.
    exact (OM PFC.Pps r3 _ ltac:(lia) H eq_refl).
  + destruct ((0 <? b) && (b <? 256)); [|discriminate H].
    destruct (PFC.pf_parse r) as [ps'|] eqn:Er; [|discriminate H]. cbn in H. injection H as <-.
    rewrite (IH r ps' ltac:(lia) Er). reflexivity.
Qed.

Definition snp_fmtb : list Z := [37; 115; 32; 37; 100; 32].   (* "%s %d " *)
Definition snp_ps : list PFC.pf_piece := [PFC.Ps; PFC.PLit 32; PFC.Pd; PFC.PLit 32].

Lemma snp_fmt_eq : forall fmt, PFC.pf_parse fmt = Some snp_ps -> fmt = snp_fmtb.
Proof. intros fmt H. exact (pf_parse_unparse (length fmt) fmt snp_ps (le_n _) H). Qed.

(* ---- THE NARROWING IS SATISFIED AT ITS TWO APPLICATIONS AT PB_fr (W_LLVMFuzzerTestOneInput_gone_p1.v, the SNP bullet
   of gp1_join_l1; W_LLVMFuzzerTestOneInput_gone_p1_x.v, the SNP bullet of gp1_join_l1_x), each premise from the
   facts the application itself holds there ---- *)
Section San. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* M1: both pass f = VAL (A_OBJ 17) (lib/B/W_LLVMFuzzerTestOneInput_gone_p1.v / lib/B/W_LLVMFuzzerTestOneInput_gone_p1_x.v V17) and the format p1_fmt, which parses to the four
   pieces p1_ps, so |fmt| = 6 *)
Lemma san_M1 : forall fmt, PFC.pf_parse fmt = Some snp_ps ->
  65536 <= @pa_val _ fr_prog_listing PB_fr (A_OBJ 17) /\
  @pa_val _ fr_prog_listing PB_fr (A_OBJ 17) + Z.of_nat (length fmt) + 1 <= FR_GOT_GUARD.
Proof.
intros fmt H. rewrite (snp_fmt_eq fmt H).
assert (V17 : @pa_val _ fr_prog_listing PB_fr (A_OBJ 17) = 135040) by (vm_compute; reflexivity).
rewrite V17. unfold FR_GOT_GUARD. cbn [length snp_fmtb]. lia.
Qed.

(* M3: both pass a3 = VAL A_lit_gesture (lib/B/W_LLVMFuzzerTestOneInput_gone_p1.v / lib/B/W_LLVMFuzzerTestOneInput_gone_p1_x.v Q13, V18) with the arguments
   [APtr K_GESTURE; AInt id], so |s| = 13 *)
Lemma san_M3 : forall (r13 : word) (id : Z) s, bv_unsigned r13 = @pa_val _ fr_prog_listing PB_fr A_lit_gesture ->
  hd_error [PFC.APtr RelayModel.K_GESTURE; PFC.AInt id] = Some (PFC.APtr s) ->
  65536 <= bv_unsigned r13 /\ bv_unsigned r13 + Z.of_nat (length s) + 1 + 8 <= FR_GOT_GUARD.
Proof.
intros r13 id s E H. cbn in H. injection H as <-.
assert (V18 : @pa_val _ fr_prog_listing PB_fr A_lit_gesture = 134944) by (vm_compute; reflexivity).
rewrite E, V18. unfold FR_GOT_GUARD, RelayModel.K_GESTURE. cbn [length]. lia.
Qed.

(* M2 at the AR application: the buffer is frame_addr ly 1 fpos + 32 for a live class-1 fake frame (lib/B/W_LLVMFuzzerTestOneInput_gone_p1.v FF /
   Hfin with HART).  AR's ledger puts ly_img over every segment (W_img.fr_img_cover: its top is at least 0x5fc000),
   and a fake frame lies above ly_img: the fake stack is disjoint from ly_img (YG0s.frame_facts), starts at or above
   4096 and is longer than kImgLo (layout_ok's lo_img) - YCbqG.v's field-17 argument *)
Lemma san_M2_AR : forall B ly S (W : world frsegs) mem md fpos,
  AR frsegs B ly S W mem md -> In (1, fpos) (frames S) -> PF_GLOBALS_TOP <= frame_addr ly 1 fpos + 32.
Proof.
intros B ly S W mem md fpos HAR Hin. pose proof HAR as (M & LG & _).
destruct (fr_img_cover ly S md LG) as [_ C2].
pose proof (lo_img _ (am_layout _ _ _ _ M)) as (I1 & I2 & _).
destruct (YG0s.frame_facts B ly S _ 1 fpos M Hin) as (C1 & _ & [F1 _] & D & _ & P1 & _).
assert (HF : fst (ly_img ly) + snd (ly_img ly) <= ly_F ly).
{ destruct (Z_lt_le_dec (ly_F ly) (fst (ly_img ly) + snd (ly_img ly))) as [Hlt|Hge]; [|exact Hge].
  exfalso. apply D. exists (Z.max (ly_F ly) (fst (ly_img ly))). unfold in_zr. cbn [fst snd].
  unfold kImgLo, kFakeStackSize in *. split; [lia | left; lia]. }
unfold frame_addr, kFakeFramesOff, PF_GLOBALS_TOP in *. lia.
Qed.

(* M2 at the ARx application (lib/B/W_LLVMFuzzerTestOneInput_gone_p1_x.v, FF := frame_addr ly 1 fpos at the walk's ARx state at []): the laws'
   image field alx_img puts the frame above ly_img, whose top is at least 0x5fc000 (W_img_x.fr_img_cover_x) *)
Lemma san_M2_x : forall B (ARx : alayout -> astate -> list Z -> world frsegs -> (word -> option byte) -> Model -> Prop)
  hl, AR_laws_x frsegs B ARx hl ->
  forall ly S Hp W mem md fpos, ARx ly S Hp W mem md -> In (1, fpos) (frames S) ->
  PF_GLOBALS_TOP <= frame_addr ly 1 fpos + 32.
Proof.
intros B ARx hl LX ly S Hp W mem md fpos HAR Hin.
destruct (W_img_x.fr_img_cover_x B ARx LX ly S Hp W mem md HAR) as [_ C2].
destruct (alx_img _ _ _ LX ly S Hp W mem md HAR) as [_ HF].
pose proof (HF 1 fpos Hin) as HF1. unfold PF_GLOBALS_TOP. lia.
Qed.
End San.

(* ---- the same three facts at any placement PI, for W_rig_top_calls.v snp_call_tail; M1 / M3 from HLITGOT ---- *)
Section SanPI. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).

Lemma san_M1_pi : forall fmt, PFC.pf_parse fmt = Some snp_ps -> VAL (A_OBJ 17) + 7 <= FR_GOT_GUARD ->
  65536 <= VAL (A_OBJ 17) /\ VAL (A_OBJ 17) + Z.of_nat (length fmt) + 1 <= FR_GOT_GUARD.
Proof.
intros fmt H HG. rewrite (snp_fmt_eq fmt H).
pose proof (@pa_obj_img _ _ PI 17 ltac:(lia)) as O17. cbn [length snp_fmtb]. lia.
Qed.

Lemma san_M3_pi : forall (r13 : word) (id : Z) s, bv_unsigned r13 = VAL (A_OBJ 18) ->
  VAL (A_OBJ 18) + 22 <= FR_GOT_GUARD ->
  hd_error [PFC.APtr RelayModel.K_GESTURE; PFC.AInt id] = Some (PFC.APtr s) ->
  65536 <= bv_unsigned r13 /\ bv_unsigned r13 + Z.of_nat (length s) + 1 + 8 <= FR_GOT_GUARD.
Proof.
intros r13 id s E HG H. cbn in H. injection H as <-.
pose proof (@pa_obj_img _ _ PI 18 ltac:(lia)) as O18.
rewrite E. unfold RelayModel.K_GESTURE. cbn [length]. lia.
Qed.

(* san_M2_AR's proof with the placement's own image cover pa_img_cover in place of W_img.fr_img_cover *)
Lemma san_M2_AR_pi : forall B ly S (W : world SEGS) mem md fpos,
  AR SEGS B ly S W mem md -> In (1, fpos) (frames S) -> PF_GLOBALS_TOP <= frame_addr ly 1 fpos + 32.
Proof.
intros B ly S W mem md fpos HAR Hin. pose proof HAR as (M & LG & _).
destruct (@pa_img_cover _ _ PI ly S md LG) as [_ C2].
pose proof (lo_img _ (am_layout _ _ _ _ M)) as (I1 & I2 & _).
destruct (YG0s.frame_facts B ly S _ 1 fpos M Hin) as (C1 & _ & [F1 _] & D & _ & P1 & _).
assert (HF : fst (ly_img ly) + snd (ly_img ly) <= ly_F ly).
{ destruct (Z_lt_le_dec (ly_F ly) (fst (ly_img ly) + snd (ly_img ly))) as [Hlt|Hge]; [|exact Hge].
  exfalso. apply D. exists (Z.max (ly_F ly) (fst (ly_img ly))). unfold in_zr. cbn [fst snd].
  unfold kImgLo, kFakeStackSize in *. split; [lia | left; lia]. }
unfold frame_addr, kFakeFramesOff, PF_GLOBALS_TOP in *. lia.
Qed.

(* san_M2_x's proof at any placement PI: the laws' image field alx_img puts the frame above ly_img, whose top is at
   least image B's 0x5fc000 by the walk's image cover (its IMGC, word for word, in place of W_img_x.fr_img_cover_x) *)
Lemma san_M2_x_pi : forall B (ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop)
  hl, AR_laws_x SEGS B ARx hl ->
  (forall ly S Hp W mem md, ARx ly S Hp W mem md ->
   fst (ly_img ly) <= 0x10000 /\ 0x5fc000 <= fst (ly_img ly) + snd (ly_img ly)) ->
  forall ly S Hp W mem md fpos, ARx ly S Hp W mem md -> In (1, fpos) (frames S) ->
  PF_GLOBALS_TOP <= frame_addr ly 1 fpos + 32.
Proof.
intros B ARx hl LX IMGC ly S Hp W mem md fpos HAR Hin.
destruct (IMGC ly S Hp W mem md HAR) as [_ C2].
destruct (alx_img _ _ _ LX ly S Hp W mem md HAR) as [_ HF].
pose proof (HF 1 fpos Hin) as HF1. unfold PF_GLOBALS_TOP. lia.
Qed.
End SanPI.

(* W_rig_top_calls.v's, W_rig_top.v's and W_relay_instance_gone.v's Section hypothesis HLITGOT, proved at the real
   placement PB_fr: "%s %d " at 0x20f80 (+ 7) and "param_gesture" at 0x20f20 (+ 22) lie below the GOT word 0x9ebd8 *)
Section HLG. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma HLITGOT_PB_fr : @pa_val _ fr_prog_listing PB_fr (A_OBJ 17) + 7 <= FR_GOT_GUARD /\
  @pa_val _ fr_prog_listing PB_fr (A_OBJ 18) + 22 <= FR_GOT_GUARD.
Proof.
assert (V17 : @pa_val _ fr_prog_listing PB_fr (A_OBJ 17) = 135040) by (vm_compute; reflexivity).
assert (V18 : @pa_val _ fr_prog_listing PB_fr (A_OBJ 18) = 134944) by (vm_compute; reflexivity).
rewrite V17, V18. unfold FR_GOT_GUARD. lia.
Qed.
End HLG.
