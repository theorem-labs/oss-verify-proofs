(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the NARROWED snprintf site contract (W_sites.v asnprintf_realizes, W_sites_x.v
   asnprintf_realizes_x: the pieces of reply's one format "%s %d "; M1 the format and M3 the %s string in the image's
   read-only data below the GOT word; M2 the destination above the image) holds at each of its three walked
   applications, every premise from the facts that application holds there.
   - W_LLVMFuzzerTestOneInput_gone_p1.v (AR at PB_fr) and W_LLVMFuzzerTestOneInput_gone_p1_x.v (ARx at PB_fr):
     san_M1, san_M3, san_M2_AR and san_M2_x, SnpAssembly's sanity lemmas TAKEN VERBATIM with the parser lemmas they
     use (lib/A/RT_pf_snp_srr.v on a working branch 8f558767590, :125-178 and :190-247; snp_text_shape left
     out, no application here uses it).
   - W_rig_top.v snp_call, which is generic over the placement PI and over the allocator relation ARx: san_M1_pi,
     san_M3_pi and san_M2_x_pi state the same facts at any PI (san_M2_AR_pi is the AR walk's form, kept for the B
     twin's AR caller).  At a generic PI the two literals' location is not known, so M1 and M3 take it from
     W_rig_top.v's Section hypothesis HLITGOT, which HLITGOT_PB_fr proves at the real placement.
   PF_GLOBALS_TOP here is the contract's own, W_sites.v's (as on image B, where mkbkit generates W_sites.v from A's);
   PF_GLOBALS_TOP_tbl proves it equal to lib/A/RT_pf_Tbl.v's, the one RT_pf_snp_srr.v names. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_place W_tbl W_kit W_img W_journal W_contract W_sites.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require printf_facts_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require RT_pf_Tbl.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_img_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require RelayModel.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* the contract's image top is RT_pf_Tbl.v's PF_GLOBALS_TOP (GXA's GLOBALS_TOP at A_img) *)
Lemma PF_GLOBALS_TOP_tbl : PF_GLOBALS_TOP = RT_pf_Tbl.PF_GLOBALS_TOP.
Proof. reflexivity. Qed.

(* ---- the one format: the parser is injective (RT_pf_snp_srr.v 8f558767590 :125-178, verbatim) ---- *)
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

(* ---- THE NARROWING IS SATISFIED AT ITS THREE APPLICATIONS (W_rig_top.v:3202, W_LLVMFuzzerTestOneInput_gone_p1.v:648,
   W_LLVMFuzzerTestOneInput_gone_p1_x.v:478), each premise from the facts the application itself holds there ---- *)
Section San. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* M1: all three pass f = VAL (A_OBJ 20) (lib/A/W_LLVMFuzzerTestOneInput_gone_p1.v:623 V20; gone_p1_x.v:476 and W_rig_top.v:3202 the same object at
   PB_fr) and a format that parses to the four pieces (RIG_FMT, p1_fmt), so |fmt| = 6 *)
Lemma san_M1 : forall fmt, PFC.pf_parse fmt = Some snp_ps ->
  65536 <= @pa_val _ fr_prog_listing PB_fr (A_OBJ 20) /\
  @pa_val _ fr_prog_listing PB_fr (A_OBJ 20) + Z.of_nat (length fmt) + 1 <= FR_GOT_GUARD.
Proof.
intros fmt H. rewrite (snp_fmt_eq fmt H).
assert (V20 : @pa_val _ fr_prog_listing PB_fr (A_OBJ 20) = 135040) by (vm_compute; reflexivity).
rewrite V20. unfold FR_GOT_GUARD. cbn [length snp_fmtb]. lia.
Qed.

(* M3: all three pass a3 = VAL (A_OBJ 21) (gone_p1.v:679 U13, W_rig_top.v:3034 R13) with the arguments
   [APtr K_GESTURE; AInt id] (lib/A/W_LLVMFuzzerTestOneInput_gone_p1.v:649, gone_p1_x.v:477, W_rig_top.v:3204), so |s| = 13 *)
Lemma san_M3 : forall (r13 : word) (id : Z) s, bv_unsigned r13 = @pa_val _ fr_prog_listing PB_fr (A_OBJ 21) ->
  hd_error [PFC.APtr RelayModel.K_GESTURE; PFC.AInt id] = Some (PFC.APtr s) ->
  65536 <= bv_unsigned r13 /\ bv_unsigned r13 + Z.of_nat (length s) + 1 + 8 <= FR_GOT_GUARD.
Proof.
intros r13 id s E H. cbn in H. injection H as <-.
assert (V21 : @pa_val _ fr_prog_listing PB_fr (A_OBJ 21) = 134944) by (vm_compute; reflexivity).
rewrite E, V21. unfold FR_GOT_GUARD, RelayModel.K_GESTURE. cbn [length]. lia.
Qed.

(* M2 at the two AR applications: the buffer is frame_addr ly 1 fpos + 32 for a live class-1 fake frame (W_rig_top.v:3177
   HAR / Hin / HF from ts_jframe; gone_p1.v:508-509 FF / Hfin with HART).  AR's ledger puts ly_img over every segment
   (W_img.fr_img_cover: its top is at least 0x5fb000), and a fake frame lies above ly_img: the fake stack is disjoint
   from ly_img (YG0s.frame_facts), starts at or above 4096 and is longer than kImgLo (layout_ok's lo_img) - YCbqG.v's
   field-17 argument (:1306-1315) *)
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

(* M2 at the ARx application (gone_p1_x.v:476, FF := frame_addr ly 1 fpos at the walk's AR0 state): the laws' image
   field alx_img puts the frame above ly_img, whose top is at least 0x5fb000 (W_img_x.fr_img_cover_x) *)
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

(* ---- W_rig_top.v snp_call, generic over the placement PI: the same three facts at any PI ---- *)
Section SanPI. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).

(* M1: san_M1 at PI; the format's location is HLITGOT's first conjunct, 65536 <= f is PAImg's pa_obj_img *)
Lemma san_M1_pi : forall fmt, PFC.pf_parse fmt = Some snp_ps -> VAL (A_OBJ 20) + 7 <= FR_GOT_GUARD ->
  65536 <= VAL (A_OBJ 20) /\ VAL (A_OBJ 20) + Z.of_nat (length fmt) + 1 <= FR_GOT_GUARD.
Proof.
intros fmt H HG. rewrite (snp_fmt_eq fmt H).
pose proof (@pa_obj_img _ _ PI 20 ltac:(lia)) as O20. cbn [length snp_fmtb]. lia.
Qed.

(* M3: san_M3 at PI; the %s string's location is HLITGOT's second conjunct (|"param_gesture"| + 1 + 8 = 22) *)
Lemma san_M3_pi : forall (r13 : word) (id : Z) s, bv_unsigned r13 = VAL (A_OBJ 21) ->
  VAL (A_OBJ 21) + 22 <= FR_GOT_GUARD ->
  hd_error [PFC.APtr RelayModel.K_GESTURE; PFC.AInt id] = Some (PFC.APtr s) ->
  65536 <= bv_unsigned r13 /\ bv_unsigned r13 + Z.of_nat (length s) + 1 + 8 <= FR_GOT_GUARD.
Proof.
intros r13 id s E HG H. cbn in H. injection H as <-.
pose proof (@pa_obj_img _ _ PI 21 ltac:(lia)) as O21.
rewrite E. unfold RelayModel.K_GESTURE. cbn [length]. lia.
Qed.

(* M2: san_M2_AR at PI, with PAImg's pa_img_cover in place of W_img.fr_img_cover *)
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

(* M2 over any allocator relation ARx at PI: san_M2_x's proof with the walk's image-cover hypothesis IMGC (stated as
   W_rig_top.v's Section hypothesis, word for word) in place of W_img_x.fr_img_cover_x, which holds only at PB_fr.
   The ARx twin of san_M2_AR_pi, shared with lib/B/SnpNarrowSites.v (one name on both images). *)
Lemma san_M2_x_pi : forall B (ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop) hl,
  AR_laws_x SEGS B ARx hl ->
  (forall ly S Hp W mem md, ARx ly S Hp W mem md ->
   fst (ly_img ly) <= 0x10000 /\ 0x5fb000 <= fst (ly_img ly) + snd (ly_img ly)) ->
  forall ly S Hp W mem md fpos, ARx ly S Hp W mem md -> In (1, fpos) (frames S) ->
  PF_GLOBALS_TOP <= frame_addr ly 1 fpos + 32.
Proof.
intros B ARx hl LX IMGC ly S Hp W mem md fpos HAR Hin.
destruct (IMGC ly S Hp W mem md HAR) as [_ C2].
destruct (alx_img _ _ _ LX ly S Hp W mem md HAR) as [_ HF].
pose proof (HF 1 fpos Hin) as HF1. unfold PF_GLOBALS_TOP. lia.
Qed.
End SanPI.

(* W_rig_top.v's and W_relay_instance_gone.v's Section hypothesis HLITGOT, proved at the real placement PB_fr: "%s %d "
   (A_OBJ 20 = 0x20f80) and "param_gesture" (A_OBJ 21 = 0x20f20) lie in .rodata, below the GOT word 0x9e658 *)
Section HLG. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma HLITGOT_PB_fr : @pa_val _ fr_prog_listing PB_fr (A_OBJ 20) + 7 <= FR_GOT_GUARD /\
  @pa_val _ fr_prog_listing PB_fr (A_OBJ 21) + 22 <= FR_GOT_GUARD.
Proof.
assert (V20 : @pa_val _ fr_prog_listing PB_fr (A_OBJ 20) = 135040) by (vm_compute; reflexivity).
assert (V21 : @pa_val _ fr_prog_listing PB_fr (A_OBJ 21) = 134944) by (vm_compute; reflexivity).
rewrite V20, V21. unfold FR_GOT_GUARD. lia.
Qed.
End HLG.
