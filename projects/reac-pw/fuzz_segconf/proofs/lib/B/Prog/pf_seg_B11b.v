(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca): segment B11b of
   reac_segconf_parse_file's walk, S_B11b_holds : S_B11b B of lib/B/Prog/pf_pieces.v
   (MISS 0x88a50 -> KREFM 0x88bd0: HA_KREFM n -> H_MISS n at every ambient FP state). The B11b segment lane of the image-B G3 walk owner,
   2026-10-30.
    proves function reac_segconf_parse_file (segment B11b; reuse search, rule 24: origin/main 6e24fa4d602c, origin/ossv/recipes 3abc3740de97, origin/ossv/candidates ee89628c9971, origin/release/pau-projects-recipes b6a0088adcb4, the earlier proof delivery and the working heads, by name and by the image-B address 0x87e38 (index and path-scoped git grep); confirmed by the rule-24 checker 2026-10-30T16:55:47Z; the result is recorded with the commissioning brief;
   reuse verdict: none released).
   ADAPTED from the image-A G3 walk owner's image-A lane, on a working branch (pf_a11b_d.v, pf_a11b_f.v) and the unit owner's
   UBSan piece walk on a working branch (lib/U/Prog/pf_p7_miss.v), re-derived on image B's code; closed
   against G3 FINAL at 6f783602b5e3 (lib/B/Prog/reac_segconf_parse_file_c.v, the B-kit copies at 694f3575dda2).

   THE B CUT PLAN of the segment (PLAN-pf-asanubsan.md section 5.2 row B11b; reac_segconf_parse_file.
   fuzz_segconf.asan-ubsan.s): 98 instructions = 0x88a50 .. 0x88bcc (96) and the slow path 0x89234 .. 0x89238 (2,
   errpath_load8, dead: B#28's shadow byte is 0); check B#28 (0x88b74, the catalogue row's shadow byte); UBSan trap
   branches T23 0x88b14, T24 0x88b44, T25 0x88b48, T26 0x88b60, T27 0x88b68, each pass, all to the unimp 0x891c8;
   calls reac_box_catalogue (0x88ad8, C42) and wrapper_snprintf (0x88b9c, C43, eleven passes); exits KREFM by
   0x88bb8 at the eleventh pass (the exits 0x88ae4 and 0x88bcc are not taken: ntok = 11, kn <= 77).
     pf_seg_B11b_a.v  MISS -> KCAT (run 1: the 31 scope-in stores, ntok = 0) -> reac_box_catalogue -> KRET -> KLOOP 0
                      (run 2: beqz not taken, the trap flags slot 0x68 = slot 0x60 = 1): pb11a_head
     pf_seg_B11b_p.v  KLOOP ti -> KSNP (T23 - T27 and B#28 decided per pass) -> snprintf (pf_seg_B11b_s.v pb11_snp)
                      -> KLOOP (S ti) or, after pass 10, KREFM: pb11p_pass
     pf_seg_B11b_d.v  the internal cut KLOOP (INV_KLOOP / H_KLOOP); pf_seg_B11b_f.v the join's list facts;
     pf_seg_B11b_k.v  the transport kit.
   The trap sites and the facts that exclude them (number_c.v's form):
     T23 0x88b14 bltu 240, kn          kn = pb11_kn ti <= 77 (pb11_kn_bound), a literal per pass
     T24 0x88b44 beq (tab <> 0), (tab + 296 ti = 0)   tab = catA = 0xa20a0 (reac_box_catalogue's post: a0 = cat)
     T25 0x88b48 bltu tab + 296 ti, tab              the same, ti <= 10
     T26 0x88b60 bnez (296 ti overflows 64 bits)      ti <= 10
     T27 0x88b68 beqz (tab & 7 = 0 /\ tab <> 0)       catA mod 8 = 0
   SECTION HYPOTHESES (pf_pieces.v's for B11b, each at every FP state, plus the listing facts the walks share):
   CAT (reac_box_catalogue_contract at BASE + AF_reac_box_catalogue, STK_reac_box_catalogue, catA), ASNPRINTF
   (RtFormat.asnprintf_realizes at pa_sigma SS___interceptor_trampoline_snprintf, gotwA, guardA), SIGP
   (SegObj.seg_sig_prog: the call target of reac_box_catalogue), OBJ (SegObj.seg_val_objs: the literal atoms). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtFormat.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable SegSyms SegList SegPa SegObj.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import reac_box_catalogue_c SegInstB pf_pieces
  pf_seg_B11b_d pf_seg_B11b_a pf_seg_B11b_p.
Import ListNotations.
Local Open Scope Z_scope.

Section s.
Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
Variable B : asyms.
Hypothesis CAT : forall fx0 : YK11.FPState, reac_box_catalogue_contract (fx := fx0) SEGS B
  (BASE + AF_reac_box_catalogue) STK_reac_box_catalogue catA.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState,
  @asnprintf_realizes fx0 rc SEGS B (pa_sigma SS___interceptor_trampoline_snprintf) gotwA guardA.
Hypothesis SIGP : seg_sig_prog (PI := PI).
Hypothesis OBJ : seg_val_objs (PI := PI).

(* the join loop by downward induction on the passes left: the head before pass ti, ti + k = 10 *)
Lemma pb11_loop : forall n, HA_KREFM B n -> forall k ti, (ti + k = 10)%nat -> HA_KLOOP B n ti.
Proof.
intros n KR k. induction k as [|k IH]; intros ti Hk f1.
- apply (pb11p_pass B ASNPRINTF OBJ (fx := f1) n ti); [lia | intros H; lia | exact KR].
- apply (pb11p_pass B ASNPRINTF OBJ (fx := f1) n ti); [lia | intros _; apply IH; lia | exact KR].
Qed.

(* the segment statement of pf_pieces.v *)
Theorem S_B11b_holds : S_B11b B.
Proof. intros f0 n KR. exact (pb11a_head B CAT SIGP f0 n (pb11_loop n KR 10 0 eq_refl)). Qed.
End s.
