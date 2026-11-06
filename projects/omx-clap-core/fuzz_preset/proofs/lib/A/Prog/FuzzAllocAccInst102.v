(* fuzz_preset image A' (asan, #102 pin 1be0f53d96cb): the INSTANCE corollaries of FuzzAllocAcc102.v's two walks,
   fuzz_alloc_ran_out_holds_inst and fuzz_alloc_ran_out_reset_holds_inst: the texts (lib/A/PRH_FnAlloc.v
   tfuzz_alloc_ran_out_specX / tfuzz_alloc_ran_out_reset_specX, byte-equal at decff67d721f :127 / :138 and at the kit
   of record f97c8b2f046b :166 / :177) at the real image-A' record B := AD2l.TfibB, with NO image premise.
   THE RECORD is the one h-rw-man-5's PALib binds at the program listing: lib/A/PALibA.v 88c72c8175cf
   (origin/cold/h-rw-man-5-palib102i d00dd1234426; on int102), palib_A : YC1fP.PALib (PI := PI_prog_A) AD2l.TfibB,
   with palib_errno_A (api_env rsegs AD2l.TfibB), palib_head_A and palib_laws_A (AR_laws_x rsegs AD2l.TfibB ARcf).
   The walks take none of these: their laws are AR_laws_ok_cf's, proved inside, and PALib has no field for the walks'
   one stand-in, pal_pst_ok (the seven statics off as_owned_static B and off errno). So pal_pst_ok is DISCHARGED here
   BY COMPUTATION at that record (acc_pal_pst_ok_A, the method of h-w6rep-2's PwAllocSurfSat.v PST_unowned_at_TfibB,
   extended by the errno half): every range of prh_pst (prh_img_A) is disjoint from every range of
   as_owned_static AD2l.TfibB (AF0m.v's Tfib_owned_static) and from the errno cell [as_errno, as_errno + 4).
   The generic checker (acc_pal_pst_b and its soundness) is image-free; FuzzAllocAccInstB102.v uses it at image B'.
   NUMERALS: 4 LENGTH (errno's width, as in pal_pst_ok's text). No ADDRESS literal. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YG00 YG01 YG0f YG0n YI16 YM05 YC4aP YGcfNames YG0ncf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import
Listing_prog PAImg_prog PRH_Base PRH_Img PRH_FnAlloc CfParamsPreset.
(* the instance: Required, not Imported, and cited by qualified name (PALibA.v's convention) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AD2l.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import FuzzAllocAcc102.
(* stdpp, through the LPS modules, shadows several list lemma names; the lemmas used here are Stdlib's *)
From Stdlib Require Import List.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- the generic checker of pal_pst_ok's text: a program static range off every runtime-owned static range and off
   the errno cell ---- *)
Definition acc_dj (r s : Z * Z) : bool := (fst r + snd r <=? fst s) || (fst s + snd s <=? fst r).
Lemma acc_dj_ok : forall r s a, acc_dj r s = true -> in_zr a r -> ~ in_zr a s.
Proof.
intros r s a H Hr Hs. unfold acc_dj, in_zr in *. apply orb_true_iff in H.
destruct H as [H|H]; apply Z.leb_le in H; lia.
Qed.
Definition acc_pal_pst_b (P : list (Z * Z)) (B : asyms) : bool :=
  forallb (fun r => forallb (acc_dj r) (as_owned_static B) && acc_dj r (as_errno B, 4)) P.
Lemma acc_pal_pst_ok_of_b : forall P B, acc_pal_pst_b P B = true -> forall a, Exists (in_zr a) P ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros P B H a HP. apply Exists_exists in HP as [r [Hr Har]].
unfold acc_pal_pst_b in H. rewrite forallb_forall in H. specialize (H r Hr). cbv beta in H.
apply andb_prop in H as [H1 H2].
split.
- intros HS. apply Exists_exists in HS as [s [Hs Has]]. rewrite forallb_forall in H1.
  exact (acc_dj_ok r s a (H1 s Hs) Har Has).
- intros He. apply (acc_dj_ok r (as_errno B, 4) a H2 Har). unfold in_zr. cbn [fst snd]. lia.
Qed.

(* pal_pst_ok (FuzzAllocAcc102.v Section T's text) at the real image-A' record *)
Lemma acc_pal_pst_ok_A : forall a, Exists (in_zr a) (@prh_pst prh_img_A) ->
  ~ Exists (in_zr a) (as_owned_static AD2l.TfibB) /\ ~ (as_errno AD2l.TfibB <= a < as_errno AD2l.TfibB + 4).
Proof. apply acc_pal_pst_ok_of_b. vm_compute. reflexivity. Qed.

(* ---- the two corollaries at B := AD2l.TfibB: the AL rows' instance with the record bound ---- *)
Section I. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
Context {SK : YI16.sink_head}.
#[local] Abbreviation CP := CfParams_preset.
#[local] Abbreviation PA := PI_prog_A.
#[local] Abbreviation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Abbreviation PIA := prh_img_A.
#[local] Abbreviation TA := AD2l.TfibB.
#[local] Abbreviation ARcfx := (fun ly S Hp W mem md => ARcf (cp := CP) SEGS TA ly S Hp W mem md /\ xs_placed_cf ly S).

Corollary fuzz_alloc_ran_out_holds_inst :
  tfuzz_alloc_ran_out_specX (cp := CP) (PI := PIA) (RL := prh_room_live_a8 (cp := CP)) (L := A_prog_listing) (PA := PA)
    TA ARcfx SK.
Proof. exact (fuzz_alloc_ran_out_holds TA). Qed.

Corollary fuzz_alloc_ran_out_reset_holds_inst :
  tfuzz_alloc_ran_out_reset_specX (cp := CP) (PI := PIA) (RL := prh_room_live_a8 (cp := CP)) (L := A_prog_listing)
    (PA := PA) TA ARcfx SK.
Proof. exact (fuzz_alloc_ran_out_reset_holds TA acc_pal_pst_ok_A). Qed.
End I.
