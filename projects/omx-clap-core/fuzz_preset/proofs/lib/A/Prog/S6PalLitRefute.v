(* fuzz_preset image A, slice S6 (WalkS6): a KERNEL-CHECKED REFUTATION of the image premise pal_lit of
   lib/A/Prog/S6PjString.v (:182-189, blob 55b7fe0b2e90) at the REAL instance (PAImg PI_prog_A, asyms AD2l.TfibB, the
   pair lib/A/PALibA.v palib_A discharges PALib at).
   pal_lit asks, for the 8 bytes PS_LIT .. PS_LIT + 7 of pj_string's "" literal (.str.1), among others
   `~ Exists (in_zr a) (as_owned_static B)`. At the instance:
   (a) PS_LIT = VAL (ps_addhi_atom 21) + ps_addhi_off 21 = 0x21420 (vm_compute of the closed term);
   (b) 0x21421 = PS_LIT + 1 is owned-static: Tfib_owned_static (lib/A/AF0m.v:1742, blob d14761416c8c, TfibB's
       as_owned_static, lib/A/AD2l.v:36) holds the entry (0x21421, 31), ASan's redzone after the 1-byte global;
   (c) so pal_lit is FALSE at the instance, for every allocator relation ARx (pal_lit_unsat_A).
   pal_lit_txt below is S6PjString.v's OLD pal_lit, verbatim, with its Section's PA / B / ARx as parameters.
   THE RESTATED STEP (S6PjString.v pal_lit, owner 16:50Z): the literal step asks only for the ONE byte it reads
   (in_roP, ROM byte 0, not owned-static, not errno: arodata_okP's form) and that the other 7 bytes of its granule are
   image bytes (seg_rom <> None), plus the const shadow cell; its state part is the separate kit fact pal_lit_sh.
   pal_lit1_txt is that text verbatim; pal_lit_A is its INSTANCE WITNESS at PI_prog_A / AD2l.TfibB (vm_compute of
   closed goals only), so the restated step is satisfiable at the real instance.
   Every fact is closed by vm_compute on a CLOSED goal (no Section variable, no abstract model term).
   rule 24: proves no function (kind: image-premise refutation). No ADDRESS in a proof step beyond the measured
   constants stated in the lemma. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YCbqGcall YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YCbqGcallW YC80xf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm YC80xf_inv YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetLiveBounds PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog PAImg_prog PRH_Base PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader PRH_FnReader PRH_FnAlloc PRH_FnPj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger PRW_StepKit S6PjCommon.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PjStringCommon.
From Stdlib Require Import FunctionalExtensionality.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AD2l AF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S6PjString.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require S1ImgA S1ImgCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0.
Import ListNotations.
Local Open Scope Z_scope.


Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* GUARD (h-rw-pre-5 18:3xZ, CrcBp's wrong-image trap: a short `Img0.rsegs` resolves to the PLAIN image's lib/Img0.v in a
   closure that loads it): the segments this file computes over are written fully qualified, and they are the ones the
   walks use at the instance (PI_prog_A's pa_segs), by reflexivity *)
Lemma pal_segs_A : @pa_segs _ A_prog_listing PI_prog_A = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Img0.rsegs.
Proof. reflexivity. Qed.


(* S6PjString.v's pal_lit (:182-189, blob 55b7fe0b2e90), verbatim over its Section's PA (SEGS = pa_segs PA), B, ARx *)
Definition pal_lit_txt (PA : PAImg A_prog_listing) (B : asyms)
    (ARx : alayout -> astate -> list Z -> world (@pa_segs _ A_prog_listing PA) -> (word -> option byte) -> Model -> Prop)
    : Prop :=
  IMG_LO + 64 <= PS_LIT (PA := PA) /\ PS_LIT (PA := PA) + 8 + 64 <= IMG_TOP /\ PS_LIT (PA := PA) mod 8 = 0 /\
  (forall a, PS_LIT (PA := PA) <= a < PS_LIT (PA := PA) + 8 ->
     in_roP (@pa_segs _ A_prog_listing PA) (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) a /\
     seg_rom (@pa_segs _ A_prog_listing PA) (Z_to_bv 64 a) = Some (Z_to_bv 8 0) /\
     ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)) /\
  (forall ly, In (z1 (ANum (shadow_addr (PS_LIT (PA := PA)))) 1) (as_const B ly)) /\
  (forall ly S Hp W mem md a, ARx ly S Hp W mem md -> IMG_LO <= a < IMG_TOP ->
     aview (@pa_segs _ A_prog_listing PA) (w_H W) mem (shadow_addr a) <> None).

(* (a) the literal's address at the instance *)
Lemma ps_lit_A : PS_LIT (PA := PI_prog_A) = 0x21420.
Proof.
unfold PS_LIT. cbn [pa_val PI_prog_A].
(* the goal is closed now (A_prog_val, ps_addhi_atom / ps_addhi_off of the listing): only then vm_compute *)
lazymatch goal with |- A_prog_val (ps_addhi_atom 21) + ps_addhi_off 21 = 0x21420 => vm_compute; reflexivity end.
Qed.

(* (b) the literal's second byte is owned-static at the instance (the entry (0x21421, 31)) *)
Lemma ps_lit_owned_A : Exists (in_zr (0x21420 + 1)) (as_owned_static AD2l.TfibB).
Proof.
assert (H : existsb (fun r => (fst r =? 0x21421) && (snd r =? 31)) AF0m.Tfib_owned_static = true)
  by (vm_compute; reflexivity).
apply existsb_exists in H as ([lo len] & Hin & Hr). apply andb_prop in Hr as [H1 H2].
apply Z.eqb_eq in H1, H2. cbn [fst snd] in H1, H2. subst lo len.
apply Exists_exists. exists (0x21421, 31). split; [exact Hin|]. unfold in_zr. cbn [fst snd]. lia.
Qed.

(* (c) pal_lit is false at the real instance, for every allocator relation *)
Lemma pal_lit_unsat_A : forall ARx, ~ pal_lit_txt PI_prog_A AD2l.TfibB ARx.
Proof.
intros ARx (_ & _ & _ & HB & _).
rewrite ps_lit_A in HB.
destruct (HB (0x21420 + 1) ltac:(lia)) as (_ & _ & Hown & _).
exact (Hown ps_lit_owned_A).
Qed.


(* S6PjString.v's RESTATED pal_lit, verbatim over its Section's PA / B (with the pa_hi bound the per-instance kept_img
   of the #102 kit tip needs) *)
Definition pal_lit1_txt (PA : PAImg A_prog_listing) (B : asyms) : Prop :=
  IMG_LO + 64 <= PS_LIT (PA := PA) /\ PS_LIT (PA := PA) + 8 + 64 <= IMG_TOP /\
  PS_LIT (PA := PA) + 8 + 64 <= @pa_hi _ _ PA /\ PS_LIT (PA := PA) mod 8 = 0 /\
  in_roP (@pa_segs _ A_prog_listing PA) (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) (PS_LIT (PA := PA)) /\
  seg_rom (@pa_segs _ A_prog_listing PA) (Z_to_bv 64 (PS_LIT (PA := PA))) = Some (Z_to_bv 8 0) /\
  ~ Exists (in_zr (PS_LIT (PA := PA))) (as_owned_static B) /\
  ~ (as_errno B <= PS_LIT (PA := PA) < as_errno B + 4) /\
  (forall a, PS_LIT (PA := PA) < a < PS_LIT (PA := PA) + 8 -> seg_rom (@pa_segs _ A_prog_listing PA) (Z_to_bv 64 a) <> None) /\
  (forall ly, In (z1 (ANum (shadow_addr (PS_LIT (PA := PA)))) 1) (as_const B ly)).

(* the INSTANCE WITNESS of the restated step *)
Lemma pal_lit_A : pal_lit1_txt PI_prog_A AD2l.TfibB.
Proof.
unfold pal_lit1_txt. rewrite ps_lit_A.
cbn [as_owned_static as_errno as_const AD2l.TfibB pa_segs pa_relro_lo pa_relro_hi pa_hi PI_prog_A].
assert (CI : IMG_LO = 65536) by (vm_compute; reflexivity).
assert (CT : IMG_TOP = 6291456) by (vm_compute; reflexivity).
split; [rewrite CI; lia|]. split; [rewrite CT; lia|]. split; [rewrite CT; lia|]. split; [reflexivity|].
split.
{ assert (Hb : S1ImgCheck.in_ro_b OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Img0.rsegs A_prog_relro_lo A_prog_relro_hi 0x21420 = true) by (vm_compute; reflexivity).
  unfold S1ImgCheck.in_ro_b in Hb. apply orb_prop in Hb as [Hb | Hb].
  - apply existsb_exists in Hb as (s & Hs & Hb). apply andb_prop in Hb as [Hb H2]. apply andb_prop in Hb as [H0 H1].
    apply negb_true_iff in H0. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
    left. exists s. split; [exact Hs|]. split; [exact H0 | lia].
  - apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. right. lia. }
split.
{ lazymatch goal with |- seg_rom OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Img0.rsegs (Z_to_bv 64 0x21420) = Some (Z_to_bv 8 0) => vm_compute; reflexivity end. }
split.
{ assert (Hb : forallb (fun r => negb ((fst r <=? 0x21420) && (0x21420 <? fst r + snd r))) AF0m.Tfib_owned_static = true)
    by (vm_compute; reflexivity).
  intros HE. apply Exists_exists in HE as (r & Hr & Hin). rewrite forallb_forall in Hb. specialize (Hb r Hr).
  unfold in_zr in Hin. destruct Hin as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. rewrite H1, H2 in Hb.
  discriminate Hb. }
split; [unfold AF0m.TFIB_ERRNO; lia|].
split.
{ assert (Hb : forallb (fun a => match seg_rom OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Img0.rsegs (Z_to_bv 64 a) with Some _ => true | None => false end)
     [0x21421; 0x21422; 0x21423; 0x21424; 0x21425; 0x21426; 0x21427] = true) by (vm_compute; reflexivity).
  intros a Ha Hn. rewrite forallb_forall in Hb.
  assert (Hin : In a [0x21421; 0x21422; 0x21423; 0x21424; 0x21425; 0x21426; 0x21427]) by (cbn [In]; lia).
  specialize (Hb a Hin). rewrite Hn in Hb. discriminate Hb. }
intros ly. unfold AF0m.Tfib_const.
(* the const cell of the literal's shadow byte, its address computed from shadow_addr (YG0f.v) on the closed term, never
   written as a hex literal (h-rw-pre-1's audit of 18b47dcb15cf: a hand-kept shadow address goes stale on a move) *)
assert (Hb : existsb (fun c => match c with ACell (ANum x) 1 (AV (ANum y)) => (x =? shadow_addr 0x21420) && (y =? 1)
                                | _ => false end)
  (AF0m.Tfib_const_sym ++ AF0m.Tfib_const_abs ++ AF0m.Tfib_const_shadow) = true) by (vm_compute; reflexivity).
apply existsb_exists in Hb as (c & Hc & Hm).
destruct c as [ca cw cv]. destruct ca; try discriminate Hm. destruct cw as [|[|cw]]; try discriminate Hm.
destruct cv as [e|]; try discriminate Hm. destruct e; try discriminate Hm.
apply andb_prop in Hm as [H1 H2]. apply Z.eqb_eq in H1, H2. subst. exact Hc.
Qed.
End r.

Print Assumptions pal_lit_unsat_A.
Print Assumptions pal_lit_A.
