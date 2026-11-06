(* Theorem Labs, 2026-10: NON-VACUITY of the kit's tpj_parse_specX premises at the A' binding B := AD2l.TfibB (pj_parse's
   image-A' walk, lib/A/Prog/PjParseA_top.v), on the kit's cwpj-fix f29626eb1667: the closure premise at the driver's
   context PresetCfnA.iface_ctx0 = [[RA_LLVMF]] (the kit's PRH_Witness.prh_univ_closure_witness_A), and, at every entry
   state, a cursor set CW meeting the kit's REPAIRED prh_cw_pj (PRH_Base.v blob ae260e28900e :1521-1527: each cursor arm
   keeps its FIRST disjunct only, the code-word disjunct is gone) on A' - parse_items' arm by the cursor end t0 + len,
   parse_string's by the word at pj_parse's slot sp - pi_frame F_pj_parse - whose room holds at the start depot
   (YCbqGwild.wild_room_cw_init, |CW| = 2 <= u_wmax = 3920, WildRoomInstA.A_wmax with clause 5). The A' walk does not
   read this premise (the kit's countermodel note, PRH_Base.v :1502-1507; lib/B/Prog/CwPjCountermodel.v (sha256 e3202550c0bc; internal record):
   A_entry_closes, parse_value's prh_cw_entry holds at every CW on A' by its code-word disjunct; A_cursor_fixed, both
   A' cursor traces are FIXED); this file only shows that the premise can be met. The B' walk's twin of these is
   pj_parse_top.v pjz_vac_univ_B / pjz_vac_cw_B (the same CW shape).
   proves no function (kind: instance witnesses). No address numeral. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog PAImg_prog PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfImgA AD2l ACej PresetCfnA WildRoomInstA PRH_Witness.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- VACUITY CHECK at the instance B := AD2l.TfibB (A'): the closure at the driver's context [[RA_LLVMF]]
   (the kit's PRH_Witness.prh_univ_closure_witness_A), and for EVERY entry state a cursor set CW meeting the kit's prh_cw_pj on A'
   - each arm by its one disjunct: parse_items' free trace at the cursor end t0 + len, parse_string's at the word w0
   at pj_parse's slot (any word when the slot is not readable) - whose room holds at the start depot
   (YCbqGwild.wild_room_cw_init: |CW| = 2 <= u_wmax = 3920, WildRoomInstA.A_wmax) ---- *)
Section v. Context {rc : YM05.RunCeil}.
Lemma pjz_vac_univ_A : @prh_univ_closure prh_img_A AD2l.TfibB CfImgA.CfImg_A PresetCfnA.iface_ctx0.
Proof. exact (PRH_Witness.prh_univ_closure_witness_A AD2l.TfibB eq_refl eq_refl). Qed.

(* the A' cursor set: one trace per cursor free site, at the cursor end (parse_items) and at the slot word w0
   (parse_string), the words prh_cw_pj names *)
Definition pjz_cw_A (t0 len w0 : Z) : list (list Z) :=
  map (fun r => prh_trace (pc_free_ra0 (as_code AD2l.TfibB)) r [t0 + len])
    (@prh_free_sites prh_img_A F_parse_items) ++
  map (fun r => prh_trace (pc_free_ra0 (as_code AD2l.TfibB)) r [w0])
    (@prh_free_sites prh_img_A F_parse_string).

Lemma pjz_vac_cw_A : forall (W : world (@pa_segs _ A_prog_listing PI_prog_A)) (mem : word -> option byte)
  (regs : bvmap 5 word) (t0 len : Z),
  exists CW, prh_cw_pj (PI := prh_img_A) (PA := PI_prog_A) AD2l.TfibB CW W mem regs t0 len /\
    YCbqGwild.wild_room (as_universe AD2l.TfibB) CW 0 (st_depot init_state).
Proof.
intros W mem regs t0 len.
assert (E2 : (length (@prh_free_sites prh_img_A F_parse_items) +
              length (@prh_free_sites prh_img_A F_parse_string) = 2)%nat) by (vm_compute; reflexivity).
assert (HW : forall w0, YCbqGwild.wild_room (as_universe AD2l.TfibB) (pjz_cw_A t0 len w0) 0 (st_depot init_state)).
{ intros w0. apply YCbqGwild.wild_room_cw_init. unfold pjz_cw_A. rewrite length_app, !length_map, E2.
  change (as_universe AD2l.TfibB) with ACej.Tfib_universe. rewrite WildRoomInstA.A_wmax. lia. }
destruct (rdword (aview (@pa_segs _ A_prog_listing PI_prog_A) (w_H W) mem)
  (spZ regs - @pi_frame prh_img_A F_pj_parse)) as [w0|] eqn:Ew.
- exists (pjz_cw_A t0 len w0).
  split; [unfold prh_cw_pj; split|exact (HW w0)].
  + intros r Hr. unfold pjz_cw_A. apply in_or_app. left. apply in_map_iff. exists r. split; [reflexivity | exact Hr].
  + intros r Hr w Hw. pose proof (eq_trans (eq_sym Ew) Hw) as Ew'. injection Ew' as <-.
    unfold pjz_cw_A. apply in_or_app. right. apply in_map_iff. exists r. split; [reflexivity | exact Hr].
- exists (pjz_cw_A t0 len 0).
  split; [unfold prh_cw_pj; split|exact (HW 0)].
  + intros r Hr. unfold pjz_cw_A. apply in_or_app. left. apply in_map_iff. exists r. split; [reflexivity | exact Hr].
  + intros r Hr w Hw. pose proof (eq_trans (eq_sym Ew) Hw) as Ew'. discriminate Ew'.
Qed.
End v.

Print Assumptions pjz_vac_univ_A.
Print Assumptions pjz_vac_cw_A.
