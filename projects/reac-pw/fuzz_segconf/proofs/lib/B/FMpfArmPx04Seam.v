(* Copied from proofs/omx-clap-core/fuzz_manifest/lib/A/FMpfArmPx04Seam.v; relocated to plugin-hostd/fuzz_command.asan by the GXA address relocator (target fuzz_command.asan): module paths changed; 0 address numerals moved (address checker 0767e70e074a, predict mode, fm.asan -> fuzz_command.asan, symbol + offset; the relocator's table for this file). *)
(* Modified by Theorem Labs, 2026-10: relocated from lib/A/<same path> to fuzz_command.asan-ubsan by the image-B address relocator (the A-to-B address map, keyed by the image maps' symbol names and by code; GXA symbol keys kept), whose check table lists every changed numeral *)
(* The three per-piece SEAM ARMS of the %04x piece Px04 (FMgxaSeamPf.v seam_text_arm :98,
   seam_pargs_arm :104, seam_bytes_arm :111, in omx-clap-core/fuzz_manifest's version), so a unit whose covered-piece
   predicate PK includes Px04 gets FMgxaSeamPf.v Section CoveredP's pf_model_agreeP for it.  New file; nothing else edited.

   - text: FMsnprintfPf.v renders Px04 as pf_hex4 v from an AInt v (pf_step, FMpfStep.v:21); GXA's Printf_text.v renders
     it with its own copy PT.pf_hex4 (Printf_text.v:67, :81).  The two copies have the same bodies; x04_pf_hexs is the
     induction over the digit fuel that makes them equal, as fuzz_disco's pt_pf_hexs / pt_pf_hex2 do for %02x
     (fuzz_disco's lib/A/FMgxaSeamPf.v:211, :220).
   - pargs: GXA's model takes %04x's argument as PA_u (v mod 2^32) (Printf_text.v pf_pargs :100), the second form of
     pt_parg_ok.
   - bytes: pf_hex4 v is '0' padding then hex digits ('0'..'9', 'a'..'f'), all bytes, whatever v is.

   Lookup in the proof index, 2026-10-29 14:4xZ:
   pt_pf_hex4 0 hits anywhere; pt_pf_hexs, pt_pargs_shape, pt_parg_ok only the unreleased fuzz_disco template above;
   pf_hex4 22 released declarations, all the definition itself, none a seam arm.  No proof of a Px04 arm exists. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib Require Import ITree.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Spec Require Import Prelim Monad FmtFp.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.GX Require Import Printf_model.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.GX Require G_printf_core_common.
Import OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.GX.G_printf_core_common.G_printf_iface.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.GX Require Printf_text.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtPFPf.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import FMpfStep FMgxaSeamPf.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Module PT := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.GX.Printf_text.

(* ---- the two hex renderers are one function ---- *)
Lemma x04_pf_hexs : forall fuel x acc, PT.pf_hexs fuel x acc = pf_hexs fuel x acc.
Proof.
induction fuel as [|f IH]; intros x acc; [reflexivity|].
cbn [PT.pf_hexs pf_hexs]. destruct (x <? 16); [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma x04_pf_hex4 : forall v, PT.pf_hex4 v = pf_hex4 v.
Proof. intros v. unfold PT.pf_hex4, pf_hex4. cbv zeta. rewrite x04_pf_hexs. reflexivity. Qed.

(* ---- pf_hex4 renders bytes ---- *)
Lemma x04_hexd_byte : forall d, 0 <= d < 16 -> 0 <= pf_hexd d < 256.
Proof. intros d Hd. unfold pf_hexd. destruct (d <? 10); lia. Qed.

Lemma x04_hexs_bytes : forall fuel x acc, 0 <= x -> Forall (fun y => 0 <= y < 256) acc ->
  Forall (fun y => 0 <= y < 256) (pf_hexs fuel x acc).
Proof.
induction fuel as [|f IH]; intros x acc Hx Hacc; [exact Hacc|].
cbn [pf_hexs]. destruct (Z.ltb_spec x 16) as [Hl|Hl].
- constructor; [apply x04_hexd_byte; lia | exact Hacc].
- apply IH; [apply Z.div_pos; lia|].
  constructor; [|exact Hacc]. apply x04_hexd_byte. pose proof (Z.mod_pos_bound x 16 ltac:(lia)). lia.
Qed.

Lemma x04_hex4_bytes : forall v, Forall (fun y => 0 <= y < 256) (pf_hex4 v).
Proof.
intros v. unfold pf_hex4. cbv zeta. apply Forall_app. split.
- apply Forall_forall. intros y Hy. apply repeat_spec in Hy. lia.
- apply x04_hexs_bytes; [exact (proj1 (Z.mod_pos_bound v (2^32) eq_refl)) | constructor].
Qed.

(* ---- the three arms ---- *)
Lemma seam_text_arm_x04 : seam_text_arm Px04.
Proof.
intros qs args c a' H. destruct args as [|[v|u|s] a'']; cbn [pf_step] in H; try discriminate H.
injection H as <- <-. cbn [pt_piece map pt_arg PT.pf_text]. rewrite x04_pf_hex4.
destruct (PT.pf_text qs (map pt_arg a'')); reflexivity.
Qed.

Lemma seam_pargs_arm_x04 : seam_pargs_arm Px04.
Proof.
intros qs args c a' H. destruct args as [|[v|u|s] a'']; cbn [pf_step] in H; try discriminate H.
injection H as <- <-. exists [AInt v], [PA_u (v mod 2^32)].
split; [reflexivity|].
split; [constructor; [right; exists v; split; reflexivity | constructor] | reflexivity].
Qed.

Lemma seam_bytes_arm_x04 : seam_bytes_arm Px04.
Proof.
intros args c a' _ _ H. destruct args as [|[v|u|s] a'']; cbn [pf_step] in H; try discriminate H.
injection H as <- _. apply x04_hex4_bytes.
Qed.

(* ---- fm's pieces plus %04x have all three arms (PK of CoveredP) ---- *)
Definition pf_fm_x04_piece (p : pf_piece) : Prop :=
  match p with PLit _ | Ps | Pps | Px04 => True | _ => False end.

Lemma pf_fm_x04_text_arms : forall p, pf_fm_x04_piece p -> seam_text_arm p.
Proof.
intros p Hp. destruct p; try (exfalso; exact Hp).
- apply seam_text_arm_lit.
- exact seam_text_arm_x04.
- exact seam_text_arm_ps.
- exact seam_text_arm_pps.
Qed.
Lemma pf_fm_x04_pargs_arms : forall p, pf_fm_x04_piece p -> seam_pargs_arm p.
Proof.
intros p Hp. destruct p; try (exfalso; exact Hp).
- apply seam_pargs_arm_lit.
- exact seam_pargs_arm_x04.
- exact seam_pargs_arm_ps.
- exact seam_pargs_arm_pps.
Qed.
Lemma pf_fm_x04_bytes_arms : forall p, pf_fm_x04_piece p -> seam_bytes_arm p.
Proof.
intros p Hp. destruct p; try (exfalso; exact Hp).
- apply seam_bytes_arm_lit.
- exact seam_bytes_arm_x04.
- exact seam_bytes_arm_ps.
- exact seam_bytes_arm_pps.
Qed.

(* CoveredP's three conclusions at that PK.  (After `End CoveredP` each lemma keeps only the arm hypothesis its proof
   uses: pf_model_agreeP takes the text arms, pt_pargs_shapeP the pargs arms, pf_text_bytesP the bytes arms.) *)
Theorem pf_model_agree_fm_x04 : forall (fmtb : list Z) (ps : list pf_piece) (args : list pf_arg) (T : list Z),
  pf_parse fmtb = Some ps -> Forall pf_fm_x04_piece ps -> pf_text ps args = Some T -> Forall pf_arg_fit args ->
  zlength T <= 2147483647 ->
  printf_model (St:=list Z) (OUT_snf (zlength T)) OUTFP_snf (fmtb ++ [0])
      (PT.pf_pargs (map pt_piece ps) (map pt_arg args)) []
    = ITree.Ret (Ok (zlength T, T))
  /\ pass1_ok (fmtb ++ [0]) = true
  /\ Forall (fun c => 0 <= c < 256) (fmtb ++ [0]).
Proof.
apply (pf_model_agreeP pf_fm_x04_piece).
all: first [exact pf_fm_x04_text_arms | exact pf_fm_x04_pargs_arms | exact pf_fm_x04_bytes_arms].
Qed.

Lemma pt_pargs_shape_fm_x04 : forall ps args T, Forall pf_fm_x04_piece ps -> pf_text ps args = Some T ->
  Forall2 pt_parg_ok args (PT.pf_pargs (map pt_piece ps) (map pt_arg args)).
Proof.
apply (pt_pargs_shapeP pf_fm_x04_piece).
all: first [exact pf_fm_x04_text_arms | exact pf_fm_x04_pargs_arms | exact pf_fm_x04_bytes_arms].
Qed.

Lemma pf_text_bytes_fm_x04 : forall ps args T, Forall pf_code_ok ps -> Forall pf_fm_x04_piece ps ->
  Forall pf_arg_fit args -> pf_text ps args = Some T -> Forall (fun x => 0 <= x < 256) T.
Proof.
apply (pf_text_bytesP pf_fm_x04_piece).
all: first [exact pf_fm_x04_text_arms | exact pf_fm_x04_pargs_arms | exact pf_fm_x04_bytes_arms].
Qed.

(* NON-VACUITY CONTROL: "x=%04x\n" with the int 255 renders "x=00ff\n"; the model, given the PA_u argument the
   agreement names, prints exactly that.  Every hypothesis of pf_model_agree_fm_x04 is discharged on a real format. *)
Example x04_control_parse : pf_parse [120; 61; 37; 48; 52; 120; 10] = Some [PLit 120; PLit 61; Px04; PLit 10].
Proof. vm_compute. reflexivity. Qed.
Example x04_control_text :
  pf_text [PLit 120; PLit 61; Px04; PLit 10] [AInt 255] = Some [120; 61; 48; 48; 102; 102; 10].
Proof. vm_compute. reflexivity. Qed.
Example x04_control_pargs :
  PT.pf_pargs (map pt_piece [PLit 120; PLit 61; Px04; PLit 10]) (map pt_arg [AInt 255]) = [PA_u 255].
Proof. vm_compute. reflexivity. Qed.
Lemma x04_control_agree :
  printf_model (St:=list Z) (OUT_snf 7) OUTFP_snf ([120; 61; 37; 48; 52; 120; 10] ++ [0]) [PA_u 255] []
    = ITree.Ret (Ok (7, [120; 61; 48; 48; 102; 102; 10])).
Proof.
assert (HK : Forall pf_fm_x04_piece [PLit 120; PLit 61; Px04; PLit 10])
  by (repeat constructor).
assert (HF : Forall pf_arg_fit [AInt 255]) by (constructor; [cbn; lia | constructor]).
assert (HL : zlength [120; 61; 48; 48; 102; 102; 10] <= 2147483647) by (vm_compute; discriminate).
destruct (pf_model_agree_fm_x04 _ _ _ _ x04_control_parse HK x04_control_text HF HL) as (M & _ & _).
rewrite x04_control_pargs in M. exact M.
Qed.
