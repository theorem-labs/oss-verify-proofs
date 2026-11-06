(* reac-pw/fuzz_role image A (fuzz_role.asan, pinned sha256
   614cffc0864cc31d9d1ced61322c4efd567b64bc89fe09a227a05b5126e0debb; every address measured on the unstripped twin
   6da77bafc5c050954dd89149e1e55a24064c2211e3cbd351822d1c0a20900ad6, the same loaded bytes): THE KEY MATCH of
   segment M02's match half. It proves lib/A/RPgSeg.v's rs_piece_W11b_key_stmt: from the cut rs_cut_KM at
   RS_KM 0x822a8 (entry m of the record is a String key and entry m + 1 exists) the walk reaches the piece's end
   cuts — rs_cut_O at 0x821bc with at = m + 2 when the key is not "reac.cfg.role", and otherwise rs_cut_MAL or
   rs_cut_T through the value the record holds at entry m + 1. Proves no function (kind: segment lemma).

   THE WALK, IN FOUR PIECES, EACH ITS OWN FILE OVER THE ONE SHARED LAYER lib/A/RPgM02KeyBase.v:
     lib/A/RPgM02KeyC.v  rl_m02_key_cmp   0x822a8 -> the strcmp wrapper 0x41ad0 -> 0x822f8: the dead `blt`, the
                                          five spills, the compare of the key's text with .str.1 0x20ee0, and the
                                          two arms — the mismatch to O 0x821bc (the scan goes on at m + 2) and the
                                          match to the value's address at 0x82318.
     lib/A/RPgM02KeyI.v  rl_m02_key_val   0x82318: the entry's type, the dispatch `beq 6` / `bne 4`, and the Int
                                          arm (the size test and the body word) to the value tail or to MAL.
     lib/A/RPgM02KeyF.v  rl_m02_key_float 0x82398: the Float arm, its size test, the one `flw` of this half and
                                          pod_nearest 0x82ccc, to the value tail or to MAL.
     lib/A/RPgM02KeyV.v  rl_m02_key_tail  0x823e0: the role's range test to MAL, check_role 0x82bdc, and the jump
                                          to T 0x82408.
   This file is only the assembly: it hands each piece the continuations of the pieces after it, so no piece ever
   sees another's proof. The one float state of the walk is the cut's own fx2, which is why the strcmp wrapper's
   contract is held at EVERY float state (ASTRCMP below) and not only at the harness's.

   WHAT IS A SECTION HYPOTHESIS. MTL and LAWS (the lane's two runtime laws), the strcmp wrapper's contract at
   every float state, and the two symbol-record cells the pod_nearest lift reads. Every other callee of this half
   is a theorem on the branch: RPgCheck.rl_check_role_A and
   RPgNear.rl_pod_nearest_A_of (RPgNearW.pod_nearest_A_holds NearSFClose.near_sf_facts_ok). *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0s YK15 YK18 YP09 YI04 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import AStrcmpDef.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout Accessors Role.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import Img0 RPgBase RPgCSpec RPgImgA RPgSeg.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgM02Base RPgM02KeyBase.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgM02KeyV RPgM02KeyI RPgM02KeyF RPgM02KeyC.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.
(* the strcmp wrapper's contract, at every float state: rs_from_KM quantifies over the cut's own float state *)
Hypothesis ASTRCMP : forall fy : YK11.FPState, @astrcmp_realizes fy rc rsegs B M2_STRCMP.
(* the two symbol-record cells the pod_nearest lift reads *)
Hypothesis HGOT : as_got_shadow B = 0x9a830.
Hypothesis HSC : as_shadow_cell B = 0xa33f8.

Theorem rl_m02_key_A : rs_piece_W11b_key_stmt rsegs B MT.
Proof using MTL LAWS ASTRCMP HGOT HSC.
unfold rs_piece_W11b_key_stmt.
intros cx POST inp at0 m Hstart HO HABS HMAL HT.
assert (Hpre : rs_pre rsegs B cx) by (destruct Hstart as (H & _); exact H).
apply (rl_m02_key_cmp (fx := fx) B MT MTL LAWS ASTRCMP cx POST inp at0 m Hstart HO).
intros fx3 ly3 S3 W3 regs3 mem3 md3 rec ent a0v
HCB HRA Hppl HAT Hentwf Hvt Hvs Hvb Hra Ha0lo Ha0hi Happ HE0 Hsnd Hfst.
(* the value tail at 0x823e0, for both arms *)
assert (HTAIL : forall (fx4 : YK11.FPState) ly4 S4 W4 regs4 mem4 md4 (v : Z),
  @rs_chk_base fx rc SK rsegs B MT cx fx4 rec ly4 S4 W4 regs4 mem4 md4 ->
  rs_role_at rsegs cx rec W4 mem4 ->
  rs_at_cx rsegs cx W4 mem4 regs4
    (rs_L_chk rsegs cx ++ [(LReg 24, snd (rs_PA rsegs cx rec)); (LReg 25, e_F (x_e rsegs cx));
                           (LReg 27, e_pp (x_e rsegs cx))]) ->
  getr regs4 (Z_to_bv 5 12) = w64 v -> 0 <= v < 2 ^ 64 ->
  (v < 2 -> snd (rs_PA rsegs cx rec) = 1 /\ rs_rcell (fst (rs_PA rsegs cx rec)) = v) ->
  (2 <= v -> fst (rs_PA rsegs cx rec) = None /\ snd (rs_PA rsegs cx rec) = -1) ->
  SRr rsegs W4 (@cfg_at fx4 rsegs M2K_VAL regs4 mem4 md4) POST).
{ intros fx4 ly4 S4 W4 regs4 mem4 md4 v Hb Hr Ha H12 Hv Hlt Hge.
  assert (Hwf : Model.pod_rec_wf rec) by (destruct Hb as (_ & _ & _ & _ & _ & H & _); exact H).
  exact (rl_m02_key_tail (fx := fx) B MT MTL LAWS cx POST rec fx4 ly4 S4 W4 regs4 mem4 md4 v
           Hpre HMAL HT Hb Hr (m2k_pp_len rec Hwf) Ha H12 Hv Hlt Hge). }
(* the Float arm at 0x82398 *)
assert (HFLT : forall (fx4 : YK11.FPState) ly4 S4 W4 regs4 mem4 md4,
  Model.e_type ent = Model.POD_FLOAT ->
  @rs_chk_base fx rc SK rsegs B MT cx fx4 rec ly4 S4 W4 regs4 mem4 md4 ->
  rs_role_at rsegs cx rec W4 mem4 ->
  rs_at_cx rsegs cx W4 mem4 regs4
    (rs_L_chk rsegs cx ++ [(LReg 24, snd (rs_PA rsegs cx rec)); (LReg 10, a0v);
                           (LReg 25, e_F (x_e rsegs cx)); (LReg 27, e_pp (x_e rsegs cx))]) ->
  val_mem rsegs (mrestrict (w_H W4) mem4) (a0v + 4) 4 (Model.e_size ent) ->
  val_mem rsegs (mrestrict (w_H W4) mem4) (a0v + 8) 4 (Cursor.rd32 (Model.e_body ent)) ->
  range_addressable (aview rsegs (w_H W4) mem4) SHADOW_OFF a0v 16 ->
  SRr rsegs W4 (@cfg_at fx4 rsegs 0x82398 regs4 mem4 md4) POST).
{ intros fx4 ly4 S4 W4 regs4 mem4 md4 Hty Hb Hr Ha Hs Hbd Hr16.
  assert (Hwf : Model.pod_rec_wf rec) by (destruct Hb as (_ & _ & _ & _ & _ & H & _); exact H).
  exact (rl_m02_key_float (fx := fx) B MT MTL LAWS HGOT HSC cx POST rec ent fx4 ly4 S4 W4 regs4 mem4 md4 a0v
           HMAL HTAIL Hpre Hb Hr (m2k_pp_len rec Hwf) Ha Hentwf Hty Hs Hbd Hr16
           Ha0lo Ha0hi Happ HE0 Hsnd Hfst). }
exact (rl_m02_key_val (fx := fx) B MT MTL LAWS cx POST rec ent fx3 ly3 S3 W3 regs3 mem3 md3 a0v
         Hpre HMAL HTAIL HFLT HCB HRA Hppl HAT Hentwf Hvt Hvs Hvb Hra Ha0lo Ha0hi Happ HE0 Hsnd Hfst).
Qed.

End k.

Print Assumptions rl_m02_key_A.
