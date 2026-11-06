(* LLVMFuzzerTestOneInput on image A (fuzz_link.asan, the PUBLISHED pin, sha256 059dae63e07c...), the op_mark arm
   (+0x6a8): the answer its inlined model_mark (+0xb34 .. +0xc0c, +0x1120 .. +0x11fc) computes, and its agreement
   with the library's (link_spec.v mark_lib, mark_quietly_c.v's Post).
   The definition and the lemma are the plain walk's (lib/Prog/Slot/LC2Defs.v mmark, LC2BSpec.v c2b_agree,
   both plain-build files of this unit), restated over link_spec only so that this closure holds no plain-image module.

   o2_mm: the codes of the read and the write are model_read's and model_write's, which normalise them (read_model /
   write_model); the verdict v is answered as it is, so this is NOT link_spec's mark_model, which normalises v too.

   Proves no function (kind: segment lemma of LLVMFuzzerTestOneInput's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_spec.
Import ListNotations.
Open Scope Z_scope.

Definition o2_mm (tab : list (list byte * Z)) (nm : option (list byte))
    (marks reqs : list (list byte)) (K : kstate) : mres :=
  match nm with
  | None => Mres (- E_INVAL) marks reqs K
  | Some s =>
      if Nat.eqb (length s) 0 then Mres (- E_INVAL) marks reqs K
      else
        let r := read_model tab nm KIND_CAP ALIAS_MAX reqs K in
        if negb (r_rc r =? 0) then Mres (r_rc r) marks (r_reqs r) (r_state r)
        else
          let v := decide (Some (r_kind r)) (Some (r_alias r)) in
          if v =? V_MARK
          then
            let w := write_model tab nm (Some S_SERVED) (r_reqs r) (r_state r) in
            if negb (w_rc w =? 0) then Mres (w_rc w) marks (w_reqs w) (w_state w)
            else Mres v (remember marks s) (w_reqs w) (w_state w)
          else if (v =? V_OURS) && bl_eqb (r_alias r) S_SERVED
          then Mres v (remember marks s) (r_reqs r) (r_state r)
          else Mres v marks (r_reqs r) (r_state r)
  end.

Lemma o2_same_rc_refl : forall x, same_rc x x = true.
Proof.
  intros x. unfold same_rc. destruct (Z.eqb_spec x RC_FAILS) as [->|_].
  - reflexivity.
  - apply Z.eqb_refl.
Qed.

Lemma o2_norm_zero : forall rc, (norm_rc rc =? 0) = (rc =? 0).
Proof.
  intros rc. unfold norm_rc. destruct (Z.ltb_spec 0 rc) as [H|H]; [|reflexivity].
  unfold RC_FAILS. destruct (Z.eqb_spec rc 0) as [E|E]; [lia | reflexivity].
Qed.

(* the model and the library on the same inputs: the same marks, the same requests, and same_rc of the codes *)
Lemma o2_agree : forall tab nm marks reqs K,
  same_rc (m_rc (mark_lib tab nm marks reqs K)) (m_rc (o2_mm tab nm marks reqs K)) = true /\
  m_marks (mark_lib tab nm marks reqs K) = m_marks (o2_mm tab nm marks reqs K) /\
  m_reqs (mark_lib tab nm marks reqs K) = m_reqs (o2_mm tab nm marks reqs K).
Proof.
  intros tab nm marks reqs K.
  unfold mark_lib, mark_core, o2_mm, read_model, write_model.
  destruct nm as [s|]; cbv beta iota zeta.
  2: { cbn [m_rc m_marks m_reqs]. split; [apply o2_same_rc_refl | split; reflexivity]. }
  destruct (Nat.eqb (length s) 0).
  { cbn [m_rc m_marks m_reqs]. split; [apply o2_same_rc_refl | split; reflexivity]. }
  destruct (read_core tab (Some s) KIND_CAP ALIAS_MAX reqs K) as [rc kd al rq st].
  cbn [r_rc r_kind r_alias r_reqs r_state].
  rewrite o2_norm_zero.
  destruct (rc =? 0).
  2: { cbn [negb m_rc m_marks m_reqs]. split; [apply same_rc_norm | split; reflexivity]. }
  cbn [negb].
  destruct (decide (Some kd) (Some al) =? V_MARK).
  - destruct (write_core tab (Some s) (Some S_SERVED) rq st) as [wrc wrq wst].
    cbn [w_rc w_reqs w_state].
    rewrite o2_norm_zero.
    destruct (wrc =? 0); cbn [negb m_rc m_marks m_reqs].
    + split; [apply o2_same_rc_refl | split; reflexivity].
    + split; [apply same_rc_norm | split; reflexivity].
  - match goal with |- context [if ?b then _ else _] => destruct b end;
      cbn [m_rc m_marks m_reqs]; (split; [apply o2_same_rc_refl | split; reflexivity]).
Qed.
