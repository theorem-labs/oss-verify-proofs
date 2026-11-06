(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import BgCommon.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition ENTRY : Z := 0xbd110.
Definition RET : Z := 0xbd9f0.           (* [comment removed for export] *)
Definition IT : itab := mk_itab_ranges BSEGS [(ENTRY, 815%nat)].
Lemma IT_ok : itab_sound BSEGS IT. Proof. apply APS.mk_itab_ranges_sound. Qed.

Definition NXF : nat := 33.            (* [comment removed for export] *)
Definition e_mtr : expr := EVar 31.  Definition e_fb : expr := EVar 32.
Definition e_p : expr := e_a0.   Definition e_v : expr := e_a1.
Definition VMAX : Z := 65536.            (* [comment removed for export] *)
Definition WSZ : Z := 5.
Definition WS : list (expr * expr) := [(e_p, ELit WSZ)].
(* [comment removed for export] *)
Definition FR : Z := 32.             (* [comment removed for export] *)
Definition YLO : Z := 32.


(* [comment removed for export] *)
Definition ga_in : list kentry :=
  [KRange e_p PTRLO (objhi WSZ); KShOk (SA e_p 0) (ELit WSZ); shmap_apart e_p 0 (ELit WSZ)]
  ++ frame_facts FR [(e_p, WSZ)] ++ RTC ++ GLZ_LOWSH.
Definition ga_out : list kentry := [KShOk (SA e_p 0) (ELit WSZ)].
Definition kn_in : list kentry :=
  [ KRange e_v 0 VMAX; KRange e_p PTRLO (objhi WSZ); KWr (SA e_p 0) (ELit WSZ) ] ++ sp_facts YLO ++ [ img_apart (e_p) 0 (ELit WSZ); KIMGA ] ++ ga_in.
Definition tin : acs := mkcs YLO WS e_mtr e_fb ENTRY regs0 kn_in NXF.

(* [comment removed for export] *)
Definition M : nat := 60.
Definition LO : nat := 61.
Definition js_regs : list expr := sr_havoc (sr_upd (sr_upd regs0 10 (eadd e_p (EVar M))) 11 (EVar LO)) caller_saved_but_a01 (S LO).
Definition kn_out : list kentry := [ KRange (EVar M) 1 WSZ; KWr (SA e_p 0) (ELit WSZ) ] ++ sp_facts YLO ++ ga_out.
Definition tout : acs := mkcs YLO WS e_mtr e_fb RET js_regs kn_out (LO + 14)%nat.
Definition ce : gcallee := GCE NXF tin [tout] 0 0.

(* [comment removed for export] *)
Fixpoint xloads (n : nat) (k : plan) : plan :=
  match n with O => k | S n' => PRun [] (PExt 0 [] (xloads n' k)) end.
Definition tail (h : nat) : plan :=
  PRun [] (PBump M (PFresh 10 0 (Some e_p) (PFact (KRange (EVar M) 1 WSZ) (PHandoff h)))).
Definition armA : plan := xloads 2 (tail 0).
Definition armB : plan := divfact e_v (q100w e_v) 100 (zfact e_v (q100w e_v) 100 (xloads 3 (tail 0))).
Definition r4 : expr := rem e_v (q1e4a e_v) 10000.
Definition armC : plan :=
  divfact e_v (q1e4a e_v) 10000 (divfact r4 (q100w r4) 100 (zfact r4 (q100w r4) 100 (xloads 4 (tail 0)))).
Definition plan_tc32 : plan :=
  PCase2 e_v 9 armA (PCase2 e_v 99 armA (PCase2 e_v 999 armB (PCase2 e_v 9999 armB armC))).
Definition SHAPE : shape := SHole 0.

(* [comment removed for export] *)
Lemma cert : check BSEGS IT ABOTH NXF LIMIT ISP0 (XN IT NXF) XE0 XB0 (HSce ce) 0%nat BFUEL FUEL None (ce_tin ce) plan_tc32 = COk SHAPE.
Proof. vm_cast_no_check (@eq_refl cres (COk SHAPE)). Qed.
Lemma gplan : gplan_ok plan_tc32 = true. Proof. vm_compute. reflexivity. Qed.
Lemma hshape : holes_only SHAPE = true. Proof. reflexivity. Qed.
(* [comment removed for export] *)
