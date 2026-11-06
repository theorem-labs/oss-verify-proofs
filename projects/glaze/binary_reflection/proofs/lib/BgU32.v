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

Definition ENTRY : Z := 0xc0eb8.
Definition RETPC : Z := 0xc1674.
Definition STPC : Z := 0xc1664.      (* [comment removed for export] *)
Definition IT : itab := mk_itab_ranges BSEGS [(ENTRY, 696%nat)].
Lemma IT_ok : itab_sound BSEGS IT. Proof. apply APS.mk_itab_ranges_sound. Qed.

(* [comment removed for export] *)
Definition NXF : nat := 38.            (* [comment removed for export] *)
Definition e_mtr : expr := EVar 36.  Definition e_fb : expr := EVar 37.
Definition e_pv := e_a0.  Definition e_str := e_a2.  Definition e_pix := e_a3.
Definition e_vraw : expr := EVar 31.          (* [comment removed for export] *)
Definition e_v : expr := EExt false 0 4 e_vraw.  (* [comment removed for export] *)  Definition e_a : expr := EVar 32.  Definition e_size : expr := EVar 33.
Definition e_data : expr := EVar 34.  Definition e_ix : expr := EVar 35.
(* [comment removed for export] *)
Definition e_dix (m : smode) : expr := match m with ML => eadd e_data e_ix | MS => eadd (eaddz e_str 1) e_ix end.
Definition VBYTES : nat := 4.

Definition WMAX : Z := 10.           (* [comment removed for export] *)
Definition WS (m : smode) : list (expr * expr) := [(e_dix m, ELit WMAX); (e_pix, ELit 8)].

(* [comment removed for export] *)
Definition FR : Z := 16.             (* [comment removed for export] *)
Definition YLO : Z := 16.
Definition str_m (m : smode) : list kentry :=
  match m with ML => str_L e_str e_a e_size e_data ++ [KRange e_data PTRLO PTRHI; KDisj (SA (e_dix ML) 0) (ELit WMAX) (SA e_str 0) (ELit 24)]
             | MS => KRange e_str PTRLO (objhi 24) :: strS e_str e_size end.


(* [comment removed for export] *)
Definition ga_in (m : smode) : list kentry :=
  [KRange e_pv PTRLO (objhi (Z.of_nat VBYTES)); KAlign e_pv 4; KShOk (SA e_pv 0) (ELit (Z.of_nat VBYTES)); KRange e_str PTRLO (objhi 24); KAlign e_str 8; KShOk (SA e_str 0) (ELit 24); KRange e_pix PTRLO (objhi 8); KAlign e_pix 8; KShOk (SA e_pix 0) (ELit 8); shmap_apart e_pix 0 (ELit 8); KRange (e_dix m) PTRLO (objhi WMAX); KShOk (SA (e_dix m) 0) (ELit WMAX); shmap_apart (e_dix m) 0 (ELit WMAX)]
  ++ frame_facts FR [(e_pv, (Z.of_nat VBYTES)); (e_str, 24); (e_pix, 8); ((e_dix m), WMAX)] ++ RTC ++ GLZ_LOWSH.
Definition ga_out (m : smode) : list kentry := [KShOk (SA e_pix 0) (ELit 8); KShOk (SA (e_dix m) 0) (ELit WMAX)].
Definition kn_in (m : smode) : list kentry :=
  [ KRange e_pv PTRLO (objhi (Z.of_nat VBYTES)); KWord (SA e_pv 0) VBYTES e_vraw ]
  ++ sp_facts YLO ++ str_m m ++
  [ KRange e_pix PTRLO (objhi 8); KWord (SA e_pix 0) 8 e_ix; KWr (SA e_pix 0) (ELit 8);
    img_apart (e_dix m) 0 (ELit WMAX);
    KRange e_ix 0 (2 ^ 40); KWr (SA (e_dix m) 0) (ELit WMAX);
    KDisj (SA (e_dix m) 0) (ELit WMAX) (SA e_pv 0) (ELit (Z.of_nat VBYTES));
    KDisj (SA (e_dix m) 0) (ELit WMAX) (SA e_pix 0) (ELit 8);
    KDisj (SA e_pix 0) (ELit 8) (SA e_pv 0) (ELit (Z.of_nat VBYTES));
    KDisj (SA e_pix 0) (ELit 8) (SA e_str 0) (ELit 24);
    KIMGA ] ++ ga_in m.
Definition tin (m : smode) : acs := mkcs YLO (WS m) e_mtr e_fb ENTRY regs0 (kn_in m) NXF.

(* [comment removed for export] *)
Definition M : nat := 60.
Definition LO : nat := 61.
Definition js_regs : list expr :=
  sr_havoc (sr_upd (sr_upd regs0 10 (eadd e_ix (EVar M))) 11 (EVar LO)) caller_saved_but_a01 (S LO).
Definition kn_out (m : smode) : list kentry :=
  [ KRange (EVar M) 1 WMAX; KWord (SA e_pix 0) 8 (eadd e_ix (EVar M)); KWr (SA e_pix 0) (ELit 8);
    KWr (SA (e_dix m) 0) (ELit WMAX) ] ++ sp_facts YLO ++ ga_out m.
Definition tout (m : smode) : acs := mkcs YLO (WS m) e_mtr e_fb RETPC js_regs (kn_out m) (LO + 14)%nat.
(* [comment removed for export] *)
Definition cem (m : smode) : gcallee := GCE NXF (tin m) [tout m] 0 0.
Definition ce : gcallee := cem ML.
Definition ceS : gcallee := cem MS.

(* [comment removed for export] *)
Fixpoint xloads (n : nat) (k : plan) : plan :=
  match n with O => k | S n' => PRun [STPC; RETPC] (PExt 0 [] (xloads n' k)) end.
Definition arm_tail : plan :=
  PRun [STPC; RETPC] (PBump M (PFresh 10 0 (Some e_ix) (PFact (KRange (EVar M) 1 WMAX) (PRun [RETPC] (PHandoff 0))))).
Definition armA : plan := xloads 2 arm_tail.
Definition armB : plan := divfact e_v (q100w e_v) 100 (zfact e_v (q100w e_v) 100 (xloads 3 arm_tail)).
Definition armC : plan := divfact e_v (q1e4a e_v) 10000 (zfact e_v (q1e4a e_v) 10000 (xloads 3 arm_tail)).
Definition armD : plan :=
  let q := q1e4b e_v in
  divfact e_v q 10000 (qfact (rem e_v q 10000) (divfact q (q100 q) 100 (pfact (rem q (q100 q) 100) (xloads 4 arm_tail)))).
Definition rE1 := rem e_v (q1e8h e_v) 100000000.
Definition armE : plan :=
  divfact e_v (q1e8h e_v) 100000000 (divfact rE1 (q1e4b rE1) 10000 (qfact (rem rE1 (q1e4b rE1) 10000) (xloads 4 arm_tail))).
Definition karms : plan :=
  PCase2 e_v 9 armA (PCase2 e_v 99 armA (PCase2 e_v 999 armB (PCase2 e_v 9999 armB
    (PCase2 e_v 99999 armC (PCase2 e_v 999999 armC (PCase2 e_v 9999999 armD (PCase2 e_v 99999999 armD
      (PCase2 e_v 999999999 armE (PCase2 e_v 2147483647 armE armE))))))))).
Definition plan_u32 : AP.plan := karms.     (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma cert : check BSEGS IT ABOTH NXF LIMIT ISP0 (XN IT NXF) XE0 XB0 (HSce ce) 0%nat BFUEL FUEL None (ce_tin ce) plan_u32 = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.   (* [comment removed for export] *)
Lemma certS : check BSEGS IT ABOTH NXF LIMIT ISP0 (XN IT NXF) XE0 XB0 (HSce ceS) 0%nat BFUEL FUEL None (ce_tin ceS) plan_u32 = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.
Lemma gplan : gplan_ok plan_u32 = true. Proof. vm_compute. reflexivity. Qed.
Lemma hshape : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
(* [comment removed for export] *)
