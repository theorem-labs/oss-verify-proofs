(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import GaCommon.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition ENTRY : Z := 0xbc470.
Definition RETPC : Z := 0xbd74c.
Definition STPC : Z := 0xbd73c.      (* [comment removed for export] *)
Definition IT : itab := mk_itab_ranges ASEGS [(ENTRY, 1798%nat)].
Lemma IT_ok : itab_sound ASEGS IT. Proof. apply APS.mk_itab_ranges_sound. Qed.

(* [comment removed for export] *)
Definition NXF : nat := 38.            (* [comment removed for export] *)
Definition e_mtr : expr := EVar 36.  Definition e_fb : expr := EVar 37.
Definition e_pv := e_a0.  Definition e_str := e_a2.  Definition e_pix := e_a3.
Definition e_v : expr := EVar 31.  Definition e_a : expr := EVar 32.  Definition e_size : expr := EVar 33.
Definition e_data : expr := EVar 34.  Definition e_ix : expr := EVar 35.
Definition e_dix : expr := eadd e_data e_ix.
Definition VBYTES : nat := 8.
Definition VMAX : Z := 2 ^ 64 - 1.
Definition WMAX : Z := 20.           (* [comment removed for export] *)
Definition WS : list (expr * expr) := [(e_dix, ELit WMAX); (e_pix, ELit 8)].

(* [comment removed for export] *)
Definition FR : Z := 16.             (* [comment removed for export] *)
Definition YLO : Z := 16.


(* [comment removed for export] *)
Definition ga_in : list kentry :=
  [KRange e_pv PTRLO (objhi (Z.of_nat VBYTES)); KAlign e_pv 8; KShOk (SA e_pv 0) (ELit (Z.of_nat VBYTES)); KRange e_str PTRLO (objhi 24); KAlign e_str 8; KShOk (SA e_str 0) (ELit 24); KRange e_pix PTRLO (objhi 8); KAlign e_pix 8; KShOk (SA e_pix 0) (ELit 8); shmap_apart e_pix 0 (ELit 8); KRange e_dix PTRLO (objhi WMAX); KShOk (SA e_dix 0) (ELit WMAX); shmap_apart e_dix 0 (ELit WMAX)]
  ++ frame_facts FR [(e_pv, (Z.of_nat VBYTES)); (e_str, 24); (e_pix, 8); (e_dix, WMAX)] ++ RTC ++ GLZ_LOWSH.
Definition ga_out : list kentry := [KShOk (SA e_pix 0) (ELit 8); KShOk (SA e_dix 0) (ELit WMAX)].
Definition kn_in : list kentry :=
  [ KRange e_v 0 VMAX; KRange e_pv PTRLO (objhi (Z.of_nat VBYTES)); KWord (SA e_pv 0) VBYTES e_v ]
  ++ sp_facts YLO ++ str_L e_str e_a e_size e_data ++
  [ KRange e_pix PTRLO (objhi 8); KWord (SA e_pix 0) 8 e_ix; KWr (SA e_pix 0) (ELit 8);
    KRange e_data PTRLO PTRHI; KRange e_ix 0 (2 ^ 40); KWr (SA e_dix 0) (ELit WMAX);
    KDisj (SA e_dix 0) (ELit WMAX) (SA e_pv 0) (ELit (Z.of_nat VBYTES));
    KDisj (SA e_dix 0) (ELit WMAX) (SA e_str 0) (ELit 24);
    KDisj (SA e_dix 0) (ELit WMAX) (SA e_pix 0) (ELit 8);
    KDisj (SA e_pix 0) (ELit 8) (SA e_pv 0) (ELit (Z.of_nat VBYTES));
    KDisj (SA e_pix 0) (ELit 8) (SA e_str 0) (ELit 24);
    img_apart (e_dix) 0 (ELit WMAX); KIMGA ] ++ ga_in.
Definition tin : acs := mkcs YLO WS e_mtr e_fb ENTRY regs0 kn_in NXF.

(* [comment removed for export] *)
Definition M : nat := 60.
Definition LO : nat := 61.
Definition js_regs : list expr :=
  sr_havoc (sr_upd (sr_upd regs0 10 (eadd e_ix (EVar M))) 11 (EVar LO)) caller_saved_but_a01 (S LO).
Definition kn_out : list kentry :=
  [ KRange (EVar M) 1 WMAX; KWord (SA e_pix 0) 8 (eadd e_ix (EVar M)); KWr (SA e_pix 0) (ELit 8);
    KWr (SA e_dix 0) (ELit WMAX) ] ++ sp_facts YLO ++ ga_out.
Definition tout : acs := mkcs YLO WS e_mtr e_fb RETPC js_regs kn_out (LO + 14)%nat.
Definition ce : gcallee := GCE NXF tin [tout] 0 0.

(* [comment removed for export] *)
Fixpoint xloads (n : nat) (k : plan) : plan :=
  match n with O => k | S n' => PRun [STPC; RETPC] (PExt 0 [] (xloads n' k)) end.
Definition arm_tail : plan :=
  PRun [STPC; RETPC] (PBump M (PFresh 10 0 (Some e_ix) (PFact (KRange (EVar M) 1 WMAX) (PRun [RETPC] (PMerge 0))))).
Definition q8 : expr := q1e8h e_v.              Definition r8 : expr := rem e_v q8 100000000.
Definition q16 : expr := q1e8h q8.              Definition rm : expr := rem q8 q16 100000000.
Definition armA2 : plan := xloads 2 arm_tail.
Definition armA4 : plan := divfact e_v (q100 e_v) 100 (xloads 3 arm_tail).
Definition armB6 : plan := divfact e_v (q1e4a e_v) 10000 (xloads 3 arm_tail).
Definition armB8 : plan :=
  divfact e_v (q1e4b e_v) 10000 (divfact (q1e4b e_v) (q100 (q1e4b e_v)) 100 (xloads 4 arm_tail)).
Definition armC10 : plan := divfact e_v q8 100000000 (divfact r8 (q1e4b r8) 10000 (xloads 4 arm_tail)).
Definition armC12 : plan :=
  divfact e_v q8 100000000 (divfact q8 (q100 q8) 100 (divfact r8 (q1e4b r8) 10000 (xloads 5 arm_tail))).
Definition armD14 : plan :=
  divfact e_v q8 100000000 (divfact r8 (q1e4b r8) 10000 (divfact q8 (q1e4a q8) 10000 (xloads 5 arm_tail))).
Definition armD16 : plan :=
  divfact e_v q8 100000000 (divfact q8 (q1e4b q8) 10000 (divfact (q1e4b q8) (q100 (q1e4b q8)) 100
    (divfact r8 (q1e4b r8) 10000 (xloads 6 arm_tail)))).
Definition armE18 : plan :=
  divfact e_v q8 100000000 (divfact q8 q16 100000000 (divfact rm (q1e4b rm) 10000
    (divfact r8 (q1e4b r8) 10000 (xloads 6 arm_tail)))).
Definition armE20 : plan :=
  divfact e_v q8 100000000 (divfact q8 q16 100000000 (divfact q16 (q100 q16) 100 (divfact rm (q1e4b rm) 10000
    (divfact r8 (q1e4b r8) 10000 (xloads 7 arm_tail))))).
Fixpoint cases (ts : list (Z * plan)) (last : plan) : plan :=
  match ts with [] => last | (t, a) :: ts' => PCase2 e_v t a (cases ts' last) end.
Definition karms : plan :=
  cases [(9, armA2); (99, armA2); (999, armA4); (9999, armA4); (99999, armB6); (999999, armB6);
         (10^7 - 1, armB8); (10^8 - 1, armB8); (10^9 - 1, armC10); (10^10 - 1, armC10);
         (10^11 - 1, armC12); (10^12 - 1, armC12); (10^13 - 1, armD14); (10^14 - 1, armD14);
         (10^15 - 1, armD16); (10^16 - 1, armD16); (10^17 - 1, armE18); (10^18 - 1, armE18);
         (10^19 - 1, armE20)] armE20.
Definition plan_u64 : AP.plan := PVia 0 tout LO karms (PHandoff 0).

(* [comment removed for export] *)
Lemma cert : check ASEGS IT AASAN NXF LIMIT ISP0 (XN IT NXF) XE0 XB0 (HSce ce) 0%nat BFUEL FUEL None (ce_tin ce) plan_u64 = COk (SHole 0).
Proof. vm_cast_no_check (@eq_refl cres (COk (SHole 0))). Qed.   (* [comment removed for export] *)
Lemma gplan : gplan_ok plan_u64 = true. Proof. vm_compute. reflexivity. Qed.
Lemma hshape : holes_only (SHole 0) = true. Proof. reflexivity. Qed.
(* [comment removed for export] *)
